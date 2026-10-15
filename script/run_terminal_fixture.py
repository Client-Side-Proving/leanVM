#!/usr/bin/env python3
"""Build and prove a fresh terminal fixture with source and executable provenance."""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import subprocess

from terminal_fixture_provenance import (
    SCHEMA, capture_sources, input_files, sha256, source_files, validate_client_fixture, validate_sources,
)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("left_fixture", type=Path)
    parser.add_argument("right_fixture", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("profiles", type=Path)
    parser.add_argument("--upstream-ref", default="origin/main")
    parser.add_argument("--cargo-offline", action="store_true")
    parser.add_argument("--cargo-feature", action="append", default=[])
    parser.add_argument("--proving-timeout-seconds", type=int, default=0)
    parser.add_argument("--client-source-provenance", type=Path)
    args = parser.parse_args()
    if args.proving_timeout_seconds < 0:
        parser.error("--proving-timeout-seconds must be nonnegative; zero disables the deadline")
    repository = Path(__file__).resolve().parents[1]
    workspace = repository.parent
    inputs = {
        "left_fixture": args.left_fixture.resolve(),
        "right_fixture": args.right_fixture.resolve(),
        "profiles": args.profiles.resolve(),
    }
    manifest_hashes = {
        validate_client_fixture(inputs["left_fixture"]),
        validate_client_fixture(inputs["right_fixture"]),
    }
    client_provenance_path = args.client_source_provenance
    if client_provenance_path is None and inputs["left_fixture"].parent == inputs["right_fixture"].parent:
        candidate = inputs["left_fixture"].parent / "client-source-provenance.json"
        if candidate.is_file():
            client_provenance_path = candidate
    client_provenance = None
    if client_provenance_path is not None:
        inputs["client_source_provenance"] = client_provenance_path.resolve()
        client_provenance = json.loads(client_provenance_path.read_text())
        if client_provenance.get("source_unchanged_during_generation") is not True:
            raise ValueError("client generation did not verify stable sources")
        if not manifest_hashes.issubset({run["manifest_sha256"] for run in client_provenance["runs"]}):
            raise ValueError("client provenance does not identify both supplied manifests")
        for name in client_provenance["source_sha256"]:
            relative = Path(name)
            if relative.is_absolute() or ".." in relative.parts:
                raise ValueError(f"invalid client source path: {name}")
        if source_files(workspace / "spartan-whir") != client_provenance["source_sha256"]:
            raise ValueError("client source inventory differs from generation")
    input_hashes = {name: input_files(path) for name, path in inputs.items()}
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    provenance = {
        "schema": SCHEMA,
        "started_at_utc": datetime.now(timezone.utc).isoformat(),
        "repositories": capture_sources(workspace, args.upstream_ref),
        "inputs": input_hashes,
        "cargo_version": subprocess.check_output(["cargo", "--version"], text=True).strip(),
        "rustc_version": subprocess.check_output(["rustc", "--version", "--verbose"], text=True).strip(),
        "environment": {
            name: os.environ[name]
            for name in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RAYON_NUM_THREADS")
            if name in os.environ
        },
        "proof_cache": "disabled; every direct, lift and root proof is generated in this run",
        "proving_timeout_seconds": args.proving_timeout_seconds,
    }
    if client_provenance is not None:
        provenance["client_generation"] = {
            key: value for key, value in client_provenance.items() if key != "runs"
        }
        provenance["client_generation"]["runs"] = [
            {key: value for key, value in run.items() if key != "command"}
            for run in client_provenance["runs"]
        ]
    command = [
        "cargo", "build", "--locked", "--release", "-p", "spartan_whir_guest",
        "--bin", "leanvm-recursion-profile", "--message-format=json-render-diagnostics",
    ]
    if args.cargo_offline:
        command.append("--offline")
    for feature in args.cargo_feature:
        command.extend(["--features", feature])
    provenance["build_command"] = command
    (output / "source-provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    with (output / "cargo-build.jsonl").open("w") as log:
        subprocess.run(command, cwd=repository, stdout=log, check=True)
    executables = set()
    for line in (output / "cargo-build.jsonl").read_text().splitlines():
        event = json.loads(line)
        if event.get("reason") == "compiler-artifact" and event.get("target", {}).get("name") == "leanvm-recursion-profile":
            if event.get("executable"):
                executables.add(Path(event["executable"]))
    if len(executables) != 1:
        raise ValueError("Cargo did not identify exactly one terminal profiling executable")
    executable = executables.pop()
    provenance["executable_sha256"] = sha256(executable)
    validate_sources(provenance, workspace)
    environment = os.environ.copy()
    environment.pop("LEANVM_DIRECT_PROOF_CACHE", None)
    environment["LEANVM_TERMINAL_EXPORT"] = str(output / "native")
    environment["LEANVM_VALIDATE_MUTATIONS"] = "1"
    environment["LEANVM_PROVING_TIMEOUT_SECONDS"] = str(args.proving_timeout_seconds)
    command = [
        str(executable), str(inputs["left_fixture"]), str(inputs["right_fixture"]),
        str(output / "report.json"), str(inputs["profiles"]),
    ]
    with (output / "proving.log").open("w") as log:
        subprocess.run(command, cwd=repository, env=environment, stdout=log, stderr=subprocess.STDOUT, check=True)
    validate_sources(provenance, workspace)
    if {name: input_files(path) for name, path in inputs.items()} != input_hashes:
        raise ValueError("client fixtures or profiles changed while generating the terminal proof")
    if sha256(executable) != provenance["executable_sha256"]:
        raise ValueError("terminal profiling executable changed while proving")
    fixture_path = output / "native/root-fixture.json"
    fixture = json.loads(fixture_path.read_text())
    selected_profiles = json.loads(inputs["profiles"].read_text())
    expected_schema = (
        "leanvm-terminal-grouped-logup-experiment-v1"
        if selected_profiles.get("terminal_grouped_logup", False)
        else "leanvm-terminal-two-commitment-fixture-v1"
    )
    if fixture.get("schema") != expected_schema:
        raise ValueError("exported terminal mode does not match the selected profiles")
    provenance["completed_at_utc"] = datetime.now(timezone.utc).isoformat()
    provenance["native_proof_sha256"] = fixture["proof_sha256"]
    provenance["program_mle_sha256"] = {
        program["program"]: program["mle_sha256"] for program in fixture["bytecodes"]
    }
    fixture["source_provenance"] = provenance
    fixture_path.write_text(json.dumps(fixture, indent=2) + "\n")
    (output / "source-provenance.json").write_text(json.dumps(provenance, indent=2) + "\n")
    print(json.dumps({"root_fixture": str(fixture_path), "native_proof_sha256": fixture["proof_sha256"]}, indent=2))


if __name__ == "__main__":
    main()
