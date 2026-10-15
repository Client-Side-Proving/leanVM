#!/usr/bin/env python3
"""Generate two current-source Privacy Pools client fixtures with build provenance."""

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

from terminal_fixture_provenance import git, sha256, source_files, validate_client_fixture


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("client_repository", type=Path)
    parser.add_argument("setup_config", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--cargo-offline", action="store_true")
    args = parser.parse_args()
    repository = args.client_repository.resolve()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    setup = output / "client-setup.json"
    shutil.copyfile(args.setup_config.resolve(), setup)
    sources = source_files(repository)
    generator_sources = {
        name: sha256(Path(__file__).resolve().parent / name)
        for name in ("run_client_fixtures.py", "terminal_fixture_provenance.py")
    }
    provenance = {
        "started_at_utc": datetime.now(timezone.utc).isoformat(),
        "repository": "spartan-whir",
        "head": git(repository, "rev-parse", "HEAD"),
        "source_sha256": sources,
        "generator_sha256": sha256(__file__),
        "generator_sources_sha256": generator_sources,
        "setup_sha256": sha256(setup),
        "features": ["parallel", "poseidon1"],
        "environment": {
            name: os.environ[name]
            for name in ("RUSTFLAGS", "CARGO_ENCODED_RUSTFLAGS", "RAYON_NUM_THREADS")
            if name in os.environ
        },
        "rustc_version": subprocess.check_output(["rustc", "--version", "--verbose"], text=True).strip(),
        "source_unchanged_during_generation": False,
        "runs": [],
    }
    provenance_path = output / "client-source-provenance.json"
    provenance_path.write_text(json.dumps(provenance, indent=2) + "\n")
    command = [
        "cargo", "build", "--locked", "--release", "--features", "parallel,poseidon1",
        "--bin", "leanvm-full-zk-spark-fixture", "--message-format=json-render-diagnostics",
    ]
    if args.cargo_offline:
        command.append("--offline")
    provenance["build_command"] = command
    build_log = output / "client-cargo-build.jsonl"
    with build_log.open("w") as log:
        subprocess.run(command, cwd=repository, stdout=log, check=True)
    executables = set()
    for line in build_log.read_text().splitlines():
        event = json.loads(line)
        if event.get("reason") == "compiler-artifact" and event.get("target", {}).get("name") == "leanvm-full-zk-spark-fixture":
            if event.get("executable"):
                executables.add(Path(event["executable"]))
    if len(executables) != 1:
        raise ValueError("Cargo did not identify exactly one client fixture executable")
    executable = executables.pop()
    provenance["executable_sha256"] = sha256(executable)
    if source_files(repository) != sources:
        raise ValueError("client sources changed during the build")
    environment = os.environ.copy()
    environment["SPARK_FRESH_MASK_BATCHING"] = "same_height"
    environment["SPARK_MASK_PACKING"] = "all_free_basis"
    provenance["mask_options"] = {key: environment[key] for key in ("SPARK_FRESH_MASK_BATCHING", "SPARK_MASK_PACKING")}
    for sample in (0, 1):
        fixture = output / f"fixture-{sample}"
        command = [str(executable), str(fixture), "--circuit", "privacy-pools", "--sample", str(sample), "--setup-config", str(setup)]
        started = time.monotonic()
        with (output / f"client-{sample}.log").open("w") as log:
            subprocess.run(command, cwd=repository, env=environment, stdout=log, stderr=subprocess.STDOUT, check=True)
        provenance["runs"].append({
            "sample": sample,
            "command": [
                executable.name, f"<output>/fixture-{sample}",
                "--circuit", "privacy-pools", "--sample", str(sample),
                "--setup-config", "<output>/client-setup.json",
            ],
            "elapsed_seconds": time.monotonic() - started,
            "manifest_sha256": validate_client_fixture(fixture),
        })
    if source_files(repository) != sources or sha256(executable) != provenance["executable_sha256"]:
        raise ValueError("client sources or executable changed during generation")
    if sha256(setup) != provenance["setup_sha256"]:
        raise ValueError("client setup changed during generation")
    if any(sha256(Path(__file__).resolve().parent / name) != expected for name, expected in generator_sources.items()):
        raise ValueError("client generation scripts changed during generation")
    provenance["source_unchanged_during_generation"] = True
    provenance["completed_at_utc"] = datetime.now(timezone.utc).isoformat()
    provenance_path.write_text(json.dumps(provenance, indent=2) + "\n")
    print(json.dumps({"client_provenance": str(provenance_path), "samples": [0, 1]}, indent=2))


if __name__ == "__main__":
    main()
