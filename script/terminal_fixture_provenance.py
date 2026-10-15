"""Capture and validate the local sources used to build terminal fixtures."""

import hashlib
import json
import subprocess
from pathlib import Path


SCHEMA = "leanvm-terminal-source-provenance-v1"
SOURCE_DIRECTORIES = {"crates", "src", "examples", "benches", "vendor", ".cargo"}
SOURCE_FILES = {
    "Cargo.toml", "Cargo.lock", "build.rs", "rust-toolchain", "rust-toolchain.toml",
    "script/run_terminal_fixture.py", "script/terminal_fixture_provenance.py",
    "script/run_client_fixtures.py",
}


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def git(repository, *arguments):
    return subprocess.check_output(["git", "-C", str(repository), *arguments], text=True).strip()


def source_files(repository):
    names = subprocess.check_output(
        ["git", "-C", str(repository), "ls-files", "--cached", "--others", "--exclude-standard", "-z"]
    ).decode().split("\0")
    result = {}
    for name in sorted(set(names) - {""}):
        path = Path(name)
        if path.parts[0] not in SOURCE_DIRECTORIES and name not in SOURCE_FILES:
            continue
        if (
            "target" in path.parts or "__pycache__" in path.parts
            or path.suffix in {".pyc", ".md"} or path.name == ".DS_Store"
        ):
            continue
        absolute = repository / path
        if absolute.is_file():
            result[name] = sha256(absolute)
    return result


def source_digest(files):
    canonical = json.dumps(files, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(canonical).hexdigest()


def capture_repository(repository, upstream_ref=None):
    files = source_files(repository)
    result = {
        "head": git(repository, "rev-parse", "HEAD"),
        "branch": git(repository, "branch", "--show-current"),
        "source_sha256": source_digest(files),
        "files": files,
    }
    if upstream_ref is not None:
        result.update(
            upstream_ref=upstream_ref,
            upstream_commit=git(repository, "rev-parse", f"{upstream_ref}^{{commit}}"),
            upstream_base=git(repository, "merge-base", "HEAD", upstream_ref),
        )
    return result


def capture_sources(workspace, upstream_ref="origin/main"):
    return {
        name: capture_repository(workspace / name, upstream_ref if name == "leanVM" else None)
        for name in ("leanVM", "spartan-whir")
    }


def validate_sources(provenance, workspace):
    if provenance.get("schema") != SCHEMA:
        raise ValueError("missing terminal source provenance; generate a fresh fixture with run_terminal_fixture.py")
    repositories = provenance.get("repositories", {})
    if set(repositories) != {"leanVM", "spartan-whir"}:
        raise ValueError("terminal provenance must identify LeanVM and Spartan-WHIR sources")
    for name, recorded in repositories.items():
        current = capture_repository(workspace / name, recorded.get("upstream_ref"))
        if current["files"] != recorded.get("files") or current["source_sha256"] != recorded.get("source_sha256"):
            changed = sorted(
                path
                for path in set(current["files"]) | set(recorded.get("files", {}))
                if current["files"].get(path) != recorded.get("files", {}).get(path)
            )
            details = ", ".join(changed[:8]) or "Git revision or upstream base"
            raise ValueError(f"{name} differs from the fixture sources: {details}")
    leanvm = repositories["leanVM"]
    if not all(leanvm.get(key) for key in ("head", "upstream_ref", "upstream_commit", "upstream_base")):
        raise ValueError("LeanVM provenance must record its branch HEAD and upstream base")


def input_files(path):
    path = Path(path)
    if path.is_file():
        return {path.name: sha256(path)}
    if not path.is_dir():
        raise ValueError(f"input does not exist: {path}")
    return {
        str(entry.relative_to(path)): sha256(entry)
        for entry in sorted(path.rglob("*"))
        if entry.is_file()
    }


def validate_client_fixture(directory):
    manifest_path = directory / "full_zk_spark_manifest.json"
    manifest = json.loads(manifest_path.read_text())
    for artifact in manifest["artifacts"].values():
        name = artifact["file"]
        if Path(name).name != name:
            raise ValueError(f"invalid client artifact filename: {name}")
        path = directory / name
        if path.stat().st_size != artifact["bytes"] or sha256(path) != artifact["sha256"]:
            raise ValueError(f"client artifact does not match its manifest: {path}")
    return sha256(manifest_path)
