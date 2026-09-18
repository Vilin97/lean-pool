"""Share the current Lean CI build with documentation without sharing mutable caches.

Only the matching Lean Action CI run is queried. A source-tree/configuration
manifest is verified before any artifact is installed; Lake still checks its
normal build traces afterwards. Missing or incompatible artifacts fall back to
the ordinary documentation build.
"""

from __future__ import annotations

import argparse
import hashlib
import io
import json
import logging
import os
import shutil
import subprocess
import tarfile
import tempfile
import time
import zipfile
from pathlib import Path, PurePosixPath
from urllib.parse import urlencode

LOGGER = logging.getLogger(__name__)
ARTIFACT_NAME = "lean-pool-build"
ARCHIVE_NAME = "lean-pool-build.tar.gz"
MANIFEST_NAME = "build-manifest.json"


def _file_digest(path: Path) -> str:
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def build_identity(root: Path) -> dict:
    """Identify the checkout tree and pinned build inputs, including merge checkouts."""
    tree = subprocess.check_output(
        ["git", "rev-parse", "HEAD^{tree}"], cwd=root, text=True
    ).strip()
    return {
        "version": 1,
        "tree": tree,
        "inputs": {
            name: _file_digest(root / name)
            for name in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")
        },
    }


def pack_build(root: Path, destination: Path) -> None:
    """Package the completed root build; toolchains and dependencies stay in caches."""
    subprocess.run(["git", "diff", "--exit-code", "HEAD", "--"], cwd=root, check=True)
    payload = json.dumps(build_identity(root)).encode()
    manifest = tarfile.TarInfo(MANIFEST_NAME)
    manifest.size = len(payload)
    with tarfile.open(
        destination, "w:gz", compresslevel=1, dereference=True
    ) as archive:
        archive.addfile(manifest, io.BytesIO(payload))
        archive.add(root / ".lake/build", arcname=".lake/build")


def restore_build(root: Path, archive_path: Path) -> bool:
    """Validate identity and archive paths before replacing the root build."""
    with tarfile.open(archive_path, "r:gz") as archive:
        manifest = archive.extractfile(MANIFEST_NAME)
        if manifest is None or json.load(manifest) != build_identity(root):
            LOGGER.info(
                "CI build has a different source tree or configuration; rebuilding"
            )
            return False
        members = [
            member for member in archive.getmembers() if member.name != MANIFEST_NAME
        ]
        for member in members:
            path = PurePosixPath(member.name)
            if (
                path.parts[:2] != (".lake", "build")
                or ".." in path.parts
                or not (member.isfile() or member.isdir())
            ):
                raise ValueError(f"Unexpected build archive member: {member.name}")
        if not any(member.isfile() for member in members):
            raise ValueError("Empty Lean build artifact")
        with tempfile.TemporaryDirectory(prefix="lean-ci-build-") as temporary:
            archive.extractall(temporary, members=members, filter="data")
            destination = root / ".lake/build"
            if destination.exists():
                shutil.rmtree(destination)
            shutil.copytree(Path(temporary) / ".lake/build", destination)
    LOGGER.info("Restored Lean CI build for the current source tree")
    return True


def github_json(endpoint: str) -> dict:
    """Read GitHub metadata through the runner's authenticated CLI."""
    return json.loads(subprocess.check_output(["gh", "api", endpoint], timeout=60))


def matching_run(repository: str, head: str, event: str) -> dict | None:
    """Select the latest Lean CI attempt for this event and exact head revision."""
    query = urlencode({"head_sha": head, "event": event, "per_page": 10})
    endpoint = f"repos/{repository}/actions/workflows/lean_action_ci.yml/runs?{query}"
    runs = github_json(endpoint)["workflow_runs"]
    return max(runs, key=lambda run: run["id"]) if runs else None


def wait_for_artifact(repository: str, run: dict, wait_seconds: int) -> int | None:
    """Wait for compiled output without waiting for later lint/quality stages."""
    deadline = time.monotonic() + wait_seconds
    endpoint = f"repos/{repository}/actions/runs/{run['id']}"
    while True:
        artifacts = github_json(f"{endpoint}/artifacts?per_page=100")["artifacts"]
        matches = [
            artifact
            for artifact in artifacts
            if artifact["name"] == ARTIFACT_NAME and not artifact["expired"]
        ]
        if matches:
            return max(matches, key=lambda artifact: artifact["id"])["id"]
        status = github_json(endpoint)
        if status["status"] == "completed" or time.monotonic() >= deadline:
            return None
        time.sleep(min(20, max(0, deadline - time.monotonic())))


def download_build(root: Path, repository: str, artifact: int) -> bool:
    """Download the archive and validate it before installing any build files."""
    with tempfile.TemporaryDirectory(prefix="lean-ci-download-") as temporary:
        directory = Path(temporary)
        zipped = directory / "artifact.zip"
        with zipped.open("wb") as output:
            subprocess.run(
                ["gh", "api", f"repos/{repository}/actions/artifacts/{artifact}/zip"],
                stdout=output,
                check=True,
                timeout=600,
            )
        with zipfile.ZipFile(zipped) as archive:
            if archive.namelist() != [ARCHIVE_NAME]:
                raise ValueError("Unexpected files in Lean CI artifact")
            with archive.open(ARCHIVE_NAME) as source:
                with (directory / ARCHIVE_NAME).open("wb") as destination:
                    shutil.copyfileobj(source, destination)
        return restore_build(root, directory / ARCHIVE_NAME)


def reuse_build(root: Path, repository: str, head: str, event: str, wait: int) -> bool:
    """Best-effort reuse; unavailable CI never removes the regular Lake build step."""
    try:
        run = matching_run(repository, head, event)
        if run is None:
            LOGGER.info("No matching Lean CI run; using the regular Lake build")
            return False
        LOGGER.info("Looking for compiled output from %s", run["html_url"])
        artifact = wait_for_artifact(repository, run, wait)
        if artifact is None:
            LOGGER.info(
                "No completed build artifact available; using the regular Lake build"
            )
            return False
        return download_build(root, repository, artifact)
    except (
        subprocess.SubprocessError,
        OSError,
        ValueError,
        KeyError,
        tarfile.TarError,
        zipfile.BadZipFile,
    ):
        LOGGER.exception("Could not reuse CI output; using the regular Lake build")
        return False


def main() -> None:
    """Package a successful build or restore the matching workflow's compiled output."""
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    pack = commands.add_parser("pack")
    pack.add_argument("--output", type=Path, default=Path(ARCHIVE_NAME))
    restore = commands.add_parser("restore")
    restore.add_argument("--repository", default=os.environ.get("GITHUB_REPOSITORY"))
    restore.add_argument("--head", required=True)
    restore.add_argument("--event", required=True)
    restore.add_argument("--wait-seconds", type=int, default=7200)
    arguments = parser.parse_args()
    logging.basicConfig(level=logging.INFO, format="ci-artifacts: %(message)s")
    if arguments.command == "pack":
        pack_build(Path.cwd(), arguments.output)
    else:
        reuse_build(
            Path.cwd(),
            arguments.repository,
            arguments.head,
            arguments.event,
            arguments.wait_seconds,
        )


if __name__ == "__main__":
    main()
