#!/usr/bin/env python3
"""Fetch the pinned arXiv source locally; never overwrite modified source files.

The archive is not redistributed by this repository. Its original license
remains in force. The SHA-256 check deliberately fails if arXiv changes bytes.
"""
from argparse import ArgumentParser
import hashlib
from io import BytesIO
from pathlib import Path
import subprocess
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parent.parent
URL = "https://arxiv.org/src/2611.34921v1"
SHA256 = "6a1c49f0563dff103de17bfd86cd9b2e56e3b0db3a97b0e280707b2836a60f7c"
FILES = {"paper.tex", "paper.bbl", "00README.json"}


def verified_members(data: bytes) -> dict[str, bytes]:
    if hashlib.sha256(data).hexdigest() != SHA256:
        raise ValueError("Source archive SHA-256 mismatch; refusing changed source")
    result = {}
    with tarfile.open(fileobj=BytesIO(data), mode="r:gz") as archive:
        for member in archive.getmembers():
            if member.name not in FILES or not member.isfile() or member.name in result:
                raise ValueError(f"Unexpected archive member: {member.name}")
            stream = archive.extractfile(member)
            if stream is None:
                raise ValueError(f"Unreadable member: {member.name}")
            result[member.name] = stream.read()
    if set(result) != FILES:
        raise ValueError("Missing source files in archive")
    return result


def main() -> None:
    parser = ArgumentParser(description=__doc__)
    parser.add_argument("--destination", type=Path, default=ROOT / "Papers/2611.34921")
    args = parser.parse_args()
    destination = args.destination.resolve()
    destination.mkdir(parents=True, exist_ok=True)
    archive_path = destination / "source.tar.gz"
    if archive_path.exists():
        data = archive_path.read_bytes()
    else:
        with tempfile.TemporaryDirectory() as tmp:
            download = Path(tmp) / "source.tar.gz"
            subprocess.run(["curl", "--fail", "--location", "--retry", "3",
                            "--connect-timeout", "30", "--max-time", "180",
                            URL, "--output", str(download)], check=True)
            data = download.read_bytes()
    members = verified_members(data)
    source = destination / "source"
    # Check every existing file before writing anything. Local edits are preserved.
    for name, content in members.items():
        path = source / name
        if path.exists() and path.read_bytes() != content:
            raise ValueError(f"Locally modified source: {path}; refusing to overwrite")
    source.mkdir(parents=True, exist_ok=True)
    if not archive_path.exists():
        archive_path.write_bytes(data)
    for name, content in members.items():
        (source / name).write_bytes(content)
    print(f"Verified arXiv:2611.34921v1 source in {source}")
    print(f"Archive SHA-256: {SHA256}")


if __name__ == "__main__":
    main()
