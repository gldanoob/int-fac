"""Restore the readable GRH cache with the combined workspace's locked Mathlib."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parent
lake = sys.argv[1]
packages = root / ".lake/packages"
packages.mkdir(parents=True, exist_ok=True)
for dep in json.loads((root / "lake-manifest.json").read_text())["packages"]:
    dest = packages / dep["name"]
    if dest.exists():
        continue
    # Mathlib and the GRH repository have much larger histories than these revisions.
    with tempfile.TemporaryDirectory(dir=packages) as tmp:
        checkout = Path(tmp) / "checkout"
        subprocess.run(["git", "init", "-q", str(checkout)], check=True)
        for args in (["remote", "add", "origin", dep["url"]],
                     ["fetch", "-q", "--depth=1", "origin", dep["rev"]],
                     ["checkout", "-q", "--detach", "FETCH_HEAD"]):
            subprocess.run(["git", *args], cwd=checkout, check=True)
        checkout.rename(dest)

probe = subprocess.run([lake, "build", "--no-build", "GRH/+Main:olean"], cwd=root,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
if probe.returncode:
    grh = packages / "GRH"
    # The upstream cache command runs from its own project root.
    nested = grh / ".lake/packages"
    nested.mkdir(parents=True, exist_ok=True)
    for dep in json.loads((grh / "lake-manifest.json").read_text())["packages"]:
        link = nested / dep["name"]
        if not link.exists() and not link.is_symlink():
            target = (packages / dep["name"]).resolve(strict=True)
            link.symlink_to(os.path.relpath(target, nested.resolve()), target_is_directory=True)
    subprocess.run([lake, "exe", "cache", "get"], cwd=grh, check=True)
