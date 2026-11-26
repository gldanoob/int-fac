"""Prepare the pinned analytic lemmas and factoring sources for Lean 4.35."""
from concurrent.futures import ThreadPoolExecutor
from hashlib import sha256
import json
from pathlib import Path
import re
import subprocess
import tempfile
import tomllib
from urllib.parse import quote
from urllib.request import urlopen

WORKSPACE = Path(__file__).resolve().parent
FORMAL = WORKSPACE.parent
BUILD = WORKSPACE / ".lake"
ORIGINAL = "3091d9fb6eab9943787c5d19d0b7848bf364eac2"
RAW = f"https://raw.githubusercontent.com/homeowmorphism/riemann-hypothesis-original/{ORIGINAL}/src/"
PRODUCT_LEMMA = re.compile(
    r"\b(prod_le_prod(?:_of_subset_of_(?:le_one|one_le))?|one_le_prod|prod_le_one)(')?(?![\w'])"
)


def analytic_source(spec):
    rel = Path(*spec["module"].split(".")).with_suffix(".lean")
    local = FORMAL / "cogentic/.lake/packages/tree/src" / rel
    cached = BUILD / "upstream" / rel
    for path in (cached, local):
        if path.is_file():
            data = path.read_bytes()
            if sha256(data).hexdigest() == spec["sha256"]:
                break
    else:
        with urlopen(RAW + quote(rel.as_posix()), timeout=60) as response:
            data = response.read()
        if sha256(data).hexdigest() != spec["sha256"]:
            raise ValueError(f"wrong source digest for {rel}")
    if not cached.is_file() or cached.read_bytes() != data:
        cached.parent.mkdir(parents=True, exist_ok=True)
        cached.write_bytes(data)
    source = data.decode().splitlines()
    lines = [line.rstrip() for first, last in spec["lines"] for line in source[first - 1:last]]
    imports = ["Mathlib", *spec["imports"]]
    return rel, ("".join(f"import {name}\n" for name in imports) + "\n" +
                 "\n".join(lines).strip() + "\n").encode()


def main():
    BUILD.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=BUILD) as tmp:
        stage = Path(tmp)
        with ThreadPoolExecutor(6) as pool:
            for rel, data in pool.map(analytic_source, json.loads((WORKSPACE / "analytic-inputs.json").read_text())):
                dest = stage / rel
                dest.parent.mkdir(parents=True, exist_ok=True)
                dest.write_bytes(data)
        libs = tomllib.loads((WORKSPACE / "lakefile.toml").read_text())["lean_lib"]
        standalone = next(lib["roots"] for lib in libs if lib["name"] == "TwoThirds")
        for src in [*(FORMAL / (name + ".lean") for name in standalone), *(FORMAL / "cogentic").glob("*.lean"),
                    *(FORMAL / "cogentic/Cogentic").glob("*.lean")]:
            dest = stage / ("Cogentic" if src.parent.name == "Cogentic" else "") / src.name
            dest.parent.mkdir(exist_ok=True)
            # Mathlib split the ordered product lemmas for groups and groups with zero.
            source = PRODUCT_LEMMA.sub(lambda m: m[1] if m[2] else m[1] + "₀", src.read_text())
            dest.write_text(source)
        subprocess.run(["patch", "--batch", "--fuzz=0", "-p1", "-i", str(WORKSPACE / "lean-4.35.patch")],
                       cwd=stage, check=True, stdout=subprocess.DEVNULL)
        port = BUILD / "port"
        for old in port.rglob("*.lean"):
            if not (stage / old.relative_to(port)).is_file():
                old.unlink()
        for src in stage.rglob("*.lean"):
            dest = port / src.relative_to(stage)
            if dest.exists() and src.read_bytes() == dest.read_bytes():
                continue
            dest.parent.mkdir(parents=True, exist_ok=True)
            src.replace(dest)


if __name__ == "__main__":
    main()
