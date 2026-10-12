#!/usr/bin/env python3
"""Check the registered revisions and the dependency checkout identities."""

import json
from pathlib import Path
import subprocess


project = Path(__file__).resolve().parent.parent
pin = json.loads((project / "foundation-pin.json").read_text())
manifest = json.loads((project / "lake-manifest.json").read_text())
expected = {item["name"]: item["revision"] for item in pin["dependencies"]}
expected[pin["foundation"]["package"]] = pin["foundation"]["revision"]
actual = {item["name"]: item["rev"] for item in manifest["packages"]}
if actual != expected:
    raise SystemExit(f"Dependency revision mismatch: expected {expected}, got {actual}")

if (project / "lean-toolchain").read_text().strip() != pin["lean_toolchain"]:
    raise SystemExit("Lean toolchain differs from the registered snapshot")

for name, revision in expected.items():
    checkout = project / ".lake" / "packages" / name
    head = subprocess.check_output(
        ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True
    ).strip()
    if head != revision:
        raise SystemExit(f"{name}: expected {revision}, got {head}")
    if subprocess.run(
        ["git", "-C", str(checkout), "diff", "--quiet", "HEAD", "--"]
    ).returncode != 0:
        raise SystemExit(f"{name}: tracked source differs from the pinned revision")

foundation = project / ".lake" / "packages" / pin["foundation"]["package"]
upstream_toolchain = (foundation / "lean-toolchain").read_text().strip()
if upstream_toolchain != pin["lean_toolchain"]:
    raise SystemExit("Foundation toolchain does not match the registered snapshot")
upstream_lock = json.loads((foundation / "lake-manifest.json").read_text())
upstream_revisions = {item["name"]: item["rev"] for item in upstream_lock["packages"]}
registered_revisions = {item["name"]: item["revision"] for item in pin["dependencies"]}
if upstream_revisions != registered_revisions:
    raise SystemExit("Foundation lockfile differs from the registered dependencies")

print(f"Verified {len(expected)} dependency revisions and {pin['lean_toolchain']}")
