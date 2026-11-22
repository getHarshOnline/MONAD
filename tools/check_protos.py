"""Compile each research header with its own declared physical include roots.

Descriptors and compiler dependency files go under target/proto-checks. These
check syntax and imports; source pinning and semantic conformance are separate.
"""

import argparse
import os
from pathlib import Path
import subprocess

EPILOG = """\
A private consumer of MONAD's headers is named on this machine, not here. Set
MONAD_PRIVATE_CONSUMERS to a comma-separated list of sibling checkout names, for
example MONAD_PRIVATE_CONSUMERS=name-one,name-two. Each is compiled with MONAD's
headers as its only provider. When the variable is unset, only the public
repositories are checked.
"""

# Quantum forks reuse virtual muon/ and hena/ names. Never combine their roots
# with the classical providers, even when the resulting descriptors are equal.
PROVIDERS = {
    "MONAD": (),
    "MUON": ("MONAD",),
    "HENA": ("MUON", "MONAD"),
    "Q-MUON": ("MONAD",),
    "Q-HENA": ("Q-MUON", "MONAD"),
}


def private_consumers() -> dict[str, tuple[str, ...]]:
    """Return the machine's private consumers, each built on MONAD alone."""
    names = os.environ.get("MONAD_PRIVATE_CONSUMERS", "")
    return {name.strip(): ("MONAD",) for name in names.split(",") if name.strip()}


def main() -> None:
    parser = argparse.ArgumentParser(
        description=__doc__,
        epilog=EPILOG,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--protoc", default="protoc")
    parser.add_argument("--siblings", type=Path, default=Path(".."))
    args = parser.parse_args()
    repository = Path(__file__).resolve().parents[1]
    consumers = {**PROVIDERS, **private_consumers()}
    roots = {
        name: (repository if name == "MONAD" else args.siblings.resolve() / name) / "protos"
        for name in consumers
    }
    missing = [str(path) for path in roots.values() if not path.is_dir()]
    if missing:
        parser.error("missing proto directories: " + ", ".join(missing))
    for name, providers in consumers.items():
        includes = [roots[provider] for provider in (name, *providers)]
        sources = sorted(roots[name].rglob("*.proto"))
        if not sources:
            parser.error(f"no proto sources in {roots[name]}")
        for source in sources:
            virtual = source.relative_to(roots[name])
            output = repository / "target" / "proto-checks" / name / virtual
            output.parent.mkdir(parents=True, exist_ok=True)
            subprocess.run(
                [args.protoc, *[f"--proto_path={root}" for root in includes],
                 "--include_imports", f"--descriptor_set_out={output.with_suffix('.pb')}",
                 f"--dependency_out={output.with_suffix('.d')}", str(source)],
                check=True,
            )
        print(f"{name}: {len(sources)} headers compiled; roots: " + ", ".join(map(str, includes)))


if __name__ == "__main__":
    main()
