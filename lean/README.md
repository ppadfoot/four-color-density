# Conjecture 4.1 — complete Lean proof

This standalone project proves the upper-density bound in Cohn and
Rajagopal's Conjecture 4.1 ([source paper, version 3](https://arxiv.org/abs/2412.00937v3)).
It contains the entire proof, including the passage from finite periodic
configurations to arbitrary configurations and the exact published statement.

## Run

Extract the archive, open a terminal in this folder, and run:

```bash
./build.sh
```

Use macOS, GNU/Linux, or Linux inside Windows WSL. You need working Git,
curl, tar, Bash and a SHA-256 utility (`shasum` or `sha256sum`), plus internet
access on the first run. These are standard development tools; on macOS,
install Command Line Tools if Git is unavailable. See the
[official Lean installation prerequisites](https://lean-lang.org/install/manual/).

You do not need to install Lean or Mathlib manually. The script selects the
exact Lean version, obtains the pinned dependencies and their official
Mathlib cache, builds every project proof module, and checks the final
theorems and their transitive axiom dependencies. If elan is missing, it
installs a checksum-verified copy locally in `.tooling/`; it does not edit
your shell profile or change your default Lean version.

The first run downloads large dependencies and may take substantial time.
The script prints each module being checked and builds our modules one at
a time to limit concurrent memory use. This source archive contains no
compiled project proofs. No earlier project, private directory, or manual
cache copying is needed.

Success is reported only after every check passes:

```text
SUCCESS: all project proof modules compiled and the final axiom guards passed.
```

The result is also saved to `build-logs/SUCCESS.txt`. Full theorem types and
axiom output are in `build-logs/final-verification.log`. A failed step stops
the script with a nonzero exit status and identifies its log. After fixing
a missing prerequisite or network problem, run the same command again.

## What is proved

`Audit41.published_statement` takes an arbitrary set of points in the
Euclidean plane, colored on that set by four cyclic colors, with these
minimum distances between distinct points:

| Relation between colors | Minimum distance |
| --- | --- |
| Equal | √2 |
| Adjacent in the four-cycle | √5 / 2 |
| Opposite | 1 |

It proves local finiteness and the literal bound

```text
limsup (r → ∞) #(S ∩ closedBall(0, r)) / (π r²) ≤ 1.
```

No periodicity, local finiteness, or existence of a limiting density is
assumed. `Conjecture41.conjecture_4_1` gives the corresponding eventual
density bound; `Conjecture41.conjecture_4_1_limsup` gives its limsup form.

`Verification.lean` checks all three final declarations. Its guards make
compilation fail unless their only transitive axioms are `propext`,
`Classical.choice`, and `Quot.sound`, the standard axioms used here in Lean.
In particular, no admitted theorem is accepted by these guards.

## Reproducibility

- Lean: `leanprover/lean4:v4.28.0`.
- Mathlib commit: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- All dependency commits: `lake-manifest.json` and `dependency-pins.txt`.
- Source integrity: `SOURCES.sha256`, checked by the runner.
- Proof entry point: `Audit41.lean`; automatic final checks: `Verification.lean`.

For an existing Lean installation, normal `lake build` also includes the
published-statement interface and the final axiom guards. The recommended
`./build.sh` additionally handles setup, integrity checks, sequential
compilation, and a fresh final verification. Do not run `lake update`:
the included manifest already fixes the dependency versions.

The project proves Conjecture 4.1's upper bound. Additional results in the
accompanying paper, such as the integer-lattice example attaining density one, its explicit
finite-radius constants, local equality classification, and five-dimensional
density transfer and identification with D5, are not formalized here.

Русская инструкция: [README_RU.md](README_RU.md).
