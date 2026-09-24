# Verification guide

## Run the proof check

From the repository root:

```bash
bash verify.sh
```

This runs the source project's documented `build.sh` without changing it. See [prerequisites and setup](../lean/README.md). The initial setup requires internet access; the source package does not include Lean, Mathlib binaries, or compiled project proofs.

## Statement correspondence

| Part of the manuscript | Formal declaration or scope |
| --- | --- |
| Upper-density theorem, stated for an arbitrary planar set with the original three distance bounds | [`Audit41.published_statement`](../lean/Audit41.lean) |
| Eventual density bound | `Conjecture41.conjecture_4_1`, exported by [`Conjecture41/Main.lean`](../lean/Conjecture41/Main.lean) |
| Real-valued radial limsup bound | `Conjecture41.conjecture_4_1_limsup`, exported by the same module |
| Local finiteness, existence of the periodic geometric objects, and passage from periodic to arbitrary configurations | Proved within the formal development, not additional assumptions on the final theorem |
| Density-one example, local equality classification, the paper's explicit finite-radius coefficients, five-dimensional transfer and identification with D5 | Proved in the manuscript; outside the formalization |

The formal development follows the same mathematical route but is not a line-by-line transcription of the article. Its internal choices and quantitative intermediate estimates need not coincide with the paper's exposition.

## Recorded result

**PASS.** All 51 project modules were compiled from source on **23 September 2026**, with only external dependency caches reused. The identical release sources were checked again on **24 September 2026** using the existing project build cache, followed by fresh elaboration of `Verification.lean`. The repeated build and final checks both returned exit code 0.

The final declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. The guards reject an additional axiom or an admitted proof in their transitive dependencies. Separate negative controls confirmed both rejections.

- [Full verification report](../verification/README.md).
- [Machine-readable results and exit codes](../verification/verification-result.json).
- [All 51 successful source-build entries, 23 September](../verification/logs/2026-09-23/clean-build-summary.log).
- [Fresh final statements and axiom checks, 24 September](../verification/logs/2026-09-24/final-verification.log).
- [Recorded success, 24 September](../verification/logs/2026-09-24/SUCCESS.txt).

The intentionally failing negative-control file lives in `verification/controls/`, outside `lean/`. It is not part of the proof library or the normal build. Its log is expected to contain two guard errors and exit code 1. The normal proof build must exit with code 0.

The recorded runs used Apple Silicon macOS. The included Linux [GitHub Actions workflow](../.github/workflows/lean.yml) is configured to run the same verification command but has not been executed on GitHub before publication. The package makes no claim of an already-passing hosted run.

## Integrity

`lean/SOURCES.sha256` is checked automatically by the proof build. `lean/dependency-pins.txt` fixes the external revisions. The repository-level `SHA256SUMS.txt` also covers the paper, documentation, workflow, and verification records in this prepared snapshot; the manifest excludes itself.

From the repository root, verify the complete snapshot on macOS with:

```bash
shasum -a 256 -c SHA256SUMS.txt
```

On GNU/Linux:

```bash
sha256sum -c SHA256SUMS.txt
```

Checksums identify file contents. Formal verification establishes the specified mathematical statements; neither verifies historical priority or every sentence of the manuscript.
