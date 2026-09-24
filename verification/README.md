# Lean verification and formal scope

This report concerns the Lean upper-bound proof accompanying *A proof of Cohn and Rajagopal's four-color density conjecture*. It does not certify every statement in the accompanying manuscript.

## What the final theorem says

`Audit41.published_statement` takes an arbitrary set `S` in the Euclidean plane and a coloring `c : S → ZMod 4`. For distinct points, it assumes the minimum distances √2 for equal colors, √5/2 for adjacent colors, and 1 for opposite colors. It proves both finiteness in every bounded centered closed ball and

```text
limsup (r → +∞) #(S ∩ closedBall(0, r)) / (π r²) ≤ 1.
```

The final theorem does not assume periodicity, saturation, local finiteness, existence of a density limit, a Delaunay triangulation, or a geometric certificate. The internal periodic triangulation and its area and face-count identities are constructed and proved. The argument then passes to arbitrary configurations by buffered periodization.

The three final declarations are:

- `Audit41.published_statement`: the public interface with the original unsquared distances and literal radial limsup;
- `Conjecture41.conjecture_4_1`: the eventual upper-density formulation;
- `Conjecture41.conjecture_4_1_limsup`: the corresponding limsup formulation.

The definitions were checked for their intended meaning: `Plane` is `EuclideanSpace ℝ (Fin 2)`; colors are `ZMod 4`; the squared exclusion thresholds are 2, 5/4, and 1. Finiteness is proved before finite cardinality is used. The density ratio is eventually bounded above and nonnegative before Lean's real-valued limsup is used.

## Formal scope limits

The project formalizes the unrestricted upper bound. It does **not** formalize the manuscript's explicit example attaining density one, local equality classification, separately stated finite-radius bound with the manuscript's coefficients, five-dimensional density transfer, or identification with D5. Literature, dates, authorship and priority assertions are not mathematical Lean theorems.

The formal development follows the proof's mathematical route without being a line-by-line transcription of its exposition. For example, its triangulation representative choices and final quantitative periodization estimates differ harmlessly from the manuscript's presentation. `AuthoritativeProof.lean` is a commented explanation; that comment itself is not a formal proof.

## Completed verification runs

**23 September 2026 — complete source build.** The identical release sources were compiled in a separate project directory with no prebuilt local proof modules. All 51 project modules compiled successfully. Only the pinned external dependency cache was reused. Each module's retained log contains a successful `Built` entry. The default build and fresh final theorem checks succeeded.

**24 September 2026 — release reverification.** All 60 entries in the release's `SOURCES.sha256` were checked against both the distributed sources and the previously compiled project. The sources matched exactly. The default `lake build` succeeded using that existing project cache, and `lake env lean Verification.lean` was then elaborated afresh. This is a new reverification with cached project modules, **not** a claim of a second complete source rebuild on 24 September.

The three final declarations report exactly:

```text
'Audit41.published_statement' depends on axioms: [propext, Classical.choice, Quot.sound]
'Conjecture41.conjecture_4_1' depends on axioms: [propext, Classical.choice, Quot.sound]
'Conjecture41.conjecture_4_1_limsup' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`Verification.lean` contains guards that make compilation fail if these reports differ. Separate negative controls, outside the distributed proof project, were checked again: an injected additional axiom and an admitted proof were each rejected by the guards. The intentionally failing control file returns exit code 1 with exactly the two expected guard errors; this is the successful outcome for those controls.

The project has 51 Lean files and 523 lemma/theorem declarations. A fresh lexical check, excluding comments and strings, found no executable `sorry`, `admit`, new `axiom`, `unsafe`, `native_decide`, `implemented_by`, `extern`, `run_elab`, `run_tac`, `initialize`, or `addDecl`. The build order covers all project Lean files and respects their imports. This scan supplements the kernel/axiom checks; it does not replace them.

## Versions and reproduction

- Lean: `leanprover/lean4:v4.28.0`.
- Lean commit: `7e01a1bf5c70fc6167d49c345d3bf80596e9a79b`.
- Mathlib: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- All nine dependency revisions are pinned in `lake-manifest.json` and `dependency-pins.txt`; their revisions and tracked-file cleanliness were checked.
- Host used for the recorded runs: Apple Silicon macOS.

From the Lean project directory in a fresh extraction, run:

```bash
bash ./build.sh
```

The script checks source hashes, selects the pinned Lean version, obtains the pinned dependencies and Mathlib cache, checks dependency revisions, builds the project modules, exercises the default build, and freshly elaborates `Verification.lean`. It reports success only if all steps pass. Git, curl, tar, Bash, a SHA-256 utility and initial internet access are required. If elan is unavailable, the script installs a checksum-verified copy locally without changing a shell profile or global default toolchain. First setup can download substantial data and take substantial time.

For an existing compatible Lean installation and downloaded dependencies, the core checks are:

```bash
lake build
lake env lean Verification.lean
```

Use the included toolchain and manifest; do not run `lake update` as part of reproducing this pinned release. `build-logs/final-verification.log` records the statements and axiom dependencies. The source release contains no compiled project proofs or bundled Mathlib binaries.

## Interpretation

Successful Lean checking establishes the formal statements above within Lean's logical foundations and the usual trust in its kernel and execution. It does not eliminate the need to interpret the definitions correctly, and it does not convert the additional unformalized parts of the paper into formal theorems. The axiom report is evidence about the transitive dependencies of these particular declarations, not a claim of absolute certainty about all accompanying prose.

The public logs have only local machine path prefixes replaced by placeholders. Mathematical statements, axiom lists, compiler diagnostics, and exit statuses have not been changed.

The negative-control source is retained in `controls/IndependentAudit.lean` for audit purposes. It is deliberately outside the proof library and is expected to fail the two guards. After a successful normal build, it can be run from the repository's `lean/` directory with `lake env lean ../verification/controls/IndependentAudit.lean` when the pinned Lean toolchain is available through `lake`. The expected result is exit code 1 with the two guard failures described above.
