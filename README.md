# A proof of Cohn and Rajagopal's four-color density conjecture

**Timofei Iuzhakov and Dmitry Vetrov**

Manuscript, LaTeX source, and a Lean 4 formalization of the upper-density bound in Conjecture 4.1 of Cohn and Rajagopal's [*Variations on five-dimensional sphere packings*](https://arxiv.org/abs/2412.00937v3).

## Independent work and chronology

An independent proposed proof of the same conjecture is available in [*The Cohn–Rajagopal Planar Density Conjecture*](https://huggingface.co/datasets/PureOne/Cohn-Rajagopal-Density-Conjecture), a research release published by Maciej Nowicki (PureOne) on **20 September 2026**.

The proof presented here was developed independently. On **6 September 2026**, Timofei Iuzhakov sent an earlier manuscript and accompanying Lean projects to Henry Cohn and Isaac Rajagopal, using [this shared Google Drive folder](https://drive.google.com/drive/folders/144vB5bDcNNnXMBGpxCOS2HuIvXGdqdBz?usp=sharing). This communication preceded the public release linked above. The communication date is recorded in the author's retained correspondence; the Drive folder is a historical link and has since been updated. See [Chronology and provenance](docs/PROVENANCE.md) for the sources and the distinction between communication, discovery, and public release dates.

## Read the paper

- [Manuscript PDF](paper/four_color_density.pdf) — 19 pages.
- [LaTeX source and figures](paper/latex/) · [PDF build instructions](paper/README.md).
- [Lean source project](lean/) · [Detailed verification scope](docs/VERIFICATION.md).
- [Инструкция на русском](README_RU.md).

The PDF and source files in this repository are the current manuscript. The historical Drive folder contains earlier material, including material about Conjecture 4.2, which is outside the scope of this repository.

## The theorem

Let a set $C\subset\mathbb R^2$ be colored by $\mathbb Z/4\mathbb Z$. For any two distinct points, the minimum distance is

| Relation between the colors | Minimum distance |
| --- | --- |
| Equal | $\sqrt 2$ |
| Adjacent in the cycle $0,1,2,3,0$ | $\sqrt 5/2$ |
| Opposite in that cycle | $1$ |

Then $C$ is locally finite and

```math
\limsup_{R\to\infty}\frac{\operatorname{card}\left(C\cap\overline{B}(0,R)\right)}{\pi R^2}\leq 1.
```

Here, cardinality counts the points in the closed Euclidean disk of radius $R$ centered at the origin.

No periodicity or existence of an ordinary density limit is assumed. The paper proves sharpness using a checkerboard coloring of $\mathbb Z^2$. Its five-dimensional consequence concerns the specified family of packings built from four translates of $D_3$ over a planar base; it does not establish unrestricted optimality of $D_5$.

## Verify the Lean proof

On macOS or GNU/Linux (including Windows through WSL), open a terminal in this repository and run:

```bash
bash verify.sh
```

Prerequisites: Bash, Git, curl, tar, a SHA-256 utility (`shasum` or `sha256sum`), and internet access for the first setup. See the [Lean project's instructions](lean/README.md) for details. The first run downloads substantial dependencies and can take tens of minutes.

The command invokes the unchanged `lean/build.sh`. It obtains the pinned toolchain and dependencies, checks source hashes and dependency revisions, builds all 51 project modules, runs the normal default build, and checks the three final declarations and their transitive axiom dependencies. If elan is missing, the script installs a checksum-verified copy locally inside `lean/.tooling/`; it does not change shell profiles or the global default toolchain.

Successful verification ends with:

```text
SUCCESS: all project proof modules compiled and the final axiom guards passed.
```

It also creates `lean/build-logs/SUCCESS.txt`. The final statements and axiom output are in `lean/build-logs/final-verification.log`. A failed check exits with a nonzero status and identifies its log. The [GitHub Actions workflow](.github/workflows/lean.yml) runs the same command after upload; a successful local check is not a claim that GitHub Actions has already run.

Pinned versions:

- Lean: `leanprover/lean4:v4.28.0`.
- Mathlib commit: `8f9d9cff6bd728b17a24e163c9402775d9e6a365`.
- Remaining revisions: [dependency-pins.txt](lean/dependency-pins.txt) and [lake-manifest.json](lean/lake-manifest.json).

Do not run `lake update` when reproducing this version.

## What Lean certifies

[`Audit41.published_statement`](lean/Audit41.lean) takes an arbitrary planar set, a coloring defined on that set, and the three original distance bounds. It proves local finiteness and the literal upper radial density bound above. The declarations `Conjecture41.conjecture_4_1` and `Conjecture41.conjecture_4_1_limsup` provide the eventual-bound and limsup formulations.

[`Verification.lean`](lean/Verification.lean) requires the transitive axiom list of each of these declarations to contain only `propext`, `Classical.choice`, and `Quot.sound`. An admitted proof or an additional axiom in those dependencies makes the guard fail.

The formalization covers the full upper-density theorem, including the passage from periodic to arbitrary configurations. It does **not** cover the paper's sharpness example, its explicit finite-radius coefficients, its local equality classification, or its five-dimensional density transfer and identification with $D_5$. Those results have proofs in the manuscript. Formal verification also does not certify authorship or priority. See the [scope and recorded checks](docs/VERIFICATION.md).

## Acknowledgments and citation

We thank Henry Cohn for his interest in this work and his encouraging comments on an early version of the manuscript. We are also grateful for his helpful correspondence and suggestions concerning related questions in five-dimensional sphere packing.

Aristotle and ChatGPT were used to assist with checking the Lean formalization, and AI tools were also used for editorial assistance, as disclosed in the manuscript. The formal checks described above are performed by Lean.

Please cite the manuscript by **Timofei Iuzhakov and Dmitry Vetrov**, *A proof of Cohn and Rajagopal's four-color density conjecture*, and identify the repository commit used. Citation metadata is provided in [CITATION.cff](CITATION.cff).
