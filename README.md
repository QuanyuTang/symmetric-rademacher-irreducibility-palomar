# Irreducibility for symmetric Rademacher matrices

**Authors** Tao Hu and Quanyu Tang

Codex developed this Lean 4 formalization from the authors’ original informal proof and its Lean-oriented revision.

The theorem gives absolute constants $c,C>0$ such that for every $n\ge 1$, the characteristic polynomial of a symmetric $n\times n$ matrix with independent uniform $\{-1,1\}$ entries on and above the diagonal is reducible over $\mathbb Q$ with probability at most $C\exp(-c n^{1/4})$. The bound is unconditional.

## Formal statement and proof

The Challenge states the probability as a ratio of finite cardinalities, using Mathlib's characteristic polynomial over the rationals. Each assignment of upper-triangular signs gives exactly one symmetric matrix. The Solution proves that both the characteristic polynomial and the probability agree with the definitions used in the proof library. The `sorry` warning during a full build comes from the separate Challenge statement for Comparator. The Solution imports the proved library theorem. [Challenge](PalomarBernoulliChallenge.lean) · [Bijection](Bernoulli/Ensemble.lean#L39) · [Solution](PalomarBernoulliSolution.lean#L25)

The proof relates the number of rational irreducible factors, counted with multiplicity, to a weighted prime average of finite-field eigenspace dimensions via the factor fields and their discriminants. The finite-field argument proves Halász's concentration bound with restricted signed relations, controls near-kernel vectors by inverse Littlewood–Offord counting, and sums the corank transitions of the principal blocks. This gives the first-moment bound for all sufficiently large dimensions on the prime band used by the prime average. [Finite-field bound](Bernoulli/RankBandEstimate.lean#L15) · [Ferber, Jain, Sah and Sawhney](https://arxiv.org/abs/2106.04049v1) · [Ferber, Jain, Luh and Samotij](https://arxiv.org/abs/1904.10425v1)

The analytic argument establishes the Euler product and logarithmic derivative series for Mathlib's Dedekind zeta function. Borel–Carathéodory and Cauchy's derivative estimate control the logarithmic derivative in the contour shift that gives the uniform smoothed prime-ideal estimate. The release pins Lean and Mathlib to the versions used by the imported proof of the zero-free region. [Logarithmic derivative bound](Bernoulli/LogDerivativeBounds.lean#L53) · [Cureton–Thorner formalization](https://github.com/AxiomMath/DedekindZetaZeroFree/commit/09afbb4ce6570c1615d58509dc197fc9f0956b7d)

The [class field theory dependency](vendor/class-field-theory) is the source subtree from that same commit. It retains its upstream licence and is declared as a contained Lake path dependency.

The final theorem uses only Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Build and audit

```sh
lake exe cache get
lake build
lake env lean verification/FinalAudit.lean
```

For a Linux Comparator run, start in a fresh checkout with Bubblewrap installed. Before the build commands above, put the class field theory build directory inside the project's writable `.lake` directory.

```sh
mkdir -p .lake/vendor/class-field-theory
ln -s ../../.lake/vendor/class-field-theory vendor/class-field-theory/.lake
```

After building, run `PATH="$(lean --print-prefix)/bin:$PATH" lake comparator --config comparator.json` to compare the statement and replay the proof in Lean and NanoDa. Allow several gigabytes for the proof export in addition to the build artifacts. On pushes to `main` and pull requests against `main`, GitHub Actions builds the pinned class field theory dependency in a separate job and reuses its outputs by source and toolchain hash. It then builds and audits the theorem. A manually dispatched run can also request full Comparator replay.
