# Irreducibility for symmetric Rademacher matrices

**Authors** Tao Hu and Quanyu Tang

Codex developed this Lean 4 formalization from the authors’ original informal proof and its Lean-oriented revision.

The theorem gives absolute constants $c,C>0$ such that for every $n\ge 1$, the characteristic polynomial of a symmetric $n\times n$ matrix with independent uniform $\{-1,1\}$ entries on and above the diagonal is reducible over $\mathbb Q$ with probability at most $C\exp(-c n^{1/4})$. The bound is unconditional.

## Formal statement and proof

[`PalomarBernoulliChallenge.lean`](PalomarBernoulliChallenge.lean) states the probability as the ratio of two finite cardinalities and uses Mathlib's characteristic polynomial and irreducibility over the rationals. [`PalomarBernoulliSolution.lean`](PalomarBernoulliSolution.lean) relates that ratio to the finite probability model used in the proof.

The proof relates the number of rational irreducible factors, counted with multiplicity, to a weighted prime average of finite-field eigenspace dimensions via the factor fields and their discriminants. The finite-field argument proves Halász's concentration bound with restricted signed relations, controls near-kernel vectors by inverse Littlewood–Offord counting, and sums the corank transitions of the principal blocks on the required prime interval. [Ferber, Jain, Sah and Sawhney](https://arxiv.org/abs/2106.04049), [Ferber, Jain, Luh and Samotij](https://arxiv.org/abs/1904.10425).

The analytic argument establishes the Euler product and logarithmic derivative series for Mathlib's Dedekind zeta function. It uses the analytic continuation and the zero-free region for the contour shift that gives the uniform smoothed prime-ideal estimate. The release pins Lean and Mathlib to the versions used by the imported proof of the zero-free region. [Cureton–Thorner formalization](https://github.com/AxiomMath/DedekindZetaZeroFree/commit/09afbb4ce6570c1615d58509dc197fc9f0956b7d).

The [class field theory dependency](vendor/class-field-theory) is the source subtree from that same commit. It retains its upstream licence and is declared as a contained Lake path dependency.

The final theorem uses only Lean's standard axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Build and audit

```sh
lake exe cache get
lake build
lake env lean verification/FinalAudit.lean
```

On Linux with Bubblewrap and the pinned toolchain on `PATH`, run `lake comparator --config comparator.json` to compare the statement and replay the solution in Lean and NanoDa. The full proof export requires several gigabytes of disk space. GitHub Actions builds and audits the proof on every push to `main` and pull request against `main`. A manually dispatched run can also request the full Comparator replay.
