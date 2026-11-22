module

public import Mathlib.Data.Fintype.Basic

namespace Bernoulli

/-- The finite support of a vector on a finite index type. -/
public noncomputable def finiteVectorSupport {ι K : Type*} [Fintype ι] [Zero K]
    (a : ι → K) : Finset ι := by
  classical
  exact Finset.univ.filter fun i => a i ≠ 0

@[simp] public theorem mem_finiteVectorSupport {ι K : Type*} [Fintype ι] [Zero K]
    {a : ι → K} {i : ι} : i ∈ finiteVectorSupport a ↔ a i ≠ 0 := by
  classical
  simp [finiteVectorSupport]

@[simp] public theorem finiteVectorSupport_zero {ι K : Type*} [Fintype ι] [Zero K] :
    finiteVectorSupport (0 : ι → K) = ∅ := by
  ext i
  simp

end Bernoulli
