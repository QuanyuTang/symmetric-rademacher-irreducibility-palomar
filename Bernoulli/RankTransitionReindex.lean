module

public import Bernoulli.RankTransitionBorder
import Mathlib.Logic.Equiv.Sum

/-!
# Transporting the conditional rank estimate across a coordinate partition
-/

open scoped BigOperators
open Matrix
namespace Bernoulli

/-- Relabeling both rows and columns preserves the nullity of a square matrix. -/
public theorem finrank_ker_mulVecLin_submatrix_equiv {K ι κ : Type*} [Field K]
    [Fintype ι] [Fintype κ] (A : Matrix ι ι K) (e : κ ≃ ι) :
    Module.finrank K (LinearMap.ker (A.submatrix e e).mulVecLin) =
      Module.finrank K (LinearMap.ker A.mulVecLin) := by
  have ha := A.mulVecLin.finrank_range_add_finrank_ker
  have he := (A.submatrix e e).mulVecLin.finrank_range_add_finrank_ker
  rw [← Matrix.rank, Module.finrank_fintype_fun_eq_card] at ha he
  rw [Matrix.rank_submatrix, Fintype.card_congr e] at he
  exact Nat.add_left_cancel (he.trans ha.symm)

/-- Relabeling preserves the approximate-kernel Fourier condition. -/
public theorem rankFourierHealthy_submatrix_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ℕ}
    {A : Matrix ι ι (ZMod p)} {r m : ℕ} {ε : ℝ} (h : rankFourierHealthy A r m ε)
    (e : κ ≃ ι) : rankFourierHealthy (A.submatrix e e) r m ε := by
  intro v hv hvSupp S hS a ha
  let w : ι → ZMod p := v ∘ e.symm
  have hw : w ≠ 0 := by
    intro he
    apply hv
    funext i
    simpa only [w, Function.comp_apply, Equiv.symm_apply_apply, Pi.zero_apply] using
      congrFun he (e i)
  have hm : (A.submatrix e e) *ᵥ v = (A *ᵥ w) ∘ e :=
    Matrix.submatrix_mulVec_equiv A v e e
  have hs : finiteVectorSupport ((A.submatrix e e) *ᵥ v) =
      (finiteVectorSupport (A *ᵥ w)).map e.symm.toEmbedding := by
    ext i
    rw [hm, mem_finiteVectorSupport, Function.comp_apply, Finset.mem_map]
    constructor
    · intro hi
      exact ⟨e i, mem_finiteVectorSupport.mpr hi, e.symm_apply_apply i⟩
    · rintro ⟨j, hj, hij⟩
      have he : e i = j := by simpa using (congrArg e hij).symm
      rw [he]
      exact mem_finiteVectorSupport.mp hj
  rw [hs, Finset.card_map] at hvSupp
  have hcard : m ≤ (S.map e.toEmbedding).card := by simpa using hS
  simpa only [Finset.prod_map, Equiv.coe_toEmbedding, w, Function.comp_apply, Equiv.symm_apply_apply]
    using h w hw hvSupp (S.map e.toEmbedding) hcard a ha

private theorem symmetricBorder_submatrix_equiv {K ι κ : Type*} [Field K]
    (A : Matrix ι ι K) (x : ι → K) (z : K) (e : κ ≃ ι) :
    (symmetricBorder A x z).submatrix (Equiv.sumCongr e (.refl Unit))
      (Equiv.sumCongr e (.refl Unit)) = symmetricBorder (A.submatrix e e) (x ∘ e) z := by
  ext i j
  cases i <;> cases j <;> simp [symmetricBorder]

/-- A coordinate partition identifies a resampled and a retained block in an
arbitrarily indexed leading matrix. -/
public theorem fairSign_corank_exception_le_of_partition {ι J I : Type*}
    [Fintype ι] [Fintype J] [Fintype I] [DecidableEq ι] [DecidableEq J] [DecidableEq I]
    {p : ℕ} [Fact p.Prime] (hp : 2 < p) {A : Matrix ι ι (ZMod p)} (hA : A.IsSymm)
    (e : J ⊕ I ≃ ι) {r m : ℕ} (hr : Fintype.card J ≤ r) (hm : m ≤ Fintype.card I)
    {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (hgood : rankFourierHealthy A r m ε)
    (z : ZMod p) :
    (∑ σ : ι → Bool, if
      Module.finrank (ZMod p) (LinearMap.ker
        (symmetricBorder A (fun i => fairSign (σ i)) z).mulVecLin) ≠
          Module.finrank (ZMod p) (LinearMap.ker A.mulVecLin) - 1
      then fairSignWeight ι else 0) ≤
      (p : ℝ)⁻¹ + Real.sqrt (fairSignWeight J + ε) := by
  classical
  let eσ : (J ⊕ I → Bool) ≃ (ι → Bool) := Equiv.arrowCongr e (.refl Bool)
  rw [← eσ.sum_comp]
  have hcard : fairSignWeight ι = fairSignWeight (J ⊕ I) := by
    rw [fairSignWeight, fairSignWeight, Fintype.card_congr e]
  have hB : (A.submatrix e e).IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact hA.apply _ _
  have hc := fairSign_corank_exception_le hp hB hr hm hε hε₁
    (rankFourierHealthy_submatrix_equiv hgood e) z
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun σ _ => ?_)) hc
  have hcol : (fun i => fairSign (p := p) (eσ σ i)) ∘ e = (fun i => fairSign (σ i)) := by
    funext i
    simp [eσ, Equiv.arrowCongr_apply]
  rw [hcard, ← finrank_ker_mulVecLin_submatrix_equiv A e,
    ← finrank_ker_mulVecLin_submatrix_equiv (symmetricBorder A (fun i => fairSign (eσ σ i)) z)
      (Equiv.sumCongr e (.refl Unit)),
    symmetricBorder_submatrix_equiv, hcol]

end Bernoulli
