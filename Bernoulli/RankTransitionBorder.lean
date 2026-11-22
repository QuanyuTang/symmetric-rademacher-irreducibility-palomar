module

public import Bernoulli.RankTransitionQuadratic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Tactic.Linarith

/-!
# Conditional corank bound for a symmetric border

For an invertible block, the difference vector supported on the resampled
coordinates is the image of the coefficient vector of the linearized form.
Consequently the same approximate-kernel condition controls both singular
and invertible leading blocks.
-/

open scoped BigOperators
open Matrix
namespace Bernoulli

private theorem two_ne_zero_mod_odd_prime {p : ℕ} [Fact p.Prime] (hp : 2 < p) :
    (2 : ZMod p) ≠ 0 := by
  change ((2 : ℕ) : ZMod p) ≠ 0
  rw [Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hp]
  decide

private theorem fairSign_injective {p : ℕ} [Fact p.Prime] (hp : 2 < p) :
    Function.Injective (fairSign (p := p)) := by
  have h : (1 : ZMod p) ≠ -1 := fun h =>
    two_ne_zero_mod_odd_prime hp (by
      have he := congrArg (fun x : ZMod p => x + 1) h
      simpa [one_add_one_eq_two] using he)
  intro b c hbc
  cases b <;> cases c <;> simp_all [fairSign, eq_comm]

private theorem finrank_ker_ne_zero_iff_det_eq_zero {K ι : Type*} [Field K] [Fintype ι]
    [DecidableEq ι] (A : Matrix ι ι K) :
    Module.finrank K (LinearMap.ker A.mulVecLin) ≠ 0 ↔ A.det = 0 := by
  rw [Ne, Submodule.finrank_eq_zero, ← Matrix.exists_mulVec_eq_zero_iff (M := A)]
  constructor
  · intro h
    obtain ⟨v, hv, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
    exact ⟨v, hv₀, hv⟩
  · rintro ⟨v, hv₀, hv⟩ heq
    have hv' : v ∈ (⊥ : Submodule K (ι → K)) :=
      heq ▸ (show v ∈ LinearMap.ker A.mulVecLin from hv)
    exact hv₀ (by simpa using hv')

/-- For an invertible healthy block, each atom of the Schur-complement
quadratic form is bounded using the number of resampled coordinates. -/
public theorem fairSign_quadratic_inv_mass_le {J I : Type*}
    [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]
    {p : ℕ} [Fact p.Prime] (hp : 2 < p) {A : Matrix (J ⊕ I) (J ⊕ I) (ZMod p)}
    (hA : A.IsSymm) (hdet : A.det ≠ 0) {r m : ℕ}
    (hr : Fintype.card J ≤ r) (hm : m ≤ Fintype.card I)
    {ε : ℝ} (hε : 0 ≤ ε) (hgood : rankFourierHealthy A r m ε) (z : ZMod p) :
    modularMass (fun _ : J ⊕ I → Bool => fairSignWeight (J ⊕ I))
      (fun ω => (fun i => fairSign (ω i)) ⬝ᵥ (A⁻¹ *ᵥ (fun i => fairSign (ω i)))) z ≤
      (p : ℝ)⁻¹ + Real.sqrt (fairSignWeight J + ε) := by
  classical
  have hsymm : (A⁻¹ : Matrix (J ⊕ I) (J ⊕ I) (ZMod p)).IsSymm := by
    change (A⁻¹)ᵀ = A⁻¹
    rw [Matrix.transpose_nonsing_inv, hA.eq]
  refine modularMass_le_of_character_bound _ _ (sum_fairSignWeight _)
    (Real.sqrt_nonneg _) (fun a ha => ?_) z
  apply norm_fairSign_quadratic_le_of_resample hsymm a hε
  intro σ σ' hσσ'
  let d : J ⊕ I → ZMod p := fairSignLeft σ - fairSignLeft σ'
  let w : J ⊕ I → ZMod p := A⁻¹ *ᵥ d
  have hAw : A *ᵥ w = d := by
    dsimp only [w]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  have hd : d ≠ 0 := by
    intro h
    apply hσσ'
    funext j
    apply fairSign_injective hp
    apply sub_eq_zero.mp
    simpa only [d, Pi.sub_apply, Pi.zero_apply, fairSignLeft, Sum.elim_inl] using
      congrFun h (Sum.inl j)
  have hw : w ≠ 0 := by
    intro h
    apply hd
    rw [← hAw, h, Matrix.mulVec_zero]
  let eJ : J ↪ J ⊕ I := ⟨Sum.inl, Sum.inl_injective⟩
  have hrw : (finiteVectorSupport (A *ᵥ w)).card ≤ r := by
    rw [hAw]
    refine (Finset.card_le_card (show finiteVectorSupport d ⊆ Finset.univ.map eJ from ?_)).trans ?_
    · intro j hj
      cases j with
      | inl j => exact Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩
      | inr i => exact False.elim ((mem_finiteVectorSupport.mp hj) (by simp [d, fairSignLeft]))
    · simpa using hr
  let eI : I ↪ J ⊕ I := ⟨Sum.inr, Sum.inr_injective⟩
  have heI : m ≤ (Finset.univ.map eI).card := by simpa using hm
  have ha' : 2 * a ≠ 0 := mul_ne_zero (two_ne_zero_mod_odd_prime hp) ha
  have hc := hgood w hw hrw (Finset.univ.map eI) heI (2 * a) ha'
  rw [norm_character_sum_fairSign]
  simpa only [Finset.prod_map, eI, Function.Embedding.coeFn_mk, w, d] using hc

/-- On a fixed healthy block, the mass of all sign columns failing to make
the default corank change is controlled uniformly in the diagonal entry. -/
public theorem fairSign_corank_exception_le {J I : Type*}
    [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]
    {p : ℕ} [Fact p.Prime] (hp : 2 < p) {A : Matrix (J ⊕ I) (J ⊕ I) (ZMod p)}
    (hA : A.IsSymm) {r m : ℕ} (hr : Fintype.card J ≤ r) (hm : m ≤ Fintype.card I)
    {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (hgood : rankFourierHealthy A r m ε)
    (z : ZMod p) :
    (∑ σ : J ⊕ I → Bool, if
      Module.finrank (ZMod p) (LinearMap.ker
        (symmetricBorder A (fun i => fairSign (σ i)) z).mulVecLin) ≠
          Module.finrank (ZMod p) (LinearMap.ker A.mulVecLin) - 1
      then fairSignWeight (J ⊕ I) else 0) ≤
      (p : ℝ)⁻¹ + Real.sqrt (fairSignWeight J + ε) := by
  classical
  by_cases hdet : A.det = 0
  · obtain ⟨v, hv, hAv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := A)).mpr hdet
    have hm' : m ≤ Fintype.card (J ⊕ I) := by rw [Fintype.card_sum]; omega
    refine (fairSign_corank_exception_le_of_kernel hA hv hAv hm' hε hgood (fun _ => z)).trans ?_
    apply add_le_add_right
    have hsq : ε ^ 2 ≤ fairSignWeight J + ε := by
      nlinarith [mul_nonneg hε (sub_nonneg.mpr hε₁), fairSignWeight_nonneg J]
    exact Real.le_sqrt_of_sq_le hsq
  · have hzero : Module.finrank (ZMod p) (LinearMap.ker A.mulVecLin) = 0 :=
      not_ne_iff.mp ((finrank_ker_ne_zero_iff_det_eq_zero A).not.mpr hdet)
    simp only [hzero, Nat.zero_sub, finrank_ker_ne_zero_iff_det_eq_zero,
      det_symmetricBorder_eq_zero_iff A hdet, eq_comm (a := z)]
    exact fairSign_quadratic_inv_mass_le hp hA hdet hr hm hε hgood z

end Bernoulli
