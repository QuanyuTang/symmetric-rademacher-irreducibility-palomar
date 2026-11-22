module

public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Fourier estimates for finite-field rank transitions

Fourier inversion bounds the atoms of a finite law by its nonzero character averages.
For a sum of independent signs, these averages factor into one-coordinate terms.
-/

open scoped BigOperators

namespace Bernoulli

/-- Nonzero Fourier coefficients bounded by `ε` give a pointwise error at most `ε` from
the uniform mass on `ZMod p`. -/
public theorem norm_sub_uniform_le_of_dft_bound {p : ℕ} [NeZero p]
    (ν : ZMod p → ℂ) (hmass : (∑ z, ν z) = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (h : ∀ a ≠ 0, ‖ZMod.dft ν a‖ ≤ ε) (z : ZMod p) :
    ‖ν z - (p : ℂ)⁻¹‖ ≤ ε := by
  let term : ZMod p → ℂ := fun a => ZMod.stdAddChar (a * z) * ZMod.dft ν a
  let nonzero := Finset.univ.erase (0 : ZMod p)
  have hterm0 : term 0 = 1 := by
    simp [term, ZMod.dft_apply_zero, hmass]
  have hinv : ν z = (p : ℂ)⁻¹ * ∑ a, term a := by
    simpa only [ZMod.invDFT_apply, smul_eq_mul, term] using
      (congrFun (ZMod.dft.symm_apply_apply ν) z).symm
  have hsplit : (∑ a, term a) = (∑ a ∈ nonzero, term a) + 1 := by
    rw [← Finset.sum_erase_add _ term (Finset.mem_univ (0 : ZMod p)), hterm0]
  have hcard : nonzero.card ≤ p := by
    calc
      nonzero.card ≤ (Finset.univ : Finset (ZMod p)).card :=
        Finset.card_le_card (Finset.erase_subset _ _)
      _ = p := by simp [ZMod.card]
  have hcoef : ∀ a ∈ nonzero, ‖term a‖ ≤ ε := by
    intro a ha
    have hne := (Finset.mem_erase.mp ha).1
    simpa [term, norm_mul, ZMod.stdAddChar_apply] using h a hne
  have hp : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  calc
    ‖ν z - (p : ℂ)⁻¹‖ = (p : ℝ)⁻¹ * ‖∑ a ∈ nonzero, term a‖ := by
      rw [hinv, hsplit, mul_add, mul_one, add_sub_cancel_right, norm_mul, norm_inv,
        Complex.norm_natCast]
    _ ≤ (p : ℝ)⁻¹ * ∑ a ∈ nonzero, ‖term a‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr (Nat.cast_nonneg p))
    _ ≤ (p : ℝ)⁻¹ * ((p : ℝ) * ε) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg p))
      calc
        _ ≤ ∑ _a ∈ nonzero, ε := Finset.sum_le_sum hcoef
        _ = (nonzero.card : ℝ) * ε := by simp [nsmul_eq_mul]
        _ ≤ _ := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) hε
    _ = ε := by rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]

/-- The mass of a value in a finite law described by its weights and a random variable. -/
@[expose] public noncomputable def modularMass {Ω : Type*} [Fintype Ω] {p : ℕ}
    (weight : Ω → ℝ) (X : Ω → ZMod p) (z : ZMod p) : ℝ :=
  ∑ ω, if X ω = z then weight ω else 0

/-- The Fourier transform of the law of `X` is its weighted character average. -/
public theorem dft_modularMass {Ω : Type*} [Fintype Ω] {p : ℕ} [NeZero p]
    (weight : Ω → ℝ) (X : Ω → ZMod p) (a : ZMod p) :
    ZMod.dft (fun z => (modularMass weight X z : ℂ)) a =
      ∑ ω, (weight ω : ℂ) * ZMod.stdAddChar (-(X ω * a)) := by
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, modularMass, Complex.ofReal_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  simp only [apply_ite Complex.ofReal, Complex.ofReal_zero, mul_ite, mul_zero]
  simp [eq_comm, mul_comm]

/-- If the nontrivial additive character averages of a finite law are bounded by `ε`,
then every atom is at most `1 / p + ε`. -/
public theorem modularMass_le_of_character_bound {Ω : Type*} [Fintype Ω] {p : ℕ} [NeZero p]
    (weight : Ω → ℝ) (X : Ω → ZMod p) (hweight : (∑ ω, weight ω) = 1)
    {ε : ℝ} (hε : 0 ≤ ε)
    (h : ∀ a ≠ 0, ‖∑ ω, (weight ω : ℂ) * ZMod.stdAddChar (-(X ω * a))‖ ≤ ε)
    (z : ZMod p) : modularMass weight X z ≤ (p : ℝ)⁻¹ + ε := by
  have hsum : (∑ u, (modularMass weight X u : ℂ)) = 1 := by
    rw [← ZMod.dft_apply_zero, dft_modularMass]
    simp [← Complex.ofReal_sum, hweight]
  have hh := norm_sub_uniform_le_of_dft_bound (fun u => (modularMass weight X u : ℂ)) hsum hε
    (fun a ha => by rw [dft_modularMass]; exact h a ha) z
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at hh
  exact sub_le_iff_le_add.mp ((le_abs_self _).trans hh) |>.trans_eq (add_comm _ _)

private theorem stdAddChar_sum {p : ℕ} [NeZero p] {ι : Type*} (s : Finset ι) (f : ι → ZMod p) :
    ZMod.stdAddChar (∑ i ∈ s, f i) = ∏ i ∈ s, ZMod.stdAddChar (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, AddChar.map_add_eq_mul, ih]

/-- A weighted additive character average for independent Boolean signs factors across
the coordinates. A fair sign uses the constant coordinate weight `1 / 2`. -/
public theorem character_sum_independent_signs {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p]
    (weight : ι → Bool → ℂ) (v : ι → ZMod p) (a : ZMod p) :
    (∑ σ : ι → Bool, (∏ i, weight i (σ i)) *
      ZMod.stdAddChar (-((∑ i, (if σ i then 1 else -1) * v i) * a))) =
    ∏ i, ∑ s : Bool, weight i s * ZMod.stdAddChar (-(((if s then 1 else -1) * v i) * a)) := by
  classical
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_mul_distrib, ← stdAddChar_sum, Finset.sum_neg_distrib, Finset.sum_mul]

/-- The average of the two character values of a fair sign is a real cosine. -/
public theorem stdAddChar_fair_sign {p : ℕ} [NeZero p] (j : ZMod p) :
    (∑ s : Bool, (1 / 2 : ℂ) * ZMod.stdAddChar (-((if s then 1 else -1) * j))) =
      (Real.cos (2 * Real.pi * (j.val : ℝ) / p) : ℂ) := by
  let θ := 2 * Real.pi * (j.val : ℝ) / p
  have hpos : ZMod.stdAddChar j = Complex.exp ((θ : ℂ) * Complex.I) := by
    have hj : ((j.val : ℤ) : ZMod p) = j := by simp
    rw [← hj, ZMod.stdAddChar_coe]
    push_cast [θ]
    congr 1
    ring
  have hneg : ZMod.stdAddChar (-j) = Complex.exp (-(θ : ℂ) * Complex.I) := by
    have hj : ((-(j.val : ℤ) : ℤ) : ZMod p) = -j := by simp
    rw [← hj, ZMod.stdAddChar_coe]
    push_cast [θ]
    congr 1
    ring
  change _ = (Real.cos θ : ℂ)
  simp [Fintype.univ_bool, hneg, hpos, Complex.ofReal_cos, Complex.cos]
  ring

/-- The magnitude of the character average of a fair signed sum is the product of the
absolute cosines of the individual angles. -/
public theorem norm_character_sum_fair_signs {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (v : ι → ZMod p) (a : ZMod p) :
    ‖∑ σ : ι → Bool, ((1 / 2 : ℂ) ^ Fintype.card ι) *
      ZMod.stdAddChar (-((∑ i, (if σ i then 1 else -1) * v i) * a))‖ =
      ∏ i, |Real.cos (2 * Real.pi * ((v i * a).val : ℝ) / p)| := by
  have h := character_sum_independent_signs (fun (_i : ι) (_s : Bool) => (1 / 2 : ℂ)) v a
  simp only [Finset.prod_const, Finset.card_univ, mul_assoc, stdAddChar_fair_sign] at h
  rw [h, Complex.norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs, mul_assoc]

end Bernoulli
