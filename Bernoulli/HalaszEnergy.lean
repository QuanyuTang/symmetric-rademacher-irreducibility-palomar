module

public import Bernoulli.SignedRelations
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Character energy of finite-field frequencies

The squared chordal distances from the additive character values to one give
both a quadratic bound for the Fourier coefficients and a real cosine moment.
-/

open scoped BigOperators
namespace Bernoulli

/-- The sum of the squared chordal distances of the coordinate characters to one. -/
@[expose] public noncomputable def characterEnergy {ι : Type*} [Fintype ι]
    {p : ℕ} [NeZero p] (v : ι → ZMod p) (r : ZMod p) : ℝ :=
  ∑ i, ‖ZMod.stdAddChar (r * v i) - 1‖ ^ 2

public theorem characterEnergy_nonneg {ι : Type*} [Fintype ι] {p : ℕ} [NeZero p]
    (v : ι → ZMod p) (r : ZMod p) : 0 ≤ characterEnergy v r :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

@[simp] public theorem characterEnergy_zero {ι : Type*} [Fintype ι] {p : ℕ} [NeZero p]
    (v : ι → ZMod p) : characterEnergy v 0 = 0 := by
  simp [characterEnergy]

private theorem norm_stdAddChar {p : ℕ} [NeZero p] (x : ZMod p) :
    ‖ZMod.stdAddChar x‖ = 1 := by
  simp [ZMod.stdAddChar_apply]

private theorem squared_chord_eq {p : ℕ} [NeZero p] (x : ZMod p) :
    ‖ZMod.stdAddChar x - 1‖ ^ 2 = 2 - 2 * (ZMod.stdAddChar x).re := by
  rw [Complex.sq_norm, Complex.normSq_sub, Complex.normSq_eq_norm_sq, norm_stdAddChar]
  norm_num

private theorem re_stdAddChar {p : ℕ} [NeZero p] (x : ZMod p) :
    (ZMod.stdAddChar x).re = Real.cos (2 * Real.pi * (x.val : ℝ) / p) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply, ← Complex.exp_ofReal_mul_I_re]
  congr 2
  push_cast
  ring

/-- The cosine sum is the number of coordinates minus half the character energy. -/
public theorem sum_cos_eq_characterEnergy {ι : Type*} [Fintype ι] {p : ℕ} [NeZero p]
    (v : ι → ZMod p) (r : ZMod p) :
    (∑ i, Real.cos (2 * Real.pi * ((r * v i).val : ℝ) / p)) =
      (Fintype.card ι : ℝ) - characterEnergy v r / 2 := by
  unfold characterEnergy
  simp_rw [squared_chord_eq, re_stdAddChar, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The average energy is twice the size of the support. -/
public theorem sum_characterEnergy {ι : Type*} [Fintype ι] {p : ℕ} [NeZero p]
    (v : ι → ZMod p) :
    (∑ r, characterEnergy v r) =
      2 * (p : ℝ) * ((Finset.univ.filter fun i => v i ≠ 0).card : ℝ) := by
  classical
  unfold characterEnergy
  rw [Finset.sum_comm]
  calc
    _ = ∑ i, if v i ≠ 0 then 2 * (p : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : v i = 0
      · simp [hi]
      · have h := AddChar.sum_mulShift (v i) (ZMod.isPrimitive_stdAddChar p)
        have hzero : (∑ r : ZMod p, (ZMod.stdAddChar (r * v i)).re) = 0 := by
          have h' : (∑ r : ZMod p, ZMod.stdAddChar (r * v i)) = 0 := by
            simpa [hi] using h
          simpa only [Complex.re_sum, Complex.zero_re] using congrArg Complex.re h'
        simp_rw [squared_chord_eq, Finset.sum_sub_distrib, ← Finset.mul_sum, hzero]
        simp [hi, ZMod.card, nsmul_eq_mul, mul_comm]
    _ = _ := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

private theorem chord_add_le {p : ℕ} [NeZero p] (x y : ZMod p) :
    ‖ZMod.stdAddChar (x + y) - 1‖ ≤
      ‖ZMod.stdAddChar x - 1‖ + ‖ZMod.stdAddChar y - 1‖ := by
  rw [AddChar.map_add_eq_mul, show
    ZMod.stdAddChar x * ZMod.stdAddChar y - 1 =
      (ZMod.stdAddChar x - 1) + ZMod.stdAddChar x * (ZMod.stdAddChar y - 1) by ring]
  simpa only [norm_mul, norm_stdAddChar, one_mul] using
    norm_add_le (ZMod.stdAddChar x - 1)
      (ZMod.stdAddChar x * (ZMod.stdAddChar y - 1))

/-- The square root of the energy is subadditive. -/
public theorem sqrt_characterEnergy_add_le {ι : Type*} [Fintype ι] {p : ℕ} [NeZero p]
    (v : ι → ZMod p) (r s : ZMod p) :
    Real.sqrt (characterEnergy v (r + s)) ≤
      Real.sqrt (characterEnergy v r) + Real.sqrt (characterEnergy v s) := by
  let a (i : ι) := ‖ZMod.stdAddChar (r * v i) - 1‖
  let b (i : ι) := ‖ZMod.stdAddChar (s * v i) - 1‖
  have hle : characterEnergy v (r + s) ≤ ∑ i, (a i + b i) ^ 2 := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [add_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (chord_add_le _ _) _
  refine Real.sqrt_le_iff.mpr ⟨by positivity, hle.trans ?_⟩
  calc
    _ = (∑ i, a i ^ 2) + (∑ i, b i ^ 2) + 2 * ∑ i, a i * b i := by
      simp_rw [add_sq, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
      ring
    _ ≤ _ := by
      have hcross := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ a b
      change (∑ i, a i * b i) ≤
        Real.sqrt (characterEnergy v r) * Real.sqrt (characterEnergy v s) at hcross
      change characterEnergy v r + characterEnergy v s + _ ≤ _
      rw [add_sq, Real.sq_sqrt (characterEnergy_nonneg v r),
        Real.sq_sqrt (characterEnergy_nonneg v s)]
      linarith

private theorem abs_cos_le_exp_chord {p : ℕ} [NeZero p] (x : ZMod p) :
    |Real.cos (2 * Real.pi * (x.val : ℝ) / p)| ≤
      Real.exp (-‖ZMod.stdAddChar (x + x) - 1‖ ^ 2 / 8) := by
  let z := ZMod.stdAddChar x
  have hz : ‖z‖ = 1 := norm_stdAddChar x
  have hnorm := Complex.sq_norm_sub_sq_re z
  rw [hz] at hnorm
  have henergy : ‖ZMod.stdAddChar (x + x) - 1‖ ^ 2 = 4 * (1 - z.re ^ 2) := by
    rw [squared_chord_eq, AddChar.map_add_eq_mul]
    change 2 - 2 * (z * z).re = _
    rw [Complex.mul_re]
    nlinarith
  have hexp := Real.add_one_le_exp (-‖ZMod.stdAddChar (x + x) - 1‖ ^ 2 / 4)
  rw [← re_stdAddChar, ← sq_le_sq₀ (abs_nonneg _) (Real.exp_nonneg _), sq_abs,
    pow_two (Real.exp _), ← Real.exp_add]
  change z.re ^ 2 ≤ _
  rw [show -‖ZMod.stdAddChar (x + x) - 1‖ ^ 2 / 8 +
      -‖ZMod.stdAddChar (x + x) - 1‖ ^ 2 / 8 =
      -‖ZMod.stdAddChar (x + x) - 1‖ ^ 2 / 4 by ring]
  linarith

/-- Every atom of a sum of independent fair signs is bounded by a sum of
exponentials of the frequency energies. -/
public theorem modularMass_fair_signs_le_exp_energy {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [Fact p.Prime] (hp : 2 < p) (v : ι → ZMod p) (z : ZMod p) :
    modularMass (fun _ : ι → Bool => (1 / 2 : ℝ) ^ Fintype.card ι)
      (fun σ => ∑ i, (if σ i then 1 else -1) * v i) z ≤
        (∑ r, Real.exp (-characterEnergy v r / 8)) / p := by
  classical
  let ν : ZMod p → ℝ := modularMass (fun _ : ι → Bool => (1 / 2 : ℝ) ^ Fintype.card ι)
      (fun σ => ∑ i, (if σ i then 1 else -1) * v i)
  let term (r : ZMod p) := ZMod.stdAddChar (r * z) * ZMod.dft (fun u => (ν u : ℂ)) r
  have hinv : (ν z : ℂ) = (p : ℂ)⁻¹ * ∑ r, term r := by
    simpa only [ZMod.invDFT_apply, smul_eq_mul, term] using
      (congrFun (ZMod.dft.symm_apply_apply (fun u => (ν u : ℂ))) z).symm
  have hterm (r : ZMod p) : ‖term r‖ ≤ Real.exp (-characterEnergy v (2 * r) / 8) := by
    simp only [term, norm_mul, norm_stdAddChar, one_mul, ν, dft_modularMass,
      Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat,
      norm_character_sum_fair_signs]
    calc
      _ ≤ ∏ i, Real.exp (-‖ZMod.stdAddChar (v i * r + v i * r) - 1‖ ^ 2 / 8) :=
        Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun _ _ => abs_cos_le_exp_chord _)
      _ = _ := by
        rw [← Real.exp_sum]
        congr 1
        simp_rw [characterEnergy, two_mul, add_mul, mul_comm r, ← Finset.sum_neg_distrib,
          ← Finset.sum_div]
  have htwo : (2 : ZMod p) ≠ 0 := by
    change ((2 : ℕ) : ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero, Nat.mod_eq_of_lt hp]
    decide
  change ν z ≤ _
  calc
    ν z ≤ ‖(ν z : ℂ)‖ := by simp [le_abs_self]
    _ = (p : ℝ)⁻¹ * ‖∑ r, term r‖ := by
      rw [hinv, norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (p : ℝ)⁻¹ * ∑ r, Real.exp (-characterEnergy v (2 * r) / 8) :=
      mul_le_mul_of_nonneg_left
        ((norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => hterm r)) (by positivity)
    _ = _ := by
      rw [div_eq_inv_mul]
      apply congrArg ((p : ℝ)⁻¹ * ·)
      exact Equiv.sum_comp (Equiv.mulLeft₀ (2 : ZMod p) htwo)
        (fun r => Real.exp (-characterEnergy v r / 8))

end Bernoulli
