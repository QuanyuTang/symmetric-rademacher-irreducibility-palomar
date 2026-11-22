module

public import Bernoulli.HalaszIntegral
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The finite-field Halász estimate

An even cosine moment counts signed zero relations. Combined with Fourier
inversion and the level-set bound, it controls the concentration of a sum of
independent fair signs over a prime field.
-/

open scoped BigOperators
namespace Bernoulli

/-- The number of ordered signed zero relations of the specified length,
with repetitions of coordinate indices allowed. -/
@[expose] public noncomputable def signedZeroRelationCount {ι : Type*} [Fintype ι]
    {p : ℕ} (v : ι → ZMod p) (m : ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun t : Fin m → ι × Bool =>
    (∑ j, (if (t j).2 then 1 else -1) * v (t j).1) = 0).card

/-- The large energy level has density bounded by the normalized count of
signed zero relations of length twice the moment parameter. -/
public theorem card_characterEnergyLevel_le_relationCount {ι : Type*} [Fintype ι]
    {p : ℕ} [NeZero p] (v : ι → ZMod p) {k : ℕ} (hk : 0 < k) {M : ℝ}
    (hM : 0 < M) (hsize : 16 * (k : ℝ) * M ≤ Fintype.card ι) :
    ((characterEnergyLevel v (8 * M)).card : ℝ) / p ≤
      2 * (signedZeroRelationCount v (2 * k) : ℝ) / (2 * (Fintype.card ι : ℝ)) ^ (2 * k) := by
  classical
  let N : ℝ := Fintype.card ι
  let m : ℕ := 2 * k
  let S (r : ZMod p) := ∑ i, Real.cos (2 * Real.pi * ((r * v i).val : ℝ) / p)
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h16 : 16 * M ≤ N := by
    exact (by nlinarith [mul_nonneg (sub_nonneg.mpr hk') hM.le] :
      16 * M ≤ 16 * (k : ℝ) * M).trans hsize
  have hN : 0 < N := by linarith
  have hfour : 4 * M ≤ N := by linarith
  have hsmall : (m : ℝ) * (4 * M / N) ≤ 1 / 2 := by
    rw [← mul_div_assoc, div_le_iff₀ hN]
    dsimp only [m]
    push_cast
    change 16 * (k : ℝ) * M ≤ N at hsize
    nlinarith
  have hbase : 1 / 2 ≤ (1 - 4 * M / N) ^ m := by
    have hdiv : 4 * M / N ≤ 1 := (div_le_iff₀ hN).mpr (by simpa using hfour)
    have h := one_add_mul_le_pow (a := -(4 * M / N)) (by linarith) m
    rw [← sub_eq_add_neg] at h
    linarith
  have hpow : N ^ m / 2 ≤ (N - 4 * M) ^ m := by
    calc
      _ ≤ N ^ m * (1 - 4 * M / N) ^ m := by
        rw [div_eq_mul_inv, ← one_div]
        exact mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = _ := by
        rw [← mul_pow, mul_sub, mul_one, mul_div_cancel₀ _ hN.ne']
  have hlevel (r : ZMod p) (hr : r ∈ characterEnergyLevel v (8 * M)) :
      N ^ m / 2 ≤ S r ^ m := by
    have he := mem_characterEnergyLevel.mp hr
    exact hpow.trans (pow_le_pow_left₀ (sub_nonneg.mpr hfour)
      (by dsimp [S]; rw [sum_cos_eq_characterEnergy]; linarith) _)
  have hsum :
      ((characterEnergyLevel v (8 * M)).card : ℝ) * (N ^ m / 2) ≤ ∑ r, S r ^ m := by
    calc
      _ = ∑ r ∈ characterEnergyLevel v (8 * M), N ^ m / 2 := by
        simp [nsmul_eq_mul]
      _ ≤ ∑ r ∈ characterEnergyLevel v (8 * M), S r ^ m := Finset.sum_le_sum hlevel
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun r _ _ => by
        rw [show m = 2 * k by rfl, pow_mul]
        positivity
  have hp : 0 < (p : ℝ) := by exact_mod_cast NeZero.pos p
  have hNm : 0 < N ^ m := pow_pos hN _
  have hmoment : (∑ r, S r ^ m) / p = (signedZeroRelationCount v m : ℝ) / (2 : ℝ) ^ m := by
    simpa only [S, signedZeroRelationCount] using average_cos_sum_pow_eq_signed_relation_count v m
  change _ ≤ 2 * (signedZeroRelationCount v m : ℝ) / (2 * N) ^ m
  calc
    _ ≤ ((2 / N ^ m) * ∑ r, S r ^ m) / p := by
      apply div_le_div_of_nonneg_right _ hp.le
      rw [div_mul_eq_mul_div, le_div_iff₀ hNm]
      calc
        _ = 2 * (((characterEnergyLevel v (8 * M)).card : ℝ) * (N ^ m / 2)) := by ring
        _ ≤ 2 * ∑ r, S r ^ m := mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = (2 / N ^ m) * ((∑ r, S r ^ m) / p) := by ring
    _ = _ := by rw [hmoment, mul_pow]; ring

/-- The finite-field Halász bound with an explicit constant and with the
uniform atom kept separate from the contribution of signed zero relations. -/
public theorem modularMass_fair_signs_le_halasz {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [Fact p.Prime] (hp : 2 < p) (v : ι → ZMod p) (z : ZMod p)
    {k : ℕ} (hk : 0 < k) {M : ℝ} (hM : 0 < M)
    (hsupport : 4 * M < ((Finset.univ.filter fun i => v i ≠ 0).card : ℝ))
    (hsize : 16 * (k : ℝ) * M ≤ Fintype.card ι) :
    modularMass (fun _ : ι → Bool => (1 / 2 : ℝ) ^ Fintype.card ι)
      (fun σ => ∑ i, (if σ i then 1 else -1) * v i) z ≤
        1 / (p : ℝ) +
          8 * (signedZeroRelationCount v (2 * k) : ℝ) /
            ((2 * (Fintype.card ι : ℝ)) ^ (2 * k) * Real.sqrt M) +
          Real.exp (-M) := by
  have hproper : (characterEnergyLevel v (8 * M)).card < p :=
    card_characterEnergyLevel_lt (by linarith)
  have hmoment := card_characterEnergyLevel_le_relationCount v hk hM hsize
  have hp' : 0 < (p : ℝ) := by exact_mod_cast NeZero.pos p
  calc
    _ ≤ (∑ r, Real.exp (-characterEnergy v r / 8)) / p :=
      modularMass_fair_signs_le_exp_energy hp v z
    _ ≤ (1 + 4 * ((characterEnergyLevel v (8 * M)).card : ℝ) / Real.sqrt M +
        (p : ℝ) * Real.exp (-M)) / p :=
      div_le_div_of_nonneg_right (sum_exp_characterEnergy_le v Fact.out hM hproper) hp'.le
    _ = 1 / (p : ℝ) + (4 / Real.sqrt M) *
        (((characterEnergyLevel v (8 * M)).card : ℝ) / p) + Real.exp (-M) := by
      field_simp [hp'.ne', (Real.sqrt_pos.mpr hM).ne']
    _ ≤ 1 / (p : ℝ) + (4 / Real.sqrt M) *
        (2 * (signedZeroRelationCount v (2 * k) : ℝ) /
          (2 * (Fintype.card ι : ℝ)) ^ (2 * k)) + Real.exp (-M) :=
      add_le_add (add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hmoment (by positivity))) le_rfl
    _ = _ := by ring

end Bernoulli
