module

public import Bernoulli.RankCosineMoment
public import Bernoulli.RankVectorCount
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.Prod

/-!
# Counting vectors with a large Fourier coefficient on some set of coordinates

The bound ranges over all retained coordinate sets of the required size and all
nonzero frequencies. Its union factor is at most `2 ^ card ι * p`.
-/

open scoped BigOperators

namespace Bernoulli

/-- Count vectors with a large cosine product at some nonzero frequency and some
set of at least `m` coordinates. One may take `m = (3 * Fintype.card ι + 3) / 4`
for the sets retaining at least three quarters of the coordinates. -/
public theorem card_bad_cos_vectors_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [Fact p.Prime] (k m : ℕ) (hp : 2 * k < p)
    (bad : Finset (ι → ZMod p)) {a b : ℝ} (ha : 0 < a) (hb₀ : 0 ≤ b) (hb₁ : b ≤ 1)
    (hscale : 1 ≤ ((k : ℝ) + 1) * b ^ 2)
    (hbad : ∀ w ∈ bad, ∃ S : Finset ι, m ≤ S.card ∧ ∃ frequency : ZMod p, frequency ≠ 0 ∧
      a ≤ ∏ i ∈ S, |Real.cos (2 * Real.pi * ((w i * frequency).val : ℝ) / p)|) :
    (bad.card : ℝ) ≤ ((2 : ℝ) ^ Fintype.card ι * (p : ℝ)) *
      ((p : ℝ) ^ Fintype.card ι * b ^ m / a ^ (2 * k)) := by
  classical
  let g : ZMod p → ℝ := fun u => |Real.cos (2 * Real.pi * (u.val : ℝ) / p)|
  let bound := (p : ℝ) ^ Fintype.card ι * b ^ m / a ^ (2 * k)
  have bound_nonneg : 0 ≤ bound := by
    exact div_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg p) _) (pow_nonneg hb₀ _))
      (pow_nonneg ha.le _)
  let badAt : Finset ι × ZMod p → Finset (ι → ZMod p) := fun label =>
    if m ≤ label.1.card ∧ label.2 ≠ 0 then
      bad.filter (fun w => a ≤ ∏ i ∈ label.1, g (w i * label.2))
    else ∅
  have covered : bad ⊆ (Finset.univ : Finset (Finset ι × ZMod p)).biUnion badAt := by
    intro w hw
    obtain ⟨S, hS, frequency, hf, hproduct⟩ := hbad w hw
    refine Finset.mem_biUnion.mpr ⟨(S, frequency), Finset.mem_univ _, ?_⟩
    have hprod : a ≤ ∏ i ∈ S, g (w i * frequency) := hproduct
    simp [badAt, hS, hf, hw, hprod]
  have hmoment : (∑ u, g u ^ (2 * k)) ≤ (Fintype.card (ZMod p) : ℝ) * b := by
    rw [ZMod.card]
    exact sum_abs_cos_even_pow_le k hp hb₀ hscale
  have count_at_label (label : Finset ι × ZMod p) : ((badAt label).card : ℝ) ≤ bound := by
    by_cases h : m ≤ label.1.card ∧ label.2 ≠ 0
    · have hprod (w : ι → ZMod p) (hw : w ∈ badAt label) :
          a ≤ ∏ i ∈ label.1, g (w i * label.2) := by
        rw [show badAt label = bad.filter (fun v => a ≤ ∏ i ∈ label.1, g (v i * label.2)) by
          simp [badAt, h]] at hw
        exact (Finset.mem_filter.mp hw).2
      have hc := card_le_of_frequency_prod_ge_of_moment label.1 g (fun _ => abs_nonneg _)
        (badAt label) (2 * k) ha h.2 hprod hmoment
      rw [ZMod.card] at hc
      refine hc.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hb₀ hb₁ h.1)
          (pow_nonneg (Nat.cast_nonneg p) _)) (pow_nonneg ha.le _))
    · simpa [badAt, h] using bound_nonneg
  calc
    (bad.card : ℝ) ≤ ((Finset.univ : Finset (Finset ι × ZMod p)).biUnion badAt).card :=
      Nat.cast_le.mpr (Finset.card_le_card covered)
    _ ≤ ∑ label, ((badAt label).card : ℝ) := by
      exact_mod_cast (Finset.card_biUnion_le (s := Finset.univ) (t := badAt))
    _ ≤ ∑ _label : Finset ι × ZMod p, bound := Finset.sum_le_sum fun label _ => count_at_label label
    _ = _ := by
      simp [bound, nsmul_eq_mul, Fintype.card_prod, ZMod.card, Nat.cast_mul, Nat.cast_pow]

end Bernoulli
