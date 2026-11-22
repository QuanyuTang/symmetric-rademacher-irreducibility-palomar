module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic

/-! The nonnegative compactly supported prime weights used in the factor-count argument. -/

namespace Bernoulli

/-- The smoothing weight on the interval `[1/2, 1]`, extended by zero. -/
@[expose] public noncomputable def weight (u : ℝ) : ℝ :=
  if (1 / 2 : ℝ) ≤ u ∧ u ≤ 1 then 48 * (u - 1 / 2) * (1 - u) else 0

public theorem weight_nonneg (u : ℝ) : 0 ≤ weight u := by
  unfold weight
  split
  · rename_i h
    exact mul_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr h.1)) (sub_nonneg.mpr h.2)
  · exact le_rfl

public theorem weight_le_three (u : ℝ) : weight u ≤ 3 := by
  unfold weight
  split
  · nlinarith [sq_nonneg (u - 3 / 4)]
  · norm_num

public theorem weight_pos_iff (u : ℝ) : 0 < weight u ↔ (1 / 2 : ℝ) < u ∧ u < 1 := by
  unfold weight
  split
  · rename_i h
    constructor
    · intro hp
      constructor
      · refine lt_of_le_of_ne h.1 ?_
        intro hu
        simp [← hu] at hp
      · refine lt_of_le_of_ne h.2 ?_
        intro hu
        simp [hu] at hp
    · intro hp
      exact mul_pos (mul_pos (by norm_num) (sub_pos.mpr hp.1)) (sub_pos.mpr hp.2)
  · rename_i h
    simp only [lt_self_iff_false, false_iff]
    exact fun hp => h ⟨hp.1.le, hp.2.le⟩

/-- The finite set of rational primes at most the scale `x`. -/
@[expose] public noncomputable def primesThrough (x : ℝ) : Finset ℕ := by
  classical
  exact (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime

public theorem mem_primesThrough {x : ℝ} {p : ℕ} (hx : 0 ≤ x) :
    p ∈ primesThrough x ↔ p.Prime ∧ (p : ℝ) ≤ x := by
  classical
  rw [primesThrough, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff,
    Nat.le_floor_iff hx, and_comm]

/-- The real coefficient of the prime `p` in the normalized average at scale `x`. -/
@[expose] public noncomputable def primeWeight (x : ℝ) (p : ℕ) : ℝ :=
  Real.log p * weight (p / x) / x

public theorem primeWeight_nonneg {x : ℝ} (hx : 0 < x) (p : ℕ) : 0 ≤ primeWeight x p := by
  unfold primeWeight
  apply div_nonneg (mul_nonneg ?_ (weight_nonneg _)) hx.le
  by_cases hp : p = 0
  · simp [hp]
  · apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hp

public theorem support_of_primeWeight_pos {x : ℝ} (hx : 0 < x) {p : ℕ}
    (hp : 0 < primeWeight x p) : x / 2 < (p : ℝ) ∧ (p : ℝ) < x := by
  have hw : 0 < weight ((p : ℝ) / x) := by
    have hne : weight ((p : ℝ) / x) ≠ 0 := by
      intro h
      simp [primeWeight, h] at hp
    exact lt_of_le_of_ne (weight_nonneg _) (Ne.symm hne)
  obtain ⟨hl, hr⟩ := (weight_pos_iff _).mp hw
  exact ⟨by simpa [div_eq_mul_inv, mul_comm] using (lt_div_iff₀ hx).mp hl,
    by simpa using (div_lt_iff₀ hx).mp hr⟩

/-- The normalized weighted sum of a function on rational primes. -/
@[expose] public noncomputable def primeAverage (x : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ p ∈ primesThrough x, f p * primeWeight x p

public theorem primeAverage_mono {x : ℝ} (hx : 0 < x) {f g : ℕ → ℝ}
    (h : ∀ p ∈ primesThrough x, 0 < primeWeight x p → f p ≤ g p) :
    primeAverage x f ≤ primeAverage x g := by
  apply Finset.sum_le_sum
  intro p hp
  rcases (primeWeight_nonneg hx p).lt_or_eq with hpw | hpw
  · exact mul_le_mul_of_nonneg_right (h p hp hpw) hpw.le
  · simp [← hpw]

end Bernoulli
