module

public import Bernoulli.RankSupport
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Expected terminal corank from one-step exceptions

The sample space in this bound may have any nonnegative weights. The main probabilistic
inputs are an upper bound for the weight of pairs of exceptional transitions and a bound
on the weight of outcomes on which the transition estimate is unavailable.
-/

open scoped BigOperators

namespace Bernoulli

/-- If two distinct exceptional transitions have weight at most `q ^ 2`, the terminal
corank has weighted mean at most `q` plus an error for a pair of exceptions or an
unhealthy outcome. The input weights need not be normalized. -/
public theorem weighted_terminal_corank_le {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ) (hweight : ∀ ω, 0 ≤ weight ω)
    (corank : Ω → ℕ → ℕ) (exception : Ω → ℕ → Prop) (unhealthy : Ω → Prop)
    [∀ ω, DecidablePred (exception ω)] [DecidablePred unhealthy]
    (m cap : ℕ) (q r : ℝ)
    (hstep : ∀ ω t, t < m + 1 → corank ω (t + 1) ≤ corank ω t + 1)
    (hdefault : ∀ ω t, t < m + 1 → ¬ unhealthy ω → ¬ exception ω t →
      corank ω (t + 1) = corank ω t - 1)
    (hburn : ∀ ω, corank ω 0 + 1 ≤ m)
    (hcap : ∀ ω, corank ω (m + 1) ≤ cap)
    (hlast : (∑ ω, if exception ω m then weight ω else 0) ≤ q)
    (hpair : ∀ i j, i < m + 1 → j < m + 1 → i ≠ j →
      (∑ ω, if exception ω i ∧ exception ω j then weight ω else 0) ≤ q ^ 2)
    (hhealth : (∑ ω, if unhealthy ω then weight ω else 0) ≤ r) :
    (∑ ω, weight ω * (corank ω (m + 1) : ℝ)) ≤
      q + (cap : ℝ) * (r + ((m + 1 : ℕ) : ℝ) ^ 2 * q ^ 2) := by
  let steps := Finset.range (m + 1)
  let lastTerm := fun ω => if exception ω m then weight ω else 0
  let healthTerm := fun ω => if unhealthy ω then weight ω else 0
  let pairTerm := fun i j ω =>
    if i ≠ j ∧ exception ω i ∧ exception ω j then weight ω else 0
  have last_nonneg (ω : Ω) : 0 ≤ lastTerm ω := by
    dsimp only [lastTerm]
    split
    · exact hweight ω
    · rfl
  have health_nonneg (ω : Ω) : 0 ≤ healthTerm ω := by
    dsimp only [healthTerm]
    split
    · exact hweight ω
    · rfl
  have pair_nonneg (i j : ℕ) (ω : Ω) : 0 ≤ pairTerm i j ω := by
    dsimp only [pairTerm]
    split
    · exact hweight ω
    · rfl
  have cap_nonneg : (0 : ℝ) ≤ cap := Nat.cast_nonneg cap
  have pointwise (ω : Ω) : weight ω * (corank ω (m + 1) : ℝ) ≤
      lastTerm ω + (cap : ℝ) * (healthTerm ω + ∑ i ∈ steps, ∑ j ∈ steps, pairTerm i j ω) := by
    have pairs_nonneg : 0 ≤ ∑ i ∈ steps, ∑ j ∈ steps, pairTerm i j ω :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => pair_nonneg i j ω
    have le_cap_weight : weight ω * (corank ω (m + 1) : ℝ) ≤ (cap : ℝ) * weight ω := by
      rw [mul_comm (cap : ℝ)]
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (hcap ω)) (hweight ω)
    by_cases hunhealthy : unhealthy ω
    · have hw : weight ω ≤ healthTerm ω + ∑ i ∈ steps, ∑ j ∈ steps, pairTerm i j ω := by
        simpa [healthTerm, hunhealthy] using pairs_nonneg
      exact le_cap_weight.trans ((mul_le_mul_of_nonneg_left hw cap_nonneg).trans
        (le_add_of_nonneg_left (last_nonneg ω)))
    · by_cases hcount : (steps.filter (exception ω)).card ≤ 1
      · have hk := terminal_corank_le_indicator_of_at_most_one_exception m (hstep ω)
          (fun t ht => hdefault ω t ht hunhealthy) (hburn ω) hcount
        calc
          _ ≤ weight ω * (Nat.cast (if exception ω m then 1 else 0) : ℝ) :=
            mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hk) (hweight ω)
          _ = lastTerm ω := by
            by_cases he : exception ω m <;> simp [he, lastTerm]
          _ ≤ _ := le_add_of_nonneg_right (mul_nonneg cap_nonneg
            (add_nonneg (health_nonneg ω) pairs_nonneg))
      · have two : ∃ i ∈ steps.filter (exception ω), ∃ j ∈ steps.filter (exception ω), i ≠ j := by
          by_contra h
          apply hcount
          rw [Finset.card_le_one]
          intro i hi j hj
          by_contra hne
          exact h ⟨i, hi, j, hj, hne⟩
        obtain ⟨i, hi, j, hj, hne⟩ := two
        obtain ⟨hi, hei⟩ := Finset.mem_filter.mp hi
        obtain ⟨hj, hej⟩ := Finset.mem_filter.mp hj
        have hw : weight ω ≤ ∑ i ∈ steps, ∑ j ∈ steps, pairTerm i j ω := by
          calc
            weight ω = pairTerm i j ω := by simp [pairTerm, hne, hei, hej]
            _ ≤ ∑ j ∈ steps, pairTerm i j ω := Finset.single_le_sum
              (fun j _ => pair_nonneg i j ω) hj
            _ ≤ _ := Finset.single_le_sum
              (fun i _ => Finset.sum_nonneg fun j _ => pair_nonneg i j ω) hi
        exact le_cap_weight.trans ((mul_le_mul_of_nonneg_left
          (hw.trans (le_add_of_nonneg_left (health_nonneg ω))) cap_nonneg).trans
          (le_add_of_nonneg_left (last_nonneg ω)))
  have pair_total : (∑ i ∈ steps, ∑ j ∈ steps, ∑ ω, pairTerm i j ω) ≤
      ∑ i ∈ steps, ∑ j ∈ steps, q ^ 2 := by
    refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => ?_
    by_cases h : i = j
    · subst j
      simpa [pairTerm] using (sq_nonneg q)
    · simpa [pairTerm, h] using hpair i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) h
  have sum_swap : (∑ ω, ∑ i ∈ steps, ∑ j ∈ steps, pairTerm i j ω) =
      ∑ i ∈ steps, ∑ j ∈ steps, ∑ ω, pairTerm i j ω := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
  calc
    _ ≤ ∑ ω, (lastTerm ω + (cap : ℝ) *
        (healthTerm ω + ∑ i ∈ steps, ∑ j ∈ steps, pairTerm i j ω)) :=
      Finset.sum_le_sum fun ω _ => pointwise ω
    _ = (∑ ω, lastTerm ω) + (cap : ℝ) *
        ((∑ ω, healthTerm ω) + ∑ i ∈ steps, ∑ j ∈ steps, ∑ ω, pairTerm i j ω) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, sum_swap]
    _ ≤ q + (cap : ℝ) * (r + ∑ i ∈ steps, ∑ j ∈ steps, q ^ 2) :=
      add_le_add hlast (mul_le_mul_of_nonneg_left (add_le_add hhealth pair_total) cap_nonneg)
    _ = _ := by simp [steps, nsmul_eq_mul, pow_two, mul_assoc]

end Bernoulli
