module

public import Bernoulli.PrimeWeights
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic

/-! Bounding the contribution of powers of rational primes with exponent at least two. -/

namespace Bernoulli

/-- Only `p ≤ √x` and `2 ≤ j ≤ log x / log p` can contribute to the weight at `p^j`. -/
@[expose] public noncomputable def primePowerSum (x : ℝ) (a : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ primesThrough (Real.sqrt x),
    ∑ j ∈ Finset.Icc 2 ⌊Real.log x / Real.log p⌋₊,
      a p j * weight ((p : ℝ) ^ j / x)

public theorem primePowerSum_bounds {x d : ℝ} (hx : 1 ≤ x) (hd : 0 ≤ d)
    {a : ℕ → ℕ → ℝ} (hcoeff : ∀ p, p.Prime → ∀ j, 2 ≤ j →
      0 ≤ a p j ∧ a p j ≤ d * Real.log p) :
    0 ≤ primePowerSum x a ∧ primePowerSum x a ≤ 3 * d * Real.sqrt x * Real.log x := by
  have hsqrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hprime {p : ℕ} (hp : p ∈ primesThrough (Real.sqrt x)) : p.Prime :=
    ((mem_primesThrough hsqrt).mp hp).1
  constructor
  · apply Finset.sum_nonneg
    intro p hp
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (hcoeff p (hprime hp) j (Finset.mem_Icc.mp hj).1).1 (weight_nonneg _)
  · have hcard : (↑(primesThrough (Real.sqrt x)).card : ℝ) ≤ Real.sqrt x := by
      have hsubset : primesThrough (Real.sqrt x) ⊆ Finset.Icc 1 ⌊Real.sqrt x⌋₊ := by
        intro p hp
        obtain ⟨hp, hbound⟩ := (mem_primesThrough hsqrt).mp hp
        exact Finset.mem_Icc.mpr ⟨hp.one_lt.le, (Nat.le_floor_iff hsqrt).mpr hbound⟩
      have h := Finset.card_le_card hsubset
      have hcast : ((primesThrough (Real.sqrt x)).card : ℝ) ≤ (⌊Real.sqrt x⌋₊ : ℕ) := by
        exact_mod_cast (show (primesThrough (Real.sqrt x)).card ≤ ⌊Real.sqrt x⌋₊ by simpa using h)
      exact hcast.trans (Nat.floor_le hsqrt)
    calc
      primePowerSum x a ≤ ∑ p ∈ primesThrough (Real.sqrt x), 3 * d * Real.log x := by
        apply Finset.sum_le_sum
        intro p hp
        have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast (hprime hp).one_lt)
        have hquot : 0 ≤ Real.log x / Real.log p := div_nonneg hlogx hlogp.le
        let J := Finset.Icc 2 ⌊Real.log x / Real.log p⌋₊
        have hJ : (J.card : ℝ) ≤ Real.log x / Real.log p := by
          have hJnat : J.card ≤ ⌊Real.log x / Real.log p⌋₊ := by
            simp [J, Nat.card_Icc]
          exact (by exact_mod_cast hJnat : (J.card : ℝ) ≤ (⌊Real.log x / Real.log p⌋₊ : ℕ)).trans
            (Nat.floor_le hquot)
        change (∑ j ∈ J, a p j * weight ((p : ℝ) ^ j / x)) ≤ 3 * d * Real.log x
        calc
          _ ≤ ∑ _j ∈ J, d * Real.log p * 3 := by
            apply Finset.sum_le_sum
            intro j hj
            obtain ⟨h₀, h₁⟩ := hcoeff p (hprime hp) j (Finset.mem_Icc.mp hj).1
            exact mul_le_mul h₁ (weight_le_three _) (weight_nonneg _) (mul_nonneg hd hlogp.le)
          _ = (J.card : ℝ) * (d * Real.log p * 3) := by simp
          _ ≤ (Real.log x / Real.log p) * (d * Real.log p * 3) :=
            mul_le_mul_of_nonneg_right hJ (by positivity)
          _ = _ := by field_simp
      _ = (↑(primesThrough (Real.sqrt x)).card : ℝ) * (3 * d * Real.log x) := by simp
      _ ≤ Real.sqrt x * (3 * d * Real.log x) := mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = _ := by ring

end Bernoulli
