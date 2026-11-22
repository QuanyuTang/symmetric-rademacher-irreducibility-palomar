module

public import Bernoulli.PrimeWeights
public import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-! The weighted error contributed by primes dividing an exceptional integer. -/

namespace Bernoulli

/-- The sum of the logarithms of the distinct prime factors of a positive integer. -/
public theorem sum_log_primeFactors_le_log {D : ℕ} (hD : 0 < D) :
    (∑ p ∈ D.primeFactors, Real.log p) ≤ Real.log D := by
  have hpos (p : ℕ) (hp : p ∈ D.primeFactors) : (0 : ℝ) < p :=
    Nat.cast_pos.mpr (Nat.pos_of_mem_primeFactors hp)
  rw [← Real.log_prod (fun p hp => (hpos p hp).ne'), ← Nat.cast_prod]
  apply Real.log_le_log
  · exact_mod_cast Finset.prod_pos (fun p hp => Nat.pos_of_mem_primeFactors hp)
  · exact_mod_cast Nat.le_of_dvd hD (Nat.prod_primeFactors_dvd D)

/-- If two functions in `[0,N]` agree off the primes dividing `D`, their weighted
prime averages differ by at most `3N log(D) / x`. -/
public theorem abs_primeAverage_sub_le_bad_primes {x N : ℝ} (hx : 0 < x) (hN : 0 ≤ N)
    {D : ℕ} (hD : 0 < D) {f g : ℕ → ℝ}
    (hf : ∀ p ∈ primesThrough x, 0 ≤ f p ∧ f p ≤ N)
    (hg : ∀ p ∈ primesThrough x, 0 ≤ g p ∧ g p ≤ N)
    (hgood : ∀ p ∈ primesThrough x, ¬ p ∣ D → f p = g p) :
    |primeAverage x f - primeAverage x g| ≤ 3 * N * Real.log D / x := by
  classical
  let bad := (primesThrough x).filter (fun p => p ∣ D)
  have hsub : bad ⊆ D.primeFactors := by
    intro p hp
    obtain ⟨hp', hpd⟩ := Finset.mem_filter.mp hp
    exact ((mem_primesThrough hx.le).mp hp').1.mem_primeFactors hpd hD.ne'
  have hlog_le : (∑ p ∈ bad, Real.log p) ≤ Real.log D := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p hp _ => ?_)).trans
      (sum_log_primeFactors_le_log hD)
    exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)
  have hdiff : ∀ p ∈ primesThrough x, |(f p - g p) * primeWeight x p| ≤
      if p ∣ D then (3 * N / x) * Real.log p else 0 := by
    intro p hp
    split
    · have hlog : 0 ≤ Real.log p := Real.log_nonneg (by
        exact_mod_cast ((mem_primesThrough hx.le).mp hp).1.one_lt.le)
      have habs : |f p - g p| ≤ N := abs_le.mpr
        ⟨by linarith [(hf p hp).1, (hg p hp).2], by linarith [(hf p hp).2, (hg p hp).1]⟩
      have hw : primeWeight x p ≤ Real.log p * 3 / x :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (weight_le_three _) hlog) hx.le
      rw [abs_mul, abs_of_nonneg (primeWeight_nonneg hx p)]
      calc
        _ ≤ N * (Real.log p * 3 / x) := mul_le_mul habs hw (primeWeight_nonneg hx p) hN
        _ = _ := by ring
    · rename_i hh
      rw [hgood p hp hh, sub_self, zero_mul, abs_zero]
  have hcoef : 0 ≤ 3 * N / x := by positivity
  calc
    |primeAverage x f - primeAverage x g| =
        |∑ p ∈ primesThrough x, (f p - g p) * primeWeight x p| := by
      simp only [primeAverage, ← Finset.sum_sub_distrib, sub_mul]
    _ ≤ ∑ p ∈ primesThrough x, |(f p - g p) * primeWeight x p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ primesThrough x, if p ∣ D then (3 * N / x) * Real.log p else 0 :=
      Finset.sum_le_sum hdiff
    _ = (3 * N / x) * (∑ p ∈ bad, Real.log p) := by
      simp only [bad, Finset.sum_filter, Finset.mul_sum, mul_ite, mul_zero]
    _ ≤ (3 * N / x) * Real.log D := mul_le_mul_of_nonneg_left hlog_le hcoef
    _ = _ := by ring

end Bernoulli
