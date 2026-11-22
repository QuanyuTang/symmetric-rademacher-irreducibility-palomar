module

public import Bernoulli.RankSparse
import Mathlib.Tactic

/-! Exponential estimates from the sparse-support union bound. -/

namespace Bernoulli

/-- The support-count bound decays exponentially when the support counts
consume at most one eighth of the dimension in the exponent and at least
three quarters of the rows can still be tested. -/
public theorem sparse_mulVec_bound_le_exp {n p : ℕ}
    (hn : 0 < n) (hp : 2 < p) (d r : ℕ) (hrows : 4 * (d + r) ≤ n)
    (hcount : (Real.log ((d : ℝ) + 1) + d * Real.log ((n : ℝ) * p)) +
      (Real.log ((r : ℝ) + 1) + r * Real.log n) ≤ (n : ℝ) / 8) :
    (((d : ℝ) + 1) * ((n : ℝ) * p) ^ d) *
      (((r : ℝ) + 1) * (n : ℝ) ^ r * (1 / 2 : ℝ) ^ (n - d - r)) ≤
      Real.exp (-(n : ℝ) / 4) := by
  let m := n - d - r
  let A := Real.log ((d : ℝ) + 1) + d * Real.log ((n : ℝ) * p)
  let B := Real.log ((r : ℝ) + 1) + r * Real.log n
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hA : Real.exp A = ((d : ℝ) + 1) * ((n : ℝ) * p) ^ d := by
    dsimp only [A]
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (show 0 < (d : ℝ) + 1 by positivity),
      Real.exp_log (mul_pos hn' hp')]
  have hB : Real.exp B = ((r : ℝ) + 1) * (n : ℝ) ^ r := by
    dsimp only [B]
    rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log (show 0 < (r : ℝ) + 1 by positivity),
      Real.exp_log hn']
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)⁻¹) (by positivity)
    rw [Real.log_inv] at h
    norm_num at h ⊢
    linarith
  have hkeep : 3 * (n : ℝ) ≤ 4 * (m : ℝ) := by
    exact_mod_cast (show 3 * n ≤ 4 * m by dsimp [m]; omega)
  have herr : A + B - (m : ℝ) * Real.log 2 ≤ -(n : ℝ) / 4 := by
    change A + B ≤ (n : ℝ) / 8 at hcount
    have h := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg m)
    linarith
  have hprod : Real.exp (A + B - (m : ℝ) * Real.log 2) =
      (((d : ℝ) + 1) * ((n : ℝ) * p) ^ d) *
        (((r : ℝ) + 1) * (n : ℝ) ^ r * (1 / 2 : ℝ) ^ m) := by
    rw [Real.exp_sub, Real.exp_add, hA, hB, Real.exp_nat_mul, Real.exp_log (show (0 : ℝ) < 2 by norm_num),
      one_div, inv_pow, div_eq_mul_inv, mul_assoc]
  exact hprod ▸ Real.exp_le_exp.mpr herr

end Bernoulli
