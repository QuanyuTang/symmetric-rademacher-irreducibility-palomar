module

public import Bernoulli.RankRelationLevels
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The relation-count scales

Taking the moment parameter to be a square lets the base size be its cube
without fractional powers in the estimate for repeated indices.
-/

namespace Bernoulli

/-- At the chosen moment and subset sizes, the repeated-index contribution
is exponentially small in the moment parameter. -/
public theorem repeatedIndexRatio_le_pow (s : ℕ) (hs : 8 ≤ s) :
    repeatedIndexRatio (s ^ 2) (s ^ 6) ≤ (1 / 2 : ℝ) ^ (s ^ 2) := by
  let k := s ^ 2
  let d := 101 * k / 100
  let z : ℝ := s
  have hz : 0 < z := by
    dsimp only [z]
    exact_mod_cast (show 0 < s by omega)
  have hz8 : 8 ≤ z := by
    dsimp only [z]
    exact_mod_cast hs
  have hd : (d : ℝ) ≤ 2 * z ^ 2 := by
    have hd' : d ≤ 2 * s ^ 2 := by dsimp [d, k]; omega
    dsimp only [z]
    exact_mod_cast hd'
  have hexp : 6 * d + 4 * k ≤ 11 * k := by dsimp [d]; omega
  have hchoose : (((s ^ 6).choose d : ℕ) : ℝ) ≤ (z ^ 6) ^ d := by
    dsimp only [z]
    exact_mod_cast Nat.choose_le_pow (s ^ 6) d
  unfold repeatedIndexRatio
  change (((s ^ 6).choose d : ℕ) : ℝ) * (2 * (d : ℝ)) ^ (2 * k) /
      (2 * ((s ^ 6 : ℕ) : ℝ)) ^ (2 * k) ≤ _
  rw [Nat.cast_pow]
  change _ / (2 * z ^ 6) ^ (2 * k) ≤ (1 / 2 : ℝ) ^ k
  calc
    _ ≤ (z ^ 6) ^ d * (2 * (2 * z ^ 2)) ^ (2 * k) / (2 * z ^ 6) ^ (2 * k) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul hchoose (pow_le_pow_left₀ (by positivity)
        (mul_le_mul_of_nonneg_left hd (by norm_num)) _) (by positivity) (by positivity)
    _ = (4 : ℝ) ^ k * z ^ (6 * d + 4 * k) / z ^ (12 * k) := by
      rw [mul_div_assoc, ← div_pow, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0),
        div_pow, ← mul_div_assoc, mul_pow, ← pow_mul z 6 d,
        ← pow_mul z 2 (2 * k), ← pow_mul z 6 (2 * k),
        show 2 * (2 * k) = 4 * k by omega, show 6 * (2 * k) = 12 * k by omega]
      congr 1
      calc
        _ = (2 : ℝ) ^ (2 * k) * (z ^ (6 * d) * z ^ (4 * k)) := by ring
        _ = _ := by rw [← pow_add, pow_mul (2 : ℝ) 2 k]; norm_num
    _ ≤ (4 : ℝ) ^ k * z ^ (11 * k) / z ^ (12 * k) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by linarith) hexp) (by positivity)) (by positivity)
    _ = (4 / z) ^ k := by
      rw [show 12 * k = 11 * k + k by omega, pow_add, div_pow]
      field_simp
    _ ≤ _ := pow_le_pow_left₀ (by positivity)
      ((div_le_iff₀ hz).mpr (by linarith)) _

end Bernoulli
