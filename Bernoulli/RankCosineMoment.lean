module

public import Bernoulli.RankFourier
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# One-coordinate cosine moments

Below the modulus, additive-character orthogonality leaves just the central
term of an even binomial expansion. The corresponding normalized central
binomial coefficient has an elementary inverse-square-root bound.
-/

open scoped BigOperators

namespace Bernoulli

private theorem sum_char_add_neg_even_pow {p : ℕ} [NeZero p] (k : ℕ) (hp : 2 * k < p) :
    (∑ u : ZMod p, (ZMod.stdAddChar u + ZMod.stdAddChar (-u)) ^ (2 * k)) =
      (p : ℂ) * (Nat.centralBinom k : ℂ) := by
  have zeroFrequency (j : ℕ) (hj : j ∈ Finset.range (2 * k + 1)) :
      (j : ZMod p) - ((2 * k - j : ℕ) : ZMod p) = 0 ↔ j = k := by
    have hjp : j < p := by have := Finset.mem_range.mp hj; omega
    have hcp : 2 * k - j < p := by omega
    rw [sub_eq_zero]
    constructor
    · intro h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt hjp, ZMod.val_natCast_of_lt hcp] at hv
      omega
    · intro hjk
      subst j
      rw [show 2 * k - k = k by omega]
  calc
    _ = ∑ j ∈ Finset.range (2 * k + 1),
        ∑ u : ZMod p, ZMod.stdAddChar (u * ((j : ZMod p) - ((2 * k - j : ℕ) : ZMod p))) *
          ((2 * k).choose j : ℂ) := by
      simp_rw [add_pow]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun u _ => ?_
      rw [← AddChar.map_nsmul_eq_pow, ← AddChar.map_nsmul_eq_pow, ← AddChar.map_add_eq_mul,
        nsmul_eq_mul, nsmul_eq_mul, mul_neg, ← sub_eq_add_neg, ← sub_mul, mul_comm _ u]
    _ = ∑ j ∈ Finset.range (2 * k + 1), if j = k then (p : ℂ) * ((2 * k).choose j : ℂ) else 0 := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [← Finset.sum_mul, AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p)]
      simp [zeroFrequency j hj, ite_mul, ZMod.card]
    _ = _ := by
      simp [Nat.centralBinom_eq_two_mul_choose, show k < 2 * k + 1 by omega]

/-- Exact even cosine moments over `ZMod p` when the exponent is less than `p`. -/
public theorem sum_abs_cos_even_pow {p : ℕ} [NeZero p] (k : ℕ) (hp : 2 * k < p) :
    (∑ u : ZMod p, |Real.cos (2 * Real.pi * (u.val : ℝ) / p)| ^ (2 * k)) =
      (p : ℝ) * (Nat.centralBinom k : ℝ) / (4 : ℝ) ^ k := by
  have hcos (u : ZMod p) :
      (Real.cos (2 * Real.pi * (u.val : ℝ) / p) : ℂ) =
        (ZMod.stdAddChar u + ZMod.stdAddChar (-u)) / 2 := by
    rw [← stdAddChar_fair_sign]
    simp [Fintype.univ_bool]
    ring
  apply Complex.ofReal_injective
  rw [Complex.ofReal_sum]
  simp_rw [pow_abs_two_mul, Complex.ofReal_pow, hcos, div_pow]
  rw [← Finset.sum_div, sum_char_add_neg_even_pow k hp]
  push_cast
  rw [pow_mul, show (2 : ℂ) ^ 2 = 4 by norm_num]

/-- An elementary decay estimate for the normalized central binomial coefficient. -/
public theorem centralBinom_normalized_sq_le (k : ℕ) :
    ((k : ℝ) + 1) * ((Nat.centralBinom k : ℝ) / (4 : ℝ) ^ k) ^ 2 ≤ 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hrec : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) =
        2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
      exact_mod_cast Nat.succ_mul_centralBinom_succ k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    have hratio : (Nat.centralBinom (k + 1) : ℝ) / (4 : ℝ) ^ (k + 1) =
        ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) * ((Nat.centralBinom k : ℝ) / 4 ^ k) := by
      rw [pow_succ]
      field_simp
      linarith only [hrec]
    have hfactor : ((k : ℝ) + 1 + 1) *
        ((2 * (k : ℝ) + 1) / (2 * ((k : ℝ) + 1))) ^ 2 ≤ (k : ℝ) + 1 := by
      field_simp
      nlinarith only [hk]
    rw [Nat.cast_succ, hratio, mul_pow, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right hfactor (sq_nonneg _)).trans ih

/-- An even moment is uniformly small below the modulus once its exponent is large enough. -/
public theorem sum_abs_cos_even_pow_le {p : ℕ} [NeZero p] (k : ℕ) (hp : 2 * k < p)
    {b : ℝ} (hb : 0 ≤ b) (hscale : 1 ≤ ((k : ℝ) + 1) * b ^ 2) :
    (∑ u : ZMod p, |Real.cos (2 * Real.pi * (u.val : ℝ) / p)| ^ (2 * k)) ≤ (p : ℝ) * b := by
  rw [sum_abs_cos_even_pow k hp, mul_div_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg p)
  have hratio : 0 ≤ (Nat.centralBinom k : ℝ) / (4 : ℝ) ^ k := by positivity
  apply (sq_le_sq₀ hratio hb).mp
  apply le_of_mul_le_mul_left _ (by positivity : 0 < (k : ℝ) + 1)
  exact (centralBinom_normalized_sq_le k).trans hscale

end Bernoulli
