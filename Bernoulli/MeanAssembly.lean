module

public import Bernoulli.Assembly
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Arithmetic assembly of the three estimates used in the reducibility bound. -/

open Filter

namespace Bernoulli

/-- The rank error is uniform when the prime lies in the interval `[x/2, x]`. -/
public theorem rank_error_le_of_half_scale {η N x p : ℝ} (hη : 0 ≤ η) (hN : 0 ≤ N)
    (hp : 2 < p) (hlower : x / 2 ≤ p) (hupper : p ≤ x) :
    N / p ^ 2 + N * p * Real.exp (-η * N / Real.log p) ≤
      4 * (N * x ^ (-(2 : ℝ)) + N * x * Real.exp (-η * N / Real.log x)) := by
  have hp₀ : 0 < p := by linarith
  have hx₀ : 0 < x := hp₀.trans_le hupper
  have hfirst : N / p ^ 2 ≤ 4 * (N * x ^ (-(2 : ℝ))) := by
    calc
      _ ≤ N / (x / 2) ^ 2 := div_le_div_of_nonneg_left hN (by positivity)
        (pow_le_pow_left₀ (by positivity) hlower 2)
      _ = _ := by
        rw [Real.rpow_neg hx₀.le, Real.rpow_ofNat]
        field_simp
        ring
  have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
  have hlogx : Real.log p ≤ Real.log x := Real.log_le_log hp₀ hupper
  have hexp : Real.exp (-η * N / Real.log p) ≤ Real.exp (-η * N / Real.log x) := by
    apply Real.exp_le_exp.mpr
    have h := div_le_div_of_nonneg_left (mul_nonneg hη hN) hlogp hlogx
    simpa only [neg_mul, neg_div] using neg_le_neg h
  have hsecond : N * p * Real.exp (-η * N / Real.log p) ≤
      N * x * Real.exp (-η * N / Real.log x) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hupper hN) hexp (Real.exp_pos _).le
      (mul_nonneg hN hx₀.le)
  have hnonneg : 0 ≤ N * x * Real.exp (-η * N / Real.log x) := by positivity
  linarith

/-- The two rational-prime mass error terms are uniformly bounded for `x ≥ 4`. -/
public theorem primeAverage_one_le_of_error {x C : ℝ} (hx : 4 ≤ x) (hC : 0 ≤ C)
    (h : |primeAverage x (fun _ ↦ 1) - 1| ≤
      C * (x ^ (-(1 / 64) : ℝ) + x ^ (-(1 / 2) : ℝ) * Real.log x)) :
    primeAverage x (fun _ ↦ 1) ≤ 1 + 3 * C := by
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ : 0 < x := by linarith
  have hfirst : x ^ (-(1 / 64) : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hx₁ (by norm_num)
  have hlog : Real.log x ≤ 2 * x ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ x ^ (1 / 2 : ℝ) / (1 / 2 : ℝ) := Real.log_le_rpow_div hx₀.le (by norm_num)
      _ = _ := by ring
  have hsecond : x ^ (-(1 / 2) : ℝ) * Real.log x ≤ 2 := by
    calc
      _ ≤ x ^ (-(1 / 2) : ℝ) * (2 * x ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hx₀.le _)
      _ = 2 * (x ^ (-(1 / 2) : ℝ) * x ^ (1 / 2 : ℝ)) := by ring
      _ = _ := by rw [← Real.rpow_add hx₀, neg_add_cancel, Real.rpow_zero, mul_one]
  have hbound := (le_abs_self _).trans (h.trans <| mul_le_mul_of_nonneg_left
    (show x ^ (-(1 / 64) : ℝ) + x ^ (-(1 / 2) : ℝ) * Real.log x ≤ 3 by linarith) hC)
  linarith

/-- The conditional reducibility bound from the finite-field mean estimate,
the uniform deterministic factor comparison, and the rational-prime mass
estimate. -/
public theorem reducibility_bound_of_three_estimates {η C_S C_F C_P : ℝ}
    (hη : 0 < η) (hCS : 0 ≤ C_S) (hCF : 0 ≤ C_F) (hCP : 0 ≤ C_P)
    (hS : ∀ n : ℕ, 1 ≤ n → ∀ p : ℕ, p.Prime → 2 < p →
      (p : ℝ) ≤ Real.exp (η * (n : ℝ) ^ (1 / 4 : ℝ)) →
      expectation (fun a : Sample n ↦ eigenspaceStatistic a p) ≤
        1 + C_S * ((n : ℝ) / (p : ℝ) ^ 2 + (n : ℝ) * (p : ℝ) *
          Real.exp (-η * (n : ℝ) / Real.log p)))
    (hF : ∀ n : ℕ, 1 ≤ n → ∀ (a : Sample n) (x : ℝ), 4 ≤ x →
      |(factorCount a : ℝ) - primeAverage x (eigenspaceStatistic a)| ≤ C_F *
        ((n : ℝ) ^ 2 * Real.log (2 * (n : ℝ)) * x ^ (-(1 / 64) : ℝ) +
          (n : ℝ) * x ^ (-(1 / 2) : ℝ) * Real.log x +
          (n : ℝ) ^ 3 * Real.log (2 * (n : ℝ)) * x⁻¹))
    (hP : ∀ x : ℝ, 4 ≤ x → |primeAverage x (fun _ ↦ 1) - 1| ≤
      C_P * (x ^ (-(1 / 64) : ℝ) + x ^ (-(1 / 2) : ℝ) * Real.log x)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
      reducibilityProbability n ≤ C * Real.exp (-c * (n : ℝ) ^ (1 / 4 : ℝ)) := by
  let K := 1 + 3 * C_P
  let A := C_F + 2 * C_P + 4 * C_S * K
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hA_F : C_F + 2 * C_P ≤ A := le_add_of_nonneg_right (by positivity)
  have hA_S : 4 * C_S * K ≤ A := le_add_of_nonneg_left (by positivity)
  apply reducibility_bound_of_prime_comparison hη hA
  filter_upwards [primeWeight_support_at_scale hη, eventually_ge_atTop (1 : ℕ)] with n hn hn₁
  obtain ⟨hx, hsupport⟩ := hn
  let x := primeScale η n
  let N : ℝ := n
  let F := N ^ 2 * Real.log (2 * N) * x ^ (-(1 / 64) : ℝ) +
    N * x ^ (-(1 / 2) : ℝ) * Real.log x + N ^ 3 * Real.log (2 * N) * x⁻¹
  let S := N * x ^ (-(2 : ℝ)) + N * x * Real.exp (-η * N / Real.log x)
  let P := x ^ (-(1 / 64) : ℝ) + x ^ (-(1 / 2) : ℝ) * Real.log x
  let T := primeAverage x (fun _ ↦ 1)
  let u := 4 * C_S * S
  let B := C_F * F
  have hx₄ : 4 ≤ x := hx
  have hx₀ : 0 < x := by linarith
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn₁
  have hlogN : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hFpos : 0 ≤ F := by dsimp [F]; positivity
  have hSpos : 0 ≤ S := by dsimp [S]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  refine ⟨B, u, ?_, ?_, ?_⟩
  · intro a
    have ha := (le_abs_self ((factorCount a : ℝ) - primeAverage x (eigenspaceStatistic a))).trans
      (hF n hn₁ a x hx₄)
    change (factorCount a : ℝ) - primeAverage x (eigenspaceStatistic a) ≤ B at ha
    linarith
  · intro p hp hpw
    obtain ⟨hp₂, hp_low, hp_high⟩ := hsupport p hpw
    have hpdata := (mem_primesThrough hx₀.le).mp hp
    have hp₂' : (2 : ℝ) < p := by exact_mod_cast hp₂
    have hlocal := hS n hn₁ p hpdata.1 hp₂ hp_high.le
    have harr := rank_error_le_of_half_scale (N := N) hη.le (zero_le_one.trans hN)
      hp₂' hp_low.le hpdata.2
    refine hlocal.trans ?_
    calc
      _ ≤ 1 + C_S * (4 * S) := add_le_add le_rfl (mul_le_mul_of_nonneg_left harr hCS)
      _ = 1 + u := by dsimp [u]; ring
  have hT : T ≤ K := primeAverage_one_le_of_error hx₄ hCP (hP x hx₄)
  have hTdiff : T - 1 ≤ C_P * P := (le_abs_self _).trans (hP x hx₄)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith
  have hlogN' : (1 / 2 : ℝ) ≤ Real.log (2 * N) :=
    hlog2.trans (Real.log_le_log (by norm_num) (by linarith))
  have hNsq : 1 ≤ N ^ 2 := one_le_pow₀ hN
  have hcoeff : 1 ≤ 2 * (N ^ 2 * Real.log (2 * N)) := by
    linarith [mul_le_mul hNsq hlogN' (by norm_num : (0 : ℝ) ≤ 1 / 2) (sq_nonneg N)]
  have hP_le : P ≤ 2 * F := by
    have hfirst := mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hx₀.le (-(1 / 64) : ℝ))
    have hsecond : x ^ (-(1 / 2) : ℝ) * Real.log x ≤ N * x ^ (-(1 / 2) : ℝ) * Real.log x := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hx₀.le (-(1 / 2) : ℝ))) hlogx
    have hsecond₀ : 0 ≤ N * x ^ (-(1 / 2) : ℝ) * Real.log x := by positivity
    have hthird₀ : 0 ≤ N ^ 3 * Real.log (2 * N) * x⁻¹ := by positivity
    dsimp [P, F]
    linarith
  have htotal : factorCountError η n = F + S := by
    dsimp [factorCountError, F, S, x, N, primeScale]
    ring
  change (1 + u) * T + B - 1 ≤ A * factorCountError η n
  calc
    _ = (T - 1) + u * T + B := by ring
    _ ≤ C_P * (2 * F) + u * K + B :=
      add_le_add (add_le_add (hTdiff.trans (mul_le_mul_of_nonneg_left hP_le hCP))
        (mul_le_mul_of_nonneg_left hT hu)) le_rfl
    _ = (C_F + 2 * C_P) * F + (4 * C_S * K) * S := by dsimp [B, u]; ring
    _ ≤ A * F + A * S := by
      exact add_le_add (mul_le_mul_of_nonneg_right hA_F hFpos)
        (mul_le_mul_of_nonneg_right hA_S hSpos)
    _ = _ := by rw [htotal]; ring

end Bernoulli
