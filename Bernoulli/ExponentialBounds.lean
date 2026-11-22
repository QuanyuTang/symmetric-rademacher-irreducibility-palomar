module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Absorbing polynomial factors in stretched-exponential estimates

These bounds apply to the finite error sum in the main irreducibility argument.
-/

@[expose] public section

namespace Bernoulli

open Filter
open scoped Topology

/-- For a positive exponent `q`, a polynomial factor is absorbed by halving the
stretched-exponential decay rate. The constant applies to all positive integers. -/
theorem rpow_mul_exp_neg_rpow_le {a b q : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hq : 0 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (1 + (n : ℝ)) ^ b * Real.exp (-a * (n : ℝ) ^ q) ≤
        C * Real.exp (-(a / 2) * (n : ℝ) ^ q) := by
  let g (n : ℕ) := ((n : ℝ) ^ q) ^ (b / q) *
    Real.exp (-(a / 2) * (n : ℝ) ^ q)
  have hg : Tendsto g atTop (𝓝 0) :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b / q) (a / 2)
      (by positivity)).comp ((tendsto_rpow_atTop hq).comp tendsto_natCast_atTop_atTop)
  obtain ⟨B, hB⟩ := hg.bddAbove_range
  refine ⟨(2 : ℝ) ^ b * max B 1,
    mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (zero_lt_one.trans_le (le_max_right _ _)), ?_⟩
  intro n hn
  have hn₁ : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn₀ : (0 : ℝ) ≤ n := by positivity
  have hpowers : ((n : ℝ) ^ q) ^ (b / q) = (n : ℝ) ^ b := by
    rw [← Real.rpow_mul hn₀, mul_div_cancel₀ b hq.ne']
  have hpolynomial : (1 + (n : ℝ)) ^ b ≤ (2 : ℝ) ^ b * ((n : ℝ) ^ q) ^ (b / q) := by
    rw [hpowers, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn₀]
    exact Real.rpow_le_rpow (by positivity) (by linarith) hb
  have hdecay : Real.exp (-a * (n : ℝ) ^ q) =
      Real.exp (-(a / 2) * (n : ℝ) ^ q) * Real.exp (-(a / 2) * (n : ℝ) ^ q) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hg_le : g n ≤ max B 1 := (hB ⟨n, rfl⟩).trans (le_max_left _ _)
  calc
    (1 + (n : ℝ)) ^ b * Real.exp (-a * (n : ℝ) ^ q) ≤
        ((2 : ℝ) ^ b * ((n : ℝ) ^ q) ^ (b / q)) * Real.exp (-a * (n : ℝ) ^ q) :=
      mul_le_mul_of_nonneg_right hpolynomial (Real.exp_pos _).le
    _ = ((2 : ℝ) ^ b * g n) * Real.exp (-(a / 2) * (n : ℝ) ^ q) := by
      rw [hdecay]
      dsimp [g]
      ring
    _ ≤ ((2 : ℝ) ^ b * max B 1) * Real.exp (-(a / 2) * (n : ℝ) ^ q) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hg_le (Real.rpow_nonneg (by norm_num) _)) (Real.exp_pos _).le

/-- The same bound holds when the decay exponent is increased from `q` to `r`. -/
theorem rpow_mul_exp_neg_rpow_le_of_le {a b q r : ℝ}
    (ha : 0 < a) (hb : 0 ≤ b) (hq : 0 < q) (hqr : q ≤ r) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      (1 + (n : ℝ)) ^ b * Real.exp (-a * (n : ℝ) ^ r) ≤
        C * Real.exp (-(a / 2) * (n : ℝ) ^ q) := by
  obtain ⟨C, hC, hbound⟩ := rpow_mul_exp_neg_rpow_le ha hb hq
  refine ⟨C, hC, fun n hn ↦ ?_⟩
  have hpowers : (n : ℝ) ^ q ≤ (n : ℝ) ^ r :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hqr
  apply le_trans _ (hbound n hn)
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (by positivity) _)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hpowers (by linarith))

/-- A stretched-exponential estimate that holds eventually on the naturals can
be made uniform by increasing its prefactor. -/
theorem exists_uniform_exp_neg_rpow_bound {f : ℕ → ℝ} {c q A : ℝ}
    (h : ∀ᶠ n in atTop, f n ≤ A * Real.exp (-c * (n : ℝ) ^ q)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, f n ≤ C * Real.exp (-c * (n : ℝ) ^ q) := by
  let g (n : ℕ) := f n / Real.exp (-c * (n : ℝ) ^ q)
  have hg : ∀ᶠ n in atTop, g n ≤ A :=
    h.mono fun n hn ↦ (div_le_iff₀ (Real.exp_pos _)).2 hn
  obtain ⟨B, hB⟩ := (isBoundedUnder_of_eventually_le hg).bddAbove_range
  refine ⟨max B 1, zero_lt_one.trans_le (le_max_right _ _), fun n ↦ ?_⟩
  exact (div_le_iff₀ (Real.exp_pos _)).1 ((hB ⟨n, rfl⟩).trans (le_max_left _ _))

/-- The sum of the five terms in the bound on the mean factor count minus one. -/
noncomputable def factorCountError (η : ℝ) (n : ℕ) : ℝ :=
  let N : ℝ := n
  let x := Real.exp ((η / 2) * N ^ (1 / 4 : ℝ))
  N ^ 2 * Real.log (2 * N) * x ^ (-(1 / 64) : ℝ) +
    N * x ^ (-(1 / 2) : ℝ) * Real.log x +
    N ^ 3 * Real.log (2 * N) * x⁻¹ + N * x ^ (-(2 : ℝ)) +
    N * x * Real.exp (-η * N / Real.log x)

/-- The five error terms in the factor-count estimate have a common
stretched-exponential bound at the prime scale `exp (η / 2 * n ^ (1 / 4))`. -/
theorem factor_count_error_le {η : ℝ} (hη : 0 < η) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      factorCountError η n ≤ C * Real.exp (-c * (n : ℝ) ^ (1 / 4 : ℝ)) := by
  let a := min (η / 128) 1
  have ha : 0 < a := lt_min (by positivity) zero_lt_one
  have haη : a ≤ η / 128 := min_le_left _ _
  have ha₁ : a ≤ 1 := min_le_right _ _
  obtain ⟨B, hB, hdecay⟩ :=
    rpow_mul_exp_neg_rpow_le (a := a) (b := 4) (q := 1 / 4) ha (by norm_num) (by norm_num)
  let K : ℝ := 5 + η / 2 + Real.exp (η ^ 2 / 16)
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨a / 2, K * B, by positivity, mul_pos hK hB, ?_⟩
  intro n hn
  let N : ℝ := n
  let u := N ^ (1 / 4 : ℝ)
  let x := Real.exp ((η / 2) * u)
  let P := (1 + N) ^ 4
  let E := Real.exp (-a * u)
  change N ^ 2 * Real.log (2 * N) * x ^ (-(1 / 64) : ℝ) +
    N * x ^ (-(1 / 2) : ℝ) * Real.log x +
    N ^ 3 * Real.log (2 * N) * x⁻¹ + N * x ^ (-(2 : ℝ)) +
    N * x * Real.exp (-η * N / Real.log x) ≤ (K * B) * Real.exp (-(a / 2) * u)
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ (n : ℝ)
    exact_mod_cast hn
  have hN₀ : 0 ≤ N := zero_le_one.trans hN
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hu : 1 ≤ u := by
    simpa [u] using Real.rpow_le_rpow zero_le_one hN (by norm_num : 0 ≤ (1 / 4 : ℝ))
  have hu₀ : 0 < u := zero_lt_one.trans_le hu
  have huN : u ≤ N := by
    simpa [u] using Real.rpow_le_rpow_of_exponent_le hN (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hu_four : u ^ 4 = N := by
    dsimp [u]
    rw [← Real.rpow_ofNat, ← Real.rpow_mul hN₀]
    norm_num
  have hpowers (k : ℕ) (hk : k ≤ 4) : N ^ k ≤ P :=
    (pow_le_pow_left₀ hN₀ (by linarith : N ≤ 1 + N) k).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ 1 + N) hk)
  have hN_P : N ≤ P := by simpa using hpowers 1 (by decide)
  have hxlog : Real.log x = (η / 2) * u := Real.log_exp _
  have hxpow (r : ℝ) : x ^ r = Real.exp (((η / 2) * u) * r) := (Real.exp_mul _ _).symm
  have hexp {r : ℝ} (hr : a ≤ r) : Real.exp (-r * u) ≤ E := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right (neg_le_neg hr) hu₀.le
  have hlog : Real.log (2 * N) ≤ 2 * N := Real.log_le_self (by positivity)
  have hfirst : N ^ 2 * Real.log (2 * N) * x ^ (-(1 / 64) : ℝ) ≤ (2 * P) * E := by
    rw [hxpow]
    have hcoeff : N ^ 2 * Real.log (2 * N) ≤ 2 * P := by
      calc
        _ ≤ N ^ 2 * (2 * N) := mul_le_mul_of_nonneg_left hlog (sq_nonneg _)
        _ = 2 * N ^ 3 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hpowers 3 (by decide)) (by norm_num)
    rw [show (η / 2 * u) * -(1 / 64 : ℝ) = -(η / 128) * u by ring]
    exact mul_le_mul hcoeff (hexp haη) (Real.exp_pos _).le (by positivity)
  have hsecond : N * x ^ (-(1 / 2) : ℝ) * Real.log x ≤ ((η / 2) * P) * E := by
    rw [hxpow, hxlog, show (η / 2 * u) * -(1 / 2 : ℝ) = -(η / 4) * u by ring]
    have hcoeff : η / 2 * (N * u) ≤ η / 2 * P := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        N * u ≤ N * N := mul_le_mul_of_nonneg_left huN hN₀
        _ = N ^ 2 := by ring
        _ ≤ P := hpowers 2 (by decide)
    calc
      _ = (η / 2 * (N * u)) * Real.exp (-(η / 4) * u) := by ring
      _ ≤ _ := mul_le_mul hcoeff (hexp (by linarith)) (Real.exp_pos _).le (by positivity)
  have hthird : N ^ 3 * Real.log (2 * N) * x⁻¹ ≤ (2 * P) * E := by
    change N ^ 3 * Real.log (2 * N) * (Real.exp ((η / 2) * u))⁻¹ ≤ _
    rw [← Real.exp_neg, ← neg_mul]
    have hcoeff : N ^ 3 * Real.log (2 * N) ≤ 2 * P := by
      calc
        _ ≤ N ^ 3 * (2 * N) := mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = 2 * N ^ 4 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hpowers 4 le_rfl) (by norm_num)
    exact mul_le_mul hcoeff (hexp (by linarith)) (Real.exp_pos _).le (by positivity)
  have hfourth : N * x ^ (-(2 : ℝ)) ≤ P * E := by
    rw [hxpow, show (η / 2 * u) * -(2 : ℝ) = -η * u by ring]
    exact mul_le_mul hN_P (hexp (by linarith)) (Real.exp_pos _).le hP
  have hfifth : N * x * Real.exp (-η * N / Real.log x) ≤
      (Real.exp (η ^ 2 / 16) * P) * E := by
    have hquotient : -η * N / Real.log x = -2 * u ^ 3 := by
      rw [hxlog, ← hu_four]
      field_simp
    have hlarge : (η / 2) * u - 2 * u ^ 3 ≤ η ^ 2 / 16 - u := by
      have h₁ : u ^ 2 ≤ u ^ 3 := pow_le_pow_right₀ hu (by decide)
      have h₂ : u ≤ u ^ 3 := by simpa using (pow_le_pow_right₀ hu (by decide : 1 ≤ 3))
      nlinarith [sq_nonneg (u - η / 4)]
    have hfifth_exp : Real.exp ((η / 2) * u - 2 * u ^ 3) ≤ Real.exp (η ^ 2 / 16) * E := by
      calc
        _ ≤ Real.exp (η ^ 2 / 16 - u) := Real.exp_le_exp.mpr hlarge
        _ = Real.exp (η ^ 2 / 16) * Real.exp (-1 * u) := by
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (hexp ha₁) (Real.exp_pos _).le
    rw [hquotient, mul_assoc]
    change N * (Real.exp ((η / 2) * u) * Real.exp (-2 * u ^ 3)) ≤ _
    rw [← Real.exp_add,
      show (η / 2) * u + -2 * u ^ 3 = (η / 2) * u - 2 * u ^ 3 by ring]
    calc
      _ ≤ P * (Real.exp (η ^ 2 / 16) * E) :=
        mul_le_mul hN_P hfifth_exp (Real.exp_pos _).le hP
      _ = (Real.exp (η ^ 2 / 16) * P) * E := by ring
  have hsum : (2 * P) * E + ((η / 2) * P) * E + (2 * P) * E + P * E +
      (Real.exp (η ^ 2 / 16) * P) * E = K * (P * E) := by
    dsimp [K]
    ring
  have hPE : P * E ≤ B * Real.exp (-(a / 2) * u) := by
    simpa only [P, E, u, N, Real.rpow_ofNat] using hdecay n hn
  calc
    _ ≤ (2 * P) * E + ((η / 2) * P) * E + (2 * P) * E + P * E +
        (Real.exp (η ^ 2 / 16) * P) * E := by
      exact add_le_add (add_le_add (add_le_add (add_le_add hfirst hsecond) hthird) hfourth) hfifth
    _ = K * (P * E) := hsum
    _ ≤ K * (B * Real.exp (-(a / 2) * u)) := mul_le_mul_of_nonneg_left hPE hK.le
    _ = _ := by ring

/-- A sequence eventually bounded by a nonnegative multiple of the five error
terms admits the desired bound for every dimension. -/
theorem exists_exp_bound_of_eventually_le_factorCountError {f : ℕ → ℝ} {η A : ℝ}
    (hη : 0 < η) (hA : 0 ≤ A)
    (h : ∀ᶠ n in atTop, f n ≤ A * factorCountError η n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
      f n ≤ C * Real.exp (-c * (n : ℝ) ^ (1 / 4 : ℝ)) := by
  obtain ⟨c, C, hc, _, hC⟩ := factor_count_error_le hη
  have heventual : ∀ᶠ n in atTop, f n ≤ (A * C) * Real.exp (-c * (n : ℝ) ^ (1 / 4 : ℝ)) := by
    filter_upwards [h, eventually_ge_atTop 1] with n hn hn₁
    exact hn.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hC n hn₁) hA)
  obtain ⟨C', hC', hbound⟩ := exists_uniform_exp_neg_rpow_bound heventual
  exact ⟨c, C', hc, hC', hbound⟩

end Bernoulli
