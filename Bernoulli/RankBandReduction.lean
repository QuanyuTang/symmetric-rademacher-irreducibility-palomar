module

public import Bernoulli.MeanAssembly
public import Bernoulli.UniformFactorEstimate
import Mathlib.Tactic

/-! The reducibility bound allows a weaker rank error on the prime band. -/

open Filter
namespace Bernoulli

private theorem rank_exponential_at_primeScale {η δ : ℝ} (hη : 0 < η)
    (hδ : 2 * η ≤ δ) {n p : ℕ} (hn : 16 ≤ n) (hp : 2 < p)
    (hupper : (p : ℝ) ≤ primeScale η n) :
    (n : ℝ) ^ 3 * p * Real.exp (-δ * (n : ℝ) / Real.log p) ≤
      (n : ℝ) * primeScale η n * Real.exp (-η * (n : ℝ) / Real.log (primeScale η n)) := by
  let N : ℝ := n
  let v := N ^ (1 / 4 : ℝ)
  let x := primeScale η n
  change N ^ 3 * p * Real.exp (-δ * N / Real.log p) ≤ N * x * Real.exp (-η * N / Real.log x)
  have hn' : 16 ≤ N := by dsimp only [N]; exact_mod_cast hn
  have hN : 0 < N := by linarith
  have hp' : (2 : ℝ) < p := by exact_mod_cast hp
  have hp₀ : 0 < (p : ℝ) := by linarith
  have hv : 2 ≤ v := by
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 16) hn' (by norm_num : (0 : ℝ) ≤ 1 / 4)
    have h16 : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
      rw [show (16 : ℝ) = (2 : ℝ) ^ (4 : ℝ) by norm_num [Real.rpow_ofNat],
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    exact h16 ▸ h
  have hv₀ : 0 < v := by linarith
  have hv4 : v ^ 4 = N := by
    dsimp [v]
    rw [← Real.rpow_ofNat, ← Real.rpow_mul hN.le]
    norm_num
  have hlogp : 0 < Real.log p := Real.log_pos (by linarith)
  have hlogx : 0 < Real.log x := hlogp.trans_le (Real.log_le_log hp₀ hupper)
  have hxlog : Real.log x = η / 2 * v := Real.log_exp _
  have hquot : η * N / Real.log x = 2 * v ^ 3 := by
    rw [hxlog, ← hv4]
    field_simp [hη.ne', hv₀.ne']
  have hlogN : 2 * Real.log N ≤ η * N / Real.log x := by
    rw [hquot]
    have hlog := Real.log_le_rpow_div hN.le (by norm_num : (0 : ℝ) < 1 / 4)
    change Real.log N ≤ v / (1 / 4 : ℝ) at hlog
    have hsq : 4 ≤ v ^ 2 := by nlinarith [sq_nonneg (v - 2)]
    nlinarith [mul_nonneg hv₀.le (sub_nonneg.mpr hsq)]
  have hδpos : 0 ≤ δ := by linarith
  have hlarge : η * N / Real.log x + η * N / Real.log x ≤ δ * N / Real.log p := by
    rw [← add_div, ← add_mul]
    exact (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : η + η ≤ δ) hN.le) hlogx.le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hδpos hN.le) hlogp (Real.log_le_log hp₀ hupper))
  have hexp : 2 * Real.log N + -(δ * N / Real.log p) ≤ -(η * N / Real.log x) := by
    linarith only [hlogN, hlarge]
  have hNp : N ^ 2 = Real.exp (2 * Real.log N) := by
    rw [mul_comm (2 : ℝ), Real.exp_mul, Real.exp_log hN, Real.rpow_ofNat]
  calc
    _ = N * p * Real.exp (2 * Real.log N + -(δ * N / Real.log p)) := by
      rw [Real.exp_add, ← hNp]
      simp only [neg_div, neg_mul]
      ring
    _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hupper hN.le)
      (Real.exp_le_exp.mpr (by simpa only [neg_div, neg_mul] using hexp))
      (Real.exp_nonneg _) (mul_nonneg hN.le (Real.exp_nonneg _))

private theorem rank_error_at_primeScale {η δ : ℝ} (hη : 0 < η) (hδ : 2 * η ≤ δ)
    {n p : ℕ} (hn : 16 ≤ n) (hp : 2 < p) (hlower : primeScale η n / 2 ≤ p)
    (hupper : (p : ℝ) ≤ primeScale η n) :
    (n : ℝ) ^ 3 / p + (n : ℝ) ^ 3 * p * Real.exp (-δ * (n : ℝ) / Real.log p) ≤
      5 * factorCountError η n := by
  let N : ℝ := n
  let x := primeScale η n
  have hx : 0 < x := Real.exp_pos _
  have hn' : 16 ≤ N := by dsimp only [N]; exact_mod_cast hn
  have hN : 0 ≤ N := by linarith
  have hx' : 2 < x := (show (2 : ℝ) < p by exact_mod_cast hp).trans_le hupper
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log (2 * N) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h.trans (Real.log_le_log (by norm_num) (by linarith))
  have hlogN : 0 ≤ Real.log (2 * N) := by linarith
  have hfirst : N ^ 3 / p ≤ 4 * (N ^ 3 * Real.log (2 * N) * x⁻¹) := by
    calc
      _ ≤ N ^ 3 / (x / 2) := div_le_div_of_nonneg_left (by positivity) (by positivity) hlower
      _ = (2 * N ^ 3) * x⁻¹ := by ring
      _ ≤ _ := by
        rw [← mul_assoc]
        have h := mul_nonneg (pow_nonneg hN 3) (sub_nonneg.mpr hlog2)
        exact mul_le_mul_of_nonneg_right (by nlinarith only [h]) (by positivity)
  have hsecond := rank_exponential_at_primeScale hη hδ hn hp hupper
  change _ ≤ N * x * Real.exp (-η * N / Real.log x) at hsecond
  have hrest₁ : 0 ≤ N ^ 2 * Real.log (2 * N) * x ^ (-(1 / 64) : ℝ) := by positivity
  have hrest₂ : 0 ≤ N * x ^ (-(1 / 2) : ℝ) * Real.log x := by positivity
  have hrest₄ : 0 ≤ N * x ^ (-(2 : ℝ)) := by positivity
  have h3 : 0 ≤ N ^ 3 * Real.log (2 * N) * x⁻¹ := by positivity
  have h5 : 0 ≤ N * x * Real.exp (-η * N / Real.log x) := by positivity
  change N ^ 3 / p + _ ≤ 5 * (N ^ 2 * Real.log (2 * N) * x ^ (-(1 / 64) : ℝ) +
    N * x ^ (-(1 / 2) : ℝ) * Real.log x + N ^ 3 * Real.log (2 * N) * x⁻¹ +
    N * x ^ (-(2 : ℝ)) + N * x * Real.exp (-η * N / Real.log x))
  linarith only [hfirst, hsecond, hrest₁, hrest₂, hrest₄, h3, h5]

private theorem factor_and_mass_errors_at_primeScale {η : ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hx : 4 ≤ primeScale η n) :
    let N : ℝ := n
    let x := primeScale η n
    let F := N ^ 2 * Real.log (2 * N) * x ^ (-(1 / 64) : ℝ) +
      N * x ^ (-(1 / 2) : ℝ) * Real.log x + N ^ 3 * Real.log (2 * N) * x⁻¹
    0 ≤ factorCountError η n ∧ F ≤ factorCountError η n ∧
      x ^ (-(1 / 64) : ℝ) + x ^ (-(1 / 2) : ℝ) * Real.log x ≤ 2 * factorCountError η n := by
  dsimp only
  let N : ℝ := n
  let x := primeScale η n
  let a := N ^ 2 * Real.log (2 * N) * x ^ (-(1 / 64) : ℝ)
  let b := N * x ^ (-(1 / 2) : ℝ) * Real.log x
  let c := N ^ 3 * Real.log (2 * N) * x⁻¹
  have hN : 1 ≤ N := by dsimp only [N]; exact_mod_cast hn
  have hx₀ : 0 < x := Real.exp_pos _
  have hlogN : (1 / 2 : ℝ) ≤ Real.log (2 * N) := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h.trans (Real.log_le_log (by norm_num) (by linarith))
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hf : a + b + c ≤ factorCountError η n := by
    have h1 : 0 ≤ N * x ^ (-(2 : ℝ)) := by positivity
    have h2 : 0 ≤ N * x * Real.exp (-η * N / Real.log x) := by positivity
    change a + b + c ≤ a + b + c + N * x ^ (-(2 : ℝ)) + N * x * Real.exp (-η * N / Real.log x)
    linarith
  refine ⟨(by linarith : 0 ≤ a + b + c).trans hf, hf, ?_⟩
  have hcoeff : 1 ≤ 2 * (N ^ 2 * Real.log (2 * N)) := by
    have hNsq : 1 ≤ N ^ 2 := one_le_pow₀ hN
    linarith [mul_le_mul hNsq hlogN (by norm_num : (0 : ℝ) ≤ 1 / 2) (sq_nonneg N)]
  have hfirst : x ^ (-(1 / 64) : ℝ) ≤ 2 * a := by
    simpa only [a, one_mul, mul_assoc] using
      mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hx₀.le (-(1 / 64) : ℝ))
  have hsecond : x ^ (-(1 / 2) : ℝ) * Real.log x ≤ b := by
    simpa only [b, one_mul] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hN (Real.rpow_nonneg hx₀.le (-(1 / 2) : ℝ))) hlogx
  linarith only [hfirst, hsecond, hf, hb, hc]

/-- An eventual eigenspace estimate on the support band suffices for
the stretched-exponential irreducibility bound. -/
public theorem reducibility_bound_of_prime_band_estimates
    (hprime : UniformPrimeIdealEstimate) {η δ C_S : ℝ} (hη : 0 < η)
    (hδ : 2 * η ≤ δ) (hCS : 0 ≤ C_S)
    (heigen : ∀ᶠ n in atTop, ∀ p : ℕ, p.Prime → 2 < p →
      primeScale η n / 2 ≤ (p : ℝ) → (p : ℝ) ≤ primeScale η n →
      expectation (fun a : Sample n => eigenspaceStatistic a p) ≤
        1 + C_S * ((n : ℝ) ^ 3 / p + (n : ℝ) ^ 3 * p *
          Real.exp (-δ * (n : ℝ) / Real.log p))) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      reducibilityProbability n ≤ C * Real.exp (-c * (n : ℝ) ^ (1 / 4 : ℝ)) := by
  obtain ⟨C_F, hCF, hF⟩ := factor_average_bound_of_uniform_estimate hprime
  obtain ⟨C_P, hCP, hP⟩ := rational_prime_mass_bound_of_uniform_estimate hprime
  let K := 1 + 3 * C_P
  let A := C_F + 2 * C_P + 5 * C_S * K
  have hA : 0 ≤ A := by dsimp [A, K]; positivity
  suffices H : ∀ᶠ n in atTop, ∃ (B u : ℝ),
      (∀ a : Sample n, (factorCount a : ℝ) ≤
        primeAverage (primeScale η n) (eigenspaceStatistic a) + B) ∧
      (∀ p ∈ primesThrough (primeScale η n), 0 < primeWeight (primeScale η n) p →
        expectation (fun a : Sample n => eigenspaceStatistic a p) ≤ 1 + u) ∧
      (1 + u) * primeAverage (primeScale η n) (fun _ => 1) + B - 1 ≤ A * factorCountError η n by
    obtain ⟨c, C, hc, hC, h⟩ := reducibility_bound_of_prime_comparison hη hA H
    exact ⟨c, C, hc, hC, fun n _ => h n⟩
  filter_upwards [heigen, primeWeight_support_at_scale hη, eventually_ge_atTop (16 : ℕ)]
    with n hE hn h16
  obtain ⟨hx, hsupport⟩ := hn
  let x := primeScale η n
  let E := factorCountError η n
  obtain ⟨hE₀, hFE, hPE⟩ := factor_and_mass_errors_at_primeScale (by omega : 1 ≤ n) hx
  let B := C_F * E
  let u := 5 * C_S * E
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hx₀ : 0 < x := Real.exp_pos _
  have hT : primeAverage x (fun _ => 1) ≤ K := primeAverage_one_le_of_error hx hCP.le (hP x hx)
  have hTdiff : primeAverage x (fun _ => 1) - 1 ≤ C_P * (2 * E) :=
    (le_abs_self _).trans ((hP x hx).trans (mul_le_mul_of_nonneg_left hPE hCP.le))
  refine ⟨B, u, ?_, ?_, ?_⟩
  · intro a
    have hcomp := hF n (by omega) a x hx
    rw [abs_sub_comm] at hcomp
    have hf := (le_abs_self _).trans (hcomp.trans (mul_le_mul_of_nonneg_left hFE hCF.le))
    change (factorCount a : ℝ) - primeAverage x (eigenspaceStatistic a) ≤ B at hf
    linarith
  · intro p hp hw
    obtain ⟨hp₂, hl, _⟩ := hsupport p hw
    obtain ⟨hp', hr⟩ := (mem_primesThrough hx₀.le).mp hp
    calc
      _ ≤ _ := hE p hp' hp₂ hl.le hr
      _ ≤ 1 + C_S * (5 * E) := add_le_add le_rfl (mul_le_mul_of_nonneg_left
        (rank_error_at_primeScale hη hδ h16 hp₂ hl.le hr) hCS)
      _ = _ := by dsimp [u]; ring
  · calc
      _ = (primeAverage x (fun _ => 1) - 1) + u * primeAverage x (fun _ => 1) + B := by ring
      _ ≤ C_P * (2 * E) + u * K + B :=
        add_le_add (add_le_add hTdiff (mul_le_mul_of_nonneg_left hT hu)) le_rfl
      _ = A * factorCountError η n := by dsimp [u, B, E, A]; ring

end Bernoulli
