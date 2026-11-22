module

public import Bernoulli.RankBandReduction
public import Bernoulli.RankHealthyScales
public import Bernoulli.RankTransitionBand
import Mathlib.Tactic

/-! The finite-field mean estimate on the prime band used in the proof. -/

open Filter
namespace Bernoulli

/-- Suitable absolute constants give the rank error uniformly on the
prime band, once the dimension is sufficiently large. -/
public theorem exists_prime_band_eigenspace_bound :
    ∃ η δ : ℝ, 0 < η ∧ 2 * η ≤ δ ∧
      ∀ᶠ n in atTop, ∀ p : ℕ, p.Prime → 2 < p →
        primeScale η n / 2 ≤ (p : ℝ) → (p : ℝ) ≤ primeScale η n →
        expectation (fun a : Sample n => eigenspaceStatistic a p) ≤
          1 + 4 * ((n : ℝ) ^ 3 / p + (n : ℝ) ^ 3 * p *
            Real.exp (-δ * (n : ℝ) / Real.log p)) := by
  let K := rankHealthyMoment
  let δ : ℝ := 1 / (48 * (K : ℝ))
  let η : ℝ := min (1 / 256) (δ / 2)
  have hK : 0 < K := rankHealthyMoment_pos
  have hK' : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hηsmall : η ≤ 1 / 256 := min_le_left _ _
  have hηδ : 2 * η ≤ δ := by linarith [min_le_right (1 / 256 : ℝ) (δ / 2)]
  refine ⟨η, δ, hη, hηδ, ?_⟩
  let w (n : ℕ) := (n : ℝ) ^ (1 / 4 : ℝ)
  have hw : Tendsto w atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_rankFourierHealthy_le_band hη hηsmall,
    eventually_ge_atTop (32 : ℕ), hw.eventually_ge_atTop (max 1 (96 * (K : ℝ)))]
    with n hn h32 hnlarge
  intro p hp hp₂ hl hr
  let : Fact p.Prime := ⟨hp⟩
  have hgood (t : ℕ) (ht₁ : n ≤ 3 * t) (ht₂ : t ≤ n) :=
    hn t p ht₁ ht₂ hp₂ hl hr
  have hlog : 8 ≤ Real.log (p : ℝ) := (hgood n (by omega) le_rfl).1
  have hp₀ : 0 < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hw₁ : 1 ≤ w n := (le_max_left _ _).trans hnlarge
  have hw₀ : 0 ≤ w n := zero_le_one.trans hw₁
  have hwK : 96 * (K : ℝ) ≤ w n := (le_max_right _ _).trans hnlarge
  have hw4 : w n ^ 4 = (n : ℝ) := by
    dsimp [w]
    rw [← Real.rpow_ofNat, ← Real.rpow_mul (Nat.cast_nonneg n)]
    norm_num
  have hlogpos : 0 < Real.log (p : ℝ) := by linarith
  have hlogupper : Real.log (p : ℝ) ≤ w n := by
    calc
      _ ≤ Real.log (primeScale η n) := Real.log_le_log hp₀ hr
      _ = η / 2 * w n := Real.log_exp _
      _ ≤ 1 * w n := mul_le_mul_of_nonneg_right (by linarith) hw₀
      _ = _ := one_mul _
  have hsize : 96 * (K : ℝ) ≤ (n : ℝ) / Real.log (p : ℝ) := by
    apply (le_div_iff₀ hlogpos).mpr
    calc
      _ ≤ w n * w n := mul_le_mul hwK hlogupper hlogpos.le hw₀
      _ = w n ^ 2 := by ring
      _ ≤ w n ^ 4 := pow_le_pow_right₀ hw₁ (by decide)
      _ = _ := hw4
  have h := expectation_eigenspaceStatistic_le_of_rankFourierHealthy_band hp₂ h32
    (Nat.succ_le_of_lt hK) (by linarith : 4 ≤ Real.log (p : ℝ)) hsize (fun lam t ht htn => by
      have ht' : (n : ℝ) ≤ 3 * (t : ℝ) := by linarith
      have htt : n ≤ 3 * t := by exact_mod_cast ht'
      exact (hgood t htt htn).2.2.2 lam)
  have hExp : -(n : ℝ) / (48 * (K : ℝ) * Real.log (p : ℝ)) =
      -δ * (n : ℝ) / Real.log (p : ℝ) := by
    dsimp [δ]
    field_simp [hK'.ne', hlogpos.ne']
  rwa [hExp] at h

/-- The uniform prime-ideal estimate implies the target bound, using the
proved finite-field mean on the prime band. -/
public theorem reducibility_bound_of_uniform_prime_ideal_estimate (hprime : UniformPrimeIdealEstimate) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      reducibilityProbability n ≤ C * Real.exp (-c * (n : ℝ) ^ (1 / 4 : ℝ)) := by
  obtain ⟨η, δ, hη, hδ, h⟩ := exists_prime_band_eigenspace_bound
  exact reducibility_bound_of_prime_band_estimates hprime hη hδ (by norm_num) h

end Bernoulli
