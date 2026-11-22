module

public import Bernoulli.ExponentialBounds
public import Bernoulli.PrimeComparison
import Mathlib.Tactic

/-! The final reduction to deterministic and mean estimates for the weighted prime sum. -/

open Filter

namespace Bernoulli

/-- The prime scale used in the factor-count estimate. -/
@[expose] public noncomputable def primeScale (η : ℝ) (n : ℕ) : ℝ :=
  Real.exp ((η / 2) * (n : ℝ) ^ (1 / 4 : ℝ))

public theorem primeScale_tendsto_atTop {η : ℝ} (hη : 0 < η) :
    Tendsto (primeScale η) atTop atTop :=
  Real.tendsto_exp_atTop.comp <|
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp
      tendsto_natCast_atTop_atTop).const_mul_atTop (by positivity)

public theorem primeWeight_support_at_scale {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, 4 ≤ primeScale η n ∧ ∀ p : ℕ, 0 < primeWeight (primeScale η n) p →
      2 < p ∧ primeScale η n / 2 < (p : ℝ) ∧
        (p : ℝ) < Real.exp (η * (n : ℝ) ^ (1 / 4 : ℝ)) := by
  filter_upwards [(tendsto_atTop.mp (primeScale_tendsto_atTop hη)) 4] with n hn
  have hx : 0 < primeScale η n := Real.exp_pos _
  refine ⟨hn, fun p hp => ?_⟩
  obtain ⟨hl, hr⟩ := support_of_primeWeight_pos hx hp
  have hη' : η / 2 ≤ η := by linarith
  have hscale : primeScale η n ≤ Real.exp (η * (n : ℝ) ^ (1 / 4 : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hη' (by positivity))
  have ht : (2 : ℝ) < p := by linarith
  exact ⟨by exact_mod_cast ht, hl, hr.trans_le hscale⟩

/-- If the uniform weighted comparison and the averaged eigenspace estimate jointly give
the five-term error, then the stretched-exponential irreducibility bound follows. -/
public theorem reducibility_bound_of_prime_comparison {η A : ℝ} (hη : 0 < η) (hA : 0 ≤ A)
    (h : ∀ᶠ n in atTop, ∃ (B u : ℝ),
      (∀ a : Sample n, (factorCount a : ℝ) ≤
        primeAverage (primeScale η n) (eigenspaceStatistic a) + B) ∧
      (∀ p ∈ primesThrough (primeScale η n), 0 < primeWeight (primeScale η n) p →
        expectation (fun a : Sample n => eigenspaceStatistic a p) ≤ 1 + u) ∧
      (1 + u) * primeAverage (primeScale η n) (fun _ => 1) + B - 1 ≤
        A * factorCountError η n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ,
      reducibilityProbability n ≤ C * Real.exp (-c * (n : ℝ) ^ (1 / 4 : ℝ)) := by
  apply exists_exp_bound_of_eventually_le_factorCountError hη hA
  filter_upwards [h, eventually_ge_atTop (1 : ℕ)] with n hn hnpos
  obtain ⟨B, u, hfactor, heigen, herror⟩ := hn
  exact (reducibilityProbability_le_of_prime_estimates hnpos (Real.exp_pos _) hfactor heigen).trans
    herror

end Bernoulli
