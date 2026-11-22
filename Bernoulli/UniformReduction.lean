module

public import Bernoulli.MeanAssembly
public import Bernoulli.UniformFactorEstimate

/-! The original reducibility bound follows from the two uniform estimates used in the proof. -/

namespace Bernoulli

/-- The upper bound on the mean total eigenspace dimension in the prime field. -/
@[expose] public def UniformExpectedEigenspaceEstimate : Prop :=
  ∃ η C : ℝ, 0 < η ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ p : ℕ, p.Prime → 2 < p →
    (p : ℝ) ≤ Real.exp (η * (n : ℝ) ^ (1 / 4 : ℝ)) →
    expectation (fun a : Sample n => eigenspaceStatistic a p) ≤
      1 + C * ((n : ℝ) / (p : ℝ) ^ 2 + (n : ℝ) * (p : ℝ) *
        Real.exp (-η * (n : ℝ) / Real.log p))

/-- The stretched-exponential reducibility bound, with the two uniform estimates
as explicit hypotheses. -/
public theorem reducibility_bound_of_uniform_estimates
    (hprime : UniformPrimeIdealEstimate) (heigen : UniformExpectedEigenspaceEstimate) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      reducibilityProbability n ≤ C * Real.exp (-c * (n : ℝ) ^ (1 / 4 : ℝ)) := by
  obtain ⟨η, C_S, hη, hCS, hS⟩ := heigen
  obtain ⟨C_F, hCF, hF⟩ := factor_average_bound_of_uniform_estimate hprime
  obtain ⟨C_P, hCP, hP⟩ := rational_prime_mass_bound_of_uniform_estimate hprime
  obtain ⟨c, C, hc, hC, hbound⟩ :=
    reducibility_bound_of_three_estimates hη hCS.le hCF.le hCP.le hS
      (fun n hn a x hx => by
        rw [abs_sub_comm]
        simpa only [div_eq_mul_inv] using hF n (Nat.succ_le_iff.mp hn) a x hx) hP
  exact ⟨c, C, hc, hC, fun n _ => hbound n⟩

end Bernoulli
