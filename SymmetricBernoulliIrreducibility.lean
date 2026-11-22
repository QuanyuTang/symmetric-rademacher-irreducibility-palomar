module

public import Bernoulli.RankBandEstimate
public import ZetaPrimeAverageComplete

/-! The stretched-exponential irreducibility bound for symmetric Rademacher matrices. -/

namespace Bernoulli

/-- For positive dimension, the reducibility probability over the rationals
is at most a constant times a stretched exponential with exponent one quarter. -/
public theorem reducibility_bound :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      reducibilityProbability n ≤ C * Real.exp (-c * (n : ℝ) ^ (1 / 4 : ℝ)) :=
  reducibility_bound_of_uniform_prime_ideal_estimate uniformPrimeIdealEstimate

end Bernoulli
