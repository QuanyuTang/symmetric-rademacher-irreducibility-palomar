module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import SymmetricBernoulliIrreducibility

/-! The proof of the statement selected for comparison by Palomar. -/

namespace PalomarBernoulli

/-- Independent Boolean signs on the upper triangle, including the diagonal. -/
public abbrev Sample (n : ℕ) := {ij : Fin n × Fin n // ij.1 ≤ ij.2} → Bool

/-- The sampled symmetric matrix over the rationals. -/
@[expose] public def signMatrix {n : ℕ} (a : Sample n) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => if a ⟨(min i j, max i j), le_trans (min_le_left ..) (le_max_left ..)⟩
    then 1 else -1

/-- The proportion of assignments having a reducible characteristic polynomial. -/
@[expose] public noncomputable def reducibilityProbability (n : ℕ) : ℝ := by
  classical
  exact (Fintype.card {a : Sample n // ¬ Irreducible (signMatrix a).charpoly} : ℝ) /
    Fintype.card (Sample n)

private theorem charpoly_agrees {n : ℕ} (a : Sample n) :
    Bernoulli.charpoly a = (signMatrix a).charpoly := by
  unfold Bernoulli.charpoly
  congr 1
  ext i j
  simp only [Matrix.map_apply, Bernoulli.matrix, signMatrix]
  split <;> simp

private theorem probability_agrees (n : ℕ) :
    reducibilityProbability n = Bernoulli.reducibilityProbability n := by
  classical
  rw [Bernoulli.reducibilityProbability, Bernoulli.probability_eq_card]
  let e : {a : Sample n // ¬ Irreducible (signMatrix a).charpoly} ≃
      {a : Bernoulli.Sample n // ¬ Irreducible (Bernoulli.charpoly a)} :=
    (Equiv.refl (Sample n)).subtypeEquiv (fun a => by simp [charpoly_agrees])
  unfold reducibilityProbability
  rw [Fintype.card_congr e]

/-- The reducibility probability decays stretched-exponentially in the dimension. -/
public theorem main_result :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      reducibilityProbability n ≤ C * Real.exp (-c * (n : ℝ) ^ (1 / 4 : ℝ)) := by
  simpa only [probability_agrees] using Bernoulli.reducibility_bound

end PalomarBernoulli
