module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Irreducibility for symmetric Rademacher matrices

Choose each entry on and above the diagonal independently and uniformly from
the two signs. The matrix over the rationals is obtained by reflection.
The probability is the fraction of sign assignments that give a reducible
characteristic polynomial. For the positive dimensions in the theorem,
the characteristic polynomial is monic of positive degree, so reducibility
means that it factors into two polynomials of positive degree over the rationals.
-/

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

/-- The reducibility probability decays stretched-exponentially in the dimension. -/
public theorem main_result :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      reducibilityProbability n ≤ C * Real.exp (-c * (n : ℝ) ^ (1 / 4 : ℝ)) := by
  sorry

end PalomarBernoulli
