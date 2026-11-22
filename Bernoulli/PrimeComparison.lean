module

public import Bernoulli.Algebra
public import Bernoulli.FactorCount
public import Bernoulli.PrimeWeights
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-! Passing from pointwise factor-count and mean eigenspace estimates to probability. -/

namespace Bernoulli

/-- Sum of the geometric multiplicities of the eigenvalues in the prime field. -/
@[expose] public noncomputable def eigenspaceStatistic {n : ℕ} (a : Sample n) (p : ℕ) : ℝ := by
  classical
  exact if hp : Nat.Prime p then
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    let A := (matrix a).map (Int.castRingHom (ZMod p))
    ∑ lam : ZMod p, (Module.finrank (ZMod p) (Module.End.eigenspace A.toLin' lam) : ℝ)
  else 0

/-- Distinct eigenspaces are independent, so their total dimension is at most `n`. -/
public theorem eigenspaceStatistic_bounds {n : ℕ} (a : Sample n) (p : ℕ) :
    0 ≤ eigenspaceStatistic a p ∧ eigenspaceStatistic a p ≤ n := by
  classical
  by_cases hp : p.Prime
  · let : Fact p.Prime := ⟨hp⟩
    let A := (matrix a).map (Int.castRingHom (ZMod p))
    simp only [eigenspaceStatistic, dite_eq_left hp]
    constructor
    · positivity
    · have h := sum_finrank_eigenspaces_le_card A
      rw [Fintype.card_fin] at h
      exact_mod_cast h
  · simp [eigenspaceStatistic, hp]

/-- At primes avoiding the discriminant of the product of the distinct factors, the
sample's eigenspace statistic agrees with its weighted count of reduced roots. -/
public theorem eigenspaceStatistic_eq_weighted_roots {n p : ℕ} (a : Sample n) (hp : p.Prime)
    {ι : Type*} [Fintype ι] (g : ι → Polynomial ℤ) (e : ι → ℕ)
    (hmonic : ∀ j, (g j).Monic) (hchar : (matrix a).charpoly = ∏ j, g j ^ e j)
    (hdisc : Int.castRingHom (ZMod p) (∏ j, g j).discr ≠ 0) :
    letI : Fact p.Prime := ⟨hp⟩
    eigenspaceStatistic a p = ∑ j, (e j : ℝ) *
      ((g j).map (Int.castRingHom (ZMod p))).roots.toFinset.card := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hsym : (matrix a).IsSymm := Matrix.IsSymm.ext fun i j => matrix_symmetric a j i
  have hann := aeval_prod_characteristic_factors_eq_zero_of_isSymm hsym g e hchar
  have h := sum_finrank_eigenspaces_map_eq_weighted_root_count (matrix a) _ g e
    hmonic hchar hann hdisc
  rw [eigenspaceStatistic, dite_eq_left hp]
  dsimp only
  exact_mod_cast h

private theorem expectation_sub_const {n : ℕ} (f : Sample n → ℝ) (r : ℝ) :
    expectation (fun a => f a - r) = expectation f - r := by
  calc
    _ = expectation f - expectation (n := n) (fun _ => r) := by
      simp only [expectation, Finset.sum_sub_distrib, sub_div]
    _ = _ := by rw [expectation_const]

public theorem expectation_primeAverage {n : ℕ} (x : ℝ) (f : Sample n → ℕ → ℝ) :
    expectation (fun a => primeAverage x (f a)) =
      primeAverage x (fun p => expectation (fun a => f a p)) := by
  classical
  simp only [expectation, primeAverage]
  rw [Finset.sum_comm, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_mul]
  ring

/-- The averaging step for the reducibility bound. The two input inequalities concern the
pointwise factor count and the mean finite-field eigenspace statistic, respectively. -/
public theorem reducibilityProbability_le_of_prime_estimates {n : ℕ} (hn : 0 < n)
    {x B u : ℝ} (hx : 0 < x)
    (hfactor : ∀ a : Sample n, (factorCount a : ℝ) ≤
      primeAverage x (eigenspaceStatistic a) + B)
    (heigen : ∀ p ∈ primesThrough x, 0 < primeWeight x p →
      expectation (fun a : Sample n => eigenspaceStatistic a p) ≤ 1 + u) :
    reducibilityProbability n ≤ (1 + u) * primeAverage x (fun _ => 1) + B - 1 := by
  have hmean := primeAverage_mono hx heigen
  have hconst : primeAverage x (fun _ => 1 + u) = (1 + u) * primeAverage x (fun _ => 1) := by
    simp [primeAverage, Finset.mul_sum]
  have htotal : expectation (fun a : Sample n => (factorCount a : ℝ) - 1) ≤
      expectation (fun a : Sample n => primeAverage x (eigenspaceStatistic a) - (1 - B)) := by
    apply expectation_mono
    intro a
    linarith [hfactor a]
  simp only [expectation_sub_const, expectation_primeAverage] at htotal
  rw [hconst] at hmean
  have hreduce := reducibilityProbability_le_expectation hn
  rw [expectation_sub_const] at hreduce
  linarith

end Bernoulli
