module

public import Bernoulli.BadPrimeError
public import Bernoulli.GoodPrime
public import Bernoulli.NumberFieldPrimes
public import Bernoulli.PrimeComparison
import Mathlib.Tactic

/-! Comparison of the matrix and number-field prime averages. -/

open NumberField

namespace Bernoulli

/-- Number of nonzero prime ideals of norm `p`. -/
@[expose] public noncomputable def primeIdealCount (K : Type*) [Field K] (p : ℕ) : ℕ :=
  Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ P.cardQuot = p}

/-- The weighted prime averages for the matrix and its factor fields differ by at most
the error from the divisors of one exceptional integer. -/
public theorem abs_matrixAverage_sub_fieldAverages_le {n : ℕ} (a : Sample n)
    {ι : Type*} [Fintype ι] (g : ι → Polynomial ℤ) (e : ι → ℕ)
    (hmonic : ∀ j, (g j).Monic) (hchar : (matrix a).charpoly = ∏ j, g j ^ e j)
    (K : ι → Type*) [∀ j, Field (K j)] [∀ j, NumberField (K j)]
    (B : ∀ j, PowerBasis ℚ (K j)) (θ : ∀ j, 𝓞 (K j))
    (hgen : ∀ j, (B j).gen = (θ j : K j)) (hmin : ∀ j, minpoly ℤ (θ j : K j) = g j)
    (hdegree : (∑ j, e j * Module.finrank ℚ (K j)) = n)
    (d : ι → ℤ) (hdisc : ∀ j, Algebra.discr ℚ (B j).basis = (d j : ℚ))
    {D : ℤ} (hD : D ≠ 0) (hDmatrix : (∏ j, g j).discr ∣ D) (hDfields : ∀ j, d j ∣ D)
    {x : ℝ} (hx : 0 < x) :
    |primeAverage x (eigenspaceStatistic a) -
      (∑ j, (e j : ℝ) * primeAverage x (fun p => primeIdealCount (K j) p))| ≤
      3 * (n : ℝ) * Real.log D.natAbs / x := by
  classical
  let F (p : ℕ) : ℝ := ∑ j, (e j : ℝ) * (primeIdealCount (K j) p : ℝ)
  have hlinear : primeAverage x F =
      ∑ j, (e j : ℝ) * primeAverage x (fun p => primeIdealCount (K j) p) := by
    simp only [F, primeAverage, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  rw [← hlinear]
  have hDabs : 0 < D.natAbs := Int.natAbs_pos.mpr hD
  apply abs_primeAverage_sub_le_bad_primes hx (Nat.cast_nonneg n) hDabs
  · intro p _
    exact eigenspaceStatistic_bounds a p
  · intro p hp
    let : Fact p.Prime := ⟨((mem_primesThrough hx.le).mp hp).1⟩
    constructor
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    · have hcount : (∑ j, e j * primeIdealCount (K j) p) ≤ n := by
        rw [← hdegree]
        exact Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _
          (card_primeIdeals_of_norm_le_finrank (K := K j) p)
      dsimp only [F]
      exact_mod_cast hcount
  · intro p hp hnot
    let hp' := ((mem_primesThrough hx.le).mp hp).1
    let : Fact p.Prime := ⟨hp'⟩
    have hnot' : ¬ (p : ℤ) ∣ D := by
      rintro ⟨k, hk⟩
      apply hnot
      rw [hk, Int.natAbs_mul, Int.natAbs_natCast]
      exact dvd_mul_right _ _
    have hsym : (matrix a).IsSymm := Matrix.IsSymm.ext fun i j => matrix_symmetric a j i
    have hgood := sum_finrank_eigenspaces_eq_weighted_primeIdeals_at_good_prime hsym g e
      hmonic hchar K B θ hgen hmin d hdisc p
      (fun h => hnot' (h.trans hDmatrix)) (fun j h => hnot' (h.trans (hDfields j)))
    rw [eigenspaceStatistic, dite_eq_left hp']
    dsimp only [F, primeIdealCount]
    exact_mod_cast hgood

end Bernoulli
