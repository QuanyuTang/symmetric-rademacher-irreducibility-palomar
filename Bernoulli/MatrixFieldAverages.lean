module

public import Bernoulli.ConcreteFactorFields
public import Bernoulli.DiscriminantBounds
public import Bernoulli.WeightedFields

/-! The prime-average comparison instantiated on the concrete characteristic factor fields. -/

open Bernoulli.ConcreteFactorFields

namespace Bernoulli

/-- The exceptional integer includes the discriminant of the product of distinct
characteristic factors and the power-basis discriminant of each factor field. -/
@[expose] public noncomputable def exceptionalDiscriminant {n : ℕ} (a : Sample n) : ℤ :=
  (∏ q : Index a, integralFactor a q).discr * ∏ q : Index a, powerDiscriminant a q

public theorem exceptionalDiscriminant_ne_zero {n : ℕ} (a : Sample n) :
    exceptionalDiscriminant a ≠ 0 := by
  have hm : (∏ q : Index a, integralFactor a q).Monic :=
    Polynomial.monic_prod_of_monic _ _ (fun q _ => integralFactor_monic a q)
  exact mul_ne_zero
    (int_poly_discr_ne_zero_of_separable_map _ hm (separable_factorProduct_map_complex a))
    (Finset.prod_ne_zero_iff.mpr fun q _ => powerDiscriminant_ne_zero a q)

/-- The field averages weighted by the multiplicities of the rational factors. -/
@[expose] public noncomputable def characteristicFieldAverage {n : ℕ}
    (a : Sample n) (x : ℝ) : ℝ :=
  ∑ q : Index a, (factorMultiplicity (matrix a).charpoly q : ℝ) *
    primeAverage x (fun p => primeIdealCount (RootField a q) p)

public theorem abs_matrixAverage_sub_characteristicFieldAverage_le {n : ℕ}
    (a : Sample n) {x : ℝ} (hx : 0 < x) :
    |primeAverage x (eigenspaceStatistic a) - characteristicFieldAverage a x| ≤
      3 * (n : ℝ) * Real.log (exceptionalDiscriminant a).natAbs / x := by
  classical
  apply abs_matrixAverage_sub_fieldAverages_le a (integralFactor a)
    (factorMultiplicity (matrix a).charpoly) (integralFactor_monic a) (factorization a)
    (RootField a) (powerBasis a) (integerGenerator a) (powerBasis_gen a) (minpoly_integerGenerator a)
    (sum_weighted_fieldDegree a) (powerDiscriminant a) (powerDiscriminant_spec a)
    (exceptionalDiscriminant_ne_zero a) ?_ ?_ hx
  · exact dvd_mul_right _ _
  · intro q
    have h := Finset.dvd_prod_of_mem (powerDiscriminant a) (Finset.mem_univ q)
    exact h.trans (dvd_mul_left _ _)

end Bernoulli
