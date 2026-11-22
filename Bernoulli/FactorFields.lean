module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.AdjoinRoot

/-! The quotient number field and its integral generator for a monic factor. -/

open Polynomial
open scoped NumberField

namespace Bernoulli

/-- The field obtained by adjoining a root of the rational image of `g` when it is irreducible. -/
public abbrev FactorField (g : Polynomial ℤ) := AdjoinRoot (g.map (algebraMap ℤ ℚ))

public theorem aeval_factorField_root (g : Polynomial ℤ) :
    aeval (AdjoinRoot.root (g.map (algebraMap ℤ ℚ))) g = 0 := by
  have h := AdjoinRoot.eval₂_root (g.map (algebraMap ℤ ℚ))
  rw [← AdjoinRoot.algebraMap_eq, Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq] at h
  exact h

/-- The generator in the ring of integers, witnessed by the monic polynomial `g`. -/
public noncomputable def factorFieldInteger {g : Polynomial ℤ} (hm : g.Monic)
    [Fact (Irreducible (g.map (algebraMap ℤ ℚ)))] : 𝓞 (FactorField g) :=
  ⟨AdjoinRoot.root (g.map (algebraMap ℤ ℚ)), ⟨g, hm, aeval_factorField_root g⟩⟩

public theorem minpoly_factorFieldInteger {g : Polynomial ℤ} (hm : g.Monic)
    [Fact (Irreducible (g.map (algebraMap ℤ ℚ)))] :
    minpoly ℤ (factorFieldInteger hm : FactorField g) = g := by
  let φ := algebraMap ℤ ℚ
  let r : FactorField g := AdjoinRoot.root (g.map φ)
  change minpoly ℤ r = g
  have hi : IsIntegral ℤ r := ⟨g, hm, aeval_factorField_root g⟩
  apply Polynomial.map_injective φ (IsFractionRing.injective ℤ ℚ)
  rw [← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hi]
  exact (AdjoinRoot.minpoly_root (f := g.map φ) (hm.map φ).ne_zero).trans (by
    rw [(hm.map φ).leadingCoeff, inv_one, C_1, mul_one])

public theorem finrank_factorField {g : Polynomial ℤ} (hm : g.Monic) :
    Module.finrank ℚ (FactorField g) = g.natDegree :=
  (finrank_quotient_span_eq_natDegree (f := g.map (algebraMap ℤ ℚ))).trans (hm.natDegree_map _)

end Bernoulli
