module

public import Bernoulli.Algebra
public import Bernoulli.DedekindRoots

/-!
# Eigenspaces and prime ideals at a good prime

At a prime avoiding the discriminants, reduction of the matrix and the
Kummer–Dedekind correspondence identify the weighted counts.
-/

public section

open NumberField
open scoped BigOperators

namespace Bernoulli

private theorem card_distinct_roots_eq_card_root_subtype {K : Type*} [Field K] [DecidableEq K]
    (g : Polynomial K) (hg : g ≠ 0) :
    g.roots.toFinset.card = Nat.card {z : K // g.IsRoot z} := by
  let e : g.roots.toFinset ≃ {z : K // g.IsRoot z} :=
    Equiv.subtypeEquivRight fun z => by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hg]
  calc
    _ = Fintype.card g.roots.toFinset := (Fintype.card_coe _).symm
    _ = Nat.card (↥g.roots.toFinset) := Nat.card_eq_fintype_card.symm
    _ = _ := Nat.card_congr e

/-- Good reduction identifies the total eigenspace dimension with the weighted
number of prime ideals of norm `p` in the number fields of the factors. -/
theorem sum_finrank_eigenspaces_eq_weighted_primeIdeals_at_good_prime
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] {A : Matrix ι ι ℤ}
    (hA : A.IsSymm) (g : κ → Polynomial ℤ) (e : κ → ℕ)
    (hmonic : ∀ j, (g j).Monic) (hchar : A.charpoly = ∏ j, g j ^ e j)
    (K : κ → Type*) [∀ j, Field (K j)] [∀ j, NumberField (K j)]
    (B : ∀ j, PowerBasis ℚ (K j)) (θ : ∀ j, 𝓞 (K j))
    (hgen : ∀ j, (B j).gen = (θ j : K j)) (hmin : ∀ j, minpoly ℤ (θ j : K j) = g j)
    (d : κ → ℤ) (hdisc : ∀ j, Algebra.discr ℚ (B j).basis = (d j : ℚ))
    (p : ℕ) [Fact p.Prime] (hgood : ¬ (p : ℤ) ∣ (∏ j, g j).discr)
    (hgoodField : ∀ j, ¬ (p : ℤ) ∣ d j) :
    (∑ z : ZMod p, Module.finrank (ZMod p)
      (Module.End.eigenspace (A.map (Int.castRingHom (ZMod p))).toLin' z)) =
    ∑ j, e j * Nat.card {P : Ideal (𝓞 (K j)) // P.IsPrime ∧ P ≠ ⊥ ∧ P.cardQuot = p} := by
  let φ := Int.castRingHom (ZMod p)
  have hp : φ (∏ j, g j).discr ≠ 0 := by
    exact fun hz => hgood ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hz)
  have hann := aeval_prod_characteristic_factors_eq_zero_of_isSymm hA g e hchar
  rw [sum_finrank_eigenspaces_map_eq_weighted_root_count A φ g e hmonic hchar hann hp]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hP := card_primeIdeals_eq_card_roots_of_not_dvd_discriminant (B j) (θ j)
    (hgen j) (hdisc j) (hgoodField j)
  rw [← RingOfIntegers.minpoly_coe, hmin j] at hP
  exact (card_distinct_roots_eq_card_root_subtype ((g j).map φ) ((hmonic j).map φ).ne_zero).trans hP.symm

end Bernoulli
