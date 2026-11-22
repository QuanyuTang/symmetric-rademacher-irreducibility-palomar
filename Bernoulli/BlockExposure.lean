module

public import Bernoulli.Ensemble
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Set
public import Mathlib.Logic.Equiv.Prod

/-! Independent coordinate families for the finite probability space. -/

open scoped Classical

namespace Bernoulli

/-- A rectangular collection of distinct upper-triangular positions can be sampled by
row, independently of the signs outside the rectangle. -/
public noncomputable def sampleExposureEquiv {n : ℕ} {ι κ : Type*}
    (edges : ι × κ ↪ UpperIndex n) :
    Sample n ≃ (ι → κ → Bool) × (((Set.range edges)ᶜ : Set (UpperIndex n)) → Bool) :=
  let split : ((ι × κ) ⊕ ((Set.range edges)ᶜ : Set (UpperIndex n))) ≃ UpperIndex n :=
    (Equiv.sumCongr (Equiv.ofInjective edges edges.injective) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range edges))
  (Equiv.arrowCongr split.symm (Equiv.refl Bool)).trans
    ((Equiv.sumArrowEquivProdArrow _ _ _).trans
      (Equiv.prodCongr (Equiv.curry _ _ _) (Equiv.refl _)))

public theorem sampleExposureEquiv_fst {n : ℕ} {ι κ : Type*} (edges : ι × κ ↪ UpperIndex n)
    (a : Sample n) (i : ι) (j : κ) : (sampleExposureEquiv edges a).1 i j = a (edges (i, j)) := by
  simp [sampleExposureEquiv, Equiv.arrowCongr, Equiv.curry]

/-- The outside coordinates keep their signs in the product space. -/
public theorem sampleExposureEquiv_snd {n : ℕ} {ι κ : Type*} (edges : ι × κ ↪ UpperIndex n)
    (a : Sample n) (j : ↥((Set.range edges)ᶜ : Set (UpperIndex n))) :
    (sampleExposureEquiv edges a).2 j = a j.1 := by
  simp [sampleExposureEquiv, Equiv.arrowCongr]

/-- With disjoint row and column sets, the unordered edge of each pair determines the pair. -/
@[expose] public def disjointEdgeEmbedding {n : ℕ} {R S : Finset (Fin n)} (h : Disjoint R S) :
    (R × S) ↪ UpperIndex n where
  toFun ij := ⟨(min ij.1.1 ij.2.1, max ij.1.1 ij.2.1),
    le_trans (min_le_left ..) (le_max_left ..)⟩
  inj' := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    have hmin : min i.1 j.1 = min i'.1 j'.1 := congrArg (fun x => x.1.1) hij
    have hmax : max i.1 j.1 = max i'.1 j'.1 := congrArg (fun x => x.1.2) hij
    rcases le_total i.1 j.1 with h₁ | h₁ <;> rcases le_total i'.1 j'.1 with h₂ | h₂
    · rw [min_eq_left h₁, min_eq_left h₂] at hmin
      rw [max_eq_right h₁, max_eq_right h₂] at hmax
      exact Prod.ext (Subtype.ext hmin) (Subtype.ext hmax)
    · rw [min_eq_left h₁, min_eq_right h₂] at hmin
      exact (Finset.disjoint_left.mp h i.2 (hmin ▸ j'.2)).elim
    · rw [min_eq_right h₁, min_eq_left h₂] at hmin
      exact (Finset.disjoint_left.mp h i'.2 (hmin ▸ j.2)).elim
    · rw [min_eq_right h₁, min_eq_right h₂] at hmin
      rw [max_eq_left h₁, max_eq_left h₂] at hmax
      exact Prod.ext (Subtype.ext hmax) (Subtype.ext hmin)

/-- Each exposed matrix entry reads exactly its independent sign in the product space. -/
public theorem matrix_apply_of_disjoint_exposure {n : ℕ} {R S : Finset (Fin n)} (h : Disjoint R S)
    (a : Sample n) (i : R) (j : S) :
    matrix a i j = if (sampleExposureEquiv (disjointEdgeEmbedding h) a).1 i j then 1 else -1 := by
  rw [sampleExposureEquiv_fst]
  rfl

/-- Under a uniform product law the probability of satisfying coordinate-wise predicates
is the product of the individual probabilities. -/
public theorem card_pi_predicates_div_card {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (P : ∀ i, α i → Prop) :
    (Fintype.card {b : ∀ i, α i // ∀ i, P i (b i)} : ℝ) / Fintype.card (∀ i, α i) =
      ∏ i, (Fintype.card {x : α i // P i x} : ℝ) / Fintype.card (α i) := by
  rw [Fintype.card_congr (Equiv.subtypePiEquivPi (p := P)), Fintype.card_pi, Fintype.card_pi,
    Nat.cast_prod, Nat.cast_prod, Finset.prod_div_distrib]

end Bernoulli
