module

public import Bernoulli.Halasz
public import Bernoulli.InverseCountRelations
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Halász bounds from relations with many distinct coordinates

Relations with few distinct indices are bounded by counting all tuples
supported on a small set. This leaves the restricted relation count used
by the inverse Littlewood–Offord argument.
-/

open scoped BigOperators
namespace Bernoulli

private theorem card_tuples_with_few_indices_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m d : ℕ) (hd : d ≤ Fintype.card ι) :
    (Finset.univ.filter (fun t : Fin m → ι × Bool =>
      (Finset.univ.image fun j => (t j).1).card ≤ d)).card ≤
        (Fintype.card ι).choose d * (2 * d) ^ m := by
  classical
  let S := (Finset.univ : Finset ι).powersetCard d
  let f (a : Σ s : ↥S, Fin m → ↥s.1 × Bool) (j : Fin m) : ι × Bool :=
    ((a.2 j).1.1, (a.2 j).2)
  have hc (s : ↥S) : s.1.card = d := (Finset.mem_powersetCard.mp s.2).2
  have hcover : (Finset.univ.filter (fun t : Fin m → ι × Bool =>
      (Finset.univ.image fun j => (t j).1).card ≤ d)) ⊆ Finset.univ.image f := by
    intro a ha
    obtain ⟨s, hs, _, hsc⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ (Finset.univ.image fun j => (a j).1))
      (Finset.mem_filter.mp ha).2 (by simpa using hd)
    let u : ↥S := ⟨s, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hsc⟩⟩
    let t (j : Fin m) : ↥s × Bool :=
      (⟨(a j).1, hs (Finset.mem_image_of_mem _ (Finset.mem_univ j))⟩, (a j).2)
    exact Finset.mem_image.mpr ⟨⟨u, t⟩, Finset.mem_univ _, by funext j; exact Prod.eta _⟩
  calc
    _ ≤ (Finset.univ.image f).card := Finset.card_le_card hcover
    _ ≤ (Finset.univ : Finset (Σ s : ↥S, Fin m → ↥s.1 × Bool)).card := Finset.card_image_le
    _ = _ := by
      simp [Fintype.card_sigma, hc, S, Nat.mul_comm 2]

/-- The unrestricted signed relation count differs from the restricted one
by at most the count of tuples whose indices all lie in a small set. -/
public theorem signedZeroRelationCount_le_restricted {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (v : ι → ZMod p) (m d : ℕ) (hd : d ≤ Fintype.card ι) :
    signedZeroRelationCount v m ≤ (bernoulliRestrictedRelations v m (d + 1)).card +
      (Fintype.card ι).choose d * (2 * d) ^ m := by
  classical
  let A := Finset.univ.filter (fun t : Fin m → ι × Bool =>
    (∑ j, (if (t j).2 then 1 else -1) * v (t j).1) = 0)
  let B := bernoulliRestrictedRelations v m (d + 1)
  let C := Finset.univ.filter (fun t : Fin m → ι × Bool =>
    (Finset.univ.image fun j => (t j).1).card ≤ d)
  have hcover : A ⊆ B ∪ C := by
    intro t ht
    have hsum : (∑ j, signedCoordinate (t j).2 (v (t j).1)) = 0 := by
      rw [show (∑ j, signedCoordinate (t j).2 (v (t j).1)) =
          (∑ j, (if (t j).2 then 1 else -1) * v (t j).1) by
        refine Finset.sum_congr rfl fun j _ => ?_
        cases (t j).2 <;> simp [signedCoordinate]]
      exact (Finset.mem_filter.mp ht).2
    by_cases h : (Finset.univ.image fun j => (t j).1).card ≤ d
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_left _
        (mem_bernoulliRestrictedRelations.mpr ⟨hsum, Nat.succ_le_of_lt (Nat.lt_of_not_ge h)⟩)
  change A.card ≤ _
  exact (Finset.card_le_card hcover).trans
    ((Finset.card_union_le B C).trans
      (Nat.add_le_add_left (card_tuples_with_few_indices_le m d hd) B.card))

/-- The concentration estimate in terms of the restricted signed relations
and the explicit contribution from repeated indices. -/
public theorem modularMass_fair_signs_le_halasz_restricted {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [Fact p.Prime] (hp : 2 < p) (v : ι → ZMod p) (z : ZMod p)
    {k : ℕ} (hk : 0 < k) {M : ℝ} (hM : 0 < M)
    (hsupport : 4 * M < ((Finset.univ.filter fun i => v i ≠ 0).card : ℝ))
    (hsize : 16 * (k : ℝ) * M ≤ Fintype.card ι)
    {d : ℕ} (hd : d ≤ Fintype.card ι) :
    modularMass (fun _ : ι → Bool => (1 / 2 : ℝ) ^ Fintype.card ι)
      (fun σ => ∑ i, (if σ i then 1 else -1) * v i) z ≤
        1 / (p : ℝ) +
          8 * (((bernoulliRestrictedRelations v (2 * k) (d + 1)).card : ℝ) +
              ((Fintype.card ι).choose d : ℝ) * (2 * (d : ℝ)) ^ (2 * k)) /
            ((2 * (Fintype.card ι : ℝ)) ^ (2 * k) * Real.sqrt M) +
          Real.exp (-M) := by
  apply (modularMass_fair_signs_le_halasz hp v z hk hM hsupport hsize).trans
  refine add_le_add (add_le_add le_rfl ?_) le_rfl
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast signedZeroRelationCount_le_restricted v (2 * k) d hd

end Bernoulli
