module

public import Bernoulli.InverseCount
import Mathlib.Tactic

/-!
# A singleton coordinate in a signed relation

This is the relation-counting input in Ferber, Jain, Sah and Sawhney,
*Random symmetric matrices: rank distribution and irreducibility of the
characteristic polynomial*, Appendix B. The threshold on the number of distinct
coordinates gives many singleton slots, and slot permutation symmetry lets us
use a fixed slot for recovering a coordinate.
-/

open scoped BigOperators

namespace Bernoulli

/-- Signed zero relations with at least `d` distinct indices. -/
public noncomputable def bernoulliRestrictedRelations {ι K : Type*} [Fintype ι]
    [DecidableEq ι] [AddCommGroup K] (a : ι → K) (m d : ℕ) : Finset (Fin m → ι × Bool) := by
  classical
  exact Finset.univ.filter fun τ =>
    (∑ j, signedCoordinate (τ j).2 (a (τ j).1)) = 0 ∧
      d ≤ (Finset.univ.image fun j => (τ j).1).card

@[simp] public theorem mem_bernoulliRestrictedRelations {ι K : Type*} [Fintype ι]
    [DecidableEq ι] [AddCommGroup K] {a : ι → K} {m d : ℕ} {τ : Fin m → ι × Bool} :
    τ ∈ bernoulliRestrictedRelations a m d ↔
      (∑ j, signedCoordinate (τ j).2 (a (τ j).1)) = 0 ∧
        d ≤ (Finset.univ.image fun j => (τ j).1).card := by
  classical
  simp [bernoulliRestrictedRelations]

private def SingletonSlot {ι : Type*} {m : ℕ} (τ : Fin m → ι × Bool) (j : Fin m) : Prop :=
  ∀ k, k ≠ j → (τ k).1 ≠ (τ j).1

private noncomputable instance {ι : Type*} {m : ℕ} (τ : Fin m → ι × Bool) (j : Fin m) :
    Decidable (SingletonSlot τ j) := Classical.propDecidable _

private noncomputable def singletonSlots {ι : Type*} {m : ℕ} (τ : Fin m → ι × Bool) :
    Finset (Fin m) := by
  classical
  exact Finset.univ.filter (SingletonSlot τ)

private lemma two_mul_card_image_le_slots_add_card_singletons {ι : Type*} [DecidableEq ι]
    {m : ℕ} (τ : Fin m → ι × Bool) :
    2 * (Finset.univ.image fun j => (τ j).1).card ≤ m + (singletonSlots τ).card := by
  classical
  let f : Fin m → ι := fun j => (τ j).1
  let T := Finset.univ.image f
  have hs : (singletonSlots τ).image f ⊆ T :=
    Finset.image_subset_image (Finset.subset_univ _)
  have h₁ := Finset.card_eq_sum_card_image f (Finset.univ : Finset (Fin m))
  rw [Finset.card_univ, Fintype.card_fin] at h₁
  have h₂ := Finset.card_eq_sum_card_fiberwise
    (f := f) (s := singletonSlots τ) (t := T) (fun j hj => hs (Finset.mem_image_of_mem f hj))
  calc
    _ = ∑ _x ∈ T, (2 : ℕ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact Nat.mul_comm _ _
    _ ≤ ∑ x ∈ T, ((Finset.univ.filter fun i => f i = x).card +
        ((singletonSlots τ).filter fun i => f i = x).card) := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hx
      by_cases hsing : SingletonSlot τ j
      · have hpos₁ : 0 < (Finset.univ.filter fun i => f i = x).card :=
          Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
        have hpos₂ : 0 < ((singletonSlots τ).filter fun i => f i = x).card :=
          Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr
            ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsing⟩, hj⟩⟩
        omega
      · unfold SingletonSlot at hsing
        push Not at hsing
        obtain ⟨i, hij, hi⟩ := hsing
        have htwo : 1 < (Finset.univ.filter fun i => f i = x).card :=
          Finset.one_lt_card.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi.trans hj⟩,
            j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hij⟩
        omega
    _ = _ := by rw [Finset.sum_add_distrib, ← h₂]; exact congrArg (· + _) h₁.symm

private lemma singletonSlot_comp {ι : Type*} {m : ℕ} (τ : Fin m → ι × Bool)
    (e : Equiv.Perm (Fin m)) (j : Fin m) : SingletonSlot (τ ∘ e) j ↔ SingletonSlot τ (e j) := by
  constructor
  · intro h k hk
    obtain ⟨i, rfl⟩ := e.surjective k
    exact h i (fun he => hk (congrArg e he))
  · intro h k hk
    exact h (e k) (fun he => hk (e.injective he))

private lemma mem_restrictedRelations_comp {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup K] (a : ι → K) {m d : ℕ} (τ : Fin m → ι × Bool)
    (e : Equiv.Perm (Fin m)) :
    τ ∘ e ∈ bernoulliRestrictedRelations a m d ↔ τ ∈ bernoulliRestrictedRelations a m d := by
  classical
  have himage : (Finset.univ.image fun j => ((τ ∘ e) j).1) =
      (Finset.univ.image fun j => (τ j).1) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
    exact ⟨fun ⟨j, hj⟩ => ⟨e j, hj⟩, fun ⟨j, hj⟩ => ⟨e.symm j, by simp [hj]⟩⟩
  have hsum : (∑ j, signedCoordinate ((τ ∘ e) j).2 (a ((τ ∘ e) j).1)) =
      ∑ j, signedCoordinate (τ j).2 (a (τ j).1) :=
    Fintype.sum_equiv e _ _ fun _ => rfl
  rw [mem_bernoulliRestrictedRelations, mem_bernoulliRestrictedRelations, hsum, himage]

private lemma card_filter_singletonSlot_eq {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup K] (a : ι → K) {m d : ℕ} (i j : Fin m) :
    ((bernoulliRestrictedRelations a m d).filter fun τ => SingletonSlot τ i).card =
      ((bernoulliRestrictedRelations a m d).filter fun τ => SingletonSlot τ j).card := by
  classical
  let e := Equiv.swap i j
  have he : e j = i := Equiv.swap_apply_right i j
  have he' : e.symm i = j := by rw [← he, e.symm_apply_apply]
  refine Finset.card_bij (fun τ _ => τ ∘ e) ?_ ?_ ?_
  · intro τ hτ
    rcases Finset.mem_filter.mp hτ with ⟨hr, hs⟩
    refine Finset.mem_filter.mpr ⟨(mem_restrictedRelations_comp a τ e).mpr hr, ?_⟩
    exact (singletonSlot_comp τ e j).mpr (he.symm ▸ hs)
  · intro τ _ σ _ h
    funext k
    obtain ⟨l, rfl⟩ := e.surjective k
    exact congrFun h l
  · intro σ hσ
    rcases Finset.mem_filter.mp hσ with ⟨hr, hs⟩
    refine ⟨σ ∘ e.symm, Finset.mem_filter.mpr
      ⟨(mem_restrictedRelations_comp a σ e.symm).mpr hr, (singletonSlot_comp σ e.symm i).mpr ?_⟩,
      funext fun j => congrArg σ (e.symm_apply_apply j)⟩
    rwa [he']

private lemma card_singletonRelations_le_deletionRelations {ι K : Type*} [DecidableEq ι]
    [AddCommGroup K] {t : Finset ι} (a : t → K) (m d : ℕ) :
    ((bernoulliRestrictedRelations a (m + 1) d).filter fun τ => SingletonSlot τ 0).card ≤
      (deletionRelations a m).card := by
  classical
  let S := (bernoulliRestrictedRelations a (m + 1) d).filter fun τ => SingletonSlot τ 0
  let encode (τ : ↥S) : DeletionWitness t m :=
    ⟨(τ.1 0).1, (fun j => ⟨(τ.1 j.succ).1.1, Finset.mem_erase.mpr
        ⟨fun h => (Finset.mem_filter.mp τ.2).2 j.succ (Fin.succ_ne_zero _) (Subtype.ext h),
          (τ.1 j.succ).1.2⟩⟩), (fun j => (τ.1 j.succ).2), (τ.1 0).2⟩
  have hrel (τ : ↥S) : encode τ ∈ deletionRelations a m := by
    apply mem_deletionRelations.mpr
    have hzero := (mem_bernoulliRestrictedRelations.mp (Finset.mem_filter.mp τ.2).1).1
    simpa only [Fin.sum_univ_succ, DeletionWitness.IsRelation, encode] using hzero
  let f (τ : ↥S) : ↥(deletionRelations a m) := ⟨encode τ, hrel τ⟩
  have hf : Function.Injective f := by
    intro τ σ h
    have heq : encode τ = encode σ := congrArg Subtype.val h
    have hpivot : (τ.1 0).1 = (σ.1 0).1 := congrArg Sigma.fst heq
    have hval : (fun j => ((encode τ).2.1 j).1) = (fun j => ((encode σ).2.1 j).1) :=
      congrArg (fun w : DeletionWitness t m => fun j => (w.2.1 j).1) heq
    have hpivotSign : (τ.1 0).2 = (σ.1 0).2 :=
      congrArg (fun w : DeletionWitness t m => w.2.2.2) heq
    have htailSign (j : Fin m) : (τ.1 j.succ).2 = (σ.1 j.succ).2 :=
      congrArg (fun w : DeletionWitness t m => w.2.2.1 j) heq
    apply Subtype.ext
    funext j
    refine Fin.cases ?_ (fun k => ?_) j
    · exact Prod.ext hpivot hpivotSign
    · exact Prod.ext (Subtype.ext (congrFun hval k)) (htailSign k)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- If `α (m+1) + (m+1) ≤ 2d`, at least a fraction `α` of the signed zero
relations with `d` distinct indices have a singleton in the distinguished slot. -/
public theorem restrictedRelations_fraction_le_deletionRelations {ι K : Type*} [DecidableEq ι]
    [AddCommGroup K] {t : Finset ι} (a : t → K) (m d : ℕ) {α : ℝ}
    (hα : α * ((m + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ) ≤ 2 * (d : ℝ)) :
    α * ((bernoulliRestrictedRelations a (m + 1) d).card : ℝ) ≤
      (deletionRelations a m).card := by
  classical
  let R := bernoulliRestrictedRelations a (m + 1) d
  let S (i : Fin (m + 1)) := R.filter fun τ => SingletonSlot τ i
  have hdouble : (m + 1) * (S 0).card = ∑ τ ∈ R, (singletonSlots τ).card := by
    calc
      _ = ∑ i : Fin (m + 1), (S i).card := by
        have h (i : Fin (m + 1)) : (S i).card = (S 0).card :=
          card_filter_singletonSlot_eq a (d := d) i 0
        simp [h]
      _ = _ := by
        simp only [S, singletonSlots, Finset.card_filter]
        exact Finset.sum_comm
  have hlower : (((m + 1 : ℕ) : ℝ) * α) * (R.card : ℝ) ≤
      ∑ τ ∈ R, ((singletonSlots τ).card : ℝ) := by
    rw [mul_comm _ (R.card : ℝ), ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun τ hτ => ?_
    have hd := (mem_bernoulliRestrictedRelations.mp hτ).2
    have hs := two_mul_card_image_le_slots_add_card_singletons τ
    have hn : 2 * d ≤ (m + 1) + (singletonSlots τ).card := (Nat.mul_le_mul_left 2 hd).trans hs
    have hr : (2 : ℝ) * (d : ℝ) ≤ ((m + 1 : ℕ) : ℝ) + ((singletonSlots τ).card : ℝ) := by
      exact_mod_cast hn
    linarith
  have hdouble' : ((m + 1 : ℕ) : ℝ) * ((S 0).card : ℝ) =
      ∑ τ ∈ R, ((singletonSlots τ).card : ℝ) := by exact_mod_cast hdouble
  rw [← hdouble', mul_assoc] at hlower
  have hsing : α * (R.card : ℝ) ≤ (S 0).card :=
    (mul_le_mul_iff_right₀ (show 0 < ((m + 1 : ℕ) : ℝ) by positivity)).mp hlower
  exact hsing.trans (by exact_mod_cast card_singletonRelations_le_deletionRelations a m d)

end Bernoulli
