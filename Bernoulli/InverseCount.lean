module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Inverse Littlewood–Offord counting by deletion of a coordinate

An ordered signed zero relation with a distinguished coordinate that occurs once
recovers the value at that coordinate from an assignment on the remaining support.
To count a hereditary family, one can search for these relations on any fixed
subset of the current support of the prescribed size.
-/

open scoped BigOperators

namespace Bernoulli

/-- Restriction of an assignment to a subset of its domain. -/
@[expose] public def restrictAssignment {ι K : Type*} {s t : Finset ι}
    (h : t ⊆ s) (a : s → K) : t → K := fun i => a ⟨i.1, h i.2⟩

/-- A distinguished index, followed by `m` signed indices different from it,
and the sign at the distinguished index. -/
public abbrev DeletionWitness {ι : Type*} [DecidableEq ι] (t : Finset ι) (m : ℕ) :=
  Σ i : t, ((Fin m → ↥(t.erase i.1)) × (Fin m → Bool) × Bool)

/-- The signs in a signed zero relation. -/
@[expose] public def signedCoordinate {K : Type*} [Neg K] (b : Bool) (x : K) : K :=
  if b then x else -x

/-- The equality associated with a deletion witness. -/
@[expose] public def DeletionWitness.IsRelation {ι K : Type*} [DecidableEq ι] [AddCommGroup K]
    {t : Finset ι} {m : ℕ} (w : DeletionWitness t m) (a : t → K) : Prop :=
  signedCoordinate w.2.2.2 (a w.1) +
    ∑ j, signedCoordinate (w.2.2.1 j) (a ⟨(w.2.1 j).1, Finset.mem_of_mem_erase (w.2.1 j).2⟩) = 0

/-- The finite set of signed zero relations with a distinguished singleton index. -/
public noncomputable def deletionRelations {ι K : Type*} [DecidableEq ι] [AddCommGroup K]
    {t : Finset ι} (a : t → K) (m : ℕ) : Finset (DeletionWitness t m) := by
  classical
  exact Finset.univ.filter (fun w => w.IsRelation a)

@[simp] public theorem mem_deletionRelations {ι K : Type*} [DecidableEq ι] [AddCommGroup K]
    {t : Finset ι} {m : ℕ} {a : t → K} {w : DeletionWitness t m} :
    w ∈ deletionRelations a m ↔ w.IsRelation a := by
  classical
  simp [deletionRelations]

private lemma card_deletionWitness {ι : Type*} [DecidableEq ι]
    (t : Finset ι) (m : ℕ) : Fintype.card (DeletionWitness t m) =
      t.card * ((t.card - 1) ^ m * (2 ^ m * 2)) := by
  classical
  rw [Fintype.card_sigma]
  simp [Finset.card_erase_of_mem, Fintype.card_prod]

private lemma deletionWitness_reconstruct {ι K : Type*} [DecidableEq ι] [AddCommGroup K]
    {s t : Finset ι} (ht : t ⊆ s) {m : ℕ} (w : DeletionWitness t m) {a b : s → K}
    (ha : w.IsRelation (restrictAssignment ht a))
    (hb : w.IsRelation (restrictAssignment ht b))
    (hrest : restrictAssignment (Finset.erase_subset w.1.1 s) a =
      restrictAssignment (Finset.erase_subset w.1.1 s) b) : a = b := by
  have heach (j : s) (hj : j.1 ≠ w.1.1) : a j = b j :=
    congrFun hrest ⟨j.1, Finset.mem_erase.mpr ⟨hj, j.2⟩⟩
  have hsum : (∑ j : Fin m, signedCoordinate (w.2.2.1 j)
      (restrictAssignment ht a ⟨(w.2.1 j).1, Finset.mem_of_mem_erase (w.2.1 j).2⟩)) =
    ∑ j : Fin m, signedCoordinate (w.2.2.1 j)
      (restrictAssignment ht b ⟨(w.2.1 j).1, Finset.mem_of_mem_erase (w.2.1 j).2⟩) := by
    refine Finset.sum_congr rfl fun j _ => congrArg _ (heach _ ?_)
    exact (Finset.mem_erase.mp (w.2.1 j).2).1
  unfold DeletionWitness.IsRelation at ha hb
  rw [hsum] at ha
  have hpivot := add_right_cancel (ha.trans hb.symm)
  have hpivot' : a ⟨w.1.1, ht w.1.2⟩ = b ⟨w.1.1, ht w.1.2⟩ := by
    cases hs : w.2.2.2 <;> simpa [signedCoordinate, restrictAssignment, hs] using hpivot
  funext j
  by_cases hj : j.1 = w.1.1
  · have heq : j = ⟨w.1.1, ht w.1.2⟩ := Subtype.ext hj
    simpa only [heq] using hpivot'
  · exact heach j hj

/-- One step of the inverse Littlewood–Offord count. The tested subset `t` is fixed
across the family, and the bounds on the smaller families are for the coordinates
of `s` other than the distinguished index. -/
public theorem card_le_of_deletion_relations {ι K : Type*} [DecidableEq ι]
    [AddCommGroup K] [Fintype K] {s t : Finset ι} (ht : t ⊆ s) (ht₀ : 0 < t.card)
    (m : ℕ) (F : (s : Finset ι) → Finset (s → K)) {β U : ℝ} (hβ : 0 < β) (hU : 0 ≤ U)
    (hrestrict : ∀ i : t, ∀ a ∈ F s,
      restrictAssignment (Finset.erase_subset i.1 s) a ∈ F (s.erase i.1))
    (hbound : ∀ i : t, ((F (s.erase i.1)).card : ℝ) ≤ U)
    (hdense : ∀ a ∈ F s,
      β * (2 * (t.card : ℝ)) ^ (m + 1) ≤ (deletionRelations (restrictAssignment ht a) m).card) :
    ((F s).card : ℝ) ≤ U / β := by
  classical
  let W := DeletionWitness t m
  let C (a : s → K) := deletionRelations (restrictAssignment ht a) m
  let pairs : Finset (Σ _ : s → K, W) := (F s).sigma C
  let target := Σ w : W, ↥(F (s.erase w.1.1))
  let encode (x : ↥pairs) : target :=
    ⟨x.1.2, ⟨restrictAssignment (Finset.erase_subset x.1.2.1.1 s) x.1.1,
      hrestrict x.1.2.1 x.1.1 (Finset.mem_sigma.mp x.2).1⟩⟩
  have hinj : Function.Injective encode := by
    intro ⟨⟨a, w⟩, ha⟩ ⟨⟨b, w'⟩, hb⟩ heq
    have hw : w = w' := congrArg Sigma.fst heq
    subst w'
    have hr : restrictAssignment (Finset.erase_subset w.1.1 s) a =
        restrictAssignment (Finset.erase_subset w.1.1 s) b := by
      have he := (Sigma.mk.inj_iff.mp heq).2
      exact congrArg Subtype.val (eq_of_heq he)
    have h₁ : w.IsRelation (restrictAssignment ht a) :=
      (Finset.mem_filter.mp (Finset.mem_sigma.mp ha).2).2
    have h₂ : w.IsRelation (restrictAssignment ht b) :=
      (Finset.mem_filter.mp (Finset.mem_sigma.mp hb).2).2
    obtain rfl := deletionWitness_reconstruct ht w h₁ h₂ hr
    rfl
  have hupper : (pairs.card : ℝ) ≤ (Fintype.card W : ℝ) * U := by
    calc
      (pairs.card : ℝ) ≤ (Fintype.card target : ℝ) := by
        have hc := Fintype.card_le_of_injective encode hinj
        rw [Fintype.card_coe] at hc
        exact_mod_cast hc
      _ = ∑ w : W, ((F (s.erase w.1.1)).card : ℝ) := by
        simp [target, Fintype.card_sigma]
      _ ≤ ∑ _w : W, U := Finset.sum_le_sum fun w _ => hbound w.1
      _ = _ := by simp [nsmul_eq_mul]
  have hcard : pairs.card = ∑ a ∈ F s, (C a).card := Finset.card_sigma _ _
  have hlower : ((F s).card : ℝ) * (β * (2 * (t.card : ℝ)) ^ (m + 1)) ≤ (pairs.card : ℝ) := by
    rw [hcard, Nat.cast_sum, ← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum hdense
  have hwsize : (Fintype.card W : ℝ) ≤ (2 * (t.card : ℝ)) ^ (m + 1) := by
    rw [card_deletionWitness]
    push_cast
    have hpow : ((t.card - 1 : ℕ) : ℝ) ^ m ≤ (t.card : ℝ) ^ m :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.sub_le t.card 1) _
    calc
      _ ≤ (t.card : ℝ) * ((t.card : ℝ) ^ m * ((2 : ℝ) ^ m * 2)) := by gcongr
      _ = _ := by rw [mul_pow, pow_succ (t.card : ℝ)]; ring
  have h := hlower.trans (hupper.trans (mul_le_mul_of_nonneg_right hwsize hU))
  apply (le_div_iff₀ hβ).mpr
  apply (mul_le_mul_iff_right₀ (show 0 < (2 * (t.card : ℝ)) ^ (m + 1) by positivity)).mp
  convert h using 1
  ring

/-- Iterating deletion gives one inverse-density factor for each coordinate removed.
At each step only the assumed density on subsets of size `base` is needed. -/
public theorem card_le_pow_of_hereditary_deletion_relations {ι K : Type*} [DecidableEq ι]
    [AddCommGroup K] [Fintype K] (F : (s : Finset ι) → Finset (s → K))
    (m base : ℕ) (hbase : 0 < base) {β : ℝ} (hβ : 0 < β)
    (hrestrict : ∀ s i, base < s.card → ∀ a ∈ F s,
      restrictAssignment (Finset.erase_subset i s) a ∈ F (s.erase i))
    (hdense : ∀ s t (ht : t ⊆ s), t.card = base → base < s.card → ∀ a ∈ F s,
      β * (2 * (base : ℝ)) ^ (m + 1) ≤ (deletionRelations (restrictAssignment ht a) m).card)
    (s : Finset ι) (hs : base ≤ s.card) :
    ((F s).card : ℝ) ≤ (Fintype.card K : ℝ) ^ base * (1 / β) ^ (s.card - base) := by
  classical
  induction hj : s.card using Nat.strong_induction_on generalizing s with
  | h j ih =>
    by_cases hlt : base < s.card
    · obtain ⟨t, ht, htcard⟩ := Finset.exists_subset_card_eq hs
      have hbase_cast : 0 < t.card := htcard ▸ hbase
      let U : ℝ := (Fintype.card K : ℝ) ^ base * (1 / β) ^ (s.card - 1 - base)
      have hU : 0 ≤ U := by dsimp [U]; positivity
      have hstep := card_le_of_deletion_relations ht hbase_cast m F hβ hU
        (fun i => hrestrict s i hlt) (fun i => ?_) (fun a ha => ?_)
      · calc
          _ ≤ U / β := hstep
          _ = _ := by
            have hexp : s.card - base = (s.card - 1 - base) + 1 := by omega
            rw [← hj, hexp, pow_succ]
            dsimp only [U]
            rw [← mul_assoc, mul_one_div]
      · have he := Finset.card_erase_of_mem (ht i.2)
        simpa only [U, he] using ih (s.erase i.1).card (by omega) (s.erase i.1) (by omega) rfl
      · simpa only [htcard] using hdense s t ht htcard hlt a ha
    · have ht : s.card = base := by omega
      have hcard := Finset.card_le_univ (F s)
      rw [Fintype.card_fun, Fintype.card_coe, ht] at hcard
      rw [← hj, ht, Nat.sub_self, pow_zero, mul_one]
      exact_mod_cast hcard

end Bernoulli
