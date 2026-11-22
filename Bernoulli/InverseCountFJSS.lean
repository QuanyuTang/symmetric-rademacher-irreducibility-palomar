module

public import Bernoulli.InverseCountRelations
public import Bernoulli.RankVectorSupport
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# The inverse Littlewood–Offord counting step for random symmetric matrices

For a fixed support, a bound on the count of signed relations on every subset of
a prescribed size gives a bound on the number of vectors. Summing this bound over
the possible supports gives the form used in Appendix B of Ferber, Jain, Sah and
Sawhney. Deletion only needs relations on one fixed-size subset at each step.
-/

namespace Bernoulli

/-- Assignments with a prescribed lower relation density on every subset of size `base`. -/
public noncomputable def relationRichAssignments {ι K : Type*} [DecidableEq ι]
    [AddCommGroup K] [Fintype K] (s : Finset ι) (m r base : ℕ) (δ : ℝ) : Finset (s → K) := by
  classical
  exact Finset.univ.filter fun a => ∀ t : Finset ι, ∀ ht : t ⊆ s, t.card = base →
    δ * (2 * (base : ℝ)) ^ m ≤ (bernoulliRestrictedRelations (restrictAssignment ht a) m r).card

@[simp] public theorem mem_relationRichAssignments {ι K : Type*} [DecidableEq ι]
    [AddCommGroup K] [Fintype K] {s : Finset ι} {m r base : ℕ} {δ : ℝ} {a : s → K} :
    a ∈ relationRichAssignments s m r base δ ↔
      ∀ t : Finset ι, ∀ ht : t ⊆ s, t.card = base →
        δ * (2 * (base : ℝ)) ^ m ≤ (bernoulliRestrictedRelations (restrictAssignment ht a) m r).card := by
  classical
  simp [relationRichAssignments]

/-- The fixed-support count uses one inverse-density factor for each deletion. -/
public theorem card_relationRichAssignments_le {ι K : Type*} [DecidableEq ι]
    [AddCommGroup K] [Fintype K] {s : Finset ι} (m r base : ℕ) (hbase : 0 < base)
    (hs : base ≤ s.card) {α δ : ℝ} (hα₀ : 0 < α) (hδ : 0 < δ)
    (hα : α * ((m + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ) ≤ 2 * (r : ℝ)) :
    ((relationRichAssignments (K := K) s (m + 1) r base δ).card : ℝ) ≤
      (Fintype.card K : ℝ) ^ base * (1 / (α * δ)) ^ (s.card - base) := by
  classical
  apply card_le_pow_of_hereditary_deletion_relations
    (fun s => relationRichAssignments s (m + 1) r base δ) m base hbase (mul_pos hα₀ hδ) _ _ s hs
  · intro s i _ a ha
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun t ht htc => ?_⟩
    exact (Finset.mem_filter.mp ha).2 t (ht.trans (Finset.erase_subset i s)) htc
  · intro s t ht htc _ a ha
    have hd : δ * (2 * (base : ℝ)) ^ (m + 1) ≤
        (bernoulliRestrictedRelations (restrictAssignment ht a) (m + 1) r).card :=
      (Finset.mem_filter.mp ha).2 t ht htc
    rw [mul_assoc]
    exact (mul_le_mul_of_nonneg_left hd hα₀.le).trans
      (restrictedRelations_fraction_le_deletionRelations (restrictAssignment ht a) m r hα)

/-- Vectors of a given support size with a prescribed lower relation density on its
subsets of size `base`. -/
public noncomputable def relationRichVectors {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup K] [Fintype K] (m r base d : ℕ) (δ : ℝ) : Finset (ι → K) := by
  classical
  exact Finset.univ.filter fun a => (finiteVectorSupport a).card = d ∧
    (fun i : ↥(finiteVectorSupport a) => a i.1) ∈
      relationRichAssignments (finiteVectorSupport a) m r base δ

@[simp] public theorem mem_relationRichVectors {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup K] [Fintype K] {m r base d : ℕ} {δ : ℝ} {a : ι → K} :
    a ∈ relationRichVectors m r base d δ ↔ (finiteVectorSupport a).card = d ∧
    (fun i : ↥(finiteVectorSupport a) => a i.1) ∈
      relationRichAssignments (finiteVectorSupport a) m r base δ := by
  classical
  simp only [relationRichVectors, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Counting vectors over all supports contributes a binomial factor. -/
public theorem card_relationRichVectors_le {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup K] [Fintype K] (m r base d : ℕ) (hbase : 0 < base) (hs : base ≤ d)
    {α δ : ℝ} (hα₀ : 0 < α) (hδ : 0 < δ)
    (hα : α * ((m + 1 : ℕ) : ℝ) + ((m + 1 : ℕ) : ℝ) ≤ 2 * (r : ℝ)) :
    ((relationRichVectors (ι := ι) (K := K) (m + 1) r base d δ).card : ℝ) ≤
      ((Fintype.card ι).choose d : ℝ) *
        ((Fintype.card K : ℝ) ^ base * (1 / (α * δ)) ^ (d - base)) := by
  classical
  let V := relationRichVectors (ι := ι) (K := K) (m + 1) r base d δ
  let S := (Finset.univ : Finset ι).powersetCard d
  let B (s : Finset ι) := relationRichAssignments (K := K) s (m + 1) r base δ
  let T := Σ s : ↥S, ↥(B s.1)
  let f (a : ↥V) : T :=
    ⟨⟨finiteVectorSupport a.1, Finset.mem_powersetCard.mpr
      ⟨Finset.subset_univ _, (Finset.mem_filter.mp a.2).2.1⟩⟩,
      ⟨fun i => a.1 i.1, (Finset.mem_filter.mp a.2).2.2⟩⟩
  have hf : Function.Injective f := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ heq
    have hsupp : finiteVectorSupport a = finiteVectorSupport b :=
      congrArg (fun x : T => x.1.1) heq
    have hvals : ∀ i : ι, a i = b i := by
      intro i
      by_cases hmem : i ∈ finiteVectorSupport a
      · let eval (x : T) : K := if hi : i ∈ x.1.1 then x.2.1 ⟨i, hi⟩ else 0
        have hmem' : i ∈ finiteVectorSupport b := hsupp ▸ hmem
        simpa only [eval, f, dite_eq_left hmem, dite_eq_left hmem'] using congrArg eval heq
      · have hmem' : i ∉ finiteVectorSupport b := hsupp ▸ hmem
        have hza : a i = 0 := by simpa only [mem_finiteVectorSupport, not_not] using hmem
        have hzb : b i = 0 := by simpa only [mem_finiteVectorSupport, not_not] using hmem'
        exact hza.trans hzb.symm
    exact Subtype.ext (funext hvals)
  let U : ℝ := (Fintype.card K : ℝ) ^ base * (1 / (α * δ)) ^ (d - base)
  calc
    (V.card : ℝ) ≤ (Fintype.card T : ℝ) := by
      have hc := Fintype.card_le_of_injective f hf
      rw [Fintype.card_coe] at hc
      exact_mod_cast hc
    _ = ∑ s : ↥S, ((B s.1).card : ℝ) := by simp [T, Fintype.card_sigma]
    _ ≤ ∑ _s : ↥S, U := by
      apply Finset.sum_le_sum
      intro s _
      have hc : s.1.card = d := (Finset.mem_powersetCard.mp s.2).2
      have h := card_relationRichAssignments_le (K := K) m r base hbase
        (show base ≤ s.1.card by rw [hc]; exact hs) hα₀ hδ hα
      rw [hc] at h
      exact h
    _ = _ := by simp [U, S, Finset.card_powersetCard, nsmul_eq_mul]

/-- Appendix B.3 in the support range used by FJSS. The cutoff `101*k/100 + 1` is the
integer form of strictly more than `1.01 k` distinct indices. Only the condition on
subsets of size `base` is needed for this stronger bound. -/
public theorem card_fjss_relationRichVectors_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (k base d : ℕ) (hk : 0 < k) (hbase : 0 < base) (hs : base ≤ d)
    {level : ℝ} (hlevel : 0 < level) :
    ((relationRichVectors (ι := ι) (K := ZMod p) (2 * k) (101 * k / 100 + 1)
        base d (level / p)).card : ℝ) ≤
      ((Fintype.card ι).choose d : ℝ) * ((p : ℝ) ^ base * (100 * p / level) ^ (d - base)) := by
  have hm : 2 * k - 1 + 1 = 2 * k := by omega
  have hcut : (101 : ℝ) * k < 100 * ((101 * k / 100 + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 101 * k < 100 * (101 * k / 100 + 1) by omega)
  have hα : (1 / 100 : ℝ) * ((2 * k - 1 + 1 : ℕ) : ℝ) + ((2 * k - 1 + 1 : ℕ) : ℝ) ≤
      2 * ((101 * k / 100 + 1 : ℕ) : ℝ) := by
    rw [hm, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  have hp : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
  have h := card_relationRichVectors_le (ι := ι) (K := ZMod p) (2 * k - 1) _ base d
    hbase hs (show 0 < (1 / 100 : ℝ) by norm_num) (div_pos hlevel hp) hα
  rw [hm, ZMod.card] at h
  have hratio : (1 : ℝ) / (1 / 100 * (level / p)) = 100 * p / level := by
    field_simp
  rwa [hratio] at h

end Bernoulli
