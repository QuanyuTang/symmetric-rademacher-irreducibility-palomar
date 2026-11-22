module

public import Bernoulli.HalaszRestricted
public import Bernoulli.InverseCountFJSS
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Relation counts on subsets of a fixed size

The smallest restricted relation count on a support determines the atom
bound on one subset and the inverse counting bound for all vectors at that
level. The count is an integer, so the union over levels is finite.
-/

open scoped BigOperators
namespace Bernoulli

/-- The restricted count on the coordinates indexed by a finset. -/
@[expose] public noncomputable def restrictedCountOn {ι : Type*} [DecidableEq ι]
    {p : ℕ} (v : ι → ZMod p) (k : ℕ) (s : Finset ι) : ℕ :=
  (bernoulliRestrictedRelations (fun i : ↥s => v i.1) (2 * k) (101 * k / 100 + 1)).card

/-- The minimum among base-size subsets of the support is attained at this count. -/
@[expose] public def IsMinimumRestrictedCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (v : ι → ZMod p) (k b c : ℕ) : Prop :=
  (∀ s : Finset ι, s ⊆ finiteVectorSupport v → s.card = b → c ≤ restrictedCountOn v k s) ∧
  ∃ s : Finset ι, s ⊆ finiteVectorSupport v ∧ s.card = b ∧ restrictedCountOn v k s = c

public theorem exists_minimumRestrictedCount {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (v : ι → ZMod p) (k b : ℕ) (hb : b ≤ (finiteVectorSupport v).card) :
    ∃ c ≤ (2 * b) ^ (2 * k), IsMinimumRestrictedCount v k b c := by
  classical
  let S := (finiteVectorSupport v).powersetCard b
  obtain ⟨s, hs, hmin⟩ := S.exists_min_image (restrictedCountOn v k)
    (Finset.powersetCard_nonempty.mpr hb)
  obtain ⟨hss, hsb⟩ := Finset.mem_powersetCard.mp hs
  refine ⟨restrictedCountOn v k s, ?_, ?_, ⟨s, hss, hsb, rfl⟩⟩
  · have h := Finset.card_le_univ (bernoulliRestrictedRelations (fun i : ↥s => v i.1)
      (2 * k) (101 * k / 100 + 1))
    simpa [restrictedCountOn, Fintype.card_fun, hsb, Nat.mul_comm 2] using h
  · intro t ht htb
    exact hmin t (Finset.mem_powersetCard.mpr ⟨ht, htb⟩)

/-- Normalization by the number of all length-two-k signed tuples on b coordinates. -/
@[expose] public noncomputable def normalizedRestrictedCount (k b c : ℕ) : ℝ :=
  (c : ℝ) / (2 * (b : ℝ)) ^ (2 * k)

/-- Ratio of tuples included in the upper bound for tuples with few distinct indices. -/
@[expose] public noncomputable def repeatedIndexRatio (k b : ℕ) : ℝ :=
  ((b.choose (101 * k / 100) : ℝ) * (2 * ((101 * k / 100 : ℕ) : ℝ)) ^ (2 * k)) /
    (2 * (b : ℝ)) ^ (2 * k)

/-- Vectors of support size d in one integer level of the restricted count. -/
@[expose] public noncomputable def vectorsOfMinimumRestrictedCount {ι : Type*}
    [Fintype ι] [DecidableEq ι] {p : ℕ} [NeZero p] (k b d c : ℕ) : Finset (ι → ZMod p) := by
  classical
  exact Finset.univ.filter fun v =>
    (finiteVectorSupport v).card = d ∧ IsMinimumRestrictedCount v k b c

@[simp] public theorem mem_vectorsOfMinimumRestrictedCount {ι : Type*}
    [Fintype ι] [DecidableEq ι] {p : ℕ} [NeZero p] {k b d c : ℕ} {v : ι → ZMod p} :
    v ∈ vectorsOfMinimumRestrictedCount k b d c ↔
      (finiteVectorSupport v).card = d ∧ IsMinimumRestrictedCount v k b c := by
  simp [vectorsOfMinimumRestrictedCount]

public theorem card_vectorsOfMinimumRestrictedCount_le {ι : Type*}
    [Fintype ι] [DecidableEq ι] {p : ℕ} [NeZero p] {k b d c : ℕ}
    (hk : 0 < k) (hb : 0 < b) (hbd : b ≤ d) (hc : 0 < c) :
    ((vectorsOfMinimumRestrictedCount (ι := ι) (p := p) k b d c).card : ℝ) ≤
      ((Fintype.card ι).choose d : ℝ) *
        ((p : ℝ) ^ b * (100 / normalizedRestrictedCount k b c) ^ (d - b)) := by
  classical
  let δ := normalizedRestrictedCount k b c
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hc' : 0 < (c : ℝ) := by exact_mod_cast hc
  have hp : 0 < (p : ℝ) := by exact_mod_cast NeZero.pos p
  have hnum : 0 < (2 * (b : ℝ)) ^ (2 * k) := by positivity
  have hδ : 0 < δ := div_pos hc' hnum
  let B := relationRichVectors (ι := ι) (K := ZMod p) (2 * k) (101 * k / 100 + 1)
    b d (((p : ℝ) * δ) / p)
  have hsub : vectorsOfMinimumRestrictedCount (ι := ι) (p := p) k b d c ⊆ B := by
    intro v hv
    have hv' := mem_vectorsOfMinimumRestrictedCount.mp hv
    refine mem_relationRichVectors.mpr ⟨hv'.1, mem_relationRichAssignments.mpr ?_⟩
    intro t ht htb
    have h := hv'.2.1 t ht htb
    change (p : ℝ) * δ / p * (2 * (b : ℝ)) ^ (2 * k) ≤ (restrictedCountOn v k t : ℝ)
    rw [show (p : ℝ) * δ / p = δ by field_simp [hp.ne']]
    dsimp [δ, normalizedRestrictedCount]
    rw [div_mul_cancel₀ _ hnum.ne']
    exact_mod_cast h
  have hcount := card_fjss_relationRichVectors_le (ι := ι) (p := p)
    k b d hk hb hbd (mul_pos hp hδ)
  apply (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
  rwa [show (100 * (p : ℝ)) / ((p : ℝ) * δ) = 100 / δ by field_simp [hp.ne', hδ.ne']]
    at hcount

/-- A minimizing subset gives the low atom bound, with the terms depending
only on the subset size and the integer level. -/
public theorem exists_subset_fairSign_atom_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [Fact p.Prime] (hp : 2 < p) {v : ι → ZMod p} {k b c : ℕ}
    (hmin : IsMinimumRestrictedCount v k b c) (hk : 0 < k) {M : ℝ} (hM : 0 < M)
    (hsupport : 4 * M < (b : ℝ)) (hsize : 16 * (k : ℝ) * M ≤ b)
    (hcut : 101 * k / 100 ≤ b) :
    ∃ s : Finset ι, s ⊆ finiteVectorSupport v ∧ s.card = b ∧
      ∀ z : ZMod p, modularMass (fun _ : ↥s → Bool => (1 / 2 : ℝ) ^ b)
        (fun σ => ∑ i : ↥s, (if σ i then 1 else -1) * v i.1) z ≤
        1 / (p : ℝ) + 8 * (normalizedRestrictedCount k b c + repeatedIndexRatio k b) /
          Real.sqrt M + Real.exp (-M) := by
  obtain ⟨s, hs, hsb, hsc⟩ := hmin.2
  have hsupp : (Finset.univ.filter (fun i : ↥s => v i.1 ≠ 0)) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => mem_finiteVectorSupport.mp (hs i.2)
  have hcard : Fintype.card ↥s = b := (Fintype.card_coe s).trans hsb
  refine ⟨s, hs, hsb, fun z => ?_⟩
  have h := modularMass_fair_signs_le_halasz_restricted hp (fun i : ↥s => v i.1)
    z hk hM (by simpa only [hsupp, Finset.card_univ, hcard] using hsupport)
    (by simpa only [hcard] using hsize) (by simpa only [hcard] using hcut)
  rw [hcard] at h
  change _ ≤ 1 / (p : ℝ) + 8 * ((restrictedCountOn v k s : ℝ) +
    (b.choose (101 * k / 100) : ℝ) * (2 * ((101 * k / 100 : ℕ) : ℝ)) ^ (2 * k)) /
      ((2 * (b : ℝ)) ^ (2 * k) * Real.sqrt M) + Real.exp (-M) at h
  rw [hsc] at h
  convert h using 1
  unfold normalizedRestrictedCount repeatedIndexRatio
  ring

end Bernoulli
