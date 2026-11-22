module

public import Bernoulli.RankDenseRows
public import Bernoulli.RankRelationLevels
public import Bernoulli.RankSparse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Relation levels and near-kernel events

The signs in the rectangular block outside the minimizing set control the
probability that a vector is annihilated by all but a given number of rows.
-/

open scoped BigOperators
namespace Bernoulli

/-- If the fair signed sum on a fixed coordinate set has every atom at
most q, a vector can have at most r nonzero image coordinates with the
stated probability. -/
public theorem probability_mulVec_support_le_of_subset_atom {n p : ℕ} [Fact p.Prime]
    (lam : ZMod p) (v : Fin n → ZMod p) (r : ℕ) (S : Finset (Fin n))
    {q : ℝ} (hq : 0 ≤ q)
    (hatom : ∀ u : ZMod p, modularMass (fun _ : S → Bool => (1 / 2 : ℝ) ^ S.card)
      (fun b => ∑ j : S, (if b j then 1 else -1) * v j.1) u ≤ q) :
    probability (fun a : Sample n =>
      (finiteVectorSupport ((shiftedSignMatrix a lam).mulVec v)).card ≤ r) ≤
        (2 : ℝ) ^ n * q ^ (n - r - S.card) := by
  classical
  let m := n - r - S.card
  let U := (Finset.univ : Finset (Fin n)).powersetCard m
  let P (R : Finset (Fin n)) (a : Sample n) :=
    Disjoint R S ∧ ∀ i ∈ R, ((shiftedSignMatrix a lam).mulVec v) i = 0
  have hcovered (a : Sample n)
      (ha : (finiteVectorSupport ((shiftedSignMatrix a lam).mulVec v)).card ≤ r) :
      ∃ R ∈ U, P R a := by
    let W := finiteVectorSupport ((shiftedSignMatrix a lam).mulVec v)
    have hW : (W ∪ S).card ≤ r + S.card := (Finset.card_union_le _ _).trans (by
      exact Nat.add_le_add_right ha _)
    have hm : m ≤ ((W ∪ S)ᶜ : Finset (Fin n)).card := by
      rw [Finset.card_compl, Fintype.card_fin]
      dsimp only [m]
      omega
    obtain ⟨R, hR, hmR⟩ := Finset.exists_subset_card_eq hm
    refine ⟨R, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hmR⟩, ?_, ?_⟩
    · refine Finset.disjoint_left.mpr fun i hi hS => ?_
      exact (Finset.mem_compl.mp (hR hi)) (Finset.mem_union_right _ hS)
    · intro i hi
      by_contra hz
      exact (Finset.mem_compl.mp (hR hi))
        (Finset.mem_union_left _ (mem_finiteVectorSupport.mpr hz))
  have hstep (R : Finset (Fin n)) (hR : R ∈ U) : probability (P R) ≤ q ^ m := by
    by_cases h : Disjoint R S
    · simpa only [P, h, true_and, (Finset.mem_powersetCard.mp hR).2] using
        probability_shiftedMulVec_zero_rows_le_of_atom lam v h q hatom
    · simp [P, h, probability, hq, pow_nonneg]
  have hU : (U.card : ℝ) ≤ (2 : ℝ) ^ n := by
    have h := Finset.card_le_card
      (show U ⊆ (Finset.univ : Finset (Fin n)).powerset from
        fun R _ => Finset.mem_powerset.mpr (Finset.subset_univ R))
    simpa only [Finset.card_powerset, Finset.card_univ, Fintype.card_fin, Nat.cast_pow,
      Nat.cast_ofNat] using (Nat.cast_le.mpr h : (U.card : ℝ) ≤ _)
  calc
    _ ≤ probability (fun a => ∃ R ∈ U, P R a) := probability_mono hcovered
    _ ≤ ∑ R ∈ U, probability (P R) := probability_finset_exists_le U P
    _ ≤ ∑ _R ∈ U, q ^ m := Finset.sum_le_sum hstep
    _ = (U.card : ℝ) * q ^ m := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hU (pow_nonneg hq _)

/-- The probability of a near-kernel vector from one integer relation level
is bounded by the level's vector count times the row constraint bound. -/
public theorem probability_nearKernel_minimumRestrictedCount_le {n p : ℕ} [Fact p.Prime]
    (hp : 2 < p) (lam : ZMod p) {k b d c r : ℕ}
    (hk : 0 < k) (hb : 0 < b) (hbd : b ≤ d) (hc : 0 < c) {M : ℝ} (hM : 0 < M)
    (hsupport : 4 * M < (b : ℝ)) (hsize : 16 * (k : ℝ) * M ≤ b)
    (hcut : 101 * k / 100 ≤ b) (q : ℝ) (hq : 0 ≤ q)
    (hq' : 1 / (p : ℝ) +
       8 * (normalizedRestrictedCount k b c + repeatedIndexRatio k b) / Real.sqrt M +
       Real.exp (-M) ≤ q) :
    probability (fun a : Sample n =>
      ∃ v ∈ vectorsOfMinimumRestrictedCount k b d c,
        (finiteVectorSupport ((shiftedSignMatrix a lam).mulVec v)).card ≤ r) ≤
        ((n.choose d : ℝ) * ((p : ℝ) ^ b *
          (100 / normalizedRestrictedCount k b c) ^ (d - b))) *
        ((2 : ℝ) ^ n * q ^ (n - r - b)) := by
  classical
  let V := vectorsOfMinimumRestrictedCount (ι := Fin n) (p := p) k b d c
  let P (v : Fin n → ZMod p) (a : Sample n) :=
    (finiteVectorSupport ((shiftedSignMatrix a lam).mulVec v)).card ≤ r
  have hstep (v : Fin n → ZMod p) (hv : v ∈ V) :
      probability (P v) ≤ (2 : ℝ) ^ n * q ^ (n - r - b) := by
    have hmin := (mem_vectorsOfMinimumRestrictedCount.mp hv).2
    obtain ⟨S, _, hSb, hS⟩ :=
      exists_subset_fairSign_atom_le hp hmin hk hM hsupport hsize hcut
    have hA (u : ZMod p) : modularMass (fun _ : S → Bool => (1 / 2 : ℝ) ^ S.card)
        (fun x => ∑ j : S, (if x j then 1 else -1) * v j.1) u ≤ q := by
      rw [hSb]
      exact (hS u).trans hq'
    simpa only [hSb] using probability_mulVec_support_le_of_subset_atom lam v r S hq hA
  have hcard := card_vectorsOfMinimumRestrictedCount_le (ι := Fin n) (p := p) hk hb hbd hc
  rw [Fintype.card_fin] at hcard
  calc
    _ ≤ ∑ v ∈ V, probability (P v) := probability_finset_exists_le V P
    _ ≤ ∑ _v ∈ V, (2 : ℝ) ^ n * q ^ (n - r - b) := Finset.sum_le_sum hstep
    _ = (V.card : ℝ) * ((2 : ℝ) ^ n * q ^ (n - r - b)) := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

end Bernoulli
