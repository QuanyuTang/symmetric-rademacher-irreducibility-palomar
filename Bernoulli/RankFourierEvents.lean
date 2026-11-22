module

public import Bernoulli.RankBadVectors
public import Bernoulli.RankRelationEvents
public import Bernoulli.RankTransition
import Mathlib.Tactic

/-!
# Near-kernel vectors with a large Fourier coefficient

A fixed vector with one low-concentration subset is unlikely to satisfy
many row constraints. Multiplying this probability by the count of vectors
with a large Fourier coefficient controls the corresponding exception.
-/

open scoped BigOperators
namespace Bernoulli

/-- The vector has a set of the stated size whose fair signed sum has small atoms. -/
@[expose] public def HasSmallAtomSubset {n p : ℕ} (v : Fin n → ZMod p) (b : ℕ) (q : ℝ) : Prop :=
  ∃ S : Finset (Fin n), S.card = b ∧
    ∀ u : ZMod p, modularMass (fun _ : S → Bool => (1 / 2 : ℝ) ^ S.card)
      (fun g => ∑ j : S, (if g j then 1 else -1) * v j.1) u ≤ q

/-- A large absolute-cosine product on some sufficiently large coordinate set. -/
@[expose] public def HasLargeFourierProduct {n p : ℕ} (v : Fin n → ZMod p)
    (m : ℕ) (ε : ℝ) : Prop :=
  ∃ S : Finset (Fin n), m ≤ S.card ∧ ∃ a : ZMod p, a ≠ 0 ∧
    ε ≤ ∏ i ∈ S, |Real.cos (2 * Real.pi * ((v i * a).val : ℝ) / p)|

/-- Combining a rectangular-block atom estimate with the Fourier counting
bound excludes near-kernel vectors that satisfy both conditions. -/
public theorem probability_nearKernel_largeFourierProduct_le {n p : ℕ} [Fact p.Prime]
    (lam : ZMod p) (r b k m : ℕ) (hp : 2 * k < p) {a β q : ℝ} (ha : 0 < a)
    (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1) (hscale : 1 ≤ ((k : ℝ) + 1) * β ^ 2) (hq : 0 ≤ q) :
    probability (fun ω : Sample n => ∃ v : Fin n → ZMod p,
      HasSmallAtomSubset v b q ∧ HasLargeFourierProduct v m a ∧
        (finiteVectorSupport ((shiftedSignMatrix ω lam).mulVec v)).card ≤ r) ≤
      (((2 : ℝ) ^ n * (p : ℝ)) * ((p : ℝ) ^ n * β ^ m / a ^ (2 * k))) *
        ((2 : ℝ) ^ n * q ^ (n - r - b)) := by
  classical
  let V := Finset.univ.filter (fun v : Fin n → ZMod p =>
    HasSmallAtomSubset v b q ∧ HasLargeFourierProduct v m a)
  let P (v : Fin n → ZMod p) (ω : Sample n) :=
    (finiteVectorSupport ((shiftedSignMatrix ω lam).mulVec v)).card ≤ r
  have hcard := card_bad_cos_vectors_le k m hp V ha hβ₀ hβ₁ hscale
    (fun v hv => (Finset.mem_filter.mp hv).2.2)
  rw [Fintype.card_fin] at hcard
  have hstep (v : Fin n → ZMod p) (hv : v ∈ V) :
      probability (P v) ≤ (2 : ℝ) ^ n * q ^ (n - r - b) := by
    obtain ⟨S, hSb, hS⟩ := (Finset.mem_filter.mp hv).2.1
    simpa only [hSb] using probability_mulVec_support_le_of_subset_atom lam v r S hq hS
  calc
    _ ≤ probability (fun ω => ∃ v ∈ V, P v ω) :=
      probability_mono (fun ω ⟨v, hb, hm, hr⟩ =>
        ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb, hm⟩, hr⟩)
    _ ≤ ∑ v ∈ V, probability (P v) := probability_finset_exists_le V P
    _ ≤ ∑ _v ∈ V, (2 : ℝ) ^ n * q ^ (n - r - b) := Finset.sum_le_sum hstep
    _ = (V.card : ℝ) * ((2 : ℝ) ^ n * q ^ (n - r - b)) := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

end Bernoulli
