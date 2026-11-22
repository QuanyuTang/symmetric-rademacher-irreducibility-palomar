module

public import Bernoulli.RankFourierEvents
public import Bernoulli.RankRelationExclusion
import Mathlib.Tactic

/-!
# The probability of a block failing the Fourier condition

An offending near-kernel vector is either sparse, lies in a high integer
relation level, or has a low-atom subset and a large Fourier product.
-/

open scoped BigOperators
namespace Bernoulli

private theorem probability_or_le {n : ℕ} (P Q : Sample n → Prop) :
    probability (fun ω => P ω ∨ Q ω) ≤ probability P + probability Q := by
  classical
  unfold probability
  calc
    _ ≤ expectation (fun ω => (if P ω then 1 else 0) + (if Q ω then 1 else 0)) := by
      apply expectation_mono
      intro ω
      by_cases hP : P ω <;> by_cases hQ : Q ω <;> simp [hP, hQ]
    _ = _ := by
      unfold expectation
      rw [Finset.sum_add_distrib, add_div]

/-- Union bound for the three kinds of near-kernel vectors that can cause
the Fourier condition to fail. The statement leaves the scale choices explicit. -/
public theorem probability_not_rankFourierHealthy_le {n p : ℕ} [Fact p.Prime]
    (hn : 0 < n) (hp : 2 < p) (lam : ZMod p) (r b d₀ k K m : ℕ)
    (hk : 0 < k) (hb : 0 < b) (hb₀ : b ≤ d₀ + 1) (hbr : b + r ≤ n)
    {M a β : ℝ} (hM : 1 ≤ M) (hsupport : 4 * M < (b : ℝ))
    (hsize : 16 * (k : ℝ) * M ≤ b) (hcut : 101 * k / 100 ≤ b)
    (hrep : repeatedIndexRatio k b ≤ 1 / (p : ℝ)) (htail : Real.exp (-M) ≤ 1 / (p : ℝ))
    (hpK : 2 * K < p) (ha : 0 < a) (hβ₀ : 0 ≤ β) (hβ₁ : β ≤ 1)
    (hscale : 1 ≤ ((K : ℝ) + 1) * β ^ 2) :
    probability (fun ω : Sample n => ¬ rankFourierHealthy (shiftedSignMatrix ω lam) r m a) ≤
      ((((d₀ : ℝ) + 1) * ((n : ℝ) * p) ^ d₀) *
        (((r : ℝ) + 1) * (n : ℝ) ^ r * (1 / 2 : ℝ) ^ (n - d₀ - r))) +
      (((n + 1 : ℕ) : ℝ) * (((2 * b) ^ (2 * k) + 1 : ℕ) : ℝ) *
        (((7200 : ℝ) ^ n * (p : ℝ) ^ (b + r)) / (Real.sqrt M) ^ (n - r - b))) +
      ((((2 : ℝ) ^ n * (p : ℝ)) * ((p : ℝ) ^ n * β ^ m / a ^ (2 * K))) *
        ((2 : ℝ) ^ n * (18 / (p : ℝ)) ^ (n - r - b))) := by
  classical
  let dMax := (2 * b) ^ (2 * k)
  let D := (Finset.range (n + 1)).filter fun d => b ≤ d
  let C := (Finset.range (dMax + 1)).filter fun c =>
    Real.sqrt M / (p : ℝ) ≤ normalizedRestrictedCount k b c
  let P (ω : Sample n) := ∃ v : Fin n → ZMod p, v ≠ 0 ∧ (finiteVectorSupport v).card ≤ d₀ ∧
    (finiteVectorSupport ((shiftedSignMatrix ω lam).mulVec v)).card ≤ r
  let L (d : ℕ) (c : ℕ) (ω : Sample n) := ∃ v ∈ vectorsOfMinimumRestrictedCount k b d c,
    (finiteVectorSupport ((shiftedSignMatrix ω lam).mulVec v)).card ≤ r
  let Q (ω : Sample n) := ∃ dc ∈ D ×ˢ C, L dc.1 dc.2 ω
  let R (ω : Sample n) := ∃ v : Fin n → ZMod p, HasSmallAtomSubset v b (18 / (p : ℝ)) ∧
    HasLargeFourierProduct v m a ∧
    (finiteVectorSupport ((shiftedSignMatrix ω lam).mulVec v)).card ≤ r
  have hcover (ω : Sample n) (hbad : ¬ rankFourierHealthy (shiftedSignMatrix ω lam) r m a) :
      (P ω ∨ Q ω) ∨ R ω := by
    unfold rankFourierHealthy at hbad
    push Not at hbad
    obtain ⟨v, hv, hAv, S, hS, ξ, hξ, hprod⟩ := hbad
    let d := (finiteVectorSupport v).card
    have hdn : d ≤ n := by simpa [d] using Finset.card_le_univ (finiteVectorSupport v)
    by_cases hd₀ : d ≤ d₀
    · exact Or.inl (Or.inl ⟨v, hv, hd₀, hAv⟩)
    have hbd : b ≤ d := by omega
    obtain ⟨c, hc, hmin⟩ := exists_minimumRestrictedCount v k b hbd
    by_cases hhigh : Real.sqrt M / (p : ℝ) ≤ normalizedRestrictedCount k b c
    · have hD : d ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hbd⟩
      have hC : c ∈ C :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hc), hhigh⟩
      have hV : v ∈ vectorsOfMinimumRestrictedCount k b d c :=
        mem_vectorsOfMinimumRestrictedCount.mpr ⟨rfl, hmin⟩
      exact Or.inl (Or.inr ⟨(d, c), Finset.mem_product.mpr ⟨hD, hC⟩, v, hV, hAv⟩)
    · have hsmall := exists_subset_fairSign_atom_le_of_low_relationLevel hp hmin hk hM
        hsupport hsize hcut hrep htail (le_of_not_ge hhigh)
      exact Or.inr ⟨v, hsmall, ⟨S, hS, ξ, hξ, hprod.le⟩, hAv⟩
  let B := ((7200 : ℝ) ^ n * (p : ℝ) ^ (b + r)) / (Real.sqrt M) ^ (n - r - b)
  have hQstep (dc : ℕ × ℕ) (hdc : dc ∈ D ×ˢ C) : probability (L dc.1 dc.2) ≤ B := by
    obtain ⟨hd, hc⟩ := Finset.mem_product.mp hdc
    obtain ⟨hd, hbd⟩ := Finset.mem_filter.mp hd
    obtain ⟨hc, hhigh⟩ := Finset.mem_filter.mp hc
    have hd' := Finset.mem_range.mp hd
    have hc' : dc.2 < dMax + 1 := Finset.mem_range.mp hc
    exact probability_high_relationLevel_nearKernel_le hp lam hk hb hbd (by omega) hbr
      (Nat.lt_succ_iff.mp hc') hM hsupport hsize hcut hrep htail hhigh
  have hlevels : (((D ×ˢ C).card : ℕ) : ℝ) ≤ (n + 1 : ℕ) * ((dMax + 1 : ℕ) : ℝ) := by
    rw [Finset.card_product, Nat.cast_mul]
    have hD : D.card ≤ n + 1 := (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
    have hC : C.card ≤ dMax + 1 := (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
    exact mul_le_mul
      (by exact_mod_cast hD) (by exact_mod_cast hC)
      (by positivity) (by positivity)
  have hQ : probability Q ≤ ((n + 1 : ℕ) : ℝ) * ((dMax + 1 : ℕ) : ℝ) * B := by
    calc
      _ ≤ ∑ dc ∈ D ×ˢ C, probability (L dc.1 dc.2) :=
        probability_finset_exists_le (D ×ˢ C) (fun dc => L dc.1 dc.2)
      _ ≤ ∑ _dc ∈ D ×ˢ C, B := Finset.sum_le_sum hQstep
      _ = ((D ×ˢ C).card : ℝ) * B := by simp [nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hlevels (by positivity)
  have hP := probability_exists_sparse_mulVec_le (n := n) hn hp lam d₀ r
  have hR := probability_nearKernel_largeFourierProduct_le (n := n) lam r b K m hpK ha hβ₀ hβ₁
    hscale (show 0 ≤ 18 / (p : ℝ) by positivity)
  calc
    _ ≤ probability (fun ω => (P ω ∨ Q ω) ∨ R ω) := probability_mono hcover
    _ ≤ (probability P + probability Q) + probability R :=
      (probability_or_le (fun ω => P ω ∨ Q ω) R).trans
        (add_le_add (probability_or_le P Q) le_rfl)
    _ ≤ _ := add_le_add (add_le_add hP hQ) hR

end Bernoulli
