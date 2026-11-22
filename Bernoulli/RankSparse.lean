module

public import Bernoulli.RankSparseRows
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic

/-!
# Exclusion of sparse vectors and sparse images

A sparse image specifies a set outside which all rows vanish. Outside both
this set and the input support, the signs in the row constraints are
independent. The two support counts supply the factors in the union bound.
-/

namespace Bernoulli

/-- The finite-law probability is monotone in the predicate. -/
public theorem probability_mono {n : ℕ} {P Q : Sample n → Prop} (h : ∀ a, P a → Q a) :
    probability P ≤ probability Q := by
  classical
  unfold probability
  apply expectation_mono
  intro a
  by_cases ha : P a
  · simp [ha, h a ha]
  · by_cases hq : Q a <;> simp [ha, hq]

/-- A finite union bound for the uniform law on matrix samples. -/
public theorem probability_finset_exists_le {n : ℕ} {ι : Type*} (s : Finset ι)
    (P : ι → Sample n → Prop) :
    probability (fun a => ∃ i ∈ s, P i a) ≤ ∑ i ∈ s, probability (P i) := by
  classical
  simp only [probability, expectation, ← Finset.sum_div]
  rw [Finset.sum_comm]
  apply div_le_div_of_nonneg_right _ (by positivity)
  refine Finset.sum_le_sum fun a _ => ?_
  split
  · rename_i h
    obtain ⟨i, hi, hia⟩ := h
    calc
      1 = (if P i a then (1 : ℝ) else 0) := (ite_eq_left hia).symm
      _ ≤ _ := Finset.single_le_sum (s := s)
        (f := fun j : ι => if P j a then (1 : ℝ) else 0)
        (fun j _ => by split <;> norm_num) hi
  · exact Finset.sum_nonneg fun j _ => by split <;> norm_num

private noncomputable def smallFinsets (ι : Type*) [Fintype ι] (r : ℕ) : Finset (Finset ι) := by
  classical
  exact (Finset.univ : Finset (Finset ι)).filter fun s => s.card ≤ r

@[simp] private theorem mem_smallFinsets {ι : Type*} [Fintype ι] {r : ℕ} {s : Finset ι} :
    s ∈ smallFinsets ι r ↔ s.card ≤ r := by
  classical
  simp [smallFinsets]

private theorem card_smallFinsets_le {ι : Type*} [Fintype ι] (hι : 0 < Fintype.card ι) (r : ℕ) :
    (smallFinsets ι r).card ≤ (r + 1) * Fintype.card ι ^ r := by
  classical
  let A (i : ℕ) := (Finset.univ : Finset ι).powersetCard i
  have hsub : smallFinsets ι r ⊆ (Finset.range (r + 1)).biUnion A := by
    intro s hs
    apply Finset.mem_biUnion.mpr
    refine ⟨s.card, Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_smallFinsets.mp hs)), ?_⟩
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩
  calc
    _ ≤ ((Finset.range (r + 1)).biUnion A).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range (r + 1), (A i).card := Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range (r + 1), Fintype.card ι ^ r := by
      refine Finset.sum_le_sum fun i hi => ?_
      simp only [A, Finset.card_powersetCard, Finset.card_univ]
      exact (Nat.choose_le_pow _ _).trans
        (Nat.pow_le_pow_right hι (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
    _ = _ := by simp

private noncomputable def smallVectors (ι K : Type*) [Fintype ι] [Fintype K] [Zero K]
    (d : ℕ) : Finset (ι → K) := by
  classical
  exact Finset.univ.filter fun v => (finiteVectorSupport v).card ≤ d

@[simp] private theorem mem_smallVectors {ι K : Type*} [Fintype ι] [Fintype K] [Zero K]
    {d : ℕ} {v : ι → K} : v ∈ smallVectors ι K d ↔ (finiteVectorSupport v).card ≤ d := by
  classical
  simp [smallVectors]

private theorem card_smallVectors_le {ι K : Type*} [Fintype ι] [Fintype K] [Zero K]
    (hι : 0 < Fintype.card ι) (d : ℕ) :
    (smallVectors ι K d).card ≤ (d + 1) * (Fintype.card ι * Fintype.card K) ^ d := by
  classical
  let U := smallFinsets ι d
  let T := Σ s : ↥U, ↥s.1 → K
  let f (v : ↥(smallVectors ι K d)) : T :=
    ⟨⟨finiteVectorSupport v.1, mem_smallFinsets.mpr (mem_smallVectors.mp v.2)⟩, fun i => v.1 i.1⟩
  have hf : Function.Injective f := by
    intro ⟨a, ha⟩ ⟨b, hb⟩ heq
    have hsupp : finiteVectorSupport a = finiteVectorSupport b :=
      congrArg (fun x : T => x.1.1) heq
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ finiteVectorSupport a
    · let eval (x : T) : K := if hj : i ∈ x.1.1 then x.2 ⟨i, hj⟩ else 0
      have hi' : i ∈ finiteVectorSupport b := hsupp ▸ hi
      simpa only [eval, f, dite_eq_left hi, dite_eq_left hi'] using congrArg eval heq
    · have hi' : i ∉ finiteVectorSupport b := hsupp ▸ hi
      have hza : a i = 0 := by simpa using hi
      have hzb : b i = 0 := by simpa using hi'
      exact hza.trans hzb.symm
  have hK : 0 < Fintype.card K := Fintype.card_pos_iff.mpr ⟨0⟩
  calc
    _ ≤ Fintype.card T := by
      simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf
    _ = ∑ s : ↥U, Fintype.card K ^ s.1.card := by
      simp [T, Fintype.card_sigma]
    _ ≤ ∑ _s : ↥U, Fintype.card K ^ d := by
      exact Finset.sum_le_sum fun s _ => Nat.pow_le_pow_right hK (mem_smallFinsets.mp s.2)
    _ = U.card * Fintype.card K ^ d := by simp
    _ ≤ _ := by
      rw [mul_pow, ← mul_assoc]
      exact Nat.mul_le_mul_right _ (card_smallFinsets_le hι d)

/-- For a fixed nonzero input vector, a small output support has exponentially small
probability, with a factor for the possible output support sets. -/
public theorem probability_sparse_shiftedMulVec_le {n p : ℕ} [Fact p.Prime]
    (hn : 0 < n) (hp : 2 < p) (lam : ZMod p) {v : Fin n → ZMod p} (hv : v ≠ 0)
    (r : ℕ) :
    probability (fun a : Sample n => (finiteVectorSupport ((shiftedSignMatrix a lam).mulVec v)).card ≤ r) ≤
      ((r : ℝ) + 1) * (n : ℝ) ^ r * (1 / 2 : ℝ) ^ (n - (finiteVectorSupport v).card - r) := by
  classical
  let S := finiteVectorSupport v
  let U := smallFinsets (Fin n) r
  let P (T : Finset (Fin n)) (a : Sample n) :=
    ∀ i ∈ (S ∪ T)ᶜ, ((shiftedSignMatrix a lam).mulVec v) i = 0
  let Q := (1 / 2 : ℝ) ^ (n - S.card - r)
  have hU (T : Finset (Fin n)) (hT : T ∈ U) :
      probability (P T) ≤ Q := by
    have hR : Disjoint (S ∪ T)ᶜ S := by
      rw [Finset.disjoint_left]
      intro i hi hs
      exact (Finset.mem_compl.mp hi) (Finset.mem_union_left _ hs)
    have hcard : n - S.card - r ≤ (S ∪ T)ᶜ.card := by
      have h := Finset.card_union_le S T
      have ht := mem_smallFinsets.mp hT
      rw [Finset.card_compl, Fintype.card_fin]
      omega
    exact (probability_shiftedMulVec_zero_rows_le hp lam hv hR).trans
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) hcard)
  have hcard : (U.card : ℝ) ≤ ((r : ℝ) + 1) * (n : ℝ) ^ r := by
    have h := card_smallFinsets_le (ι := Fin n) (by simpa using hn) r
    rw [Fintype.card_fin] at h
    exact_mod_cast h
  calc
    _ ≤ probability (fun a => ∃ T ∈ U, P T a) := by
      apply probability_mono
      intro a ha
      refine ⟨finiteVectorSupport ((shiftedSignMatrix a lam).mulVec v), mem_smallFinsets.mpr ha, ?_⟩
      intro i hi
      have h := Finset.mem_compl.mp hi
      exact not_ne_iff.mp (fun hne => h (Finset.mem_union_right _ (mem_finiteVectorSupport.mpr hne)))
    _ ≤ ∑ T ∈ U, probability (P T) := probability_finset_exists_le U P
    _ ≤ ∑ _T ∈ U, Q := Finset.sum_le_sum hU
    _ = (U.card : ℝ) * Q := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

/-- A bound uniform in the shift for the event that some sparse nonzero vector has
a sparse image under the shifted symmetric sign matrix. -/
public theorem probability_exists_sparse_mulVec_le {n p : ℕ} [Fact p.Prime]
    (hn : 0 < n) (hp : 2 < p) (lam : ZMod p) (d r : ℕ) :
    probability (fun a : Sample n => ∃ v : Fin n → ZMod p, v ≠ 0 ∧ (finiteVectorSupport v).card ≤ d ∧
      (finiteVectorSupport ((shiftedSignMatrix a lam).mulVec v)).card ≤ r) ≤
      (((d : ℝ) + 1) * ((n : ℝ) * p) ^ d) *
        (((r : ℝ) + 1) * (n : ℝ) ^ r * (1 / 2 : ℝ) ^ (n - d - r)) := by
  classical
  let V := (smallVectors (Fin n) (ZMod p) d).filter fun v => v ≠ 0
  let P (v : Fin n → ZMod p) (a : Sample n) :=
    (finiteVectorSupport ((shiftedSignMatrix a lam).mulVec v)).card ≤ r
  let Q := ((r : ℝ) + 1) * (n : ℝ) ^ r * (1 / 2 : ℝ) ^ (n - d - r)
  have hV (v : Fin n → ZMod p) (hv : v ∈ V) : probability (P v) ≤ Q := by
    obtain ⟨hv, hne⟩ := Finset.mem_filter.mp hv
    have hd := mem_smallVectors.mp hv
    have hpow : n - d - r ≤ n - (finiteVectorSupport v).card - r := by omega
    exact (probability_sparse_shiftedMulVec_le hn hp lam hne r).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) hpow) (by positivity))
  have hcard : (V.card : ℝ) ≤ ((d : ℝ) + 1) * ((n : ℝ) * p) ^ d := by
    have hf : V.card ≤ (smallVectors (Fin n) (ZMod p) d).card := Finset.card_filter_le _ _
    have h := hf.trans (card_smallVectors_le
      (ι := Fin n) (K := ZMod p) (by simpa using hn) d)
    rw [Fintype.card_fin, ZMod.card] at h
    exact_mod_cast h
  calc
    _ ≤ probability (fun a => ∃ v ∈ V, P v a) := by
      apply probability_mono
      rintro a ⟨v, hne, hd, hr⟩
      exact ⟨v, Finset.mem_filter.mpr ⟨mem_smallVectors.mpr hd, hne⟩, hr⟩
    _ ≤ ∑ v ∈ V, probability (P v) := probability_finset_exists_le V P
    _ ≤ ∑ _v ∈ V, Q := Finset.sum_le_sum hV
    _ = (V.card : ℝ) * Q := by simp [nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)

end Bernoulli
