module

public import Bernoulli.BlockExposure
public import Bernoulli.RankVectorSupport
public import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic

/-!
# Independent constraints on rows outside the support

For a prescribed support, the rectangular set of edges linking it to any
disjoint row set is independent. A nonzero coefficient leaves at most one
possible sign for its edge in each constrained row.
-/

namespace Bernoulli

/-- A shifted matrix from the symmetric Bernoulli ensemble over the prime field. -/
@[expose] public def shiftedSignMatrix {n p : ℕ} (a : Sample n) (lam : ZMod p) :
    Matrix (Fin n) (Fin n) (ZMod p) :=
  (matrix a).map (Int.castRingHom (ZMod p)) - Matrix.diagonal (fun _ => lam)

/-- The probability of a predicate in the sample space is its normalized count. -/
public theorem probability_eq_card {n : ℕ} (P : Sample n → Prop) [instP : DecidablePred P] :
    probability P =
      (Fintype.card {a : Sample n // P a} : ℝ) / Fintype.card (Sample n) := by
  classical
  simp only [probability, expectation, Fintype.card_subtype]
  congr 1
  trans ∑ a, @ite ℝ (P a) (instP a) 1 0
  · refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : P a <;> simp [h]
  · have h := (Finset.sum_filter (s := Finset.univ) P (fun _ => (1 : ℝ))).symm
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using h

private theorem card_sign_sum_eq_zero_le {ι : Type*} [Fintype ι]
    {p : ℕ} [Fact p.Prime] (hp : 2 < p) (v : ι → ZMod p) (j : ι) (hv : v j ≠ 0) :
    Nat.card {b : ι → Bool // ∑ i, (if b i then 1 else -1) * v i = 0} ≤
      2 ^ (Fintype.card ι - 1) := by
  classical
  let _ : Fact (2 < p) := ⟨hp⟩
  let term (b : ι → Bool) (i : ι) : ZMod p := (if b i then 1 else -1) * v i
  let f (b : {b : ι → Bool // ∑ i, term b i = 0}) : {i : ι // i ≠ j} → Bool :=
    fun i => b.1 i.1
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    have heq (i : ι) (hi : i ≠ j) : a.1 i = b.1 i := congrFun hab ⟨i, hi⟩
    have hsum : ∑ i ∈ Finset.univ.erase j, term a.1 i =
        ∑ i ∈ Finset.univ.erase j, term b.1 i := by
      refine Finset.sum_congr rfl fun i hi => ?_
      simp only [term, heq i (Finset.mem_erase.mp hi).1]
    have ha := a.2
    have hb := b.2
    rw [← Finset.sum_erase_add _ (term a.1) (Finset.mem_univ j), hsum] at ha
    rw [← Finset.sum_erase_add _ (term b.1) (Finset.mem_univ j)] at hb
    have ht := add_left_cancel (ha.trans hb.symm)
    have hj : (if a.1 j then (1 : ZMod p) else -1) =
        (if b.1 j then (1 : ZMod p) else -1) := mul_right_cancel₀ hv ht
    have hsign : Function.Injective (fun z : Bool => if z then (1 : ZMod p) else -1) := by
      intro x y hxy
      cases x <;> cases y <;> simp_all [ZMod.neg_one_ne_one, Ne.symm ZMod.neg_one_ne_one]
    funext i
    by_cases hi : i = j
    · subst i
      exact hsign hj
    · exact heq i hi
  have hC : Fintype.card {i : ι // i ≠ j} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl (fun i => i = j), Fintype.card_subtype_eq]
  simpa only [term, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_bool, hC] using
    (Nat.card_le_card_of_injective f hinj)

/-- Outside the support of a nonzero vector, different prescribed zero rows
constrain independent sets of signs. -/
public theorem probability_shiftedMulVec_zero_rows_le {n p : ℕ} [Fact p.Prime] (hp : 2 < p)
    (lam : ZMod p) {v : Fin n → ZMod p} (hv : v ≠ 0)
    {R : Finset (Fin n)} (hR : Disjoint R (finiteVectorSupport v)) :
    probability (fun a : Sample n => ∀ i ∈ R, ((shiftedSignMatrix a lam).mulVec v) i = 0) ≤
      (1 / 2 : ℝ) ^ R.card := by
  classical
  let S := finiteVectorSupport v
  have hS : S.Nonempty := by
    by_contra he
    apply hv
    funext i
    exact not_ne_iff.mp (fun hi => he ⟨i, mem_finiteVectorSupport.mpr hi⟩)
  obtain ⟨j, hj⟩ := hS
  let j₀ : S := ⟨j, hj⟩
  let e := sampleExposureEquiv (disjointEdgeEmbedding hR)
  let β := ((Set.range (disjointEdgeEmbedding hR))ᶜ : Set (UpperIndex n)) → Bool
  let P (b : S → Bool) := (∑ j : S, (if b j then 1 else -1) * v j.1) = 0
  have hout (a : Sample n) (i : R) :
      ((shiftedSignMatrix a lam).mulVec v) i.1 =
        ∑ j : S, (if (e a).1 i j then 1 else -1) * v j.1 := by
    have hiz : v i.1 = 0 :=
      not_ne_iff.mp (fun hi => Finset.disjoint_left.mp hR i.2 (mem_finiteVectorSupport.mpr hi))
    simp only [shiftedSignMatrix, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal,
      hiz, mul_zero, sub_zero]
    change (∑ j, (matrix a i.1 j : ZMod p) * v j) = _
    calc
      _ = ∑ j ∈ S, (matrix a i.1 j : ZMod p) * v j := by
        symm
        refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
        simp [not_ne_iff.mp (fun h => hj (mem_finiteVectorSupport.mpr h))]
      _ = ∑ j : S, (matrix a i.1 j.1 : ZMod p) * v j.1 := by
        rw [← Finset.sum_attach]
        rfl
      _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [matrix_apply_of_disjoint_exposure hR a i j]
        change (↑(if (e a).1 i j then (1 : ℤ) else -1) : ZMod p) * v j.1 = _
        split <;> simp
  let good₁ := {a : Sample n // ∀ i ∈ R, ((shiftedSignMatrix a lam).mulVec v) i = 0}
  let good₂ := {g : R → S → Bool // ∀ i, P (g i)}
  let es : good₁ ≃ good₂ × β :=
    (e.subtypeEquiv (p := fun a : Sample n => ∀ i ∈ R,
        ((shiftedSignMatrix a lam).mulVec v) i = 0)
      (q := fun z : (R → S → Bool) × β => ∀ i, P (z.1 i))
      (fun a => ⟨fun ha i => (hout a i).symm.trans (ha i.1 i.2),
        fun ha i hi => (hout a ⟨i, hi⟩).trans (ha ⟨i, hi⟩)⟩)).trans
      { toFun := fun z => (⟨z.1.1, z.2⟩, z.1.2)
        invFun := fun z => ⟨(z.1.1, z.2), z.1.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hβ : (0 : ℝ) < Fintype.card β := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨fun _ => false⟩)
  have hprob :
      probability (fun a : Sample n => ∀ i ∈ R, ((shiftedSignMatrix a lam).mulVec v) i = 0) =
        (Fintype.card good₂ : ℝ) / Fintype.card (R → S → Bool) := by
    rw [probability_eq_card, Fintype.card_congr es, Fintype.card_congr e,
      Fintype.card_prod, Fintype.card_prod, Nat.cast_mul, Nat.cast_mul, mul_div_mul_right _ _ hβ.ne']
  have hrow : (Fintype.card {x : S → Bool // P x} : ℝ) / Fintype.card (S → Bool) ≤ 1 / 2 := by
    have hj' : v j₀.1 ≠ 0 := mem_finiteVectorSupport.mp hj
    have hc := card_sign_sum_eq_zero_le hp (fun i : S => v i.1) j₀ hj'
    rw [Nat.card_eq_fintype_card] at hc
    change Fintype.card {x : S → Bool // P x} ≤ _ at hc
    have hd : Fintype.card S - 1 + 1 = Fintype.card S := by
      apply Nat.sub_add_cancel
      exact Fintype.card_pos_iff.mpr ⟨j₀⟩
    rw [Fintype.card_fun, Fintype.card_bool]
    push_cast
    calc
      _ ≤ ((2 : ℝ) ^ (Fintype.card S - 1)) / ((2 : ℝ) ^ Fintype.card S) := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (by positivity)
      _ = _ := by
        have hpow := congrArg (fun k : ℕ => (2 : ℝ) ^ k) hd
        simp only [pow_succ] at hpow
        rw [← hpow, div_mul_eq_div_div, div_self (by positivity)]
  rw [hprob]
  change (Fintype.card {g : R → S → Bool // ∀ i, P (g i)} : ℝ) / Fintype.card (R → S → Bool) ≤ _
  have hprob_product : (Fintype.card {g : R → S → Bool // ∀ i, P (g i)} : ℝ) /
      Fintype.card (R → S → Bool) =
        ∏ _i : R, (Fintype.card {x : S → Bool // P x} : ℝ) / Fintype.card (S → Bool) := by
    simpa only [← Nat.card_eq_fintype_card] using
      card_pi_predicates_div_card (fun (_ : R) => P)
  rw [hprob_product]
  calc
    _ ≤ ∏ _i : R, (1 / 2 : ℝ) :=
      Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun _ _ => hrow)
    _ = _ := by simp

end Bernoulli
