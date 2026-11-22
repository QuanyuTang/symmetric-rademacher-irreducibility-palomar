module

public import Bernoulli.Ensemble
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring

/-! The upper-triangular coordinates of a principal block and its new column are disjoint. -/

namespace Bernoulli

private def oldPosition {n : ℕ} (ij : UpperIndex n) : UpperIndex (n + 1) :=
  ⟨(ij.1.1.castSucc, ij.1.2.castSucc), Fin.castSucc_le_castSucc_iff.mpr ij.2⟩

private def newPosition {n : ℕ} (i : Fin (n + 1)) : UpperIndex (n + 1) :=
  ⟨(i, Fin.last n), Fin.le_last i⟩

/-- Restricting to the original block and to the new column partitions all sampled positions. -/
public noncomputable def upperIndexSuccEquiv (n : ℕ) :
    (UpperIndex n ⊕ Fin (n + 1)) ≃ UpperIndex (n + 1) := by
  refine Equiv.ofBijective (Sum.elim oldPosition newPosition) ⟨?_, ?_⟩
  · intro a b hab
    cases a with
    | inl a =>
      cases b with
      | inl b =>
        apply congrArg Sum.inl
        apply Subtype.ext
        exact Prod.ext (Fin.castSucc_injective _ (congrArg (fun x => x.1.1) hab))
          (Fin.castSucc_injective _ (congrArg (fun x => x.1.2) hab))
      | inr b =>
        exact (Fin.castSucc_ne_last a.1.2 (congrArg (fun x => x.1.2) hab)).elim
    | inr a =>
      cases b with
      | inl b =>
        exact (Fin.castSucc_ne_last b.1.2 (congrArg (fun x => x.1.2) hab.symm)).elim
      | inr b =>
        exact congrArg Sum.inr (congrArg (fun x => x.1.1) hab)
  · rintro ⟨⟨i, j⟩, hij⟩
    rcases Fin.eq_castSucc_or_eq_last j with ⟨j', rfl⟩ | rfl
    · have hi : i ≠ Fin.last n := fun h =>
        (not_le_of_gt j'.castSucc_lt_last) (h ▸ hij)
      obtain ⟨i', rfl⟩ := Fin.eq_castSucc_of_ne_last hi
      exact ⟨Sum.inl ⟨(i', j'), Fin.castSucc_le_castSucc_iff.mp hij⟩, rfl⟩
    · exact ⟨Sum.inr i, rfl⟩

/-- Uniformly sampling the larger block is equivalent to independently sampling the old
block and all `n + 1` signs of the new column. -/
public noncomputable def sampleSuccEquiv (n : ℕ) : Sample (n + 1) ≃ Sample n × (Fin (n + 1) → Bool) :=
  (Equiv.arrowCongr (upperIndexSuccEquiv n).symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (UpperIndex n) (Fin (n + 1)) Bool)

/-- The first factor of the exposure restricts the assignment to old positions. -/
public theorem sampleSuccEquiv_fst_apply {n : ℕ} (a : Sample (n + 1)) (ij : UpperIndex n) :
    (sampleSuccEquiv n a).1 ij =
      a ⟨(ij.1.1.castSucc, ij.1.2.castSucc), Fin.castSucc_le_castSucc_iff.mpr ij.2⟩ := by
  simp only [sampleSuccEquiv, Equiv.trans_apply, Equiv.sumArrowEquivProdArrow_apply_fst,
    Equiv.arrowCongr_apply, Equiv.symm_symm, Equiv.refl_apply, Function.comp_apply]
  rfl

/-- Restricting the larger sample to old positions recovers the principal matrix. -/
public theorem matrix_sampleSuccEquiv_fst {n : ℕ} (a : Sample (n + 1)) (i j : Fin n) :
    matrix ((sampleSuccEquiv n a).1) i j = matrix a i.castSucc j.castSucc := by
  rcases le_total i j with hij | hji
  · have h := Fin.castSucc_le_castSucc_iff.mpr hij
    simp only [matrix, min_eq_left hij, max_eq_right hij, min_eq_left h, max_eq_right h]
    rfl
  · have h := Fin.castSucc_le_castSucc_iff.mpr hji
    simp only [matrix, min_eq_right hji, max_eq_left hji, min_eq_right h, max_eq_left h]
    rfl

/-- The second factor of the larger sample gives the sign of each new entry. -/
public theorem matrix_sampleSuccEquiv_snd {n : ℕ} (a : Sample (n + 1)) (i : Fin (n + 1)) :
    matrix a i (Fin.last n) = if (sampleSuccEquiv n a).2 i then 1 else -1 := by
  simp only [matrix, min_eq_left (Fin.le_last i), max_eq_right (Fin.le_last i)]
  rfl

public theorem card_upperIndex_succ (n : ℕ) :
    Fintype.card (UpperIndex (n + 1)) = Fintype.card (UpperIndex n) + (n + 1) := by
  rw [← Fintype.card_congr (upperIndexSuccEquiv n), Fintype.card_sum, Fintype.card_fin]

public theorem twice_card_upperIndex (n : ℕ) : 2 * Fintype.card (UpperIndex n) = n * (n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [card_upperIndex_succ, Nat.mul_add, ih]
    ring

public theorem card_Sample (n : ℕ) : Fintype.card (Sample n) = 2 ^ (n * (n + 1) / 2) := by
  have h := twice_card_upperIndex n
  have hcard : Fintype.card (UpperIndex n) = n * (n + 1) / 2 := by omega
  rw [Fintype.card_fun, Fintype.card_bool, hcard]

end Bernoulli
