module

public import Bernoulli.PrincipalBlocks
public import Bernoulli.RankSparseRows
public import Bernoulli.RankTransitionReindex
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

/-!
# Exposing one row and column of a shifted symmetric sign matrix
-/

open scoped BigOperators
open Matrix
namespace Bernoulli

/-- The nullity of the shifted sign matrix over the prime field. -/
@[expose] public noncomputable def shiftedSignCorank {n p : ℕ} [Fact p.Prime]
    (a : Sample n) (lam : ZMod p) : ℕ :=
  Module.finrank (ZMod p) (LinearMap.ker (shiftedSignMatrix a lam).mulVecLin)

public theorem shiftedSignMatrix_isSymm {n p : ℕ} (a : Sample n) (lam : ZMod p) :
    (shiftedSignMatrix a lam).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  by_cases h : i = j
  · subst j
    rfl
  · simp only [shiftedSignMatrix, Matrix.sub_apply, Matrix.map_apply, Matrix.diagonal_apply,
      matrix_symmetric a j i, ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- The initial principal block of the shifted matrix depends only on the
first factor of the exposure of its last column. -/
public theorem shiftedSignMatrix_principal_submatrix {n p : ℕ}
    (a : Sample (n + 1)) (lam : ZMod p) :
    (shiftedSignMatrix a lam).submatrix Fin.castSucc Fin.castSucc =
      shiftedSignMatrix (sampleSuccEquiv n a).1 lam := by
  ext i j
  simp [shiftedSignMatrix, Matrix.diagonal_apply, matrix_sampleSuccEquiv_fst]

/-- The next corank can increase by at most one for every sample. -/
public theorem shiftedSignCorank_succ_le {n p : ℕ} [Fact p.Prime]
    (a : Sample (n + 1)) (lam : ZMod p) :
    shiftedSignCorank a lam ≤ shiftedSignCorank (sampleSuccEquiv n a).1 lam + 1 := by
  unfold shiftedSignCorank
  rw [← shiftedSignMatrix_principal_submatrix a lam]
  exact matrix_corank_succ_le _

private def finBorderEquiv (n : ℕ) : Fin n ⊕ Unit ≃ Fin (n + 1) :=
  (Equiv.sumCongr (Equiv.refl (Fin n)) (Equiv.ofUnique Unit (Fin 1))).trans finSumFinEquiv

@[simp] private theorem finBorderEquiv_inl (n : ℕ) (i : Fin n) :
    finBorderEquiv n (Sum.inl i) = i.castSucc := rfl

@[simp] private theorem finBorderEquiv_inr (n : ℕ) (i : Unit) :
    finBorderEquiv n (Sum.inr i) = Fin.last n := rfl

private theorem shiftedSignMatrix_symmetricBorder {n p : ℕ} (a : Sample (n + 1))
    (lam : ZMod p) :
    (shiftedSignMatrix a lam).submatrix (finBorderEquiv n) (finBorderEquiv n) =
      symmetricBorder (shiftedSignMatrix (sampleSuccEquiv n a).1 lam)
        (fun i => fairSign ((sampleSuccEquiv n a).2 i.castSucc))
        (fairSign ((sampleSuccEquiv n a).2 (Fin.last n)) - lam) := by
  ext i j
  rcases i with i | ⟨⟩ <;> rcases j with j | ⟨⟩
  · simpa [symmetricBorder] using congrFun (congrFun (shiftedSignMatrix_principal_submatrix a lam) i) j
  · cases h : (sampleSuccEquiv n a).2 i.castSucc <;>
      simp [symmetricBorder, shiftedSignMatrix, matrix_sampleSuccEquiv_snd,
        Fin.castSucc_ne_last, fairSign, h]
  · cases h : (sampleSuccEquiv n a).2 j.castSucc <;>
      simp [symmetricBorder, shiftedSignMatrix, matrix_symmetric a (Fin.last n) j.castSucc,
        matrix_sampleSuccEquiv_snd, Ne.symm (Fin.castSucc_ne_last j), fairSign, h]
  · simp [symmetricBorder, shiftedSignMatrix, matrix_sampleSuccEquiv_snd, fairSign, apply_ite]

private def borderColumnEquiv (n : ℕ) :
    (Fin (n + 1) → Bool) ≃ (Fin n → Bool) × (Unit → Bool) :=
  (Equiv.arrowCongr (finBorderEquiv n).symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin n) Unit Bool)

@[simp] private theorem borderColumnEquiv_symm_apply_castSucc {n : ℕ}
    (σ : Fin n → Bool) (δ : Unit → Bool) (i : Fin n) :
    (borderColumnEquiv n).symm (σ, δ) i.castSucc = σ i := by
  have h : (borderColumnEquiv n).symm (σ, δ) (finBorderEquiv n (Sum.inl i)) = σ i := by
    change Sum.elim σ δ ((finBorderEquiv n).symm (finBorderEquiv n (Sum.inl i))) = σ i
    rw [Equiv.symm_apply_apply]
    rfl
  simpa only [finBorderEquiv_inl] using h

@[simp] private theorem borderColumnEquiv_symm_apply_last {n : ℕ}
    (σ : Fin n → Bool) (δ : Unit → Bool) :
    (borderColumnEquiv n).symm (σ, δ) (Fin.last n) = δ () := by
  have h : (borderColumnEquiv n).symm (σ, δ) (finBorderEquiv n (Sum.inr ())) = δ () := by
    change Sum.elim σ δ ((finBorderEquiv n).symm (finBorderEquiv n (Sum.inr ()))) = δ ()
    rw [Equiv.symm_apply_apply]
    rfl
  simpa only [finBorderEquiv_inr] using h

/-- For a fixed healthy leading block, the probability of departing from the
default corank change is bounded over the independent new column. -/
public theorem shiftedSignCorank_exception_mass_le {n p : ℕ} [Fact p.Prime]
    (hp : 2 < p) (a : Sample n) (lam : ZMod p)
    {J I : Type*} [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I]
    (part : J ⊕ I ≃ Fin n) {r m : ℕ} (hr : Fintype.card J ≤ r) (hm : m ≤ Fintype.card I)
    {ε : ℝ} (hε : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hgood : rankFourierHealthy (shiftedSignMatrix a lam) r m ε) :
    (∑ col : Fin (n + 1) → Bool, if
      shiftedSignCorank ((sampleSuccEquiv n).symm (a, col)) lam ≠ shiftedSignCorank a lam - 1
      then fairSignWeight (Fin (n + 1)) else 0) ≤
      (p : ℝ)⁻¹ + Real.sqrt (fairSignWeight J + ε) := by
  classical
  let A := shiftedSignMatrix a lam
  let q := (p : ℝ)⁻¹ + Real.sqrt (fairSignWeight J + ε)
  let w := fairSignWeight (Fin n)
  let wδ := fairSignWeight Unit
  let term (σ : (Fin n → Bool) × (Unit → Bool)) :=
    if Module.finrank (ZMod p) (LinearMap.ker
        (symmetricBorder A (fun i => fairSign (σ.1 i)) (fairSign (σ.2 ()) - lam)).mulVecLin) ≠
      shiftedSignCorank a lam - 1 then w else 0
  have hstep (σ : (Fin n → Bool) × (Unit → Bool)) :
      shiftedSignCorank ((sampleSuccEquiv n).symm (a, (borderColumnEquiv n).symm σ)) lam =
        Module.finrank (ZMod p) (LinearMap.ker
          (symmetricBorder A (fun i => fairSign (σ.1 i)) (fairSign (σ.2 ()) - lam)).mulVecLin) := by
    rcases σ with ⟨s, δ⟩
    unfold shiftedSignCorank
    rw [← finrank_ker_mulVecLin_submatrix_equiv _ (finBorderEquiv n),
      shiftedSignMatrix_symmetricBorder, Equiv.apply_symm_apply]
    have hs : (fun i : Fin n => fairSign (p := p) ((borderColumnEquiv n).symm (s, δ) i.castSucc)) =
        (fun i => fairSign (s i)) :=
      funext fun i => congrArg fairSign (borderColumnEquiv_symm_apply_castSucc s δ i)
    have hz := congrArg (fun b => fairSign b - lam) (borderColumnEquiv_symm_apply_last s δ)
    exact congrArg (fun B : Matrix (Fin n ⊕ Unit) (Fin n ⊕ Unit) (ZMod p) =>
      Module.finrank (ZMod p) (LinearMap.ker B.mulVecLin)) (congrArg₂ (symmetricBorder A) hs hz)
  have hw : fairSignWeight (Fin (n + 1)) = w * wδ := by
    simp [w, wδ, fairSignWeight, pow_succ]
  have hconditional (δ : Unit → Bool) : (∑ σ : Fin n → Bool, term (σ, δ)) ≤ q :=
    fairSign_corank_exception_le_of_partition hp (shiftedSignMatrix_isSymm a lam)
      part hr hm hε hε₁ hgood (fairSign (δ ()) - lam)
  change _ ≤ q
  rw [← (borderColumnEquiv n).symm.sum_comp]
  calc
    _ = ∑ σ : (Fin n → Bool) × (Unit → Bool), wδ * term σ := by
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [hstep, hw]
      dsimp only [term]
      split <;> ring
    _ = ∑ δ : Unit → Bool, wδ * ∑ σ : Fin n → Bool, term (σ, δ) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ ∑ _ : Unit → Bool, wδ * q := Finset.sum_le_sum fun δ _ =>
      mul_le_mul_of_nonneg_left (hconditional δ) (fairSignWeight_nonneg Unit)
    _ = q := by rw [← Finset.sum_mul, sum_fairSignWeight, one_mul]

private theorem fairSignWeight_eq_inv_card (ι : Type*) [Fintype ι] [DecidableEq ι] :
    fairSignWeight ι = ((Fintype.card (ι → Bool) : ℕ) : ℝ)⁻¹ := by
  rw [fairSignWeight, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow, Nat.cast_ofNat,
    one_div, inv_pow]

/-- Uniform averaging over all entries of the larger matrix equals averaging
first over the independent new column and then over the leading block. -/
public theorem expectation_sampleSuccEquiv {n : ℕ} (f : Sample (n + 1) → ℝ) :
    expectation f = expectation (fun a : Sample n =>
      ∑ col : Fin (n + 1) → Bool, fairSignWeight (Fin (n + 1)) *
        f ((sampleSuccEquiv n).symm (a, col))) := by
  unfold expectation
  rw [← (sampleSuccEquiv n).symm.sum_comp, Fintype.sum_prod_type,
    Fintype.card_congr (sampleSuccEquiv n), Fintype.card_prod]
  simp_rw [← Finset.mul_sum]
  rw [fairSignWeight_eq_inv_card, Nat.cast_mul, div_eq_mul_inv, mul_inv]
  ring

/-- The probability of a new event on an old event is bounded by the
conditional probability bound on every leading block in the old event. -/
public theorem probability_and_sampleSuccEquiv_le {n : ℕ}
    (Q : Sample n → Prop) (R : Sample (n + 1) → Prop) [DecidablePred R] (q : ℝ)
    (h : ∀ a, Q a → (∑ col : Fin (n + 1) → Bool,
      if R ((sampleSuccEquiv n).symm (a, col)) then fairSignWeight (Fin (n + 1)) else 0) ≤ q) :
    probability (fun b => Q (sampleSuccEquiv n b).1 ∧ R b) ≤ q * probability Q := by
  classical
  unfold probability
  rw [expectation_sampleSuccEquiv]
  have hq : expectation (fun a : Sample n => q * (if Q a then 1 else 0)) =
      q * expectation (fun a : Sample n => if Q a then 1 else 0) := by
    simp only [expectation, ← Finset.mul_sum, mul_div_assoc]
  rw [← hq]
  apply expectation_mono
  intro a
  by_cases ha : Q a
  · simpa only [Equiv.apply_symm_apply, ha, true_and, mul_ite, mul_zero, mul_one,
      ite_eq_left ha, ite_true] using h a ha
  · simp [ha]

/-- A bound on every conditional probability also bounds the unconditional
probability of the new event. -/
public theorem probability_sampleSuccEquiv_le {n : ℕ}
    (R : Sample (n + 1) → Prop) [DecidablePred R] (q : ℝ)
    (h : ∀ a : Sample n, (∑ col : Fin (n + 1) → Bool,
      if R ((sampleSuccEquiv n).symm (a, col)) then fairSignWeight (Fin (n + 1)) else 0) ≤ q) :
    probability R ≤ q := by
  have h' := probability_and_sampleSuccEquiv_le (fun _ => True) R q (fun a _ => h a)
  have he : (fun b : Sample (n + 1) => True ∧ R b) = R := by funext b; simp
  have ht : probability (fun _ : Sample n => True) = 1 := by simp [probability]
  rwa [he, ht, mul_one] at h'

end Bernoulli
