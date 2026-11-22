module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Range
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Deterministic corank estimate for successive principal blocks

Adding a row and column increases corank by at most one. The default transition decreases it by
one, with zero as a lower bound. The following estimate isolates what happens when all but at most
one of the transitions are default transitions, independently of the probability of exceptions.
-/

public section

namespace Bernoulli

open Matrix

/-- Add one row and its transpose as a column, with diagonal entry `z`. -/
@[expose] def symmetricBorder {K ι : Type*} (A : Matrix ι ι K) (x : ι → K) (z : K) :
    Matrix (ι ⊕ Unit) (ι ⊕ Unit) K :=
  Matrix.fromBlocks A (Matrix.of fun i _ => x i) (Matrix.of fun _ j => x j)
    (Matrix.of fun _ _ => z)

private theorem symmetricBorder_mulVec_eq_zero_iff {K ι : Type*} [Field K] [Fintype ι]
    (A : Matrix ι ι K) (x : ι → K) (z : K) (u : ι ⊕ Unit → K) :
    symmetricBorder A x z *ᵥ u = 0 ↔
      A *ᵥ (u ∘ Sum.inl) + u (Sum.inr ()) • x = 0 ∧
        x ⬝ᵥ (u ∘ Sum.inl) + z * u (Sum.inr ()) = 0 := by
  rw [symmetricBorder, Matrix.fromBlocks_mulVec]
  constructor
  · intro h
    refine ⟨funext fun i => ?_, ?_⟩
    · simpa [Matrix.mulVec, dotProduct, mul_comm] using congrFun h (Sum.inl i)
    · simpa [Matrix.mulVec, dotProduct] using congrFun h (Sum.inr ())
  · rintro ⟨hinl, hinr⟩
    funext i
    rcases i with i | ⟨⟩
    · simpa [Matrix.mulVec, dotProduct, mul_comm] using congrFun hinl i
    · simpa [Matrix.mulVec, dotProduct] using hinr

/-- If the new column pairs nontrivially with an old kernel vector, the nullity falls by one. -/
theorem finrank_ker_symmetricBorder_add_one {K ι : Type*} [Field K] [Fintype ι]
    {A : Matrix ι ι K} (hA : A.IsSymm) {x v : ι → K} (z : K)
    (hv : A *ᵥ v = 0) (hxv : x ⬝ᵥ v ≠ 0) :
    Module.finrank K (LinearMap.ker (symmetricBorder A x z).mulVecLin) + 1 =
      Module.finrank K (LinearMap.ker A.mulVecLin) := by
  let f : LinearMap.ker A.mulVecLin →ₗ[K] K :=
    { toFun := fun u => x ⬝ᵥ (u : ι → K)
      map_add' := fun u w => by simp [dotProduct_add]
      map_smul' := fun a u => by simp [dotProduct_smul] }
  let vKer : LinearMap.ker A.mulVecLin := ⟨v, hv⟩
  have hf : Function.Surjective f := by
    intro b
    refine ⟨(b / (x ⬝ᵥ v)) • vKer, ?_⟩
    rw [map_smul]
    change b / (x ⬝ᵥ v) * (x ⬝ᵥ v) = b
    exact div_mul_cancel₀ b hxv
  have hdimension := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, Module.finrank_self] at hdimension
  let extend : LinearMap.ker f →ₗ[K] LinearMap.ker (symmetricBorder A x z).mulVecLin :=
    { toFun := fun u => ⟨Sum.elim (u.val : ι → K) 0, by
        have hu : x ⬝ᵥ (u.val : ι → K) = 0 := u.property
        have hak : A *ᵥ (u.val : ι → K) = 0 := u.val.property
        exact (symmetricBorder_mulVec_eq_zero_iff A x z _).mpr (by simp [hak, hu])⟩
      map_add' := by
        intro u w
        apply Subtype.ext
        funext i
        cases i <;> simp [Pi.add_apply]
      map_smul' := by
        intro a u
        apply Subtype.ext
        funext i
        cases i <;> simp [Pi.smul_apply] }
  have hinjective : Function.Injective extend := by
    intro u w h
    apply Subtype.ext
    apply Subtype.ext
    funext i
    exact congrArg (fun q : LinearMap.ker (symmetricBorder A x z).mulVecLin => q.val (Sum.inl i)) h
  have hsurjective : Function.Surjective extend := by
    intro u
    obtain ⟨htop, hbottom⟩ := (symmetricBorder_mulVec_eq_zero_iff A x z _).mp u.property
    have hlast : u.val (Sum.inr ()) = 0 := by
      have h := congrArg (fun w => v ⬝ᵥ w) htop
      rw [dotProduct_add, hA.dotProduct_mulVec_comm, hv, dotProduct_zero, zero_add,
        dotProduct_smul, dotProduct_zero, smul_eq_mul, dotProduct_comm v x] at h
      exact (mul_eq_zero.mp h).resolve_right hxv
    let base : LinearMap.ker A.mulVecLin := ⟨u.val ∘ Sum.inl, by simpa [hlast] using htop⟩
    have hbase : base ∈ LinearMap.ker f := by
      change x ⬝ᵥ (u.val ∘ Sum.inl) = 0
      simpa [hlast] using hbottom
    refine ⟨⟨base, hbase⟩, ?_⟩
    apply Subtype.ext
    funext i
    rcases i with i | ⟨⟩
    · rfl
    · exact hlast.symm
  have hequiv := (LinearEquiv.ofBijective extend ⟨hinjective, hsurjective⟩).finrank_eq
  omega

/-- For an invertible leading block the new block is singular precisely when its scalar Schur
complement vanishes. -/
theorem det_symmetricBorder_eq_zero_iff {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) (hA : A.det ≠ 0) (x : ι → K) (z : K) :
    (symmetricBorder A x z).det = 0 ↔ z = x ⬝ᵥ (A⁻¹ *ᵥ x) := by
  let := Matrix.invertibleOfIsUnitDet A (isUnit_iff_ne_zero.mpr hA)
  rw [symmetricBorder, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv,
    mul_eq_zero, or_iff_right hA, Matrix.det_unique, Matrix.sub_apply, sub_eq_zero,
    Matrix.mul_assoc]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- A one-row, one-column extension increases the nullity by at most one. -/
theorem matrix_corank_succ_le {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    Module.finrank K (LinearMap.ker A.mulVecLin) ≤
      Module.finrank K (LinearMap.ker (A.submatrix Fin.castSucc Fin.castSucc).mulVecLin) + 1 := by
  have hRank := A.rank_submatrix_le Fin.castSucc Fin.castSucc
  have hFull := A.mulVecLin.finrank_range_add_finrank_ker
  have hPrincipal := (A.submatrix Fin.castSucc Fin.castSucc).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin, ← Matrix.rank] at hFull hPrincipal
  omega

/-- The corank at step `m` is controlled by its initial value and the number of exceptions to the
default decrement. The statement works for any sequence with these transition bounds. -/
theorem corank_le_of_count_exceptions {corank : ℕ → ℕ} {exception : ℕ → Prop}
    [DecidablePred exception] (m : ℕ)
    (hstep : ∀ t < m, corank (t + 1) ≤ corank t + 1)
    (hdefault : ∀ t < m, ¬ exception t → corank (t + 1) = corank t - 1) :
    let count := ((Finset.range m).filter exception).card
    corank m ≤ max (corank 0 + 2 * count - m) count := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hprevious := ih (fun t ht => hstep t (by omega))
      (fun t ht => hdefault t (by omega))
    let count := ((Finset.range m).filter exception).card
    change corank m ≤ max (corank 0 + 2 * count - m) count at hprevious
    have hm : m ∉ (Finset.range m).filter exception := by simp
    by_cases hexception : exception m
    · have hcard : ((Finset.range (m + 1)).filter exception).card = count + 1 := by
        rw [Finset.range_add_one, Finset.filter_insert, ite_eq_left hexception,
          Finset.card_insert_of_notMem hm]
      dsimp only
      rw [hcard]
      have hnext := hstep m (Nat.lt_succ_self m)
      omega
    · have hcard : ((Finset.range (m + 1)).filter exception).card = count := by
        rw [Finset.range_add_one, Finset.filter_insert, ite_eq_right hexception]
      dsimp only
      rw [hcard, hdefault m (Nat.lt_succ_self m) hexception]
      omega

/-- If there is enough time for the initial corank to fall to zero and there is at most one
exception, a positive terminal corank requires an exception at the final transition. -/
theorem terminal_corank_le_indicator_of_at_most_one_exception {corank : ℕ → ℕ}
    {exception : ℕ → Prop} [DecidablePred exception] (m : ℕ)
    (hstep : ∀ t < m + 1, corank (t + 1) ≤ corank t + 1)
    (hdefault : ∀ t < m + 1, ¬ exception t → corank (t + 1) = corank t - 1)
    (hburn : corank 0 + 1 ≤ m)
    (hcount : ((Finset.range (m + 1)).filter exception).card ≤ 1) :
    corank (m + 1) ≤ if exception m then 1 else 0 := by
  have hcorank := corank_le_of_count_exceptions (m + 1) hstep hdefault
  dsimp only at hcorank
  by_cases hexception : exception m
  · rw [ite_eq_left hexception]
    omega
  · rw [ite_eq_right hexception, hdefault m (Nat.lt_succ_self m) hexception]
    have hprefixCount : ((Finset.range m).filter exception).card ≤ 1 := by
      rw [Finset.range_add_one, Finset.filter_insert, ite_eq_right hexception] at hcount
      exact hcount
    have hprefix := corank_le_of_count_exceptions m (fun t ht => hstep t (by omega))
      (fun t ht => hdefault t (by omega))
    dsimp only at hprefix
    omega

end Bernoulli
