module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

import Mathlib.FieldTheory.Perfect
import Mathlib.LinearAlgebra.DFinsupp
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Zero

/-!
# Eigenvalue bounds for the algebraic reduction

The bound on the roots of the characteristic polynomial uses only the bound on
the entries. Hermitian symmetry gives reality of the roots separately. The
finite-field argument uses the dimension bound for a sum of distinct eigenspaces.
-/

public section

open scoped BigOperators DirectSum Matrix

namespace Bernoulli

/-- A root of the characteristic polynomial of a matrix with entries of norm at most
`1` has norm at most the size of the matrix. -/
theorem norm_le_card_of_isRoot_charpoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℂ) (hA : ∀ i j, ‖A i j‖ ≤ 1) {z : ℂ}
    (hz : A.charpoly.IsRoot z) : ‖z‖ ≤ Fintype.card ι := by
  classical
  have he : Module.End.HasEigenvalue A.toLin' z := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    exact hz
  obtain ⟨v, hv⟩ := he.exists_hasEigenvector
  have hv_ne : v ≠ 0 := hv.2
  have hne : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv_ne (funext h)
  obtain ⟨i, hi⟩ := hne
  obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun k => ‖v k‖)
    ⟨i, Finset.mem_univ i⟩
  have hj_pos : 0 < ‖v j‖ := (norm_pos_iff.mpr hi).trans_le (hj i (Finset.mem_univ i))
  have hrow : (∑ k, A j k * v k) = z * v j := by
    have h := congrFun hv.apply_eq_smul j
    simpa [Matrix.toLin'_apply', Matrix.mulVec, dotProduct] using h
  exact (mul_le_mul_iff_of_pos_right hj_pos).mp <| calc
    ‖z‖ * ‖v j‖ = ‖∑ k, A j k * v k‖ := by rw [hrow, norm_mul]
    _ ≤ ∑ k, ‖A j k * v k‖ := norm_sum_le _ _
    _ ≤ ∑ _ : ι, ‖v j‖ := by
      refine Finset.sum_le_sum fun k hk => ?_
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (hA j k) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hj k hk)
    _ = (Fintype.card ι : ℝ) * ‖v j‖ := by simp

/-- Every root of the characteristic polynomial of a complex Hermitian matrix is real. -/
theorem im_eq_zero_of_isRoot_charpoly {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) {z : ℂ}
    (hz : A.charpoly.IsRoot z) : z.im = 0 := by
  classical
  have hmem : z ∈ A.charpoly.roots := (Polynomial.mem_roots A.charpoly_monic.ne_zero).mpr hz
  rw [hA.roots_charpoly_eq_eigenvalues] at hmem
  obtain ⟨i, _, rfl⟩ := Multiset.mem_map.mp hmem
  exact Complex.ofReal_im (hA.eigenvalues i)

/-- The characteristic roots of a symmetric sign matrix are real and have norm
bounded by the size of the matrix. -/
theorem roots_of_symmetric_sign_matrix {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℤ} (hsym : A.IsSymm) (hA : ∀ i j, A i j = -1 ∨ A i j = 1)
    {z : ℂ} (hz : (A.charpoly.map (Int.castRingHom ℂ)).IsRoot z) :
    z.im = 0 ∧ ‖z‖ ≤ Fintype.card ι := by
  let B := A.map (Int.castRingHom ℂ)
  have hB : B.IsHermitian := by
    rw [Matrix.IsHermitian.ext_iff]
    intro i j
    simp [B, hsym.apply i j]
  have hzB : B.charpoly.IsRoot z := by
    simpa only [B, Matrix.charpoly_map] using hz
  refine ⟨im_eq_zero_of_isRoot_charpoly hB hzB, norm_le_card_of_isRoot_charpoly B ?_ hzB⟩
  intro i j
  rcases hA i j with h | h <;> simp [B, h]

/-- Over a finite field, the sum of the dimensions of the eigenspaces of a square
matrix is bounded by the dimension of its ambient column space. -/
theorem sum_finrank_eigenspaces_le_card {K ι : Type*} [Field K] [Fintype K]
    [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K) :
    (∑ z : K, Module.finrank K (Module.End.eigenspace A.toLin' z)) ≤ Fintype.card ι := by
  classical
  let f : Module.End K (ι → K) := A.toLin'
  let inclusion : (⨁ z : K, f.eigenspace z) →ₗ[K] (ι → K) :=
    DFinsupp.lsum ℕ fun z => (f.eigenspace z).subtype
  have h : Function.Injective inclusion := f.eigenspaces_iSupIndep.dfinsupp_lsum_injective
  simpa [f, Module.finrank_directSum] using LinearMap.finrank_le_finrank_of_injective h

/-- When a squarefree polynomial annihilates a matrix, its eigenspace dimension
at any scalar equals the multiplicity of that scalar in the characteristic polynomial. -/
theorem finrank_eigenspace_eq_rootMultiplicity_of_squarefree_aeval_eq_zero
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] (A : Matrix ι ι K)
    {g : Polynomial K} (hg : Squarefree g) (hA : Polynomial.aeval A g = 0) (z : K) :
    Module.finrank K (Module.End.eigenspace A.toLin' z) = A.charpoly.rootMultiplicity z := by
  have hlin : Polynomial.aeval A.toLin' g = 0 := by
    change Polynomial.aeval (Matrix.toLinAlgEquiv' A) g = 0
    rw [Polynomial.aeval_algHom_apply, hA, map_zero]
  have hs := Module.End.isSemisimple_of_squarefree_aeval_eq_zero hg hlin
  rw [← hs.isFinitelySemisimple.maxGenEigenspace_eq_eigenspace z,
    LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin']

/-- When the squarefree product of the factors annihilates a finite-field
matrix, its total eigenspace dimension counts their distinct roots weighted by
their multiplicities in the characteristic polynomial. -/
theorem sum_finrank_eigenspaces_eq_weighted_root_count {K ι κ : Type*} [Field K]
    [Fintype K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq K]
    (A : Matrix ι ι K) (g : κ → Polynomial K) (e : κ → ℕ)
    (hchar : A.charpoly = ∏ j, g j ^ e j) (hsq : Squarefree (∏ j, g j))
    (hann : Polynomial.aeval A (∏ j, g j) = 0) :
    (∑ z : K, Module.finrank K (Module.End.eigenspace A.toLin' z)) =
      ∑ j, e j * (g j).roots.toFinset.card := by
  calc
    _ = A.charpoly.roots.card := by
      simp_rw [finrank_eigenspace_eq_rootMultiplicity_of_squarefree_aeval_eq_zero A hsq hann,
        ← Polynomial.count_roots]
      exact Multiset.sum_count_eq_card (fun z _ => Finset.mem_univ z)
    _ = _ := by
      have hprod : (∏ j, g j ^ e j) ≠ 0 := hchar ▸ A.charpoly_monic.ne_zero
      rw [hchar, Polynomial.roots_prod _ _ hprod, Multiset.card_bind]
      change (∑ j, (g j ^ e j).roots.card) = _
      refine Finset.sum_congr rfl fun j hj => ?_
      have hgj : Squarefree (g j) := hsq.squarefree_of_dvd (Finset.dvd_prod_of_mem g hj)
      rw [Polynomial.roots_pow, Multiset.card_nsmul,
        Multiset.toFinset_card_of_nodup
          (Polynomial.nodup_roots (PerfectField.separable_iff_squarefree.mpr hgj))]

/-- If the discriminant of a monic polynomial remains nonzero after reducing
its coefficients to a field, the reduction is separable. -/
theorem separable_map_of_discriminant_ne_zero {R K : Type*} [CommRing R] [Field K]
    (f : Polynomial R) (hmonic : f.Monic) (φ : R →+* K) (h : φ f.discr ≠ 0) :
    (f.map φ).Separable := by
  by_cases hz : f.natDegree = 0
  · simp [Polynomial.eq_one_of_monic_natDegree_zero hmonic hz]
  let r := f.resultant f.derivative f.natDegree (f.natDegree - 1)
  have hr : φ r ≠ 0 := by
    have hd : 0 < f.degree := Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hz)
    simp [r, Polynomial.resultant_deriv hd, hmonic.leadingCoeff, h]
  obtain ⟨u, v, _, _, huv⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    f f.derivative le_rfl (Polynomial.natDegree_derivative_le f) (Or.inl hz)
  have hm := congrArg (Polynomial.map φ) huv
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul,
    ← Polynomial.derivative_map, Polynomial.map_C] at hm
  refine ⟨Polynomial.C (φ r)⁻¹ * u.map φ, Polynomial.C (φ r)⁻¹ * v.map φ, ?_⟩
  calc
    _ = Polynomial.C (φ r)⁻¹ * (f.map φ * u.map φ + (f.map φ).derivative * v.map φ) := by
      ring
    _ = 1 := by rw [hm, ← Polynomial.C_mul, inv_mul_cancel₀ hr, Polynomial.C_1]

private theorem map_aeval_matrix {R S ι : Type*} [CommRing R] [CommRing S]
    [Fintype ι] [DecidableEq ι] (φ : R →+* S) (A : Matrix ι ι R) (f : Polynomial R) :
    (Polynomial.aeval A f).map φ = Polynomial.aeval (A.map φ) (f.map φ) := by
  have hcomm : (algebraMap S (Matrix ι ι S)).comp φ =
      φ.mapMatrix.comp (algebraMap R (Matrix ι ι R)) := by
    ext r i j
    by_cases hij : i = j <;> simp [Matrix.algebraMap_matrix_apply, hij]
  exact Polynomial.map_aeval_eq_aeval_map hcomm f A

/-- Each eigenvalue of a Hermitian matrix is a root of some factor in a
characteristic-polynomial product. Hence the product without powers annihilates the matrix. -/
theorem aeval_prod_characteristic_factors_eq_zero_of_isHermitian
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] {A : Matrix ι ι ℂ}
    (hA : A.IsHermitian) (g : κ → Polynomial ℂ) (e : κ → ℕ)
    (hchar : A.charpoly = ∏ j, g j ^ e j) : Polynomial.aeval A (∏ j, g j) = 0 := by
  classical
  let l : ι → ℂ := RCLike.ofReal ∘ hA.eigenvalues
  have hl (i : ι) : A.charpoly.IsRoot (l i) := by
    apply (Polynomial.mem_roots A.charpoly_monic.ne_zero).mp
    rw [hA.roots_charpoly_eq_eigenvalues]
    exact Multiset.mem_map.mpr ⟨i, by simp, rfl⟩
  have hprod : Polynomial.aeval l (∏ j, g j) = 0 := by
    funext i
    rw [Polynomial.aeval_pi_apply₂]
    change (∏ j, g j).eval (l i) = 0
    have hi := hl i
    rw [hchar, Polynomial.IsRoot.def, Polynomial.eval_prod] at hi
    obtain ⟨j, hj, hj0⟩ := Finset.prod_eq_zero_iff.mp hi
    rw [Polynomial.eval_pow] at hj0
    rw [Polynomial.eval_prod]
    apply Finset.prod_eq_zero hj
    by_contra hne
    exact (pow_ne_zero _ hne) hj0
  let U := (Unitary.conjStarAlgAut ℂ (Matrix ι ι ℂ) hA.eigenvectorUnitary).toAlgEquiv.toAlgHom
  let D : (ι → ℂ) →ₐ[ℂ] Matrix ι ι ℂ := Matrix.diagonalAlgHom ℂ
  rw [show A = U (D l) from hA.spectral_theorem,
    Polynomial.aeval_algHom_apply, Polynomial.aeval_algHom_apply, hprod, map_zero, map_zero]

/-- An integer symmetric matrix is annihilated by the product of its distinct
characteristic factors. -/
theorem aeval_prod_characteristic_factors_eq_zero_of_isSymm
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] {A : Matrix ι ι ℤ}
    (hA : A.IsSymm) (g : κ → Polynomial ℤ) (e : κ → ℕ)
    (hchar : A.charpoly = ∏ j, g j ^ e j) : Polynomial.aeval A (∏ j, g j) = 0 := by
  let φ := Int.castRingHom ℂ
  let B := A.map φ
  have hB : B.IsHermitian := by
    rw [Matrix.IsHermitian.ext_iff]
    intro i j
    simp [B, φ, hA.apply i j]
  have hcharB : B.charpoly = ∏ j, ((g j).map φ) ^ e j := by
    change (A.map φ).charpoly = _
    rw [Matrix.charpoly_map, hchar, Polynomial.map_prod]
    simp only [Polynomial.map_pow]
  have hz : (Polynomial.aeval A (∏ j, g j)).map φ = 0 := by
    rw [map_aeval_matrix, Polynomial.map_prod]
    exact aeval_prod_characteristic_factors_eq_zero_of_isHermitian hB _ _ hcharB
  ext i j
  apply Int.cast_injective (α := ℂ)
  simpa [φ] using congrArg (fun M : Matrix ι ι ℂ => M i j) hz

/-- The weighted root-count identity after reducing the entries of a matrix.
The exceptional primes are detected by the discriminant of the product of the
distinct characteristic factors. -/
theorem sum_finrank_eigenspaces_map_eq_weighted_root_count
    {R K ι κ : Type*} [CommRing R] [Field K] [Fintype K] [DecidableEq K]
    [Fintype ι] [DecidableEq ι] [Fintype κ] (A : Matrix ι ι R) (φ : R →+* K)
    (g : κ → Polynomial R) (e : κ → ℕ) (hmonic : ∀ j, (g j).Monic)
    (hchar : A.charpoly = ∏ j, g j ^ e j) (hann : Polynomial.aeval A (∏ j, g j) = 0)
    (hdisc : φ (∏ j, g j).discr ≠ 0) :
    (∑ z : K, Module.finrank K (Module.End.eigenspace (A.map φ).toLin' z)) =
      ∑ j, e j * ((g j).map φ).roots.toFinset.card := by
  have hcharMap : (A.map φ).charpoly = ∏ j, ((g j).map φ) ^ e j := by
    rw [Matrix.charpoly_map, hchar, Polynomial.map_prod]
    simp only [Polynomial.map_pow]
  have hmapProd : (∏ j, g j).map φ = ∏ j, (g j).map φ := Polynomial.map_prod φ _ _
  have hprodMonic : (∏ j, g j).Monic := Polynomial.monic_prod_of_monic _ _ (fun j _ => hmonic j)
  have hsep := separable_map_of_discriminant_ne_zero _ hprodMonic φ hdisc
  rw [hmapProd] at hsep
  have hannMap : Polynomial.aeval (A.map φ) (∏ j, (g j).map φ) = 0 := by
    rw [← hmapProd, ← map_aeval_matrix, hann]
    exact φ.mapMatrix.map_zero
  exact sum_finrank_eigenspaces_eq_weighted_root_count _ _ _ hcharMap hsep.squarefree hannMap

end Bernoulli
