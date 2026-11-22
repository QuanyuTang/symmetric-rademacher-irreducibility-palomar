module

public import Bernoulli.ConcreteFactorFields
public import Bernoulli.DiscriminantBounds

import Bernoulli.Algebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-! Uniform discriminant bounds for the characteristic factors of a sampled matrix. -/

public section

open Bernoulli.ConcreteFactorFields
open scoped BigOperators

namespace Bernoulli

private theorem log_two_mul_dim_nonneg {n : ℕ} (hn : 0 < n) :
    0 ≤ Real.log (2 * (n : ℝ)) := by
  have h : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt hn)
  exact Real.log_nonneg (le_trans (by norm_num) (le_mul_of_one_le_right (by norm_num) h))

private theorem fieldDegree_le_dim {n : ℕ} (a : Sample n) (q : Index a) :
    Module.finrank ℚ (RootField a q) ≤ n := by
  rw [fieldDegree_eq_natDegree]
  exact (Polynomial.natDegree_le_of_dvd (integralFactor_dvd_charpoly a q)
    (matrix a).charpoly_monic.ne_zero).trans (by simp)

private theorem map_minpoly_dvd_charpoly {n : ℕ} (a : Sample n) (q : Index a) :
    (minpoly ℚ (powerBasis a q).gen).map (algebraMap ℚ ℂ) ∣
      ((matrix a).map (Int.castRingHom ℂ)).charpoly := by
  rw [minpoly_powerBasis_gen, Polynomial.map_map,
    RingHom.eq_intCast' ((algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ)), Matrix.charpoly_map]
  exact Polynomial.map_dvd _ (integralFactor_dvd_charpoly a q)

private theorem norm_matrix_complex_entries_le_one {n : ℕ} (a : Sample n) (i j : Fin n) :
    ‖((matrix a).map (Int.castRingHom ℂ)) i j‖ ≤ 1 := by
  rcases matrix_entry a i j with h | h <;> simp [h]

private theorem norm_conjugate_le_dim {n : ℕ} (a : Sample n) (q : Index a)
    (σ : RootField a q →ₐ[ℚ] ℂ) : ‖σ (powerBasis a q).gen‖ ≤ (n : ℝ) := by
  have hroot : ((matrix a).map (Int.castRingHom ℂ)).charpoly.IsRoot (σ (powerBasis a q).gen) := by
    have hz : ((minpoly ℚ (powerBasis a q).gen).map (algebraMap ℚ ℂ)).eval
        (σ (powerBasis a q).gen) = 0 := by
      rw [Polynomial.eval_map_algebraMap, Polynomial.aeval_algHom_apply σ, minpoly.aeval, map_zero]
    obtain ⟨g, hg⟩ := map_minpoly_dvd_charpoly a q
    rw [Polynomial.IsRoot.def, hg, Polynomial.eval_mul, hz, zero_mul]
  simpa only [Fintype.card_fin] using norm_le_card_of_isRoot_charpoly _
    (norm_matrix_complex_entries_le_one a) hroot

private theorem log_abs_powerDiscriminant_le {n : ℕ} (a : Sample n) (q : Index a) :
    Real.log |(powerDiscriminant a q : ℝ)| ≤
      ((Module.finrank ℚ (RootField a q) * (Module.finrank ℚ (RootField a q) - 1) : ℕ) : ℝ) *
        Real.log (2 * n) := by
  have hnorm := norm_powerBasis_discr_le (powerBasis a q) (norm_conjugate_le_dim a q)
  rw [powerDiscriminant_spec] at hnorm
  change ‖((powerDiscriminant a q : ℚ) : ℂ)‖ ≤ _ at hnorm
  rw [Rat.cast_intCast, Complex.norm_intCast, ← (powerBasis a q).finrank] at hnorm
  have hpos : 0 < |(powerDiscriminant a q : ℝ)| :=
    abs_pos.mpr (Int.cast_ne_zero.mpr (powerDiscriminant_ne_zero a q))
  exact (Real.log_le_log hpos hnorm).trans_eq (Real.log_pow _ _)

private theorem weighted_logs_le {ι : Type*} [Fintype ι] (d e : ι → ℕ)
    (l : ι → ℝ) {n : ℕ} {s : ℝ} (hs : 0 ≤ s) (hd : ∀ q, d q ≤ n)
    (hde : (∑ q, e q * d q) ≤ n)
    (hl : ∀ q, l q ≤ ((d q * (d q - 1) : ℕ) : ℝ) * s) :
    (∑ q, (e q : ℝ) * l q) ≤ ((n * (n - 1) : ℕ) : ℝ) * s := by
  have hsum : (∑ q, e q * (d q * (d q - 1))) ≤ n * (n - 1) := by
    calc
      _ ≤ ∑ q, e q * (d q * (n - 1)) := Finset.sum_le_sum fun q _ =>
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (hd q) 1))
      _ = (∑ q, e q * d q) * (n - 1) := by
        rw [Finset.sum_mul]
        simp only [Nat.mul_assoc]
      _ ≤ _ := Nat.mul_le_mul_right _ hde
  calc
    _ ≤ ∑ q, ((e q * (d q * (d q - 1)) : ℕ) : ℝ) * s := by
      refine Finset.sum_le_sum fun q _ => ?_
      rw [Nat.cast_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hl q) (Nat.cast_nonneg _)
    _ = ((∑ q, e q * (d q * (d q - 1)) : ℕ) : ℝ) * s := by
      rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hsum) hs

/-- The weighted sum of the logarithms of the factor-field discriminants is
at most `n * (n - 1) * log (2 * n)`. -/
theorem sum_weighted_log_abs_fieldDiscriminant_le {n : ℕ} (a : Sample n) (hn : 0 < n) :
    (∑ q : Index a, (factorMultiplicity (matrix a).charpoly q : ℝ) *
      Real.log |(NumberField.discr (RootField a q) : ℝ)|) ≤
      (n : ℝ) * ((n : ℝ) - 1) * Real.log (2 * n) := by
  have h := weighted_logs_le (fun q => Module.finrank ℚ (RootField a q))
    (factorMultiplicity (matrix a).charpoly)
    (fun q => Real.log |(NumberField.discr (RootField a q) : ℝ)|)
    (log_two_mul_dim_nonneg hn) (fieldDegree_le_dim a) (sum_weighted_fieldDegree a).le (fun q => by
      simpa only [Fintype.card_fin] using log_abs_fieldDiscr_le_of_minpoly_dvd_charpoly
        (powerBasis a q) (integerGenerator a q) (powerBasis_gen a q) _
        (norm_matrix_complex_entries_le_one a) (map_minpoly_dvd_charpoly a q))
  simpa only [Nat.cast_mul, Nat.cast_sub (Nat.succ_le_of_lt hn), Nat.cast_one] using h

/-- The logarithm of the absolute exceptional product is at most twice
`n * (n - 1) * log (2 * n)`. Both the squarefree polynomial discriminant and
the product of the power-basis discriminants contribute at most one copy. -/
theorem log_natAbs_exceptional_product_le {n : ℕ} (a : Sample n) (hn : 0 < n) :
    Real.log (((∏ q : Index a, integralFactor a q).discr *
      ∏ q : Index a, powerDiscriminant a q).natAbs : ℝ) ≤
      2 * (n : ℝ) * ((n : ℝ) - 1) * Real.log (2 * n) := by
  let P := ∏ q : Index a, integralFactor a q
  let degree := fun q : Index a => Module.finrank ℚ (RootField a q)
  have hm : P.Monic := Polynomial.monic_prod_of_monic _ _ fun q _ => integralFactor_monic a q
  have hdiscr : P.discr ≠ 0 :=
    int_poly_discr_ne_zero_of_separable_map _ hm (separable_factorProduct_map_complex a)
  have hsym : (matrix a).IsSymm := Matrix.IsSymm.ext fun i j => matrix_symmetric a j i
  have hPdegree : P.natDegree ≤ n :=
    (Polynomial.natDegree_le_of_dvd (factorProduct_dvd_charpoly a)
      (matrix a).charpoly_monic.ne_zero).trans (by simp)
  have hs := log_two_mul_dim_nonneg hn
  have hP : Real.log |(P.discr : ℝ)| ≤ ((n * (n - 1) : ℕ) : ℝ) * Real.log (2 * n) := by
    have h := log_abs_int_poly_discr_le_of_dvd_charpoly hsym
      (fun i j => (matrix_entry a i j).symm) P hm (factorProduct_dvd_charpoly a) hdiscr
    simp only [Fintype.card_fin] at h
    refine h.trans (mul_le_mul_of_nonneg_right ?_ hs)
    exact_mod_cast Nat.mul_le_mul hPdegree (Nat.sub_le_sub_right hPdegree 1)
  have hdegreeSum : (∑ q, 1 * degree q) ≤ n := by
    calc
      _ ≤ ∑ q : Index a, factorMultiplicity (matrix a).charpoly q * degree q :=
        Finset.sum_le_sum fun q _ => Nat.mul_le_mul_right _
          (Nat.succ_le_of_lt (factorMultiplicity_pos (matrix a).charpoly q))
      _ = n := sum_weighted_fieldDegree a
  have hpowers : (∑ q : Index a, Real.log |(powerDiscriminant a q : ℝ)|) ≤
      ((n * (n - 1) : ℕ) : ℝ) * Real.log (2 * n) := by
    simpa only [Nat.cast_one, one_mul] using weighted_logs_le degree (fun _ => 1)
      (fun q => Real.log |(powerDiscriminant a q : ℝ)|) hs (fieldDegree_le_dim a)
      hdegreeSum (log_abs_powerDiscriminant_le a)
  have hnonzero (q : Index a) : |(powerDiscriminant a q : ℝ)| ≠ 0 :=
    abs_ne_zero.mpr (Int.cast_ne_zero.mpr (powerDiscriminant_ne_zero a q))
  have hprod : Real.log |((∏ q : Index a, powerDiscriminant a q : ℤ) : ℝ)| =
      ∑ q : Index a, Real.log |(powerDiscriminant a q : ℝ)| := by
    rw [Int.cast_prod, Finset.abs_prod]
    exact Real.log_prod (fun q _ => hnonzero q)
  have hprod_ne_zero : |((∏ q : Index a, powerDiscriminant a q : ℤ) : ℝ)| ≠ 0 := by
    rw [Int.cast_prod, Finset.abs_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun q _ => hnonzero q)
  change Real.log ((P.discr * ∏ q : Index a, powerDiscriminant a q).natAbs : ℝ) ≤ _
  rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_mul, abs_mul,
    Real.log_mul (abs_ne_zero.mpr (Int.cast_ne_zero.mpr hdiscr)) hprod_ne_zero, hprod]
  calc
    _ ≤ ((n * (n - 1) : ℕ) : ℝ) * Real.log (2 * n) +
        ((n * (n - 1) : ℕ) : ℝ) * Real.log (2 * n) := add_le_add hP hpowers
    _ = _ := by
      rw [Nat.cast_mul, Nat.cast_sub (Nat.succ_le_of_lt hn), Nat.cast_one]
      ring

end Bernoulli
