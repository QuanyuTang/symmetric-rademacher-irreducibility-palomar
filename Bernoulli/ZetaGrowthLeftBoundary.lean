module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! The uniform left-edge estimate for the Dedekind zeta functional equation. -/

open Complex
open scoped ComplexConjugate

namespace Bernoulli

/-- The completion multiplier in the functional equation, including the absolute discriminant. -/
@[expose] public noncomputable def dedekindCompletionFactor (K : Type) [Field K] [NumberField K]
    (s : ℂ) : ℂ :=
  (((|NumberField.discr K| : ℤ) : ℂ) ^ (s / 2)) *
    Gammaℝ s ^ NumberField.InfinitePlace.nrRealPlaces K *
    Gammaℂ s ^ NumberField.InfinitePlace.nrComplexPlaces K

private theorem reflected_left_edge {s : ℂ} (hs : s.re = -1 / 2) :
    1 - s = conj (s + 2) := by
  apply Complex.ext
  · simp [Complex.sub_re, Complex.add_re, hs]
    norm_num
  · simp [Complex.sub_im, Complex.add_im]

private theorem left_edge_ne_zero {s : ℂ} (hs : s.re = -1 / 2) : s ≠ 0 := by
  intro h
  rw [h, Complex.zero_re] at hs
  norm_num at hs

private theorem shifted_left_edge_ne_zero {s : ℂ} (hs : s.re = -1 / 2) : s + 1 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [Complex.add_re, hs] at hre

private theorem norm_Gammaℝ_conj (s : ℂ) : ‖Gammaℝ (conj s)‖ = ‖Gammaℝ s‖ := by
  have hc : conj s / 2 = conj (s / 2) := by rw [map_div₀, map_ofNat]
  simp only [Gammaℝ_def, norm_mul, hc,
    Gamma_conj, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos,
    Complex.div_ofNat_re, Complex.neg_re, Complex.conj_re]

private theorem norm_Gammaℂ_conj (s : ℂ) : ‖Gammaℂ (conj s)‖ = ‖Gammaℂ s‖ := by
  have hc : (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; rfl
  simp only [Gammaℂ_def, norm_mul, hc, Gamma_conj, Complex.norm_conj,
    Complex.norm_cpow_eq_rpow_re_of_pos (show 0 < 2 * Real.pi by positivity),
    Complex.neg_re, Complex.conj_re]

private theorem norm_gamma_real_reflected_left {s : ℂ} (hs : s.re = -1 / 2) :
    ‖Gammaℝ (1 - s)‖ = ‖Gammaℝ s‖ * (‖s‖ / (2 * Real.pi)) := by
  rw [reflected_left_edge hs, norm_Gammaℝ_conj, Gammaℝ_add_two (left_edge_ne_zero hs)]
  simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  norm_num
  ring

private theorem norm_gamma_complex_reflected_left {s : ℂ} (hs : s.re = -1 / 2) :
    ‖Gammaℂ (1 - s)‖ =
      ‖Gammaℂ s‖ * (‖s‖ / (2 * Real.pi)) * (‖s + 1‖ / (2 * Real.pi)) := by
  rw [reflected_left_edge hs, norm_Gammaℂ_conj,
    show s + 2 = (s + 1) + 1 by ring, Gammaℂ_add_one (shifted_left_edge_ne_zero hs),
    Gammaℂ_add_one (left_edge_ne_zero hs)]
  simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  norm_num
  ring

private theorem gamma_real_left_ne_zero {s : ℂ} (hs : s.re = -1 / 2) : Gammaℝ s ≠ 0 := by
  intro h
  have hpos : 0 < (s + 2).re := by norm_num [Complex.add_re, hs]
  have hg := Gammaℝ_ne_zero_of_re_pos hpos
  simp [Gammaℝ_add_two (left_edge_ne_zero hs), h] at hg

private theorem gamma_complex_left_ne_zero {s : ℂ} (hs : s.re = -1 / 2) : Gammaℂ s ≠ 0 := by
  rw [Gammaℂ_def]
  refine mul_ne_zero (mul_ne_zero two_ne_zero (cpow_ne_zero_iff.mpr (Or.inl ?_))) ?_
  · exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  · intro h
    have hpos : 0 < (s + 2).re := by norm_num [Complex.add_re, hs]
    have hg := Gamma_ne_zero_of_re_pos hpos
    rw [show s + 2 = (s + 1) + 1 by ring,
      Gamma_add_one _ (shifted_left_edge_ne_zero hs), Gamma_add_one _ (left_edge_ne_zero hs),
      h, mul_zero, mul_zero] at hg
    exact hg rfl

private theorem norm_left_edge_bases {s : ℂ} (hs : s.re = -1 / 2) :
    ‖s‖ / (2 * Real.pi) ≤ 2 + |s.im| ∧ ‖s + 1‖ / (2 * Real.pi) ≤ 2 + |s.im| := by
  have h₀ := Complex.norm_le_abs_re_add_abs_im s
  have h₁ := Complex.norm_le_abs_re_add_abs_im (s + 1)
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  norm_num [Complex.add_re, Complex.add_im, hs] at h₀ h₁
  constructor
  · exact (div_le_self (norm_nonneg _) hpi).trans (by linarith)
  · exact (div_le_self (norm_nonneg _) hpi).trans (by linarith)

/-- Along `Re(s) = -1/2` the reflected Gamma factors are related by integral
shifts and conjugation. The resulting polynomial has degree `[K : ℚ]`. -/
public theorem norm_dedekind_reflected_left_boundary (K : Type) [Field K] [NumberField K]
    {ζ : ℂ → ℂ} {s : ℂ} (hs : s.re = -1 / 2)
    (hFE : dedekindCompletionFactor K s * ζ s =
      dedekindCompletionFactor K (1 - s) * ζ (1 - s)) :
    ‖ζ s‖ ≤ ((|NumberField.discr K| : ℤ) : ℝ) *
      (2 + |s.im|) ^ Module.finrank ℚ K * ‖ζ (1 - s)‖ := by
  let D : ℝ := ((|NumberField.discr K| : ℤ) : ℝ)
  have hD : 0 < D := Int.cast_pos.mpr (abs_pos.mpr (NumberField.discr_ne_zero K))
  have hDℂ : ((|NumberField.discr K| : ℤ) : ℂ) = (D : ℂ) :=
    (Complex.ofReal_intCast _).symm
  have hpow :
      ‖(D : ℂ) ^ ((1 - s) / 2)‖ = D * ‖(D : ℂ) ^ (s / 2)‖ := by
    simp only [Complex.norm_cpow_eq_rpow_re_of_pos hD, Complex.div_ofNat_re,
      Complex.sub_re, Complex.one_re, hs]
    rw [show (1 - -1 / 2 : ℝ) / 2 = 1 + (-1 / 2) / 2 by norm_num,
      Real.rpow_add hD, Real.rpow_one]
  have hGℝ := norm_gamma_real_reflected_left hs
  have hGℂ := norm_gamma_complex_reflected_left hs
  let H : ℝ := 2 + |s.im|
  have hH : 0 ≤ H := by positivity
  obtain ⟨h₀, h₁⟩ := norm_left_edge_bases hs
  have hreal : ‖Gammaℝ (1 - s)‖ ≤ ‖Gammaℝ s‖ * H := by
    rw [hGℝ]
    exact mul_le_mul_of_nonneg_left h₀ (norm_nonneg _)
  have hcomplex : ‖Gammaℂ (1 - s)‖ ≤ ‖Gammaℂ s‖ * H ^ 2 := by
    rw [hGℂ, mul_assoc, pow_two]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact mul_le_mul h₀ h₁ (by positivity) hH
  have hfactor : ‖dedekindCompletionFactor K (1 - s)‖ ≤
      ‖dedekindCompletionFactor K s‖ * (D * H ^ Module.finrank ℚ K) := by
    simp only [dedekindCompletionFactor, hDℂ, norm_mul, norm_pow, hpow]
    calc
      _ ≤ (D * ‖(D : ℂ) ^ (s / 2)‖) *
          (‖Gammaℝ s‖ * H) ^ NumberField.InfinitePlace.nrRealPlaces K *
          (‖Gammaℂ s‖ * H ^ 2) ^ NumberField.InfinitePlace.nrComplexPlaces K := by
        gcongr
      _ = _ := by
        rw [mul_pow, mul_pow, ← pow_mul, ← NumberField.InfinitePlace.card_add_two_mul_card_eq_rank,
          pow_add]
        ring
  have hfactor_pos : 0 < ‖dedekindCompletionFactor K s‖ := by
    refine norm_pos_iff.mpr ?_
    unfold dedekindCompletionFactor
    rw [hDℂ]
    exact mul_ne_zero (mul_ne_zero
      (cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr hD.ne')))
      (pow_ne_zero _ (gamma_real_left_ne_zero hs))) (pow_ne_zero _ (gamma_complex_left_ne_zero hs))
  have hnorm := congrArg norm hFE
  simp only [norm_mul] at hnorm
  apply le_of_mul_le_mul_left _ hfactor_pos
  rw [hnorm, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hfactor (norm_nonneg _)

end Bernoulli
