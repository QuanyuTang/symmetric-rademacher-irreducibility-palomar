module

public import Bernoulli.ZetaGrowthLeftBoundary
public import Bernoulli.ZetaGrowthStrip
import Mathlib.Tactic

/-! Quantitative disk growth for the pole-cleared Dedekind zeta function. -/

namespace Bernoulli

/-- Combine the completed functional equation with an absolute-convergence bound.
Only the initial growth estimate is allowed to have arbitrary field-dependent constants. -/
public theorem norm_dedekind_regularization_le_disk (K : Type) [Field K] [NumberField K]
    {ζ Z : ℂ → ℂ} {R : ℝ} (hR : 1 ≤ R) (hZ : Differentiable ℂ Z)
    (hZ_eq : ∀ s : ℂ, s ≠ 1 → Z s = (s - 1) * ζ s)
    (hFE : ∀ s : ℂ, s.re = -1 / 2 → dedekindCompletionFactor K s * ζ s =
      dedekindCompletionFactor K (1 - s) * ζ (1 - s))
    (hright : ∀ s : ℂ, 3 / 2 ≤ s.re → ‖ζ s‖ ≤ R ^ Module.finrank ℚ K)
    (hgrowth : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, -1 / 2 < s.re → s.re < 4 → ‖Z s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2))
    {t : ℝ} {s : ℂ} (hs : s ∈ Metric.ball (2 + (t : ℂ) * Complex.I) (131 / 128)) :
    ‖Z s‖ ≤ 2 * ((|NumberField.discr K| : ℤ) : ℝ) * R ^ Module.finrank ℚ K *
      (9 * (4 + |t|)) ^ (Module.finrank ℚ K + 1) := by
  let D : ℝ := ((|NumberField.discr K| : ℤ) : ℝ)
  let d : ℕ := Module.finrank ℚ K
  have hD : 1 ≤ D := by
    have h := abs_pos.mpr (NumberField.discr_ne_zero K)
    change (1 : ℝ) ≤ ((|NumberField.discr K| : ℤ) : ℝ)
    exact_mod_cast (show (1 : ℤ) ≤ |NumberField.discr K| by omega)
  refine norm_le_zeta_disk_of_polynomial_boundary (by positivity) (d + 1) hZ hgrowth ?_ hs
  intro z hz
  have hz₁ : z ≠ 1 := by
    rintro rfl
    norm_num at hz
  have hz_norm := Complex.norm_le_abs_re_add_abs_im (z - 1)
  have hH : 1 ≤ 2 + |z.im| := by linarith [abs_nonneg z.im]
  rw [hZ_eq z hz₁, norm_mul]
  obtain hz | hz := hz
  · have hright' : 3 / 2 ≤ (1 - z).re := by norm_num [Complex.sub_re, hz]
    have hleft := (norm_dedekind_reflected_left_boundary K hz (hFE z hz)).trans
      (mul_le_mul_of_nonneg_left (hright _ hright') (by positivity))
    have hnorm : ‖z - 1‖ ≤ 2 + |z.im| := by
      norm_num [Complex.sub_re, Complex.sub_im, hz] at hz_norm
      linarith
    calc
      _ ≤ (2 + |z.im|) * (D * (2 + |z.im|) ^ d * R ^ d) :=
        mul_le_mul hnorm hleft (norm_nonneg _) (by positivity)
      _ = D * R ^ d * (2 + |z.im|) ^ (d + 1) := by rw [pow_succ]; ring
      _ ≤ 2 * D * R ^ d * (2 + |z.im|) ^ (d + 1) := by
        gcongr
        linarith
  · have hright' : 3 / 2 ≤ z.re := by linarith
    have hnorm : ‖z - 1‖ ≤ 2 * (2 + |z.im|) := by
      norm_num [Complex.sub_re, Complex.sub_im, hz] at hz_norm
      linarith [abs_nonneg z.im]
    have hpow : 2 + |z.im| ≤ (2 + |z.im|) ^ (d + 1) := by
      exact (pow_one (2 + |z.im|)).symm.le.trans (pow_le_pow_right₀ hH (by omega))
    calc
      _ ≤ (2 * (2 + |z.im|)) * R ^ d :=
        mul_le_mul hnorm (hright z hright') (norm_nonneg _) (by positivity)
      _ = 2 * R ^ d * (2 + |z.im|) := by ring
      _ ≤ 2 * R ^ d * (2 + |z.im|) ^ (d + 1) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ 2 * D * R ^ d * (2 + |z.im|) ^ (d + 1) := by
        gcongr
        linarith

end Bernoulli
