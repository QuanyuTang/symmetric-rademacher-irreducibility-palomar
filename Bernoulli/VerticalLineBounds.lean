module

public import Bernoulli.WeightIntegral
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Absolute convergence on the shifted line under a logarithmic growth estimate. -/

open MeasureTheory

namespace Bernoulli

private theorem log_height_le (t : ℝ) :
    Real.log (3 + |t|) ≤ 4 * (1 + |t|) ^ (1 / 2 : ℝ) := by
  have hpos : 0 < 3 + |t| := by positivity
  have hlog := Real.log_le_self (Real.rpow_nonneg hpos.le (1 / 2 : ℝ))
  rw [Real.log_rpow hpos] at hlog
  have hs : (3 + |t|) ^ (1 / 2 : ℝ) ≤ 2 * (1 + |t|) ^ (1 / 2 : ℝ) := by
    calc
      _ ≤ (4 * (1 + |t|)) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) (by linarith [abs_nonneg t]) (by norm_num)
      _ = _ := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by positivity), ← Real.sqrt_eq_rpow]
        norm_num
  linarith

private theorem height_power_mul_weight (t : ℝ) :
    (1 + |t|) ^ (1 / 2 : ℝ) * ((1 + |t|) ^ (2 : ℕ))⁻¹ =
      (1 + |t|) ^ (-(3 / 2) : ℝ) := by
  have h : 0 < 1 + |t| := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_neg h.le, ← Real.rpow_add h]
  norm_num

/-- The integrand on the shifted line is absolutely integrable. Its integral is bounded
uniformly in the logarithmic growth coefficients and the positive scaling parameter. -/
public theorem vertical_mellin_integral_bound {σ A D x : ℝ}
    (hσ₀ : 1 / 2 ≤ σ) (hσ₁ : σ ≤ 2) (hA : 0 ≤ A) (hD : 0 ≤ D) (hx : 0 < x)
    {L : ℝ → ℂ} (hL : Continuous L)
    (hsize : ∀ t, ‖L t‖ ≤ A + D * Real.log (|t| + 3)) :
    let z (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
    let f (t : ℝ) := L t * (x : ℂ) ^ z t * mellinWeight (z t)
    Integrable f ∧ ‖∫ t : ℝ, f t‖ ≤
      ((A + 4 * D) * 3240 * x ^ σ) * ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ) := by
  dsimp only
  let z (t : ℝ) : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  let f (t : ℝ) := L t * (x : ℂ) ^ z t * mellinWeight (z t)
  change Integrable f ∧ ‖∫ t : ℝ, f t‖ ≤ _
  have hre (t : ℝ) : (z t).re = σ := by simp [z]
  have him (t : ℝ) : (z t).im = t := by simp [z]
  have hz : Continuous z := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hw : Continuous (fun t => mellinWeight (z t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (analyticAt_mellinWeight (by rw [hre]; linarith)).continuousAt.comp hz.continuousAt
  have hx₀ : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hxp : Continuous (fun t => (x : ℂ) ^ z t) := by
    simp only [Complex.cpow_def_of_ne_zero hx₀]
    exact (continuous_const.mul hz).cexp
  have hf : Continuous f := (hL.mul hxp).mul hw
  let g (t : ℝ) := (1 + |t|) ^ (-(3 / 2) : ℝ)
  let c := (A + 4 * D) * 3240 * x ^ σ
  have hg : Integrable g := by
    simpa [g, Real.norm_eq_abs] using
      (integrable_one_add_norm (E := ℝ) (r := 3 / 2) (by norm_num))
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hbound (t : ℝ) : ‖f t‖ ≤ c * g t := by
    have hy : 0 < 1 + |t| := by positivity
    have hy' : 1 ≤ (1 + |t|) ^ (1 / 2 : ℝ) := Real.one_le_rpow (by linarith [abs_nonneg t])
      (by norm_num)
    have hlog : Real.log (|t| + 3) ≤ 4 * (1 + |t|) ^ (1 / 2 : ℝ) := by
      simpa [add_comm] using log_height_le t
    have hb : ‖L t‖ ≤ (A + 4 * D) * (1 + |t|) ^ (1 / 2 : ℝ) := by
      have h₁ := mul_le_mul_of_nonneg_left hlog hD
      have h₂ := mul_le_mul_of_nonneg_left hy' hA
      linarith [hsize t]
    have hW : ‖mellinWeight (z t)‖ ≤ 3240 / (1 + |t|) ^ 2 := by
      simpa [him] using norm_mellinWeight_le (s := z t) (by rwa [hre]) (by rwa [hre])
    have hxpow : ‖(x : ℂ) ^ z t‖ = x ^ σ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]
    calc
      ‖f t‖ ≤ (((A + 4 * D) * (1 + |t|) ^ (1 / 2 : ℝ)) * x ^ σ) *
          (3240 / (1 + |t|) ^ 2) := by
        simp only [f, norm_mul, hxpow]
        exact mul_le_mul (mul_le_mul_of_nonneg_right hb (by positivity)) hW
          (norm_nonneg _) (by positivity)
      _ = c * ((1 + |t|) ^ (1 / 2 : ℝ) * ((1 + |t|) ^ (2 : ℕ))⁻¹) := by
        dsimp [c]
        rw [div_eq_mul_inv]
        ring
      _ = c * g t := by rw [height_power_mul_weight]
  have hcg : Integrable (fun t => c * g t) := hg.const_mul c
  have hfi : Integrable f := hcg.mono' hf.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
  refine ⟨hfi, ?_⟩
  calc
    ‖∫ t, f t‖ ≤ ∫ t, ‖f t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t, c * g t := integral_mono hfi.norm hcg hbound
    _ = _ := integral_const_mul c g

end Bernoulli
