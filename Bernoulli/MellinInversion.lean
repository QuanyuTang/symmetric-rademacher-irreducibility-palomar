module

public import Bernoulli.WeightIntegral
public import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Mellin inversion for the smoothing weight on the vertical line `Re s = 2`. -/

open Complex MeasureTheory Set
open scoped FourierTransform Interval

namespace Bernoulli

/-- The vertical line used for Mellin inversion, parameterized by its height. -/
@[expose] public noncomputable def mellinLine (t : ℝ) : ℂ := 2 + (t : ℂ) * I

@[simp] public theorem mellinLine_re (t : ℝ) : (mellinLine t).re = 2 := by
  norm_num [mellinLine, add_re, mul_re]

@[simp] public theorem mellinLine_im (t : ℝ) : (mellinLine t).im = t := by
  norm_num [mellinLine, add_im, mul_im]

private theorem ofReal_cpow_eq_exp_log {y : ℝ} (hy : 0 < y) (s : ℂ) :
    (y : ℂ) ^ s = Complex.exp ((Real.log y : ℂ) * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hy.ne'), ← Complex.ofReal_log hy.le]

private theorem weight_eq_zero_of_not_mem {u : ℝ} (hu : u ∉ Ioo (1 / 2 : ℝ) 1) :
    weight u = 0 := by
  by_contra h
  exact hu ((weight_pos_iff u).1 (lt_of_le_of_ne (weight_nonneg u) (Ne.symm h)))

private theorem continuous_weight : Continuous weight := by
  suffices heq : weight = fun u : ℝ ↦ 48 * max (u - 1 / 2) 0 * max (1 - u) 0 by
    rw [heq]
    fun_prop
  funext u
  unfold weight
  by_cases hl : (1 / 2 : ℝ) ≤ u
  · by_cases hr : u ≤ 1
    · rw [ite_eq_left ⟨hl, hr⟩, max_eq_left (sub_nonneg.mpr hl), max_eq_left (sub_nonneg.mpr hr)]
    · rw [ite_eq_right (fun h ↦ hr h.2), max_eq_right (sub_nonpos.mpr (le_of_not_ge hr)), mul_zero]
  · rw [ite_eq_right (fun h ↦ hl h.1), max_eq_right (sub_nonpos.mpr (le_of_not_ge hl)), mul_zero, zero_mul]

private noncomputable def logWeight (u : ℝ) : ℂ :=
  (weight (Real.exp u) : ℂ) * Complex.exp (2 * (u : ℂ))

private theorem continuous_logWeight : Continuous logWeight := by
  unfold logWeight
  exact (Complex.continuous_ofReal.comp (continuous_weight.comp Real.continuous_exp)).mul (by fun_prop)

private theorem integrable_logWeight : Integrable logWeight := by
  apply continuous_logWeight.integrable_of_hasCompactSupport
  refine HasCompactSupport.intro (K := Icc (Real.log (1 / 2 : ℝ)) 0) isCompact_Icc ?_
  intro u hu
  have he : Real.exp u ∉ Ioo (1 / 2 : ℝ) 1 := by
    intro h
    exact hu ⟨by simpa using Real.log_le_log (by norm_num) h.1.le,
      Real.exp_le_one_iff.mp h.2.le⟩
  simp [logWeight, weight_eq_zero_of_not_mem he]

private theorem fourier_logWeight (t : ℝ) :
    𝓕 logWeight t = mellinWeight (mellinLine (-(2 * Real.pi) * t)) := by
  let s := mellinLine (-(2 * Real.pi) * t)
  let g (u : ℝ) : ℂ := (weight u : ℂ) * (u : ℂ) ^ (s - 1)
  have hcomp : (fun v : ℝ ↦ Complex.exp ((↑(-2 * Real.pi * v * t) : ℂ) * I) • logWeight v) =
      (fun v : ℝ ↦ Real.exp v • g (Real.exp v)) := by
    funext v
    change _ = Real.exp v • ((weight (Real.exp v) : ℂ) * (Real.exp v : ℂ) ^ (s - 1))
    rw [ofReal_cpow_eq_exp_log (Real.exp_pos _), Real.log_exp, Complex.real_smul,
      Complex.ofReal_exp, smul_eq_mul]
    unfold logWeight
    calc
      _ = (weight (Real.exp v) : ℂ) *
          Complex.exp (((↑(-2 * Real.pi * v * t) : ℂ) * I) + 2 * (v : ℂ)) := by
        rw [Complex.exp_add]
        ring
      _ = (weight (Real.exp v) : ℂ) * Complex.exp ((v : ℂ) + (v : ℂ) * (s - 1)) := by
        congr 2
        dsimp [s, mellinLine]
        push_cast
        ring
      _ = _ := by rw [Complex.exp_add]; ring
  rw [Real.fourier_real_eq_integral_exp_smul, hcomp, integral_comp_exp]
  change (∫ u in Ioi 0, g u) = mellinWeight s
  unfold mellinWeight
  change (∫ u in Ioi 0, g u) = ∫ u in (1 / 2 : ℝ)..1, g u
  rw [intervalIntegral.integral_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1),
    ← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with u
  by_cases hu : u ∈ Ioc (1 / 2 : ℝ) 1
  · have hu₀ : u ∈ Ioi (0 : ℝ) := lt_trans (by norm_num) hu.1
    rw [indicator_of_mem hu₀, indicator_of_mem hu]
  · have hu' : u ∉ Ioo (1 / 2 : ℝ) 1 := fun hv ↦ hu (Ioo_subset_Ioc_self hv)
    have hg : g u = 0 := by simp [g, weight_eq_zero_of_not_mem hu']
    rw [indicator_of_notMem hu]
    by_cases hu₀ : u ∈ Ioi (0 : ℝ)
    · rw [indicator_of_mem hu₀, hg]
    · rw [indicator_of_notMem hu₀]

private theorem continuous_mellinLine : Continuous mellinLine := by
  unfold mellinLine
  fun_prop

private theorem continuous_mellinWeight_line : Continuous (fun t ↦ mellinWeight (mellinLine t)) := by
  refine continuous_iff_continuousAt.2 fun t ↦ ?_
  exact (analyticAt_mellinWeight (by simp : 0 < (mellinLine t).re)).continuousAt.comp
    continuous_mellinLine.continuousAt

/-- The Mellin transform restricted to the integration line is integrable. -/
public theorem integrable_mellinWeight_line : Integrable (fun t ↦ mellinWeight (mellinLine t)) := by
  have hdom : Integrable (fun t : ℝ ↦ 3240 * (1 + t ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul _
  refine hdom.mono' continuous_mellinWeight_line.aestronglyMeasurable ?_
  filter_upwards with t
  refine (norm_mellinWeight_le (s := mellinLine t) (by norm_num) (by simp)).trans ?_
  rw [mellinLine_im, ← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  nlinarith [abs_nonneg t, sq_abs t]

/-- Mellin inversion on `Re s = 2`, with real height as the integration variable. -/
public theorem mellin_inversion {y : ℝ} (hy : 0 < y) :
    (weight y : ℂ) = (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
      ∫ t : ℝ, mellinWeight (mellinLine t) * (y : ℂ) ^ (-(mellinLine t)) := by
  let c : ℝ := -(2 * Real.pi)
  let L := Real.log y
  let B := Complex.exp (2 * (L : ℂ))
  let F (t : ℝ) := mellinWeight (mellinLine t) * (y : ℂ) ^ (-(mellinLine t))
  have hpi : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hc : c ≠ 0 := neg_ne_zero.mpr hpi.ne'
  have hFourier : Integrable (𝓕 logWeight) := by
    rw [show 𝓕 logWeight = (fun t ↦ mellinWeight (mellinLine (c * t))) from funext fourier_logWeight]
    exact integrable_mellinWeight_line.comp_mul_left' hc
  have hinv := integrable_logWeight.fourierInv_fourier_eq hFourier
    (v := L) continuous_logWeight.continuousAt
  have hkernel : 𝓕⁻ (𝓕 logWeight) L = ∫ u : ℝ, B * F (c * u) := by
    rw [Real.fourierInv_eq_fourier_neg, Real.fourier_real_eq_integral_exp_smul]
    apply integral_congr_ae
    filter_upwards with u
    rw [fourier_logWeight, smul_eq_mul]
    change Complex.exp ((↑(-2 * Real.pi * u * -L) : ℂ) * I) *
      mellinWeight (mellinLine (c * u)) = B *
      (mellinWeight (mellinLine (c * u)) * (y : ℂ) ^ (-(mellinLine (c * u))))
    rw [ofReal_cpow_eq_exp_log hy]
    dsimp [B]
    calc
      _ = mellinWeight (mellinLine (c * u)) *
          Complex.exp (((↑(-2 * Real.pi * u * -L) : ℂ) * I)) := by ring
      _ = mellinWeight (mellinLine (c * u)) *
          Complex.exp (2 * (L : ℂ) + (L : ℂ) * (-(mellinLine (c * u)))) := by
        congr 2
        dsimp [mellinLine, c]
        push_cast
        ring
      _ = _ := by rw [Complex.exp_add]; dsimp [L]; ring
  rw [hkernel, integral_const_mul, Measure.integral_comp_mul_left] at hinv
  have hscale : |c⁻¹| = (2 * Real.pi)⁻¹ := by
    rw [abs_inv]
    simp [c, abs_of_pos hpi]
  rw [hscale, Complex.real_smul, Complex.ofReal_inv] at hinv
  have hv : logWeight L = B * (weight y : ℂ) := by
    simp [logWeight, B, L, Real.exp_log hy, mul_comm]
  rw [hv] at hinv
  exact mul_left_cancel₀ (Complex.exp_ne_zero _) hinv.symm

/-- For a series absolutely summable on the integration line, the sum may be
passed through Mellin inversion. The positive bases can be specialized to
`(n + 1) / x` for a scaled Dirichlet series. -/
public theorem tsum_mellin_inversion {ι : Type*} [Countable ι] (a : ι → ℂ) (y : ι → ℝ)
    (hy : ∀ i, 0 < y i) (hsum : Summable (fun i ↦ ‖a i‖ * (y i) ^ (-(2 : ℝ)))) :
    (∑' i, a i * (weight (y i) : ℂ)) = (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
      ∫ t : ℝ, (∑' i, a i * (y i : ℂ) ^ (-(mellinLine t))) * mellinWeight (mellinLine t) := by
  let f (i : ι) (t : ℝ) := (a i * (y i : ℂ) ^ (-(mellinLine t))) * mellinWeight (mellinLine t)
  have hf_norm (i : ι) (t : ℝ) :
      ‖f i t‖ = (‖a i‖ * (y i) ^ (-(2 : ℝ))) * ‖mellinWeight (mellinLine t)‖ := by
    simp only [f, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hy i), neg_re, mellinLine_re]
  have hf_int (i : ι) : Integrable (f i) := by
    have hpow : Continuous (fun t ↦ (y i : ℂ) ^ (-(mellinLine t))) := by
      simp_rw [ofReal_cpow_eq_exp_log (hy i)]
      exact Complex.continuous_exp.comp (continuous_const.mul continuous_mellinLine.neg)
    have hcont : Continuous (f i) := (continuous_const.mul hpow).mul continuous_mellinWeight_line
    apply (integrable_mellinWeight_line.norm.const_mul (‖a i‖ * (y i) ^ (-(2 : ℝ)))).mono'
    · exact hcont.aestronglyMeasurable
    · filter_upwards with t
      exact (hf_norm i t).le
  have hf_summable : Summable (fun i ↦ ∫ t : ℝ, ‖f i t‖) := by
    simp_rw [hf_norm, integral_const_mul]
    exact hsum.mul_right _
  calc
    (∑' i, a i * (weight (y i) : ℂ)) =
        (((2 * Real.pi : ℝ) : ℂ)⁻¹) * (∑' i, ∫ t : ℝ, f i t) := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro i
      have hf_eq : f i = fun t ↦ a i * (mellinWeight (mellinLine t) * (y i : ℂ) ^ (-(mellinLine t))) := by
        funext t
        dsimp [f]
        ring
      rw [hf_eq, integral_const_mul, mellin_inversion (hy i)]
      ring
    _ = _ := by
      rw [integral_tsum_of_summable_integral_norm hf_int hf_summable]
      congr 1
      apply integral_congr_ae
      filter_upwards with t
      simp only [f, tsum_mul_right]

/-- Mellin inversion for an absolutely summable Dirichlet series on `Re s = 2`.
The index `n` denotes the positive integer `n + 1`. -/
public theorem dirichlet_mellin_inversion (a : ℕ → ℂ) {x : ℝ} (hx : 0 < x)
    (ha : Summable (fun n : ℕ ↦ ‖a n‖ * (n + 1 : ℝ) ^ (-(2 : ℝ)))) :
    (∑' n : ℕ, a n * (weight ((n + 1 : ℝ) / x) : ℂ)) = (((2 * Real.pi : ℝ) : ℂ)⁻¹) *
      ∫ t : ℝ, ((∑' n : ℕ, a n * ((n + 1 : ℝ) : ℂ) ^ (-(mellinLine t))) *
        (x : ℂ) ^ (mellinLine t)) * mellinWeight (mellinLine t) := by
  let b (n : ℕ) : ℝ := n + 1
  have hb (n : ℕ) : 0 < b n := by dsimp [b]; positivity
  have hsum : Summable (fun n : ℕ ↦ ‖a n‖ * (b n / x) ^ (-(2 : ℝ))) := by
    convert ha.mul_right (x ^ (2 : ℝ)) using 1
    funext n
    change ‖a n‖ * (b n / x) ^ (-(2 : ℝ)) = (‖a n‖ * b n ^ (-(2 : ℝ))) * x ^ (2 : ℝ)
    rw [Real.div_rpow (hb n).le hx.le, Real.rpow_neg hx.le, div_inv_eq_mul]
    ring
  have hpow (n : ℕ) (s : ℂ) :
      ((b n / x : ℝ) : ℂ) ^ (-s) = (b n : ℂ) ^ (-s) * (x : ℂ) ^ s := by
    rw [ofReal_cpow_eq_exp_log (div_pos (hb n) hx), ofReal_cpow_eq_exp_log (hb n),
      ofReal_cpow_eq_exp_log hx, Real.log_div (hb n).ne' hx.ne', Complex.ofReal_sub, ← Complex.exp_add]
    congr 1
    ring
  rw [tsum_mellin_inversion a (fun n ↦ b n / x) (fun n ↦ div_pos (hb n) hx) hsum]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  change (∑' n : ℕ, a n * ((b n / x : ℝ) : ℂ) ^ (-(mellinLine t))) * mellinWeight (mellinLine t) =
    ((∑' n : ℕ, a n * (b n : ℂ) ^ (-(mellinLine t))) * (x : ℂ) ^ (mellinLine t)) *
      mellinWeight (mellinLine t)
  simp only [hpow, ← mul_assoc, tsum_mul_right]

end Bernoulli
