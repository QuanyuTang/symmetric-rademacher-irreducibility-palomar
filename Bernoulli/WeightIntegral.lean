module

public import Bernoulli.PrimeWeights
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! The Mellin transform of the compactly supported smoothing weight. -/

open Set MeasureTheory
open scoped Interval

namespace Bernoulli

/-- The Mellin transform of `weight`. Its integral is restricted to the support. -/
@[expose] public noncomputable def mellinWeight (s : ℂ) : ℂ :=
  ∫ u : ℝ in (1 / 2 : ℝ)..1, (weight u : ℂ) * (u : ℂ) ^ (s - 1)

/-- The Mellin transform is an explicit rational expression with a single
complex power of `1 / 2`. -/
public theorem mellinWeight_eq {s : ℂ} (hs : 0 < s.re) :
    mellinWeight s =
      12 * (2 * (s - 2) + (s + 4) * (1 / 2 : ℂ) ^ s) / (s * (s + 1) * (s + 2)) := by
  have h0 : -1 < (s - 1).re := by simpa using sub_lt_sub_right hs 1
  have h1 : -1 < s.re := by linarith
  have h2 : -1 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hi (r : ℂ) (hr : -1 < r.re) :
      IntervalIntegrable (fun u : ℝ ↦ (u : ℂ) ^ r) volume (1 / 2) 1 :=
    intervalIntegral.intervalIntegrable_cpow' hr
  have hi2 := (hi (s + 1) h2).const_mul (-48)
  have hi1 := (hi s h1).const_mul 72
  have hi0 := (hi (s - 1) h0).const_mul 24
  have hs0 : s ≠ 0 := by
    intro h
    simp [h] at hs
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re] at hre
    linarith
  have hs2 : s + 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re] at hre
    linarith
  calc
    mellinWeight s =
        ∫ u : ℝ in (1 / 2 : ℝ)..1,
          (-48 : ℂ) * (u : ℂ) ^ (s + 1) + 72 * (u : ℂ) ^ s - 24 * (u : ℂ) ^ (s - 1) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 1)] at hu
      have hu₀ : (u : ℂ) ≠ 0 := by
        exact_mod_cast (show u ≠ 0 by linarith [hu.1])
      have hsu : (u : ℂ) ^ s = (u : ℂ) ^ (s - 1) * (u : ℂ) := by
        rw [show s = (s - 1) + 1 by ring, Complex.cpow_add _ _ hu₀, Complex.cpow_one]
        rw [show s - 1 + 1 - 1 = s - 1 by ring]
      have hsu' : (u : ℂ) ^ (s + 1) = (u : ℂ) ^ (s - 1) * (u : ℂ) ^ 2 := by
        rw [show s + 1 = (s - 1) + 2 by ring, Complex.cpow_add _ _ hu₀, Complex.cpow_two]
      change (weight u : ℂ) * (u : ℂ) ^ (s - 1) =
        (-48 : ℂ) * (u : ℂ) ^ (s + 1) + 72 * (u : ℂ) ^ s - 24 * (u : ℂ) ^ (s - 1)
      unfold weight
      rw [ite_eq_left ⟨hu.1, hu.2⟩, hsu', hsu]
      push_cast
      ring
    _ = -48 * (1 - (1 / 2 : ℂ) ^ (s + 2)) / (s + 2) +
          72 * (1 - (1 / 2 : ℂ) ^ (s + 1)) / (s + 1) -
          24 * (1 - (1 / 2 : ℂ) ^ s) / s := by
      have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by push_cast; rfl
      rw [intervalIntegral.integral_sub (hi2.add hi1) hi0, intervalIntegral.integral_add hi2 hi1]
      simp only [intervalIntegral.integral_const_mul, integral_cpow (Or.inl h0),
        integral_cpow (Or.inl h1), integral_cpow (Or.inl h2),
        Complex.ofReal_one, Complex.one_cpow, hhalf, sub_add_cancel]
      rw [show s + 1 + 1 = s + 2 by ring]
      ring
    _ = _ := by
      have hz : (1 / 2 : ℂ) ≠ 0 := by norm_num
      rw [Complex.cpow_add s (2 : ℂ) hz, Complex.cpow_add s 1 hz,
        Complex.cpow_two, Complex.cpow_one]
      field_simp
      ring

/-- The weight has Mellin mass one at `s = 1`. -/
public theorem mellinWeight_one : mellinWeight 1 = 1 := by
  rw [mellinWeight_eq (by norm_num : 0 < (1 : ℂ).re), Complex.cpow_one]
  norm_num

/-- The real integral of the smoothing weight over its support is one. -/
public theorem integral_weight : (∫ u : ℝ in (1 / 2 : ℝ)..1, weight u) = 1 := by
  have h := mellinWeight_one
  simp only [mellinWeight, sub_self, Complex.cpow_zero, mul_one, intervalIntegral.integral_ofReal] at h
  exact_mod_cast h

/-- The transform is analytic throughout the right half-plane. -/
public theorem analyticAt_mellinWeight {s : ℂ} (hs : 0 < s.re) :
    AnalyticAt ℂ mellinWeight s := by
  let numerator (z : ℂ) :=
    12 * (2 * (z - 2) + (z + 4) * Complex.exp (Complex.log (1 / 2) * z))
  let denominator (z : ℂ) := z * (z + 1) * (z + 2)
  have nonzero_of_re_pos {z : ℂ} (hz : 0 < z.re) : z ≠ 0 := by
    intro h
    simp [h] at hz
  have hden : denominator s ≠ 0 := by
    have hs₁ : 0 < (s + 1).re := by norm_num [Complex.add_re]; linarith
    have hs₂ : 0 < (s + 2).re := by norm_num [Complex.add_re]; linarith
    exact mul_ne_zero (mul_ne_zero (nonzero_of_re_pos hs) (nonzero_of_re_pos hs₁))
      (nonzero_of_re_pos hs₂)
  have hn : AnalyticAt ℂ numerator s := by dsimp [numerator]; fun_prop
  have hd : AnalyticAt ℂ denominator s := by dsimp [denominator]; fun_prop
  refine (hn.div hd hden).congr ?_
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.eventually_mem hs] with z hz
  rw [mellinWeight_eq hz, Complex.cpow_def_of_ne_zero (by norm_num : (1 / 2 : ℂ) ≠ 0)]
  rfl

/-- On the strip `1 / 2 ≤ Re s ≤ 2`, the Mellin transform decays quadratically
in the imaginary part, uniformly across the strip. -/
public theorem norm_mellinWeight_le {s : ℂ} (hs₀ : 1 / 2 ≤ s.re) (hs₁ : s.re ≤ 2) :
    ‖mellinWeight s‖ ≤ 3240 / (1 + |s.im|) ^ 2 := by
  let R := 1 + |s.im|
  have hR : 0 < R := by dsimp [R]; positivity
  have hpower : ‖(1 / 2 : ℂ) ^ s‖ ≤ 1 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    exact Real.rpow_le_one (by norm_num) (by norm_num) (by linarith)
  have hsub : ‖s - 2‖ ≤ 2 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    norm_num [Complex.sub_re, Complex.sub_im, abs_of_nonpos (sub_nonpos.mpr hs₁)]
    linarith
  have hadd : ‖s + 4‖ ≤ 6 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have h : 0 ≤ s.re + 4 := by linarith
    norm_num [Complex.add_re, Complex.add_im, abs_of_nonneg h]
    linarith
  have hlow (z : ℂ) (hre : 1 / 2 ≤ z.re) (him : z.im = s.im) : R / 3 ≤ ‖z‖ := by
    have h₁ := hre.trans (Complex.re_le_norm z)
    have h₂ : |s.im| ≤ ‖z‖ := by rw [← him]; exact Complex.abs_im_le_norm z
    dsimp [R]
    linarith
  have hlow0 := hlow s hs₀ rfl
  have hlow1 := hlow (s + 1) (by norm_num [Complex.add_re]; linarith) (by simp)
  have hlow2 := hlow (s + 2) (by norm_num [Complex.add_re]; linarith) (by simp)
  let denom : ℝ := ‖s‖ * ‖s + 1‖ * ‖s + 2‖
  have hdenom : (R / 3) ^ 3 ≤ denom := by
    calc
      _ = (R / 3) * (R / 3) * (R / 3) := by ring
      _ ≤ _ := by dsimp [denom]; gcongr
  have hdenom_pos : 0 < denom := lt_of_lt_of_le (by positivity) hdenom
  have hnum : ‖2 * (s - 2) + (s + 4) * (1 / 2 : ℂ) ^ s‖ ≤ 10 * R := by
    calc
      _ ≤ ‖2 * (s - 2)‖ + ‖(s + 4) * (1 / 2 : ℂ) ^ s‖ := norm_add_le _ _
      _ = 2 * ‖s - 2‖ + ‖s + 4‖ * ‖(1 / 2 : ℂ) ^ s‖ := by norm_num [norm_mul]
      _ ≤ 2 * (2 + |s.im|) + (6 + |s.im|) * 1 := by gcongr
      _ ≤ _ := by dsimp [R]; linarith [abs_nonneg s.im]
  rw [mellinWeight_eq (by linarith), norm_div, norm_mul]
  simp only [norm_mul]
  have htwelve : ‖(12 : ℂ)‖ = 12 := by norm_num
  rw [htwelve]
  change 12 * ‖2 * (s - 2) + (s + 4) * (1 / 2 : ℂ) ^ s‖ / denom ≤ 3240 / R ^ 2
  calc
    _ ≤ 120 * R / denom := by
      apply div_le_div_of_nonneg_right _ hdenom_pos.le
      linarith
    _ ≤ 120 * R / (R / 3) ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hdenom
    _ = _ := by field_simp; ring

end Bernoulli
