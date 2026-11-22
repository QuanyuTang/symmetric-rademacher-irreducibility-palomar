module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Rectangular contour shifting with integrable vertical lines and vanishing horizontal edges. -/

open Complex Filter MeasureTheory Set
open scoped Interval Topology

namespace Bernoulli

/-- The closed vertical strip with real coordinates between `a` and `b`. -/
@[expose] public def verticalStrip (a b : ℝ) : Set ℂ := {z | z.re ∈ Icc a b}

/-- The difference of the upward vertical contour integrals on a rectangle is
the difference of its left-to-right horizontal integrals. -/
public theorem vertical_rectangle_identity {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f (verticalStrip a b)) (T : ℝ) :
    I * ((∫ t : ℝ in -T..T, f ((b : ℂ) + (t : ℂ) * I)) -
        (∫ t : ℝ in -T..T, f ((a : ℂ) + (t : ℂ) * I))) =
      (∫ u : ℝ in a..b, f ((u : ℂ) + (T : ℂ) * I)) -
        (∫ u : ℝ in a..b, f ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) := by
  let z : ℂ := ⟨a, -T⟩
  let w : ℂ := ⟨b, T⟩
  have hRect : DifferentiableOn ℂ f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    apply hf.mono
    intro p hp
    change p.re ∈ Set.uIcc a b ∧ _ at hp
    exact (uIcc_of_le hab ▸ hp.1 : p.re ∈ Icc a b)
  have h := integral_boundary_rect_eq_zero_of_differentiableOn f z w hRect
  dsimp [z, w] at h
  linear_combination h

private theorem horizontal_integral_tendsto_zero {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    {height g : ℝ → ℝ} (hg : Tendsto g atTop (𝓝 0))
    (hbound : ∀ᶠ T in atTop, ∀ u ∈ Icc a b,
      ‖f ((u : ℂ) + (height T : ℂ) * I)‖ ≤ g T) :
    Tendsto (fun T : ℝ ↦ ∫ u : ℝ in a..b, f ((u : ℂ) + (height T : ℂ) * I)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hdom : Tendsto (fun T : ℝ ↦ g T * |b - a|) atTop (𝓝 0) := by
    simpa only [zero_mul] using hg.mul_const |b - a|
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hdom
  filter_upwards [hbound] with T hT
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro u hu
  have hu' := uIoc_subset_uIcc hu
  rw [uIcc_of_le hab] at hu'
  exact hT u hu'

/-- A holomorphic function on a closed vertical strip has equal integrals on
the two vertical lines if both are integrable and a common bound for the two
horizontal edges tends to zero. The vertical integrals are parameterized by
the imaginary coordinate, increasing upwards. -/
public theorem integral_vertical_eq_of_decay {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f (verticalStrip a b))
    (hleft : Integrable (fun t : ℝ ↦ f ((a : ℂ) + (t : ℂ) * I)))
    (hright : Integrable (fun t : ℝ ↦ f ((b : ℂ) + (t : ℂ) * I)))
    {g : ℝ → ℝ} (hg : Tendsto g atTop (𝓝 0))
    (hdecay : ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc a b,
      ‖f ((u : ℂ) + (T : ℂ) * I)‖ ≤ g T ∧
      ‖f ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ g T) :
    (∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * I)) =
      (∫ t : ℝ, f ((a : ℂ) + (t : ℂ) * I)) := by
  have hUpper := horizontal_integral_tendsto_zero (height := id) hab hg
    (hdecay.mono fun _ ht u hu ↦ (ht u hu).1)
  have hLower := horizontal_integral_tendsto_zero (height := fun T ↦ -T) hab hg
    (hdecay.mono fun _ ht u hu ↦ (ht u hu).2)
  have hLeft := intervalIntegral_tendsto_integral hleft tendsto_neg_atTop_atBot tendsto_id
  have hRight := intervalIntegral_tendsto_integral hright tendsto_neg_atTop_atBot tendsto_id
  have hV := (hRight.sub hLeft).const_mul I
  have hH := hUpper.sub hLower
  have h := tendsto_nhds_unique (hV.congr (vertical_rectangle_identity hab hf)) hH
  rw [sub_self] at h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left I_ne_zero)

/-- A unit pole at `p`, with a compensating pole at `q` so the difference
decays quadratically on vertical lines. -/
@[expose] public noncomputable def simplePoleDifference (p q : ℝ) (z : ℂ) : ℂ :=
  (z - (p : ℂ))⁻¹ - (z - (q : ℂ))⁻¹

private noncomputable def cauchyKernel (d t : ℝ) : ℝ := d / (d ^ 2 + t ^ 2)

private theorem cauchyKernel_eq {d : ℝ} (hd : d ≠ 0) (t : ℝ) :
    cauchyKernel d t = d⁻¹ * (1 + (d⁻¹ * t) ^ 2)⁻¹ := by
  unfold cauchyKernel
  have h₁ : 0 < d ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hd) (sq_nonneg _)
  have h₂ : 0 < 1 + (d⁻¹ * t) ^ 2 := by positivity
  field_simp [hd, h₁.ne', h₂.ne']

private theorem integrable_cauchyKernel {d : ℝ} (hd : d ≠ 0) : Integrable (cauchyKernel d) := by
  rw [show cauchyKernel d = (fun t : ℝ ↦ d⁻¹ * (1 + (d⁻¹ * t) ^ 2)⁻¹) from
    funext (cauchyKernel_eq hd)]
  exact (integrable_inv_one_add_mul_sq (inv_ne_zero hd)).const_mul _

private theorem integral_cauchyKernel {d : ℝ} (hd : d ≠ 0) :
    (∫ t : ℝ, cauchyKernel d t) = Real.pi * (|d| / d) := by
  simp_rw [cauchyKernel_eq hd]
  rw [integral_const_mul, integral_univ_inv_one_add_mul_sq, abs_inv, div_inv_eq_mul]
  ring

private noncomputable def contourPoint (c t : ℝ) : ℂ := (c : ℂ) + (t : ℂ) * I

@[simp] private theorem contourPoint_re (c t : ℝ) : (contourPoint c t).re = c := by
  simp [contourPoint, add_re, mul_re]

@[simp] private theorem contourPoint_im (c t : ℝ) : (contourPoint c t).im = t := by
  simp [contourPoint, add_im, mul_im]

private theorem contourPoint_sub_ne_zero {c p : ℝ} (hc : c ≠ p) (t : ℝ) :
    contourPoint c t - (p : ℂ) ≠ 0 := by
  intro h
  apply hc
  have hre := congrArg Complex.re h
  simpa [sub_re, sub_eq_zero] using hre

private theorem continuous_poleDifference_line {c p q : ℝ} (hp : c ≠ p) (hq : c ≠ q) :
    Continuous (fun t : ℝ ↦ simplePoleDifference p q (contourPoint c t)) := by
  have hconst (v : ℝ) : Continuous (fun t : ℝ ↦ contourPoint c t - (v : ℂ)) := by
    unfold contourPoint
    fun_prop
  exact ((hconst p).inv₀ (contourPoint_sub_ne_zero hp)).sub
    ((hconst q).inv₀ (contourPoint_sub_ne_zero hq))

/-- Away from the real axis the compensated pole has a quadratic bound,
uniformly in the real coordinate. -/
public theorem norm_simplePoleDifference_le {p q : ℝ} {z : ℂ} (hz : z.im ≠ 0) :
    ‖simplePoleDifference p q z‖ ≤ ‖(p : ℂ) - (q : ℂ)‖ / z.im ^ 2 := by
  let zp := z - (p : ℂ)
  let zq := z - (q : ℂ)
  have hp' : zp ≠ 0 := by
    intro h
    exact hz (by simpa [zp, sub_im] using congrArg Complex.im h)
  have hq' : zq ≠ 0 := by
    intro h
    exact hz (by simpa [zq, sub_im] using congrArg Complex.im h)
  have him : z.im ^ 2 ≤ ‖zp‖ * ‖zq‖ := by
    rw [← sq_abs, pow_two]
    refine mul_le_mul ?_ ?_ (abs_nonneg _) (norm_nonneg _)
    · simpa [zp, sub_im] using Complex.abs_im_le_norm zp
    · simpa [zq, sub_im] using Complex.abs_im_le_norm zq
  have hn : zq - zp = (p : ℂ) - (q : ℂ) := by dsimp [zp, zq]; ring
  change ‖zp⁻¹ - zq⁻¹‖ ≤ ‖(p : ℂ) - (q : ℂ)‖ / z.im ^ 2
  rw [inv_sub_inv hp' hq', norm_div, norm_mul, hn]
  exact div_le_div_of_nonneg_left (norm_nonneg _) (sq_pos_of_ne_zero hz) him

/-- Both vertical lines of the compensated simple pole are absolutely
integrable whenever they avoid its poles. -/
public theorem integrable_simplePoleDifference_line {c p q : ℝ} (hp : c ≠ p) (hq : c ≠ q) :
    Integrable (fun t : ℝ ↦ simplePoleDifference p q ((c : ℂ) + (t : ℂ) * I)) := by
  let m := min (|c - p| * |c - q|) 1
  have hm : 0 < m := lt_min
    (mul_pos (abs_pos.mpr (sub_ne_zero.mpr hp)) (abs_pos.mpr (sub_ne_zero.mpr hq))) zero_lt_one
  have hm₁ : m ≤ 1 := min_le_right _ _
  let A : ℝ := 2 * ‖((p : ℂ) - (q : ℂ))‖ / m
  have hInt : Integrable (fun t : ℝ ↦ A * (1 + t ^ 2)⁻¹) := integrable_inv_one_add_sq.const_mul _
  change Integrable (fun t : ℝ ↦ simplePoleDifference p q (contourPoint c t))
  refine hInt.mono' (continuous_poleDifference_line hp hq).aestronglyMeasurable ?_
  filter_upwards with t
  let zp := contourPoint c t - (p : ℂ)
  let zq := contourPoint c t - (q : ℂ)
  have hp' : zp ≠ 0 := contourPoint_sub_ne_zero hp t
  have hq' : zq ≠ 0 := contourPoint_sub_ne_zero hq t
  have hre : m ≤ ‖zp‖ * ‖zq‖ := by
    refine (min_le_left _ _).trans (mul_le_mul ?_ ?_ (abs_nonneg _) (norm_nonneg _))
    · simpa [zp, sub_re] using Complex.abs_re_le_norm zp
    · simpa [zq, sub_re] using Complex.abs_re_le_norm zq
  have him : t ^ 2 ≤ ‖zp‖ * ‖zq‖ := by
    rw [← sq_abs, pow_two]
    refine mul_le_mul ?_ ?_ (abs_nonneg _) (norm_nonneg _)
    · simpa [zp, sub_im] using Complex.abs_im_le_norm zp
    · simpa [zq, sub_im] using Complex.abs_im_le_norm zq
  have hden : m * (1 + t ^ 2) / 2 ≤ ‖zp‖ * ‖zq‖ := by
    have h₀ : m * t ^ 2 ≤ t ^ 2 := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm₁ (sq_nonneg t)
    have h := h₀.trans him
    nlinarith
  have hn : zq - zp = (p : ℂ) - (q : ℂ) := by dsimp [zp, zq]; ring
  have hm' : 0 < m * (1 + t ^ 2) / 2 := by positivity
  change ‖zp⁻¹ - zq⁻¹‖ ≤ A * (1 + t ^ 2)⁻¹
  rw [inv_sub_inv hp' hq', norm_div, norm_mul, hn]
  calc
    _ ≤ ‖((p : ℂ) - (q : ℂ))‖ / (m * (1 + t ^ 2) / 2) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hm' hden
    _ = _ := by dsimp [A]; field_simp

private theorem simplePoleDifference_re (c p q t : ℝ) :
    (simplePoleDifference p q (contourPoint c t)).re = cauchyKernel (c - p) t - cauchyKernel (c - q) t := by
  simp [simplePoleDifference, cauchyKernel, sub_re, inv_re, normSq_apply, sub_im, pow_two]

private theorem simplePoleDifference_im_odd (c p q t : ℝ) :
    (simplePoleDifference p q (contourPoint c (-t))).im =
      -(simplePoleDifference p q (contourPoint c t)).im := by
  simp [simplePoleDifference, sub_re, sub_im, inv_im, normSq_apply, neg_div]
  ring

/-- The integral of the compensated pole is determined by the two signs of the
real distances from the vertical line to the poles. -/
public theorem integral_simplePoleDifference_line {c p q : ℝ} (hp : c ≠ p) (hq : c ≠ q) :
    (∫ t : ℝ, simplePoleDifference p q ((c : ℂ) + (t : ℂ) * I)) =
      ((Real.pi * (|c - p| / (c - p) - |c - q| / (c - q)) : ℝ) : ℂ) := by
  let f t := simplePoleDifference p q (contourPoint c t)
  have hInt : Integrable f := integrable_simplePoleDifference_line hp hq
  have hRe hfun : RCLike.re (f hfun) = cauchyKernel (c - p) hfun - cauchyKernel (c - q) hfun :=
    simplePoleDifference_re c p q hfun
  have hImag : (∫ t : ℝ, (f t).im) = 0 := by
    have hReflection : (∫ t : ℝ, (f (-t)).im) = ∫ t : ℝ, (f t).im := by
      simpa using Measure.integral_comp_mul_left (fun t : ℝ ↦ (f t).im) (-1)
    simp_rw [show ∀ t, (f (-t)).im = -(f t).im from simplePoleDifference_im_odd c p q] at hReflection
    rw [integral_neg] at hReflection
    linarith
  change (∫ t : ℝ, f t) = _
  apply Complex.ext
  · rw [Complex.ofReal_re]
    change RCLike.re (∫ t : ℝ, f t) = _
    rw [← integral_re hInt]
    simp_rw [hRe]
    rw [integral_sub (integrable_cauchyKernel (sub_ne_zero.mpr hp))
        (integrable_cauchyKernel (sub_ne_zero.mpr hq)),
      integral_cauchyKernel (sub_ne_zero.mpr hp), integral_cauchyKernel (sub_ne_zero.mpr hq)]
    ring
  · rw [Complex.ofReal_im]
    change RCLike.im (∫ t : ℝ, f t) = 0
    rw [← integral_im hInt]
    exact hImag

/-- Shifting a vertical integral to the left across a simple pole on the real
axis adds `2π` times its residue to the original right-minus-left difference.
The holomorphic correction uses a compensating pole at `q` to the left of the strip. -/
public theorem integral_vertical_sub_eq_of_simple_pole {f g : ℂ → ℂ} {q a p b : ℝ} {R : ℂ}
    (hqa : q < a) (hap : a < p) (hpb : p < b)
    (hfg : EqOn f (fun z ↦ g z + R * simplePoleDifference p q z)
      (verticalStrip a b \ {(p : ℂ)}))
    (hf : DifferentiableOn ℂ g (verticalStrip a b))
    (hleft : Integrable (fun t : ℝ ↦ g ((a : ℂ) + (t : ℂ) * I)))
    (hright : Integrable (fun t : ℝ ↦ g ((b : ℂ) + (t : ℂ) * I)))
    {bound : ℝ → ℝ} (hbound : Tendsto bound atTop (𝓝 0))
    (hdecay : ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc a b,
      ‖g ((u : ℂ) + (T : ℂ) * I)‖ ≤ bound T ∧
      ‖g ((u : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤ bound T) :
    (∫ t : ℝ, f ((b : ℂ) + (t : ℂ) * I)) -
      (∫ t : ℝ, f ((a : ℂ) + (t : ℂ) * I)) = (((2 * Real.pi : ℝ) : ℂ)) * R := by
  have hab : a ≤ b := (hap.trans hpb).le
  have hbq : q < b := hqa.trans (hap.trans hpb)
  have hg := integral_vertical_eq_of_decay hab hf hleft hright hbound hdecay
  have hline (c : ℝ) (hc : c ∈ Icc a b) (hcp : c ≠ p) (hcq : c ≠ q)
      (hgc : Integrable (fun t : ℝ ↦ g (contourPoint c t))) :
      (∫ t : ℝ, f (contourPoint c t)) =
        (∫ t : ℝ, g (contourPoint c t)) + R * (∫ t : ℝ, simplePoleDifference p q (contourPoint c t)) := by
    have hpole : Integrable (fun t : ℝ ↦ simplePoleDifference p q (contourPoint c t)) :=
      integrable_simplePoleDifference_line hcp hcq
    calc
      _ = ∫ t : ℝ, g (contourPoint c t) + R * simplePoleDifference p q (contourPoint c t) := by
        apply integral_congr_ae
        filter_upwards with t
        apply hfg
        exact ⟨by simpa [verticalStrip] using hc, fun hp ↦
          contourPoint_sub_ne_zero hcp t (sub_eq_zero.mpr hp)⟩
      _ = _ := by rw [integral_add hgc (hpole.const_mul R), integral_const_mul]
  have hPoleLeft : (∫ t : ℝ, simplePoleDifference p q (contourPoint a t)) =
      -((2 * Real.pi : ℝ) : ℂ) := by
    have h1 : a - p < 0 := sub_neg.mpr hap
    have h2 : 0 < a - q := sub_pos.mpr hqa
    change (∫ t : ℝ, simplePoleDifference p q ((a : ℂ) + (t : ℂ) * I)) = _
    rw [integral_simplePoleDifference_line hap.ne hqa.ne', abs_of_neg h1, abs_of_pos h2,
      neg_div, div_self h1.ne, div_self h2.ne']
    push_cast
    ring
  have hPoleRight : (∫ t : ℝ, simplePoleDifference p q (contourPoint b t)) = 0 := by
    have h1 : 0 < b - p := sub_pos.mpr hpb
    have h2 : 0 < b - q := sub_pos.mpr hbq
    change (∫ t : ℝ, simplePoleDifference p q ((b : ℂ) + (t : ℂ) * I)) = _
    rw [integral_simplePoleDifference_line hpb.ne' hbq.ne', abs_of_pos h1, abs_of_pos h2,
      div_self h1.ne', div_self h2.ne']
    simp
  change (∫ t : ℝ, f (contourPoint b t)) - (∫ t : ℝ, f (contourPoint a t)) = _
  change (∫ t : ℝ, g (contourPoint b t)) = (∫ t : ℝ, g (contourPoint a t)) at hg
  rw [hline a ⟨le_rfl, hab⟩ hap.ne hqa.ne' hleft, hline b ⟨hab, le_rfl⟩ hpb.ne' hbq.ne' hright,
    hg, hPoleLeft, hPoleRight]
  ring

end Bernoulli
