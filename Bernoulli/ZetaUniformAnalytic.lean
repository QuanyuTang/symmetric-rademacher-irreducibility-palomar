module

public import Bernoulli.AnalyticGrowth
public import Bernoulli.LogDerivativeBounds
public import Bernoulli.ZetaEulerBounds
public import Bernoulli.ZetaGrowth
public import Bernoulli.ZetaRegularization
import Mathlib.Tactic

/-! Logarithmic derivative control in the fixed strip used by the smoothed prime average. -/

open Filter Metric Set
open scoped Topology
namespace Bernoulli

/-- The left endpoint of the Mellin shift inside the known zero-free region. -/
public noncomputable abbrev zetaShiftLine : ℝ := 63 / 64

private theorem center_re (t : ℝ) : (mellinLine t).re = 2 := by simp [mellinLine]

private theorem re_gt_zeroFree_of_mem_ball {z : ℂ} {t : ℝ}
    (hz : z ∈ ball (mellinLine t) (131 / 128)) : 31 / 32 < z.re := by
  rw [mem_ball, Complex.dist_eq] at hz
  have h := (Complex.abs_re_le_norm (z - mellinLine t)).trans_lt hz
  rw [Complex.sub_re, center_re] at h
  linarith [(abs_lt.mp h).1]

private theorem mem_center_ball_of_mem_strip {z : ℂ}
    (hz : z ∈ verticalStrip zetaShiftLine 2) :
    z ∈ closedBall (mellinLine z.im) (65 / 64) := by
  change z.re ∈ Icc zetaShiftLine 2 at hz
  rw [mem_closedBall, Complex.dist_eq]
  have h : z - mellinLine z.im = ((z.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.sub_re]
    · simp [Complex.sub_im]
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hz.2)]
  unfold zetaShiftLine at hz
  linarith [hz.1]

private theorem pole_norm_le {z : ℂ}
    (hz : z.re = zetaShiftLine ∨ z.re = 2 ∨ 1 ≤ |z.im|) :
    ‖(z - 1)⁻¹‖ ≤ 64 := by
  rw [norm_inv]
  have h : 1 / 64 ≤ ‖z - 1‖ := by
    rcases hz with hz | hz | hz
    · have h := Complex.abs_re_le_norm (z - 1)
      norm_num [Complex.sub_re, hz, zetaShiftLine] at h
      exact h
    · have h := Complex.abs_re_le_norm (z - 1)
      norm_num [Complex.sub_re, hz] at h
      linarith
    · have h := Complex.abs_im_le_norm (z - 1)
      simp [Complex.sub_im] at h
      linarith
  simpa using inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 64) h

private theorem log_norm_upper {D R : ℝ} (hD : 1 ≤ D) (hR : 1 ≤ R) {d : ℕ} (hd : 1 ≤ d)
    {t : ℝ} {v : ℝ}
    (hv : v ≤ 2 * D * R ^ d * (9 * (4 + |t|)) ^ (d + 1)) :
    v ≤ Real.exp (Real.log D + (Real.log (2 * R) + 2 * Real.log 12) * d +
      2 * d * Real.log (|t| + 3)) := by
  let W := 12 * (|t| + 3)
  have hW : 1 ≤ W := by dsimp [W]; linarith [abs_nonneg t]
  have hWR : 0 < W := zero_lt_one.trans_le hW
  have hd₁ : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hA : 9 * (4 + |t|) ≤ W := by dsimp [W]; linarith [abs_nonneg t]
  refine hv.trans (le_trans (b := 2 * D * R ^ d * W ^ (2 * d)) ?_ ?_)
  · gcongr
    exact (pow_le_pow_left₀ (by positivity) hA _).trans (pow_le_pow_right₀ hW (by omega))
  · have hprod : 0 < 2 * D * R ^ d * W ^ (2 * d) := by positivity
    rw [← Real.exp_log hprod, Real.exp_le_exp, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_mul (by norm_num) (by positivity)]
    have hlog2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have hbase := mul_le_mul_of_nonneg_right hd₁ hlog2
    rw [Real.log_mul (x := 2) (y := R) (by norm_num) (zero_lt_one.trans_le hR).ne']
    push_cast
    nlinarith

private theorem continuation_eq_regularized_quotient {ζ Z : ℂ → ℂ}
    (hZeq : ∀ s : ℂ, s ≠ 1 → Z s = (s - 1) * ζ s)
    {s : ℂ} (hs : s ≠ 1) : ζ =ᶠ[𝓝 s] fun z => Z z / (z - 1) := by
  filter_upwards [isOpen_compl_singleton.mem_nhds (show s ∈ ({1} : Set ℂ)ᶜ from hs)] with z hz
  have hz' : z ≠ 1 := hz
  rw [hZeq z hz', mul_div_cancel_left₀ _ (sub_ne_zero.mpr hz')]

/-- There is a single absolute constant for the strip bounds in all fields.
The inputs are analytic continuation data on the actual Dedekind zeta function. -/
public theorem exists_dedekind_logDeriv_strip_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K] (ζ Z : ℂ → ℂ),
      Differentiable ℂ Z →
      (∀ s : ℂ, s ≠ 1 → Z s = (s - 1) * ζ s) →
      (∀ s : ℂ, 1 < s.re → ζ s = NumberField.dedekindZeta K s) →
      (∀ s : ℂ, 31 / 32 < s.re → s ≠ 1 → ζ s ≠ 0) →
      (∀ s : ℂ, s.re = -1 / 2 → dedekindCompletionFactor K s * ζ s =
        dedekindCompletionFactor K (1 - s) * ζ (1 - s)) →
      (∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
        ∀ s : ℂ, -1 / 2 < s.re → s.re < 4 → ‖Z s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2)) →
      DifferentiableOn ℂ (fun z => -logDeriv Z z) (verticalStrip zetaShiftLine 2) ∧
      EqOn (fun z => -logDeriv ζ z) (fun z => -logDeriv Z z + (z - 1)⁻¹)
        (verticalStrip zetaShiftLine 2 \ {(1 : ℂ)}) ∧
      ∀ z ∈ verticalStrip zetaShiftLine 2, (z.re = zetaShiftLine ∨ z.re = 2 ∨ 1 ≤ |z.im|) →
        ‖-logDeriv ζ z‖ ≤ C * (Real.log |(NumberField.discr K : ℝ)| + Module.finrank ℚ K) +
          (C * Module.finrank ℚ K) * Real.log (|z.im| + 3) := by
  obtain ⟨A, hA, hcenter⟩ := exists_dedekindZeta_center_norm_lower
  obtain ⟨R, hR, hright⟩ := exists_dedekindZeta_norm_upper
  let F := Real.log (2 * R) + 2 * Real.log 12
  let C := 133632 * (A + F + 2) + 64
  have hF : 0 ≤ F := add_nonneg (Real.log_nonneg (by linarith))
    (mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num)))
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, fun K _ _ ζ Z hZ hZeq hζ hζnz hFE hgrowth => ?_⟩
  let d : ℕ := Module.finrank ℚ K
  let D : ℝ := |(NumberField.discr K : ℝ)|
  have hd : 1 ≤ d := Module.finrank_pos
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hD : 1 ≤ D := by
    have h := abs_pos.mpr (NumberField.discr_ne_zero K)
    change (1 : ℝ) ≤ |(NumberField.discr K : ℝ)|
    exact_mod_cast (show (1 : ℤ) ≤ |NumberField.discr K| by omega)
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD
  have hNV (s : ℂ) (hs : 31 / 32 < s.re) : Z s ≠ 0 :=
    dedekind_regularization_ne_zero K hZ.continuous.continuousAt hZeq hζ hζnz hs
  have hnzStrip : ∀ z ∈ verticalStrip zetaShiftLine 2, Z z ≠ 0 := fun z hz =>
    hNV z (lt_of_lt_of_le (by norm_num [zetaShiftLine]) hz.1)
  have hza : AnalyticOnNhd ℂ Z (verticalStrip zetaShiftLine 2) := fun z _ => hZ.analyticAt z
  obtain ⟨hhol, hexpansion⟩ := neg_logDeriv_div_has_pole_expansion hza hnzStrip
  have hpole : EqOn (fun z => -logDeriv ζ z) (fun z => -logDeriv Z z + (z - 1)⁻¹)
      (verticalStrip zetaShiftLine 2 \ {(1 : ℂ)}) := by
    intro z hz
    have h := (logDeriv_congr_nhds (continuation_eq_regularized_quotient hZeq hz.2)).eq_of_nhds
    change -logDeriv ζ z = -logDeriv Z z + (z - 1)⁻¹
    rw [h]
    exact hexpansion hz
  refine ⟨hhol, hpole, fun z hz hedge => ?_⟩
  let t := z.im
  let B := Real.log D + F * d + 2 * d * Real.log (|t| + 3)
  have hupper (w : ℂ) (hw : w ∈ ball (mellinLine t) (131 / 128)) : ‖Z w‖ ≤ Real.exp B := by
    have h := norm_dedekind_regularization_le_disk K hR hZ hZeq hFE
      (fun s hs => by rw [hζ s (by linarith)]; exact hright K s hs) hgrowth hw
    exact log_norm_upper hD hR hd (by simpa [D, Int.cast_abs] using h)
  have hc₁ : 1 < (mellinLine t).re := by rw [center_re]; norm_num
  have hc_norm : 1 ≤ ‖mellinLine t - 1‖ := by
    have h := Complex.re_le_norm (mellinLine t - 1)
    rw [Complex.sub_re, center_re, Complex.one_re] at h
    linarith
  have hclower : Real.exp (-(A * d)) ≤ ‖Z (mellinLine t)‖ := by
    have hcne : mellinLine t ≠ 1 := fun h => by norm_num [h] at hc₁
    rw [hZeq _ hcne, hζ _ hc₁, norm_mul, ← neg_mul]
    exact (hcenter K t).trans (le_mul_of_one_le_left (norm_nonneg _) hc_norm)
  have hlog := norm_logDeriv_le_fixed_radii hZ.differentiableOn
    (fun w hw => hNV w (re_gt_zeroFree_of_mem_ball hw)) hupper hclower
    (mem_center_ball_of_mem_strip hz)
  have hzne : z ≠ 1 := by
    rcases hedge with he | he | he <;> rintro rfl <;> norm_num [zetaShiftLine] at he
  have ht3 : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith [abs_nonneg t])
  have hC₁ : 133632 ≤ C := by dsimp [C]; linarith
  have hC₂ : 2 * 133632 ≤ C := by dsimp [C]; linarith
  have hC₃ : 133632 * (A + F + 1) + 64 ≤ C := by dsimp [C]; linarith
  have h0 : 0 ≤ 133632 * (1 : ℝ) + 64 := by norm_num
  have heq : -logDeriv ζ z = -logDeriv Z z + (z - 1)⁻¹ := hpole ⟨hz, hzne⟩
  rw [heq]
  calc
    _ ≤ ‖-logDeriv Z z‖ + ‖(z - 1)⁻¹‖ := norm_add_le _ _
    _ ≤ 133632 * (A * d + B + 1) + 64 := by
      exact add_le_add (by simpa [logDeriv_apply] using hlog) (pole_norm_le hedge)
    _ ≤ 133632 * Real.log D + (133632 * (A + F + 1) + 64) * d +
        (2 * 133632) * (d * Real.log (|t| + 3)) := by
      dsimp [B]
      nlinarith only [mul_le_mul_of_nonneg_left hd' h0]
    _ ≤ C * Real.log D + C * d + C * (d * Real.log (|t| + 3)) :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_right hC₁ hlogD)
        (mul_le_mul_of_nonneg_right hC₃ (Nat.cast_nonneg d)))
        (mul_le_mul_of_nonneg_right hC₂ (by positivity))
    _ = _ := by dsimp [d, D, t]; ring

end Bernoulli
