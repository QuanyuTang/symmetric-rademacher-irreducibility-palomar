module

public import Mathlib.Analysis.Complex.BorelCaratheodory
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Bounds for the logarithmic derivative of a zero-free holomorphic function on a disk. -/

open Metric Set

namespace Bernoulli

/-- A holomorphic function without zeros on a disk has a logarithm normalized
by `g c = 0` after dividing the function by its central value. -/
public theorem exists_normalized_holomorphic_log {Z : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hZ : DifferentiableOn ℂ Z (ball c R)) (hZ₀ : ∀ z ∈ ball c R, Z z ≠ 0) :
    ∃ g : ℂ → ℂ, g c = 0 ∧
      (∀ z ∈ ball c R, HasDerivAt g (deriv Z z / Z z) z) ∧
      EqOn Z (fun z ↦ Z c * Complex.exp (g z)) (ball c R) := by
  let Q (z : ℂ) := deriv Z z / Z z
  have hdZ : DifferentiableOn ℂ (deriv Z) (ball c R) :=
    (hZ.analyticOnNhd isOpen_ball).deriv.differentiableOn
  have hQ : DifferentiableOn ℂ Q (ball c R) := hdZ.div hZ hZ₀
  obtain ⟨g, hgc, hg⟩ := hQ.isExactOn_ball.with_val_at c (0 : ℂ)
  refine ⟨g, hgc, hg, ?_⟩
  let F (z : ℂ) := Z z * Complex.exp (-g z)
  have hF (z : ℂ) (hz : z ∈ ball c R) : HasDerivAt F 0 z := by
    have hzD := (hZ.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hproduct := hzD.mul (hg z hz).neg.cexp
    convert hproduct using 1
    dsimp [Q]
    field_simp [hZ₀ z hz]
    ring
  intro z hz
  have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball c R).isPreconnected
    (f := F) (fun w hw ↦ (hF w hw).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hF w hw).deriv) hz (mem_ball_self hR)
  change Z z * Complex.exp (-g z) = Z c * Complex.exp (-g c) at hconst
  rw [hgc, neg_zero, Complex.exp_zero, mul_one] at hconst
  calc
    Z z = (Z z * Complex.exp (-g z)) * Complex.exp (g z) := by
      rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = Z c * Complex.exp (g z) := by rw [hconst]

/-- Borel–Carathéodory followed by Cauchy's derivative estimate. A bound on
the real part of a holomorphic function that vanishes at the center controls
its derivative on a smaller concentric disk. -/
public theorem norm_deriv_le_of_re_le_of_center_zero {g : ℂ → ℂ} {c z : ℂ} {r ρ R M : ℝ}
    (hr : 0 ≤ r) (hrρ : r < ρ) (hρR : ρ < R) (hM : 0 < M)
    (hg : DifferentiableOn ℂ g (ball c R)) (hgc : g c = 0)
    (hRe : ∀ w ∈ ball c R, (g w).re ≤ M) (hz : z ∈ closedBall c r) :
    ‖deriv g z‖ ≤ (2 * M * ρ / (R - ρ)) / (ρ - r) := by
  have hR : 0 < R := hr.trans_lt (hrρ.trans hρR)
  have hshift : MapsTo (fun w : ℂ ↦ c + w) (ball 0 R) (ball c R) := by
    intro w hw
    simpa [mem_ball, Complex.dist_eq] using hw
  have hDiff : DifferentiableOn ℂ (fun w : ℂ ↦ g (c + w)) (ball 0 R) :=
    hg.comp (by fun_prop) hshift
  have hReShift : MapsTo (fun w : ℂ ↦ g (c + w)) (ball 0 R) {v | v.re ≤ M} :=
    fun _ hw ↦ hRe _ (hshift hw)
  have hNorm (w : ℂ) (hw : w ∈ closedBall c ρ) : ‖g w‖ ≤ 2 * M * ρ / (R - ρ) := by
    have hnorm : ‖w - c‖ ≤ ρ := by simpa [mem_closedBall, Complex.dist_eq] using hw
    have hball : w - c ∈ ball (0 : ℂ) R := mem_ball_zero_iff.mpr (hnorm.trans_lt hρR)
    have hBC := Complex.borelCaratheodory_zero hM hDiff hReShift hR hball (by simp [hgc])
    simp only [add_sub_cancel] at hBC
    calc
      ‖g w‖ ≤ 2 * M * ‖w - c‖ / (R - ‖w - c‖) := hBC
      _ ≤ 2 * M * ‖w - c‖ / (R - ρ) :=
        div_le_div_of_nonneg_left (by positivity) (sub_pos.mpr hρR) (sub_le_sub_left hnorm R)
      _ ≤ 2 * M * ρ / (R - ρ) := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnorm (by positivity)) (sub_nonneg.mpr hρR.le)
  have hSub : closedBall z (ρ - r) ⊆ closedBall c ρ := by
    intro w hw
    have hDist := dist_triangle w z c
    have hwz := mem_closedBall.mp hw
    have hzc := mem_closedBall.mp hz
    exact mem_closedBall.mpr (by linarith)
  have hClosure : closure (ball z (ρ - r)) ⊆ ball c R :=
    closure_ball_subset_closedBall.trans (hSub.trans (closedBall_subset_ball hρR))
  exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (sub_pos.mpr hrρ)
    (hg.mono hClosure).diffContOnCl (fun w hw ↦ hNorm w (hSub (sphere_subset_closedBall hw)))

/-- A zero-free holomorphic function has a quantitative logarithmic derivative
bound on a smaller disk, from exponential bounds on its modulus on the disk
and at its center. -/
public theorem norm_logDeriv_le_of_norm_le_exp {Z : ℂ → ℂ} {c z : ℂ} {r ρ R A B : ℝ}
    (hr : 0 ≤ r) (hrρ : r < ρ) (hρR : ρ < R)
    (hZ : DifferentiableOn ℂ Z (ball c R)) (hZ₀ : ∀ w ∈ ball c R, Z w ≠ 0)
    (hupper : ∀ w ∈ ball c R, ‖Z w‖ ≤ Real.exp B) (hlower : Real.exp (-A) ≤ ‖Z c‖)
    (hz : z ∈ closedBall c r) :
    ‖deriv Z z / Z z‖ ≤ (2 * (A + B + 1) * ρ / (R - ρ)) / (ρ - r) := by
  have hR : 0 < R := hr.trans_lt (hrρ.trans hρR)
  have hc : c ∈ ball c R := mem_ball_self hR
  obtain ⟨g, hgc, hgd, heq⟩ := exists_normalized_holomorphic_log hR hZ hZ₀
  have hg : DifferentiableOn ℂ g (ball c R) := fun w hw ↦
    (hgd w hw).differentiableAt.differentiableWithinAt
  have hM : 0 < A + B + 1 := by
    linarith [Real.exp_le_exp.mp (hlower.trans (hupper c hc))]
  have hRe (w : ℂ) (hw : w ∈ ball c R) : (g w).re ≤ A + B + 1 := by
    have hNorm : Real.exp ((g w).re) * ‖Z c‖ = ‖Z w‖ := by
      rw [heq hw, norm_mul, Complex.norm_exp, mul_comm]
    have hExp := (mul_le_mul_of_nonneg_left hlower (Real.exp_pos ((g w).re)).le).trans
      (hNorm.le.trans (hupper w hw))
    rw [← Real.exp_add, Real.exp_le_exp] at hExp
    linarith
  have hBound := norm_deriv_le_of_re_le_of_center_zero hr hrρ hρR hM hg hgc hRe hz
  have hz' : z ∈ ball c R := closedBall_subset_ball (hrρ.trans hρR) hz
  simpa only [(hgd z hz').deriv] using hBound

/-- The logarithmic derivative estimate at the radii used for the zeta bound. -/
public theorem norm_logDeriv_le_fixed_radii {Z : ℂ → ℂ} {c z : ℂ} {A B : ℝ}
    (hZ : DifferentiableOn ℂ Z (ball c (131 / 128)))
    (hZ₀ : ∀ w ∈ ball c (131 / 128), Z w ≠ 0)
    (hupper : ∀ w ∈ ball c (131 / 128), ‖Z w‖ ≤ Real.exp B)
    (hlower : Real.exp (-A) ≤ ‖Z c‖) (hz : z ∈ closedBall c (65 / 64)) :
    ‖deriv Z z / Z z‖ ≤ 133632 * (A + B + 1) := by
  have h := norm_logDeriv_le_of_norm_le_exp (ρ := 261 / 256)
    (by norm_num) (by norm_num) (by norm_num) hZ hZ₀ hupper hlower hz
  exact h.trans_eq (by ring)

end Bernoulli
