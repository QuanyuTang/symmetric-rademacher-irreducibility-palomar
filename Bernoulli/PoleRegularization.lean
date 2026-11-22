module

public import Bernoulli.ContourShift
public import Bernoulli.WeightIntegral
public import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Holomorphic correction of the smoothed Dirichlet integrand at its simple pole. -/

open Filter Set
open scoped Topology

namespace Bernoulli

/-- Dividing a nonvanishing holomorphic function by `z - 1` contributes a unit
simple pole to the negative logarithmic derivative. -/
public theorem neg_logDeriv_div_has_pole_expansion {U : Set ℂ} {Z : ℂ → ℂ}
    (hZ : AnalyticOnNhd ℂ Z U) (hNZ : ∀ z ∈ U, Z z ≠ 0) :
    DifferentiableOn ℂ (fun z => -logDeriv Z z) U ∧
      EqOn (fun z => -logDeriv (fun w => Z w / (w - 1)) z)
        (fun z => -logDeriv Z z + (z - 1)⁻¹) (U \ {(1 : ℂ)}) := by
  constructor
  · intro z hz
    have ha : AnalyticAt ℂ Z z := hZ z hz
    exact ((ha.deriv.differentiableAt.div ha.differentiableAt (hNZ z hz)).neg).differentiableWithinAt
  · intro z hz
    have hz1 : z ≠ 1 := by simpa using hz.2
    have hsub : HasDerivAt (fun w : ℂ => w - 1) 1 z := (hasDerivAt_id z).sub_const 1
    change -logDeriv (fun w : ℂ => Z w / (w - 1)) z = -logDeriv Z z + (z - 1)⁻¹
    rw [logDeriv_fun_div (f := Z) (g := fun w : ℂ => w - 1) z (hNZ z hz.1) (sub_ne_zero.mpr hz1)
      (hZ z hz.1).differentiableAt hsub.differentiableAt,
      logDeriv_apply (fun w : ℂ => w - 1) z, hsub.deriv, one_div]
    ring

/-- If `L` has a unit simple pole at `1` with a holomorphic remainder `H`, the
smoothed integrand has a holomorphic correction on the strip after removing
the compensated pole with residue `x`. -/
public theorem exists_smoothedPoleCorrection {x σ : ℝ} (hx : 0 < x)
    (hσ : 0 < σ) (hσ₁ : σ < 1) {L H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (verticalStrip σ 2))
    (hL : EqOn L (fun z ↦ H z + (z - 1)⁻¹) (verticalStrip σ 2 \ {(1 : ℂ)})) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (verticalStrip σ 2) ∧
      EqOn (fun z : ℂ ↦ L z * (x : ℂ) ^ z * mellinWeight z)
        (fun z ↦ G z + (x : ℂ) * simplePoleDifference 1 0 z)
        (verticalStrip σ 2 \ {(1 : ℂ)}) := by
  let M (z : ℂ) := (x : ℂ) ^ z * mellinWeight z
  let G (z : ℂ) := H z * M z + dslope M 1 z + (x : ℂ) * z⁻¹
  have hM₁ : M 1 = (x : ℂ) := by simp [M, mellinWeight_one]
  have hx₀ : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hPow : Differentiable ℂ (fun z : ℂ ↦ (x : ℂ) ^ z) := by
    simp_rw [Complex.cpow_def_of_ne_zero hx₀]
    fun_prop
  have hRe {z : ℂ} (hz : z ∈ verticalStrip σ 2) : 0 < z.re := hσ.trans_le hz.1
  have hM : DifferentiableOn ℂ M (verticalStrip σ 2) := by
    intro z hz
    exact (hPow z).differentiableWithinAt.mul
      (analyticAt_mellinWeight (hRe hz)).differentiableAt.differentiableWithinAt
  have hStrip : verticalStrip σ 2 ∈ 𝓝 (1 : ℂ) := by
    let interior := Complex.re ⁻¹' Ioo σ 2
    have hopen : IsOpen interior := isOpen_Ioo.preimage Complex.continuous_re
    have hone : (1 : ℂ) ∈ interior := by
      change (1 : ℂ).re ∈ Ioo σ 2
      rw [Complex.one_re]
      exact ⟨hσ₁, by norm_num⟩
    exact mem_of_superset (hopen.mem_nhds hone) fun _ hz ↦ Ioo_subset_Icc_self hz
  have hSlope : DifferentiableOn ℂ (dslope M 1) (verticalStrip σ 2) :=
    (Complex.differentiableOn_dslope hStrip).mpr hM
  have hInv : DifferentiableOn ℂ (fun z : ℂ ↦ z⁻¹) (verticalStrip σ 2) := by
    refine differentiableOn_id.inv fun z hz ↦ ?_
    intro hz₀
    change z = 0 at hz₀
    have hzre := hRe hz
    rw [hz₀, Complex.zero_re] at hzre
    exact (lt_irrefl _ hzre)
  refine ⟨G, ((hH.mul hM).add hSlope).add (hInv.const_mul _), ?_⟩
  intro z hz
  have hz₁ : z ≠ 1 := fun h ↦ hz.2 h
  change L z * (x : ℂ) ^ z * mellinWeight z =
    H z * M z + dslope M 1 z + (x : ℂ) * z⁻¹ + (x : ℂ) * simplePoleDifference 1 0 z
  rw [hL hz, dslope_of_ne M hz₁, slope_def_field, hM₁]
  unfold simplePoleDifference
  simp only [Complex.ofReal_one, Complex.ofReal_zero, sub_zero, div_eq_mul_inv, M]
  ring

end Bernoulli
