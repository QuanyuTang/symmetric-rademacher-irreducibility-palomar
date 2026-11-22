module

public import Bernoulli.ContourShift
public import Bernoulli.MellinInversion
public import Bernoulli.VerticalLineBounds
import Mathlib.Tactic

/-! The smoothed Dirichlet coefficient estimate from a simple pole and vertical bounds. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Bernoulli

/-- The integrand in the weighted Dirichlet coefficient estimate. -/
@[expose] public noncomputable def smoothedIntegrand (L : ℂ → ℂ) (x : ℝ) (z : ℂ) : ℂ :=
  L z * (x : ℂ) ^ z * mellinWeight z

/-- The quantitative contour argument with the analytic continuation and strip bounds
as hypotheses on the Dirichlet series. -/
public theorem smoothed_dirichlet_bound {x σ A D : ℝ} (hx : 0 < x)
    (hσ : 1 / 2 ≤ σ) (hσ₁ : σ < 1) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (a : ℕ → ℂ) (L G : ℂ → ℂ)
    (hsum : Summable (fun n : ℕ => ‖a n‖ * (n + 1 : ℝ) ^ (-(2 : ℝ))))
    (hseries : ∀ t, L (mellinLine t) = ∑' n : ℕ, a n * ((n + 1 : ℝ) : ℂ) ^ (-mellinLine t))
    (hG : DifferentiableOn ℂ G (verticalStrip σ 2))
    (hG_eq : EqOn (smoothedIntegrand L x) (fun z => G z + (x : ℂ) * simplePoleDifference 1 0 z)
      (verticalStrip σ 2 \ {(1 : ℂ)}))
    (hGleft : Integrable (fun t : ℝ => G ((σ : ℂ) + (t : ℂ) * Complex.I)))
    (hGright : Integrable (fun t : ℝ => G ((2 : ℂ) + (t : ℂ) * Complex.I)))
    {bound : ℝ → ℝ} (hbound : Tendsto bound atTop (𝓝 0))
    (hdecay : ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc σ 2,
      ‖G ((u : ℂ) + (T : ℂ) * Complex.I)‖ ≤ bound T ∧
      ‖G ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ bound T)
    (hL : Continuous (fun t : ℝ => L ((σ : ℂ) + (t : ℂ) * Complex.I)))
    (hsize : ∀ t : ℝ,
      ‖L ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A + D * Real.log (|t| + 3)) :
    ‖(∑' n : ℕ, a n * (weight ((n + 1 : ℝ) / x) : ℂ)) - (x : ℂ)‖ ≤
      ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
      (((A + 4 * D) * 3240 * x ^ σ) * ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ)) := by
  let κ : ℂ := ((2 * Real.pi : ℝ) : ℂ)
  let right := ∫ t : ℝ, smoothedIntegrand L x ((2 : ℂ) + (t : ℂ) * Complex.I)
  let left := ∫ t : ℝ, smoothedIntegrand L x ((σ : ℂ) + (t : ℂ) * Complex.I)
  have hκ : κ ≠ 0 := by
    dsimp [κ]
    exact_mod_cast (ne_of_gt (by positivity : 0 < 2 * Real.pi))
  have hshift : right - left = κ * (x : ℂ) :=
    integral_vertical_sub_eq_of_simple_pole (by linarith : 0 < σ) hσ₁ (by norm_num : (1 : ℝ) < 2)
      hG_eq hG hGleft hGright hbound hdecay
  have hr : (∑' n : ℕ, a n * (weight ((n + 1 : ℝ) / x) : ℂ)) = κ⁻¹ * right := by
    rw [dirichlet_mellin_inversion a hx hsum]
    change κ⁻¹ * (∫ t : ℝ, ((∑' n : ℕ, a n * ((n + 1 : ℝ) : ℂ) ^ (-mellinLine t)) *
      (x : ℂ) ^ mellinLine t) * mellinWeight (mellinLine t)) =
      κ⁻¹ * (∫ t : ℝ, (L (mellinLine t) * (x : ℂ) ^ mellinLine t) * mellinWeight (mellinLine t))
    simp only [hseries]
  have hleft := (vertical_mellin_integral_bound hσ (by linarith) hA hD hx hL hsize).2
  change ‖left‖ ≤ _ at hleft
  rw [hr, show κ⁻¹ * right - (x : ℂ) = κ⁻¹ * left by
    have heq : right = left + κ * (x : ℂ) := by linear_combination hshift
    rw [heq, mul_add, ← mul_assoc, inv_mul_cancel₀ hκ, one_mul, add_sub_cancel_right], norm_mul]
  exact mul_le_mul_of_nonneg_left hleft (norm_nonneg _)

end Bernoulli
