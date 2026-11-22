module

public import Bernoulli.AnalyticAverage
public import Bernoulli.PoleRegularization
import Mathlib.Tactic

/-! Horizontal-edge decay for the regularized Mellin integrand. -/

open Filter MeasureTheory Set
open scoped Topology

namespace Bernoulli

/-- A logarithmic strip bound for the Dirichlet series suffices to make the horizontal
edges of the compensated contour tend to zero. -/
public theorem smoothedPoleCorrection_horizontal_decay {x σ A D : ℝ}
    (hx : 1 ≤ x) (hσ : 1 / 2 ≤ σ) (hA : 0 ≤ A) (hD : 0 ≤ D)
    {L G : ℂ → ℂ}
    (hG_eq : EqOn (smoothedIntegrand L x) (fun z => G z + (x : ℂ) * simplePoleDifference 1 0 z)
      (verticalStrip σ 2 \ {(1 : ℂ)}))
    (hsize : ∀ z ∈ verticalStrip σ 2, 1 ≤ |z.im| → ‖L z‖ ≤ A + D * Real.log (|z.im| + 3)) :
    ∃ bound : ℝ → ℝ, Tendsto bound atTop (𝓝 0) ∧
      ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc σ 2,
        ‖G ((u : ℂ) + (T : ℂ) * Complex.I)‖ ≤ bound T ∧
        ‖G ((u : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ bound T := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  let B := 3240 * x ^ 2 * (A + 3 * D)
  let bound (T : ℝ) := B / (1 + T) + x / T ^ 2
  use bound
  constructor
  · have htop : Tendsto (fun t : ℝ => 1 + t) atTop atTop := by
      refine tendsto_atTop.mpr fun b => ?_
      filter_upwards [eventually_ge_atTop b] with t ht
      linarith
    have h₁ := tendsto_inv_atTop_zero.comp htop
    have h₂ := (tendsto_inv_atTop_zero (𝕜 := ℝ)).pow 2
    simpa [bound, div_eq_mul_inv, inv_pow] using (h₁.const_mul B).add (h₂.const_mul x)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
    intro u hu
    have hTpos : 0 < T := zero_lt_one.trans_le hT
    have atHeight (t : ℝ) (ht : |t| = T) : ‖G ((u : ℂ) + (t : ℂ) * Complex.I)‖ ≤ bound T := by
      let z : ℂ := (u : ℂ) + (t : ℂ) * Complex.I
      change ‖G z‖ ≤ bound T
      have hre : z.re = u := by simp [z]
      have him : z.im = t := by simp [z]
      have hz : z ∈ verticalStrip σ 2 := by simpa [verticalStrip, hre] using hu
      have hzim : z.im ≠ 0 := by
        intro h
        rw [him] at h
        simp [h] at ht
        linarith
      have hz1 : z ≠ 1 := fun h => hzim (by simp [h])
      have hLe : ‖L z‖ ≤ (A + 3 * D) * (1 + T) := by
        have hL := hsize z hz (by rwa [him, ht])
        rw [him, ht] at hL
        have hlog := Real.log_le_self (by linarith : 0 ≤ T + 3)
        have hmul := mul_le_mul_of_nonneg_left hlog hD
        nlinarith [mul_nonneg hA hTpos.le, mul_nonneg hD hTpos.le]
      have hxpow : ‖(x : ℂ) ^ z‖ ≤ x ^ 2 := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hxpos, hre, ← Real.rpow_ofNat]
        exact Real.rpow_le_rpow_of_exponent_le hx hu.2
      have hW : ‖mellinWeight z‖ ≤ 3240 / (1 + T) ^ 2 := by
        simpa [him, ht] using norm_mellinWeight_le (s := z)
          (by rw [hre]; exact hσ.trans hu.1) (by rw [hre]; exact hu.2)
      have hF : ‖smoothedIntegrand L x z‖ ≤ B / (1 + T) := by
        calc
          _ ≤ (((A + 3 * D) * (1 + T)) * x ^ 2) * (3240 / (1 + T) ^ 2) := by
            simp only [smoothedIntegrand, norm_mul]
            exact mul_le_mul (mul_le_mul hLe hxpow (norm_nonneg _) (by positivity)) hW
              (norm_nonneg _) (by positivity)
          _ = _ := by dsimp [B]; field_simp
      have hPole := norm_simplePoleDifference_le (p := 1) (q := 0) hzim
      have himpow : z.im ^ 2 = T ^ 2 := by rw [him, ← ht, sq_abs]
      have hsub : G z = smoothedIntegrand L x z - (x : ℂ) * simplePoleDifference 1 0 z := by
        rw [hG_eq ⟨hz, by simpa using hz1⟩, add_sub_cancel_right]
      have hP : ‖(x : ℂ) * simplePoleDifference 1 0 z‖ ≤ x / T ^ 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hxpos.le, div_eq_mul_inv]
        apply mul_le_mul_of_nonneg_left _ hxpos.le
        simpa [himpow, one_div] using hPole
      calc
        ‖G z‖ ≤ ‖smoothedIntegrand L x z‖ + ‖(x : ℂ) * simplePoleDifference 1 0 z‖ := by
          simpa only [hsub] using norm_sub_le (smoothedIntegrand L x z)
            ((x : ℂ) * simplePoleDifference 1 0 z)
        _ ≤ bound T := add_le_add hF hP
    exact ⟨atHeight T (abs_of_nonneg hTpos.le), atHeight (-T) (by simp [abs_of_nonneg hTpos.le])⟩

private theorem integrable_smoothedPoleCorrection_line {x σ α A D : ℝ}
    (hx : 0 < x) (hσ : 1 / 2 ≤ σ) (hα : α ∈ Icc σ 2) (hα₁ : α ≠ 1)
    (hA : 0 ≤ A) (hD : 0 ≤ D) {L G : ℂ → ℂ}
    (hG_eq : EqOn (smoothedIntegrand L x) (fun z => G z + (x : ℂ) * simplePoleDifference 1 0 z)
      (verticalStrip σ 2 \ {(1 : ℂ)}))
    (hC : Continuous (fun t : ℝ => L ((α : ℂ) + (t : ℂ) * Complex.I)))
    (hsize : ∀ t : ℝ, ‖L ((α : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A + D * Real.log (|t| + 3)) :
    Integrable (fun t : ℝ => G ((α : ℂ) + (t : ℂ) * Complex.I)) := by
  let line (t : ℝ) : ℂ := (α : ℂ) + (t : ℂ) * Complex.I
  have hα₀ : 0 < α := (by norm_num : (0 : ℝ) < 1 / 2).trans_le (hσ.trans hα.1)
  have hF := (vertical_mellin_integral_bound (hσ.trans hα.1) hα.2 hA hD hx hC hsize).1
  have hP := (integrable_simplePoleDifference_line (c := α) hα₁ hα₀.ne').const_mul (x : ℂ)
  have hF' : Integrable (fun t : ℝ => smoothedIntegrand L x (line t)) := hF
  refine (hF'.sub hP).congr (Eventually.of_forall fun t => ?_)
  have hre : (line t).re = α := by simp [line]
  have hz1 : line t ≠ 1 := fun hz => hα₁ (by simpa [hz] using hre.symm)
  have hz : line t ∈ verticalStrip σ 2 \ {(1 : ℂ)} :=
    ⟨by simpa [verticalStrip, hre] using hα, by simpa using hz1⟩
  have h := hG_eq hz
  change smoothedIntegrand L x (line t) - (x : ℂ) * simplePoleDifference 1 0 (line t) = G (line t)
  rw [h, add_sub_cancel_right]

/-- A smoothed Dirichlet estimate from a unit simple pole, a holomorphic remainder,
and logarithmic bounds along the vertical lines and at large heights in the strip. -/
public theorem smoothed_dirichlet_bound_of_log_growth {x σ A D : ℝ}
    (hx : 1 ≤ x) (hσ : 1 / 2 ≤ σ) (hσ₁ : σ < 1) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (a : ℕ → ℂ) {L H : ℂ → ℂ}
    (hsum : Summable (fun n : ℕ => ‖a n‖ * (n + 1 : ℝ) ^ (-(2 : ℝ))))
    (hseries : ∀ t, L (mellinLine t) = ∑' n : ℕ, a n * ((n + 1 : ℝ) : ℂ) ^ (-mellinLine t))
    (hH : DifferentiableOn ℂ H (verticalStrip σ 2))
    (hL : EqOn L (fun z => H z + (z - 1)⁻¹) (verticalStrip σ 2 \ {(1 : ℂ)}))
    (hsize : ∀ z ∈ verticalStrip σ 2, (z.re = σ ∨ z.re = 2 ∨ 1 ≤ |z.im|) →
      ‖L z‖ ≤ A + D * Real.log (|z.im| + 3)) :
    ‖(∑' n : ℕ, a n * (weight ((n + 1 : ℝ) / x) : ℂ)) - (x : ℂ)‖ ≤
      ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ *
      (((A + 4 * D) * 3240 * x ^ σ) * ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ)) := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hσ₂ : σ ≤ 2 := by linarith
  obtain ⟨G, hG, hG_eq⟩ := exists_smoothedPoleCorrection hxpos (by linarith) hσ₁ hH hL
  have hEq : EqOn (smoothedIntegrand L x) (fun z => G z + (x : ℂ) * simplePoleDifference 1 0 z)
      (verticalStrip σ 2 \ {(1 : ℂ)}) := hG_eq
  obtain ⟨bound, hbound, hdecay⟩ := smoothedPoleCorrection_horizontal_decay hx hσ hA hD hEq
    (fun z hz h => hsize z hz (Or.inr (Or.inr h)))
  have hC (α : ℝ) (hα : α ∈ Icc σ 2) (hα₁ : α ≠ 1) :
      Continuous (fun t : ℝ => L ((α : ℂ) + (t : ℂ) * Complex.I)) := by
    let line (t : ℝ) : ℂ := (α : ℂ) + (t : ℂ) * Complex.I
    have hc : Continuous line := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    have hm : MapsTo line univ (verticalStrip σ 2) := by
      intro t _
      simpa [line, verticalStrip] using hα
    have hZ (t : ℝ) : line t ≠ 1 := fun h => hα₁ (by simpa [line] using congrArg Complex.re h)
    have heq : (fun t : ℝ => L (line t)) = fun t => H (line t) + (line t - 1)⁻¹ := by
      funext t
      exact hL ⟨hm (mem_univ t), by simpa using hZ t⟩
    change Continuous (fun t : ℝ => L (line t))
    rw [heq]
    exact (hH.continuousOn.comp_continuous hc (fun t => hm (mem_univ t))).add
      ((hc.sub continuous_const).inv₀ fun t => sub_ne_zero.mpr (hZ t))
  have hlineSize (α : ℝ) (hα : α ∈ Icc σ 2) (he : α = σ ∨ α = 2) (t : ℝ) :
      ‖L ((α : ℂ) + (t : ℂ) * Complex.I)‖ ≤ A + D * Real.log (|t| + 3) := by
    have hp : α = σ ∨ α = 2 ∨ 1 ≤ |t| := he.elim Or.inl (fun h => Or.inr (Or.inl h))
    simpa using hsize ((α : ℂ) + (t : ℂ) * Complex.I) (by simpa [verticalStrip] using hα)
      (by simpa using hp)
  have hleft := hlineSize σ ⟨le_rfl, hσ₂⟩ (Or.inl rfl)
  have hright := hlineSize 2 ⟨hσ₂, le_rfl⟩ (Or.inr rfl)
  have hneq : (2 : ℝ) ≠ 1 := by norm_num
  have hCl := hC σ ⟨le_rfl, hσ₂⟩ hσ₁.ne
  have hCr := hC 2 ⟨hσ₂, le_rfl⟩ hneq
  exact smoothed_dirichlet_bound hxpos hσ hσ₁ hA hD a L G hsum hseries hG hEq
    (integrable_smoothedPoleCorrection_line hxpos hσ ⟨le_rfl, hσ₂⟩ hσ₁.ne hA hD hEq hCl hleft)
    (integrable_smoothedPoleCorrection_line hxpos hσ ⟨hσ₂, le_rfl⟩ hneq hA hD hEq hCr hright)
    hbound hdecay hCl hleft

end Bernoulli
