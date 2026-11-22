module

public import Bernoulli.ZetaUniformAnalytic
public import Bernoulli.ZetaWeightedSums
public import Bernoulli.ZetaDirichletSeries
import Mathlib.Tactic

/-! Mellin inversion converts the logarithmic derivative bound into the uniform prime average. -/

open MeasureTheory Set
namespace Bernoulli

/-- Analytic data for the continuation of the actual Mathlib Dedekind zeta function. -/
public structure DedekindZetaContinuationData (K : Type) [Field K] [NumberField K] where
  zeta : ℂ → ℂ
  regularized : ℂ → ℂ
  entire : Differentiable ℂ regularized
  regularization : ∀ s : ℂ, s ≠ 1 → regularized s = (s - 1) * zeta s
  agrees : ∀ s : ℂ, 1 < s.re → zeta s = NumberField.dedekindZeta K s
  zeroFree : ∀ s : ℂ, 31 / 32 < s.re → s ≠ 1 → zeta s ≠ 0
  functionalEquation : ∀ s : ℂ, s.re = -1 / 2 → dedekindCompletionFactor K s * zeta s =
    dedekindCompletionFactor K (1 - s) * zeta (1 - s)
  growth : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
    ∀ s : ℂ, -1 / 2 < s.re → s.re < 4 → ‖regularized s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2)

private theorem rpow_shift_div_x {x : ℝ} (hx : 0 < x) :
    x ^ zetaShiftLine / x = x ^ (-(1 / 64) : ℝ) := by
  calc
    _ = x ^ zetaShiftLine / x ^ (1 : ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [← Real.rpow_sub hx]; congr 1; norm_num [zetaShiftLine]

private theorem sqrt_log_div_x {x : ℝ} (hx : 0 < x) :
    Real.sqrt x * Real.log x / x = x ^ (-(1 / 2) : ℝ) * Real.log x := by
  rw [mul_comm, mul_div_assoc, Real.sqrt_eq_rpow]
  have h : x ^ (1 / 2 : ℝ) / x = x ^ (-(1 / 2) : ℝ) := by
    calc
      _ = x ^ (1 / 2 : ℝ) / x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_sub hx]; congr 1; norm_num
  rw [h, mul_comm]

/-- The canonical continuum data and the absolutely convergent logarithmic series
imply the uniform quantitative prime-ideal estimate. -/
public theorem uniformPrimeIdealEstimate_of_zeta_data
    (hdata : ∀ (K : Type) [Field K] [NumberField K], Nonempty (DedekindZetaContinuationData K))
    (hseries : ∀ (K : Type) [Field K] [NumberField K] (t : ℝ),
      -logDeriv (NumberField.dedekindZeta K) (mellinLine t) =
        ∑' n : ℕ, (dedekindMangoldt K (n + 1) : ℂ) *
          ((n + 1 : ℝ) : ℂ) ^ (-mellinLine t)) :
    UniformPrimeIdealEstimate := by
  obtain ⟨C, hC, hbound⟩ := exists_dedekind_logDeriv_strip_bound
  let I := ∫ t : ℝ, (1 + |t|) ^ (-(3 / 2) : ℝ)
  let B := ‖(((2 * Real.pi : ℝ) : ℂ)⁻¹)‖ * 3240 * I
  have hI : 0 ≤ I := integral_nonneg fun _ => by positivity
  have hB : 0 ≤ B := by positivity
  refine ⟨B * (5 * C) + 3, by positivity, fun K _ _ x hx => ?_⟩
  obtain ⟨z⟩ := hdata K
  let ℓ := Real.log |(NumberField.discr K : ℝ)|
  let d : ℝ := Module.finrank ℚ K
  let A := C * (ℓ + d)
  let D := C * d
  let P := primeIdealAverage K x
  let Q := primePowerSum x (dedekindPrimePowerWeight K)
  have hℓ : 0 ≤ ℓ := by
    apply Real.log_nonneg
    have h := abs_pos.mpr (NumberField.discr_ne_zero K)
    change (1 : ℝ) ≤ |(NumberField.discr K : ℝ)|
    exact_mod_cast (show (1 : ℤ) ≤ |NumberField.discr K| by omega)
  have hd : 0 ≤ d := Nat.cast_nonneg _
  have hA : 0 ≤ A := by positivity
  have hD : 0 ≤ D := by positivity
  have hDA : D ≤ A := by dsimp [D, A]; gcongr; linarith
  have hx₁ : 1 ≤ x := by linarith
  have hx₀ : 0 < x := zero_lt_one.trans_le hx₁
  have hQ := dedekindPrimePowerSum_bounds K hx₁
  obtain ⟨hhol, hLaurent, hL⟩ := hbound K z.zeta z.regularized z.entire z.regularization
    z.agrees z.zeroFree z.functionalEquation z.growth
  have hseries' (t : ℝ) :
      -logDeriv z.zeta (mellinLine t) =
        ∑' n : ℕ, (dedekindMangoldt K (n + 1) : ℂ) *
          ((n + 1 : ℝ) : ℂ) ^ (-mellinLine t) := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    have hEq : z.zeta =ᶠ[nhds (mellinLine t)] NumberField.dedekindZeta K := by
      filter_upwards [hopen.mem_nhds (show 1 < (mellinLine t).re from by simp)] with s hs
      exact z.agrees s hs
    rw [(logDeriv_congr_nhds hEq).eq_of_nhds]
    exact hseries K t
  have hM := smoothed_dirichlet_bound_of_log_growth hx₁ (σ := zetaShiftLine)
    (by norm_num [zetaShiftLine]) (by norm_num [zetaShiftLine]) hA hD
    (fun n => (dedekindMangoldt K (n + 1) : ℂ))
    (summable_norm_dedekindMangoldt_mul_rpow K (by norm_num : (1 : ℝ) < 2))
    hseries' hhol hLaurent hL
  have hreal :
      (∑' n : ℕ, (dedekindMangoldt K (n + 1) : ℂ) * (weight ((n + 1 : ℝ) / x) : ℂ)) =
        ((x * P + Q : ℝ) : ℂ) := by
    simp_rw [← Complex.ofReal_mul, ← Complex.ofReal_tsum]
    rw [tsum_dedekindMangoldt_weight K hx₁]
  rw [hreal, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hM
  have hmain : |x * P + Q - x| ≤ B * (A + 4 * D) * x ^ zetaShiftLine := by
    refine hM.trans_eq ?_
    dsimp [B, I]
    ring
  have htri : x * |P - 1| ≤ B * (A + 4 * D) * x ^ zetaShiftLine + Q := by
    calc
      _ = |x * (P - 1)| := by rw [abs_mul, abs_of_pos hx₀]
      _ = |(x * P + Q - x) + -Q| := by congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hmain (by rw [abs_neg, abs_of_nonneg hQ.1]))
  have hdelta : |P - 1| ≤
      B * (5 * C) * ((ℓ + d) * x ^ (-(1 / 64) : ℝ)) +
        3 * (d * x ^ (-(1 / 2) : ℝ) * Real.log x) := by
    calc
      _ ≤ (B * (A + 4 * D) * x ^ zetaShiftLine + Q) / x :=
        (le_div_iff₀ hx₀).mpr (by simpa only [mul_comm x] using htri)
      _ ≤ (B * (5 * A) * x ^ zetaShiftLine + 3 * d * Real.sqrt x * Real.log x) / x := by
        apply div_le_div_of_nonneg_right _ hx₀.le
        exact add_le_add (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) hB) (by positivity)) hQ.2
      _ = _ := by
        rw [add_div, mul_div_assoc, rpow_shift_div_x hx₀, mul_assoc (3 * d), mul_div_assoc,
          sqrt_log_div_x hx₀]
        dsimp [A]
        ring
  calc
    _ ≤ _ := hdelta
    _ ≤ _ := by
      have h1 : 0 ≤ (ℓ + d) * x ^ (-(1 / 64) : ℝ) := by positivity
      have h2 : 0 ≤ d * x ^ (-(1 / 2) : ℝ) * Real.log x :=
        mul_nonneg (by positivity) (Real.log_nonneg hx₁)
      rw [mul_add]
      refine add_le_add (mul_le_mul_of_nonneg_right (by linarith) h1) ?_
      exact mul_le_mul_of_nonneg_right (by linarith [mul_nonneg hB (by positivity : 0 ≤ 5 * C)]) h2

/-- The uniform prime-ideal estimate follows from the continuation data, using the
logarithmic Euler series for the actual Dedekind zeta function. -/
public theorem uniformPrimeIdealEstimate_of_continuation_data
    (hdata : ∀ (K : Type) [Field K] [NumberField K], Nonempty (DedekindZetaContinuationData K)) :
    UniformPrimeIdealEstimate :=
  uniformPrimeIdealEstimate_of_zeta_data hdata fun K _ _ t =>
    neg_logDeriv_dedekindZeta_eq_tsum K (by simp)

end Bernoulli
