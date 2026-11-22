module

public import Bernoulli.ZetaEulerBounds
public import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-! Differentiation of the logarithm of the prime-ideal Euler product. -/

open Complex IsDedekindDomain NumberField
open scoped Topology
namespace Bernoulli

variable (K : Type*) [Field K] [NumberField K]

/-- The Euler factor monomial formed from the norm of a nonzero prime ideal. -/
@[expose] public noncomputable def primeIdealNormPower (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) : ℂ :=
  (P.asIdeal.absNorm : ℂ) ^ (-s)

local notation "normPower" => primeIdealNormPower

private theorem norm_normPower (P : HeightOneSpectrum (𝓞 K)) (s : ℂ) :
    ‖normPower K P s‖ = (P.asIdeal.absNorm : ℝ) ^ (-s.re) := by
  have hp : 1 < (P.asIdeal.absNorm : ℝ) := by exact_mod_cast one_lt_absNorm_heightOne K P
  unfold primeIdealNormPower
  rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hp),
    Complex.neg_re]

private theorem norm_normPower_le_half (P : HeightOneSpectrum (𝓞 K)) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖normPower K P s‖ ≤ 1 / 2 := by
  have hp : (2 : ℝ) ≤ P.asIdeal.absNorm := by exact_mod_cast one_lt_absNorm_heightOne K P
  rw [norm_normPower]
  refine (Real.rpow_le_rpow_of_exponent_le (by linarith) (show -s.re ≤ -1 by linarith)).trans ?_
  rw [Real.rpow_neg_one, one_div]
  exact inv_anti₀ (by norm_num) hp

private theorem one_sub_normPower_mem_slitPlane (P : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hs : 1 ≤ s.re) : 1 - normPower K P s ∈ slitPlane := by
  have h : ‖-normPower K P s‖ < 1 := by
    rw [norm_neg]
    exact (norm_normPower_le_half K P hs).trans_lt (by norm_num)
  simpa only [sub_eq_add_neg] using mem_slitPlane_of_norm_lt_one h

/-- The negative logarithmic derivative of an individual Euler factor. -/
@[expose] public noncomputable def primeIdealLogEulerTerm (P : HeightOneSpectrum (𝓞 K))
    (s : ℂ) : ℂ :=
  (Real.log P.asIdeal.absNorm : ℂ) * primeIdealNormPower K P s / (1 - primeIdealNormPower K P s)

private theorem hasDerivAt_log_eulerFactor (P : HeightOneSpectrum (𝓞 K)) {s : ℂ}
    (hs : 1 ≤ s.re) :
    HasDerivAt (fun z => -log (1 - normPower K P z)) (-primeIdealLogEulerTerm K P s) s := by
  have hp : 1 < (P.asIdeal.absNorm : ℝ) := by exact_mod_cast one_lt_absNorm_heightOne K P
  have hpne : (P.asIdeal.absNorm : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_natCast]
    exact Complex.ofReal_ne_zero.mpr (zero_lt_one.trans hp).ne'
  have hPow := ((hasDerivAt_id s).neg.const_cpow (c := (P.asIdeal.absNorm : ℂ)) (Or.inl hpne))
  have hSub := (hasDerivAt_const s (1 : ℂ)).sub hPow
  have hLog := ((Complex.hasDerivAt_log (one_sub_normPower_mem_slitPlane K P hs)).comp s hSub).neg
  convert hLog using 1
  · rfl
  · unfold primeIdealLogEulerTerm primeIdealNormPower
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (zero_le_one.trans hp.le)]
    simp only [Pi.neg_apply, id_eq, zero_sub, div_eq_mul_inv]
    ring

private theorem summable_log_norm_mul_norm_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun P : HeightOneSpectrum (𝓞 K) =>
      2 * Real.log P.asIdeal.absNorm * (P.asIdeal.absNorm : ℝ) ^ (-σ)) := by
  let ε : ℝ := (σ - 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hs : 1 < σ - ε := by dsimp [ε]; linarith
  refine (((primeNormSum_le K hs).1).mul_left (2 / ε)).of_nonneg_of_le ?_ ?_
  · intro P
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.log_natCast_nonneg _)) (by positivity)
  · intro P
    have hp : (0 : ℝ) < P.asIdeal.absNorm := by
      exact_mod_cast zero_lt_one.trans (one_lt_absNorm_heightOne K P)
    calc
      _ ≤ 2 * ((P.asIdeal.absNorm : ℝ) ^ ε / ε) * (P.asIdeal.absNorm : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (Real.log_le_rpow_div hp.le hε) (by norm_num)) (by positivity)
      _ = _ := by
        rw [show -(σ - ε) = ε + -σ by ring, Real.rpow_add hp]
        ring

private theorem norm_primeIdealLogEulerTerm_le (P : HeightOneSpectrum (𝓞 K)) {s : ℂ} {σ : ℝ}
    (hσ : 1 ≤ σ) (hs : σ ≤ s.re) :
    ‖primeIdealLogEulerTerm K P s‖ ≤
      2 * Real.log P.asIdeal.absNorm * (P.asIdeal.absNorm : ℝ) ^ (-σ) := by
  have hp : 1 ≤ (P.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (one_lt_absNorm_heightOne K P).le
  have hlow : 1 / 2 ≤ ‖1 - normPower K P s‖ := by
    have h := norm_sub_norm_le (1 : ℂ) (normPower K P s)
    rw [norm_one] at h
    linarith [norm_normPower_le_half K P (hσ.trans hs)]
  have hinv : ‖1 - normPower K P s‖⁻¹ ≤ 2 := by
    have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) hlow
    norm_num at h
    exact h
  have hm : ‖normPower K P s‖ ≤ (P.asIdeal.absNorm : ℝ) ^ (-σ) := by
    rw [norm_normPower]
    exact Real.rpow_le_rpow_of_exponent_le hp (neg_le_neg hs)
  have hlog := Real.log_nonneg hp
  rw [primeIdealLogEulerTerm, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  calc
    _ ≤ (Real.log P.asIdeal.absNorm * (P.asIdeal.absNorm : ℝ) ^ (-σ)) * 2 := by
      rw [div_eq_mul_inv]
      exact mul_le_mul (mul_le_mul_of_nonneg_left hm hlog) hinv (by positivity) (by positivity)
    _ = _ := by ring

/-- The Dirichlet series of logarithmic Euler terms is absolutely convergent on the right. -/
public theorem summable_norm_primeIdealLogEulerTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (fun P : HeightOneSpectrum (𝓞 K) => ‖primeIdealLogEulerTerm K P s‖) :=
  (summable_log_norm_mul_norm_rpow K hs).of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun P => norm_primeIdealLogEulerTerm_le K P hs.le le_rfl)

/-- The geometric series expands one prime-ideal Euler term into its positive powers. -/
public theorem hasSum_primeIdealLogEulerTerm {s : ℂ} (hs : 1 < s.re)
    (P : HeightOneSpectrum (𝓞 K)) :
    HasSum (fun k : ℕ => (Real.log P.asIdeal.absNorm : ℂ) * primeIdealNormPower K P s ^ (k + 1))
      (primeIdealLogEulerTerm K P s) := by
  let r := normPower K P s
  have hr : ‖r‖ < 1 := (norm_normPower_le_half K P hs.le).trans_lt (by norm_num)
  have hg := summable_geometric_of_norm_lt_one hr
  have hgs := (summable_nat_add_iff 1).mpr hg
  have heq : (∑' k : ℕ, (Real.log P.asIdeal.absNorm : ℂ) * r ^ (k + 1)) =
      primeIdealLogEulerTerm K P s := by
    rw [hgs.tsum_mul_left, ← geom_series_mul_shift r hr, tsum_geometric_of_norm_lt_one hr,
      primeIdealLogEulerTerm, div_eq_mul_inv, mul_assoc]
  exact heq ▸ (hgs.mul_left _).hasSum

/-- The series over all prime ideals and their positive powers is absolutely convergent. -/
public theorem summable_norm_primeIdealLogEulerSeries {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : HeightOneSpectrum (𝓞 K) × ℕ =>
      ‖(Real.log u.1.asIdeal.absNorm : ℂ) * primeIdealNormPower K u.1 s ^ (u.2 + 1)‖) := by
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  constructor
  · intro P
    let a := ‖normPower K P s‖
    have hhalf : a ≤ 1 / 2 := norm_normPower_le_half K P hs.le
    have ha : ‖a‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; linarith
    have hg : Summable (fun k : ℕ => a ^ (k + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_norm_lt_one ha)
    simpa only [norm_mul, Complex.norm_real, norm_pow] using
      (hg.mul_left ‖Real.log P.asIdeal.absNorm‖)
  · apply (summable_log_norm_mul_norm_rpow K hs).of_nonneg_of_le
    · intro P
      exact tsum_nonneg fun _ => norm_nonneg _
    · intro P
      let a := ‖normPower K P s‖
      have hhalf : a ≤ 1 / 2 := norm_normPower_le_half K P hs.le
      have ha : ‖a‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; linarith
      have hlog : 0 ≤ Real.log P.asIdeal.absNorm := Real.log_natCast_nonneg _
      have hinv : (1 - a)⁻¹ ≤ 2 := by
        have h := inv_anti₀ (by norm_num : (0 : ℝ) < 1 / 2) (show 1 / 2 ≤ 1 - a by linarith)
        norm_num at h
        exact h
      simp_rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog, norm_pow]
      change (∑' k : ℕ, Real.log P.asIdeal.absNorm * a ^ (k + 1)) ≤ _
      rw [tsum_mul_left, ← geom_series_mul_shift a ha, tsum_geometric_of_norm_lt_one ha]
      calc
        _ ≤ Real.log P.asIdeal.absNorm * (a * 2) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hinv (norm_nonneg _)) hlog
        _ = _ := by dsimp [a]; rw [norm_normPower]; ring

private theorem summable_log_term {s : ℂ} (hs : 1 < s.re) :
    Summable (fun P : HeightOneSpectrum (𝓞 K) => -log (1 - normPower K P s)) := by
  have hnorm : Summable (fun P : HeightOneSpectrum (𝓞 K) => ‖normPower K P s‖) := by
    simpa only [norm_normPower] using (primeNormSum_le K hs).1
  have h := Complex.summable_log_one_add_of_summable hnorm.of_norm.neg
  simpa only [sub_eq_add_neg] using h.neg

/-- The negative logarithmic derivative of the Dedekind zeta function is the
sum of the prime-ideal logarithmic Euler terms on the absolute-convergence half-plane. -/
public theorem neg_logDeriv_dedekindZeta_eq_tsum_primeIdeal {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (dedekindZeta K) s =
      ∑' P : HeightOneSpectrum (𝓞 K), primeIdealLogEulerTerm K P s := by
  let σ : ℝ := (1 + s.re) / 2
  have hσ₀ : 1 < σ := by dsimp [σ]; linarith
  have hσ₁ : σ < s.re := by dsimp [σ]; linarith
  let U := {w : ℂ | σ < w.re}
  have hopen : IsOpen U := isOpen_lt continuous_const continuous_re
  let F (w : ℂ) := ∑' P : HeightOneSpectrum (𝓞 K), -log (1 - normPower K P w)
  have hDeriv : HasDerivAt F (∑' P : HeightOneSpectrum (𝓞 K), -primeIdealLogEulerTerm K P s) s :=
    hasDerivAt_tsum_of_isPreconnected (summable_log_norm_mul_norm_rpow K hσ₀) hopen
      (convex_halfSpace_re_gt σ).isPreconnected
      (fun P w (hw : σ < w.re) => hasDerivAt_log_eulerFactor K P (hσ₀.le.trans hw.le))
      (fun P w (hw : σ < w.re) => by
        rw [norm_neg]
        exact norm_primeIdealLogEulerTerm_le K P hσ₀.le hw.le)
      hσ₁ (summable_log_term K hs) hσ₁
  have hprod (w : ℂ) (hw : 1 < w.re) : exp (F w) = dedekindZeta K w := by
    have hf : HasProd (dedekindEulerFactor K w) (exp (F w)) := by
      refine (summable_log_term K hw).hasSum.cexp.congr_fun fun P => ?_
      change dedekindEulerFactor K w P = exp (-log (1 - normPower K P w))
      rw [Complex.exp_neg, Complex.exp_log
        (slitPlane_ne_zero (one_sub_normPower_mem_slitPlane K P hw.le))]
      rfl
    exact hf.unique (hasProd_dedekindZeta K hw)
  have hEq : (fun w => exp (F w)) =ᶠ[nhds s] dedekindZeta K := by
    filter_upwards [hopen.mem_nhds (show s ∈ U from hσ₁)] with w hw
    exact hprod w (hσ₀.trans hw)
  have hlog := (logDeriv_congr_nhds hEq).eq_of_nhds
  rw [← hlog, logDeriv_apply, hDeriv.cexp.deriv, mul_comm, mul_div_cancel_right₀ _ (exp_ne_zero _),
    ← tsum_neg]
  simp

end Bernoulli
