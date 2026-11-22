module

public import Bernoulli.ZetaGrowthLeftBoundary
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-! Growth inherited by the uncompleted zeta function from its entire completion. -/

open Complex Set
namespace Bernoulli

/-- The reciprocal of the archimedean and discriminant completion factors. -/
@[expose] public noncomputable def dedekindCompletionReciprocal (K : Type)
    [Field K] [NumberField K] (s : ℂ) : ℂ :=
  (((|NumberField.discr K| : ℤ) : ℂ) ^ (-s / 2)) *
    (Gammaℝ s)⁻¹ ^ NumberField.InfinitePlace.nrRealPlaces K *
    (Gammaℂ s)⁻¹ ^ NumberField.InfinitePlace.nrComplexPlaces K

private theorem norm_cpow_le_in_strip {a : ℝ} (ha : 1 ≤ a) {w : ℂ}
    (hw : w.re ≤ 4) : ‖(a : ℂ) ^ w‖ ≤ a ^ 4 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le ha),
    ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le ha
  simpa using hw

/-- Bounds on reciprocal Gamma along bounded real strips control the reciprocal
completion factor with a field-dependent exponential type. -/
public theorem dedekindCompletionReciprocal_growth (K : Type) [Field K] [NumberField K]
    (hGamma : ∀ a b : ℝ, ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, z.re ∈ Icc a b →
      ‖(Gamma z)⁻¹‖ ≤ C * Real.exp (Real.pi * |z.im|)) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 4 →
      ‖dedekindCompletionReciprocal K s‖ ≤ A * Real.exp (B * |s.im|) := by
  obtain ⟨Cr, hCr, hr⟩ := hGamma (-1 / 4) 2
  obtain ⟨Cc, hCc, hc⟩ := hGamma (-1 / 2) 4
  let D : ℝ := ((|NumberField.discr K| : ℤ) : ℝ)
  let r := NumberField.InfinitePlace.nrRealPlaces K
  let c := NumberField.InfinitePlace.nrComplexPlaces K
  let H₁ := Real.pi ^ 4 * Cr
  let H₂ := (2 * Real.pi) ^ 4 * Cc
  have hD : 1 ≤ D := by
    have h := abs_pos.mpr (NumberField.discr_ne_zero K)
    change (1 : ℝ) ≤ ((|NumberField.discr K| : ℤ) : ℝ)
    exact_mod_cast (show (1 : ℤ) ≤ |NumberField.discr K| by omega)
  have hπ : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have h2π : 1 ≤ 2 * Real.pi := by linarith
  refine ⟨D ^ 4 * H₁ ^ r * H₂ ^ c, (r + c : ℝ) * Real.pi, by positivity, by positivity, ?_⟩
  intro s hsl hsu
  have hnormD : ‖(D : ℂ) ^ (-s / 2)‖ ≤ D ^ 4 :=
    norm_cpow_le_in_strip hD (by norm_num [Complex.div_ofNat_re]; linarith)
  have hhr := hr (s / 2) (by constructor <;> norm_num [Complex.div_ofNat_re] <;> linarith)
  have hhc := hc s ⟨hsl, hsu⟩
  have hb₁ : ‖(Gammaℝ s)⁻¹‖ ≤ H₁ * Real.exp (Real.pi * |s.im|) := by
    rw [Gammaℝ_def, mul_inv, norm_mul, ← cpow_neg, neg_div, neg_neg]
    have hb : ‖(Real.pi : ℂ) ^ (s / 2)‖ ≤ Real.pi ^ 4 :=
      norm_cpow_le_in_strip hπ (by norm_num [Complex.div_ofNat_re]; linarith)
    have hr' : ‖(Gamma (s / 2))⁻¹‖ ≤ Cr * Real.exp (Real.pi * |s.im|) := by
      refine hhr.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCr.le)
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      rw [Complex.div_ofNat_im, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      linarith [abs_nonneg s.im]
    exact (mul_le_mul hb hr' (norm_nonneg _) (by positivity)).trans_eq (by dsimp [H₁]; ring)
  have hb₂ : ‖(Gammaℂ s)⁻¹‖ ≤ H₂ * Real.exp (Real.pi * |s.im|) := by
    rw [Gammaℂ_def, mul_inv, mul_inv, norm_mul, norm_mul, ← cpow_neg, neg_neg,
      show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; rfl]
    have hb := norm_cpow_le_in_strip h2π hsu
    have htwo : ‖(2 : ℂ)⁻¹‖ ≤ 1 := by norm_num
    refine (mul_le_mul (mul_le_mul htwo hb (norm_nonneg _) (by norm_num)) hhc
      (norm_nonneg _) (by positivity)).trans_eq ?_
    dsimp [H₂]
    ring
  change ‖(D : ℂ) ^ (-s / 2) * (Gammaℝ s)⁻¹ ^ r * (Gammaℂ s)⁻¹ ^ c‖ ≤ _
  rw [norm_mul, norm_mul, norm_pow, norm_pow]
  refine (mul_le_mul (mul_le_mul hnormD (pow_le_pow_left₀ (norm_nonneg _) hb₁ r)
    (by positivity) (by positivity)) (pow_le_pow_left₀ (norm_nonneg _) hb₂ c)
    (by positivity) (by positivity)).trans_eq ?_
  rw [mul_pow H₁ _ r, mul_pow H₂ _ c, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
  rw [show ((r : ℝ) + c) * Real.pi * |s.im| =
    (r : ℝ) * (Real.pi * |s.im|) + (c : ℝ) * (Real.pi * |s.im|) by ring, Real.exp_add]
  ring

/-- An order-two bound for the completed function controls the regularized
Dedekind zeta function throughout the fixed open strip. -/
public theorem regularized_growth_of_poleCleared {Z E q : ℂ → ℂ}
    (hZ : Continuous Z) (hquot : ∀ s : ℂ, 1 ≤ |s.im| → Z s = q s / s * E s)
    {A B C : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hq : ∀ s : ℂ, -1 / 2 ≤ s.re → s.re ≤ 4 → ‖q s‖ ≤ A * Real.exp (B * |s.im|))
    (hE : ∀ s : ℂ, ‖E s‖ ≤ C * Real.exp (‖s‖ ^ (2 : ℝ))) :
    ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, -1 / 2 < s.re → s.re < 4 → ‖Z s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2) := by
  obtain ⟨D, hD⟩ := ((isCompact_closedBall (0 : ℂ) 5).image (continuous_norm.comp hZ)).bddAbove
  let M := max (A * max C 0) (max D 0)
  refine ⟨M, B + 16, le_trans (le_max_right _ _) (le_max_right _ _), by linarith, ?_⟩
  intro s hsl hsu
  have hre : |s.re| ≤ 4 := abs_le.mpr ⟨by linarith, hsu.le⟩
  have hnorm : ‖s‖ ≤ 4 + |s.im| :=
    (Complex.norm_le_abs_re_add_abs_im s).trans (add_le_add hre le_rfl)
  by_cases hs : 1 ≤ |s.im|
  · have hsnorm : 1 ≤ ‖s‖ := hs.trans (Complex.abs_im_le_norm s)
    have hqt := (div_le_self (norm_nonneg (q s)) hsnorm).trans (hq s hsl.le hsu.le)
    have het : ‖E s‖ ≤ max C 0 * Real.exp (‖s‖ ^ 2) := by
      refine (hE s).trans ?_
      rw [Real.rpow_two]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_nonneg _)
    have him : |s.im| ≤ (1 + |s.im|) ^ 2 := by
      nlinarith [abs_nonneg s.im, sq_nonneg |s.im|]
    have hsq : ‖s‖ ^ 2 ≤ 16 * (1 + |s.im|) ^ 2 := by
      have h := pow_le_pow_left₀ (norm_nonneg s) (show ‖s‖ ≤ 4 * (1 + |s.im|) by
        linarith [abs_nonneg s.im]) 2
      nlinarith only [h]
    rw [hquot s hs, norm_mul, norm_div]
    calc
      _ ≤ (A * Real.exp (B * |s.im|)) * (max C 0 * Real.exp (‖s‖ ^ 2)) :=
        mul_le_mul hqt het (norm_nonneg _) (by positivity)
      _ = (A * max C 0) * Real.exp (B * |s.im| + ‖s‖ ^ 2) := by rw [Real.exp_add]; ring
      _ ≤ M * Real.exp ((B + 16) * (1 + |s.im|) ^ 2) := by
        refine mul_le_mul (le_max_left _ _) (Real.exp_le_exp.mpr ?_) (Real.exp_nonneg _) (by positivity)
        nlinarith only [mul_le_mul_of_nonneg_left him hB, hsq]
  · have hmem : s ∈ Metric.closedBall (0 : ℂ) 5 := by
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith [lt_of_not_ge hs]
    have hb : ‖Z s‖ ≤ D := hD (mem_image_of_mem _ hmem)
    exact (hb.trans ((le_max_left _ _).trans (le_max_right _ _))).trans
      (le_mul_of_one_le_right (by positivity : 0 ≤ M) (Real.one_le_exp (by positivity)))

end Bernoulli
