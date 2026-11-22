module

public import Bernoulli.ZetaGammaGrowth

public import DedekindZetaZeroFree.LFunctions.Dedekind.HolomorphicContinuation
public import DedekindZetaZeroFree.Theta.Inversion.MixedPairGlobalSelfDuality
public import DedekindZetaZeroFree.Theta.Profiles.MixedPairExponentialTails
public import DedekindZetaZeroFree.LFunctions.Hecke.Growth.PoleClearedOrderOne
public import DedekindZetaZeroFree.Analysis.Gamma.ReflectionAndReciprocalStripBounds
public import DedekindZetaZeroFree.HarmonicAnalysis.Mellin.WeakPairPoleClearing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The analytic continuation and functional equation on the left boundary,
assembled from the mixed-signature theta model. -/

open Complex Set
open DedekindZetaZeroFree
open DedekindZetaZeroFree.AbelianQuotient
open DedekindZetaZeroFree.Hecke

namespace Bernoulli

private theorem gamma_factors_left_ne_zero {s : ℂ} (hs : s.re = -1 / 2) :
    Gammaℝ s ≠ 0 ∧ Gammaℂ s ≠ 0 := by
  have hs₀ : s ≠ 0 := by rintro rfl; norm_num at hs
  have hs₁ : s + 1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re, hs] at hre
  have hpos : 0 < (s + 2).re := by norm_num [Complex.add_re, hs]
  constructor
  · intro h
    have hg := Gammaℝ_ne_zero_of_re_pos hpos
    simp [Gammaℝ_add_two hs₀, h] at hg
  · rw [Gammaℂ_def]
    refine mul_ne_zero (mul_ne_zero two_ne_zero (cpow_ne_zero_iff.mpr (Or.inl ?_))) ?_
    · exact mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
    · intro h
      have hg := Gamma_ne_zero_of_re_pos hpos
      rw [show s + 2 = (s + 1) + 1 by ring, Gamma_add_one _ hs₁, Gamma_add_one _ hs₀,
        h, mul_zero, mul_zero] at hg
      exact hg rfl

private theorem zetaGammaFactor_mul_reciprocal_left (K : Type) [Field K] [NumberField K]
    {s : ℂ} (hs : s.re = -1 / 2) : zetaGammaFactor K s * zetaGammaReciprocal K s = 1 := by
  obtain ⟨hr, hc⟩ := gamma_factors_left_ne_zero hs
  let D : ℂ := ((|NumberField.discr K| : ℤ) : ℂ)
  have hD : D ≠ 0 := by simp [D, NumberField.discr_ne_zero K]
  let r := NumberField.InfinitePlace.nrRealPlaces K
  let c := NumberField.InfinitePlace.nrComplexPlaces K
  have hpow : D ^ (s / 2) * D ^ (-s / 2) = 1 := by
    rw [← cpow_add _ _ hD, show s / 2 + -s / 2 = 0 by ring, cpow_zero]
  change D ^ (s / 2) * Gammaℝ s ^ r * Gammaℂ s ^ c *
    (D ^ (-s / 2) * (Gammaℝ s)⁻¹ ^ r * (Gammaℂ s)⁻¹ ^ c) = 1
  calc
    _ = (D ^ (s / 2) * D ^ (-s / 2)) *
        (Gammaℝ s ^ r * (Gammaℝ s)⁻¹ ^ r) * (Gammaℂ s ^ c * (Gammaℂ s)⁻¹ ^ c) := by ring
    _ = 1 := by rw [hpow, ← mul_pow, ← mul_pow, mul_inv_cancel₀ hr, mul_inv_cancel₀ hc]; simp


/-- A canonical meromorphic continuation and its entire regularization, with the functional
equation on the left boundary and preliminary growth through the critical strip. -/
public theorem exists_dedekind_zeta_regularization_functional_equation
    (K : Type) [Field K] [NumberField K] :
    ∃ ζ Z : ℂ → ℂ,
      DifferentiableOn ℂ ζ ({1}ᶜ : Set ℂ) ∧ Differentiable ℂ Z ∧
      (∀ s : ℂ, 1 < s.re → ζ s = NumberField.dedekindZeta K s) ∧
      (∀ s : ℂ, s ≠ 1 → Z s = (s - 1) * ζ s) ∧
      (∀ s : ℂ, s.re = -1 / 2 →
        zetaGammaFactor K s * ζ s = zetaGammaFactor K (1 - s) * ζ (1 - s)) ∧
      (∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
        ∀ s : ℂ, -1 / 2 < s.re → s.re < 4 → ‖Z s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2)) := by
  let P := Theta.mixedThetaPair K
  have hk : P.k = 1 := Theta.mixedThetaPair_k K
  let q := zetaGammaReciprocal K
  have hq : Differentiable ℂ q := zetaGammaReciprocal_differentiable K
  obtain ⟨u, hu, hqu⟩ := entire_division_at_zero q hq (zetaGammaReciprocal_zero K)
  let ζ := fun s : ℂ ↦ q s * P.Λ₀ s - u s * P.f₀ - q s * (P.ε / (1 - s)) * P.g₀
  let Z := fun s : ℂ ↦ (s - 1) * (q s * P.Λ₀ s - u s * P.f₀) + q s * P.ε * P.g₀
  have hζ : DifferentiableOn ℂ ζ ({1}ᶜ : Set ℂ) ∧
      ∀ s : ℂ, s ≠ 0 → s ≠ 1 → ζ s = q s * P.Λ s :=
    weakFE_uncompletion P hk q u hq hu hqu
  have hZ : Differentiable ℂ Z := by
    unfold Z
    have hΛ := P.differentiable_Λ₀
    fun_prop
  have hseries (s : ℂ) (hs : 1 < s.re) :
      P.Λ s = zetaGammaFactor K s * NumberField.dedekindZeta K s :=
    (P.hasMellin (s := s) (by rwa [hk])).2.symm.trans (Theta.hasMellin_mixedThetaPair K hs).2
  have hright (s : ℂ) (hs : 1 < s.re) : ζ s = NumberField.dedekindZeta K s := by
    have hs₀ : s ≠ 0 := by rintro rfl; norm_num at hs
    have hs₁ : s ≠ 1 := by rintro rfl; norm_num at hs
    rw [hζ.2 s hs₀ hs₁, hseries s hs, ← mul_assoc,
      zetaGammaReciprocal_mul_factor K s hs, one_mul]
  have hZE (s : ℂ) (hs : s ≠ 1) : Z s = (s - 1) * ζ s := by
    have hne : 1 - s ≠ 0 := sub_ne_zero.mpr hs.symm
    dsimp [ζ, Z]
    field_simp
    ring
  refine ⟨ζ, Z, hζ.1, hZ, hright, hZE, ?_, ?_⟩
  · intro s hs
    have hs₀ : s ≠ 0 := by rintro rfl; norm_num at hs
    have hs₁ : s ≠ 1 := by rintro rfl; norm_num at hs
    have hright' : 1 < (1 - s).re := by norm_num [Complex.sub_re, hs]
    have hreflect := weakFEPair_selfDual_reflection P hk (mixedThetaPair_global_selfDual K)
      (mixedThetaPair_global_g₀_eq_f₀ K) (mixedThetaPair_global_ε_eq_one K) s hs₀ hs₁
    rw [hζ.2 s hs₀ hs₁, ← mul_assoc, zetaGammaFactor_mul_reciprocal_left K hs, one_mul,
      hright (1 - s) hright', ← hseries (1 - s) hright']
    exact hreflect
  · obtain ⟨A, B, hA, hB, hbound⟩ := dedekindCompletionReciprocal_growth K
      GammaBounds.inverse_Gamma_strip_exp_bound_complex
    obtain ⟨hp, C, D, hC, hD, htail⟩ := mixedThetaPair_exponential_tail K
    obtain ⟨L, hL⟩ := WeakFEPair.orderOneBound_poleClear P hk
      ⟨C, D, 2 / (Module.finrank ℚ K : ℝ), hC.le, hD, hp, htail⟩
      (poleCleared P) (fun s => rfl) 1 (by norm_num)
    have hL' (s : ℂ) : ‖poleCleared P s‖ ≤ L * Real.exp (‖s‖ ^ (2 : ℝ)) := by
      rw [← Real.rpow_eq_pow ‖s‖ 2]
      exact (show (1 + 1 : ℝ) = 2 by norm_num) ▸ hL s
    refine regularized_growth_of_poleCleared (E := poleCleared P) (q := q)
      hZ.continuous ?_ hA hB hbound hL'
    intro s hs
    have hs₀ : s ≠ 0 := by rintro rfl; norm_num at hs
    have hs₁ : s ≠ 1 := by rintro rfl; norm_num at hs
    rw [hZE s hs₁, hζ.2 s hs₀ hs₁, poleCleared_eq P hk s hs₀ hs₁]
    field_simp

end Bernoulli
