module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Tactic

/-! The class number formula identifies the value of the pole-cleared zeta at one. -/

open Filter Set
open scoped Topology
namespace Bernoulli

/-- A continuous regularization has at one the positive Dedekind zeta residue. -/
public theorem dedekind_regularization_at_one (K : Type) [Field K] [NumberField K]
    {ζ Z : ℂ → ℂ} (hZ : ContinuousAt Z 1)
    (hZ_eq : ∀ s : ℂ, s ≠ 1 → Z s = (s - 1) * ζ s)
    (hζ : ∀ s : ℂ, 1 < s.re → ζ s = NumberField.dedekindZeta K s) :
    Z 1 = NumberField.dedekindZeta_residue K := by
  have hcont : Tendsto (fun s : ℝ => Z s) (𝓝[>] 1) (𝓝 (Z 1)) := by
    have hreal : ContinuousAt (fun s : ℝ => Z (s : ℂ)) 1 :=
      (show ContinuousAt Z ((1 : ℝ) : ℂ) by simpa using hZ).comp
        Complex.continuous_ofReal.continuousAt
    exact hreal.continuousWithinAt.tendsto
  have hlimit := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hEq : (fun s : ℝ => (s - 1) * NumberField.dedekindZeta K s) =ᶠ[𝓝[>] 1]
      (fun s : ℝ => Z s) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : 1 < s := hs
    have hsr : 1 < (s : ℂ).re := by simpa using hs'
    have hne : (s : ℂ) ≠ 1 := by
      rintro h
      simp [h] at hsr
    rw [hZ_eq _ hne, hζ _ hsr]
  exact tendsto_nhds_unique hcont (hlimit.congr' hEq)

/-- Nonvanishing off the pole extends to the pole-cleared function on the whole region. -/
public theorem dedekind_regularization_ne_zero (K : Type) [Field K] [NumberField K]
    {ζ Z : ℂ → ℂ} (hZ : ContinuousAt Z 1)
    (hZ_eq : ∀ s : ℂ, s ≠ 1 → Z s = (s - 1) * ζ s)
    (hζ : ∀ s : ℂ, 1 < s.re → ζ s = NumberField.dedekindZeta K s)
    (hnz : ∀ s : ℂ, 31 / 32 < s.re → s ≠ 1 → ζ s ≠ 0)
    {s : ℂ} (hs : 31 / 32 < s.re) :
    Z s ≠ 0 := by
  by_cases h : s = 1
  · rw [h, dedekind_regularization_at_one K hZ hZ_eq hζ]
    exact Complex.ofReal_ne_zero.mpr (NumberField.dedekindZeta_residue_ne_zero K)
  · rw [hZ_eq _ h]
    exact mul_ne_zero (sub_ne_zero.mpr h) (hnz s hs h)

end Bernoulli
