module

public import Bernoulli.HalaszLevelSets
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Integrating the character-energy levels

The frequency zero contributes exactly one to the unnormalized Fourier sum.
For the other frequencies, the square-root growth estimate is integrated
against the exponential kernel up to the reference energy.
-/

open scoped BigOperators
open MeasureTheory Set
namespace Bernoulli

/-- A proper reference level bounds the sum of exponentially weighted energies
in terms of the size of that level and the exponential tail. -/
public theorem sum_exp_characterEnergy_le {ι : Type*} [Fintype ι] {p : ℕ} [NeZero p]
    (v : ι → ZMod p) (hp : p.Prime) {M : ℝ} (hM : 0 < M)
    (hproper : (characterEnergyLevel v (8 * M)).card < p) :
    (∑ r, Real.exp (-characterEnergy v r / 8)) ≤
      1 + 4 * ((characterEnergyLevel v (8 * M)).card : ℝ) / Real.sqrt M +
        (p : ℝ) * Real.exp (-M) := by
  classical
  let s := (Finset.univ : Finset (ZMod p)).erase 0
  let f (r : ZMod p) := (Ioi (characterEnergy v r / 8)).indicator (fun t => Real.exp (-t))
  let F (t : ℝ) := ∑ r ∈ s, f r t
  let A := 2 * ((characterEnergyLevel v (8 * M)).card : ℝ) / Real.sqrt M
  have hf (r : ZMod p) : IntegrableOn (f r) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).indicator measurableSet_Ioi
  have hF : IntegrableOn F (Ioi 0) := integrable_finsetSum _ fun r _ => hf r
  have hi (r : ZMod p) :
      (∫ t in Ioi 0, f r t) = Real.exp (-characterEnergy v r / 8) := by
    have he : 0 ≤ characterEnergy v r / 8 := by positivity [characterEnergy_nonneg v r]
    simp only [f, setIntegral_indicator measurableSet_Ioi,
      inter_eq_right.mpr (Ioi_subset_Ioi he), integral_exp_neg_Ioi, neg_div]
  have hsum :
      (∑ r, Real.exp (-characterEnergy v r / 8)) = 1 + ∫ t in Ioi 0, F t := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod p)),
      characterEnergy_zero, neg_zero, zero_div, Real.exp_zero, add_comm]
    unfold F
    rw [integral_finsetSum s (fun r _ => hf r)]
    simp only [s, hi]
  have hsum_filter (t : ℝ) :
      F t = ((s.filter fun r => characterEnergy v r / 8 < t).card : ℝ) * Real.exp (-t) := by
    simp only [F, f, indicator, mem_Ioi, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hsmall (t : ℝ) (ht : t ∈ Ioc 0 M) :
      F t ≤ A * Real.exp ((-1 / 2 : ℝ) * t) := by
    have hsub : (s.filter fun r => characterEnergy v r / 8 < t) ⊆
        (characterEnergyLevel v (8 * t)).erase 0 := by
      intro r hr
      obtain ⟨hr, hrt⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hr).1,
        mem_characterEnergyLevel.mpr (by linarith)⟩
    have hcard : ((s.filter fun r => characterEnergy v r / 8 < t).card : ℝ) ≤
        2 * ((characterEnergyLevel v (8 * M)).card : ℝ) *
          (Real.sqrt (8 * t) / Real.sqrt (8 * M)) :=
      (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
        (card_erase_characterEnergyLevel_le v hp (by linarith [ht.1])
          (by linarith [ht.2]) hproper)
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8),
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8),
      mul_div_mul_left _ _ (by positivity : Real.sqrt 8 ≠ 0)] at hcard
    have hroot : Real.sqrt t ≤ Real.exp ((1 / 2 : ℝ) * t) := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨Real.exp_nonneg _, ?_⟩
      rw [pow_two, ← Real.exp_add, show (1 / 2 : ℝ) * t + 1 / 2 * t = t by ring]
      linarith [Real.add_one_le_exp t]
    rw [hsum_filter]
    calc
      _ ≤ (A * Real.sqrt t) * Real.exp (-t) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
        exact hcard.trans_eq (by dsimp [A]; ring)
      _ ≤ (A * Real.exp ((1 / 2 : ℝ) * t)) * Real.exp (-t) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by positivity [A]))
          (Real.exp_nonneg _)
      _ = _ := by rw [mul_assoc, ← Real.exp_add]; congr 2; ring
  have hlarge (t : ℝ) : F t ≤ (p : ℝ) * Real.exp (-t) := by
    rw [hsum_filter]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_nonneg _)
    simpa only [ZMod.card] using
      (Nat.cast_le.mpr (Finset.card_le_univ _) :
        ((s.filter fun r => characterEnergy v r / 8 < t).card : ℝ) ≤ Fintype.card (ZMod p))
  have hexp : IntegrableOn (fun t : ℝ => A * Real.exp ((-1 / 2 : ℝ) * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) 0).const_mul A
  have hleft : (∫ t in Ioc 0 M, F t) ≤ 2 * A := by
    calc
      _ ≤ ∫ t in Ioc 0 M, A * Real.exp ((-1 / 2 : ℝ) * t) :=
        setIntegral_mono_on (hF.mono_set Ioc_subset_Ioi_self)
          (hexp.mono_set Ioc_subset_Ioi_self) measurableSet_Ioc hsmall
      _ ≤ ∫ t in Ioi 0, A * Real.exp ((-1 / 2 : ℝ) * t) :=
        setIntegral_mono_set hexp (Filter.Eventually.of_forall fun _ => by positivity [A])
          Ioc_subset_Ioi_self.eventuallySubset
      _ = _ := by
        rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0)]
        ring_nf
        simp
  have hright : (∫ t in Ioi M, F t) ≤ (p : ℝ) * Real.exp (-M) := by
    calc
      _ ≤ ∫ t in Ioi M, (p : ℝ) * Real.exp (-t) :=
        setIntegral_mono_on (hF.mono_set (Ioi_subset_Ioi hM.le))
          ((integrableOn_exp_neg_Ioi M).const_mul _) measurableSet_Ioi (fun t _ => hlarge t)
      _ = _ := by rw [integral_const_mul, integral_exp_neg_Ioi]
  rw [hsum, ← Ioc_union_Ioi_eq_Ioi hM.le, setIntegral_union Ioc_disjoint_Ioi_same
    measurableSet_Ioi (hF.mono_set Ioc_subset_Ioi_self) (hF.mono_set (Ioi_subset_Ioi hM.le))]
  calc
    _ ≤ 1 + (2 * A + (p : ℝ) * Real.exp (-M)) :=
      add_le_add le_rfl (add_le_add hleft hright)
    _ = _ := by dsimp [A]; ring

end Bernoulli
