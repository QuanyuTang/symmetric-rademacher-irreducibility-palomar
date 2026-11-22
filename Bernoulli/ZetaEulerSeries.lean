module

public import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic

/-! The absolutely convergent ideal-indexed Dedekind series. -/

public section

open Filter NumberField
open scoped Topology

namespace Bernoulli

variable (K : Type*) [Field K] [NumberField K]

private noncomputable def idealNormCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // I.absNorm = n}

private theorem tendsto_idealNormCount :
    Tendsto (fun n : ℕ => (∑ k ∈ Finset.Icc 1 n, (idealNormCount K k : ℝ)) / n)
      atTop (𝓝 (dedekindZeta_residue K)) := by
  rw [dedekindZeta_residue_def]
  refine ((Ideal.tendsto_norm_le_div_atTop₀ K).comp tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr 1
  norm_cast
  simp only [idealNormCount]
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // I.absNorm = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc n.zero_le,
    ← Finset.card_preimage_eq_sum_card_image_eq
      (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

theorem dedekindLSeriesSummable {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n => (Nat.card {I : Ideal (𝓞 K) // I.absNorm = n} : ℂ)) s := by
  change LSeriesSummable (fun n => (idealNormCount K n : ℂ)) s
  refine LSeriesSummable_of_sum_norm_bigO_and_nonneg ?_ (fun n => by positivity) zero_le_one hs
  exact Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    (by simpa using tendsto_idealNormCount K)

private noncomputable def idealZetaTerm (s : ℂ) (I : Ideal (𝓞 K)) : ℂ :=
  if I.absNorm = 0 then 0 else (I.absNorm : ℂ) ^ (-s)

private theorem summable_norm_idealZetaTerm {s : ℂ} (hs : 1 < s.re) :
    Summable (‖idealZetaTerm K s ·‖) := by
  classical
  let e := Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 K) → ℕ)
  rw [← e.summable_iff]
  refine (summable_sigma_of_nonneg fun _ => norm_nonneg _).mpr ⟨?_, ?_⟩
  · intro n
    let : Fintype {I : Ideal (𝓞 K) // I.absNorm = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).fintype
    exact Summable.of_finite
  · have h := (dedekindLSeriesSummable K hs).norm
    refine h.congr fun n => ?_
    let : Fintype {I : Ideal (𝓞 K) // I.absNorm = n} :=
      (Ideal.finite_setOfPred_absNorm_eq n).fintype
    change _ = ∑' I : {I : Ideal (𝓞 K) // I.absNorm = n}, ‖idealZetaTerm K s I‖
    have hnorm (I : {I : Ideal (𝓞 K) // I.absNorm = n}) :
        ‖idealZetaTerm K s I‖ = ‖(if n = 0 then 0 else (n : ℂ) ^ (-s))‖ := by
      rw [idealZetaTerm, I.2]
    simp_rw [hnorm]
    rw [tsum_const, nsmul_eq_mul]
    by_cases hn : n = 0
    · simp [hn, LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, norm_mul,
        Complex.norm_natCast, ite_eq_right hn]

private theorem hasSum_idealZetaTerm_fiber (s : ℂ) (n : ℕ) :
    HasSum (fun I : {I : Ideal (𝓞 K) // I.absNorm = n} => idealZetaTerm K s I)
      (LSeries.term (fun n => (idealNormCount K n : ℂ)) s n) := by
  classical
  let : Fintype {I : Ideal (𝓞 K) // I.absNorm = n} :=
    (Ideal.finite_setOfPred_absNorm_eq n).fintype
  convert hasSum_fintype (fun x : {I : Ideal (𝓞 K) // I.absNorm = n} => idealZetaTerm K s x) using 1
  have hconst (I : {I : Ideal (𝓞 K) // I.absNorm = n}) :
      idealZetaTerm K s I = if n = 0 then 0 else (n : ℂ) ^ (-s) := by
    simp only [idealZetaTerm, I.2]
  simp_rw [hconst, Finset.sum_const, nsmul_eq_mul]
  by_cases hn : n = 0
  · simp [hn, LSeries.term_zero]
  · rw [LSeries.term_of_ne_zero hn, div_eq_mul_inv, ← Complex.cpow_neg, ite_eq_right hn,
      Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl

private theorem hasSum_idealZetaTerm {s : ℂ} (hs : 1 < s.re) :
    HasSum (idealZetaTerm K s) (NumberField.dedekindZeta K s) := by
  classical
  let e := Equiv.sigmaFiberEquiv (Ideal.absNorm : Ideal (𝓞 K) → ℕ)
  have h := (summable_norm_idealZetaTerm K hs).of_norm.hasSum
  have hgroup := (e.hasSum_iff.mpr h).sigma (hasSum_idealZetaTerm_fiber K s)
  rw [NumberField.dedekindZeta]
  rw [← hgroup.unique (dedekindLSeriesSummable K hs).LSeriesHasSum]
  exact h

/-- The Dedekind series is absolutely convergent when indexed by nonzero integral ideals. -/
theorem summable_norm_dedekindZeta_ideal {s : ℂ} (hs : 1 < s.re) :
    Summable (fun I : {I : Ideal (𝓞 K) // I ≠ 0} => ‖(I.val.absNorm : ℂ) ^ (-s)‖) := by
  refine ((summable_norm_idealZetaTerm K hs).comp_injective Subtype.val_injective).congr fun I => ?_
  have hn := fun h => I.2 (Ideal.absNorm_eq_zero_iff.mp h)
  simp only [Function.comp_apply, idealZetaTerm, ite_eq_right hn]

/-- The sum over nonzero integral ideals is Mathlib's norm-indexed Dedekind zeta function. -/
theorem hasSum_dedekindZeta_ideal {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : {I : Ideal (𝓞 K) // I ≠ 0} => (I.val.absNorm : ℂ) ^ (-s))
      (NumberField.dedekindZeta K s) := by
  have hzero (I : Ideal (𝓞 K))
      (hI : I ∉ Set.range (Subtype.val : {I : Ideal (𝓞 K) // I ≠ 0} → Ideal (𝓞 K))) :
      idealZetaTerm K s I = 0 := by
    have : I = 0 := by simpa using hI
    simp [idealZetaTerm, this]
  refine ((Subtype.val_injective.hasSum_iff hzero).mpr (hasSum_idealZetaTerm K hs)).congr_fun
    fun I => ?_
  have hn := fun h => I.2 (Ideal.absNorm_eq_zero_iff.mp h)
  simp only [Function.comp_apply, idealZetaTerm, ite_eq_right hn]

end Bernoulli
