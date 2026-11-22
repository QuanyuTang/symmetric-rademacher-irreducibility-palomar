module

public import Bernoulli.NumberFieldPrimes
public import Bernoulli.PrimePowers
public import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic

/-! The rational-prime-power coefficients of the Dedekind logarithmic Euler factors. -/

public section

open NumberField

namespace Bernoulli

variable (K : Type*) [Field K] [NumberField K]

/-- The contribution indexed by the prime `p` and the exponent `m`. -/
@[expose] noncomputable def dedekindPrimePowerWeight (p m : ℕ) : ℝ :=
  if hp : p.Prime then
    letI : Fact p.Prime := ⟨hp⟩
    Real.log p * primePowerCoefficient (K := K) p m
  else 0

theorem dedekindPrimePowerWeight_of_prime (p m : ℕ) [Fact p.Prime] :
    dedekindPrimePowerWeight K p m = Real.log p * primePowerCoefficient (K := K) p m := by
  simp [dedekindPrimePowerWeight, (Fact.out : p.Prime)]

/-- Each logarithmic Euler factor has nonnegative coefficients bounded by `log p`
times the field degree. -/
theorem dedekindPrimePowerWeight_bounds {p : ℕ} (hp : p.Prime) (m : ℕ) :
    0 ≤ dedekindPrimePowerWeight K p m ∧
      dedekindPrimePowerWeight K p m ≤ Module.finrank ℚ K * Real.log p := by
  let : Fact p.Prime := ⟨hp⟩
  rw [dedekindPrimePowerWeight_of_prime, mul_comm (Real.log p)]
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  exact ⟨mul_nonneg (Nat.cast_nonneg _) hlog,
    mul_le_mul_of_nonneg_right (by exact_mod_cast primePowerCoefficient_le_finrank (K := K) p m) hlog⟩

/-- The coefficient sequence indexed by rational integers, with support on prime powers. -/
@[expose] noncomputable def dedekindMangoldt (n : ℕ) : ℝ :=
  if IsPrimePow n then dedekindPrimePowerWeight K n.minFac (n.factorization n.minFac) else 0

@[simp] theorem dedekindMangoldt_zero : dedekindMangoldt K 0 = 0 := by
  simp [dedekindMangoldt, not_isPrimePow_zero]

@[simp] theorem dedekindMangoldt_one : dedekindMangoldt K 1 = 0 := by
  simp [dedekindMangoldt, not_isPrimePow_one]

theorem dedekindMangoldt_prime_pow {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    dedekindMangoldt K (p ^ m) = dedekindPrimePowerWeight K p m := by
  simp [dedekindMangoldt, hp.isPrimePow.pow hm, hp.pow_minFac hm, hp.factorization_self]

theorem dedekindMangoldt_bounds (n : ℕ) :
    0 ≤ dedekindMangoldt K n ∧ dedekindMangoldt K n ≤ Module.finrank ℚ K * Real.log n := by
  by_cases hn : IsPrimePow n
  · rw [dedekindMangoldt, ite_eq_left hn]
    have hp := Nat.minFac_prime hn.ne_one
    have h := dedekindPrimePowerWeight_bounds K hp (n.factorization n.minFac)
    refine ⟨h.1, h.2.trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))⟩
    exact Real.log_le_log (by exact_mod_cast hp.pos)
      (by exact_mod_cast Nat.le_of_dvd hn.pos (Nat.minFac_dvd n))
  · rw [dedekindMangoldt, ite_eq_right hn]
    exact ⟨le_rfl, mul_nonneg (Nat.cast_nonneg _) (Real.log_natCast_nonneg n)⟩

/-- The logarithmic Euler coefficients are absolutely summable against every `n⁻σ`
for `σ > 1`. The index starts at one for Mellin inversion. -/
theorem summable_dedekindMangoldt_mul_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => dedekindMangoldt K (n + 1) * (n + 1 : ℝ) ^ (-σ)) := by
  let ε : ℝ := (σ - 1) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (ε - σ)) :=
    Real.summable_nat_rpow.mpr (by dsimp [ε]; linarith)
  have hshift : Summable (fun n : ℕ => (n + 1 : ℝ) ^ (ε - σ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff 1).mpr hsum
  refine ((hshift.mul_left ((Module.finrank ℚ K : ℝ) / ε))).of_nonneg_of_le ?_ ?_
  · intro n
    exact mul_nonneg (dedekindMangoldt_bounds K (n + 1)).1 (by positivity)
  · intro n
    have hn : 0 < (n + 1 : ℝ) := by positivity
    calc
      _ ≤ (Module.finrank ℚ K : ℝ) * Real.log (n + 1) * (n + 1 : ℝ) ^ (-σ) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [Nat.cast_add, Nat.cast_one] using (dedekindMangoldt_bounds K (n + 1)).2
      _ ≤ (Module.finrank ℚ K : ℝ) * ((n + 1 : ℝ) ^ ε / ε) * (n + 1 : ℝ) ^ (-σ) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hn.le hε) (Nat.cast_nonneg _))
          (by positivity)
      _ = _ := by
        rw [show ε - σ = ε + -σ by ring, Real.rpow_add hn]
        ring

theorem summable_norm_dedekindMangoldt_mul_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ‖(dedekindMangoldt K (n + 1) : ℂ)‖ * (n + 1 : ℝ) ^ (-σ)) := by
  refine (summable_dedekindMangoldt_mul_rpow K hσ).congr fun n => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (dedekindMangoldt_bounds K (n + 1)).1]

/-- The prime-power remainder specialized to the Dedekind logarithmic Euler coefficients. -/
theorem dedekindPrimePowerSum_bounds {x : ℝ} (hx : 1 ≤ x) :
    0 ≤ primePowerSum x (dedekindPrimePowerWeight K) ∧
      primePowerSum x (dedekindPrimePowerWeight K) ≤
        3 * Module.finrank ℚ K * Real.sqrt x * Real.log x :=
  primePowerSum_bounds hx (Nat.cast_nonneg _) fun _ hp m _ => dedekindPrimePowerWeight_bounds K hp m

end Bernoulli
