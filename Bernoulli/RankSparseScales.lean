module

public import Bernoulli.RankSparseExponential
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! Sparse-vector exclusion at the prime scale used in the irreducibility theorem. -/

namespace Bernoulli

open Filter

/-- The support cutoffs at logarithmic scale satisfy the exponential estimate once
the logarithms of the prime and the dimension satisfy elementary size bounds. -/
public theorem sparse_mulVec_bound_le_exp_of_log {n p : ℕ}
    (hn : 0 < n) (hp : 2 < p) (hlog : 8 ≤ Real.log (p : ℝ))
    (hlogp : 64 * Real.log ((n : ℝ) + 1) ≤ Real.log (p : ℝ))
    (hlogn : 64 * Real.log ((n : ℝ) + 1) ≤ (n : ℝ)) :
    let d := ⌊(n : ℝ) / (16 * Real.log (p : ℝ))⌋₊
    let r := ⌊(n : ℝ) / Real.log (p : ℝ)⌋₊
    (((d : ℝ) + 1) * ((n : ℝ) * p) ^ d) *
      (((r : ℝ) + 1) * (n : ℝ) ^ r * (1 / 2 : ℝ) ^ (n - d - r)) ≤
      Real.exp (-(n : ℝ) / 4) := by
  let L := Real.log (p : ℝ)
  let d := ⌊(n : ℝ) / (16 * L)⌋₊
  let r := ⌊(n : ℝ) / L⌋₊
  change 8 ≤ L at hlog
  change 64 * Real.log ((n : ℝ) + 1) ≤ L at hlogp
  have hL : 0 < L := by linarith
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hdf : (d : ℝ) * (16 * L) ≤ n := by
    exact (le_div_iff₀ (by positivity : 0 < 16 * L)).mp (Nat.floor_le (by positivity))
  have hrf : (r : ℝ) * L ≤ n := by
    exact (le_div_iff₀ hL).mp (Nat.floor_le (by positivity))
  have hdL : (d : ℝ) * L ≤ (n : ℝ) / 16 := by linarith
  have hd8 : 8 * (d : ℝ) ≤ n := by
    linarith [mul_le_mul_of_nonneg_left hlog hd0]
  have hr8 : 8 * (r : ℝ) ≤ n := by
    linarith [mul_le_mul_of_nonneg_left hlog hr0]
  have hrows : 4 * (d + r) ≤ n := by
    exact_mod_cast (show 4 * ((d : ℝ) + (r : ℝ)) ≤ n by linarith)
  have hlogSucc : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log hn' (by linarith)
  have hlogRatio : 64 * Real.log (n : ℝ) ≤ L := by linarith
  have hdl : (d : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ) / 64 := by
    linarith [mul_le_mul_of_nonneg_left hlogRatio hd0]
  have hrl : (r : ℝ) * Real.log (n : ℝ) ≤ (n : ℝ) / 64 := by
    linarith [mul_le_mul_of_nonneg_left hlogRatio hr0]
  have hdl' : Real.log ((d : ℝ) + 1) ≤ (n : ℝ) / 64 :=
    (Real.log_le_log (by positivity) (by linarith : (d : ℝ) + 1 ≤ (n : ℝ) + 1)).trans
      (by linarith)
  have hrl' : Real.log ((r : ℝ) + 1) ≤ (n : ℝ) / 64 :=
    (Real.log_le_log (by positivity) (by linarith : (r : ℝ) + 1 ≤ (n : ℝ) + 1)).trans
      (by linarith)
  apply sparse_mulVec_bound_le_exp hn hp d r hrows
  rw [Real.log_mul hn'.ne' hp'.ne']
  have hlognp : (d : ℝ) * (Real.log (n : ℝ) + Real.log (p : ℝ)) =
      (d : ℝ) * Real.log (n : ℝ) + (d : ℝ) * L := mul_add _ _ _
  rw [hlognp]
  linarith

/-- The explicit sparse-vector bound is exponentially small throughout the
large-prime band and for all blocks of size at least a third of the full matrix. -/
public theorem eventually_sparse_mulVec_bound_le_exp_band {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (n p : ℕ), N ≤ 3 * n → n ≤ N → 2 < p →
        Real.exp (a * (N : ℝ) ^ (1 / 4 : ℝ)) / 2 ≤ (p : ℝ) →
        let d := ⌊(n : ℝ) / (16 * Real.log (p : ℝ))⌋₊
        let r := ⌊(n : ℝ) / Real.log (p : ℝ)⌋₊
        (((d : ℝ) + 1) * ((n : ℝ) * p) ^ d) *
          (((r : ℝ) + 1) * (n : ℝ) ^ r * (1 / 2 : ℝ) ^ (n - d - r)) ≤
          Real.exp (-(n : ℝ) / 4) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hquarter :=
    (isLittleO_log_rpow_atTop (r := 1 / 4) (by norm_num)).def (c := a / 128)
      (by positivity)
  have hlin := Real.isLittleO_log_id_atTop.def (c := 1 / 384) (by norm_num)
  have hscale : Tendsto (fun N : ℕ => (a / 2) * (N : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity)
      ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 4 : ℝ))).comp hcast)
  filter_upwards [eventually_ge_atTop (1 : ℕ), hcast.eventually hquarter, hcast.eventually hlin,
    hscale.eventually (eventually_ge_atTop (65 * Real.log 2 + 8)),
    hcast.eventually (eventually_ge_atTop (384 * Real.log 2))]
    with N hN hq hlin hscale hlarge
  intro n p hNn hnN hp hpLower
  have hn : 0 < n := by omega
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hnN'' : (N : ℝ) ≤ 3 * (n : ℝ) := by exact_mod_cast hNn
  have hquarterNonneg : 0 ≤ (N : ℝ) ^ (1 / 4 : ℝ) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hq' : Real.log (N : ℝ) ≤ (a / 128) * (N : ℝ) ^ (1 / 4 : ℝ) :=
    (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg hquarterNonneg] using hq)
  have hlin' : Real.log (N : ℝ) ≤ (1 / 384 : ℝ) * (N : ℝ) :=
    (le_abs_self _).trans (by
      simpa only [id_eq, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg N : (0 : ℝ) ≤ N)] using hlin)
  have hdim : Real.log ((n : ℝ) + 1) ≤ Real.log (N : ℝ) + Real.log 2 := by
    have h := Real.log_le_log (by positivity : 0 < (n : ℝ) + 1)
      (by linarith : (n : ℝ) + 1 ≤ (N : ℝ) * 2)
    rwa [Real.log_mul (zero_lt_one.trans_le hN').ne' (by norm_num)] at h
  have hprime : a * (N : ℝ) ^ (1 / 4 : ℝ) - Real.log 2 ≤ Real.log (p : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < Real.exp (a * (N : ℝ) ^ (1 / 4 : ℝ)) / 2)
      hpLower
    rwa [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at h
  have hLogTwo : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  exact sparse_mulVec_bound_le_exp_of_log hn hp
    (by nlinarith [mul_nonneg ha.le hquarterNonneg])
    (by nlinarith [mul_nonneg ha.le hquarterNonneg])
    (by linarith)

/-- Sparse-vector exclusion holds throughout the large-prime band, uniformly
over the shift and all principal blocks of size at least a third of the full matrix. -/
public theorem eventually_probability_exists_sparse_mulVec_le_band {a : ℝ} (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop,
      ∀ (n p : ℕ) [Fact p.Prime], N ≤ 3 * n → n ≤ N → 2 < p →
        Real.exp (a * (N : ℝ) ^ (1 / 4 : ℝ)) / 2 ≤ (p : ℝ) → ∀ lam : ZMod p,
        let d := ⌊(n : ℝ) / (16 * Real.log (p : ℝ))⌋₊
        let r := ⌊(n : ℝ) / Real.log (p : ℝ)⌋₊
        probability (fun b : Sample n => ∃ v : Fin n → ZMod p, v ≠ 0 ∧
          (finiteVectorSupport v).card ≤ d ∧
          (finiteVectorSupport ((shiftedSignMatrix b lam).mulVec v)).card ≤ r) ≤
          Real.exp (-(n : ℝ) / 4) := by
  filter_upwards [eventually_sparse_mulVec_bound_le_exp_band ha, eventually_ge_atTop (1 : ℕ)]
    with N hband hN
  intro n p _ hNn hnN hp hpLower lam
  exact (probability_exists_sparse_mulVec_le (show 0 < n by omega) hp lam _ _).trans
    (hband n p hNn hnN hp hpLower)

end Bernoulli
