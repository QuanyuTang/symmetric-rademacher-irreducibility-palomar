module

public import Bernoulli.RankTransitionStatistic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Corank expectation on a prime band

Resampling the first floor(t / log p) coordinates allows the exponential
health estimates for the leading blocks to be used uniformly across every
step and every diagonal shift.
-/

open scoped BigOperators
namespace Bernoulli

private theorem conditional_mass_le_of_rankFourierHealthy {t p K : ℕ} [Fact p.Prime]
    (hp : 2 < p) (hK : 1 ≤ K) (hlog : 4 ≤ Real.log (p : ℝ))
    (hsize : 2 ≤ (t : ℝ) / Real.log (p : ℝ)) (a : Sample t) (lam : ZMod p)
    (hgood : rankFourierHealthy (shiftedSignMatrix a lam)
      ⌊(t : ℝ) / Real.log (p : ℝ)⌋₊ (t - ⌊(t : ℝ) / Real.log (p : ℝ)⌋₊)
      (Real.exp (-(t : ℝ) / (2 * (K : ℝ))))) :
    (∑ col : Fin (t + 1) → Bool, if
      shiftedSignCorank ((sampleSuccEquiv t).symm (a, col)) lam ≠ shiftedSignCorank a lam - 1
      then fairSignWeight (Fin (t + 1)) else 0) ≤
        (p : ℝ)⁻¹ + 2 * Real.exp (-(t : ℝ) / (8 * (K : ℝ) * Real.log (p : ℝ))) := by
  let x := Real.log (p : ℝ)
  let X := (t : ℝ) / x
  let r := ⌊X⌋₊
  let L := (t : ℝ) / (4 * (K : ℝ) * x)
  let ε := Real.exp (-(t : ℝ) / (2 * (K : ℝ)))
  change 4 ≤ x at hlog
  have hx : 0 < x := by linarith
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : 0 < (K : ℝ) := by linarith
  have hX : 0 ≤ X := by positivity
  have hr_le : (r : ℝ) ≤ X := Nat.floor_le hX
  have hX_le : X ≤ 2 * (r : ℝ) := by
    have h := Nat.lt_floor_add_one X
    change X < (r : ℝ) + 1 at h
    change 2 ≤ X at hsize
    linarith
  have h4r : 4 * r ≤ t := by
    have hcast : 4 * (r : ℝ) ≤ t := by
      calc
        _ ≤ 4 * X := by linarith
        _ ≤ _ := by
          dsimp only [X]
          rw [← mul_div_assoc, div_le_iff₀ hx]
          have h := mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg t)
          nlinarith
    exact_mod_cast hcast
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hL : L ≤ (r : ℝ) * Real.log 2 := by
    calc
      L = X / (4 * (K : ℝ)) := by dsimp [L, X]; rw [div_mul_eq_div_div_swap]
      _ ≤ X / 4 := div_le_div_of_nonneg_left hX (by norm_num) (by linarith)
      _ ≤ (r : ℝ) / 2 := by linarith
      _ ≤ _ := by
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg r)
  have hL' : L ≤ (t : ℝ) / (2 * (K : ℝ)) := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg t) (by positivity)
    have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 4 * (K : ℝ) by positivity)
    nlinarith
  have hε : ε ≤ Real.exp (-L) := by
    apply Real.exp_le_exp.mpr
    simpa only [neg_div] using neg_le_neg hL'
  have hε₁ : ε ≤ 1 := Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg _)) (by positivity))
  let part : Fin r ⊕ Fin (t - r) ≃ Fin t :=
    finSumFinEquiv.trans (finCongr (show r + (t - r) = t by omega))
  have hm : t - r ≤ Fintype.card (Fin (t - r)) := by simp
  have hstep := shiftedSignCorank_exception_mass_le hp a lam part (by simp : Fintype.card (Fin r) ≤ r)
    hm (Real.exp_nonneg _) hε₁ hgood
  refine hstep.trans (add_le_add_right ((sqrt_fairSignWeight_add_le_exp r hL hε).trans_eq ?_) _)
  refine congrArg (fun y => 2 * Real.exp y) ?_
  change -((t : ℝ) / (4 * (K : ℝ) * x)) / 2 = -(t : ℝ) / (8 * (K : ℝ) * x)
  field_simp [hKpos.ne', hx.ne']
  ring

/-- A single exponential health estimate for blocks of sizes between one
third and all of the sample gives the mean eigenspace bound on the band. -/
public theorem expectation_eigenspaceStatistic_le_of_rankFourierHealthy_band
    {N p K : ℕ} [Fact p.Prime] (hp : 2 < p) (hN : 32 ≤ N) (hK : 1 ≤ K)
    (hlog : 4 ≤ Real.log (p : ℝ)) (hsize : 96 * (K : ℝ) ≤ (N : ℝ) / Real.log (p : ℝ))
    (hgood : ∀ (lam : ZMod p) (t : ℕ), (N : ℝ) / 3 ≤ (t : ℝ) → t ≤ N →
      probability (fun a : Sample t => ¬ rankFourierHealthy (shiftedSignMatrix a lam)
        ⌊(t : ℝ) / Real.log (p : ℝ)⌋₊ (t - ⌊(t : ℝ) / Real.log (p : ℝ)⌋₊)
        (Real.exp (-(t : ℝ) / (2 * (K : ℝ))))) ≤ 3 * Real.exp (-(t : ℝ) / 4)) :
    expectation (fun a : Sample N => eigenspaceStatistic a p) ≤
      1 + 4 * ((N : ℝ) ^ 3 / p +
        (N : ℝ) ^ 3 * p * Real.exp (-(N : ℝ) / (48 * (K : ℝ) * Real.log (p : ℝ)))) := by
  let x := Real.log (p : ℝ)
  let L := (N : ℝ) / (48 * (K : ℝ) * x)
  let δ := Real.exp (-L)
  let start := (N + 2) / 3
  let m := N - start - 1
  let good (lam : ZMod p) (t : ℕ) (a : Sample t) :=
    rankFourierHealthy (shiftedSignMatrix a lam) ⌊(t : ℝ) / x⌋₊ (t - ⌊(t : ℝ) / x⌋₊)
      (Real.exp (-(t : ℝ) / (2 * (K : ℝ))))
  change 4 ≤ x at hlog
  change 96 * (K : ℝ) ≤ (N : ℝ) / x at hsize
  have hx : 0 < x := by linarith
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : 0 < (K : ℝ) := by linarith
  have hN' : (32 : ℝ) ≤ N := by exact_mod_cast hN
  have hEq : start + m + 1 = N := by dsimp [start, m]; omega
  have hburn : start + 1 ≤ m := by dsimp [start, m]; omega
  have hL : 1 ≤ L := by
    calc
      _ ≤ ((N : ℝ) / x) / (48 * (K : ℝ)) := by
        rw [le_div_iff₀ (by positivity), one_mul]
        linarith [hsize]
      _ = L := (div_mul_eq_div_div_swap (N : ℝ) (48 * (K : ℝ)) x).symm
  have hLN : L ≤ (N : ℝ) / 48 := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by norm_num)
    have h := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 48 * (K : ℝ) by positivity)
    nlinarith
  have htlo (u : ℕ) : (N : ℝ) / 3 ≤ ((start + u : ℕ) : ℝ) := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
    exact_mod_cast (show N ≤ (start + u) * 3 by dsimp [start]; omega)
  have hthi {u : ℕ} (hu : u < m + 1) : start + u ≤ N := by omega
  have hGood (lam : ZMod p) (u : ℕ) (hu : u < m + 1) :
      probability (fun a : Sample (start + u) => ¬ good lam (start + u) a) ≤ δ := by
    have hsep : L + 2 ≤ ((start + u : ℕ) : ℝ) / 4 := by
      linarith [htlo u]
    have h3 : (3 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
    calc
      _ ≤ 3 * Real.exp (-((start + u : ℕ) : ℝ) / 4) :=
        hgood lam (start + u) (htlo u) (hthi hu)
      _ ≤ Real.exp 2 * Real.exp (-((start + u : ℕ) : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)
      _ = Real.exp (2 - ((start + u : ℕ) : ℝ) / 4) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ δ := Real.exp_le_exp.mpr (by linarith)
  have hCond (lam : ZMod p) (u : ℕ) (_hu : u < m + 1) (a : Sample (start + u))
      (ha : good lam (start + u) a) :
      (∑ col : Fin (start + u + 1) → Bool, if
        shiftedSignCorank ((sampleSuccEquiv (start + u)).symm (a, col)) lam ≠
          shiftedSignCorank a lam - 1 then fairSignWeight (Fin (start + u + 1)) else 0) ≤
            (p : ℝ)⁻¹ + δ := by
    let t := start + u
    have ht : (N : ℝ) / 3 ≤ (t : ℝ) := htlo u
    have htX : 2 ≤ (t : ℝ) / x := by
      calc
        _ ≤ ((N : ℝ) / x) / 3 := by linarith [hK', hsize]
        _ = ((N : ℝ) / 3) / x := by rw [← div_mul_eq_div_div_swap, div_mul_eq_div_div]
        _ ≤ (t : ℝ) / x := div_le_div_of_nonneg_right ht hx.le
    have htL : 2 * L ≤ (t : ℝ) / (8 * (K : ℝ) * x) := by
      calc
        _ = ((N : ℝ) / 3) / (8 * (K : ℝ) * x) := by
          dsimp only [L]
          field_simp [hKpos.ne', hx.ne']
          ring
        _ ≤ _ := div_le_div_of_nonneg_right ht (by positivity)
    have h2 : (2 : ℝ) ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
    have herr : 2 * Real.exp (-(t : ℝ) / (8 * (K : ℝ) * x)) ≤ δ := by
      calc
        _ ≤ 2 * Real.exp (-(2 * L)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          apply Real.exp_le_exp.mpr
          simpa only [neg_div] using neg_le_neg htL
        _ ≤ Real.exp L * Real.exp (-(2 * L)) :=
          mul_le_mul_of_nonneg_right h2 (Real.exp_nonneg _)
        _ = δ := by
          rw [← Real.exp_add]
          dsimp only [δ]
          congr 1
          ring
    exact (conditional_mass_le_of_rankFourierHealthy hp hK hlog htX a lam ha).trans
      (add_le_add_right herr _)
  have hδ₁ : δ ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h := expectation_eigenspaceStatistic_le_of_conditional start m hburn good
    (Real.exp_nonneg _) hδ₁ hGood hCond
  rw [congrArg (fun n : ℕ => expectation (fun a : Sample n => eigenspaceStatistic a p)) hEq] at h
  simpa only [hEq, δ, L, x, neg_div] using h

end Bernoulli
