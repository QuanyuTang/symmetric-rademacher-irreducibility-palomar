module

public import Bernoulli.PrimeComparison
public import Bernoulli.RankTransitionExpectation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Summing the shifted-corank bounds over all field elements
-/

open scoped BigOperators
open Matrix
namespace Bernoulli

/-- An exponential upper bound on both the sign collision probability and
the retained-coordinate Fourier bound controls the quadratic error. -/
public theorem sqrt_fairSignWeight_add_le_exp (j : ℕ) {L ε : ℝ}
    (hL : L ≤ (j : ℝ) * Real.log 2) (hε : ε ≤ Real.exp (-L)) :
    Real.sqrt (fairSignWeight (Fin j) + ε) ≤ 2 * Real.exp (-L / 2) := by
  have hw : fairSignWeight (Fin j) = Real.exp (-((j : ℝ) * Real.log 2)) := by
    rw [fairSignWeight, Fintype.card_fin, ← mul_neg, Real.exp_nat_mul, Real.exp_neg,
      Real.exp_log (by norm_num : (0 : ℝ) < 2), one_div]
  have h₁ : fairSignWeight (Fin j) ≤ Real.exp (-L) := by
    rw [hw]
    exact Real.exp_le_exp.mpr (neg_le_neg hL)
  have h₂ : (Real.exp (-L / 2)) ^ 2 = Real.exp (-L) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, h₂]
  linarith [Real.exp_nonneg (-L)]

/-- The eigenspace statistic is the sum of the shifted coranks over the
prime field. -/
public theorem eigenspaceStatistic_eq_sum_shiftedSignCorank {n p : ℕ} [Fact p.Prime]
    (a : Sample n) :
    eigenspaceStatistic a p = ∑ lam : ZMod p, (shiftedSignCorank a lam : ℝ) := by
  have hp : p.Prime := Fact.out
  simp only [eigenspaceStatistic, dite_eq_left hp, shiftedSignCorank]
  apply Finset.sum_congr rfl
  intro lam _
  congr 1
  have hdiag (v : Fin n → ZMod p) : Matrix.diagonal (fun _ => lam) *ᵥ v = lam • v := by
    funext i
    simp [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
  have heq : Module.End.eigenspace ((matrix a).map (Int.castRingHom (ZMod p))).toLin' lam =
      LinearMap.ker (shiftedSignMatrix a lam).mulVecLin := by
    ext v
    simp only [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, LinearMap.mem_ker,
      Matrix.mulVecLin_apply, shiftedSignMatrix, Matrix.sub_mulVec, sub_eq_zero, hdiag]
  rw [heq]

/-- A uniform upper bound for each shift gives an upper bound for the mean
eigenspace statistic, with the cardinality of the field as a factor. -/
public theorem expectation_eigenspaceStatistic_le_of_shiftedSignCorank
    {n p : ℕ} [Fact p.Prime] {q : ℝ}
    (h : ∀ lam : ZMod p,
      expectation (fun a : Sample n => (shiftedSignCorank a lam : ℝ)) ≤ q) :
    expectation (fun a : Sample n => eigenspaceStatistic a p) ≤ (p : ℝ) * q := by
  simp_rw [eigenspaceStatistic_eq_sum_shiftedSignCorank, expectation]
  rw [Finset.sum_comm, Finset.sum_div]
  calc
    _ ≤ ∑ _lam : ZMod p, q := Finset.sum_le_sum fun lam _ => h lam
    _ = _ := by simp [ZMod.card, nsmul_eq_mul]

/-- Uniform conditional transition and health errors at most δ give an
expected eigenspace statistic at most one plus the explicit finite-size
and shift-summed errors. -/
public theorem expectation_eigenspaceStatistic_le_of_conditional {p : ℕ} [Fact p.Prime]
    (start m : ℕ) (hburn : start + 1 ≤ m)
    (good : (lam : ZMod p) → (t : ℕ) → Sample t → Prop)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδ₁ : δ ≤ 1)
    (hgood : ∀ lam : ZMod p, ∀ t < m + 1,
      probability (fun a : Sample (start + t) => ¬ good lam (start + t) a) ≤ δ)
    (hcond : ∀ lam : ZMod p, ∀ t < m + 1, ∀ a : Sample (start + t),
      good lam (start + t) a →
      (∑ col : Fin (start + t + 1) → Bool, if
        shiftedSignCorank ((sampleSuccEquiv (start + t)).symm (a, col)) lam ≠
          shiftedSignCorank a lam - 1 then fairSignWeight (Fin (start + t + 1)) else 0) ≤
            (p : ℝ)⁻¹ + δ) :
    expectation (fun a : Sample (start + m + 1) => eigenspaceStatistic a p) ≤
      1 + 4 * (((start + m + 1 : ℕ) : ℝ) ^ 3 / p + ((start + m + 1 : ℕ) : ℝ) ^ 3 * p * δ) := by
  let N : ℝ := (start + m + 1 : ℕ)
  let M : ℝ := (m + 1 : ℕ)
  let q : ℝ := (p : ℝ)⁻¹ + δ
  have hp : 0 < (p : ℝ) := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have hq : 0 ≤ q := add_nonneg (inv_nonneg.mpr hp.le) hδ
  have hMN : M ≤ N := by
    dsimp only [M, N]
    exact_mod_cast (show m + 1 ≤ start + m + 1 by omega)
  have hN : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast (show 1 ≤ start + m + 1 by omega)
  have hδsq : δ ^ 2 ≤ δ := by nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ₁)]
  have hqsq : q ^ 2 ≤ 2 * ((p : ℝ)⁻¹) ^ 2 + 2 * δ := by
    dsimp only [q]
    nlinarith [sq_nonneg ((p : ℝ)⁻¹ - δ)]
  have hNsq : N ^ 2 ≤ N ^ 3 := by nlinarith [mul_nonneg (sq_nonneg N) (sub_nonneg.mpr hN)]
  have hNcube : 1 ≤ N ^ 3 := by
    exact one_le_pow₀ hN
  have hone : δ * p ≤ N ^ 3 * p * δ := by
    rw [mul_comm δ (p : ℝ), ← one_mul ((p : ℝ) * δ), mul_assoc]
    exact mul_le_mul_of_nonneg_right hNcube (mul_nonneg hp.le hδ)
  have htwo : N ^ 2 * p * δ ≤ N ^ 3 * p * δ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNsq hp.le) hδ
  change _ ≤ 1 + 4 * (N ^ 3 / p + N ^ 3 * p * δ)
  calc
    _ ≤ (p : ℝ) * (q + N * (M * δ + M ^ 2 * q ^ 2)) :=
      expectation_eigenspaceStatistic_le_of_shiftedSignCorank fun lam =>
        expectation_shiftedSignCorank_le_of_conditional lam start m hburn (good lam) hq
          (hgood lam) (hcond lam)
    _ ≤ (p : ℝ) * (q + N * (N * δ + N ^ 2 * (2 * ((p : ℝ)⁻¹) ^ 2 + 2 * δ))) := by
      gcongr
    _ = 1 + δ * p + N ^ 2 * p * δ + 2 * (N ^ 3 / p) + 2 * (N ^ 3 * p * δ) := by
      dsimp only [q]
      field_simp [hp.ne']
      ring
    _ ≤ _ := by linarith [div_nonneg (pow_nonneg (zero_le_one.trans hN) 3) hp.le]

end Bernoulli
