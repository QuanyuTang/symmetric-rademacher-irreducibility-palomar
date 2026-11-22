module

public import Bernoulli.MatrixDiscriminantBounds
public import Bernoulli.MatrixFieldAverages
import Mathlib.Tactic

/-! The deterministic factor-count bound follows from a uniform prime-ideal estimate. -/

open Bernoulli.ConcreteFactorFields NumberField

namespace Bernoulli

/-- The degree-one prime-ideal average of a number field. -/
@[expose] public noncomputable def primeIdealAverage (K : Type) [Field K] (x : ℝ) : ℝ :=
  primeAverage x (fun p => primeIdealCount K p)

/-- The uniform quantitative prime-ideal statement needed by the proof. -/
@[expose] public def UniformPrimeIdealEstimate : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (K : Type) [Field K] [NumberField K] (x : ℝ), 4 ≤ x →
    |primeIdealAverage K x - 1| ≤ C *
      ((Real.log |(NumberField.discr K : ℝ)| + (Module.finrank ℚ K : ℝ)) * x ^ (-(1 / 64) : ℝ) +
        (Module.finrank ℚ K : ℝ) * x ^ (-(1 / 2) : ℝ) * Real.log x)

/-- The rational prime mass bound follows by taking `K = ℚ`. -/
public theorem rational_prime_mass_bound_of_uniform_estimate (h : UniformPrimeIdealEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 4 ≤ x → |primeAverage x (fun _ => 1) - 1| ≤
      C * (x ^ (-(1 / 64) : ℝ) + x ^ (-(1 / 2) : ℝ) * Real.log x) := by
  obtain ⟨C, hC, hP⟩ := h
  refine ⟨C, hC, fun x hx => ?_⟩
  have hx₀ : 0 ≤ x := by linarith
  have hrat : primeIdealAverage ℚ x = primeAverage x (fun _ => 1) := by
    unfold primeIdealAverage primeAverage
    apply Finset.sum_congr rfl
    intro p hp
    let : Fact p.Prime := ⟨((mem_primesThrough hx₀).mp hp).1⟩
    change (primeIdealCount ℚ p : ℝ) * primeWeight x p = _
    simp only [show primeIdealCount ℚ p = 1 from card_primeIdeals_rat_eq_one p, Nat.cast_one, one_mul]
  simpa [hrat, NumberField.discr_rat] using hP ℚ x hx

/-- A uniform field estimate implies a deterministic estimate of the number of
irreducible factors of every sampled matrix, counted with their multiplicities. -/
public theorem factor_average_bound_of_uniform_estimate (h : UniformPrimeIdealEstimate) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 0 < n → ∀ (a : Sample n) (x : ℝ), 4 ≤ x →
      |primeAverage x (eigenspaceStatistic a) - (factorCount a : ℝ)| ≤
      C * ((n : ℝ) ^ 2 * Real.log (2 * n) * x ^ (-(1 / 64) : ℝ) +
        (n : ℝ) * x ^ (-(1 / 2) : ℝ) * Real.log x + (n : ℝ) ^ 3 * Real.log (2 * n) / x) := by
  obtain ⟨C, hC, hP⟩ := h
  refine ⟨3 * C + 6, by positivity, fun n hn a x hx => ?_⟩
  let N : ℝ := n
  let u := x ^ (-(1 / 64) : ℝ)
  let v := x ^ (-(1 / 2) : ℝ) * Real.log x
  let e (q : Index a) : ℝ := factorMultiplicity (matrix a).charpoly q
  let d (q : Index a) : ℝ := Module.finrank ℚ (RootField a q)
  let l (q : Index a) : ℝ := Real.log |(NumberField.discr (RootField a q) : ℝ)|
  have hN : 1 ≤ N := by
    change (1 : ℝ) ≤ (n : ℝ)
    exact_mod_cast (Nat.succ_le_iff.mpr hn)
  have hxpos : 0 < x := by linarith
  have hv : 0 ≤ v := mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hlog : (1 / 2 : ℝ) ≤ Real.log (2 * N) := by
    have h₂ : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
      norm_num at h ⊢
      exact h
    exact h₂.trans (Real.log_le_log (by norm_num) (by linarith))
  have hlog₀ : 0 ≤ Real.log (2 * N) := by linarith
  have hNN : N * (N - 1) ≤ N ^ 2 := by nlinarith
  have hNlog : N ≤ 2 * (N ^ 2 * Real.log (2 * N)) := by
    have hN2 : N ≤ N ^ 2 := by nlinarith [mul_nonneg (show 0 ≤ N by positivity) (sub_nonneg.mpr hN)]
    calc
      _ ≤ N ^ 2 := hN2
      _ ≤ _ := by nlinarith [mul_nonneg (sq_nonneg N) (sub_nonneg.mpr hlog)]
  have hsumD : (∑ q : Index a, e q * d q) = N := by
    dsimp [e, d, N]
    exact_mod_cast sum_weighted_fieldDegree a
  have hsumM : (∑ q : Index a, e q) = (factorCount a : ℝ) := by
    dsimp [e]
    exact_mod_cast sum_factorMultiplicity_eq_factorCount a
  have hlogD : (∑ q : Index a, e q * l q) ≤ N ^ 2 * Real.log (2 * N) :=
    (sum_weighted_log_abs_fieldDiscriminant_le a hn).trans (mul_le_mul_of_nonneg_right hNN hlog₀)
  have hlogE : Real.log (exceptionalDiscriminant a).natAbs ≤ 2 * N ^ 2 * Real.log (2 * N) := by
    calc
      _ ≤ 2 * N * (N - 1) * Real.log (2 * N) := log_natAbs_exceptional_product_le a hn
      _ = (2 * (N * (N - 1))) * Real.log (2 * N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hNN (by norm_num : (0 : ℝ) ≤ 2)) hlog₀
  have hT : |characteristicFieldAverage a x - (factorCount a : ℝ)| ≤
      C * (3 * (N ^ 2 * Real.log (2 * N)) * u + N * v) := by
    have hexpand : characteristicFieldAverage a x - (factorCount a : ℝ) =
        ∑ q : Index a, e q * (primeIdealAverage (RootField a q) x - 1) := by
      simp only [characteristicFieldAverage, primeIdealAverage, mul_sub, mul_one, Finset.sum_sub_distrib]
      rw [hsumM]
    rw [hexpand]
    calc
      _ ≤ ∑ q : Index a, |e q * (primeIdealAverage (RootField a q) x - 1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ q : Index a, C * ((e q * l q + e q * d q) * u + e q * d q * v) := by
        apply Finset.sum_le_sum
        intro q _
        have heq : 0 ≤ e q := Nat.cast_nonneg _
        rw [abs_mul, abs_of_nonneg heq]
        calc
          _ ≤ e q * (C * ((l q + d q) * u + d q * v)) := by
            apply mul_le_mul_of_nonneg_left _ heq
            convert hP (RootField a q) x hx using 1
            dsimp [l, d, u, v]
            ring
          _ = _ := by ring
      _ = C * (((∑ q : Index a, e q * l q) + N) * u + N * v) := by
        rw [← hsumD]
        simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, Finset.sum_add_distrib]
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hC.le
        exact add_le_add (mul_le_mul_of_nonneg_right (by linarith) hu) le_rfl
  let z := primeAverage x (eigenspaceStatistic a)
  let m : ℝ := factorCount a
  let w := characteristicFieldAverage a x
  have hZ : |z - w| ≤ 6 * N ^ 3 * Real.log (2 * N) / x := by
    calc
      _ ≤ 3 * N * Real.log (exceptionalDiscriminant a).natAbs / x :=
        abs_matrixAverage_sub_characteristicFieldAverage_le a hxpos
      _ ≤ 3 * N * (2 * N ^ 2 * Real.log (2 * N)) / x :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hlogE (by positivity)) hxpos.le
      _ = _ := by ring
  calc
    |z - m| = |(z - w) + (w - m)| := by
      congr 1
      ring
    _ ≤ |z - w| + |w - m| := abs_add_le _ _
    _ ≤ 6 * N ^ 3 * Real.log (2 * N) / x + C * (3 * (N ^ 2 * Real.log (2 * N)) * u + N * v) :=
      add_le_add hZ hT
    _ ≤ (3 * C + 6) * (N ^ 2 * Real.log (2 * N) * u + N * v + N ^ 3 * Real.log (2 * N) / x) := by
      have hN₀ : 0 ≤ N := zero_le_one.trans hN
      have h₁ : 0 ≤ N ^ 2 * Real.log (2 * N) * u := mul_nonneg (mul_nonneg (sq_nonneg N) hlog₀) hu
      have h₂ : 0 ≤ N * v := mul_nonneg hN₀ hv
      have h₃ : 0 ≤ N ^ 3 * Real.log (2 * N) / x :=
        div_nonneg (mul_nonneg (pow_nonneg hN₀ _) hlog₀) hxpos.le
      let U := N ^ 2 * Real.log (2 * N) * u
      let V := N * v
      let W := N ^ 3 * Real.log (2 * N) / x
      calc
        _ = (3 * C) * U + C * V + 6 * W := by dsimp [U, V, W]; ring
        _ ≤ (3 * C + 6) * U + (3 * C + 6) * V + (3 * C + 6) * W := by
          exact add_le_add
            (add_le_add (mul_le_mul_of_nonneg_right (by linarith) h₁)
              (mul_le_mul_of_nonneg_right (by linarith) h₂))
            (mul_le_mul_of_nonneg_right (by linarith) h₃)
        _ = _ := by dsimp [U, V, W]; ring
    _ = _ := by dsimp [N, u, v]; ring

end Bernoulli
