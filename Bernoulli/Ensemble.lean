module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! The symmetric Rademacher ensemble and its uniform finite law. -/

open scoped BigOperators

namespace Bernoulli

/-- The independently sampled positions, including the diagonal. -/
public abbrev UpperIndex (n : ℕ) := {ij : Fin n × Fin n // ij.1 ≤ ij.2}

/-- Each Boolean assignment occurs with the same probability. -/
public abbrev Sample (n : ℕ) := UpperIndex n → Bool

/-- The symmetric integer matrix obtained by reflecting the upper triangle. -/
@[expose] public def matrix {n : ℕ} (a : Sample n) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j =>
    if a ⟨(min i j, max i j), le_trans (min_le_left ..) (le_max_left ..)⟩ then 1 else -1

/-- The matrices described by Definition 1.1 of the manuscript. -/
public abbrev SignedSymmetric (n : ℕ) := {A : Matrix (Fin n) (Fin n) ℤ //
  (∀ i j, A i j = A j i) ∧ (∀ i j, A i j = 1 ∨ A i j = -1)}

public theorem matrix_symmetric {n : ℕ} (a : Sample n) (i j : Fin n) :
    matrix a i j = matrix a j i := by
  unfold matrix
  simp only [min_comm, max_comm]

public theorem matrix_entry {n : ℕ} (a : Sample n) (i j : Fin n) :
    matrix a i j = 1 ∨ matrix a i j = -1 := by
  unfold matrix
  split <;> simp

/-- Recovering the upper-triangular signs is inverse to reflection. -/
public def sampleEquivMatrix (n : ℕ) : Sample n ≃ SignedSymmetric n where
  toFun a := ⟨matrix a, matrix_symmetric a, matrix_entry a⟩
  invFun A := fun ij => decide (A.1 ij.1.1 ij.1.2 = 1)
  left_inv a := by
    funext ij
    obtain ⟨⟨i, j⟩, hij⟩ := ij
    simp only [matrix, min_eq_left hij, max_eq_right hij]
    cases a ⟨(i, j), hij⟩ <;> decide
  right_inv A := by
    apply Subtype.ext
    funext i j
    change (if (decide (A.1 (min i j) (max i j) = 1)) then (1 : ℤ) else -1) = A.1 i j
    have hsort : A.1 (min i j) (max i j) = A.1 i j := by
      rcases le_total i j with hij | hji
      · rw [min_eq_left hij, max_eq_right hij]
      · rw [min_eq_right hji, max_eq_left hji, A.2.1 j i]
    rw [hsort]
    rcases A.2.2 i j with h | h <;> rw [h] <;> decide

/-- Expectation for the uniform distribution on upper-triangular assignments. -/
@[expose] public noncomputable def expectation {n : ℕ} (f : Sample n → ℝ) : ℝ :=
  (∑ a, f a) / (Fintype.card (Sample n) : ℝ)

/-- Uniform probability, written as the expectation of a Boolean-valued indicator. -/
@[expose] public noncomputable def probability {n : ℕ} (p : Sample n → Prop) : ℝ := by
  classical
  exact expectation (fun a => if p a then 1 else 0)

public theorem expectation_mono {n : ℕ} {f g : Sample n → ℝ} (h : ∀ a, f a ≤ g a) :
    expectation f ≤ expectation g := by
  apply div_le_div_of_nonneg_right (Finset.sum_le_sum fun a _ => h a)
  exact Nat.cast_nonneg _

@[simp] public theorem expectation_const {n : ℕ} (r : ℝ) :
    expectation (n := n) (fun _ => r) = r := by
  simp [expectation]

public theorem probability_le_one {n : ℕ} (p : Sample n → Prop) : probability p ≤ 1 := by
  classical
  rw [← expectation_const (n := n) 1]
  apply expectation_mono
  intro a
  split <;> simp

/-- The characteristic polynomial over `ℚ` of the sampled matrix. -/
@[expose] public noncomputable def charpoly {n : ℕ} (a : Sample n) : Polynomial ℚ :=
  ((matrix a).map (Int.castRingHom ℚ)).charpoly

/-- The event in the main theorem of the manuscript, for positive dimension. -/
@[expose] public noncomputable def reducibilityProbability (n : ℕ) : ℝ :=
  probability (fun a : Sample n => ¬ Irreducible (charpoly a))

end Bernoulli
