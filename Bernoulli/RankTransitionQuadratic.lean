module

public import Bernoulli.RankTransition
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.Ring

/-!
# Quadratic character averages on two coordinate sets

Resampling one set of signs leaves a linear phase on the other set.
The two resampled assignments coincide with probability equal to the mass of
one assignment on the resampled set.
-/

open scoped BigOperators
open Matrix

namespace Bernoulli

/-- Extend signs on the first coordinate set by zero on the second. -/
@[expose] public def fairSignLeft {J I : Type*} {p : ℕ} (σ : J → Bool) :
    J ⊕ I → ZMod p :=
  Sum.elim (fun j => fairSign (σ j)) 0

/-- Extend signs on the second coordinate set by zero on the first. -/
@[expose] public def fairSignRight {J I : Type*} {p : ℕ} (τ : I → Bool) :
    J ⊕ I → ZMod p :=
  Sum.elim 0 (fun i => fairSign (τ i))

private theorem fairSignWeight_sum_type (J I : Type*) [Fintype J] [Fintype I] :
    fairSignWeight (J ⊕ I) = fairSignWeight J * fairSignWeight I := by
  simp [fairSignWeight, Fintype.card_sum, pow_add]

private theorem dotProduct_fairSignRight {J I : Type*} [Fintype J] [Fintype I]
    {p : ℕ} (τ : I → Bool) (v : J ⊕ I → ZMod p) :
    fairSignRight τ ⬝ᵥ v = (fun i => fairSign (τ i)) ⬝ᵥ (fun i => v (Sum.inr i)) := by
  simp [dotProduct, fairSignRight, Fintype.sum_sum_type]

/-- The quadratic character average is bounded by the square root of the
collision probability on the resampled block plus the uniform bound for the
nontrivial resampled linear phases. -/
public theorem norm_fairSign_quadratic_le_of_resample {J I : Type*}
    [Fintype J] [Fintype I] [DecidableEq J] [DecidableEq I] {p : ℕ} [NeZero p]
    {B : Matrix (J ⊕ I) (J ⊕ I) (ZMod p)} (hB : B.IsSymm) (a : ZMod p)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hlinear : ∀ σ σ' : J → Bool, σ ≠ σ' →
      ‖∑ τ : I → Bool, (fairSignWeight I : ℂ) * ZMod.stdAddChar
        (-(((fun i => fairSign (τ i)) ⬝ᵥ
          (fun i => (B *ᵥ (fairSignLeft σ - fairSignLeft σ')) (Sum.inr i))) *
            (2 * a)))‖ ≤ ε) :
    ‖∑ ω : J ⊕ I → Bool, (fairSignWeight (J ⊕ I) : ℂ) *
      ZMod.stdAddChar (-(((fun i => fairSign (ω i)) ⬝ᵥ
        (B *ᵥ (fun i => fairSign (ω i)))) * a))‖ ≤
      Real.sqrt (fairSignWeight J + ε) := by
  classical
  let x : (J → Bool) → (J ⊕ I → ZMod p) := fairSignLeft
  let y : (I → Bool) → (J ⊕ I → ZMod p) := fairSignRight
  let phase (σ : J → Bool) (τ : I → Bool) :=
    -(((x σ + y τ) ⬝ᵥ (B *ᵥ (x σ + y τ))) * a)
  let R (σ σ' : J → Bool) :=
    ‖∑ τ : I → Bool, (fairSignWeight I : ℂ) *
      ZMod.stdAddChar (phase σ τ - phase σ' τ)‖
  have hsplit :
      (∑ ω : J ⊕ I → Bool, (fairSignWeight (J ⊕ I) : ℂ) *
        ZMod.stdAddChar (-(((fun i => fairSign (ω i)) ⬝ᵥ
          (B *ᵥ (fun i => fairSign (ω i)))) * a))) =
      ∑ τ : I → Bool, (fairSignWeight I : ℂ) *
        ∑ σ : J → Bool, (fairSignWeight J : ℂ) * ZMod.stdAddChar (phase σ τ) := by
    rw [← (Equiv.sumArrowEquivProdArrow J I Bool).symm.sum_comp]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have hsign : (fun i => fairSign ((Equiv.sumArrowEquivProdArrow J I Bool).symm (σ, τ) i)) =
        x σ + y τ := by
      funext i
      cases i <;> simp [x, y, fairSignLeft, fairSignRight]
    rw [hsign, fairSignWeight_sum_type, Complex.ofReal_mul]
    dsimp only [phase]
    ring
  have hpoint (σ σ' : J → Bool) : R σ σ' ≤ (if σ = σ' then 1 else 0) + ε := by
    by_cases heq : σ = σ'
    · subst σ'
      have hsum : (∑ _τ : I → Bool, (fairSignWeight I : ℂ)) = 1 := by
        rw [← Complex.ofReal_sum, sum_fairSignWeight, Complex.ofReal_one]
      have hR : R σ σ = 1 := by
        simp only [R, sub_self, AddChar.map_zero_eq_one, mul_one, hsum, norm_one]
      rw [hR, ite_eq_left rfl]
      exact le_add_of_nonneg_right hε
    · let w : J ⊕ I → ZMod p := B *ᵥ (x σ - x σ')
      let c := -((x σ ⬝ᵥ (B *ᵥ x σ) - x σ' ⬝ᵥ (B *ᵥ x σ')) * a)
      have hphase (τ : I → Bool) :
          phase σ τ - phase σ' τ =
            c + -(((fun i => fairSign (τ i)) ⬝ᵥ (fun i => w (Sum.inr i))) * (2 * a)) := by
        dsimp only [phase, c]
        rw [show -(((x σ + y τ) ⬝ᵥ (B *ᵥ (x σ + y τ))) * a) -
            -(((x σ' + y τ) ⬝ᵥ (B *ᵥ (x σ' + y τ))) * a) =
            -(((x σ + y τ) ⬝ᵥ (B *ᵥ (x σ + y τ)) -
              (x σ' + y τ) ⬝ᵥ (B *ᵥ (x σ' + y τ))) * a) by ring]
        rw [quadratic_sub_resample_eq hB, dotProduct_fairSignRight τ w]
        ring
      have hcancel := norm_modular_phase_add_const (fun _ : I → Bool => fairSignWeight I)
        (fun τ => -(((fun i => fairSign (τ i)) ⬝ᵥ (fun i => w (Sum.inr i))) * (2 * a))) c
      simpa only [R, hphase, hcancel, heq, ite_false, zero_add] using hlinear σ σ' heq
  have hweighted (σ : J → Bool) :
      (∑ σ' : J → Bool, fairSignWeight J * fairSignWeight J * R σ σ') ≤
        fairSignWeight J * fairSignWeight J + fairSignWeight J * ε := by
    calc
      _ ≤ ∑ σ' : J → Bool, fairSignWeight J * fairSignWeight J *
          ((if σ = σ' then 1 else 0) + ε) :=
        Finset.sum_le_sum fun σ' _ => mul_le_mul_of_nonneg_left (hpoint σ σ')
          (mul_nonneg (fairSignWeight_nonneg J) (fairSignWeight_nonneg J))
      _ = _ := by
        simp_rw [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
        rw [show (∑ σ' : J → Bool, if σ = σ' then fairSignWeight J * fairSignWeight J
              else 0) = fairSignWeight J * fairSignWeight J by simp]
        congr 1
        rw [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, sum_fairSignWeight, one_mul]
  rw [hsplit]
  apply Real.le_sqrt_of_sq_le
  calc
    _ ≤ ∑ σ : J → Bool, ∑ σ' : J → Bool, fairSignWeight J * fairSignWeight J * R σ σ' :=
      norm_modular_phase_sq_le_resampling (fun _ => fairSignWeight J) (fun _ => fairSignWeight I)
        (fun _ => fairSignWeight_nonneg J) (fun _ => fairSignWeight_nonneg I)
        (sum_fairSignWeight I) phase
    _ ≤ ∑ _σ : J → Bool, (fairSignWeight J * fairSignWeight J + fairSignWeight J * ε) :=
      Finset.sum_le_sum fun σ _ => hweighted σ
    _ = _ := by simp_rw [← mul_add, ← Finset.sum_mul, sum_fairSignWeight, one_mul]

end Bernoulli
