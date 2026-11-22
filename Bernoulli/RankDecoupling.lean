module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Tactic.Ring

/-!
# Decoupling a quadratic phase by resampling

A Cauchy–Schwarz inequality for finite weights lets one resample just one block
of signs. The difference of the resulting quadratic phases is linear in the
unchanged signs, up to a constant depending only on the resampled block.
-/

open scoped BigOperators ComplexConjugate

namespace Bernoulli

/-- After squaring a product-space average, Cauchy–Schwarz lets one share `y`
and resample `x` independently. The weights on the shared coordinate sum to one. -/
public theorem norm_weighted_sum_sq_le_resampling {X Y : Type*} [Fintype X] [Fintype Y]
    (wx : X → ℝ) (wy : Y → ℝ) (hx : ∀ x, 0 ≤ wx x) (hy : ∀ y, 0 ≤ wy y)
    (hwy : (∑ y, wy y) = 1) (f : X → Y → ℂ) :
    ‖∑ y, (wy y : ℂ) * ∑ x, (wx x : ℂ) * f x y‖ ^ 2 ≤
      ∑ x, ∑ x', wx x * wx x' * ‖∑ y, (wy y : ℂ) * (f x y * conj (f x' y))‖ := by
  let g : Y → ℂ := fun y => ∑ x, (wx x : ℂ) * f x y
  have htriangle : ‖∑ y, (wy y : ℂ) * g y‖ ≤ ∑ y, wy y * ‖g y‖ := by
    calc
      _ ≤ ∑ y, ‖(wy y : ℂ) * g y‖ := norm_sum_le _ _
      _ = _ := by simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg, hy]
  have hcs : (∑ y, wy y * ‖g y‖) ^ 2 ≤ ∑ y, wy y * ‖g y‖ ^ 2 := by
    have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
      (r := fun y => wy y * ‖g y‖) (f := wy) (g := fun y => wy y * ‖g y‖ ^ 2)
      (fun y _ => hy y) (fun y _ => mul_nonneg (hy y) (sq_nonneg _))
      (fun y _ => le_of_eq (by ring))
    simpa [hwy] using h
  have hexpand : (∑ y, (wy y : ℂ) * (g y * conj (g y))) =
      ∑ x, ∑ x', (wx x : ℂ) * (wx x' : ℂ) *
        ∑ y, (wy y : ℂ) * (f x y * conj (f x' y)) := by
    calc
      _ = ∑ y, ∑ x, ∑ x', (wy y : ℂ) * ((wx x : ℂ) * f x y) *
          ((wx x' : ℂ) * conj (f x' y)) := by
        refine Finset.sum_congr rfl fun y _ => ?_
        simp only [g, map_sum, map_mul, Complex.conj_ofReal]
        rw [Finset.sum_mul]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
        ring
      _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun y _ => ?_
        ring
  calc
    ‖∑ y, (wy y : ℂ) * ∑ x, (wx x : ℂ) * f x y‖ ^ 2
        ≤ ∑ y, wy y * ‖g y‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) htriangle 2).trans hcs
    _ = (∑ y, (wy y : ℂ) * (g y * conj (g y))).re := by
      change _ = Complex.reAddGroupHom _
      rw [map_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      simp [Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    _ = (∑ x, ∑ x', (wx x : ℂ) * (wx x' : ℂ) *
        ∑ y, (wy y : ℂ) * (f x y * conj (f x' y))).re := congrArg Complex.re hexpand
    _ ≤ _ := by
      change Complex.reAddGroupHom _ ≤ _
      simp only [map_sum, Complex.coe_reAddGroupHom]
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun x' _ => ?_
      rw [← Complex.ofReal_mul]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      exact mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (mul_nonneg (hx x) (hx x'))

/-- The resampling inequality for a phase in `ZMod p`, written directly as a
character average of differences. -/
public theorem norm_modular_phase_sq_le_resampling {X Y : Type*} [Fintype X] [Fintype Y]
    {p : ℕ} [NeZero p] (wx : X → ℝ) (wy : Y → ℝ)
    (hx : ∀ x, 0 ≤ wx x) (hy : ∀ y, 0 ≤ wy y) (hwy : (∑ y, wy y) = 1)
    (phase : X → Y → ZMod p) :
    ‖∑ y, (wy y : ℂ) * ∑ x, (wx x : ℂ) * ZMod.stdAddChar (phase x y)‖ ^ 2 ≤
      ∑ x, ∑ x', wx x * wx x' *
        ‖∑ y, (wy y : ℂ) * ZMod.stdAddChar (phase x y - phase x' y)‖ := by
  have hconj (z : ZMod p) : conj (ZMod.stdAddChar z) = ZMod.stdAddChar (-z) := by
    rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply, ← Circle.coe_inv_eq_conj, Circle.coe_inv]
  simpa only [hconj, ← AddChar.map_add_eq_mul, ← sub_eq_add_neg] using
    norm_weighted_sum_sq_le_resampling wx wy hx hy hwy
      (fun x y => ZMod.stdAddChar (phase x y))

/-- A constant phase can be discarded when bounding the magnitude of a character average. -/
public theorem norm_modular_phase_add_const {Y : Type*} [Fintype Y] {p : ℕ} [NeZero p]
    (w : Y → ℝ) (phase : Y → ZMod p) (c : ZMod p) :
    ‖∑ y, (w y : ℂ) * ZMod.stdAddChar (c + phase y)‖ =
      ‖∑ y, (w y : ℂ) * ZMod.stdAddChar (phase y)‖ := by
  have h : (∑ y, (w y : ℂ) * ZMod.stdAddChar (c + phase y)) =
      ZMod.stdAddChar c * ∑ y, (w y : ℂ) * ZMod.stdAddChar (phase y) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [AddChar.map_add_eq_mul]
    ring
  rw [h, Complex.norm_mul]
  simp [ZMod.stdAddChar_apply]

open Matrix

/-- Holding `y` fixed and changing `x` to `x'` in a symmetric quadratic form
leaves a term linear in `y` and a constant independent of `y`. -/
public theorem quadratic_sub_resample_eq {K ι : Type*} [CommRing K] [Fintype ι]
    {A : Matrix ι ι K} (hA : A.IsSymm) (x x' y : ι → K) :
    (x + y) ⬝ᵥ (A *ᵥ (x + y)) - (x' + y) ⬝ᵥ (A *ᵥ (x' + y)) =
      (x ⬝ᵥ (A *ᵥ x) - x' ⬝ᵥ (A *ᵥ x')) + 2 * (y ⬝ᵥ (A *ᵥ (x - x'))) := by
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, add_dotProduct, dotProduct_add, dotProduct_sub]
  rw [hA.dotProduct_mulVec_comm (x := x) (y := y),
    hA.dotProduct_mulVec_comm (x := x') (y := y)]
  ring

end Bernoulli
