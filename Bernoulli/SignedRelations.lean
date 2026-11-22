module

public import Bernoulli.RankFourier
public import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Character moments and signed zero relations

Expanding an integer power of a finite character sum gives ordered tuples of
coordinates, with repetitions allowed. Averaging across frequencies then keeps
exactly the tuples whose corresponding linear relation vanishes.
-/

open scoped BigOperators

namespace Bernoulli

/-- The unnormalized character moment counts ordered tuples summing to zero. -/
public theorem additive_char_sum_pow_eq_relation_count {ι : Type*} [Fintype ι]
    {p : ℕ} [NeZero p] (v : ι → ZMod p) (m : ℕ) :
    (∑ ξ : ZMod p, (∑ i, ZMod.stdAddChar (ξ * v i)) ^ m) =
      (p : ℂ) * ((Finset.univ.filter (fun t : Fin m → ι => ∑ j, v (t j) = 0)).card : ℂ) := by
  classical
  simp_rw [Fintype.sum_pow]
  rw [Finset.sum_comm]
  have hprod (ξ : ZMod p) (t : Fin m → ι) :
      (∏ j, ZMod.stdAddChar (ξ * v (t j))) = ZMod.stdAddChar (ξ * ∑ j, v (t j)) := by
    rw [Finset.mul_sum]
    exact (congrArg Additive.toMul (map_sum (ZMod.stdAddChar (N := p)).toAddMonoidHom
      (fun j => ξ * v (t j)) Finset.univ)).symm
  calc
    _ = ∑ t : Fin m → ι, if (∑ j, v (t j)) = 0 then (p : ℂ) else 0 := by
      refine Finset.sum_congr rfl fun t _ => ?_
      simp_rw [hprod]
      simpa only [ZMod.card, Nat.cast_ite, Nat.cast_zero] using AddChar.sum_mulShift (∑ j, v (t j))
        (ZMod.isPrimitive_stdAddChar p)
    _ = _ := by
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- The normalized `m`-th moment of a cosine sum is the number of ordered
length-`m` signed relations divided by `2 ^ m`. Both the indexing and the sign
of every term are independently chosen, and indices may repeat. -/
public theorem average_cos_sum_pow_eq_signed_relation_count {ι : Type*} [Fintype ι]
    {p : ℕ} [NeZero p] (v : ι → ZMod p) (m : ℕ) :
    (∑ ξ : ZMod p, (∑ i, Real.cos (2 * Real.pi * ((ξ * v i).val : ℝ) / p)) ^ m) / p =
      ((Finset.univ.filter (fun t : Fin m → ι × Bool =>
        (∑ j, (if (t j).2 then 1 else -1) * v (t j).1) = 0)).card : ℝ) / (2 : ℝ) ^ m := by
  let signed : ι × Bool → ZMod p := fun i => (if i.2 then 1 else -1) * v i.1
  have hcos (u : ZMod p) :
      (Real.cos (2 * Real.pi * (u.val : ℝ) / p) : ℂ) =
        (∑ s : Bool, ZMod.stdAddChar ((if s then 1 else -1) * u)) / 2 := by
    rw [← stdAddChar_fair_sign]
    simp [Fintype.univ_bool]
    ring
  have hsum (ξ : ZMod p) :
      (∑ i, (Real.cos (2 * Real.pi * ((ξ * v i).val : ℝ) / p) : ℂ)) =
        (∑ i, ZMod.stdAddChar (ξ * signed i)) / 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcos]
    apply congrArg (fun z : ℂ => z / 2)
    refine Finset.sum_congr rfl fun s _ => ?_
    dsimp only [signed]
    congr 1
    ring
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_div, Complex.ofReal_sum, Complex.ofReal_pow,
    Complex.ofReal_natCast, Complex.ofReal_ofNat]
  simp_rw [hsum, div_pow]
  rw [← Finset.sum_div, additive_char_sum_pow_eq_relation_count signed m]
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne p)
  dsimp [signed]
  field_simp

end Bernoulli
