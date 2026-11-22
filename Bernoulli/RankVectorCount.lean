module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.GroupWithZero.Units.Equiv
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Counting vectors with large products of nonnegative factors

The finite product formula and Markov's inequality bound the number of vectors
with unusually large products. The second statement takes moments only on the
selected coordinates, as needed for the finite-field character estimates.
-/

open scoped BigOperators

namespace Bernoulli

/-- A product-space counting bound for a finite set of vectors whose nonnegative
product is bounded below by `a`. -/
public theorem card_mul_le_prod_sum {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (g : ι → Ω → ℝ) (hg : ∀ i x, 0 ≤ g i x) (bad : Finset (ι → Ω)) (a : ℝ)
    (hbad : ∀ w ∈ bad, a ≤ ∏ i, g i (w i)) :
    (bad.card : ℝ) * a ≤ ∏ i, ∑ x, g i x := by
  calc
    _ = ∑ _w ∈ bad, a := by simp [nsmul_eq_mul]
    _ ≤ ∑ w ∈ bad, ∏ i, g i (w i) := Finset.sum_le_sum hbad
    _ ≤ ∑ w : ι → Ω, ∏ i, g i (w i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun w _ _ => Finset.prod_nonneg fun i _ => hg i (w i))
    _ = _ := (Fintype.prod_sum g).symm

/-- If the `q`-th moment on each tested coordinate is at most `b`, the number of
vectors whose product on the tested coordinates is at least `a` is at most
`|Ω|^|ι| * b^|tested| / a^q`. The condition on moments is written without dividing by `|Ω|`. -/
public theorem card_le_of_prod_ge_of_coordinate_moment {ι Ω : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (tested : Finset ι) (g : ι → Ω → ℝ) (hg : ∀ i x, 0 ≤ g i x)
    (bad : Finset (ι → Ω)) (q : ℕ) {a b : ℝ} (ha : 0 < a)
    (hbad : ∀ w ∈ bad, a ≤ ∏ i ∈ tested, g i (w i))
    (hmoment : ∀ i ∈ tested, (∑ x, g i x ^ q) ≤ (Fintype.card Ω : ℝ) * b) :
    (bad.card : ℝ) ≤ (Fintype.card Ω : ℝ) ^ Fintype.card ι * b ^ tested.card / a ^ q := by
  let moment : ι → Ω → ℝ := fun i x => if i ∈ tested then g i x ^ q else 1
  have hnonneg (i : ι) (x : Ω) : 0 ≤ moment i x := by
    dsimp only [moment]
    split
    · exact pow_nonneg (hg i x) q
    · exact zero_le_one
  have hprod (w : ι → Ω) : (∏ i, moment i (w i)) = (∏ i ∈ tested, g i (w i)) ^ q := by
    rw [show (∏ i, moment i (w i)) = ∏ i ∈ tested, g i (w i) ^ q from Fintype.prod_ite_mem _ _,
      Finset.prod_pow]
  apply (le_div_iff₀ (pow_pos ha q)).mpr
  calc
    _ ≤ ∏ i, ∑ x, moment i x := card_mul_le_prod_sum moment hnonneg bad _ fun w hw => by
      rw [hprod]
      exact pow_le_pow_left₀ ha.le (hbad w hw) q
    _ ≤ ∏ i : ι, (Fintype.card Ω : ℝ) * (if i ∈ tested then b else 1) := by
      apply Finset.prod_le_prod₀ fun i _ => Finset.sum_nonneg fun x _ => hnonneg i x
      intro i _
      by_cases hi : i ∈ tested
      · simpa [moment, hi] using hmoment i hi
      · simp [moment, hi, nsmul_eq_mul]
    _ = _ := by rw [Finset.prod_mul_distrib, Fintype.prod_ite_mem, Finset.prod_const,
      Finset.prod_const, Finset.card_univ]

/-- Multiplying by a nonzero frequency permutes the coordinate alphabet, so a
single moment bound applies to every nonzero frequency. -/
public theorem card_le_of_frequency_prod_ge_of_moment {ι K : Type*}
    [Fintype ι] [DecidableEq ι] [GroupWithZero K] [Fintype K]
    (tested : Finset ι) (g : K → ℝ) (hg : ∀ x, 0 ≤ g x)
    (bad : Finset (ι → K)) (q : ℕ) {a b : ℝ} (ha : 0 < a)
    {frequency : K} (hf : frequency ≠ 0)
    (hbad : ∀ w ∈ bad, a ≤ ∏ i ∈ tested, g (w i * frequency))
    (hmoment : (∑ x, g x ^ q) ≤ (Fintype.card K : ℝ) * b) :
    (bad.card : ℝ) ≤ (Fintype.card K : ℝ) ^ Fintype.card ι * b ^ tested.card / a ^ q := by
  refine card_le_of_prod_ge_of_coordinate_moment tested (fun _ x => g (x * frequency))
    (fun _ x => hg (x * frequency)) bad q ha hbad (fun _ _ => ?_)
  have hperm : (∑ x, g (x * frequency) ^ q) = ∑ x, g x ^ q :=
    Fintype.sum_equiv (Equiv.mulRight₀ frequency hf) _ _ (fun _ => rfl)
  exact hperm.trans_le hmoment

end Bernoulli
