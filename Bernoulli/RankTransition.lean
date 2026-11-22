module

public import Bernoulli.RankDecoupling
public import Bernoulli.RankFourier
public import Bernoulli.RankSupport
public import Bernoulli.RankVectorSupport
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Ring

/-!
# Conditional rank estimates for a fixed symmetric block

Once the old block is fixed, the new row and column are described by independent
fair signs. A nonzero kernel vector gives a linear obstruction to the default
corank change. For an invertible block, the obstruction is a scalar Schur
complement, whose character average can be bounded by resampling.
-/

open scoped BigOperators
open Matrix

namespace Bernoulli

/-- The value in the prime field assigned to a single Boolean sign. -/
@[expose] public def fairSign {p : ℕ} (b : Bool) : ZMod p := if b then 1 else -1

/-- The constant mass of each sign assignment on a finite coordinate set. -/
@[expose] public noncomputable def fairSignWeight (ι : Type*) [Fintype ι] : ℝ :=
  (1 / 2) ^ Fintype.card ι

public theorem fairSignWeight_nonneg (ι : Type*) [Fintype ι] :
    0 ≤ fairSignWeight ι := by
  unfold fairSignWeight
  positivity

@[simp] public theorem sum_fairSignWeight (ι : Type*) [Fintype ι] [DecidableEq ι] :
    (∑ _ : ι → Bool, fairSignWeight ι) = 1 := by
  simp [fairSignWeight, Nat.cast_pow, nsmul_eq_mul]

/-! The conditions below concern approximate kernel vectors, with sparsity imposed on
their image under the old block. -/

/-- All nonzero vectors with image supported on at most the given number of
coordinates have small Fourier coefficients on every sufficiently large retained set. -/
@[expose] public def rankFourierHealthy {ι : Type*} [Fintype ι] {p : ℕ}
    (A : Matrix ι ι (ZMod p)) (r m : ℕ) (ε : ℝ) : Prop :=
  ∀ v : ι → ZMod p, v ≠ 0 → (finiteVectorSupport (A *ᵥ v)).card ≤ r →
    ∀ S : Finset ι, m ≤ S.card → ∀ a : ZMod p, a ≠ 0 →
      ∏ i ∈ S, |Real.cos (2 * Real.pi * ((v i * a).val : ℝ) / p)| ≤ ε

/-- The character average of a signed linear form factors into absolute cosines. -/
public theorem norm_character_sum_fairSign {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [NeZero p] (v : ι → ZMod p) (a : ZMod p) :
    ‖∑ σ : ι → Bool, (fairSignWeight ι : ℂ) *
      ZMod.stdAddChar (-(((fun i => fairSign (σ i)) ⬝ᵥ v) * a))‖ =
      ∏ i, |Real.cos (2 * Real.pi * ((v i * a).val : ℝ) / p)| := by
  simpa only [fairSign, fairSignWeight, dotProduct, Complex.ofReal_pow, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat] using norm_character_sum_fair_signs v a

/-- For a singular healthy block, a fixed nonzero kernel vector suffices to
bound the probability of failing to make the default corank decrement.
The bound holds even for a diagonal entry depending on the new column. -/
public theorem fairSign_corank_exception_le_of_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} [Fact p.Prime] {A : Matrix ι ι (ZMod p)} (hA : A.IsSymm)
    {v : ι → ZMod p} (hv : v ≠ 0) (hAv : A *ᵥ v = 0) {r m : ℕ}
    (hm : m ≤ Fintype.card ι) {ε : ℝ} (hε : 0 ≤ ε) (hgood : rankFourierHealthy A r m ε)
    (diag : (ι → Bool) → ZMod p) :
    (∑ σ : ι → Bool, if
      Module.finrank (ZMod p) (LinearMap.ker
        (symmetricBorder A (fun i => fairSign (σ i)) (diag σ)).mulVecLin) ≠
          Module.finrank (ZMod p) (LinearMap.ker A.mulVecLin) - 1
      then fairSignWeight ι else 0) ≤ (p : ℝ)⁻¹ + ε := by
  classical
  let q (σ : ι → Bool) := (fun i => fairSign (σ i)) ⬝ᵥ v
  have hq : ∀ a : ZMod p, a ≠ 0 →
      ‖∑ σ : ι → Bool, (fairSignWeight ι : ℂ) * ZMod.stdAddChar (-(q σ * a))‖ ≤ ε := by
    intro a ha
    have hcard : (finiteVectorSupport (A *ᵥ v)).card ≤ r := by simp [hAv]
    exact (norm_character_sum_fairSign v a).trans_le
      (hgood v hv hcard Finset.univ (by simpa using hm) a ha)
  refine le_trans ?_ (modularMass_le_of_character_bound (fun _ => fairSignWeight ι)
    q (sum_fairSignWeight ι) hε hq 0)
  refine Finset.sum_le_sum fun σ _ => ?_
  by_cases hqσ : q σ = 0
  · simp only [hqσ, ↓reduceIte]
    split
    · exact le_rfl
    · exact fairSignWeight_nonneg ι
  · let k := Module.finrank (ZMod p) (LinearMap.ker
        (symmetricBorder A (fun i => fairSign (σ i)) (diag σ)).mulVecLin)
    let l := Module.finrank (ZMod p) (LinearMap.ker A.mulVecLin)
    have hc : k + 1 = l :=
      finrank_ker_symmetricBorder_add_one
        (A := A) (x := fun i => fairSign (σ i)) (v := v) hA (diag σ) hAv hqσ
    have he : k = l - 1 := Nat.sub_eq_of_eq_add hc.symm |>.symm
    change (if k ≠ l - 1 then fairSignWeight ι else 0) ≤
      if q σ = 0 then fairSignWeight ι else 0
    rw [ite_eq_right (not_not_intro he), ite_eq_right hqσ]

end Bernoulli
