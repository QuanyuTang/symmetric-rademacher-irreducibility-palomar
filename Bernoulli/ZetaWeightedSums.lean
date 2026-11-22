module

public import Bernoulli.UniformFactorEstimate
public import Bernoulli.ZetaEulerCoefficients
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic

/-! The Mellin coefficient sum splits into the prime average and the prime-power remainder. -/

open NumberField
namespace Bernoulli

private theorem mem_primePowerIndices {x : ℝ} (hx : 1 ≤ x) {u : Sigma fun _ : ℕ => ℕ} :
    u ∈ (primesThrough (Real.sqrt x)).sigma (fun p =>
      Finset.Icc 2 ⌊Real.log x / Real.log p⌋₊) ↔
        u.1.Prime ∧ 2 ≤ u.2 ∧ (u.1 : ℝ) ^ u.2 ≤ x := by
  rw [Finset.mem_sigma, mem_primesThrough (Real.sqrt_nonneg x), Finset.mem_Icc]
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  constructor
  · rintro ⟨⟨hp, _⟩, hj, hj₁⟩
    have hp₀ : (0 : ℝ) < u.1 := by exact_mod_cast hp.pos
    have hlog : 0 < Real.log u.1 := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hquot : 0 ≤ Real.log x / Real.log u.1 := div_nonneg (Real.log_nonneg hx) hlog.le
    exact ⟨hp, hj, (Real.pow_le_iff_le_log hp₀ hx₀).mpr
      ((le_div_iff₀ hlog).mp ((Nat.le_floor_iff hquot).mp hj₁))⟩
  · rintro ⟨hp, hj, hj₁⟩
    have hp₀ : (0 : ℝ) < u.1 := by exact_mod_cast hp.pos
    have hp₁ : (1 : ℝ) ≤ u.1 := by exact_mod_cast hp.one_lt.le
    have hlog : 0 < Real.log u.1 := Real.log_pos (by exact_mod_cast hp.one_lt)
    have hquot : 0 ≤ Real.log x / Real.log u.1 := div_nonneg (Real.log_nonneg hx) hlog.le
    refine ⟨⟨hp, Real.le_sqrt_of_sq_le ((pow_le_pow_right₀ hp₁ hj).trans hj₁)⟩, hj, ?_⟩
    exact (Nat.le_floor_iff hquot).mpr ((le_div_iff₀ hlog).mpr
      ((Real.pow_le_iff_le_log hp₀ hx₀).mp hj₁))

private theorem dedekindMangoldt_weight_zero_of_lt (K : Type) [Field K] [NumberField K]
    {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : x < n) :
    dedekindMangoldt K n * weight (n / x) = 0 := by
  have hgt : 1 < (n : ℝ) / x := (lt_div_iff₀ hx).mpr (by simpa using hn)
  simp [weight, not_le_of_gt hgt]

/-- The integer-indexed sum counts prime ideals of residue degree one in its prime part. -/
public theorem tsum_dedekindMangoldt_weight (K : Type) [Field K] [NumberField K]
    {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, dedekindMangoldt K (n + 1) * weight ((n + 1 : ℝ) / x)) =
      x * primeIdealAverage K x + primePowerSum x (dedekindPrimePowerWeight K) := by
  classical
  let S := Finset.range (⌊x⌋₊ + 1)
  let F := S.filter fun n => ¬n.Prime ∧ IsPrimePow n
  let J := (primesThrough (Real.sqrt x)).sigma (fun p => Finset.Icc 2 ⌊Real.log x / Real.log p⌋₊)
  let f (n : ℕ) := dedekindMangoldt K n * weight (n / x)
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hS (n : ℕ) : n ∈ S ↔ (n : ℝ) ≤ x := by
    dsimp [S]
    rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_floor_iff hx₀.le]
  have hsupport (n : ℕ) (hn : n ∉ S) : f n = 0 :=
    dedekindMangoldt_weight_zero_of_lt K hx₀ (lt_of_not_ge (mt (hS n).mpr hn))
  have hshift :
      (∑' n : ℕ, dedekindMangoldt K (n + 1) * weight ((n + 1 : ℝ) / x)) = ∑ n ∈ S, f n := by
    have hsum : HasSum f (∑ n ∈ S, f n) := hasSum_sum_of_ne_finset_zero hsupport
    simpa [f, Nat.cast_add] using (hsum.summable.tsum_eq_zero_add.symm.trans hsum.tsum_eq)
  have hprime : (∑ p ∈ primesThrough x, f p) = x * primeIdealAverage K x := by
    rw [primeIdealAverage, primeAverage, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := ((mem_primesThrough hx₀.le).mp hp).1
    let : Fact p.Prime := ⟨hp'⟩
    have hcoeff := dedekindMangoldt_prime_pow K hp' (m := 1) (by decide)
    rw [pow_one, dedekindPrimePowerWeight_of_prime, primePowerCoefficient_one] at hcoeff
    dsimp [f, primeWeight, primeIdealCount]
    rw [hcoeff]
    field_simp
  have hF : F = J.image (fun u => u.1 ^ u.2) := by
    ext n
    rw [Finset.mem_image]
    constructor
    · intro hn
      obtain ⟨hnx, hnp, hpow⟩ := Finset.mem_filter.mp hn
      obtain ⟨p, m, hp, hm, rfl⟩ := hpow
      have hp' := Nat.prime_iff.mpr hp
      have hm' : 2 ≤ m := by
        by_contra! h
        have hm₁ : m = 1 := by omega
        exact hnp (by simpa [hm₁] using hp')
      exact ⟨⟨p, m⟩, (mem_primePowerIndices hx).mpr ⟨hp', hm', by simpa using (hS _).mp hnx⟩, rfl⟩
    · rintro ⟨⟨p, m⟩, hj, rfl⟩
      obtain ⟨hp, hm, hpx⟩ := (mem_primePowerIndices hx).mp hj
      change p.Prime at hp
      change 2 ≤ m at hm
      have hm₀ : m ≠ 0 := by omega
      have hnp : ¬(p ^ m).Prime := by
        intro hn
        have h := (hp.pow_inj' hn (m := m) (n := 1) hm₀ (by decide) (by rw [pow_one])).2
        omega
      exact Finset.mem_filter.mpr ⟨(hS _).mpr (by simpa using hpx), hnp, hp.isPrimePow.pow hm₀⟩
  have hpower : (∑ n ∈ F, f n) = primePowerSum x (dedekindPrimePowerWeight K) := by
    rw [hF, Finset.sum_image]
    · rw [primePowerSum, Finset.sum_sigma' _ _ (fun p m =>
        dedekindPrimePowerWeight K p m * weight ((p : ℝ) ^ m / x))]
      refine Finset.sum_congr rfl fun ⟨p, m⟩ hpm => ?_
      obtain ⟨hp, hm, _⟩ := (mem_primePowerIndices hx).mp hpm
      change 2 ≤ m at hm
      simp [f, dedekindMangoldt_prime_pow K hp (by omega : m ≠ 0)]
    · intro ⟨p, m⟩ hpm ⟨q, j⟩ hqj he
      obtain ⟨hp, hm, _⟩ := (mem_primePowerIndices hx).mp hpm
      obtain ⟨hq, hj, _⟩ := (mem_primePowerIndices hx).mp hqj
      change p.Prime at hp
      change q.Prime at hq
      change 2 ≤ m at hm
      change 2 ≤ j at hj
      change p ^ m = q ^ j at he
      obtain ⟨rfl, rfl⟩ := hp.pow_inj' hq (m := m) (n := j) (by omega) (by omega) he
      rfl
  have hnonprime : (∑ n ∈ S.filter (fun n => ¬n.Prime), f n) = ∑ n ∈ F, f n := by
    symm
    apply Finset.sum_subset (fun n hn => Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hn).1, (Finset.mem_filter.mp hn).2.1⟩)
    intro n hn hn'
    have hpow : ¬IsPrimePow n := fun h => hn' (Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hn).1, (Finset.mem_filter.mp hn).2, h⟩)
    simp [f, dedekindMangoldt, hpow]
  rw [hshift, ← Finset.sum_filter_add_sum_filter_not S Nat.Prime f, hnonprime, hpower]
  exact congrArg (fun a => a + primePowerSum x (dedekindPrimePowerWeight K)) hprime

end Bernoulli
