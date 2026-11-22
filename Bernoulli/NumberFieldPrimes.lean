module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Mathlib.RingTheory.Ideal.Int
public import Mathlib.RingTheory.RamificationInertia.Basic

/-!
# Bounds on primes of prescribed norm

The sum of the products of the ramification indices and inertia degrees over
a rational prime is the degree of the number field. Each summand is positive.
-/

public section

open NumberField
open scoped BigOperators

namespace Bernoulli

private noncomputable def primeOfNormToPrimesOver {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime]
    (P : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ P.cardQuot = p}) :
    (Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver (𝓞 K) := by
  let : Infinite (𝓞 K) := Infinite.of_injective (fun z : ℤ => (z : 𝓞 K)) Int.cast_injective
  refine ⟨P, P.2.1, ⟨?_⟩⟩
  have hnorm : P.1.absNorm = p := P.2.2.2
  have h := Ideal.span_singleton_absNorm (I := P.1) (hnorm.symm ▸ (Fact.out : p.Prime))
  simpa [Ideal.under_def, hnorm] using h

private theorem primeOfNormToPrimesOver_injective {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : Function.Injective (primeOfNormToPrimesOver (K := K) p) := by
  intro P Q h
  apply Subtype.ext
  exact congrArg (fun T : (Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver (𝓞 K) => T.1) h

/-- The number of prime ideals above a rational prime is at most the degree. -/
theorem card_primesOver_le_finrank {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    Nat.card ((Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver (𝓞 K)) ≤ Module.finrank ℚ K := by
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  let hq : q.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  let : q.IsPrime := hq.isPrime
  change Nat.card (q.primesOver (𝓞 K)) ≤ _
  rw [Nat.card_eq_fintype_card, ← RingOfIntegers.rank K,
    ← Ideal.sum_ramification_inertia_eq_finrank q (𝓞 K)]
  calc
    _ = ∑ _P : q.primesOver (𝓞 K), 1 := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro P _
      exact Nat.succ_le_of_lt (Nat.mul_pos
        (Ideal.ramificationIdx_pos (q := (P : Ideal (𝓞 K))) (R := ℤ))
        (Ideal.inertiaDeg_pos (P : Ideal (𝓞 K)) ℤ))

/-- The number of nonzero prime ideals of a specified prime norm is at most
the degree of the number field. -/
theorem card_primeIdeals_of_norm_le_finrank {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] :
    Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ P.cardQuot = p} ≤ Module.finrank ℚ K := by
  let : (Ideal.span ({(p : ℤ)} : Set ℤ)).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  exact (Nat.card_le_card_of_injective _ (primeOfNormToPrimesOver_injective p)).trans
    (card_primesOver_le_finrank p)

/-- Exactly one nonzero prime ideal of the rational field has norm `p`. -/
theorem card_primeIdeals_rat_eq_one (p : ℕ) [Fact p.Prime] :
    Nat.card {P : Ideal (𝓞 ℚ) // P.IsPrime ∧ P ≠ ⊥ ∧ P.cardQuot = p} = 1 := by
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  let hq : q.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  let : q.IsPrime := hq.isPrime
  let : Infinite (𝓞 ℚ) := Infinite.of_injective (fun z : ℤ => (z : 𝓞 ℚ)) Int.cast_injective
  apply le_antisymm (by simpa using card_primeIdeals_of_norm_le_finrank (K := ℚ) p)
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 ℚ) q
  let Q : q.primesOver (𝓞 ℚ) := ⟨P, hP.isPrime, hPQ⟩
  have hsum : ∑ Q' : q.primesOver (𝓞 ℚ), Q'.1.ramificationIdx ℤ * Q'.1.inertiaDeg ℤ = 1 := by
    rw [Ideal.sum_ramification_inertia_eq_finrank, RingOfIntegers.rank, Module.finrank_self]
  have hram : 1 ≤ Q.1.ramificationIdx ℤ := Nat.succ_le_of_lt
    (Ideal.ramificationIdx_pos (q := Q.1) (R := ℤ))
  have hInertia : Q.1.inertiaDeg ℤ = 1 := by
    apply le_antisymm _ (Nat.succ_le_of_lt (Ideal.inertiaDeg_pos Q.1 ℤ))
    calc
      _ = 1 * Q.1.inertiaDeg ℤ := (Nat.one_mul _).symm
      _ ≤ Q.1.ramificationIdx ℤ * Q.1.inertiaDeg ℤ := Nat.mul_le_mul_right _ hram
      _ ≤ ∑ Q' : q.primesOver (𝓞 ℚ), Q'.1.ramificationIdx ℤ * Q'.1.inertiaDeg ℤ :=
        Finset.single_le_sum
          (f := fun Q' : q.primesOver (𝓞 ℚ) => Q'.1.ramificationIdx ℤ * Q'.1.inertiaDeg ℤ)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ Q)
      _ = 1 := hsum
  have hqNorm : q.absNorm = p := by simp [q]
  have hnorm : Q.1.absNorm = p := by
    rw [← Ideal.absNorm_pow_inertiaDeg q Q.1, hqNorm, hInertia, pow_one]
  have hne : Q.1 ≠ ⊥ := fun h => (Fact.out : p.Prime).ne_zero
    (hnorm.symm.trans (Ideal.absNorm_eq_zero_iff.mpr h))
  let : Finite {P : Ideal (𝓞 ℚ) // P.IsPrime ∧ P ≠ ⊥ ∧ P.cardQuot = p} :=
    Finite.of_injective _ (primeOfNormToPrimesOver_injective (K := ℚ) p)
  exact Nat.succ_le_of_lt (Nat.card_pos_iff.mpr ⟨⟨⟨Q.1, Q.2.1, hne, hnorm⟩⟩, inferInstance⟩)

/-- The integer coefficient in the logarithmic Euler factor at `p^m`. The logarithmic
derivative multiplies this coefficient by `log p`. -/
@[expose] noncomputable def primePowerCoefficient {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (m : ℕ) : ℕ := by
  classical
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  let hq : q.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  let : q.IsPrime := hq.isPrime
  exact ∑ P : q.primesOver (𝓞 K),
    if P.1.inertiaDeg ℤ ∣ m then P.1.inertiaDeg ℤ else 0

theorem primePowerCoefficient_le_finrank {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] (m : ℕ) :
    primePowerCoefficient (K := K) p m ≤ Module.finrank ℚ K := by
  classical
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  let hq : q.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  let : q.IsPrime := hq.isPrime
  unfold primePowerCoefficient
  dsimp only
  rw [← RingOfIntegers.rank K, ← Ideal.sum_ramification_inertia_eq_finrank q (𝓞 K)]
  apply Finset.sum_le_sum
  intro P _
  split
  · exact (Nat.one_mul _).symm.le.trans (Nat.mul_le_mul_right _
      (Nat.succ_le_of_lt (Ideal.ramificationIdx_pos (q := P.1) (R := ℤ))))
  · exact Nat.zero_le _

/-- At the first power of `p`, precisely the ideals of norm `p` contribute. -/
theorem primePowerCoefficient_one {K : Type*} [Field K] [NumberField K]
    (p : ℕ) [Fact p.Prime] : primePowerCoefficient (K := K) p 1 =
      Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ P.cardQuot = p} := by
  classical
  let q : Ideal ℤ := Ideal.span {(p : ℤ)}
  let hq : q.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  let : q.IsPrime := hq.isPrime
  let : Infinite (𝓞 K) := Infinite.of_injective (fun z : ℤ => (z : 𝓞 K)) Int.cast_injective
  have hqNorm : q.absNorm = p := by simp [q]
  have norm_eq (Q : q.primesOver (𝓞 K)) : Q.1.absNorm = p ^ Q.1.inertiaDeg ℤ := by
    rw [← Ideal.absNorm_pow_inertiaDeg q Q.1, hqNorm]
  let equivalence : {Q : q.primesOver (𝓞 K) // Q.1.inertiaDeg ℤ = 1} ≃
      {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ P.cardQuot = p} := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro Q
      have hnorm : Q.1.1.absNorm = p := by rw [norm_eq, Q.2, pow_one]
      have hne : Q.1.1 ≠ ⊥ := fun h => (Fact.out : p.Prime).ne_zero
        (hnorm.symm.trans (Ideal.absNorm_eq_zero_iff.mpr h))
      exact ⟨Q.1.1, Q.1.2.1, hne, hnorm⟩
    · intro P
      let Q : q.primesOver (𝓞 K) := primeOfNormToPrimesOver p P
      have hnorm : Q.1.absNorm = p := P.2.2.2
      refine ⟨Q, (Nat.pow_right_injective (Fact.out : p.Prime).two_le) ?_⟩
      change p ^ Q.1.inertiaDeg ℤ = p ^ (1 : ℕ)
      rw [pow_one, ← norm_eq Q, hnorm]
    · intro Q
      exact Subtype.ext (Subtype.ext rfl)
    · intro P
      exact Subtype.ext rfl
  change (∑ Q : q.primesOver (𝓞 K), if Q.1.inertiaDeg ℤ ∣ 1 then Q.1.inertiaDeg ℤ else 0) = _
  calc
    _ = ∑ Q : q.primesOver (𝓞 K), if Q.1.inertiaDeg ℤ = 1 then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro Q _
      by_cases h : Q.1.inertiaDeg ℤ = 1 <;> simp [h, Nat.dvd_one]
    _ = Nat.card {Q : q.primesOver (𝓞 K) // Q.1.inertiaDeg ℤ = 1} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_eq_sum_ones,
        Finset.sum_filter]
    _ = _ := Nat.card_congr equivalence

end Bernoulli
