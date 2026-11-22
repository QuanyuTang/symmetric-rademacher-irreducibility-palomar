module

public import Bernoulli.ZetaEulerDerivative
public import Bernoulli.ZetaEulerCoefficients
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic

/-! Regrouping the prime-ideal logarithmic derivative by norms of prime powers. -/

open IsDedekindDomain NumberField
namespace Bernoulli

variable (K : Type*) [Field K] [NumberField K]

private abbrev PrimeIdeal := HeightOneSpectrum (𝓞 K)

private theorem absNorm_eq_primeBelow_pow (P : PrimeIdeal K) :
    P.asIdeal.absNorm = (rationalPrimeBelow K P : ℕ) ^ P.asIdeal.inertiaDeg ℤ :=
  (Ideal.absNorm_pow_inertiaDeg (P.asIdeal.under ℤ) P.asIdeal).symm

private noncomputable def powerIndex (u : PrimeIdeal K × ℕ) : ℕ :=
  u.1.asIdeal.absNorm ^ (u.2 + 1)

private theorem powerIndex_eq (u : PrimeIdeal K × ℕ) :
    powerIndex K u =
      (rationalPrimeBelow K u.1 : ℕ) ^ (u.1.asIdeal.inertiaDeg ℤ * (u.2 + 1)) := by
  rw [powerIndex, absNorm_eq_primeBelow_pow, pow_mul]

private theorem isPrimePow_powerIndex (u : PrimeIdeal K × ℕ) : IsPrimePow (powerIndex K u) := by
  rw [powerIndex_eq]
  exact (rationalPrimeBelow K u.1).prop.isPrimePow.pow
    (Nat.mul_ne_zero (Ideal.inertiaDeg_pos u.1.asIdeal ℤ).ne' (Nat.succ_ne_zero _))

private theorem powerIndex_eq_prime_pow {p : Nat.Primes} {m : ℕ} (hm : m ≠ 0)
    (u : PrimeIdeal K × ℕ) (hu : powerIndex K u = (p : ℕ) ^ m) :
    rationalPrimeBelow K u.1 = p ∧ u.1.asIdeal.inertiaDeg ℤ * (u.2 + 1) = m := by
  rw [powerIndex_eq] at hu
  obtain ⟨h₁, h₂⟩ := (rationalPrimeBelow K u.1).prop.pow_inj' p.prop
    (Nat.mul_ne_zero (Ideal.inertiaDeg_pos u.1.asIdeal ℤ).ne' (Nat.succ_ne_zero _)) hm hu
  exact ⟨Subtype.ext h₁, h₂⟩

private noncomputable def primePowerFiberEquiv (p : Nat.Primes) {m : ℕ} (hm : m ≠ 0) :
    {u : PrimeIdeal K × ℕ // powerIndex K u = (p : ℕ) ^ m} ≃
      {P : {P : PrimeIdeal K // rationalPrimeBelow K P = p} // P.val.asIdeal.inertiaDeg ℤ ∣ m} := by
  let f (u : {u : PrimeIdeal K × ℕ // powerIndex K u = (p : ℕ) ^ m}) :
      {P : {P : PrimeIdeal K // rationalPrimeBelow K P = p} // P.val.asIdeal.inertiaDeg ℤ ∣ m} :=
    ⟨⟨u.val.1, (powerIndex_eq_prime_pow K hm u.val u.2).1⟩,
      ⟨u.val.2 + 1, (powerIndex_eq_prime_pow K hm u.val u.2).2.symm⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    have hP : a.val.1 = b.val.1 := congrArg (fun u => u.val.val) hab
    have he := a.2.trans b.2.symm
    change a.val.1.asIdeal.absNorm ^ (a.val.2 + 1) =
      b.val.1.asIdeal.absNorm ^ (b.val.2 + 1) at he
    rw [hP] at he
    exact Subtype.ext (Prod.ext hP (Nat.add_right_cancel
      ((Nat.pow_right_injective (one_lt_absNorm_heightOne K b.val.1)) he)))
  · intro P
    obtain ⟨k, hk⟩ := P.2
    have hk₀ : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr fun h => hm (by simpa [h] using hk)
    have he : powerIndex K (P.val.val, k - 1) = (p : ℕ) ^ m := by
      rw [powerIndex_eq]
      change (rationalPrimeBelow K P.val.val : ℕ) ^
        (P.val.val.asIdeal.inertiaDeg ℤ * (k - 1 + 1)) = (p : ℕ) ^ m
      rw [P.val.2, Nat.sub_add_cancel hk₀, ← hk]
    exact ⟨⟨⟨P.val.val, k - 1⟩, he⟩, Subtype.ext (Subtype.ext rfl)⟩

private theorem natCast_pow_cpow (a m : ℕ) (s : ℂ) :
    ((a ^ m : ℕ) : ℂ) ^ s = ((a : ℂ) ^ s) ^ m := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ a, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

private noncomputable def idealPowerTerm (s : ℂ) (u : PrimeIdeal K × ℕ) : ℂ :=
  (Real.log u.1.asIdeal.absNorm : ℂ) * primeIdealNormPower K u.1 s ^ (u.2 + 1)

private theorem primePowerFiber_sum (s : ℂ) (p : Nat.Primes) {m : ℕ} (hm : m ≠ 0) :
    (∑' u : {u : PrimeIdeal K × ℕ // powerIndex K u = (p : ℕ) ^ m}, idealPowerTerm K s u.val) =
      (dedekindMangoldt K ((p : ℕ) ^ m) : ℂ) * (((p : ℕ) ^ m : ℕ) : ℂ) ^ (-s) := by
  classical
  let q : Ideal ℤ := Ideal.span ({((p : ℕ) : ℤ)} : Set ℤ)
  let : Fact p.val.Prime := ⟨p.prop⟩
  let hq : q.IsMaximal := Int.ideal_span_isMaximal_of_prime p.val
  let : q.IsPrime := hq.isPrime
  let V := {P : q.primesOver (𝓞 K) // P.val.inertiaDeg ℤ ∣ m}
  let U := {u : PrimeIdeal K × ℕ // powerIndex K u = (p : ℕ) ^ m}
  let e : U ≃ V := (primePowerFiberEquiv K p hm).trans
    ((rationalPrimeBelowFiber K p).subtypeEquiv fun _ => Iff.rfl)
  let z : ℂ := (((p : ℕ) ^ m : ℕ) : ℂ) ^ (-s)
  let L : ℂ := (Real.log (p : ℕ) : ℂ)
  have hu (u : U) : idealPowerTerm K s u.val = ((e u).val.val.inertiaDeg ℤ : ℂ) * L * z := by
    have hp := (powerIndex_eq_prime_pow K hm u.val u.2).1
    have hNorm := absNorm_eq_primeBelow_pow K u.val.1
    rw [hp] at hNorm
    have hI : (e u).val.val = u.val.1.asIdeal := rfl
    unfold idealPowerTerm primeIdealNormPower
    rw [← natCast_pow_cpow, show u.val.1.asIdeal.absNorm ^ (u.val.2 + 1) = (p : ℕ) ^ m from u.2,
      hNorm, Nat.cast_pow, Real.log_pow, Complex.ofReal_mul, Complex.ofReal_natCast, hI]
  change (∑' u : U, idealPowerTerm K s u.val) = _
  rw [← e.symm.tsum_eq (fun u : U => idealPowerTerm K s u.val)]
  simp_rw [hu, Equiv.apply_symm_apply]
  change (∑' P : V, (P.val.val.inertiaDeg ℤ : ℂ) * L * z) =
    (dedekindMangoldt K ((p : ℕ) ^ m) : ℂ) * z
  let W : Set (q.primesOver (𝓞 K)) := {P | P.val.inertiaDeg ℤ ∣ m}
  let f (P : q.primesOver (𝓞 K)) : ℂ := (P.val.inertiaDeg ℤ : ℂ) * L * z
  have hsum : (∑' P : V, (P.val.val.inertiaDeg ℤ : ℂ) * L * z) =
      ∑ P : q.primesOver (𝓞 K), if P.val.inertiaDeg ℤ ∣ m then f P else 0 := by
    change (∑' P : W, f P.val) = _
    rw [tsum_subtype W f, tsum_fintype]
    simp only [Set.indicator_apply, W, Set.mem_ofPred_eq]
  have hweight : (dedekindPrimePowerWeight K (p : ℕ) m : ℂ) =
      L * ∑ P : q.primesOver (𝓞 K), if P.val.inertiaDeg ℤ ∣ m then (P.val.inertiaDeg ℤ : ℂ) else 0 := by
    rw [dedekindPrimePowerWeight_of_prime]
    change ((Real.log (p : ℕ) * ((∑ P : q.primesOver (𝓞 K),
      if P.val.inertiaDeg ℤ ∣ m then P.val.inertiaDeg ℤ else 0) : ℕ) : ℝ) : ℂ) = _
    push_cast [L]
    simp only [apply_ite Complex.ofReal, Complex.ofReal_natCast, Complex.ofReal_zero]
  rw [hsum, dedekindMangoldt_prime_pow K p.prop hm, hweight, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun P _ => ?_
  by_cases h : P.val.inertiaDeg ℤ ∣ m <;> simp [h, L, f, mul_comm]

private theorem allPrimePowerFibers_sum (s : ℂ) (n : ℕ) :
    (∑' u : {u : PrimeIdeal K × ℕ // powerIndex K u = n}, idealPowerTerm K s u.val) =
      (dedekindMangoldt K n : ℂ) * (n : ℂ) ^ (-s) := by
  by_cases hn : IsPrimePow n
  · obtain ⟨p, m, hp, hm, rfl⟩ := hn
    exact primePowerFiber_sum K s ⟨p, Nat.prime_iff.mpr hp⟩ hm.ne'
  · have : IsEmpty {u : PrimeIdeal K × ℕ // powerIndex K u = n} :=
      ⟨fun u => hn (u.2 ▸ isPrimePow_powerIndex K u.val)⟩
    simp [dedekindMangoldt, hn]

/-- The ordinary Dirichlet series of the Dedekind Mangoldt coefficients is the
negative logarithmic derivative of the Dedekind zeta function. -/
public theorem neg_logDeriv_dedekindZeta_eq_tsum {s : ℂ} (hs : 1 < s.re) :
    -logDeriv (NumberField.dedekindZeta K) s =
      ∑' n : ℕ, (dedekindMangoldt K (n + 1) : ℂ) * ((n + 1 : ℝ) : ℂ) ^ (-s) := by
  have hsum : Summable (idealPowerTerm K s) :=
    (summable_norm_primeIdealLogEulerSeries K hs).of_norm
  have hgroup := hsum.hasSum.tsum_fiberwise (powerIndex K)
  have hfull : HasSum (fun n : ℕ => (dedekindMangoldt K n : ℂ) * (n : ℂ) ^ (-s))
      (∑' u, idealPowerTerm K s u) :=
    hgroup.congr_fun (fun n => (allPrimePowerFibers_sum K s n).symm)
  have hshift : (∑' n : ℕ, (dedekindMangoldt K n : ℂ) * (n : ℂ) ^ (-s)) =
      ∑' n : ℕ, (dedekindMangoldt K (n + 1) : ℂ) * ((n + 1 : ℝ) : ℂ) ^ (-s) := by
    rw [hfull.summable.tsum_eq_zero_add]
    simp only [dedekindMangoldt_zero, Complex.ofReal_zero, zero_mul, zero_add, Nat.cast_add,
      Nat.cast_one, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one]
  rw [neg_logDeriv_dedekindZeta_eq_tsum_primeIdeal K hs, ← hshift, hfull.tsum_eq,
    hsum.tsum_prod' (fun P => (hasSum_primeIdealLogEulerTerm K hs P).summable)]
  exact tsum_congr (fun P => (hasSum_primeIdealLogEulerTerm K hs P).tsum_eq.symm)

end Bernoulli
