module

public import Bernoulli.ZetaEuler
public import Bernoulli.NumberFieldPrimes
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.Field
import Mathlib.Tactic

/-! Degree-uniform lower bounds from the prime-ideal Euler product. -/

public section

open IsDedekindDomain NumberField

namespace Bernoulli

variable (K : Type*) [Field K] [NumberField K]

/-- The rational prime beneath a nonzero prime ideal. -/
@[expose] noncomputable def rationalPrimeBelow (P : HeightOneSpectrum (𝓞 K)) : Nat.Primes :=
  ⟨(P.asIdeal.under ℤ).absNorm,
    (Int.prime_absNorm _).mpr (Ideal.prime_of_isPrime (Ideal.under_ne_bot ℤ P.ne_bot) inferInstance)⟩

/-- The fiber over a rational prime identifies with the usual `primesOver` type. -/
@[expose] noncomputable def rationalPrimeBelowFiber (p : Nat.Primes) :
    {P : HeightOneSpectrum (𝓞 K) // rationalPrimeBelow K P = p} ≃
      (Ideal.span ({((p : ℕ) : ℤ)} : Set ℤ)).primesOver (𝓞 K) where
  toFun P := ⟨P.val.asIdeal, P.val.isPrime, ⟨by
    have hp := congrArg Subtype.val P.2
    change (P.val.asIdeal.under ℤ).absNorm = (p : ℕ) at hp
    rw [← hp, Int.ideal_span_absNorm_eq_self]⟩⟩
  invFun P := by
    let q := Ideal.span ({((p : ℕ) : ℤ)} : Set ℤ)
    have hq : q ≠ ⊥ := fun h => p.prop.ne_zero (by
      simpa [q] using congrArg Ideal.absNorm h)
    have hP : P.val ≠ ⊥ := Ideal.ne_bot_of_mem_primesOver hq P.2
    refine ⟨⟨P.val, P.2.1, hP⟩, Subtype.ext ?_⟩
    change (P.val.under ℤ).absNorm = (p : ℕ)
    rw [← P.val.over_def q]
    simp [q]
  left_inv P := Subtype.ext (HeightOneSpectrum.ext rfl)
  right_inv P := Subtype.ext rfl

private theorem le_norm_of_rationalPrimeBelow (P : HeightOneSpectrum (𝓞 K)) :
    (rationalPrimeBelow K P : ℕ) ≤ P.asIdeal.absNorm := by
  rw [← Ideal.absNorm_pow_inertiaDeg (P.asIdeal.under ℤ) P.asIdeal]
  exact le_self_pow₀ (rationalPrimeBelow K P).prop.one_lt.le
    (Ideal.inertiaDeg_pos P.asIdeal ℤ).ne'

/-- The prime-ideal norm series is bounded by the rational integer series times the degree. -/
theorem primeNormSum_le {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun P : HeightOneSpectrum (𝓞 K) => (P.asIdeal.absNorm : ℝ) ^ (-σ)) ∧
      (∑' P : HeightOneSpectrum (𝓞 K), (P.asIdeal.absNorm : ℝ) ^ (-σ)) ≤
        (Module.finrank ℚ K : ℝ) * (∑' n : ℕ, (n : ℝ) ^ (-σ)) := by
  classical
  let f (P : HeightOneSpectrum (𝓞 K)) := (P.asIdeal.absNorm : ℝ) ^ (-σ)
  let g (p : Nat.Primes) := (Module.finrank ℚ K : ℝ) * (p.val : ℝ) ^ (-σ)
  have hf (P : HeightOneSpectrum (𝓞 K)) : 0 ≤ f P := by positivity
  have hnat : Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hprime : Summable (g) := (hnat.comp_injective Subtype.val_injective).mul_left _
  let e := Equiv.sigmaFiberEquiv (rationalPrimeBelow K)
  have hfiber (p : Nat.Primes) :
      Summable (fun P : {P // rationalPrimeBelow K P = p} => f P.val) ∧
        (∑' P : {P // rationalPrimeBelow K P = p}, f P.val) ≤ g p := by
    let : Fact p.val.Prime := ⟨p.prop⟩
    let q : Ideal ℤ := Ideal.span ({(p.val : ℤ)} : Set ℤ)
    let hq : q.IsMaximal := Int.ideal_span_isMaximal_of_prime p.val
    let : q.IsPrime := hq.isPrime
    let : Fintype {P // rationalPrimeBelow K P = p} := Fintype.ofEquiv _ (rationalPrimeBelowFiber K p).symm
    have hcard := (Nat.card_congr (rationalPrimeBelowFiber K p)).le.trans
      (card_primesOver_le_finrank (K := K) p.val)
    refine ⟨Summable.of_finite, ?_⟩
    rw [tsum_fintype]
    calc
      _ ≤ ∑ _P : {P // rationalPrimeBelow K P = p}, (p.val : ℝ) ^ (-σ) := by
        apply Finset.sum_le_sum
        intro P _
        apply Real.rpow_le_rpow_of_nonpos (by exact_mod_cast p.prop.pos) _ (by linarith)
        exact_mod_cast P.2 ▸ le_norm_of_rationalPrimeBelow K P.val
      _ ≤ g p := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, ← Nat.card_eq_fintype_card]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
  have houter : Summable (fun p : Nat.Primes => ∑' P : {P // rationalPrimeBelow K P = p}, f P.val) :=
    hprime.of_nonneg_of_le (fun _ => tsum_nonneg fun P => hf P.val) fun p => (hfiber p).2
  have hsigma : Summable (f ∘ e) :=
    (summable_sigma_of_nonneg fun a => hf (e a)).mpr ⟨fun p => (hfiber p).1, houter⟩
  refine ⟨e.summable_iff.mp hsigma, ?_⟩
  rw [← e.tsum_eq f]
  change (∑' P, (f ∘ e) P) ≤ _
  rw [hsigma.tsum_sigma' (fun p => (hfiber p).1)]
  refine (houter.tsum_le_tsum (fun p => (hfiber p).2) hprime).trans ?_
  rw [show (∑' p : Nat.Primes, g p) = (Module.finrank ℚ K : ℝ) *
      (∑' p : Nat.Primes, (p.val : ℝ) ^ (-σ)) from tsum_mul_left]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply le_of_tendsto' (hnat.comp_injective
    (Subtype.val_injective (p := Nat.Prime))).hasSum
  intro S
  calc
    _ = ∑ n ∈ S.image Subtype.val, (n : ℝ) ^ (-σ) :=
      (Finset.sum_image Subtype.val_injective.injOn).symm
    _ ≤ _ := hnat.sum_le_tsum _ (fun _ _ => by positivity)

private theorem exp_neg_norm_le_eulerFactor {s : ℂ} (hs : 1 < s.re)
    (P : HeightOneSpectrum (𝓞 K)) :
    Real.exp (-((P.asIdeal.absNorm : ℝ) ^ (-s.re))) ≤ ‖dedekindEulerFactor K s P‖ := by
  let r := (P.asIdeal.absNorm : ℂ) ^ (-s)
  have hp : 1 < (P.asIdeal.absNorm : ℝ) := by exact_mod_cast one_lt_absNorm_heightOne K P
  have hnorm : ‖r‖ = (P.asIdeal.absNorm : ℝ) ^ (-s.re) := by
    dsimp [r]
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hp),
      Complex.neg_re]
  have hr : ‖r‖ < 1 := by rw [hnorm]; exact Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hne : 1 - r ≠ 0 := by
    intro h
    have he := (sub_eq_zero.mp h).symm
    simp [he] at hr
  have hpos : 0 < ‖1 - r‖ := norm_pos_iff.mpr hne
  have hle : ‖1 - r‖ ≤ Real.exp ‖r‖ := by
    simpa [norm_one, add_comm] using (norm_sub_le (1 : ℂ) r).trans (by
      simpa [norm_one, add_comm] using Real.add_one_le_exp ‖r‖)
  rw [← hnorm, Real.exp_neg, dedekindEulerFactor, norm_inv]
  exact inv_anti₀ hpos hle

/-- The inverse Euler factors give a degree-uniform lower bound throughout the half-plane. -/
theorem dedekindZeta_norm_lower {s : ℂ} (hs : 1 < s.re) :
    Real.exp (-(Module.finrank ℚ K : ℝ) * (∑' n : ℕ, (n : ℝ) ^ (-s.re))) ≤
      ‖NumberField.dedekindZeta K s‖ := by
  classical
  let f (P : HeightOneSpectrum (𝓞 K)) := (P.asIdeal.absNorm : ℝ) ^ (-s.re)
  have hsums := primeNormSum_le K hs
  have hprod := (hasProd_dedekindZeta K hs).norm
  apply ge_of_tendsto' hprod
  intro S
  calc
    _ ≤ Real.exp (-∑ P ∈ S, f P) := by
      apply Real.exp_le_exp.mpr
      have h := (hsums.1.sum_le_tsum S (fun _ _ => by positivity)).trans hsums.2
      rw [neg_mul]
      exact neg_le_neg h
    _ = ∏ P ∈ S, Real.exp (-f P) := by rw [← Finset.sum_neg_distrib, Real.exp_sum]
    _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => Real.exp_nonneg _) fun P _ =>
      exp_neg_norm_le_eulerFactor K hs P

/-- An absolute constant controls the lower bound at every center `2 + it`, in every field. -/
theorem exists_dedekindZeta_center_norm_lower :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Type*) [Field K] [NumberField K] (t : ℝ),
      Real.exp (-C * Module.finrank ℚ K) ≤
        ‖NumberField.dedekindZeta K (2 + (t : ℂ) * Complex.I)‖ := by
  let C := ∑' n : ℕ, (n : ℝ) ^ (-(2 : ℝ))
  have hsum := Real.summable_nat_rpow.mpr (by norm_num : -(2 : ℝ) < -1)
  refine ⟨C, ?_, ?_⟩
  · have h := hsum.sum_le_tsum ({1} : Finset ℕ) (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    exact zero_lt_one.trans_le (by simpa only [Finset.sum_singleton, Nat.cast_one, Real.one_rpow] using h)
  · intro K _ _ t
    have hRe : (2 + (t : ℂ) * Complex.I).re = 2 := by simp
    simpa [hRe, mul_comm, C] using dedekindZeta_norm_lower K (s := 2 + (t : ℂ) * Complex.I) (by
      rw [hRe]; norm_num)

private theorem norm_eulerFactor_le_exp {s : ℂ} (hs : 3 / 2 ≤ s.re)
    (P : HeightOneSpectrum (𝓞 K)) :
    ‖dedekindEulerFactor K s P‖ ≤ Real.exp (2 * (P.asIdeal.absNorm : ℝ) ^ (-(3 / 2) : ℝ)) := by
  let r := (P.asIdeal.absNorm : ℂ) ^ (-s)
  have hp : (2 : ℝ) ≤ P.asIdeal.absNorm := by exact_mod_cast one_lt_absNorm_heightOne K P
  have hp₀ : (0 : ℝ) < P.asIdeal.absNorm := by positivity
  have hp₁ : (1 : ℝ) ≤ P.asIdeal.absNorm := by linarith
  have hnorm : ‖r‖ = (P.asIdeal.absNorm : ℝ) ^ (-s.re) := by
    dsimp [r]
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos hp₀, Complex.neg_re]
  have hr : ‖r‖ ≤ (P.asIdeal.absNorm : ℝ) ^ (-(3 / 2) : ℝ) := by
    rw [hnorm]
    exact Real.rpow_le_rpow_of_exponent_le hp₁ (neg_le_neg hs)
  have hhalf : ‖r‖ ≤ 1 / 2 := by
    refine hr.trans ((Real.rpow_le_rpow_of_exponent_le hp₁ (by norm_num : -(3 / 2 : ℝ) ≤ -1)).trans ?_)
    rw [Real.rpow_neg_one, one_div]
    exact inv_anti₀ (by norm_num) hp
  have hsub : 1 - ‖r‖ ≤ ‖(1 : ℂ) - r‖ := by simpa using norm_sub_norm_le (1 : ℂ) r
  have hpos : 0 < 1 - ‖r‖ := by linarith
  calc
    ‖dedekindEulerFactor K s P‖ = ‖(1 : ℂ) - r‖⁻¹ := by rw [dedekindEulerFactor, norm_inv]
    _ ≤ (1 - ‖r‖)⁻¹ := inv_anti₀ hpos hsub
    _ ≤ 1 + 2 * ‖r‖ := by
      rw [← one_div, div_le_iff₀ hpos]
      nlinarith only [mul_nonneg (norm_nonneg r) (show 0 ≤ 1 - 2 * ‖r‖ by linarith)]
    _ ≤ Real.exp (2 * ‖r‖) := by simpa [add_comm] using Real.add_one_le_exp (2 * ‖r‖)
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

/-- An absolute constant bounds the zeta norm per field degree on the half-plane
with real part at least three halves. -/
theorem exists_dedekindZeta_norm_upper :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ (K : Type*) [Field K] [NumberField K] (s : ℂ), 3 / 2 ≤ s.re →
      ‖NumberField.dedekindZeta K s‖ ≤ R ^ Module.finrank ℚ K := by
  let T := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2) : ℝ)
  refine ⟨Real.exp (2 * T), ?_, ?_⟩
  · exact Real.one_le_exp (by positivity : 0 ≤ 2 * T)
  · intro K _ _ s hs
    let f (P : HeightOneSpectrum (𝓞 K)) := (P.asIdeal.absNorm : ℝ) ^ (-(3 / 2) : ℝ)
    have hseries := primeNormSum_le K (by norm_num : (1 : ℝ) < 3 / 2)
    have hprod := (hasProd_dedekindZeta K (s := s) (by linarith)).norm
    apply le_of_tendsto' hprod
    intro S
    calc
      _ ≤ ∏ P ∈ S, Real.exp (2 * f P) :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun P _ => norm_eulerFactor_le_exp K hs P
      _ = Real.exp (2 * ∑ P ∈ S, f P) := by rw [← Real.exp_sum, Finset.mul_sum]
      _ ≤ Real.exp (2 * ((Module.finrank ℚ K : ℝ) * T)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
          ((hseries.1.sum_le_tsum S (fun _ _ => by positivity)).trans hseries.2) (by norm_num))
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end Bernoulli
