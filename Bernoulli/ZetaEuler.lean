module

public import Bernoulli.ZetaEulerSeries
public import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finsupp.Order
import Mathlib.Tactic

/-! The prime-ideal Euler product for the Dedekind zeta function in `1 < re s`. -/

public section

open IsDedekindDomain NumberField UniqueFactorizationMonoid

namespace Bernoulli

section GeometricProduct

variable {α : Type*} [DecidableEq α]

private noncomputable def insertSupportEquiv {a : α} {S : Finset α} (ha : a ∉ S) :
    {f : α →₀ ℕ // f.support = insert a S} ≃ ℕ × {f : α →₀ ℕ // f.support = S} where
  toFun f := (f.val a - 1, ⟨f.val.erase a, by simp [f.2, ha]⟩)
  invFun g := ⟨Finsupp.single a (g.1 + 1) + g.2.val, by
    rw [Finsupp.support_add_eq_union, Finsupp.support_single _ (Nat.succ_ne_zero _), g.2.2,
      Finset.singleton_union]⟩
  left_inv f := by
    have hfa : f.val a ≠ 0 := Finsupp.mem_support_iff.mp (by rw [f.2]; simp)
    apply Subtype.ext
    apply Finsupp.ext
    intro x
    by_cases hx : x = a
    · subst x
      simp [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hfa)]
    · simp [Finsupp.single_eq_of_ne hx, hx]
  right_inv g := by
    have hga : g.2.val a = 0 := Finsupp.notMem_support_iff.mp (by rw [g.2.2]; exact ha)
    apply Prod.ext
    · simp [hga]
    · apply Subtype.ext
      apply Finsupp.ext
      intro x
      by_cases hx : x = a
      · subst x
        simp [hga]
      · simp [hx]

private theorem hasSum_finsupp_pow_support (r : α → ℂ) (hr : ∀ a, ‖r a‖ < 1)
    (hsum : Summable (fun f : α →₀ ℕ => f.prod fun a m => r a ^ m)) (S : Finset α) :
    HasSum (fun f : {f : α →₀ ℕ // f.support = S} => f.val.prod fun a m => r a ^ m)
      (∏ a ∈ S, ∑' m : ℕ, r a ^ (m + 1)) := by
  induction S using Finset.induction_on with
  | empty =>
    let : Unique {f : α →₀ ℕ // f.support = ∅} :=
      ⟨⟨⟨0, rfl⟩⟩, fun f => Subtype.ext (Finsupp.support_eq_empty.mp f.2)⟩
    simpa [Unique.default_eq (⟨0, rfl⟩ : {f : α →₀ ℕ // f.support = ∅})] using
      hasSum_fintype (fun f : {f : α →₀ ℕ // f.support = ∅} => f.val.prod fun a m => r a ^ m)
  | insert a S ha ih =>
    let e := insertSupportEquiv ha
    have hfact (g : ℕ × {f : α →₀ ℕ // f.support = S}) :
        (e.symm g).val.prod (fun b m => r b ^ m) = r a ^ (g.1 + 1) *
          g.2.val.prod (fun b m => r b ^ m) := by
      change (Finsupp.single a (g.1 + 1) + g.2.val).prod _ = _
      rw [Finsupp.prod_add_index' (fun b => pow_zero (r b)) (fun b i j => pow_add (r b) i j),
        Finsupp.prod_single_index (h := fun b m => r b ^ m) (pow_zero (r a))]
    have hprod : Summable (fun g : ℕ × {f : α →₀ ℕ // f.support = S} =>
        r a ^ (g.1 + 1) * g.2.val.prod (fun b m => r b ^ m)) := by
      exact ((e.symm.summable_iff).mpr (hsum.comp_injective Subtype.val_injective)).congr hfact
    have h₁ : Summable (fun m : ℕ => r a ^ (m + 1)) :=
      (summable_nat_add_iff 1).mpr (summable_geometric_of_norm_lt_one (hr a))
    rw [Finset.prod_insert ha]
    exact e.symm.hasSum_iff.mp ((h₁.hasSum.mul ih hprod).congr_fun hfact)

private theorem hasProd_of_hasSum_finsupp_pow (r : α → ℂ) (hr : ∀ a, ‖r a‖ < 1) {z : ℂ}
    (hsum : HasSum (fun f : α →₀ ℕ => f.prod fun a m => r a ^ m) z) :
    HasProd (fun a => (1 - r a)⁻¹) z := by
  let e := Equiv.sigmaFiberEquiv (Finsupp.support : (α →₀ ℕ) → Finset α)
  have hfibers := (e.hasSum_iff.mpr hsum).sigma (hasSum_finsupp_pow_support r hr hsum.summable)
  refine (hasProd_one_add_of_hasSum_prod hfibers).congr_fun fun a => ?_
  rw [geom_series_succ _ (hr a), tsum_geometric_of_norm_lt_one (hr a)]
  ring

end GeometricProduct

variable (K : Type*) [Field K] [NumberField K]

private noncomputable def primeFactors (I : {I : Ideal (𝓞 K) // I ≠ 0}) :
    Multiset (HeightOneSpectrum (𝓞 K)) :=
  (normalizedFactors I.val).pmap (fun _ hP => HeightOneSpectrum.ofPrime hP) prime_of_normalized_factor

private noncomputable def idealOfFactors (m : Multiset (HeightOneSpectrum (𝓞 K))) :
    {I : Ideal (𝓞 K) // I ≠ 0} :=
  ⟨(m.map HeightOneSpectrum.asIdeal).prod, Multiset.prod_ne_zero fun h => by
    obtain ⟨P, _, hP⟩ := Multiset.mem_map.mp h
    exact P.ne_bot hP⟩

private noncomputable def idealEquivFactors :
    {I : Ideal (𝓞 K) // I ≠ 0} ≃ Multiset (HeightOneSpectrum (𝓞 K)) where
  toFun := primeFactors K
  invFun := idealOfFactors K
  left_inv I := by
    apply Subtype.ext
    change ((primeFactors K I).map HeightOneSpectrum.asIdeal).prod = I.val
    rw [primeFactors, Multiset.map_pmap]
    change (Multiset.pmap (fun a (_ : Prime a) => id a) _ _).prod = _
    rw [Multiset.pmap_eq_map]
    simpa only [Multiset.map_id, normalize_eq] using prod_normalizedFactors_eq I.2
  right_inv m := by
    have hprime (P : Ideal (𝓞 K)) (hP : P ∈ m.map HeightOneSpectrum.asIdeal) : Prime P := by
      obtain ⟨Q, _, rfl⟩ := Multiset.mem_map.mp hP
      exact Q.prime
    unfold primeFactors
    have hnorm : normalizedFactors (idealOfFactors K m).val = m.map HeightOneSpectrum.asIdeal :=
      normalizedFactors_prod_of_prime hprime
    suffices hpmap : ∀ h : ∀ P ∈ m.map HeightOneSpectrum.asIdeal, Prime P,
        (m.map HeightOneSpectrum.asIdeal).pmap (fun _ hP => HeightOneSpectrum.ofPrime hP) h = m by
      simp_all
    clear hprime hnorm
    revert m
    intro m
    induction m using Multiset.induction_on with
    | empty => simp
    | cons P m ih =>
      intro h
      simp only [Multiset.map_cons, Multiset.pmap_cons, ih]
      congr 1

/-- A nonzero prime ideal has norm strictly greater than one. -/
theorem one_lt_absNorm_heightOne (P : HeightOneSpectrum (𝓞 K)) : 1 < P.asIdeal.absNorm := by
  exact Nat.one_lt_iff_ne_zero_and_ne_one.mpr ⟨
    fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.mp h),
    fun h => P.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)⟩

/-- The factor `(1 - N(P)⁻ˢ)⁻¹` from a nonzero prime ideal. -/
@[expose] noncomputable def dedekindEulerFactor (s : ℂ) (P : HeightOneSpectrum (𝓞 K)) : ℂ :=
  (1 - (P.asIdeal.absNorm : ℂ) ^ (-s))⁻¹

private noncomputable def natCpow (s : ℂ) : ℕ →* ℂ where
  toFun n := (n : ℂ) ^ s
  map_one' := by simp
  map_mul' := fun m n => by simpa using Complex.natCast_mul_natCast_cpow m n s

/-- Mathlib's Dedekind zeta function is the Euler product over the actual prime ideals. -/
theorem hasProd_dedekindZeta {s : ℂ} (hs : 1 < s.re) :
    HasProd (dedekindEulerFactor K s) (NumberField.dedekindZeta K s) := by
  classical
  let e : (HeightOneSpectrum (𝓞 K) →₀ ℕ) ≃ {I : Ideal (𝓞 K) // I ≠ 0} :=
    Multiset.toFinsupp.toEquiv.symm.trans (idealEquivFactors K).symm
  let r (P : HeightOneSpectrum (𝓞 K)) : ℂ := (P.asIdeal.absNorm : ℂ) ^ (-s)
  have hr (P : HeightOneSpectrum (𝓞 K)) : ‖r P‖ < 1 := by
    have hp : 1 < (P.asIdeal.absNorm : ℝ) := by exact_mod_cast one_lt_absNorm_heightOne K P
    dsimp [r]
    rw [← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hp),
      Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  apply hasProd_of_hasSum_finsupp_pow r hr
  refine (e.hasSum_iff.mpr (hasSum_dedekindZeta_ideal K hs)).congr_fun fun f => ?_
  symm
  change ((natCpow (-s)).comp Ideal.absNorm.toMonoidHom)
    ((f.toMultiset.map HeightOneSpectrum.asIdeal).prod) = _
  rw [map_multiset_prod, Multiset.map_map]
  change (f.toMultiset.map r).prod = _
  induction f using Finsupp.induction with
  | zero => simp
  | single_add a m f _ _ ih =>
    rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.prod_add, ih,
      Finsupp.prod_add_index' (fun b => pow_zero (r b)) (fun b i j => pow_add (r b) i j),
      Finsupp.prod_single_index (h := fun b m => r b ^ m) (pow_zero (r a)), Finsupp.toMultiset_single]
    have h (n : ℕ) : ((n • ({a} : Multiset _)).map r).prod = r a ^ n := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [succ_nsmul, Multiset.map_add, Multiset.prod_add, ih, Multiset.map_singleton,
          Multiset.prod_singleton, pow_succ]
    rw [h]

end Bernoulli
