module

public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.NumberTheory.NumberField.Discriminant.Defs
public import Mathlib.RingTheory.Discriminant

/-!
# Primes and reductions of a power basis

The power-basis discriminant belongs to the conductor of the order generated
by an integral basis generator. This supplies the coprimality condition in the
Kummer–Dedekind correspondence.
-/

public section

open NumberField Polynomial

namespace Bernoulli

/-- The conductor exponent of an integral power-basis generator divides the
integer discriminant of the power basis. -/
theorem exponent_dvd_powerBasis_discriminant {K : Type*} [Field K] [NumberField K]
    (B : PowerBasis ℚ K) (θ : 𝓞 K) (hgen : B.gen = (θ : K)) {d : ℤ}
    (hdisc : Algebra.discr ℚ B.basis = (d : ℚ)) : (RingOfIntegers.exponent θ : ℤ) ∣ d := by
  have hd : d ∈ Ideal.under ℤ (conductor ℤ θ) := by
    change algebraMap ℤ (𝓞 K) d ∈ conductor ℤ θ
    rw [mem_conductor_iff]
    intro z
    let inclusion := IsScalarTower.toAlgHom ℤ (𝓞 K) K
    have hmem : inclusion (algebraMap ℤ (𝓞 K) d * z) ∈
        Algebra.adjoin ℤ ({inclusion θ} : Set K) := by
      have hθ : IsIntegral ℤ B.gen := hgen.symm ▸ RingOfIntegers.isIntegral_coe θ
      have hz := Algebra.discr_mul_isIntegral_mem_adjoin ℚ (R := ℤ) hθ
        (RingOfIntegers.isIntegral_coe z)
      rw [hdisc, hgen, Algebra.smul_def] at hz
      simpa [inclusion] using hz
    rw [← AlgHom.map_adjoin_singleton] at hmem
    obtain ⟨w, hw, hwz⟩ := Subalgebra.mem_map.mp hmem
    have heq : w = algebraMap ℤ (𝓞 K) d * z := RingOfIntegers.coe_injective hwz
    exact heq ▸ hw
  rw [← Int.ideal_span_absNorm_eq_self (Ideal.under ℤ (conductor ℤ θ)),
    ← RingOfIntegers.exponent, Ideal.mem_span_singleton] at hd
  exact hd

/-- A rational prime outside the power-basis discriminant satisfies the
conductor condition of Kummer–Dedekind. -/
theorem not_dvd_exponent_of_not_dvd_powerBasis_discriminant {K : Type*}
    [Field K] [NumberField K] (B : PowerBasis ℚ K) (θ : 𝓞 K) (hgen : B.gen = (θ : K))
    {d : ℤ} (hdisc : Algebra.discr ℚ B.basis = (d : ℚ)) {p : ℕ} (hp : ¬ (p : ℤ) ∣ d) :
    ¬ p ∣ RingOfIntegers.exponent θ := by
  intro h
  exact hp (dvd_trans (Int.natCast_dvd_natCast.mpr h)
    (exponent_dvd_powerBasis_discriminant B θ hgen hdisc))

/-- The residue-degree-one primes above `p` correspond to the distinct roots of
the reduced minimum polynomial when `p` misses the conductor exponent. -/
noncomputable def degreeOnePrimesEquivRoots {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) {p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ RingOfIntegers.exponent θ) :
    {P : (Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver (𝓞 K) //
      Ideal.inertiaDeg (P : Ideal (𝓞 K)) ℤ = 1} ≃
    {x : ZMod p // ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))).IsRoot x} := by
  classical
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod (θ := θ) hp
  have he (Q : RingOfIntegers.monicFactorsMod θ p) :
      Ideal.inertiaDeg (e.symm Q : Ideal (𝓞 K)) ℤ = (Q : Polynomial (ZMod p)).natDegree :=
    NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp Q.2
  let ed : {Q : RingOfIntegers.monicFactorsMod θ p // (Q : Polynomial (ZMod p)).natDegree = 1} ≃
      {P : (Ideal.span ({(p : ℤ)} : Set ℤ)).primesOver (𝓞 K) //
        Ideal.inertiaDeg (P : Ideal (𝓞 K)) ℤ = 1} :=
    e.symm.subtypeEquiv (fun Q => by rw [he Q])
  let g := (minpoly ℤ θ).map (Int.castRingHom (ZMod p))
  have hg : g ≠ 0 := ((minpoly.monic (RingOfIntegers.isIntegral θ)).map _).ne_zero
  have hfactor (Q : Polynomial (ZMod p)) :
      Q ∈ RingOfIntegers.monicFactorsMod θ p ↔ Irreducible Q ∧ Q.Monic ∧ Q ∣ g := by
    simpa only [RingOfIntegers.monicFactorsMod, Multiset.mem_toFinset, g] using
      (Polynomial.mem_normalizedFactors_iff (p := Q) hg)
  have hlinear (Q : RingOfIntegers.monicFactorsMod θ p)
      (hQ : (Q : Polynomial (ZMod p)).natDegree = 1) :
      (Q : Polynomial (ZMod p)) = X - C (-(Q : Polynomial (ZMod p)).coeff 0) := by
    simpa using ((hfactor Q).mp Q.2).2.1.eq_X_add_C hQ
  refine ed.symm.trans {
    toFun := fun Q => ⟨-(Q.1 : Polynomial (ZMod p)).coeff 0, ?_⟩
    invFun := fun a => ⟨⟨X - C a.1, ?_⟩, natDegree_X_sub_C _⟩
    left_inv := ?_
    right_inv := ?_
  }
  · apply dvd_iff_isRoot.mp
    rw [← hlinear Q.1 Q.2]
    exact ((hfactor Q.1).mp Q.1.2).2.2
  · exact (hfactor _).mpr ⟨irreducible_X_sub_C _, monic_X_sub_C _, dvd_iff_isRoot.mpr a.2⟩
  · intro Q
    exact Subtype.ext (Subtype.ext (hlinear Q.1 Q.2).symm)
  · intro a
    exact Subtype.ext (by simp)

/-- The absolute-norm-`p` ideals correspond to the distinct roots of the reduced
minimum polynomial whenever `p` misses the integral power-basis discriminant. -/
theorem card_primeIdeals_eq_card_roots_of_not_dvd_discriminant {K : Type*}
    [Field K] [NumberField K] (B : PowerBasis ℚ K) (θ : 𝓞 K) (hgen : B.gen = (θ : K))
    {d : ℤ} (hdisc : Algebra.discr ℚ B.basis = (d : ℚ)) {p : ℕ} [Fact p.Prime]
    (hp : ¬ (p : ℤ) ∣ d) :
    Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ P.cardQuot = p} =
      Nat.card {x : ZMod p // ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))).IsRoot x} := by
  let : Infinite (𝓞 K) := Infinite.of_injective (fun z : ℤ => (z : 𝓞 K)) Int.cast_injective
  change Nat.card {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ P.absNorm = p} = _
  let pIdeal : Ideal ℤ := Ideal.span {(p : ℤ)}
  have hprime : p.Prime := Fact.out
  have hnorm (P : pIdeal.primesOver (𝓞 K)) : (P : Ideal (𝓞 K)).absNorm = p ↔
      Ideal.inertiaDeg (P : Ideal (𝓞 K)) ℤ = 1 := by
    have hpn : pIdeal.absNorm = p := by simp [pIdeal]
    rw [← Ideal.absNorm_pow_inertiaDeg pIdeal (P : Ideal (𝓞 K)), hpn]
    constructor
    · intro h
      apply Nat.pow_right_injective hprime.two_le
      simpa only [pow_one] using h
    · intro h
      simp [h]
  let e : {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥ ∧ P.absNorm = p} ≃
      {P : pIdeal.primesOver (𝓞 K) // (P : Ideal (𝓞 K)).absNorm = p} :=
    { toFun := fun P => ⟨⟨P, P.2.1, ⟨by
        have h := Ideal.span_singleton_absNorm (I := P.1) (P.2.2.2.symm ▸ hprime)
        simpa [pIdeal, Ideal.under_def, P.2.2.2] using h⟩⟩, P.2.2.2⟩
      invFun := fun P => ⟨P.1, P.1.2.1,
        fun h => hprime.ne_zero (P.2.symm.trans (Ideal.absNorm_eq_zero_iff.mpr h)), P.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr <| e.trans <| (Equiv.subtypeEquivRight hnorm).trans <|
    degreeOnePrimesEquivRoots θ (not_dvd_exponent_of_not_dvd_powerBasis_discriminant B θ hgen hdisc hp)

/-- The discriminant of an integral power basis is the field discriminant times
the square of an integer, obtained from its change of basis. -/
theorem exists_powerBasis_discriminant_eq_fieldDiscr_mul_sq {K : Type*}
    [Field K] [NumberField K] (B : PowerBasis ℚ K) (θ : 𝓞 K) (hgen : B.gen = (θ : K)) :
    ∃ a : ℤ, Algebra.discr ℚ B.basis = ((NumberField.discr K * a ^ 2 : ℤ) : ℚ) := by
  classical
  let b := integralBasis K
  let e := b.indexEquiv B.basis
  let c := b.reindex e
  have hentry (i j : Fin B.dim) : IsIntegral ℤ (c.toMatrix B.basis i j) := by
    change IsIntegral ℤ ((b.reindex e).repr (B.basis j) i)
    rw [Module.Basis.repr_reindex_apply, B.basis_eq_pow, hgen]
    rw [← map_pow (algebraMap (𝓞 K) K), integralBasis_repr_apply]
    exact isIntegral_algebraMap
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.det hentry)
  have hc : Algebra.discr ℚ c = Algebra.discr ℚ b := by
    simp only [c, Module.Basis.coe_reindex, Algebra.discr_reindex]
  refine ⟨a, ?_⟩
  calc
    Algebra.discr ℚ B.basis = Algebra.discr ℚ
        (Matrix.vecMul c ((c.toMatrix B.basis).map (algebraMap ℚ K))) :=
      congrArg (Algebra.discr ℚ) (c.toMatrix_map_vecMul B.basis).symm
    _ = (c.toMatrix B.basis).det ^ 2 * Algebra.discr ℚ c :=
      Algebra.discr_of_matrix_vecMul c (c.toMatrix B.basis)
    _ = ((NumberField.discr K * a ^ 2 : ℤ) : ℚ) := by
      rw [hc, show Algebra.discr ℚ b = (NumberField.discr K : ℚ) from (coe_discr K).symm, ← ha]
      simp [mul_comm]

end Bernoulli
