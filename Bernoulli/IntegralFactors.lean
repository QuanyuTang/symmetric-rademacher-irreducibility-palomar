module

public import Bernoulli.FactorCount
public import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.Tactic

/-! Integral lifts of the monic rational irreducible factors. -/

open scoped Classical
open Polynomial UniqueFactorizationMonoid

namespace Bernoulli

/-- The distinct monic rational irreducible factors of an integral polynomial. -/
@[expose] public noncomputable def factorSet (P : Polynomial ℤ) : Finset (Polynomial ℚ) :=
  (normalizedFactors (P.map (algebraMap ℤ ℚ))).toFinset

/-- The multiplicity of a factor in the rational factorization of `P`. -/
@[expose] public noncomputable def factorMultiplicity (P : Polynomial ℤ) (q : factorSet P) : ℕ :=
  (normalizedFactors (P.map (algebraMap ℤ ℚ))).count q.1

public theorem factorMultiplicity_pos (P : Polynomial ℤ) (q : factorSet P) :
    0 < factorMultiplicity P q :=
  Multiset.count_pos.mpr (Multiset.mem_toFinset.mp q.2)

/-- The factorization of a monic integral polynomial over `ℚ` lifts to monic irreducible
integral factors with the same multiplicities. -/
public theorem exists_integral_factorization (P : Polynomial ℤ) (hP : P.Monic) :
    ∃ g : factorSet P → Polynomial ℤ,
      P = ∏ q : factorSet P, g q ^ factorMultiplicity P q ∧
      Function.Injective g ∧
      ∀ q, (g q).Monic ∧ Irreducible (g q) ∧ (g q).map (algebraMap ℤ ℚ) = q.1 := by
  let φ := algebraMap ℤ ℚ
  have hφ : Function.Injective φ := IsFractionRing.injective ℤ ℚ
  have hrational := hP.map φ
  have hfactor (q : factorSet P) : Irreducible q.1 ∧ q.1.Monic ∧ q.1 ∣ P.map φ :=
    (Polynomial.mem_normalizedFactors_iff hrational.ne_zero).mp (Multiset.mem_toFinset.mp q.2)
  have hlift (q : factorSet P) : ∃ g : Polynomial ℤ, g.map φ = q.1 := by
    obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd ℚ hP (hfactor q).2.2
    rw [(hfactor q).2.1.leadingCoeff, C_1, mul_one] at hg
    exact ⟨g, hg⟩
  choose g hg using hlift
  refine ⟨g, ?_, ?_, ?_⟩
  · apply Polynomial.map_injective φ hφ
    rw [Polynomial.map_prod]
    simp only [Polynomial.map_pow, hg]
    let s := normalizedFactors (P.map φ)
    change P.map φ = ∏ q : s.toFinset, (q : Polynomial ℚ) ^ s.count (q : Polynomial ℚ)
    calc
      P.map φ = s.prod :=
        ((prod_normalizedFactors_eq hrational.ne_zero).trans hrational.normalize_eq_self).symm
      _ = ∏ q ∈ s.toFinset, q ^ s.count q := Finset.prod_multiset_count s
      _ = _ := (Finset.prod_coe_sort s.toFinset (fun q => q ^ s.count q)).symm
  · intro q r heq
    apply Subtype.ext
    rw [← hg q, heq, hg r]
  · intro q
    have hmonic : (g q).Monic := hφ.monic_map_iff.mpr (hg q ▸ (hfactor q).2.1)
    refine ⟨hmonic, (hmonic.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mpr ?_, hg q⟩
    rw [hg q]
    exact (hfactor q).1

public theorem sum_factorMultiplicity_eq_factorCount {n : ℕ} (a : Sample n) :
    (∑ q : factorSet (matrix a).charpoly, factorMultiplicity (matrix a).charpoly q) = factorCount a := by
  let s := normalizedFactors ((matrix a).charpoly.map (algebraMap ℤ ℚ))
  change (∑ q : s.toFinset, s.count (q : Polynomial ℚ)) = (normalizedFactors (charpoly a)).card
  calc
    _ = ∑ q ∈ s.toFinset, s.count q := Finset.sum_coe_sort s.toFinset s.count
    _ = s.card := Multiset.toFinset_sum_count_eq s
    _ = _ := congrArg (fun p => (normalizedFactors p).card)
      (Matrix.charpoly_map (matrix a) (algebraMap ℤ ℚ)).symm

/-- Degrees of monic factors add with their multiplicities. -/
public theorem sum_weighted_natDegree {ι : Type*} [Fintype ι] {P : Polynomial ℤ}
    {g : ι → Polynomial ℤ} {e : ι → ℕ} (hm : ∀ i, (g i).Monic)
    (hprod : P = ∏ i, g i ^ e i) : (∑ i, e i * (g i).natDegree) = P.natDegree := by
  rw [hprod, Polynomial.natDegree_prod_of_monic _ _ (fun i _ => (hm i).pow (e i))]
  simp only [Polynomial.natDegree_pow]

end Bernoulli
