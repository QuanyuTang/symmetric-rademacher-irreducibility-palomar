module

public import Bernoulli.Ensemble
public import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic

/-! Counting irreducible factors with their multiplicities. -/

open UniqueFactorizationMonoid

namespace Bernoulli

/-- The total multiplicity of the rational irreducible factors of the characteristic polynomial. -/
@[expose] public noncomputable def factorCount {n : ℕ} (a : Sample n) : ℕ :=
  (normalizedFactors (charpoly a)).card

public theorem charpoly_monic {n : ℕ} (a : Sample n) : (charpoly a).Monic :=
  Matrix.charpoly_monic _

@[simp] public theorem charpoly_natDegree {n : ℕ} (a : Sample n) : (charpoly a).natDegree = n := by
  simp [charpoly]

public theorem factorCount_pos {n : ℕ} (hn : 0 < n) (a : Sample n) : 0 < factorCount a := by
  by_contra! h
  have hs : normalizedFactors (charpoly a) = 0 := by
    simpa [factorCount] using h
  have hp := prod_normalizedFactors_eq (charpoly_monic a).ne_zero
  rw [(charpoly_monic a).normalize_eq_self, hs, Multiset.prod_zero] at hp
  have hd := congrArg Polynomial.natDegree hp
  simp at hd
  omega

public theorem irreducible_charpoly_iff_factorCount_eq_one {n : ℕ} (a : Sample n) :
    Irreducible (charpoly a) ↔ factorCount a = 1 := by
  constructor
  · intro h
    simp [factorCount, normalizedFactors_irreducible h]
  · intro h
    obtain ⟨g, hg⟩ := Multiset.card_eq_one.mp h
    have hg_irr : Irreducible g := irreducible_of_normalized_factor _ (by rw [hg]; simp)
    have hp := prod_normalizedFactors_eq (charpoly_monic a).ne_zero
    rw [(charpoly_monic a).normalize_eq_self, hg, Multiset.prod_singleton] at hp
    rwa [← hp]

private theorem card_le_sum_natDegree (s : Multiset (Polynomial ℚ))
    (hs : ∀ g ∈ s, 0 < g.natDegree) : s.card ≤ (s.map Polynomial.natDegree).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons g s ih =>
    have hg := hs g (by simp)
    have h := ih (fun q hq => hs q (by simp [hq]))
    simp only [Multiset.card_cons, Multiset.map_cons, Multiset.sum_cons]
    omega

public theorem factorCount_le_dimension {n : ℕ} (a : Sample n) : factorCount a ≤ n := by
  let s := normalizedFactors (charpoly a)
  have hs : ∀ g ∈ s, Irreducible g := fun _ hg => irreducible_of_normalized_factor _ hg
  have h0 : (0 : Polynomial ℚ) ∉ s := fun hg => (hs 0 hg).ne_zero rfl
  have hp : s.prod = charpoly a :=
    (prod_normalizedFactors_eq (charpoly_monic a).ne_zero).trans
      (charpoly_monic a).normalize_eq_self
  calc
    factorCount a = s.card := rfl
    _ ≤ (s.map Polynomial.natDegree).sum :=
      card_le_sum_natDegree s fun g hg => (hs g hg).natDegree_pos
    _ = s.prod.natDegree := (Polynomial.natDegree_multiset_prod _ h0).symm
    _ = n := by rw [hp, charpoly_natDegree]

/-- The reducible indicator is bounded above by the excess number of irreducible factors. -/
public theorem reducibilityProbability_le_expectation {n : ℕ} (hn : 0 < n) :
    reducibilityProbability n ≤ expectation (fun a : Sample n => (factorCount a : ℝ) - 1) := by
  classical
  apply expectation_mono
  intro a
  have hpos := factorCount_pos hn a
  split
  · rename_i h
    have hne := mt (irreducible_charpoly_iff_factorCount_eq_one a).mpr h
    have htwo : 2 ≤ factorCount a := by omega
    have htwo' : (2 : ℝ) ≤ factorCount a := by exact_mod_cast htwo
    linarith
  · have hone : (1 : ℝ) ≤ factorCount a := by exact_mod_cast hpos
    linarith

end Bernoulli
