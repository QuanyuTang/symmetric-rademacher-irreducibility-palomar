module

public import Bernoulli.RankSparseRows
public import Bernoulli.RankFourier
import Mathlib.Tactic

/-!
# Conditioned row constraints for complementary sets of coordinates

After the signs off a rectangular block have been fixed, each row constraint
has an arbitrary right-hand side. An upper bound for every atom of the
remaining signed sum gives the same bound uniformly in the conditioned
signs.
-/

namespace Bernoulli

private theorem probability_conditioned_rows_le {n : ℕ} {β R σ : Type*}
    [Fintype β] [Fintype R] [Fintype σ] [Nonempty β] [Nonempty σ]
    (e : Sample n ≃ β × (R → σ)) (P : Sample n → Prop)
    (Q : β → R → σ → Prop) [∀ b i, DecidablePred (Q b i)]
    (he : ∀ a, P a ↔ ∀ i : R, Q (e a).1 i ((e a).2 i))
    (q : ℝ) (hq : ∀ b i, (Fintype.card {s : σ // Q b i s} : ℝ) / Fintype.card σ ≤ q) :
    probability P ≤ q ^ Fintype.card R := by
  classical
  let es := (e.subtypeEquiv he).trans (Equiv.subtypeProdEquivSigmaSubtype
    (fun b (g : R → σ) => ∀ i, Q b i (g i)))
  have hA : 0 < (Fintype.card (R → σ) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := R → σ)
  have hB : 0 < (Fintype.card β : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := β)
  have hrow (b : β) : (Fintype.card {g : R → σ // ∀ i, Q b i (g i)} : ℝ) ≤
      (Fintype.card (R → σ) : ℝ) * q ^ Fintype.card R := by
    rw [mul_comm]
    apply (div_le_iff₀ hA).mp
    have hprob_product :
        (Fintype.card {g : R → σ // ∀ i, Q b i (g i)} : ℝ) / Fintype.card (R → σ) =
          ∏ i : R, (Fintype.card {s : σ // Q b i s} : ℝ) / Fintype.card σ := by
      simpa only [← Nat.card_eq_fintype_card] using
        card_pi_predicates_div_card (fun i : R => Q b i)
    rw [hprob_product]
    calc
      _ ≤ ∏ _i : R, q := Finset.prod_le_prod₀ (fun _ _ => by positivity) (fun i _ => hq b i)
      _ = _ := by simp
  rw [probability_eq_card, Fintype.card_congr es, Fintype.card_congr e,
    Fintype.card_sigma, Fintype.card_prod, Nat.cast_sum, Nat.cast_mul]
  calc
    _ ≤ (∑ _b : β, (Fintype.card (R → σ) : ℝ) * q ^ Fintype.card R) /
        ((Fintype.card β : ℝ) * Fintype.card (R → σ)) :=
      div_le_div_of_nonneg_right (Finset.sum_le_sum fun b _ => hrow b) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc]
      exact mul_div_cancel_left₀ _ (mul_ne_zero hB.ne' hA.ne')

private def sortedSignPosition {n : ℕ} (i j : Fin n) : UpperIndex n :=
  ⟨(min i j, max i j), le_trans (min_le_left ..) (le_max_left ..)⟩

private theorem sortedSignPosition_not_mem {n : ℕ} {R S : Finset (Fin n)}
    (hRS : Disjoint R S) (i : R) (j : ↥Sᶜ) :
    sortedSignPosition i.1 j.1 ∉ Set.range (disjointEdgeEmbedding hRS) := by
  rintro ⟨⟨i', j'⟩, heq⟩
  have hnot : i.1 ∉ S := Finset.disjoint_left.mp hRS i.2
  have hnot' : j.1 ∉ S := Finset.mem_compl.mp j.2
  have hm : min i'.1 j'.1 = min i.1 j.1 := congrArg (fun z : UpperIndex n => z.1.1) heq
  have hM : max i'.1 j'.1 = max i.1 j.1 := congrArg (fun z : UpperIndex n => z.1.2) heq
  have hmin : min i.1 j.1 ∉ S := by
    rcases le_total i.1 j.1 with h | h
    · simpa only [min_eq_left h] using hnot
    · simpa only [min_eq_right h] using hnot'
  have hmax : max i.1 j.1 ∉ S := by
    rcases le_total i.1 j.1 with h | h
    · simpa only [max_eq_right h] using hnot'
    · simpa only [max_eq_left h] using hnot
  rcases le_total i'.1 j'.1 with h | h
  · exact hmax ((max_eq_right h).symm.trans hM ▸ j'.2)
  · exact hmin ((min_eq_right h).symm.trans hm ▸ j'.2)

private theorem fairSign_mass_eq_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (v : ι → ZMod p) (u : ZMod p) :
    modularMass (fun _ : ι → Bool => (1 / 2 : ℝ) ^ Fintype.card ι)
      (fun b => ∑ i, (if b i then 1 else -1) * v i) u =
        (Fintype.card {b : ι → Bool // (∑ i, (if b i then 1 else -1) * v i) = u} : ℝ) /
          Fintype.card (ι → Bool) := by
  classical
  let P (b : ι → Bool) := (∑ i, (if b i then 1 else -1) * v i) = u
  change (∑ b : ι → Bool, if P b then (1 / 2 : ℝ) ^ Fintype.card ι else 0) = _
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  simp only [P, Fintype.card_subtype, Fintype.card_fun, Fintype.card_bool, Nat.cast_pow,
    Nat.cast_ofNat, div_eq_mul_inv, one_mul, inv_pow]

/-- Bounds for all signed-sum atoms control any collection of zero rows
outside the selected coordinate set. -/
public theorem probability_shiftedMulVec_zero_rows_le_of_atom {n p : ℕ} [Fact p.Prime]
    (lam : ZMod p) (v : Fin n → ZMod p) {R S : Finset (Fin n)} (hRS : Disjoint R S)
    (q : ℝ)
    (hq : ∀ u : ZMod p, modularMass (fun _ : S → Bool => (1 / 2 : ℝ) ^ S.card)
      (fun b => ∑ j : S, (if b j then 1 else -1) * v j.1) u ≤ q) :
    probability (fun a : Sample n => ∀ i ∈ R, ((shiftedSignMatrix a lam).mulVec v) i = 0) ≤
      q ^ R.card := by
  classical
  let edges := disjointEdgeEmbedding hRS
  let β := ((Set.range edges)ᶜ : Set (UpperIndex n)) → Bool
  let g := sampleExposureEquiv edges
  let e : Sample n ≃ β × (R → S → Bool) := g.trans (Equiv.prodComm _ _)
  let outside (i : R) (j : ↥Sᶜ) : ↥((Set.range edges)ᶜ : Set (UpperIndex n)) :=
    ⟨sortedSignPosition i.1 j.1, sortedSignPosition_not_mem hRS i j⟩
  let X (b : S → Bool) := ∑ j : S, (if b j then 1 else -1) * v j.1
  let z (b : β) (i : R) : ZMod p :=
    lam * v i.1 - ∑ j : ↥Sᶜ, (if b (outside i j) then 1 else -1) * v j.1
  let P (a : Sample n) := ∀ i ∈ R, ((shiftedSignMatrix a lam).mulVec v) i = 0
  let Q (b : β) (i : R) (x : S → Bool) := X x = z b i
  have hsplit (a : Sample n) (i : R) :
      ((shiftedSignMatrix a lam).mulVec v) i.1 = X ((e a).2 i) - z (e a).1 i := by
    simp only [shiftedSignMatrix, Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
    change (∑ j, (matrix a i.1 j : ZMod p) * v j) - lam * v i.1 = _
    have hin (j : S) : (matrix a i.1 j.1 : ZMod p) =
        if (e a).2 i j then 1 else -1 := by
      rw [matrix_apply_of_disjoint_exposure hRS a i j]
      change (↑(if (g a).1 i j then (1 : ℤ) else -1) : ZMod p) =
        if (g a).1 i j then 1 else -1
      split <;> simp
    have hout (j : ↥Sᶜ) : (matrix a i.1 j.1 : ZMod p) =
        if (e a).1 (outside i j) then 1 else -1 := by
      change _ = if (g a).2 (outside i j) then 1 else -1
      rw [sampleExposureEquiv_snd]
      change (↑(if a (sortedSignPosition i.1 j.1) then (1 : ℤ) else -1) : ZMod p) = _
      split <;> simp
    rw [← Finset.sum_add_sum_compl S]
    simp only [X, z, ← Finset.sum_attach S, ← Finset.sum_attach Sᶜ]
    change (∑ j : S, (matrix a i.1 j.1 : ZMod p) * v j.1) +
      (∑ j : ↥Sᶜ, (matrix a i.1 j.1 : ZMod p) * v j.1) - _ = _
    simp only [hin, hout]
    ring
  have he (a : Sample n) : P a ↔ ∀ i : R, Q (e a).1 i ((e a).2 i) := by
    constructor
    · intro ha i
      have hi := ha i.1 i.2
      rw [hsplit] at hi
      exact sub_eq_zero.mp hi
    · intro ha i hi
      rw [hsplit a ⟨i, hi⟩]
      exact sub_eq_zero.mpr (ha ⟨i, hi⟩)
  have h := probability_conditioned_rows_le e P Q he q (fun b i => by
    change (Fintype.card {x : S → Bool // X x = z b i} : ℝ) / Fintype.card (S → Bool) ≤ q
    rw [← fairSign_mass_eq_card (fun j : S => v j.1) (z b i)]
    simpa only [Fintype.card_coe] using hq (z b i))
  simpa only [Fintype.card_coe] using h

end Bernoulli
