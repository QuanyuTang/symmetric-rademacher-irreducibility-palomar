module

public import Mathlib.SetTheory.Cardinal.Finite

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Prod

/-!
# Counting conditioned row constraints

After fixing the shared entries, each row has its own allowed set of entries.
The count of allowed tuples is the sum of the products of the row counts.
-/

public section

open scoped BigOperators

namespace Bernoulli

/-- Uniform bounds on separate row constraints give a product bound after conditioning
on the shared entries. -/
theorem card_conditioned_row_constraints_le {β ι : Type*} [Finite β] [Fintype ι]
    {α : ι → Type*} [∀ i, Finite (α i)] (P : β → ∀ i : ι, α i → Prop)
    (c : ι → ℕ) (h : ∀ b i, Nat.card {x : α i // P b i x} ≤ c i) :
    Nat.card {z : β × (∀ i, α i) // ∀ i, P z.1 i (z.2 i)} ≤ Nat.card β * ∏ i, c i := by
  classical
  let : Fintype β := Fintype.ofFinite β
  let e : {z : β × (∀ i, α i) // ∀ i, P z.1 i (z.2 i)} ≃
      (Σ b : β, ∀ i, {x : α i // P b i x}) :=
    (Equiv.subtypeProdEquivSigmaSubtype (fun (b : β) (f : ∀ i, α i) => ∀ i, P b i (f i))).trans
      (Equiv.sigmaCongrRight fun b => Equiv.subtypePiEquivPi (β := α) (p := P b))
  calc
    _ = ∑ b : β, ∏ i, Nat.card {x : α i // P b i x} := by
      rw [Nat.card_congr e, Nat.card_sigma]
      simp_rw [Nat.card_pi]
    _ ≤ ∑ _b : β, ∏ i, c i := by
      exact Finset.sum_le_sum fun b _ =>
        Finset.prod_le_prod₀ (fun _ _ => Nat.zero_le _) (fun i _ => h b i)
    _ = _ := by
      simp only [Finset.sum_const, Nat.nsmul_eq_mul, Finset.card_univ, Nat.card_eq_fintype_card]

end Bernoulli
