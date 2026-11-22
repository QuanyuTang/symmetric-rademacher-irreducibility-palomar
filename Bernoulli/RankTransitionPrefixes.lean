module

public import Bernoulli.RankTransitionExposure

/-!
# Prefix consistency of the sequential symmetric ensemble

Every leading block is uniform at its own dimension. Conditioning on later
bordering steps therefore transfers pair bounds to samples of any final size.
-/

open scoped BigOperators
namespace Bernoulli

/-- Restrict the independent signs to the leading principal block. -/
@[expose] public def samplePrefix {k n : ℕ} (h : k ≤ n) (a : Sample n) : Sample k :=
  fun ij => a ⟨(Fin.castLE h ij.1.1, Fin.castLE h ij.1.2), ij.2⟩

@[simp] public theorem samplePrefix_refl {n : ℕ} (a : Sample n) :
    samplePrefix (Nat.le_refl n) a = a := by
  funext ij
  rfl

public theorem samplePrefix_comp {i j n : ℕ} (hij : i ≤ j) (hjn : j ≤ n) (a : Sample n) :
    samplePrefix hij (samplePrefix hjn a) = samplePrefix (hij.trans hjn) a := by
  funext ij
  rfl

public theorem samplePrefix_succ {n : ℕ} (a : Sample (n + 1)) :
    samplePrefix (Nat.le_succ n) a = (sampleSuccEquiv n a).1 := by
  funext ij
  rw [sampleSuccEquiv_fst_apply]
  rfl

/-- A leading principal sample has exactly its own uniform distribution. -/
public theorem expectation_samplePrefix {k n : ℕ} (h : k ≤ n) (f : Sample k → ℝ) :
    expectation (fun a : Sample n => f (samplePrefix h a)) = expectation f := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n h ih =>
    rw [expectation_sampleSuccEquiv]
    have hstep (a : Sample n) (col : Fin (n + 1) → Bool) :
        samplePrefix (h.trans (Nat.le_succ n)) ((sampleSuccEquiv n).symm (a, col)) =
          samplePrefix h a := by
      rw [← samplePrefix_comp h (Nat.le_succ n), samplePrefix_succ (n := n),
        Equiv.apply_symm_apply]
    simp_rw [hstep, ← Finset.sum_mul, sum_fairSignWeight, one_mul]
    exact ih

/-- The finite probability of an event of a principal sample is unchanged
when it is regarded as an event of a larger sample. -/
public theorem probability_samplePrefix {k n : ℕ} (h : k ≤ n) (P : Sample k → Prop) :
    probability (fun a : Sample n => P (samplePrefix h a)) = probability P := by
  classical
  unfold probability
  exact expectation_samplePrefix h (fun a => if P a then (1 : ℝ) else 0)

/-- If an earlier prefix event has probability at most q and a later event
has conditional probability at most q, their joint probability is at most
q squared in any sample containing both prefixes. -/
public theorem probability_two_samplePrefix_events_le {i j n : ℕ}
    (hij : i + 1 ≤ j) (hjn : j + 1 ≤ n)
    (P : Sample (i + 1) → Prop) (Q : Sample (j + 1) → Prop) [DecidablePred Q]
    {q : ℝ} (hq : 0 ≤ q) (hP : probability (n := i + 1) P ≤ q)
    (hQ : ∀ a : Sample j, (∑ col : Fin (j + 1) → Bool,
      if Q ((sampleSuccEquiv j).symm (a, col)) then fairSignWeight (Fin (j + 1)) else 0) ≤ q) :
    probability (n := n) (fun a =>
      P (samplePrefix (k := i + 1) (n := n) (hij.trans ((Nat.le_succ j).trans hjn)) a) ∧
        Q (samplePrefix (k := j + 1) (n := n) hjn a)) ≤ q ^ 2 := by
  let P' (a : Sample j) := P (samplePrefix hij a)
  let Q' (b : Sample (j + 1)) := P' (sampleSuccEquiv j b).1 ∧ Q b
  have hprefix (a : Sample n) :
      samplePrefix hij (sampleSuccEquiv j (samplePrefix hjn a)).1 =
        samplePrefix (hij.trans ((Nat.le_succ j).trans hjn)) a := by
    exact (congrArg (samplePrefix hij) (samplePrefix_succ (samplePrefix hjn a)).symm).trans
      ((samplePrefix_comp hij (Nat.le_succ j) (samplePrefix hjn a)).trans
        (samplePrefix_comp (hij.trans (Nat.le_succ j)) hjn a))
  have hQ' : probability (n := j + 1) Q' ≤ q * probability (n := j) P' :=
    probability_and_sampleSuccEquiv_le (n := j) P' Q q (fun a _ => hQ a)
  have hP' : probability (n := j) P' = probability (n := i + 1) P :=
    probability_samplePrefix (k := i + 1) (n := j) hij P
  calc
    _ = probability (fun a : Sample n => Q' (samplePrefix hjn a)) := by
      exact congrArg (probability (n := n)) (funext fun a =>
        congrArg (fun b => P b ∧ Q (samplePrefix hjn a)) (hprefix a).symm)
    _ = probability (n := j + 1) Q' := probability_samplePrefix (k := j + 1) (n := n) hjn Q'
    _ ≤ q * probability (n := j) P' := hQ'
    _ = q * probability (n := i + 1) P := congrArg (q * ·) hP'
    _ ≤ q ^ 2 := by simpa only [pow_two] using mul_le_mul_of_nonneg_left hP hq

end Bernoulli
