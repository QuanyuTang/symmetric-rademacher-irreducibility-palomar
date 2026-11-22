module

public import Bernoulli.RankExpectation
public import Bernoulli.RankSparse
public import Bernoulli.RankTransitionPrefixes

/-!
# Terminal corank from healthy conditional rank transitions

The initial corank fits within a fixed burn-in interval. After that interval,
the possible contribution of two exceptional transitions is bounded by two
successive applications of the conditional probability estimate.
-/

open scoped BigOperators
namespace Bernoulli

private theorem shiftedSignCorank_le_size {n p : ℕ} [Fact p.Prime]
    (a : Sample n) (lam : ZMod p) : shiftedSignCorank a lam ≤ n := by
  unfold shiftedSignCorank
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
    (LinearMap.ker (shiftedSignMatrix a lam).mulVecLin).finrank_le

private theorem sum_weighted_indicator_eq_probability {n : ℕ}
    (P : Sample n → Prop) [DecidablePred P] :
    (∑ a : Sample n, if P a then ((Fintype.card (Sample n) : ℕ) : ℝ)⁻¹ else 0) =
      probability P := by
  unfold probability expectation
  rw [div_eq_mul_inv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : P a <;> simp [ha]

set_option maxHeartbeats 600000 in
/-- A uniform estimate for the conditional exceptional-step mass, together
with an upper bound on the chance of an unhealthy leading block, bounds the
mean terminal corank of the shifted symmetric Bernoulli matrix. -/
public theorem expectation_shiftedSignCorank_le_of_conditional {p : ℕ} [Fact p.Prime]
    (lam : ZMod p) (start m : ℕ) (hburn : start + 1 ≤ m)
    (good : (t : ℕ) → Sample t → Prop) {q r : ℝ} (hq : 0 ≤ q)
    (hgood : ∀ t < m + 1, probability (fun a : Sample (start + t) => ¬ good (start + t) a) ≤ r)
    (hcond : ∀ t < m + 1, ∀ a : Sample (start + t), good (start + t) a →
      (∑ col : Fin (start + t + 1) → Bool, if
        shiftedSignCorank ((sampleSuccEquiv (start + t)).symm (a, col)) lam ≠
          shiftedSignCorank a lam - 1 then fairSignWeight (Fin (start + t + 1)) else 0) ≤ q) :
    expectation (fun a : Sample (start + m + 1) => (shiftedSignCorank a lam : ℝ)) ≤
      q + ((start + m + 1 : ℕ) : ℝ) *
        (((m + 1 : ℕ) : ℝ) * r + ((m + 1 : ℕ) : ℝ) ^ 2 * q ^ 2) := by
  classical
  let n := start + m + 1
  let w : ℝ := (Fintype.card (Sample n) : ℝ)⁻¹
  let C (a : Sample n) (t : ℕ) :=
    if ht : start + t ≤ n then shiftedSignCorank (samplePrefix ht a) lam else 0
  let G (a : Sample n) (t : ℕ) : Prop :=
    if ht : start + t ≤ n then good (start + t) (samplePrefix ht a) else False
  let ex (a : Sample n) (t : ℕ) : Prop := G a t ∧ C a (t + 1) ≠ C a t - 1
  let unhealthy (a : Sample n) : Prop := ∃ t ∈ Finset.range (m + 1), ¬ G a t
  let R (t : ℕ) (b : Sample (start + t + 1)) : Prop :=
    good (start + t) (sampleSuccEquiv (start + t) b).1 ∧
      shiftedSignCorank b lam ≠ shiftedSignCorank (sampleSuccEquiv (start + t) b).1 lam - 1
  have ht0 {t : ℕ} (ht : t < m + 1) : start + t ≤ n := by dsimp [n]; omega
  have ht1 {t : ℕ} (ht : t < m + 1) : start + t + 1 ≤ n := by dsimp [n]; omega
  have hC (a : Sample n) {t : ℕ} (h : start + t ≤ n) :
      C a t = shiftedSignCorank (samplePrefix h a) lam := by simp only [C, dite_eq_left h]
  have hG (a : Sample n) {t : ℕ} (h : start + t ≤ n) :
      G a t ↔ good (start + t) (samplePrefix h a) := by simp only [G, dite_eq_left h]
  have hOld {t : ℕ} (ht : t < m + 1) (a : Sample n) :
      (sampleSuccEquiv (start + t) (samplePrefix (ht1 ht) a)).1 = samplePrefix (ht0 ht) a := by
    rw [← samplePrefix_succ, samplePrefix_comp]
  have hEx {t : ℕ} (ht : t < m + 1) (a : Sample n) :
      ex a t ↔ R t (samplePrefix (ht1 ht) a) := by
    simp only [ex, R, hG a (ht0 ht), hC a (t := t) (ht0 ht), hC a (t := t + 1) (ht1 ht),
      hOld ht a]
  have hMass {t : ℕ} (ht : t < m + 1) (a : Sample (start + t)) :
      (∑ col : Fin (start + t + 1) → Bool, if R t ((sampleSuccEquiv (start + t)).symm (a, col))
        then fairSignWeight (Fin (start + t + 1)) else 0) ≤ q := by
    by_cases hg : good (start + t) a
    · simpa only [R, Equiv.apply_symm_apply, hg, true_and] using hcond t ht a hg
    · simpa only [R, Equiv.apply_symm_apply, hg, false_and, ite_false, Finset.sum_const_zero]
        using hq
  have hOne {t : ℕ} (ht : t < m + 1) : probability (R t) ≤ q :=
    probability_sampleSuccEquiv_le (R t) q (hMass ht)
  have hPairOrdered {i j : ℕ} (hi : i < m + 1) (hj : j < m + 1) (hij : i < j) :
      probability (n := n) (fun a => ex a i ∧ ex a j) ≤ q ^ 2 := by
    have he : (fun a : Sample n => ex a i ∧ ex a j) =
        (fun a => R i (samplePrefix (ht1 hi) a) ∧ R j (samplePrefix (ht1 hj) a)) :=
      funext fun a => propext (and_congr (hEx hi a) (hEx hj a))
    exact (congrArg (probability (n := n)) he).trans_le (probability_two_samplePrefix_events_le
      (i := start + i) (j := start + j) (n := n) (by omega) (ht1 hj)
      (R i) (R j) hq (hOne hi) (hMass hj))
  have hPair (i j : ℕ) (hi : i < m + 1) (hj : j < m + 1) (hij : i ≠ j) :
      probability (fun a => ex a i ∧ ex a j) ≤ q ^ 2 := by
    rcases lt_or_gt_of_ne hij with h | h
    · exact hPairOrdered hi hj h
    · exact (congrArg (probability (n := n)) (funext fun a => propext (And.comm
        (a := ex a i) (b := ex a j)))).trans_le (hPairOrdered hj hi h)
  have hBad (t : ℕ) (ht : t < m + 1) : probability (fun a => ¬ G a t) ≤ r := by
    rw [show (fun a : Sample n => ¬ G a t) =
      (fun a => ¬ good (start + t) (samplePrefix (ht0 ht) a)) from
      funext fun a => propext (not_congr (hG a (ht0 ht))),
      probability_samplePrefix (ht0 ht) (fun a => ¬good (start + t) a)]
    exact hgood t ht
  have hBadAll : probability unhealthy ≤ ((m + 1 : ℕ) : ℝ) * r := by
    calc
      _ ≤ ∑ t ∈ Finset.range (m + 1), probability (fun a => ¬ G a t) :=
        probability_finset_exists_le _ _
      _ ≤ ∑ _t ∈ Finset.range (m + 1), r := Finset.sum_le_sum fun t ht =>
        hBad t (Finset.mem_range.mp ht)
      _ = _ := by simp [nsmul_eq_mul]
  have hstep (a : Sample n) (t : ℕ) (ht : t < m + 1) : C a (t + 1) ≤ C a t + 1 := by
    rw [hC a (t := t + 1) (ht1 ht), hC a (ht0 ht)]
    simpa only [hOld ht a] using
      shiftedSignCorank_succ_le (samplePrefix (ht1 ht) a) lam
  have hdefault (a : Sample n) (t : ℕ) (ht : t < m + 1) (hb : ¬ unhealthy a)
      (hn : ¬ ex a t) : C a (t + 1) = C a t - 1 := by
    have hg : G a t := not_not.mp (fun h => hb ⟨t, Finset.mem_range.mpr ht, h⟩)
    exact not_not.mp (fun h => hn ⟨hg, h⟩)
  have hb (a : Sample n) : C a 0 + 1 ≤ m := by
    have hn : start ≤ n := by dsimp [n]; omega
    have hs : C a 0 ≤ start :=
      (hC a (t := 0) hn).trans_le (shiftedSignCorank_le_size (samplePrefix hn a) lam)
    omega
  have hEnd (a : Sample n) : C a (m + 1) = shiftedSignCorank a lam :=
    (hC a (t := m + 1) (Nat.le_refl n)).trans
      (congrArg (fun b => shiftedSignCorank b lam) (samplePrefix_refl a))
  have hcap (a : Sample n) : C a (m + 1) ≤ n :=
    (hEnd a).trans_le (shiftedSignCorank_le_size a lam)
  have hlast : probability (fun a => ex a m) ≤ q := by
    rw [show (fun a => ex a m) = (fun a => R m (samplePrefix (ht1 (Nat.lt_succ_self m)) a)) by
      funext a; exact propext (hEx (Nat.lt_succ_self m) a), probability_samplePrefix]
    exact hOne (Nat.lt_succ_self m)
  have h := weighted_terminal_corank_le (fun _ : Sample n => w) (fun _ => by positivity [w])
    C ex unhealthy m n q (((m + 1 : ℕ) : ℝ) * r) hstep hdefault hb hcap
    ((sum_weighted_indicator_eq_probability (n := n) (fun a => ex a m)).trans_le hlast)
    (fun i j hi hj hij => (sum_weighted_indicator_eq_probability (n := n)
      (fun a => ex a i ∧ ex a j)).trans_le (hPair i j hi hj hij))
    ((sum_weighted_indicator_eq_probability (n := n) unhealthy).trans_le hBadAll)
  rw [expectation, div_eq_inv_mul, Finset.mul_sum]
  simpa only [hEnd, w] using h

end Bernoulli
