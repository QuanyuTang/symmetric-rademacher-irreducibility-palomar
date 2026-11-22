module

public import Bernoulli.HalaszEnergy
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Growth of character-energy level sets

Cauchy–Davenport turns repeated addition of small-energy frequencies into a
cardinality estimate at the scale of the square root of the energy.
-/

open scoped BigOperators Pointwise
namespace Bernoulli

variable {ι : Type*} [Fintype ι] {p : ℕ} [NeZero p]

/-- The frequencies whose character energy is at most the given threshold. -/
@[expose] public noncomputable def characterEnergyLevel (v : ι → ZMod p) (u : ℝ) :
    Finset (ZMod p) := by
  classical
  exact Finset.univ.filter fun r => characterEnergy v r ≤ u

@[simp] public theorem mem_characterEnergyLevel {v : ι → ZMod p} {u : ℝ} {r : ZMod p} :
    r ∈ characterEnergyLevel v u ↔ characterEnergy v r ≤ u := by
  classical
  simp [characterEnergyLevel]

/-- A threshold below the mean energy gives a proper subset of the field. -/
public theorem card_characterEnergyLevel_lt {v : ι → ZMod p} {u : ℝ}
    (hu : u < 2 * ((Finset.univ.filter fun i => v i ≠ 0).card : ℝ)) :
    (characterEnergyLevel v u).card < p := by
  suffices characterEnergyLevel v u ≠ Finset.univ by
    simpa only [ZMod.card] using (Finset.card_lt_iff_ne_univ _).mpr this
  intro h
  have hle : (∑ r : ZMod p, characterEnergy v r) ≤ (p : ℝ) * u := by
    calc
      _ ≤ ∑ _r : ZMod p, u := Finset.sum_le_sum fun r _ =>
        mem_characterEnergyLevel.mp (h ▸ Finset.mem_univ r)
      _ = _ := by simp [ZMod.card, nsmul_eq_mul]
  rw [sum_characterEnergy] at hle
  rw [mul_comm (2 : ℝ), mul_assoc] at hle
  have hp : 0 < (p : ℝ) := by exact_mod_cast NeZero.pos p
  exact (not_le_of_gt hu) ((mul_le_mul_iff_right₀ hp).1 hle)

private theorem nsmul_characterEnergyLevel_subset (v : ι → ZMod p) {u : ℝ} (hu : 0 ≤ u)
    (n : ℕ) :
    n • characterEnergyLevel v u ⊆ characterEnergyLevel v ((n : ℝ) ^ 2 * u) := by
  induction n with
  | zero => simp [← Finset.singleton_zero, Finset.singleton_subset_iff]
  | succ n ih =>
    intro r hr
    rw [succ_nsmul] at hr
    obtain ⟨s, hs, t, ht, rfl⟩ := Finset.mem_add.mp hr
    have hs' := Real.sqrt_le_sqrt (mem_characterEnergyLevel.mp (ih hs))
    have ht' := Real.sqrt_le_sqrt (mem_characterEnergyLevel.mp ht)
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)] at hs'
    have h := (sqrt_characterEnergy_add_le v s t).trans (add_le_add hs' ht')
    apply mem_characterEnergyLevel.mpr
    have hsq := pow_le_pow_left₀ (Real.sqrt_nonneg _) h 2
    rw [Real.sq_sqrt (characterEnergy_nonneg v _)] at hsq
    convert hsq using 1
    rw [← add_one_mul, mul_pow, Real.sq_sqrt hu, Nat.cast_succ]

omit [NeZero p] in
private theorem card_nsmul_lower {s : Finset (ZMod p)} (hp : p.Prime) (hs : 0 ∈ s)
    (n : ℕ) (hn : (n • s).card < p) :
    n * (s.card - 1) + 1 ≤ (n • s).card := by
  induction n with
  | zero => simp [← Finset.singleton_zero]
  | succ n ih =>
    have hsub : n • s ⊆ (n + 1) • s := by
      intro r hr
      rw [succ_nsmul]
      exact Finset.mem_add.mpr ⟨r, hr, 0, hs, add_zero r⟩
    have hsmall := (Finset.card_le_card hsub).trans_lt hn
    have hs' : s.Nonempty := ⟨0, hs⟩
    have hcd := ZMod.cauchy_davenport hp (hs'.nsmul (n := n)) hs'
    rw [← succ_nsmul] at hcd
    have hlast := (min_le_iff.mp hcd).resolve_left (not_le_of_gt hn)
    have hpos := Finset.card_pos.mpr hs'
    calc
      _ = (n * (s.card - 1) + 1) + s.card - 1 := by rw [Nat.succ_mul]; omega
      _ ≤ (n • s).card + s.card - 1 := by gcongr; exact ih hsmall
      _ ≤ _ := hlast

/-- Below a proper reference level, the proportion of nonzero frequencies in
the smaller level is bounded by the square-root ratio of the two energies. -/
public theorem card_erase_characterEnergyLevel_le (v : ι → ZMod p) (hp : p.Prime)
    {u b : ℝ} (hu : 0 < u) (hub : u ≤ b) (hproper : (characterEnergyLevel v b).card < p) :
    ((characterEnergyLevel v u).erase 0).card ≤
      2 * ((characterEnergyLevel v b).card : ℝ) * (Real.sqrt u / Real.sqrt b) := by
  let q := Real.sqrt b / Real.sqrt u
  let n := ⌊q⌋₊
  have hb := hu.trans_le hub
  have hsu := Real.sqrt_pos.mpr hu
  have hsb := Real.sqrt_pos.mpr hb
  have hq : 1 ≤ q := (le_div_iff₀ hsu).mpr (by simpa using Real.sqrt_le_sqrt hub)
  have hn : 1 ≤ n := (Nat.one_le_floor_iff _).mpr hq
  have hn_le : (n : ℝ) ≤ q := Nat.floor_le (zero_le_one.trans hq)
  have hq_le : q ≤ 2 * (n : ℝ) := by
    have h := Nat.lt_floor_add_one q
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    change q < (n : ℝ) + 1 at h
    linarith
  have hscale : (n : ℝ) ^ 2 * u ≤ b := by
    calc
      _ ≤ q ^ 2 * u := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (Nat.cast_nonneg _) hn_le _) hu.le
      _ = b := by
        dsimp [q]
        rw [div_pow, Real.sq_sqrt hu.le, Real.sq_sqrt hb.le, div_mul_cancel₀ _ hu.ne']
  let s := characterEnergyLevel v u
  have hsub : n • s ⊆ characterEnergyLevel v b := fun r hr =>
    mem_characterEnergyLevel.mpr
      ((mem_characterEnergyLevel.mp (nsmul_characterEnergyLevel_subset v hu.le n hr)).trans hscale)
  have hcard := Finset.card_le_card hsub
  have hs : 0 ∈ s := by simp [s, hu.le]
  have hcount := (card_nsmul_lower hp hs n (hcard.trans_lt hproper)).trans hcard
  have hbound : (n : ℝ) * ((s.erase 0).card : ℝ) ≤ (characterEnergyLevel v b).card := by
    have h' : n * (s.erase 0).card ≤ (characterEnergyLevel v b).card := by
      rw [Finset.card_erase_of_mem hs]
      exact (Nat.le_succ _).trans hcount
    exact_mod_cast h'
  change ((s.erase 0).card : ℝ) ≤ _
  calc
    _ = (q * ((s.erase 0).card : ℝ)) * (Real.sqrt u / Real.sqrt b) := by
      dsimp [q]
      field_simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      calc
        _ ≤ (2 * (n : ℝ)) * ((s.erase 0).card : ℝ) :=
          mul_le_mul_of_nonneg_right hq_le (Nat.cast_nonneg _)
        _ = 2 * ((n : ℝ) * ((s.erase 0).card : ℝ)) := mul_assoc _ _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left hbound (by norm_num)

end Bernoulli
