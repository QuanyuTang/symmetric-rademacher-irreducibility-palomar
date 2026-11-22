module

public import Bernoulli.RankRelationEvents
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Excluding near-kernel vectors at high relation levels

In a high level the row atom is proportional to the normalized relation
count. This factor cancels the reciprocal dependence in the inverse count,
up to the number of rows that may fail the constraint.
-/

open scoped BigOperators
namespace Bernoulli

private theorem relationLevel_atomError_le {k b c p : ℕ} {M : ℝ}
    (hp : 0 < (p : ℝ)) (hM : 1 ≤ M)
    (hrep : repeatedIndexRatio k b ≤ 1 / (p : ℝ)) (htail : Real.exp (-M) ≤ 1 / (p : ℝ)) :
    1 / (p : ℝ) + 8 * (normalizedRestrictedCount k b c + repeatedIndexRatio k b) /
          Real.sqrt M + Real.exp (-M) ≤
        10 / (p : ℝ) + 8 * normalizedRestrictedCount k b c / Real.sqrt M := by
  have hroot : 1 ≤ Real.sqrt M := Real.one_le_sqrt.mpr hM
  have hterm : 8 * repeatedIndexRatio k b / Real.sqrt M ≤ 8 / (p : ℝ) := by
    calc
      _ ≤ (8 / (p : ℝ)) / Real.sqrt M := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hrep (by norm_num : 0 ≤ (8 : ℝ))
      _ ≤ _ := div_le_self (by positivity) hroot
  rw [mul_add, add_div]
  simp only [div_eq_mul_inv] at hterm htail ⊢
  linarith only [hterm, htail]

/-- A low relation level admits a base-size coordinate set on which every
atom is at most eighteen times the uniform probability. -/
public theorem exists_subset_fairSign_atom_le_of_low_relationLevel {ι : Type*}
    [Fintype ι] [DecidableEq ι] {p : ℕ} [Fact p.Prime] (hp : 2 < p)
    {v : ι → ZMod p} {k b c : ℕ} (hmin : IsMinimumRestrictedCount v k b c)
    (hk : 0 < k) {M : ℝ} (hM : 1 ≤ M) (hsupport : 4 * M < (b : ℝ))
    (hsize : 16 * (k : ℝ) * M ≤ b) (hcut : 101 * k / 100 ≤ b)
    (hrep : repeatedIndexRatio k b ≤ 1 / (p : ℝ)) (htail : Real.exp (-M) ≤ 1 / (p : ℝ))
    (hlow : normalizedRestrictedCount k b c ≤ Real.sqrt M / p) :
    ∃ S : Finset ι, S.card = b ∧
      ∀ u : ZMod p, modularMass (fun _ : S → Bool => (1 / 2 : ℝ) ^ S.card)
        (fun g => ∑ j : S, (if g j then 1 else -1) * v j.1) u ≤ 18 / (p : ℝ) := by
  have hp' : 0 < (p : ℝ) := by exact_mod_cast NeZero.pos p
  have hM' : 0 < M := zero_lt_one.trans_le hM
  have hδ : normalizedRestrictedCount k b c / Real.sqrt M ≤ 1 / (p : ℝ) :=
    (div_le_iff₀ (Real.sqrt_pos.mpr hM')).mpr
      (by simpa [div_eq_mul_inv, mul_comm] using hlow)
  obtain ⟨S, _, hSb, hS⟩ :=
    exists_subset_fairSign_atom_le hp hmin hk hM' hsupport hsize hcut
  refine ⟨S, hSb, fun u => ?_⟩
  rw [hSb]
  refine ((hS u).trans (relationLevel_atomError_le hp' hM hrep htail)).trans ?_
  rw [mul_div_assoc]
  simp only [div_eq_mul_inv] at hδ ⊢
  linarith only [hδ]

private theorem levelCount_mul_atomPow_le {n d b r : ℕ} (hd : d ≤ n) (hbr : b + r ≤ n)
    {P δ M : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1) (hPδ : δ⁻¹ ≤ P) (hM : 0 < M) :
    (100 / δ) ^ (d - b) * (18 * δ / Real.sqrt M) ^ (n - r - b) ≤
      (1800 : ℝ) ^ n * P ^ r / (Real.sqrt M) ^ (n - r - b) := by
  let e := d - b
  let m := n - r - b
  have he : e ≤ m + r := by dsimp [e, m]; omega
  have hδpow : δ ^ m / δ ^ e ≤ P ^ r := by
    apply (div_le_iff₀ (pow_pos hδ _)).mpr
    calc
      δ ^ m = δ ^ (m + r) * (δ⁻¹) ^ r := by
        rw [pow_add, mul_assoc, ← mul_pow, mul_inv_cancel₀ hδ.ne', one_pow, mul_one]
      _ ≤ δ ^ e * P ^ r := mul_le_mul (pow_le_pow_of_le_one hδ.le hδ₁ he)
        (pow_le_pow_left₀ (by positivity) hPδ _) (by positivity) (by positivity)
      _ = _ := mul_comm _ _
  have hC : (100 : ℝ) ^ e * (18 : ℝ) ^ m ≤ 1800 ^ n := by
    have hen : e ≤ n := (Nat.sub_le _ _).trans hd
    have hmn : m ≤ n := (Nat.sub_le _ _).trans (Nat.sub_le _ _)
    calc
      _ ≤ (100 : ℝ) ^ n * (18 : ℝ) ^ n :=
        mul_le_mul (pow_le_pow_right₀ (by norm_num) hen)
          (pow_le_pow_right₀ (by norm_num) hmn) (by positivity) (by positivity)
      _ = _ := by rw [← mul_pow]; norm_num
  change (100 / δ) ^ e * (18 * δ / Real.sqrt M) ^ m ≤ _
  calc
    _ = (((100 : ℝ) ^ e * (18 : ℝ) ^ m) * (δ ^ m / δ ^ e)) /
        (Real.sqrt M) ^ m := by simp only [div_pow, mul_pow]; ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul hC hδpow (by positivity) (by positivity)) (by positivity)

/-- At a high relation level, the inverse count and row constraints give a
probability bound independent of the particular relation count. -/
public theorem probability_high_relationLevel_nearKernel_le {n p : ℕ} [Fact p.Prime]
    (hp : 2 < p) (lam : ZMod p) {k b d c r : ℕ} (hk : 0 < k) (hb : 0 < b)
    (hbd : b ≤ d) (hd : d ≤ n) (hbr : b + r ≤ n) (hc : c ≤ (2 * b) ^ (2 * k))
    {M : ℝ} (hM : 1 ≤ M) (hsupport : 4 * M < (b : ℝ))
    (hsize : 16 * (k : ℝ) * M ≤ b) (hcut : 101 * k / 100 ≤ b)
    (hrep : repeatedIndexRatio k b ≤ 1 / (p : ℝ)) (htail : Real.exp (-M) ≤ 1 / (p : ℝ))
    (hhigh : Real.sqrt M / (p : ℝ) ≤ normalizedRestrictedCount k b c) :
    probability (fun a : Sample n =>
      ∃ v ∈ vectorsOfMinimumRestrictedCount k b d c,
        (finiteVectorSupport ((shiftedSignMatrix a lam).mulVec v)).card ≤ r) ≤
          ((7200 : ℝ) ^ n * (p : ℝ) ^ (b + r)) /
            (Real.sqrt M) ^ (n - r - b) := by
  let δ := normalizedRestrictedCount k b c
  have hp' : 0 < (p : ℝ) := by exact_mod_cast NeZero.pos p
  have hb' : 0 < (b : ℝ) := by exact_mod_cast hb
  have hM' : 0 < M := zero_lt_one.trans_le hM
  have hδ : 0 < δ := (div_pos (Real.sqrt_pos.mpr hM') hp').trans_le hhigh
  have hc' : 0 < c := by
    by_contra h
    have h0 : c = 0 := by omega
    simp [δ, normalizedRestrictedCount, h0] at hδ
  have hδ₁ : δ ≤ 1 := by
    dsimp [δ, normalizedRestrictedCount]
    apply (div_le_iff₀ (by positivity : 0 < (2 * (b : ℝ)) ^ (2 * k))).mpr
    rw [one_mul]
    exact_mod_cast hc
  have hroot : 1 ≤ Real.sqrt M := Real.one_le_sqrt.mpr hM
  have hδp : 1 / (p : ℝ) ≤ δ := calc
    _ ≤ Real.sqrt M / (p : ℝ) := div_le_div_of_nonneg_right hroot hp'.le
    _ ≤ _ := hhigh
  have hinv : δ⁻¹ ≤ (p : ℝ) := (inv_le_iff_one_le_mul₀' hδ).mpr (calc
    1 = (1 / (p : ℝ)) * p := (div_mul_cancel₀ _ hp'.ne').symm
    _ ≤ δ * p := mul_le_mul_of_nonneg_right hδp hp'.le)
  have hδM : 1 / (p : ℝ) ≤ δ / Real.sqrt M :=
    (le_div_iff₀ (Real.sqrt_pos.mpr hM')).mpr
      (by simpa [div_eq_mul_inv, mul_comm] using hhigh)
  let q := 18 * δ / Real.sqrt M
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hq' := (relationLevel_atomError_le (k := k) (b := b) (c := c) hp' hM hrep htail).trans
    (show 10 / (p : ℝ) + 8 * δ / Real.sqrt M ≤ q by
      dsimp only [q]
      rw [mul_div_assoc, mul_div_assoc]
      simp only [div_eq_mul_inv] at hδM ⊢
      linarith only [hδM])
  have hprob := probability_nearKernel_minimumRestrictedCount_le (n := n) (r := r)
    hp lam hk hb hbd hc' hM' hsupport hsize hcut q hq hq'
  have hbin : (n.choose d : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast Nat.choose_le_two_pow n d
  refine hprob.trans ?_
  calc
    _ = ((n.choose d : ℝ) * (2 : ℝ) ^ n * (p : ℝ) ^ b) *
        ((100 / δ) ^ (d - b) * (18 * δ / Real.sqrt M) ^ (n - r - b)) := by
      dsimp [q, δ]
      ring
    _ ≤ ((2 : ℝ) ^ n * (2 : ℝ) ^ n * (p : ℝ) ^ b) *
        ((1800 : ℝ) ^ n * (p : ℝ) ^ r / (Real.sqrt M) ^ (n - r - b)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbin (by positivity))
        (by positivity)) (levelCount_mul_atomPow_le hd hbr hδ hδ₁ hinv hM')
        (by positivity) (by positivity)
    _ = (((2 : ℝ) ^ n * (2 : ℝ) ^ n * (1800 : ℝ) ^ n) *
          ((p : ℝ) ^ b * (p : ℝ) ^ r)) / (Real.sqrt M) ^ (n - r - b) := by ring
    _ = _ := by rw [← mul_pow, ← mul_pow, ← pow_add]; norm_num

end Bernoulli
