module

public import Bernoulli.RankHealthyErrors
public import Bernoulli.RankRelationScales
public import Bernoulli.RankSparseScales
import Mathlib.Tactic

/-! Parameter choices for the Fourier condition in the large-prime band. -/

namespace Bernoulli

open Filter

/-- A fixed moment large enough to permit the constant Fourier damping factor. -/
@[expose] public noncomputable def rankHealthyMoment : ℕ :=
  ⌈Real.exp (64 : ℝ)⌉₊

public theorem rankHealthyMoment_pos : 0 < rankHealthyMoment := by
  unfold rankHealthyMoment
  exact Nat.ceil_pos.mpr (Real.exp_pos _)

private theorem rankHealthyMoment_scale :
    1 ≤ ((rankHealthyMoment : ℝ) + 1) * (Real.exp (-32)) ^ 2 := by
  have hK : Real.exp 64 ≤ (rankHealthyMoment : ℝ) := Nat.le_ceil _
  rw [← Real.exp_nat_mul, show ((2 : ℕ) : ℝ) * (-32 : ℝ) = -64 by norm_num,
    Real.exp_neg, ← div_eq_mul_inv]
  exact (le_div_iff₀ (Real.exp_pos _)).mpr (by linarith)

private theorem rankLevelCount_le_exp {n b k : ℕ} (hn : 2 ≤ n) (hb : 0 < b) (hbn : b ≤ n)
    (hk : (k : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ))
    (hlog : Real.log (2 * (n : ℝ)) ≤ (n : ℝ) ^ (3 / 4 : ℝ) / 4) :
    ((n + 1 : ℕ) : ℝ) * (((2 * b) ^ (2 * k) + 1 : ℕ) : ℝ) ≤
      Real.exp (2 * (n : ℝ)) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hp : (n : ℝ) ^ (1 / 4 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add (by positivity), show (1 / 4 : ℝ) + 3 / 4 = 1 by norm_num,
      Real.rpow_one]
  have hlog' : Real.log (2 * (b : ℝ)) ≤ (n : ℝ) ^ (3 / 4 : ℝ) / 4 :=
    (Real.log_le_log (by positivity)
      (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hbn) (by norm_num))).trans hlog
  have hx : (2 * (b : ℝ)) ^ (2 * k) ≤ Real.exp ((n : ℝ) / 2) := by
    rw [← Real.exp_log (show 0 < 2 * (b : ℝ) by positivity), ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    push_cast
    calc
      _ ≤ (2 * (k : ℝ)) * ((n : ℝ) ^ (3 / 4 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_left hlog' (by positivity)
      _ ≤ (2 * (n : ℝ) ^ (1 / 4 : ℝ)) * ((n : ℝ) ^ (3 / 4 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num))
          (by positivity)
      _ = _ := by linarith only [hp]
  have he : 2 ≤ Real.exp ((n : ℝ) / 2) := by
    linarith [Real.add_one_le_exp ((n : ℝ) / 2)]
  have hx' : (2 * (b : ℝ)) ^ (2 * k) + 1 ≤ Real.exp (n : ℝ) := by
    calc
      _ ≤ 2 * Real.exp ((n : ℝ) / 2) := by linarith
      _ ≤ Real.exp ((n : ℝ) / 2) * Real.exp ((n : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  push_cast
  calc
    _ ≤ Real.exp (n : ℝ) * Real.exp (n : ℝ) :=
      mul_le_mul (Real.add_one_le_exp _) hx' (by positivity) (by positivity)
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

private theorem rankHealthy_band_at_scales {n p : ℕ} [Fact p.Prime]
    (hn : 2 ≤ n) (hp : 2 < p) (lam : ZMod p)
    (hroot : Real.exp 48 + 8 ≤ (n : ℝ) ^ (1 / 8 : ℝ))
    (hlogn : Real.log (2 * (n : ℝ)) ≤ (n : ℝ) ^ (3 / 4 : ℝ) / 4)
    (hlogp : 8 ≤ Real.log (p : ℝ))
    (hlogp' : Real.log (p : ℝ) ≤ (n : ℝ) ^ (1 / 4 : ℝ) / 32)
    (hpK : 2 * rankHealthyMoment < p)
    (hsparse :
      let d := ⌊(n : ℝ) / (16 * Real.log (p : ℝ))⌋₊
      let r := ⌊(n : ℝ) / Real.log (p : ℝ)⌋₊
      (((d : ℝ) + 1) * ((n : ℝ) * p) ^ d) *
        (((r : ℝ) + 1) * (n : ℝ) ^ r * (1 / 2 : ℝ) ^ (n - d - r)) ≤
        Real.exp (-(n : ℝ) / 4)) :
    let r := ⌊(n : ℝ) / Real.log (p : ℝ)⌋₊
    probability (fun ω : Sample n => ¬ rankFourierHealthy (shiftedSignMatrix ω lam) r (n - r)
      (Real.exp (-(n : ℝ) / (2 * (rankHealthyMoment : ℝ))))) ≤
      3 * Real.exp (-(n : ℝ) / 4) := by
  let u := (n : ℝ) ^ (1 / 8 : ℝ)
  let w := (n : ℝ) ^ (1 / 4 : ℝ)
  let v := (n : ℝ) ^ (3 / 4 : ℝ)
  let L := Real.log (p : ℝ)
  let s := ⌊u⌋₊
  let k := s ^ 2
  let b := s ^ 6
  let M : ℝ := k
  let r := ⌊(n : ℝ) / L⌋₊
  let d := ⌊(n : ℝ) / (16 * L)⌋₊
  change 8 ≤ L at hlogp
  change L ≤ w / 32 at hlogp'
  change Real.exp 48 + 8 ≤ u at hroot
  have hL : 0 < L := by linarith
  have hn' : (0 : ℝ) < n := by positivity
  have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hu : 0 ≤ u := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hw : 0 ≤ w := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hv : 0 ≤ v := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hu2 : u ^ 2 = w := by
    dsimp [u, w]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn'.le]
    norm_num
  have hu6 : u ^ 6 = v := by
    dsimp [u, v]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn'.le]
    norm_num
  have hwv : w * v = (n : ℝ) := by
    dsimp [w, v]
    rw [← Real.rpow_add hn', show (1 / 4 : ℝ) + 3 / 4 = 1 by norm_num, Real.rpow_one]
  have hs8 : 8 ≤ s := Nat.le_floor (by
    change (8 : ℝ) ≤ u
    linarith [Real.exp_pos (48 : ℝ)])
  have hs8' : (8 : ℝ) ≤ s := by exact_mod_cast hs8
  have hsUpper : (s : ℝ) ≤ u := Nat.floor_le hu
  have hsLower : u / 2 ≤ (s : ℝ) := by
    have hf : u < (s : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hsqrt : Real.exp 48 ≤ Real.sqrt M := by
    change Real.exp 48 ≤ Real.sqrt ((s ^ 2 : ℕ) : ℝ)
    rw [Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg s)]
    have hf : u < (s : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have hkLow : w / 4 ≤ (k : ℝ) := by
    change w / 4 ≤ ((s ^ 2 : ℕ) : ℝ)
    rw [Nat.cast_pow, ← hu2]
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ u / 2) hsLower 2
    linarith
  have hkUp : (k : ℝ) ≤ w := by
    change ((s ^ 2 : ℕ) : ℝ) ≤ w
    rw [Nat.cast_pow, ← hu2]
    exact pow_le_pow_left₀ (Nat.cast_nonneg s) hsUpper _
  have hbUp : (b : ℝ) ≤ v := by
    change ((s ^ 6 : ℕ) : ℝ) ≤ v
    rw [Nat.cast_pow, ← hu6]
    exact pow_le_pow_left₀ (Nat.cast_nonneg s) hsUpper _
  have hk : 0 < k := by dsimp [k]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  have hM : 1 ≤ M := by
    change (1 : ℝ) ≤ k
    exact_mod_cast hk
  have hsupport : 4 * M < (b : ℝ) := by
    have h4 := pow_le_pow_left₀ (by norm_num) hs8' 4
    have h := mul_lt_mul_of_pos_right (show (4 : ℝ) < (s : ℝ) ^ 4 by norm_num at h4; linarith)
      (show 0 < (s : ℝ) ^ 2 by positivity)
    dsimp [M, k, b]
    push_cast
    nlinarith only [h]
  have hsize : 16 * (k : ℝ) * M ≤ (b : ℝ) := by
    have h2 := pow_le_pow_left₀ (by norm_num) hs8' 2
    have h := mul_le_mul_of_nonneg_right
      (show (16 : ℝ) ≤ (s : ℝ) ^ 2 by norm_num at h2; linarith)
      (show 0 ≤ (s : ℝ) ^ 4 by positivity)
    dsimp [M, k, b]
    push_cast
    nlinarith only [h]
  have hcut : 101 * k / 100 ≤ b := by
    have h4 : 4 * k < b := by
      exact_mod_cast (show 4 * (k : ℝ) < (b : ℝ) from hsupport)
    omega
  have hbL : (b : ℝ) * L ≤ (n : ℝ) / 32 := by
    calc
      _ ≤ v * (w / 32) := mul_le_mul hbUp hlogp' hL.le hv
      _ = _ := by linarith only [hwv]
  have hbD : b ≤ d := by
    apply Nat.le_floor
    apply (le_div_iff₀ (by positivity : 0 < 16 * L)).mpr
    linarith
  have hrL : (r : ℝ) * L ≤ n :=
    (le_div_iff₀ hL).mp (Nat.floor_le (by positivity))
  have hb8 : 8 * (b : ℝ) ≤ (n : ℝ) / 32 := by
    linarith [mul_le_mul_of_nonneg_left hlogp (Nat.cast_nonneg b : (0 : ℝ) ≤ b)]
  have hr8 : 8 * (r : ℝ) ≤ n := by
    linarith [mul_le_mul_of_nonneg_left hlogp (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hrows' : 2 * (b + r) ≤ n := by
    exact_mod_cast (show 2 * ((b : ℝ) + (r : ℝ)) ≤ n by linarith)
  have hrows : n ≤ 2 * (n - r - b) := by omega
  have hbr : b + r ≤ n := by omega
  have hm : n ≤ 2 * (n - r) := by omega
  have hLsmall : L ≤ (n : ℝ) / 32 := by
    have hb' : (1 : ℝ) ≤ b := by exact_mod_cast hb
    linarith [mul_le_mul_of_nonneg_right hb' hL.le]
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.log_le_sub_one_of_pos (x := (2 : ℝ)⁻¹) (by positivity)
    rw [Real.log_inv] at h
    norm_num at h ⊢
    linarith
  have ht : L ≤ (k : ℝ) * Real.log 2 := by
    have h := mul_le_mul_of_nonneg_left hlogtwo (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have ht' : L ≤ M := by linarith
  have hcInv : Real.exp (-L) = 1 / (p : ℝ) := by
    rw [Real.exp_neg]
    simp only [L, Real.exp_log hp', one_div]
  have hrep : repeatedIndexRatio k b ≤ 1 / (p : ℝ) := by
    apply (repeatedIndexRatio_le_pow s hs8).trans
    rw [one_div, ← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_neg,
      ← Real.exp_nat_mul, ← hcInv]
    exact Real.exp_le_exp.mpr (by linarith)
  have htail : Real.exp (-M) ≤ 1 / (p : ℝ) := by
    rw [← hcInv]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpowers : (p : ℝ) ^ (b + r) ≤ Real.exp (2 * (n : ℝ)) := by
    rw [← Real.exp_log hp', ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    change ((b + r : ℕ) : ℝ) * L ≤ _
    push_cast
    linarith
  have hpowers' : (p : ℝ) ^ (b + r + 1) ≤ Real.exp (3 * (n : ℝ)) := by
    rw [← Real.exp_log hp', ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    change ((b + r + 1 : ℕ) : ℝ) * L ≤ _
    push_cast
    linarith
  exact probability_not_rankFourierHealthy_le_exp (by omega) hp lam r b d k rankHealthyMoment (n - r)
    hk hb (by omega) hbr hM hsupport hsize hcut hrep htail rankHealthyMoment_pos hpK
    rankHealthyMoment_scale hrows hm hsqrt hpowers hpowers'
    (rankLevelCount_le_exp hn hb (by omega) hkUp hlogn) hsparse

private theorem eventually_block_dimension_scales :
    ∀ᶠ n : ℕ in atTop, 2 ≤ n ∧
      Real.exp 48 + 8 ≤ (n : ℝ) ^ (1 / 8 : ℝ) ∧
      Real.log (2 * (n : ℝ)) ≤ (n : ℝ) ^ (3 / 4 : ℝ) / 4 := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have ht := (tendsto_rpow_atTop (by norm_num : 0 < (1 / 8 : ℝ))).comp hcast
  have hroot := ht.eventually_ge_atTop (Real.exp 48 + 8)
  have h2cast : Tendsto (fun n : ℕ => 2 * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num) hcast
  have hlogs := (isLittleO_log_rpow_atTop (r := 3 / 4) (by norm_num)).def (c := 1 / 8)
    (by norm_num)
  filter_upwards [eventually_ge_atTop (2 : ℕ), hroot, h2cast.eventually hlogs] with n hn hu hlog
  refine ⟨hn, hu, ?_⟩
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hnonneg : (0 : ℝ) ≤ (2 * (n : ℝ)) ^ (3 / 4 : ℝ) :=
    Real.rpow_nonneg (by positivity) _
  calc
    _ ≤ (1 / 8 : ℝ) * (2 * (n : ℝ)) ^ (3 / 4 : ℝ) :=
      (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg] using hlog)
    _ = (1 / 8 : ℝ) * ((2 : ℝ) ^ (3 / 4 : ℝ) * (n : ℝ) ^ (3 / 4 : ℝ)) := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hnn]
    _ ≤ (1 / 8 : ℝ) * (2 * (n : ℝ) ^ (3 / 4 : ℝ)) := by
      gcongr
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (3 / 4 : ℝ) ≤ 1))
    _ = _ := by ring

/-- At the prime scale used in the proof, every leading block of comparable
dimension has exponentially small probability of failing the Fourier condition.
The same parameters leave a block of independent signs for the rank transition. -/
public theorem eventually_rankFourierHealthy_le_band {η : ℝ} (hη : 0 < η) (hηSmall : η ≤ 1 / 256) :
    ∀ᶠ N : ℕ in atTop, ∀ (n p : ℕ) [Fact p.Prime], N ≤ 3 * n → n ≤ N → 2 < p →
      Real.exp ((η / 2) * (N : ℝ) ^ (1 / 4 : ℝ)) / 2 ≤ (p : ℝ) →
      (p : ℝ) ≤ Real.exp ((η / 2) * (N : ℝ) ^ (1 / 4 : ℝ)) →
      let L := Real.log (p : ℝ)
      let r := ⌊(n : ℝ) / L⌋₊
      8 ≤ L ∧ (n : ℝ) / (2 * L) ≤ (r : ℝ) ∧ r ≤ n ∧
        ∀ lam : ZMod p,
          probability (fun ω : Sample n => ¬ rankFourierHealthy (shiftedSignMatrix ω lam) r (n - r)
            (Real.exp (-(n : ℝ) / (2 * (rankHealthyMoment : ℝ))))) ≤
            3 * Real.exp (-(n : ℝ) / 4) := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp eventually_block_dimension_scales
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have he : Tendsto (fun N : ℕ => (η / 2) * (N : ℝ) ^ (1 / 4 : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity)
      ((tendsto_rpow_atTop (by norm_num : 0 < (1 / 4 : ℝ))).comp hcast)
  have he' : Tendsto (fun N : ℕ => Real.exp ((η / 2) * (N : ℝ) ^ (1 / 4 : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp he
  filter_upwards [eventually_ge_atTop (3 * n₀), he.eventually_ge_atTop (8 + Real.log 2),
    he'.eventually_ge_atTop (2 * (2 * (rankHealthyMoment : ℝ) + 1)),
    eventually_sparse_mulVec_bound_le_exp_band (a := η / 2) (by positivity)]
    with N hN hLog hK hSparse
  intro n p _ hNn hnN hp hpLower hpUpper
  obtain ⟨hn, hroot, hlogn⟩ := hn₀ n (by omega)
  let L := Real.log (p : ℝ)
  let r := ⌊(n : ℝ) / L⌋₊
  let w := (n : ℝ) ^ (1 / 4 : ℝ)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hp' : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hL : 8 ≤ L := by
    have h := Real.log_le_log
      (show 0 < Real.exp ((η / 2) * (N : ℝ) ^ (1 / 4 : ℝ)) / 2 by positivity) hpLower
    rw [Real.log_div (Real.exp_ne_zero _) (by norm_num), Real.log_exp] at h
    dsimp [L]
    linarith
  have hpK : 2 * rankHealthyMoment < p := by
    exact_mod_cast (show 2 * (rankHealthyMoment : ℝ) < (p : ℝ) by linarith)
  have hcomp : (N : ℝ) ^ (1 / 4 : ℝ) ≤ 3 * w := by
    calc
      _ ≤ (3 * (n : ℝ)) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by positivity)
        (by exact_mod_cast hNn) (by norm_num)
      _ = (3 : ℝ) ^ (1 / 4 : ℝ) * w :=
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) (Nat.cast_nonneg n)
      _ ≤ _ := by
        gcongr
        simpa only [Real.rpow_one] using
          (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3)
            (by norm_num : (1 / 4 : ℝ) ≤ 1))
  have hL' : L ≤ w / 32 := by
    have h := Real.log_le_log hp' hpUpper
    rw [Real.log_exp] at h
    calc
      L ≤ (η / 2) * (N : ℝ) ^ (1 / 4 : ℝ) := h
      _ ≤ (η / 2) * (3 * w) := mul_le_mul_of_nonneg_left hcomp (by positivity)
      _ = ((η / 2) * 3) * w := by ring
      _ ≤ (1 / 32 : ℝ) * w := mul_le_mul_of_nonneg_right (by linarith) (by positivity [w])
      _ = _ := by ring
  have hLpos : 0 < L := by linarith
  have hwle : w ≤ (n : ℝ) := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (1 / 4 : ℝ) ≤ 1))
  have hrUpper : r ≤ n := by
    apply Nat.floor_le_of_le
    apply (div_le_iff₀ hLpos).mpr
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (show 1 ≤ L by linarith)
      (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hrLower : (n : ℝ) / (2 * L) ≤ (r : ℝ) := by
    have h := Nat.lt_floor_add_one ((n : ℝ) / L)
    have h2 : 2 ≤ (n : ℝ) / L := (le_div_iff₀ hLpos).mpr (by linarith)
    change (n : ℝ) / L < (r : ℝ) + 1 at h
    rw [mul_comm (2 : ℝ), ← div_div]
    linarith
  refine ⟨hL, hrLower, hrUpper, fun lam => ?_⟩
  exact rankHealthy_band_at_scales hn hp lam hroot hlogn hL hL' hpK
    (hSparse n p hNn hnN hp hpLower)

end Bernoulli
