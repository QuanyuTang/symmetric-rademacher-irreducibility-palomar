module

public import Bernoulli.RankHealthyProbability
import Mathlib.Tactic

/-! Exponential bounds for the two dense-vector terms in the Fourier condition. -/

namespace Bernoulli

private theorem pow_two_le_exp_nat (j : ℕ) : (2 : ℝ) ^ j ≤ Real.exp j := by
  rw [show (j : ℝ) = (j : ℝ) * 1 by ring, Real.exp_nat_mul]
  exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) _

/-- The high-relation contribution, including its number of levels, is
exponentially small once the reference energy is large enough. -/
public theorem rankHighRelationError_le_exp {n p b r k : ℕ} {M : ℝ}
    (hrows : n ≤ 2 * (n - r - b))
    (hsqrt : Real.exp 48 ≤ Real.sqrt M)
    (hpowers : (p : ℝ) ^ (b + r) ≤ Real.exp (2 * (n : ℝ)))
    (hcount : ((n + 1 : ℕ) : ℝ) * (((2 * b) ^ (2 * k) + 1 : ℕ) : ℝ) ≤
      Real.exp (2 * (n : ℝ))) :
    ((n + 1 : ℕ) : ℝ) * (((2 * b) ^ (2 * k) + 1 : ℕ) : ℝ) *
      ((7200 : ℝ) ^ n * (p : ℝ) ^ (b + r) / (Real.sqrt M) ^ (n - r - b)) ≤
      Real.exp (-(n : ℝ)) := by
  let t := n - r - b
  let D := ((n + 1 : ℕ) : ℝ) * (((2 * b) ^ (2 * k) + 1 : ℕ) : ℝ)
  have h7200 : (7200 : ℝ) ≤ Real.exp 16 :=
    (by norm_num : (7200 : ℝ) ≤ 2 ^ (16 : ℕ)).trans (pow_two_le_exp_nat 16)
  have hbase : (7200 : ℝ) ^ n ≤ Real.exp (16 * (n : ℝ)) := by
    rw [mul_comm (16 : ℝ), Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) h7200 _
  have hrow' : (n : ℝ) ≤ 2 * (t : ℝ) := by
    change n ≤ 2 * t at hrows
    exact_mod_cast hrows
  have hden : Real.exp (24 * (n : ℝ)) ≤ (Real.sqrt M) ^ t := by
    calc
      _ ≤ Real.exp ((t : ℝ) * 48) := Real.exp_le_exp.mpr (by linarith)
      _ = (Real.exp 48) ^ t := Real.exp_nat_mul _ _
      _ ≤ _ := pow_le_pow_left₀ (Real.exp_pos _).le hsqrt _
  change D * ((7200 : ℝ) ^ n * (p : ℝ) ^ (b + r) / (Real.sqrt M) ^ t) ≤ _
  calc
    _ = D * (7200 : ℝ) ^ n * (p : ℝ) ^ (b + r) / (Real.sqrt M) ^ t := by ring
    _ ≤ Real.exp (2 * (n : ℝ)) * Real.exp (16 * (n : ℝ)) * Real.exp (2 * (n : ℝ)) /
        Real.exp (24 * (n : ℝ)) :=
      div_le_div₀ (by positivity)
        (mul_le_mul (mul_le_mul hcount hbase (by positivity) (by positivity))
          hpowers (by positivity) (by positivity))
        (Real.exp_pos _) hden
    _ = Real.exp (-4 * (n : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg n (α := ℝ)])

/-- The large-Fourier-product contribution is exponentially small for a
fixed moment-scale damping factor and an exponential Fourier cutoff. -/
public theorem rankLargeFourierError_le_exp {n p b r K m : ℕ}
    (hp : 0 < p) (hK : 0 < K) (hrows : b + r ≤ n) (hm : n ≤ 2 * m)
    (hpowers : (p : ℝ) ^ (b + r + 1) ≤ Real.exp (3 * (n : ℝ))) :
    (((2 : ℝ) ^ n * (p : ℝ)) *
      ((p : ℝ) ^ n * (Real.exp (-32)) ^ m /
        (Real.exp (-(n : ℝ) / (2 * (K : ℝ)))) ^ (2 * K))) *
      ((2 : ℝ) ^ n * (18 / (p : ℝ)) ^ (n - r - b)) ≤ Real.exp (-(n : ℝ)) := by
  let t := n - r - b
  let A := Real.exp (-(n : ℝ) / (2 * (K : ℝ)))
  let B := Real.exp (-32)
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have hA : A ^ (2 * K) = Real.exp (-(n : ℝ)) := by
    dsimp only [A]
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp [hK'.ne']
  have hm' : (n : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hm
  have hB : B ^ m ≤ Real.exp (-16 * (n : ℝ)) := by
    dsimp only [B]
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by linarith)
  have h72 : (72 : ℝ) ≤ Real.exp 8 :=
    (by norm_num : (72 : ℝ) ≤ 2 ^ (8 : ℕ)).trans (pow_two_le_exp_nat 8)
  have hbase : (4 : ℝ) ^ n * (18 : ℝ) ^ t ≤ Real.exp (8 * (n : ℝ)) := by
    calc
      _ ≤ (4 : ℝ) ^ n * (18 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by dsimp [t]; omega))
          (by positivity)
      _ = (72 : ℝ) ^ n := by rw [← mul_pow]; norm_num
      _ ≤ _ := by
        rw [mul_comm (8 : ℝ), Real.exp_nat_mul]
        exact pow_le_pow_left₀ (by norm_num) h72 _
  have hpFactor : (p : ℝ) ^ n * p / (p : ℝ) ^ t = (p : ℝ) ^ (b + r + 1) := by
    rw [← pow_succ, show n + 1 = t + (b + r + 1) by dsimp [t]; omega, pow_add]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ hp'.ne')
  change (((2 : ℝ) ^ n * (p : ℝ)) * ((p : ℝ) ^ n * B ^ m / A ^ (2 * K))) *
    ((2 : ℝ) ^ n * (18 / (p : ℝ)) ^ t) ≤ _
  calc
    _ = ((4 : ℝ) ^ n * (18 : ℝ) ^ t) * ((p : ℝ) ^ n * p / (p : ℝ) ^ t) *
        (B ^ m / A ^ (2 * K)) := by
      rw [div_pow, show (4 : ℝ) ^ n = (2 : ℝ) ^ n * (2 : ℝ) ^ n by rw [← mul_pow]; norm_num]
      ring
    _ ≤ Real.exp (8 * (n : ℝ)) * Real.exp (3 * (n : ℝ)) *
        (Real.exp (-16 * (n : ℝ)) / Real.exp (-(n : ℝ))) := by
      rw [hpFactor, hA]
      exact mul_le_mul (mul_le_mul hbase hpowers (by positivity) (by positivity))
        (div_le_div_of_nonneg_right hB (by positivity)) (by positivity) (by positivity)
    _ = Real.exp (-4 * (n : ℝ)) := by
      rw [← Real.exp_sub, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg n (α := ℝ)])

/-- The three near-kernel contributions give the exponential bound on
unhealthy blocks once the scale inequalities hold. -/
public theorem probability_not_rankFourierHealthy_le_exp {n p : ℕ} [Fact p.Prime]
    (hn : 0 < n) (hp : 2 < p) (lam : ZMod p) (r b d₀ k K m : ℕ)
    (hk : 0 < k) (hb : 0 < b) (hb₀ : b ≤ d₀ + 1) (hbr : b + r ≤ n)
    {M : ℝ} (hM : 1 ≤ M) (hsupport : 4 * M < (b : ℝ))
    (hsize : 16 * (k : ℝ) * M ≤ b) (hcut : 101 * k / 100 ≤ b)
    (hrep : repeatedIndexRatio k b ≤ 1 / (p : ℝ)) (htail : Real.exp (-M) ≤ 1 / (p : ℝ))
    (hK : 0 < K) (hpK : 2 * K < p) (hscale : 1 ≤ ((K : ℝ) + 1) * (Real.exp (-32)) ^ 2)
    (hrows : n ≤ 2 * (n - r - b)) (hm : n ≤ 2 * m)
    (hsqrt : Real.exp 48 ≤ Real.sqrt M)
    (hpowers : (p : ℝ) ^ (b + r) ≤ Real.exp (2 * (n : ℝ)))
    (hpowers' : (p : ℝ) ^ (b + r + 1) ≤ Real.exp (3 * (n : ℝ)))
    (hcount : ((n + 1 : ℕ) : ℝ) * (((2 * b) ^ (2 * k) + 1 : ℕ) : ℝ) ≤
      Real.exp (2 * (n : ℝ)))
    (hsparse : (((d₀ : ℝ) + 1) * ((n : ℝ) * p) ^ d₀) *
      (((r : ℝ) + 1) * (n : ℝ) ^ r * (1 / 2 : ℝ) ^ (n - d₀ - r)) ≤
        Real.exp (-(n : ℝ) / 4)) :
    probability (fun ω : Sample n => ¬ rankFourierHealthy (shiftedSignMatrix ω lam) r m
      (Real.exp (-(n : ℝ) / (2 * (K : ℝ))))) ≤
      3 * Real.exp (-(n : ℝ) / 4) := by
  have h := probability_not_rankFourierHealthy_le
    (a := Real.exp (-(n : ℝ) / (2 * (K : ℝ)))) (β := Real.exp (-32))
    hn hp lam r b d₀ k K m
    hk hb hb₀ hbr hM hsupport hsize hcut hrep htail hpK (Real.exp_pos _)
    (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by norm_num)) hscale
  have hhigh := rankHighRelationError_le_exp hrows hsqrt hpowers hcount
  have hFourier := rankLargeFourierError_le_exp (show 0 < p by omega) hK hbr hm hpowers'
  refine h.trans ((add_le_add (add_le_add hsparse hhigh) hFourier).trans ?_)
  have hdecay : Real.exp (-(n : ℝ)) ≤ Real.exp (-(n : ℝ) / 4) :=
    Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg n (α := ℝ)])
  linarith

end Bernoulli
