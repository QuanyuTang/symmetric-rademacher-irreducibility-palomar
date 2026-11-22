module

public import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Tactic

/-! Polynomial bounds on the strip containing the logarithmic derivative disks. -/

open Filter Metric Set
open scoped Asymptotics Topology

namespace Bernoulli

private abbrev zetaOpenStrip : Set ℂ := {s | -1 / 2 < s.re ∧ s.re < 4}

private theorem quadratic_growth_isBigO {f : ℂ → ℂ}
    (hgrowth : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s ∈ zetaOpenStrip, ‖f s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2)) :
    ∃ c < Real.pi / (4 - (-1 / 2)), ∃ B, f =O[comap (abs ∘ Complex.im) atTop ⊓
      𝓟 zetaOpenStrip] fun s ↦ Real.exp (B * Real.exp (c * |s.im|)) := by
  obtain ⟨M, B, hM, hB, hbound⟩ := hgrowth
  let c : ℝ := Real.pi / 9
  have hc : 0 < c := div_pos Real.pi_pos (by norm_num)
  have hc' : c < Real.pi / (4 - (-1 / 2)) :=
    div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by norm_num)
  refine ⟨c, hc', B * (2 * Real.exp c / c ^ 2), Asymptotics.IsBigO.of_bound M ?_⟩
  filter_upwards [Filter.eventually_inf_principal.mpr
    (Filter.Eventually.of_forall (fun _ h ↦ h))] with s hs
  have hnonneg : 0 ≤ c * (1 + |s.im|) := mul_nonneg hc.le (by positivity)
  have hpoly := Real.quadratic_le_exp_of_nonneg hnonneg
  have hpow : (1 + |s.im|) ^ 2 ≤ 2 * Real.exp (c * (1 + |s.im|)) / c ^ 2 := by
    rw [le_div_iff₀ (sq_pos_of_pos hc)]
    nlinarith only [hpoly, hnonneg]
  have hexp : 2 * Real.exp (c * (1 + |s.im|)) / c ^ 2 =
      2 * Real.exp c / c ^ 2 * Real.exp (c * |s.im|) := by
    rw [mul_add, mul_one, Real.exp_add]
    ring
  simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  refine (hbound s hs).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hM)
  rw [mul_assoc, ← hexp]
  exact mul_le_mul_of_nonneg_left hpow hB

/-- The polynomial degree in the boundary estimate is preserved through the strip.
The preliminary quadratic-exponential bound can depend on the field arbitrarily. -/
public theorem norm_le_zeta_strip_of_polynomial_boundary {f : ℂ → ℂ} {H : ℝ}
    (hH : 0 ≤ H) (k : ℕ) (hhol : Differentiable ℂ f)
    (hgrowth : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, -1 / 2 < s.re → s.re < 4 → ‖f s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2))
    (hboundary : ∀ s : ℂ, (s.re = -1 / 2 ∨ s.re = 4) → ‖f s‖ ≤ H * (2 + |s.im|) ^ k)
    {s : ℂ} (hs₀ : -1 / 2 ≤ s.re) (hs₁ : s.re ≤ 4) :
    ‖f s‖ ≤ H * (9 * (2 + |s.im|)) ^ k := by
  let g : ℂ → ℂ := fun z ↦ f z / (z + 2) ^ k
  have hden (z : ℂ) (hz : -1 / 2 ≤ z.re) : 1 ≤ ‖z + 2‖ := by
    have h := Complex.re_le_norm (z + 2)
    norm_num [Complex.add_re] at h
    linarith
  have hden_ne (z : ℂ) (hz : -1 / 2 ≤ z.re) : (z + 2) ^ k ≠ 0 :=
    pow_ne_zero _ (norm_pos_iff.mp (zero_lt_one.trans_le (hden z hz)))
  have hclosure : closure zetaOpenStrip ⊆ {z : ℂ | -1 / 2 ≤ z.re} :=
    closure_minimal (fun _ hz ↦ hz.1.le) (isClosed_Ici.preimage Complex.continuous_re)
  have hdiff : DiffContOnCl ℂ g zetaOpenStrip := by
    refine ⟨?_, ?_⟩
    · exact hhol.differentiableOn.div ((differentiableOn_id.add_const 2).pow k)
        (fun z hz ↦ hden_ne z hz.1.le)
    · exact hhol.continuous.continuousOn.div
        (((continuous_id.add continuous_const).pow k).continuousOn)
        (fun z hz ↦ hden_ne z (hclosure hz))
  have hgrowth' : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ z ∈ zetaOpenStrip, ‖g z‖ ≤ M * Real.exp (B * (1 + |z.im|) ^ 2) := by
    obtain ⟨M, B, hM, hB, hbound⟩ := hgrowth
    refine ⟨M, B, hM, hB, fun z hz ↦ ?_⟩
    change ‖f z / (z + 2) ^ k‖ ≤ _
    rw [norm_div, norm_pow]
    exact (div_le_self (norm_nonneg _) (one_le_pow₀ (hden z hz.1.le))).trans (hbound z hz.1 hz.2)
  have hedge (z : ℂ) (hz : z.re = -1 / 2 ∨ z.re = 4) : ‖g z‖ ≤ H * 3 ^ k := by
    have hzr : -1 / 2 ≤ z.re := by rcases hz with hz | hz <;> linarith
    have h1 := hden z hzr
    have him : |z.im| ≤ ‖z + 2‖ := by simpa using Complex.abs_im_le_norm (z + 2)
    have hsum : 2 + |z.im| ≤ 3 * ‖z + 2‖ := by linarith
    change ‖f z / (z + 2) ^ k‖ ≤ _
    rw [norm_div, norm_pow, div_le_iff₀ (pow_pos (zero_lt_one.trans_le h1) _)]
    calc
      ‖f z‖ ≤ H * (2 + |z.im|) ^ k := hboundary z hz
      _ ≤ H * (3 * ‖z + 2‖) ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum _) hH
      _ = _ := by rw [mul_pow, mul_assoc]
  have hbounded := PhragmenLindelof.vertical_strip hdiff (quadratic_growth_isBigO hgrowth')
    (fun z hz ↦ hedge z (Or.inl hz)) (fun z hz ↦ hedge z (Or.inr hz)) hs₀ hs₁
  change ‖f s / (s + 2) ^ k‖ ≤ _ at hbounded
  rw [norm_div, norm_pow, div_le_iff₀ (pow_pos (zero_lt_one.trans_le (hden s hs₀)) _)] at hbounded
  have hsden : ‖s + 2‖ ≤ 3 * (2 + |s.im|) := by
    have h := Complex.norm_le_abs_re_add_abs_im (s + 2)
    norm_num [Complex.add_re, Complex.add_im, abs_of_nonneg (show 0 ≤ s.re + 2 by linarith)] at h
    linarith [abs_nonneg s.im]
  refine hbounded.trans (le_trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hsden _) (by positivity)) ?_)
  rw [mul_assoc, ← mul_pow]
  rw [show (3 : ℝ) * (3 * (2 + |s.im|)) = 9 * (2 + |s.im|) by ring]

/-- The disk upper bound required by the fixed-radius logarithmic derivative lemma. -/
public theorem norm_le_zeta_disk_of_polynomial_boundary {f : ℂ → ℂ} {H : ℝ}
    (hH : 0 ≤ H) (k : ℕ) (hhol : Differentiable ℂ f)
    (hgrowth : ∃ M B : ℝ, 0 ≤ M ∧ 0 ≤ B ∧
      ∀ s : ℂ, -1 / 2 < s.re → s.re < 4 → ‖f s‖ ≤ M * Real.exp (B * (1 + |s.im|) ^ 2))
    (hboundary : ∀ s : ℂ, (s.re = -1 / 2 ∨ s.re = 4) → ‖f s‖ ≤ H * (2 + |s.im|) ^ k)
    {t : ℝ} {s : ℂ} (hs : s ∈ ball (2 + (t : ℂ) * Complex.I) (131 / 128)) :
    ‖f s‖ ≤ H * (9 * (4 + |t|)) ^ k := by
  rw [mem_ball, Complex.dist_eq] at hs
  have hre := (Complex.abs_re_le_norm (s - (2 + (t : ℂ) * Complex.I))).trans_lt hs
  have him := (Complex.abs_im_le_norm (s - (2 + (t : ℂ) * Complex.I))).trans_lt hs
  norm_num [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im] at hre him
  obtain ⟨hre₀, hre₁⟩ := abs_lt.mp hre
  have htime := abs_add_le (s.im - t) t
  rw [sub_add_cancel] at htime
  refine (norm_le_zeta_strip_of_polynomial_boundary hH k hhol hgrowth hboundary
    (by linarith) (by linarith)).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) _) hH

end Bernoulli
