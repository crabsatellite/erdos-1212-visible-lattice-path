import Erdos1212Kernel.DeBruijnG1RegularPartBound

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

theorem deBruijn_polynomial_exp_decay (n : Nat) {a : Real} (ha : 0 < a) :
    Tendsto (fun u : Real => u ^ n * Real.exp (-a * u)) atTop (nhds 0) := by
  have hs : Tendsto (fun u : Real => a * u) atTop atTop := tendsto_id.const_mul_atTop ha
  have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).comp hs).div_const (a ^ n)
  simp only [zero_div] at h
  apply h.congr'
  filter_upwards with u
  simp only [Function.comp_apply, mul_pow, neg_mul]
  field_simp [pow_ne_zero n ha.ne']

def deBruijnG1RegularMajorant (u : Real) : Real :=
  (2 * u ^ 2 * Real.exp (-4 * u)) * (deBruijn1951NearBound (u + 1) + deBruijn1951Phi 1)

theorem deBruijnG1RegularMajorant_expand (u : Real) :
    deBruijnG1RegularMajorant u =
      4 * Real.exp (1 + Real.exp 1) * (u ^ 3 * Real.exp (-3 * u) + (1 + Real.exp 1) * (u ^ 2 * Real.exp (-3 * u))) +
        (2 * deBruijn1951Phi 1) * (u ^ 2 * Real.exp (-4 * u)) := by
  let c := 1 + Real.exp 1
  have he : Real.exp (-4 * u) * Real.exp (u + c) = Real.exp c * Real.exp (-3 * u) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hN : deBruijn1951NearBound (u + 1) = 2 * (u + c) * Real.exp (u + c) := by
    unfold deBruijn1951NearBound
    have harg : u + 1 + Real.exp 1 = u + c := by dsimp [c]; ring
    rw [harg]
  unfold deBruijnG1RegularMajorant
  rw [hN]
  calc
    _ = 4 * u ^ 2 * (u + c) * (Real.exp (-4 * u) * Real.exp (u + c)) +
        (2 * deBruijn1951Phi 1) * (u ^ 2 * Real.exp (-4 * u)) := by ring
    _ = 4 * u ^ 2 * (u + c) * (Real.exp c * Real.exp (-3 * u)) +
        (2 * deBruijn1951Phi 1) * (u ^ 2 * Real.exp (-4 * u)) := by rw [he]
    _ = _ := by dsimp [c]; ring

theorem tendsto_deBruijnG1RegularMajorant : Tendsto deBruijnG1RegularMajorant atTop (nhds 0) := by
  have h3 := deBruijn_polynomial_exp_decay 3 (a := (3 : Real)) (by norm_num)
  have h2 := deBruijn_polynomial_exp_decay 2 (a := (3 : Real)) (by norm_num)
  have h4 := deBruijn_polynomial_exp_decay 2 (a := (4 : Real)) (by norm_num)
  have h := ((h3.add (h2.const_mul (1 + Real.exp 1))).const_mul (4 * Real.exp (1 + Real.exp 1))).add
    (h4.const_mul (2 * deBruijn1951Phi 1))
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards with u
  exact (deBruijnG1RegularMajorant_expand u).symm

theorem tendsto_deBruijnG1_normalized_regular {b : Real} (hb : b ∈ Set.Icc (0 : Real) 1) :
    Tendsto (fun u : Real => deBruijnG1Normalizer u b * deBruijnG1RegularPart u b) atTop (nhds 0) := by
  apply squeeze_zero_norm' (a := deBruijnG1RegularMajorant) _ tendsto_deBruijnG1RegularMajorant
  filter_upwards [eventually_gt_atTop (1 : Real), eventually_deBruijnSaddleHeight_small] with u hu hH
  have hN : deBruijnG1Normalizer u b ≤ 2 * u ^ 2 * Real.exp (-4 * u) :=
    (deBruijnG1Normalizer_upper hu hb.1).trans (mul_le_mul_of_nonneg_left hH (by positivity))
  have hR := deBruijnG1RegularPart_abs_bound hu hb
  have hNpos := deBruijnG1Normalizer_pos hu b
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hNpos]
  exact mul_le_mul hN hR (abs_nonneg _) (by positivity)

end

end Erdos1212Kernel
