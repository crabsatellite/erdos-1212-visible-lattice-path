import Erdos1212Kernel.VaughanPromotedComponentConfinement
import Erdos1212Kernel.TaoThetaRootLogError
import Erdos1212Kernel.IwaniecRootLogDecay
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Erdos1212Kernel

noncomputable section

open Filter Topology Asymptotics

set_option maxHeartbeats 700000

theorem eventually_chebyshevTheta_ge_half :
    ∀ᶠ n : Nat in atTop, (n : Real) / 2 ≤ Chebyshev.theta n := by
  obtain ⟨a, A, X₀, ha, hA, hX₀, herr⟩ := exists_taoTheta_root_log_error
  have hdecay := (tendsto_iwaniecRootLogDecay ha).const_mul A
  simp only [mul_zero] at hdecay
  have hdecayNat := hdecay.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (Nat.ceil X₀),
    hdecayNat.eventually (Iio_mem_nhds (show (0 : Real) < 1 / 2 by norm_num))]
    with n hn hsmall
  have hcast : X₀ ≤ (n : Real) :=
    (Nat.le_ceil X₀).trans (by exact_mod_cast hn)
  have hraw := herr n hcast
  have hlower := (abs_le.mp hraw).1
  have hn0 : (0 : Real) ≤ n := Nat.cast_nonneg n
  have hscaled := mul_le_mul_of_nonneg_right hsmall.le hn0
  simp only [Function.comp_apply] at hscaled
  unfold iwaniecRootLogDecay at hsmall hscaled
  nlinarith only [hlower, hscaled]

theorem eventually_exp_half_le_primorial :
    ∀ᶠ n : Nat in atTop, Real.exp ((n : Real) / 2) ≤ (primorial n : Real) := by
  filter_upwards [eventually_chebyshevTheta_ge_half] with n htheta
  have hlog : (n : Real) / 2 ≤ Real.log (primorial n : Real) := by
    simpa only [Chebyshev.theta_eq_log_primorial, Nat.floor_natCast] using htheta
  have hh := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (by exact_mod_cast primorial_pos n)] at hh
  exact hh

/-- Every fixed shifted degree-six polynomial is eventually dominated
by exp(n/4), in the natural rank variable used by the gap comparison. -/
theorem eventually_shifted_sixth_le_exp_quarter (C D : Real)
    (hC : 0 ≤ C) (hD : 0 ≤ D) :
    ∀ᶠ n : Nat in atTop,
      D * ((n : Real) + C) ^ 6 ≤ Real.exp ((n : Real) / 4) := by
  let E := D * (C + 1) ^ 6
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hlim := (isLittleO_pow_exp_pos_mul_atTop 6
    (b := (1 / 4 : Real)) (by norm_num)).const_mul_left E
  have hnat := hlim.comp_tendsto tendsto_natCast_atTop_atTop
  filter_upwards [hnat.bound one_pos, eventually_ge_atTop (1 : Nat)] with n hbound hn
  have hnR : (1 : Real) ≤ n := by exact_mod_cast hn
  have hshift : (n : Real) + C ≤ (C + 1) * n := by
    nlinarith only [hnR, hC]
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (n : Real) + C) hshift 6
  have hscaled := mul_le_mul_of_nonneg_left hpow hD
  have hbound' : E * (n : Real) ^ 6 ≤ Real.exp ((1 / 4 : Real) * n) := by
    simpa only [Function.comp_apply, Real.norm_of_nonneg (mul_nonneg hE (pow_nonneg (Nat.cast_nonneg n) 6)),
      Real.norm_of_nonneg (Real.exp_pos _).le, one_mul] using hbound
  calc
    _ ≤ D * ((C + 1) * (n : Real)) ^ 6 := hscaled
    _ = E * (n : Real) ^ 6 := by dsimp [E]; ring
    _ ≤ _ := by
      have hexp : (1 / 4 : Real) * (n : Real) = (n : Real) / 4 := by ring
      rwa [hexp] at hbound'

end

end Erdos1212Kernel
