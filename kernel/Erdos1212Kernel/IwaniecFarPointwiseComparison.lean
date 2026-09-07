import Erdos1212Kernel.IwaniecFarExponentComparison
import Erdos1212Kernel.IwaniecFarWeightLower
import Erdos1212Kernel.IwaniecAuxiliaryMonotonicity

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

theorem iwaniec_log_four_power_exp {L : Real} (hL : 0 < L) :
    L ^ 4 = Real.exp (4 * Real.log L) := by
  have hh := Real.exp_nat_mul (Real.log L) 4
  rw [Real.exp_log hL] at hh
  simpa only [Nat.cast_ofNat] using hh.symm

theorem iwaniecFar_small_parameter_compare (rank : Nat)
    {level C ξ s : Real} (hy : 1 < level) (hC : 0 ≤ C) (hξ : 6 ≤ ξ)
    (hlogξ : 1 ≤ Real.log ξ) (hs : iwaniecAuxGStart rank ≤ s) (hhalf : s ≤ ξ / 2)
    (hscale : 4 * Real.log (Real.log level) ≤ C * ξ)
    (hG : Real.exp (-(ξ / 2) * Real.log (ξ / 2) - (ξ / 2) * Real.log (Real.log (ξ / 2)) - C * (ξ / 2)) ≤
      iwaniecAuxG rank (ξ / 2)) :
    Real.exp (-(ξ / 2) * Real.log ξ - ξ * Real.log (Real.log ξ) - 2 * C * ξ) ≤
      iwaniecAuxWeightPower level s * iwaniecAuxG rank s / Real.log level ^ 4 := by
  have hL := Real.log_pos hy
  have hξ0 : 0 < ξ := by linarith
  have hhalf0 : 0 < ξ / 2 := by linarith
  have hloghalf : 0 < Real.log (ξ / 2) := Real.log_pos (by linarith)
  have hlogOrder := Real.log_le_log hhalf0 (show ξ / 2 ≤ ξ by linarith)
  have hloglogOrder := Real.log_le_log hloghalf hlogOrder
  have hloglog0 : 0 ≤ Real.log (Real.log ξ) := Real.log_nonneg hlogξ
  have hterm1 := mul_le_mul_of_nonneg_left hlogOrder hhalf0.le
  have hterm2a := mul_le_mul_of_nonneg_left hloglogOrder hhalf0.le
  have hterm2b := mul_le_mul_of_nonneg_right (show ξ / 2 ≤ ξ by linarith) hloglog0
  have hterm2 := hterm2a.trans hterm2b
  have hterm3 := mul_le_mul_of_nonneg_left (show ξ / 2 ≤ ξ by linarith) hC
  have hexponent :
      (-(ξ / 2) * Real.log ξ - ξ * Real.log (Real.log ξ) - 2 * C * ξ) +
        4 * Real.log (Real.log level) ≤
      -(ξ / 2) * Real.log (ξ / 2) - (ξ / 2) * Real.log (Real.log (ξ / 2)) - C * (ξ / 2) := by
    nlinarith only [hterm1, hterm2, hterm3, hscale]
  have hGorder := iwaniecAuxG_antitoneOn_exactDomain rank hs (hs.trans hhalf) hhalf
  have hGsource := hG.trans hGorder
  have hnormalized : Real.exp (-(ξ / 2) * Real.log ξ - ξ * Real.log (Real.log ξ) - 2 * C * ξ) ≤
      iwaniecAuxG rank s / Real.log level ^ 4 := by
    apply (le_div_iff₀ (pow_pos hL 4)).mpr
    rw [iwaniec_log_four_power_exp hL, ← Real.exp_add]
    exact (Real.exp_le_exp.mpr hexponent).trans hGsource
  have hstart1 : 1 ≤ iwaniecAuxGStart rank := by unfold iwaniecAuxGStart; split_ifs <;> norm_num
  have hW : 1 ≤ iwaniecAuxWeightPower level s :=
    Real.one_le_rpow (iwaniecAuxWeightBase_one_le level (hstart1.trans hs)) (by linarith)
  have hWG := mul_le_mul_of_nonneg_right hW (iwaniecAuxG_pos_exactDomain rank hs).le
  exact hnormalized.trans (div_le_div_of_nonneg_right (by simpa only [one_mul] using hWG) (pow_nonneg hL.le 4))

theorem iwaniecFar_large_parameter_compare (rank : Nat)
    {level C s : Real} (hy : 1 < level) (hs : 3 ≤ s)
    (hscale : 4 * Real.log (Real.log level) ≤ C * s)
    (hG : Real.exp (-s * Real.log s - s * Real.log (Real.log s) - C * s) ≤ iwaniecAuxG rank s)
    (hW : Real.exp (3 * s * Real.log (Real.log s) - C * s) ≤ iwaniecAuxWeightPower level s) :
    Real.exp (iwaniecFarHighExponent C s) ≤
      iwaniecAuxWeightPower level s * iwaniecAuxG rank s / Real.log level ^ 4 := by
  have hL := Real.log_pos hy
  have hprod := mul_le_mul hW hG (Real.exp_pos _).le
    (iwaniecAuxWeightPower_pos level (by linarith)).le
  have hprodeq : Real.exp (3 * s * Real.log (Real.log s) - C * s) *
      Real.exp (-s * Real.log s - s * Real.log (Real.log s) - C * s) =
      Real.exp (-s * Real.log s + 2 * s * Real.log (Real.log s) - 2 * C * s) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hprodeq] at hprod
  apply (le_div_iff₀ (pow_pos hL 4)).mpr
  rw [iwaniec_log_four_power_exp hL, ← Real.exp_add]
  apply le_trans _ hprod
  apply Real.exp_le_exp.mpr
  unfold iwaniecFarHighExponent
  linarith only [hscale]

end

end Erdos1212Kernel
