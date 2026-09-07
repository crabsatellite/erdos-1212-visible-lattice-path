import Erdos1212Kernel.IwaniecStoppedPrefixExtension
import Erdos1212Kernel.IwaniecPaperARankThreshold

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 600000

/-- Stirling with the finite index slack needed for the exact successful
prefixes in the source's large-rank branch. -/
theorem iwaniecFactorial_shifted_dominates_level {level : Real} (hy : 1 < level)
    (htwelve : 12 ≤ Real.log (Real.log level))
    (hsmall : Real.log (Real.log (Real.log level)) ≤ Real.log (Real.log level) / 4)
    (hscale : Real.log (Real.log level) ≤ Real.log level / 6)
    (n : Nat) (hn : 2 * Real.log level / Real.log (Real.log level) ≤ ((n + 3 : Nat) : Real)) :
    level ≤ (n.factorial : Real) := by
  let L := Real.log level
  let t := Real.log L
  have hL : 0 < L := Real.log_pos hy
  have ht : 0 < t := by dsimp [t, L]; linarith
  have ht12 : 12 ≤ t := htwelve
  have hsmall' : Real.log t ≤ t / 4 := hsmall
  have hscale' : t ≤ L / 6 := hscale
  have hn' : 2 * L / t ≤ (n : Real) + 3 := by simpa only [Nat.cast_add, Nat.cast_ofNat] using hn
  have hprod := (div_le_iff₀ ht).mp hn'
  have hnprod : (3 / 2 : Real) * L ≤ (n : Real) * t := by nlinarith only [hprod, hscale']
  have hratio : L / t ≤ (n : Real) := (div_le_iff₀ ht).mpr (by linarith)
  have hnPos : (0 : Real) < n := (div_pos hL ht).trans_le hratio
  have hnNat : 1 ≤ n := by exact_mod_cast hnPos
  have hlogn := Real.log_le_log (div_pos hL ht) hratio
  rw [Real.log_div hL.ne' ht.ne'] at hlogn
  change t - Real.log t ≤ Real.log (n : Real) at hlogn
  have hlognLower : 2 * t / 3 ≤ Real.log (n : Real) - 1 := by linarith
  have hscaled := mul_le_mul_of_nonneg_left hlognLower hnPos.le
  have hmain : L ≤ (n : Real) * Real.log (n : Real) - n := by nlinarith only [hscaled, hnprod]
  have hstirling := Erdos696.Mertens.log_factorial_ge n hnNat
  have hlog : Real.log level ≤ Real.log (n.factorial : Real) := hmain.trans hstirling
  have he := Real.exp_le_exp.mpr hlog
  rwa [Real.exp_log (zero_lt_one.trans hy), Real.exp_log (by exact_mod_cast Nat.factorial_pos n)] at he

theorem eventually_iwaniecFactorial_shifted_dominates_level :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ n : Nat,
      2 * Real.log level / Real.log (Real.log level) ≤ ((n + 3 : Nat) : Real) →
        level ≤ (n.factorial : Real) := by
  have hloglog : Tendsto (fun level : Real => Real.log (Real.log level)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hratio := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hsmall := (hratio.comp hloglog).eventually (Iio_mem_nhds (show (0 : Real) < 1 / 4 by norm_num))
  have hscale := (hratio.comp Real.tendsto_log_atTop).eventually (Iio_mem_nhds (show (0 : Real) < 1 / 6 by norm_num))
  filter_upwards [eventually_gt_atTop (1 : Real), hloglog.eventually_ge_atTop 12, hsmall, hscale]
    with level hy ht hs hc
  have hL : 0 < Real.log level := Real.log_pos hy
  have ht0 : 0 < Real.log (Real.log level) := by linarith
  have hs' : Real.log (Real.log (Real.log level)) ≤ Real.log (Real.log level) / 4 := by
    have hh := (div_lt_iff₀ ht0).mp (show Real.log (Real.log (Real.log level)) / Real.log (Real.log level) < 1 / 4 from hs)
    linarith
  have hc' : Real.log (Real.log level) ≤ Real.log level / 6 := by
    have hh := (div_lt_iff₀ hL).mp (show Real.log (Real.log level) / Real.log level < 1 / 6 from hc)
    linarith
  exact ⟨hy, fun n hn => iwaniecFactorial_shifted_dominates_level hy ht hs' hc' n hn⟩

end

end Erdos1212Kernel
