import Erdos1212Kernel.IwaniecMertensThetaKernel

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

def iwaniecMertensRealRemainder (x : Real) : Real :=
  iwaniecPrimeReciprocalReal x - Real.log (Real.log x) - Erdos696.Mertens.meisselMertensConstant

theorem iwaniecMertensRealRemainder_nat (N : Nat) :
    iwaniecMertensRealRemainder N = iwaniecPrimeReciprocalRemainder N := by
  simp only [iwaniecMertensRealRemainder, iwaniecPrimeReciprocalReal_nat, iwaniecPrimeReciprocalRemainder]

theorem iwaniec_tendsto_log_floor_difference :
    Tendsto (fun x : Real => Real.log (⌊x⌋₊ : Real) - Real.log x) atTop (nhds 0) := by
  have h := (Real.continuousAt_log (by norm_num : (1 : Real) ≠ 0)).tendsto.comp
    (tendsto_nat_floor_div_atTop (R := Real))
  rw [Real.log_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
  have hn : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hn0 : (0 : Real) < ⌊x⌋₊ := by exact_mod_cast (show 0 < ⌊x⌋₊ by omega)
  exact Real.log_div hn0.ne' (by linarith : x ≠ 0)

theorem iwaniec_tendsto_log_floor_ratio :
    Tendsto (fun x : Real => Real.log (⌊x⌋₊ : Real) / Real.log x) atTop (nhds 1) := by
  have h := (tendsto_const_nhds (x := (1 : Real))).add
    (iwaniec_tendsto_log_floor_difference.div_atTop Real.tendsto_log_atTop)
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (1 : Real)] with x hx
  field_simp [(Real.log_pos hx).ne']
  <;> ring

theorem iwaniec_tendsto_loglog_floor_difference :
    Tendsto (fun x : Real => Real.log (Real.log (⌊x⌋₊ : Real)) - Real.log (Real.log x)) atTop (nhds 0) := by
  have h := (Real.continuousAt_log (by norm_num : (1 : Real) ≠ 0)).tendsto.comp iwaniec_tendsto_log_floor_ratio
  rw [Real.log_one] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : Real)] with x hx
  have hn : 2 ≤ ⌊x⌋₊ := Nat.le_floor hx
  have hn1 : (1 : Real) < ⌊x⌋₊ := by exact_mod_cast (show 1 < ⌊x⌋₊ by omega)
  exact Real.log_div (Real.log_pos hn1).ne' (Real.log_pos (show 1 < x by linarith)).ne'

/-- The actual natural-cutoff Mertens constant is transported to real x;
the floor and logarithmic correction are proved, not silently reindexed. -/
theorem tendsto_iwaniecMertensRealRemainder : Tendsto iwaniecMertensRealRemainder atTop (nhds 0) := by
  have h := (tendsto_iwaniecPrimeReciprocalRemainder_zero.comp (tendsto_nat_floor_atTop (α := Real))).add
    iwaniec_tendsto_loglog_floor_difference
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards with x
  unfold iwaniecMertensRealRemainder iwaniecPrimeReciprocalRemainder iwaniecPrimeReciprocalReal
  simp only [Function.comp_apply]
  ring

end

end Erdos1212Kernel
