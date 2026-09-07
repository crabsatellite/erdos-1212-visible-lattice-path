import Erdos1212Kernel.IwaniecInductionFixedWeight
import Erdos1212Kernel.IwaniecInductionExponentialError

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 700000

theorem iwaniecFar_weight_base_lower {level s : Real}
    (hy : 1 < level) (hs : 3 ≤ s)
    (hu : 1 ≤ Real.log (Real.log (3 * level)))
    (hhalf : iwaniecPaperXi level / 2 ≤ s)
    (hlog : Real.log (Real.log (3 * level)) / 2 ≤ Real.log s) :
    Real.log (Real.log (3 * level)) ^ (3 / 5 : Real) / 128 ≤ iwaniecAuxWeightBase level s := by
  let u := Real.log (Real.log (3 * level))
  let L := Real.log level
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hL : 0 < L := Real.log_pos hy
  have hs0 : 0 < s := by linarith
  have hden : 0 < u ^ (11 / 5 : Real) := Real.rpow_pos_of_pos hu0 _
  have hLscale : L ≤ 2 * s * u ^ (11 / 5 : Real) := by
    apply (div_le_iff₀ hden).mp
    change iwaniecPaperXi level ≤ 2 * s
    linarith only [hhalf]
  have hLs := pow_le_pow_left₀ hL.le hLscale 2
  have hdenSq : (u ^ (11 / 5 : Real)) ^ 2 = u ^ (22 / 5 : Real) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hu0.le]
    norm_num
  have hLs' : L ^ 2 ≤ 4 * s ^ 2 * u ^ (22 / 5 : Real) := by
    rw [mul_pow, mul_pow, hdenSq] at hLs
    norm_num at hLs
    exact hLs
  have hpowers : u ^ (3 / 5 : Real) * u ^ (22 / 5 : Real) = u ^ 5 := by
    rw [← Real.rpow_add hu0]
    norm_num
  have hscale := mul_le_mul_of_nonneg_left hLs' (Real.rpow_nonneg hu0.le (3 / 5 : Real))
  have hscale' : u ^ (3 / 5 : Real) * L ^ 2 ≤ 4 * s ^ 2 * u ^ 5 := by
    have heq : u ^ (3 / 5 : Real) * (4 * s ^ 2 * u ^ (22 / 5 : Real)) = 4 * s ^ 2 * u ^ 5 := by
      calc
        _ = 4 * s ^ 2 * (u ^ (3 / 5 : Real) * u ^ (22 / 5 : Real)) := by ring
        _ = _ := by rw [hpowers]
    rwa [heq] at hscale
  have hlogpow := pow_le_pow_left₀ (show 0 ≤ u / 2 by positivity) hlog 5
  have hlogpow' : u ^ 5 ≤ 32 * Real.log s ^ 5 := by nlinarith only [hlogpow]
  have hprod := mul_le_mul_of_nonneg_left hlogpow' (show 0 ≤ 4 * s ^ 2 by positivity)
  have hraw : u ^ (3 / 5 : Real) / 128 ≤ s ^ 2 * Real.log s ^ 5 / L ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    nlinarith only [hscale', hprod]
  unfold iwaniecAuxWeightBase
  exact hraw.trans (by dsimp [L]; linarith)

theorem iwaniecFar_weight_power_lower {level s : Real}
    (hy : 1 < level) (hs : 3 ≤ s)
    (hu : 1 ≤ Real.log (Real.log (3 * level)))
    (hhalf : iwaniecPaperXi level / 2 ≤ s)
    (hloglo : Real.log (Real.log (3 * level)) / 2 ≤ Real.log s)
    (hloghi : Real.log s ≤ Real.log (Real.log (3 * level))) :
    Real.exp (3 * s * Real.log (Real.log s) - (5 * Real.log 128) * s) ≤
      iwaniecAuxWeightPower level s := by
  let u := Real.log (Real.log (3 * level))
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hs0 : 0 < s := by linarith
  have hlogpos : 0 < Real.log s := Real.log_pos (by linarith)
  have hbase := iwaniecFar_weight_base_lower hy hs hu hhalf hloglo
  have hlogbase := Real.log_le_log (div_pos (Real.rpow_pos_of_pos hu0 (3 / 5 : Real)) (by norm_num)) hbase
  rw [Real.log_div (Real.rpow_pos_of_pos hu0 (3 / 5 : Real)).ne' (by norm_num : (128 : Real) ≠ 0),
    Real.log_rpow hu0] at hlogbase
  have hloglog := Real.log_le_log hlogpos hloghi
  have hfirst := mul_le_mul_of_nonneg_right hlogbase (show 0 ≤ 5 * s by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hloglog (show 0 ≤ 3 * s by positivity)
  unfold iwaniecAuxWeightPower
  rw [Real.rpow_def_of_pos (iwaniecAuxWeightBase_pos level (by linarith))]
  apply Real.exp_le_exp.mpr
  nlinarith only [hfirst, hsecond]

theorem eventually_iwaniecFar_log_comparisons :
    ∀ᶠ level : Real in atTop, 1 < level ∧ 1 ≤ Real.log (Real.log (3 * level)) ∧
      ∀ s : Real, iwaniecPaperXi level / 2 ≤ s → s ≤ iwaniecPaperXi level →
        3 ≤ s ∧ Real.log (Real.log (3 * level)) / 2 ≤ Real.log s ∧
          Real.log s ≤ Real.log (Real.log (3 * level)) := by
  have hratio := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_iwaniecLogLogThree_atTop
  filter_upwards [eventually_gt_atTop (1 : Real),
    tendsto_iwaniecLogLogThree_atTop.eventually_ge_atTop (max 10 (4 * (1 + Real.log 2))),
    tendsto_iwaniecPaperXi_atTop.eventually_ge_atTop 6,
    tendsto_iwaniecShiftedLogLog_difference.eventually (Iio_mem_nhds (show (0 : Real) < 1 by norm_num)),
    hratio.eventually (Iio_mem_nhds (show (0 : Real) < 1 / 10 by norm_num))]
    with level hy hu hξ hdiff hsmall
  let u := Real.log (Real.log (3 * level))
  have hu10 : 10 ≤ u := (le_max_left _ _).trans hu
  have huconst : 4 * (1 + Real.log 2) ≤ u := (le_max_right _ _).trans hu
  have hu0 : 0 < u := by linarith
  have hL : 0 < Real.log level := Real.log_pos hy
  have hξ0 : 0 < iwaniecPaperXi level := by linarith
  have hlogu : Real.log u ≤ u / 10 := by
    have hh := (div_lt_iff₀ hu0).mp (show Real.log u / u < 1 / 10 from hsmall)
    linarith only [hh]
  have hlogξ : Real.log (iwaniecPaperXi level) = Real.log (Real.log level) - (11 / 5 : Real) * Real.log u := by
    unfold iwaniecPaperXi
    rw [Real.log_div hL.ne' (Real.rpow_pos_of_pos hu0 _).ne', Real.log_rpow hu0]
  have hloghalf : u / 2 ≤ Real.log (iwaniecPaperXi level / 2) := by
    rw [Real.log_div hξ0.ne' (by norm_num : (2 : Real) ≠ 0), hlogξ]
    change u - Real.log (Real.log level) < 1 at hdiff
    nlinarith only [hdiff, hlogu, huconst, hu10]
  refine ⟨hy, by dsimp [u] at hu10; linarith, ?_⟩
  intro s hs hstop
  have hs3 : 3 ≤ s := by linarith
  have hs0 : 0 < s := by linarith
  have hlo := Real.log_le_log (div_pos hξ0 (by norm_num)) hs
  have hhi := Real.log_le_log hs0 (hstop.trans (iwaniecPaperXi_le_exp_loglog hy (by dsimp [u] at hu10; linarith)))
  rw [Real.log_exp] at hhi
  exact ⟨hs3, hloghalf.trans hlo, hhi⟩

end

end Erdos1212Kernel
