import Erdos1212Kernel.IwaniecQFarRoundingScalar
import Erdos1212Kernel.IwaniecXiShortDecay
import Erdos1212Kernel.IwaniecXiErrorAbsorption

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 600000

theorem iwaniec_log_twenty_thirds_lt_two : Real.log (20 / 3 : Real) < 2 := by
  have he : (8 / 3 : Real) ≤ Real.exp 1 := by
    have hh := Real.sum_le_exp_of_nonneg (x := (1 : Real)) (by norm_num) 4
    norm_num [Finset.sum_range_succ] at hh
    exact hh
  have hsq := pow_le_pow_left₀ (by norm_num : (0 : Real) ≤ 8 / 3) he 2
  have he2 : (20 / 3 : Real) < Real.exp 2 := by
    rw [show (2 : Real) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith only [hsq]
  exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : Real) < 20 / 3)).mpr he2

theorem eventually_iwaniecQ_loglog_le_four_thirds_log_xi :
    ∀ᶠ level : Real in atTop, 1 < level ∧
      Real.log (Real.log level) ≤ (4 / 3 : Real) * Real.log (iwaniecPaperXi level) := by
  have hratio := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_iwaniecLogLogThree_atTop
  filter_upwards [eventually_gt_atTop (1 : Real), tendsto_iwaniecLogLog_atTop.eventually_ge_atTop 1,
    tendsto_iwaniecLogLogThree_atTop.eventually_ge_atTop 1,
    tendsto_iwaniecShiftedLogLog_difference.eventually (Iio_mem_nhds (show (0 : Real) < 1 by norm_num)),
    hratio.eventually (Iio_mem_nhds (show (0 : Real) < 1 / 20 by norm_num))]
    with level hy ht hu hdiff hsmall
  let u := Real.log (Real.log (3 * level))
  have hu0 : 0 < u := by dsimp [u]; linarith
  have hlogu : Real.log u ≤ u / 20 := by
    have hh := (div_lt_iff₀ hu0).mp (show Real.log u / u < 1 / 20 from hsmall)
    linarith
  have hd : u - Real.log (Real.log level) < 1 := hdiff
  refine ⟨hy, ?_⟩
  rw [iwaniecPaperXi_log hy hu0]
  change Real.log (Real.log level) ≤ (4 / 3 : Real) * (Real.log (Real.log level) - (11 / 5 : Real) * Real.log u)
  linarith only [hlogu, hd, ht]

theorem iwaniecQFar_power_lt_exponential {xi T : Real} (hxi : 1 < xi) (hT : 0 < T)
    (hlog : T ≤ (4 / 3 : Real) * Real.log xi) :
    (5 * T / xi) ^ xi < Real.exp (-xi * Real.log xi + xi * Real.log (Real.log xi) + 2 * xi) := by
  have hxi0 : 0 < xi := zero_lt_one.trans hxi
  have hlogxi : 0 < Real.log xi := Real.log_pos hxi
  have hnum : 5 * T ≤ (20 / 3 : Real) * Real.log xi := by nlinarith only [hlog]
  have hlognum := Real.log_le_log (show 0 < 5 * T by positivity) hnum
  rw [Real.log_mul (by norm_num : (20 / 3 : Real) ≠ 0) hlogxi.ne'] at hlognum
  have htop : Real.log (5 * T) < Real.log (Real.log xi) + 2 := by
    linarith [iwaniec_log_twenty_thirds_lt_two]
  rw [Real.rpow_def_of_pos (show 0 < 5 * T / xi by positivity),
    Real.log_div (by positivity : 5 * T ≠ 0) hxi0.ne']
  apply Real.exp_lt_exp.mpr
  have hh := mul_lt_mul_of_pos_left htop hxi0
  nlinarith only [hh]

end

end Erdos1212Kernel
