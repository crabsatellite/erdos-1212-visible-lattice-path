import Erdos1212Kernel.IwaniecPaperQFactorialTail
import Erdos1212Kernel.IwaniecXiScaleGrowth

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 650000

/-- The first integer k satisfying k>xi-3 in the source far tail. -/
def iwaniecQFarDepth (xi : Real) : Nat := Nat.floor xi - 2

theorem iwaniecQFarDepth_bounds {xi : Real} (hxi : 4 ≤ xi) :
    0 < iwaniecQFarDepth xi ∧ xi - 3 < (iwaniecQFarDepth xi : Real) ∧
      ((iwaniecQFarDepth xi + 1 : Nat) : Real) ≤ xi - 1 ∧
      xi - 2 ≤ ((iwaniecQFarDepth xi + 1 : Nat) : Real) := by
  have hfloor4 : 4 ≤ Nat.floor xi := Nat.le_floor hxi
  have hlo := Nat.floor_le (show 0 ≤ xi by linarith)
  have hhi := Nat.lt_floor_add_one xi
  have hcast : (iwaniecQFarDepth xi : Real) = (Nat.floor xi : Real) - 2 := by
    unfold iwaniecQFarDepth
    rw [Nat.cast_sub (by omega : 2 ≤ Nat.floor xi), Nat.cast_ofNat]
  have hsucc : ((iwaniecQFarDepth xi + 1 : Nat) : Real) = (Nat.floor xi : Real) - 1 := by
    rw [Nat.cast_add, Nat.cast_one, hcast]
    ring
  refine ⟨by unfold iwaniecQFarDepth; omega, ?_, ?_, ?_⟩
  · rw [hcast]
    linarith
  · rw [hsucc]
    linarith
  · rw [hsucc]
    linarith

theorem iwaniecQFarDepth_le_iff {xi : Real} (hxi : 4 ≤ xi) (k : Nat) :
    iwaniecQFarDepth xi ≤ k ↔ xi - 3 < (k : Real) := by
  have hdata := iwaniecQFarDepth_bounds hxi
  constructor
  · intro hk
    exact hdata.2.1.trans_le (by exact_mod_cast hk)
  · intro hk
    have hf := Nat.floor_le (show 0 ≤ xi by linarith)
    have hfr : (Nat.floor xi : Real) < (k : Real) + 3 := by linarith
    have hfn : Nat.floor xi < k + 3 := by exact_mod_cast hfr
    unfold iwaniecQFarDepth
    omega

/-- The actual Q far point after the source reciprocal-factorial
estimate and Stirling. The rounded lower degree is kept explicit. -/
theorem eventually_iwaniecPaperQ_far_factorial_bound :
    ∀ᶠ level : Real in atTop, 1 < level ∧ 4 ≤ iwaniecPaperXi level ∧ ∀ rank : Nat,
      iwaniecPaperQ rank level (iwaniecPaperXi level - 1) ≤
        2 * (3 * Real.log (Real.log level) / (iwaniecQFarDepth (iwaniecPaperXi level) : Real)) ^
          iwaniecQFarDepth (iwaniecPaperXi level) := by
  filter_upwards [eventually_gt_atTop (1 : Real), tendsto_iwaniecPaperXi_atTop.eventually_ge_atTop 4,
    tendsto_iwaniecLogLog_atTop.eventually_ge_atTop 1,
    tendsto_iwaniecPaperXi_div_loglog_atTop.eventually_ge_atTop 8,
    eventually_iwaniecExp_mul_primeReciprocal_le_three_loglog]
    with level hy hxi ht hratio hM
  refine ⟨hy, hxi, ?_⟩
  intro rank
  let xi := iwaniecPaperXi level
  let K := iwaniecQFarDepth xi
  let T := Real.log (Real.log level)
  let M := iwaniecStrictPrimeReciprocalSum level
  have hT : 0 < T := by dsimp [T]; linarith
  have hxiT : 8 * T ≤ xi := (le_div_iff₀ hT).mp hratio
  have hdepth := iwaniecQFarDepth_bounds hxi
  have hK : 0 < K := hdepth.1
  have hK0 : (0 : Real) < K := by exact_mod_cast hK
  have hKhigh : ((K + 1 : Nat) : Real) ≤ xi - 1 := hdepth.2.2.1
  have hKlow : xi - 2 ≤ ((K + 1 : Nat) : Real) := hdepth.2.2.2
  have hM0 : 0 ≤ M := Finset.sum_nonneg (fun p _ => inv_nonneg.mpr (Nat.cast_nonneg p))
  have heM : Real.exp 1 * M ≤ 3 * T := hM level le_rfl
  have hMle : M ≤ 3 * T := by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp_iff.mpr (by norm_num)
    have hh := mul_le_mul_of_nonneg_right he hM0
    nlinarith only [hh, heM]
  have hthreshold : 2 * M ≤ ((K + 1 : Nat) : Real) := by
    change 1 ≤ T at ht
    linarith
  have htail := iwaniecPaperQ_le_stirling_tail rank K hK hy (show 1 ≤ xi - 1 by dsimp [xi]; linarith)
    hKhigh hthreshold
  have hbase := div_le_div_of_nonneg_right heM hK0.le
  have hp := pow_le_pow_left₀ (div_nonneg (mul_nonneg (Real.exp_pos _).le hM0) hK0.le) hbase K
  exact htail.trans (mul_le_mul_of_nonneg_left hp (by norm_num))

end

end Erdos1212Kernel
