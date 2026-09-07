import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1000000

def iwaniecXiSplit (xi : Real) : Real := xi - xi / Real.log xi

def iwaniecXiSplitThreshold (xi : Real) : Nat := ⌈iwaniecXiSplit xi⌉₊

theorem iwaniecXiSplit_pos {xi : Real} (hxi : 1 < xi) (hlog : 1 < Real.log xi) :
    0 < iwaniecXiSplit xi := by
  unfold iwaniecXiSplit
  have hdiv : xi / Real.log xi < xi := by
    rw [div_lt_iff₀ (by linarith : 0 < Real.log xi)]
    nlinarith
  linarith

/-- Exact classification of the paper's short indices `k < xi_1`. -/
theorem iwaniecXiSplitThreshold_short_iff (xi : Real) (k : Nat) :
    k < iwaniecXiSplitThreshold xi ↔ (k : Real) < iwaniecXiSplit xi :=
  Nat.lt_ceil

theorem iwaniecXiSplitThreshold_long_iff (xi : Real) (k : Nat) :
    iwaniecXiSplitThreshold xi ≤ k ↔ iwaniecXiSplit xi ≤ (k : Real) :=
  Nat.ceil_le

theorem iwaniecXiSplitThreshold_pos {xi : Real} (hxi : 1 < xi)
    (hlog : 1 < Real.log xi) :
    0 < iwaniecXiSplitThreshold xi := Nat.ceil_pos.mpr (iwaniecXiSplit_pos hxi hlog)

theorem iwaniecXiSplitThreshold_pred_lt {xi : Real} (hxi : 1 < xi)
    (hlog : 1 < Real.log xi) :
    ((iwaniecXiSplitThreshold xi - 1 : Nat) : Real) < iwaniecXiSplit xi := by
  rw [← iwaniecXiSplitThreshold_short_iff]
  have hK := iwaniecXiSplitThreshold_pos hxi hlog
  omega

theorem iwaniecXiSplit_le_threshold (xi : Real) :
    iwaniecXiSplit xi ≤ (iwaniecXiSplitThreshold xi : Real) := Nat.le_ceil _

theorem iwaniecXiSplitThreshold_lt_add_one {xi : Real} (hxi : 1 < xi)
    (hlog : 1 < Real.log xi) :
    (iwaniecXiSplitThreshold xi : Real) < iwaniecXiSplit xi + 1 :=
  Nat.ceil_lt_add_one (iwaniecXiSplit_pos hxi hlog).le

/-- The paper's logarithm is `log (2*xi)`, not `(log xi)^2`. -/
theorem iwaniecXiSplit_ratio_bound
    {xi : Real} (hxi : 1 < xi) (hlog : 1 < Real.log xi)
    (hslack : Real.log xi ^ 2 ≤ xi * Real.log 2) :
    iwaniecXiSplit xi / (xi - 1) ≤ 1 - 1 / Real.log (2 * xi) := by
  let t := Real.log xi
  let a := Real.log 2
  have ht : 0 < t := by dsimp [t]; linarith
  have ha : 0 < a := Real.log_pos (by norm_num)
  have haOne : a ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
    dsimp [a]
    linarith
  have hats : 0 < a + t := by positivity
  have hlogMul : Real.log (2 * xi) = a + t :=
    Real.log_mul (by norm_num) (by linarith)
  have halgebra : (xi - 1) * t ≤ (xi - t) * (a + t) := by
    change t ^ 2 ≤ xi * a at hslack
    nlinarith [mul_nonneg (sub_nonneg.mpr haOne) ht.le]
  have hdivision : xi - 1 ≤ (xi / t - 1) * (a + t) := by
    have h := (le_div_iff₀ ht).2 halgebra
    have heq : ((xi - t) * (a + t)) / t = (xi / t - 1) * (a + t) := by
      field_simp
    rwa [heq] at h
  have hpay : (xi - 1) / (a + t) ≤ xi / t - 1 :=
    (div_le_iff₀ hats).2 hdivision
  rw [hlogMul, div_le_iff₀ (by linarith : 0 < xi - 1)]
  change xi - xi / t ≤ (1 - 1 / (a + t)) * (xi - 1)
  calc
    xi - xi / t ≤ xi - 1 - (xi - 1) / (a + t) := by linarith
    _ = (1 - 1 / (a + t)) * (xi - 1) := by ring

theorem iwaniecXiSplitThreshold_pred_ratio_bound
    {xi : Real} (hxi : 1 < xi) (hlog : 1 < Real.log xi)
    (hslack : Real.log xi ^ 2 ≤ xi * Real.log 2) :
    ((iwaniecXiSplitThreshold xi - 1 : Nat) : Real) / (xi - 1) ≤
      1 - 1 / Real.log (2 * xi) := by
  exact (div_le_div_of_nonneg_right (iwaniecXiSplitThreshold_pred_lt hxi hlog).le
    (by linarith)).trans (iwaniecXiSplit_ratio_bound hxi hlog hslack)

theorem eventually_iwaniecXiSplit_slack :
    ∀ᶠ xi : Real in atTop,
      2 < xi ∧ 1 < Real.log xi ∧ Real.log xi ^ 2 ≤ xi * Real.log 2 := by
  have hratio : Tendsto (fun xi : Real => Real.log xi ^ 2 / xi) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hsmall := hratio.eventually
    (gt_mem_nhds (Real.log_pos (show (1 : Real) < 2 by norm_num)))
  filter_upwards [eventually_gt_atTop (2 : Real),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (1 : Real)), hsmall]
    with xi hxi hlog hratio
  refine ⟨hxi, hlog, ?_⟩
  have h := (div_lt_iff₀ (by linarith : 0 < xi)).1 hratio
  nlinarith

end

end Erdos1212Kernel
