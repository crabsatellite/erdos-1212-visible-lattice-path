import Erdos1212Kernel.IwaniecXiRoundedBound

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

/-- Scalar long-tail comparison with the source's real split.  The small
prime sum will be supplied at the actual far cutoff, not at a larger pool. -/
theorem iwaniecXi_sqrt_tail_scalar
    {xi t : Real} (hxi : 2 ≤ xi) (hv : 2 ≤ Real.log xi)
    (hlogv : 6 ≤ Real.log (Real.log xi)) (ht : 1 ≤ t)
    (htv : t ≤ 2 * Real.log xi) :
    2 * (Real.sqrt t / iwaniecXiSplit xi) ^ iwaniecXiSplit xi ≤
      Real.exp (-xi * Real.log xi + xi * Real.log (Real.log xi)) := by
  let v := Real.log xi
  let q := 1 - 1 / v
  let a := iwaniecXiSplit xi
  have hxiPos : 0 < xi := by linarith
  have hvPos : 0 < v := by dsimp [v]; linarith
  have hvSub : 0 < v - 1 := by dsimp [v]; linarith
  have hqEq : q = (v - 1) / v := by dsimp [q]; field_simp
  have hqPos : 0 < q := by rw [hqEq]; exact div_pos hvSub hvPos
  have haEq : a = xi * q := by dsimp [a, q, iwaniecXiSplit, v]; ring
  have haPos : 0 < a := by rw [haEq]; exact mul_pos hxiPos hqPos
  have haLe : a ≤ xi := by
    dsimp [a, iwaniecXiSplit]
    exact sub_le_self _ (div_nonneg hxiPos.le hvPos.le)
  have hlogq := Real.one_sub_inv_le_log_of_pos hqPos
  have hinv : 1 - q⁻¹ = -1 / (v - 1) := by
    rw [hqEq]
    field_simp [hvSub.ne', hvPos.ne']
    ring
  rw [hinv] at hlogq
  have hrecip : (1 : Real) / (v - 1) ≤ 2 / v := by
    rw [div_le_div_iff₀ hvSub hvPos]
    dsimp [v]
    linarith
  have hlogqLower : -2 / v ≤ Real.log q := by
    have hneg : -2 / v ≤ -1 / (v - 1) := by
      simpa only [neg_div] using neg_le_neg hrecip
    exact hneg.trans hlogq
  have hloga : v - 2 / v ≤ Real.log a := by
    rw [haEq, Real.log_mul hxiPos.ne' hqPos.ne']
    convert add_le_add (le_refl v) hlogqLower using 1 <;> dsimp [v] <;> ring
  have haV : a * v = xi * (v - 1) := by
    dsimp [a, iwaniecXiSplit, v]
    field_simp [hvPos.ne']
  have hproduct : xi * (v - 1) - 2 * xi / v ≤ a * Real.log a := by
    have hdiv := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left haLe (show (0 : Real) ≤ 2 by norm_num)) hvPos.le
    calc
      xi * (v - 1) - 2 * xi / v ≤ xi * (v - 1) - 2 * a / v := by linarith
      _ = a * (v - 2 / v) := by rw [← haV]; ring
      _ ≤ a * Real.log a := mul_le_mul_of_nonneg_left hloga haPos.le
  have htPos : 0 < t := by linarith
  have hrootPos : 0 < Real.sqrt t := Real.sqrt_pos.mpr htPos
  have hrootOne : 1 ≤ Real.sqrt t := by
    simpa using Real.sqrt_le_sqrt ht
  have hlogRootNonneg : 0 ≤ Real.log (Real.sqrt t) := Real.log_nonneg hrootOne
  have hlogt : Real.log t ≤ Real.log 2 + Real.log v := by
    have h := Real.log_le_log htPos htv
    rwa [Real.log_mul (by norm_num) hvPos.ne'] at h
  have hlogRoot : Real.log (Real.sqrt t) ≤ (Real.log 2 + Real.log v) / 2 := by
    rw [Real.log_sqrt htPos.le]
    linarith
  have hnumerator : a * Real.log (Real.sqrt t) ≤
      xi * ((Real.log 2 + Real.log v) / 2) :=
    mul_le_mul haLe hlogRoot hlogRootNonneg hxiPos.le
  have hdivSmall : 2 * xi / v ≤ xi := by
    rw [div_le_iff₀ hvPos]
    change 2 ≤ v at hv
    nlinarith
  have hlog2Le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
    linarith
  have hcoeff : Real.log 2 ≤ xi / 2 := by linarith
  have hlogvMul : 6 * xi ≤ xi * Real.log v := by
    have h := mul_le_mul_of_nonneg_left hlogv hxiPos.le
    dsimp [v] at h ⊢
    nlinarith
  have hlogBound : Real.log 2 + a * Real.log (Real.sqrt t / a) ≤
      -xi * v + xi * Real.log v := by
    rw [Real.log_div hrootPos.ne' haPos.ne']
    have hlog2Mul := mul_le_mul_of_nonneg_left hlog2Le hxiPos.le
    nlinarith
  have hpowEq : 2 * (Real.sqrt t / a) ^ a =
      Real.exp (Real.log 2 + a * Real.log (Real.sqrt t / a)) := by
    rw [Real.rpow_def_of_pos (div_pos hrootPos haPos), Real.exp_add,
      Real.exp_log (show (0 : Real) < 2 by norm_num)]
    congr 1
    congr 1
    ring
  change 2 * (Real.sqrt t / a) ^ a ≤ _
  rw [hpowEq]
  exact Real.exp_le_exp.mpr hlogBound

end

end Erdos1212Kernel
