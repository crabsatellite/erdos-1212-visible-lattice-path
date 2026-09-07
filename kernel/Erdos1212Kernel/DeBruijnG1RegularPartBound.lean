import Erdos1212Kernel.DeBruijnG1Normalization
import Erdos1212Kernel.DeBruijnDickmanAbelianBounds

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijn1951NegativeTail_nonneg {v : Real} (hv : 0 ≤ v) : 0 ≤ deBruijn1951NegativeTail v := by
  unfold deBruijn1951NegativeTail
  apply MeasureTheory.integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact mul_nonneg (Real.exp_pos _).le (deBruijn1951Phi_pos (by linarith [hx.out] : 0 < x)).le

theorem deBruijn1951NegativeTail_le_phi {v : Real} (hv : 0 ≤ v) :
    deBruijn1951NegativeTail v ≤ deBruijn1951Phi 1 := by
  have h := deBruijn1951BoundaryAverage_upper (a := v + 1) (R := 1) (by linarith) le_rfl
  simp only [sub_self, mul_zero, zero_add, mul_one] at h
  change (v + 1) * deBruijn1951NegativeTail v ≤ deBruijn1951Phi 1 * Real.exp (-(v + 1)) at h
  have he : Real.exp (-(v + 1)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hphi := deBruijn1951Phi_pos (x := 1) (by norm_num)
  have heMul := mul_le_mul_of_nonneg_left he hphi.le
  have hn := deBruijn1951NegativeTail_nonneg hv
  nlinarith

theorem deBruijnG1RegularPart_abs_bound {u b : Real} (hu : 1 < u) (hb : b ∈ Set.Icc (0 : Real) 1) :
    |deBruijnG1RegularPart u b| ≤ deBruijn1951NearBound (u + 1) + deBruijn1951Phi 1 := by
  have hM : |(u - 1 + b) + 1| ≤ u + 1 := by
    rw [show (u - 1 + b) + 1 = u + b by ring, abs_of_pos (show 0 < u + b by linarith [hb.1])]
    linarith [hb.2]
  have hnear := deBruijn1951NearIntegral_abs_le hM
  have hv : 0 ≤ u - 1 + b := by linarith [hb.1]
  have hneg : |deBruijn1951NegativeTail (u - 1 + b)| ≤ deBruijn1951Phi 1 := by
    rw [abs_of_nonneg (deBruijn1951NegativeTail_nonneg hv)]
    exact deBruijn1951NegativeTail_le_phi hv
  unfold deBruijnG1RegularPart
  calc
    _ ≤ |deBruijn1951NearIntegral (u - 1 + b)| + |deBruijn1951NegativeTail (u - 1 + b)| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (deBruijn1951NearIntegral (u - 1 + b)) (-deBruijn1951NegativeTail (u - 1 + b))
    _ ≤ _ := add_le_add hnear hneg

end

end Erdos1212Kernel
