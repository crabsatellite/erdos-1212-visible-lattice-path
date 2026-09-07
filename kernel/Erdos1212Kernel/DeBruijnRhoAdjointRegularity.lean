import Erdos1212Kernel.DeBruijnAdjointEquation
import Erdos1212Kernel.DeBruijnDickmanZeroExtension

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem deBruijnRho_hasDerivAt_except_one {s : Real} (hs : 0 < s) (hsOne : s ≠ 1) :
    HasDerivAt deBruijnRho (-deBruijnRho (s - 1) / s) s := by
  rcases lt_or_gt_of_ne hsOne with hlow | hhigh
  · rw [deBruijnRho_eq_zero (by linarith : s - 1 < 0), neg_zero, zero_div]
    apply (hasDerivAt_const s (1 : Real)).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hs hlow] with t ht
    exact deBruijnRho_initial ⟨ht.1.le, ht.2.le⟩
  · have h := iwaniecDickman_hasDerivAt hhigh
    rw [← deBruijnRho_eq_dickman (by linarith : 0 ≤ s - 1)] at h
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hs] with t ht
    exact deBruijnRho_eq_dickman ht.le

def deBruijnRhoG1Integrand (s : Real) : Real := deBruijnRho s * deBruijn1951G1 s

theorem deBruijnRhoG1Integrand_intervalIntegrable {a b : Real} (ha : -1 < a) (hb : -1 < b) :
    IntervalIntegrable deBruijnRhoG1Integrand volume a b := by
  apply (deBruijnRho_intervalIntegrable a b).mul_continuousOn
  apply deBruijn1951G1_continuousOn.mono
  intro x hx
  exact (lt_min ha hb).trans_le hx.1

theorem deBruijnRhoG1Integrand_eq_zero {s : Real} (hs : s < 0) : deBruijnRhoG1Integrand s = 0 := by
  rw [deBruijnRhoG1Integrand, deBruijnRho_eq_zero hs, zero_mul]

theorem deBruijnRhoG1Integrand_continuousAt {s : Real} (hs : -1 < s) (hsZero : s ≠ 0) :
    ContinuousAt deBruijnRhoG1Integrand s := by
  rcases lt_or_gt_of_ne hsZero with hneg | hpos
  · apply (continuousAt_const (y := (0 : Real))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hneg] with t ht
    exact deBruijnRhoG1Integrand_eq_zero ht
  · exact (deBruijnRho_continuousOn_positive.continuousAt (Ioi_mem_nhds hpos)).mul
      (deBruijn1951G1_hasDerivAt hs).continuousAt

def deBruijnRhoG1Primitive (s : Real) : Real := ∫ x in (0 : Real)..s, deBruijnRhoG1Integrand x

/-- Local integrability, not continuity of the zero extension at zero,
provides the primitive's continuity across that endpoint. -/
theorem deBruijnRhoG1Primitive_continuousAt {s : Real} (hs : -1 < s) :
    ContinuousAt deBruijnRhoG1Primitive s := by
  let l : Real := (min 0 s - 1) / 2
  let r : Real := max 0 s + 1
  have hm : -1 < min (0 : Real) s := lt_min (by norm_num) hs
  have hl : -1 < l := by dsimp [l]; linarith
  have hlm : l < min (0 : Real) s := by dsimp [l]; linarith
  have hl0 : l < 0 := hlm.trans_le (min_le_left _ _)
  have hls : l < s := hlm.trans_le (min_le_right _ _)
  have hr0 : 0 < r := by dsimp [r]; linarith [le_max_left (0 : Real) s]
  have hsr : s < r := by dsimp [r]; linarith [le_max_right (0 : Real) s]
  have hlr : l ≤ r := le_of_lt (hl0.trans hr0)
  have h0mem : (0 : Real) ∈ Set.uIcc l r := by
    rw [Set.uIcc_of_le hlr]
    exact ⟨hl0.le, hr0.le⟩
  have hc := intervalIntegral.continuousOn_primitive_interval'
    (deBruijnRhoG1Integrand_intervalIntegrable hl (by linarith : -1 < r)) h0mem
  rw [Set.uIcc_of_le hlr] at hc
  exact hc.continuousAt (Icc_mem_nhds hls hsr)

theorem deBruijnRhoG1Primitive_hasDerivAt {s : Real} (hs : -1 < s) (hsZero : s ≠ 0) :
    HasDerivAt deBruijnRhoG1Primitive (deBruijnRhoG1Integrand s) s := by
  have hc := deBruijnRhoG1Integrand_continuousAt hs hsZero
  have hopen : IsOpen (Set.Ioi (-1 : Real) \ {(0 : Real)}) := isOpen_Ioi.inter isClosed_singleton.isOpen_compl
  have hmeas : StronglyMeasurableAtFilter deBruijnRhoG1Integrand (nhds s) volume :=
    ContinuousAt.stronglyMeasurableAtFilter hopen
      (fun x hx => deBruijnRhoG1Integrand_continuousAt hx.1 (by simpa only [Set.mem_singleton_iff] using hx.2))
      s ⟨hs, by simpa only [Set.mem_singleton_iff] using hsZero⟩
  exact intervalIntegral.integral_hasDerivAt_right
    (deBruijnRhoG1Integrand_intervalIntegrable (by norm_num) hs)
    hmeas hc

theorem deBruijnRhoG1Primitive_sub {a : Real} (ha : 0 < a) :
    deBruijnRhoG1Primitive a - deBruijnRhoG1Primitive (a - 1) =
      ∫ u in (a - 1)..a, deBruijnRhoG1Integrand u := by
  exact intervalIntegral.integral_interval_sub_left
    (deBruijnRhoG1Integrand_intervalIntegrable (by norm_num) (by linarith : -1 < a))
    (deBruijnRhoG1Integrand_intervalIntegrable (by norm_num) (by linarith : -1 < a - 1))

theorem deBruijnRhoG1Primitive_nonpositive {s : Real} (hs : s ≤ 0) : deBruijnRhoG1Primitive s = 0 := by
  unfold deBruijnRhoG1Primitive
  apply intervalIntegral.integral_zero_ae
  filter_upwards [volume.ae_ne (0 : Real)] with x hx hmem
  rw [Set.uIoc_of_ge hs] at hmem
  exact deBruijnRhoG1Integrand_eq_zero (lt_of_le_of_ne hmem.2 hx)

end

end Erdos1212Kernel
