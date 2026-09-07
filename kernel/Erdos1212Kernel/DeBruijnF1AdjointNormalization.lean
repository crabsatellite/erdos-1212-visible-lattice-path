import Erdos1212Kernel.DeBruijnF1G1SaddleProducts
import Erdos1212Kernel.DeBruijnF1AdjointPairing
import Erdos1212Kernel.DeBruijnUnitWindowLimit

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

theorem tendsto_deBruijnF1G1_window :
    Tendsto (fun a : Real => ∫ u in (a - 1)..a, deBruijnF1 u * deBruijn1951G1 u) atTop (nhds 1) := by
  apply deBruijn_unit_window_integral_limit tendsto_deBruijnF1G1_product
  filter_upwards [eventually_gt_atTop (0 : Real)] with a ha
  exact deBruijnF1G1Integrand_intervalIntegrable (by linarith : -1 < a - 1) (by linarith : -1 < a)

theorem tendsto_deBruijnF1G1Pairing : Tendsto deBruijnF1G1Pairing atTop (nhds 1) := by
  simpa only [sub_zero] using tendsto_deBruijnF1G1_window.sub tendsto_deBruijnF1G1_shifted_product

/-- The source value (2.14) for the actual contour and principal-value
solutions, obtained from the proved saddle estimates and conserved pairing. -/
theorem deBruijnF1G1Pairing_normalization {a : Real} (ha : 0 < a) : deBruijnF1G1Pairing a = 1 := by
  have hconst : Tendsto deBruijnF1G1Pairing atTop (nhds (deBruijnF1G1Pairing a)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : Real)] with t ht
    exact (deBruijnF1G1Pairing_constant ht ha).symm
  exact tendsto_nhds_unique hconst tendsto_deBruijnF1G1Pairing

theorem deBruijn1951_F1_G1_pairing {a : Real} (ha : 0 < a) :
    (∫ u in (a - 1)..a, deBruijnF1 u * deBruijn1951G1 u) - a * deBruijnF1 a * deBruijn1951G1 (a - 1) = 1 :=
  deBruijnF1G1Pairing_normalization ha

end

end Erdos1212Kernel
