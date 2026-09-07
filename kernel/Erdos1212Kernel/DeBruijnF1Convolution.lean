import Erdos1212Kernel.DeBruijnF1Fubini
import Erdos1212Kernel.DeBruijnF1ContourBalance
import Erdos1212Kernel.DeBruijnF1Entire

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijnF1ContourIntegral_shift_average (u : Complex) :
    (∫ t in (0 : Real)..1, deBruijnF1ContourIntegral (u - (t : Complex))) =
      -(∫ x in Set.Ioi (0 : Real), deBruijnF1ShiftAverage u ((x : Complex) - (Real.pi : Complex) * Complex.I)) +
      (∫ x in (-Real.pi)..Real.pi, deBruijnF1ShiftAverage u ((x : Complex) * Complex.I) * Complex.I) +
      (∫ x in Set.Ioi (0 : Real), deBruijnF1ShiftAverage u ((x : Complex) + (Real.pi : Complex) * Complex.I)) := by
  have hcL : Continuous deBruijnF1LowerIntegral :=
    continuous_iff_continuousAt.mpr (fun v => (deBruijnF1LowerIntegral_hasDerivAt v).continuousAt)
  have hcV : Continuous deBruijnF1VerticalIntegral :=
    continuous_iff_continuousAt.mpr (fun v => (deBruijnF1VerticalIntegral_hasDerivAt v).continuousAt)
  have hcU : Continuous deBruijnF1UpperIntegral :=
    continuous_iff_continuousAt.mpr (fun v => (deBruijnF1UpperIntegral_hasDerivAt v).continuousAt)
  have hs : Continuous (fun t : Real => u - (t : Complex)) := continuous_const.sub Complex.continuous_ofReal
  have hL : IntervalIntegrable (fun t : Real => deBruijnF1LowerIntegral (u - (t : Complex))) volume 0 1 :=
    (hcL.comp hs).intervalIntegrable 0 1
  have hV : IntervalIntegrable (fun t : Real => deBruijnF1VerticalIntegral (u - (t : Complex))) volume 0 1 :=
    (hcV.comp hs).intervalIntegrable 0 1
  have hU : IntervalIntegrable (fun t : Real => deBruijnF1UpperIntegral (u - (t : Complex))) volume 0 1 :=
    (hcU.comp hs).intervalIntegrable 0 1
  have hnegL : IntervalIntegrable (fun t : Real => -deBruijnF1LowerIntegral (u - (t : Complex))) volume 0 1 := hL.neg
  have hLV : IntervalIntegrable (fun t : Real => -deBruijnF1LowerIntegral (u - (t : Complex)) +
      deBruijnF1VerticalIntegral (u - (t : Complex))) volume 0 1 := hnegL.add hV
  unfold deBruijnF1ContourIntegral
  rw [intervalIntegral.integral_add hLV hU, intervalIntegral.integral_add hnegL hV, intervalIntegral.integral_neg,
    deBruijnF1LowerIntegral_shift_average, deBruijnF1VerticalIntegral_shift_average, deBruijnF1UpperIntegral_shift_average]

theorem deBruijnF1ContourIntegral_convolution (u : Complex) :
    u * deBruijnF1ContourIntegral u = ∫ t in (0 : Real)..1, deBruijnF1ContourIntegral (u - (t : Complex)) :=
  (deBruijnF1ContourIntegral_balance u).trans (deBruijnF1ContourIntegral_shift_average u).symm

/-- The original convolution equation (2.2), now proved for the actual
contour formula (2.4), including its normalization. -/
theorem deBruijnF1Complex_convolution (u : Complex) :
    u * deBruijnF1Complex u = ∫ t in (0 : Real)..1, deBruijnF1Complex (u - (t : Complex)) := by
  calc
    _ = (1 / (2 * (Real.pi : Complex) * Complex.I)) * (u * deBruijnF1ContourIntegral u) := by
      unfold deBruijnF1Complex
      ring
    _ = (1 / (2 * (Real.pi : Complex) * Complex.I)) *
        (∫ t in (0 : Real)..1, deBruijnF1ContourIntegral (u - (t : Complex))) := by rw [deBruijnF1ContourIntegral_convolution]
    _ = ∫ t in (0 : Real)..1, (1 / (2 * (Real.pi : Complex) * Complex.I)) * deBruijnF1ContourIntegral (u - (t : Complex)) := by
      rw [intervalIntegral.integral_const_mul]
    _ = _ := rfl

/-- The real source equation consumes the proved real/complex contour
identity, rather than assuming the imaginary part disappears. -/
theorem deBruijnF1_convolution (u : Real) :
    u * deBruijnF1 u = ∫ t in (0 : Real)..1, deBruijnF1 (u - t) := by
  apply Complex.ofReal_injective
  rw [Complex.ofReal_mul, deBruijnF1_ofReal, ← intervalIntegral.integral_ofReal, deBruijnF1Complex_convolution]
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only
  rw [← Complex.ofReal_sub, deBruijnF1_ofReal]

end

end Erdos1212Kernel
