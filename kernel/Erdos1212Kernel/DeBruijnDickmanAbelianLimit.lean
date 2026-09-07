import Erdos1212Kernel.DeBruijnDickmanAbelianBounds

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

/-- The limit of the exact right-hand side of de Bruijn 1951 (2.15).
The principal-value-to-tail reduction for G1 is a separate obligation. -/
theorem tendsto_deBruijn1951BoundaryAverage :
    Tendsto deBruijn1951BoundaryAverage (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.exp Real.eulerMascheroniConstant)) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    have hc : Continuous (fun a : Real => Real.exp Real.eulerMascheroniConstant * Real.exp (-a)) :=
      continuous_const.mul (Real.continuous_exp.comp continuous_neg)
    have h0 : ContinuousWithinAt (fun a : Real => Real.exp Real.eulerMascheroniConstant * Real.exp (-a))
        (Set.Ioi 0) 0 := hc.continuousAt.continuousWithinAt
    have hl : Tendsto (fun a : Real => Real.exp Real.eulerMascheroniConstant * Real.exp (-a))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp Real.eulerMascheroniConstant)) := by simpa using h0.tendsto
    have he := hl.eventually (Ioi_mem_nhds hb)
    filter_upwards [self_mem_nhdsWithin, he] with a ha he
    have haPos : 0 < a := ha
    have he' : b < Real.exp Real.eulerMascheroniConstant * Real.exp (-a) := he
    exact he'.trans_le (deBruijn1951BoundaryAverage_lower haPos)
  · intro b hb
    have he := tendsto_deBruijn1951Phi.eventually (Iio_mem_nhds hb)
    obtain ⟨R, hR, hPhi⟩ := ((eventually_ge_atTop (1 : Real)).and he).exists
    have hPhi' : deBruijn1951Phi R < b := hPhi
    let upper := fun a : Real => a * (deBruijn1951Phi 1 * (R - 1)) + deBruijn1951Phi R * Real.exp (-a * R)
    have hc : Continuous upper :=
      (continuous_id.mul continuous_const).add
        (continuous_const.mul (Real.continuous_exp.comp (continuous_id.neg.mul continuous_const)))
    have h0 : ContinuousWithinAt upper (Set.Ioi 0) 0 := hc.continuousAt.continuousWithinAt
    have hl : Tendsto upper (nhdsWithin 0 (Set.Ioi 0)) (nhds (deBruijn1951Phi R)) := by
      simpa only [upper, zero_mul, neg_zero, Real.exp_zero, mul_one, zero_add] using h0.tendsto
    have heU := hl.eventually (Iio_mem_nhds hPhi')
    filter_upwards [self_mem_nhdsWithin, heU] with a ha heU
    have haPos : 0 < a := ha
    have heU' : upper a < b := heU
    exact (deBruijn1951BoundaryAverage_upper haPos hR).trans_lt heU'

theorem deBruijn1951_abelian_normalization :
    Tendsto (fun a : Real => a * ∫ z in Set.Ioi (1 : Real),
      Real.exp (-a * z) * (z⁻¹ * Real.exp (-(∫ t in (0 : Real)..(-z), (Real.exp t - 1) / t))))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp Real.eulerMascheroniConstant)) := by
  exact tendsto_deBruijn1951BoundaryAverage

end

end Erdos1212Kernel
