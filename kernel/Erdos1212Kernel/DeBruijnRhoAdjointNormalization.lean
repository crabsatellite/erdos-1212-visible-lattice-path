import Erdos1212Kernel.DeBruijnRhoAdjointPairing
import Erdos1212Kernel.DeBruijnAdjointBoundaryNormalization

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1200000

theorem deBruijnRhoG1Pairing_initial {a : Real} (ha : a ∈ Set.Ioc (0 : Real) 1) :
    deBruijnRhoG1Pairing a = deBruijnRhoG1Primitive a - a * deBruijn1951G1 (a - 1) := by
  rw [deBruijnRhoG1Pairing_eq_primitive ha.1,
    deBruijnRhoG1Primitive_nonpositive (by linarith [ha.2] : a - 1 ≤ 0),
    deBruijnRho_initial ⟨ha.1.le, ha.2⟩]
  ring

theorem tendsto_deBruijnRhoG1Pairing_boundary :
    Tendsto deBruijnRhoG1Pairing (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.exp Real.eulerMascheroniConstant)) := by
  have hP : Tendsto deBruijnRhoG1Primitive (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have h := (deBruijnRhoG1Primitive_continuousAt (s := (0 : Real)) (by norm_num)).tendsto
    rw [deBruijnRhoG1Primitive_nonpositive (by norm_num : (0 : Real) ≤ 0)] at h
    exact h.mono_left nhdsWithin_le_nhds
  have h := hP.add deBruijn1951_G1_boundary_normalization
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    eventually_nhdsWithin_of_eventually_nhds (Iic_mem_nhds (show (0 : Real) < 1 by norm_num))] with a ha hOne
  rw [deBruijnRhoG1Pairing_initial ⟨ha, hOne⟩]
  ring

/-- The source normalization `(rho,G1)=exp(gamma)` for every positive
pairing parameter, consuming both actual solution producers. -/
theorem deBruijnRhoG1Pairing_normalization {a : Real} (ha : 0 < a) :
    deBruijnRhoG1Pairing a = Real.exp Real.eulerMascheroniConstant := by
  have hconst : Tendsto deBruijnRhoG1Pairing (nhdsWithin 0 (Set.Ioi 0)) (nhds (deBruijnRhoG1Pairing a)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (deBruijnRhoG1Pairing_constant ht ha).symm
  exact tendsto_nhds_unique hconst tendsto_deBruijnRhoG1Pairing_boundary

theorem deBruijn1951_rho_G1_pairing {a : Real} (ha : 0 < a) :
    (∫ u in (a - 1)..a, deBruijnRho u * deBruijn1951G1 u) - a * deBruijnRho a * deBruijn1951G1 (a - 1) =
      Real.exp Real.eulerMascheroniConstant :=
  deBruijnRhoG1Pairing_normalization ha

end

end Erdos1212Kernel
