import Erdos1212Kernel.DeBruijnDickmanPhaseTransport

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

theorem deBruijn1951Phi_pos {x : Real} (hx : 0 < x) : 0 < deBruijn1951Phi x := by
  unfold deBruijn1951Phi
  exact mul_pos (inv_pos.mpr hx) (Real.exp_pos _)

theorem deBruijn1951Phi_hasDerivAt {x : Real} (hx : 0 < x) :
    HasDerivAt deBruijn1951Phi
      (-Real.exp (-x + deBruijnPhi x) / deBruijnAdjointPrimitive x ^ 2) x := by
  have hp : 0 < deBruijnAdjointPrimitive x := by
    unfold deBruijnAdjointPrimitive
    exact mul_pos hx (Real.exp_pos _)
  have h := (deBruijnAdjointPrimitive_hasDerivAt hx).inv hp.ne'
  apply h.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact deBruijn1951Phi_eq_inv_primitive hy

theorem deBruijn1951Phi_continuousOn : ContinuousOn deBruijn1951Phi (Set.Ioi (0 : Real)) := by
  intro x hx
  exact (deBruijn1951Phi_hasDerivAt hx).continuousAt.continuousWithinAt

theorem deBruijn1951Phi_antitoneOn : AntitoneOn deBruijn1951Phi (Set.Ici (1 : Real)) := by
  intro x hx y hy hxy
  have hxPos : 0 < x := by linarith [hx.out]
  have hyPos : 0 < y := by linarith [hy.out]
  rw [deBruijn1951Phi_eq_inv_primitive hxPos, deBruijn1951Phi_eq_inv_primitive hyPos]
  have hprim := deBruijnAdjointPrimitive_monotoneOn hxPos.le hyPos.le hxy
  have hxPrim : 0 < deBruijnAdjointPrimitive x := by
    unfold deBruijnAdjointPrimitive
    exact mul_pos hxPos (Real.exp_pos _)
  exact inv_anti₀ hxPrim hprim

theorem deBruijn1951Phi_bounds {x : Real} (hx : 1 ≤ x) :
    Real.exp Real.eulerMascheroniConstant ≤ deBruijn1951Phi x ∧ deBruijn1951Phi x ≤ deBruijn1951Phi 1 := by
  constructor
  · apply le_of_tendsto tendsto_deBruijn1951Phi
    filter_upwards [eventually_ge_atTop x] with y hy
    exact deBruijn1951Phi_antitoneOn hx (hx.trans hy) hy
  · exact deBruijn1951Phi_antitoneOn (show (1 : Real) ∈ Set.Ici 1 by simp) hx hx

theorem deBruijn1951BoundaryKernel_continuousOn (a : Real) :
    ContinuousOn (deBruijn1951BoundaryKernel a) (Set.Ioi (0 : Real)) := by
  have hexp : Continuous (fun x : Real => Real.exp (-a * x)) := Real.continuous_exp.comp (continuous_const.mul continuous_id)
  exact hexp.continuousOn.mul deBruijn1951Phi_continuousOn

theorem deBruijn1951BoundaryKernel_integrable {a : Real} (ha : 0 < a) :
    IntegrableOn (deBruijn1951BoundaryKernel a) (Set.Ioi (1 : Real)) := by
  have hbase := (exp_neg_integrableOn_Ioi (1 : Real) ha).const_mul (deBruijn1951Phi 1)
  apply hbase.mono'
  · apply ((deBruijn1951BoundaryKernel_continuousOn a).mono _).aestronglyMeasurable measurableSet_Ioi
    intro x hx
    change (0 : Real) < x
    linarith [hx.out]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxOne : 1 ≤ x := (show 1 < x from hx).le
    have hp := deBruijn1951Phi_pos (x := x) (by linarith)
    unfold deBruijn1951BoundaryKernel
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le hp.le)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (deBruijn1951Phi_bounds hxOne).2 (Real.exp_pos (-a * x)).le

end

end Erdos1212Kernel
