import Erdos1212Kernel.DeBruijnRhoAdjointRegularity

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1500000

/-- The displayed pairing (2.8) for the source zero-extended rho and the
actual principal-value G1. -/
def deBruijnRhoG1Pairing (a : Real) : Real :=
  (∫ u in (a - 1)..a, deBruijnRho u * deBruijn1951G1 u) - a * deBruijnRho a * deBruijn1951G1 (a - 1)

theorem deBruijnRhoG1Pairing_eq_primitive {a : Real} (ha : 0 < a) :
    deBruijnRhoG1Pairing a = deBruijnRhoG1Primitive a - deBruijnRhoG1Primitive (a - 1) -
      a * deBruijnRho a * deBruijn1951G1 (a - 1) := by
  rw [deBruijnRhoG1Primitive_sub ha]
  rfl

theorem deBruijnRhoG1Pairing_continuousAt {a : Real} (ha : 0 < a) :
    ContinuousAt deBruijnRhoG1Pairing a := by
  have hp := deBruijnRhoG1Primitive_continuousAt (by linarith : -1 < a)
  have hshift : ContinuousAt (fun x : Real => x - 1) a := continuousAt_id.sub continuousAt_const
  have hn : ContinuousAt (fun x : Real => deBruijnRhoG1Primitive (x - 1)) a :=
    (deBruijnRhoG1Primitive_continuousAt (by linarith : -1 < a - 1)).comp (f := fun x : Real => x - 1) (x := a) hshift
  have hr := deBruijnRho_continuousOn_positive.continuousAt (Ioi_mem_nhds ha)
  have hg : ContinuousAt (fun x : Real => deBruijn1951G1 (x - 1)) a :=
    (deBruijn1951G1_hasDerivAt (by linarith : -1 < a - 1)).continuousAt.comp (f := fun x : Real => x - 1) (x := a) hshift
  have hc := (hp.sub hn).sub ((continuousAt_id.mul hr).mul hg)
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with x hx
  exact deBruijnRhoG1Pairing_eq_primitive hx

theorem deBruijnRhoG1Pairing_hasDerivAt_except_one {a : Real} (ha : 0 < a) (haOne : a ≠ 1) :
    HasDerivAt deBruijnRhoG1Pairing 0 a := by
  have hshift : HasDerivAt (fun x : Real => x - 1) 1 a := (hasDerivAt_id a).sub_const 1
  have hp := deBruijnRhoG1Primitive_hasDerivAt (by linarith : -1 < a) ha.ne'
  have hn := (deBruijnRhoG1Primitive_hasDerivAt (by linarith : -1 < a - 1) (sub_ne_zero.mpr haOne)).comp a hshift
  have hr := deBruijnRho_hasDerivAt_except_one ha haOne
  have hg := (deBruijn1951G1_hasDerivAt (by linarith : -1 < a - 1)).comp a hshift
  have hraw := (hp.sub hn).sub (((hasDerivAt_id a).mul hr).mul hg)
  have hmodel : HasDerivAt (fun x : Real => deBruijnRhoG1Primitive x - deBruijnRhoG1Primitive (x - 1) -
      x * deBruijnRho x * deBruijn1951G1 (x - 1)) 0 a := by
    apply hraw.congr_deriv
    simp only [Function.comp_apply, Pi.mul_apply, id_eq, mul_one, one_mul]
    have hcancel : a * (-deBruijnRho (a - 1) / a) = -deBruijnRho (a - 1) := by field_simp
    rw [hcancel]
    unfold deBruijnRhoG1Integrand
    have hbalance := congrArg (fun y : Real => deBruijnRho a * y) (deBruijn1951Adjoint_mass_balance ha)
    dsimp only at hbalance
    nlinarith [hbalance]
  apply hmodel.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ha] with x hx
  exact deBruijnRhoG1Pairing_eq_primitive hx

theorem deBruijnRhoG1Pairing_eq_low {a b : Real} (ha : a ∈ Set.Ioo (0 : Real) 1) (hb : b ∈ Set.Ioo (0 : Real) 1) :
    deBruijnRhoG1Pairing a = deBruijnRhoG1Pairing b := by
  apply isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
  · intro x hx
    exact (deBruijnRhoG1Pairing_hasDerivAt_except_one hx.1 hx.2.ne).differentiableAt.differentiableWithinAt
  · intro x hx
    exact (deBruijnRhoG1Pairing_hasDerivAt_except_one hx.1 hx.2.ne).deriv
  · exact ha
  · exact hb

theorem deBruijnRhoG1Pairing_eq_high {a b : Real} (ha : 1 < a) (hb : 1 < b) :
    deBruijnRhoG1Pairing a = deBruijnRhoG1Pairing b := by
  apply isOpen_Ioi.is_const_of_deriv_eq_zero isPreconnected_Ioi
  · intro x hx
    exact (deBruijnRhoG1Pairing_hasDerivAt_except_one (by linarith [hx.out]) hx.ne').differentiableAt.differentiableWithinAt
  · intro x hx
    exact (deBruijnRhoG1Pairing_hasDerivAt_except_one (by linarith [hx.out]) hx.ne').deriv
  · exact ha
  · exact hb

/-- Constancy across the rho corner at one is proved by continuity;
rho is not incorrectly declared differentiable at that point. -/
theorem deBruijnRhoG1Pairing_eq_one {a : Real} (ha : 0 < a) :
    deBruijnRhoG1Pairing a = deBruijnRhoG1Pairing 1 := by
  have hc := deBruijnRhoG1Pairing_continuousAt (a := (1 : Real)) (by norm_num)
  rcases lt_trichotomy a 1 with hlow | rfl | hhigh
  · have hlim : Tendsto deBruijnRhoG1Pairing (nhdsWithin 1 (Set.Iio 1)) (nhds (deBruijnRhoG1Pairing 1)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    have hconst : Tendsto deBruijnRhoG1Pairing (nhdsWithin 1 (Set.Iio 1)) (nhds (deBruijnRhoG1Pairing a)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds (show (0 : Real) < 1 by norm_num))] with t ht ht0
      exact (deBruijnRhoG1Pairing_eq_low ⟨ht0, ht⟩ ⟨ha, hlow⟩).symm
    exact tendsto_nhds_unique hconst hlim
  · rfl
  · have hlim : Tendsto deBruijnRhoG1Pairing (nhdsWithin 1 (Set.Ioi 1)) (nhds (deBruijnRhoG1Pairing 1)) :=
      hc.tendsto.mono_left nhdsWithin_le_nhds
    have hconst : Tendsto deBruijnRhoG1Pairing (nhdsWithin 1 (Set.Ioi 1)) (nhds (deBruijnRhoG1Pairing a)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact (deBruijnRhoG1Pairing_eq_high ht hhigh).symm
    exact tendsto_nhds_unique hconst hlim

theorem deBruijnRhoG1Pairing_constant {a b : Real} (ha : 0 < a) (hb : 0 < b) :
    deBruijnRhoG1Pairing a = deBruijnRhoG1Pairing b :=
  (deBruijnRhoG1Pairing_eq_one ha).trans (deBruijnRhoG1Pairing_eq_one hb).symm

end

end Erdos1212Kernel
