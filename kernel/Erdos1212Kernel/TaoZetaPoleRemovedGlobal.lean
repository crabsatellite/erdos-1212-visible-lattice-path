import Erdos1212Kernel.TaoPerronRieszInterchange

namespace Erdos1212Kernel

noncomputable section

open Filter Metric Topology

set_option maxHeartbeats 1900000

theorem analyticAt_taoZetaPoleRemoved_global (s : Complex) :
    AnalyticAt Complex taoZetaPoleRemoved s := by
  by_cases hs : s = 1
  · subst s
    exact analyticAt_taoZetaPoleRemoved_one
  · have hEq : taoZetaPoleRemoved =ᶠ[nhds s]
        (fun z => (z - 1) * riemannZeta z) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hs] with z hz
      exact taoZetaPoleRemoved_of_ne_one hz
    have hzeta : AnalyticAt Complex riemannZeta s :=
      analyticOn_riemannZeta s (by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs)
    exact ((analyticAt_id.sub analyticAt_const).mul hzeta).congr hEq.symm

theorem taoZetaPoleRemoved_ne_zero_of_eq_one_or_zeta_ne_zero
    {s : Complex} (hs : s = 1 ∨ riemannZeta s ≠ 0) :
    taoZetaPoleRemoved s ≠ 0 := by
  rcases hs with rfl | hzeta
  · simp
  · by_cases hs1 : s = 1
    · subst s
      simp
    · rw [taoZetaPoleRemoved_of_ne_one hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1) hzeta

theorem analyticAt_logDeriv_taoZetaPoleRemoved
    {s : Complex} (hH : taoZetaPoleRemoved s ≠ 0) :
    AnalyticAt Complex (logDeriv taoZetaPoleRemoved) s := by
  have hAn := analyticAt_taoZetaPoleRemoved_global s
  unfold logDeriv
  exact hAn.deriv.div hAn hH

theorem taoZetaLogDerivative_eq_inv_sub_logDeriv_poleRemoved_of_ne_zero
    {s : Complex} (hs1 : s ≠ 1) (hzeta : riemannZeta s ≠ 0) :
    taoZetaLogDerivative s = 1 / (s - 1) - logDeriv taoZetaPoleRemoved s := by
  have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hEq : taoZetaPoleRemoved =ᶠ[nhds s]
      (fun z => (z - 1) * riemannZeta z) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs1] with z hz
    exact taoZetaPoleRemoved_of_ne_one hz
  have hval := hEq.self_of_nhds
  have hderiv := hEq.deriv_eq
  have hmul := logDeriv_mul s hsub hzeta
    (differentiableAt_id.sub_const 1) (differentiableAt_riemannZeta hs1)
  have hlinear : logDeriv (fun z : Complex => z - 1) s = 1 / (s - 1) := by
    unfold logDeriv
    simp only [Pi.div_apply]
    rw [deriv_sub_const, show deriv (fun z : Complex => z) s = 1 by
      simpa using (deriv_id (x := s))]
  have hmul' : logDeriv (fun z => (z - 1) * riemannZeta z) s =
      1 / (s - 1) + logDeriv riemannZeta s := by
    simpa only [id_eq, hlinear] using hmul
  have hlogEq : logDeriv taoZetaPoleRemoved s =
      logDeriv (fun z => (z - 1) * riemannZeta z) s := by
    unfold logDeriv
    simp only [Pi.div_apply]
    rw [hderiv, hval]
  rw [hlogEq, hmul']
  unfold taoZetaLogDerivative logDeriv
  simp only [Pi.div_apply]
  ring

end

end Erdos1212Kernel
