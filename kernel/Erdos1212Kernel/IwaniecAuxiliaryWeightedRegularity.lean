import Erdos1212Kernel.IwaniecAuxiliaryWeightedFunctions

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

theorem iwaniecAuxWeightBase_monotoneOn (level : Real) :
    MonotoneOn (iwaniecAuxWeightBase level) (Set.Ici (1 : Real)) := by
  intro x hx y hy hxy
  have hxPos : 0 < x := by linarith [hx.out]
  have hlog := Real.log_le_log hxPos hxy
  have hp := pow_le_pow_left₀ (Real.log_nonneg hx) hlog 5
  have hsq := pow_le_pow_left₀ hxPos.le hxy 2
  have hprod := mul_le_mul hsq hp (pow_nonneg (Real.log_nonneg hx) 5) (sq_nonneg y)
  have hdiv := div_le_div_of_nonneg_right hprod (sq_nonneg (Real.log level))
  unfold iwaniecAuxWeightBase
  simpa only [add_comm] using add_le_add_left hdiv 1

theorem iwaniecAuxWeightLowerPower_continuousAt (level : Real) {s : Real} (hs : 1 ≤ s) :
    ContinuousAt (iwaniecAuxWeightLowerPower level) s := by
  have hbase := iwaniecAuxWeightBase_hasDerivAt level (show 0 < s by linarith)
  have hexp : HasDerivAt (fun t : Real => 5 * (t - 1)) 5 s := by
    simpa only [id_eq, mul_one] using ((hasDerivAt_id s).sub_const 1).const_mul 5
  exact (hbase.rpow hexp (iwaniecAuxWeightBase_pos level hs)).continuousAt

theorem iwaniecAuxWeightedIntegrand_continuousOn (rank : Nat) (level : Real) :
    ContinuousOn (iwaniecAuxWeightedIntegrand rank level) (Set.Ioi (3 : Real)) := by
  have hc : ContinuousOn (iwaniecAuxWeightLowerPower level) (Set.Ioi (3 : Real)) := by
    intro s hs
    exact (iwaniecAuxWeightLowerPower_continuousAt level (by linarith [hs.out])).continuousWithinAt
  apply (hc.mul (iwaniecAuxGKernel_continuousOn rank)).congr
  intro s _hs
  exact iwaniecAuxWeightedIntegrand_eq rank level s

theorem iwaniecAuxTau_continuousOn (rank : Nat) {level : Real} (hy : 1 < level) :
    ContinuousOn (iwaniecAuxTau rank level) (Set.Ioi (3 : Real)) := by
  intro s hs
  exact (iwaniecAuxTau_hasDerivAt rank hy hs).continuousAt.continuousWithinAt

end

end Erdos1212Kernel
