import Erdos1212Kernel.IwaniecQXiLogComparison

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 600000

/-- First displayed far-tail bound in the proof of Theorem 4, with
the actual Q carrier and one threshold uniform over every rank. -/
theorem eventually_iwaniecPaperQ_far_power_bound :
    ∀ᶠ level : Real in atTop, 1 < level ∧ 15 ≤ iwaniecPaperXi level ∧ ∀ rank : Nat,
      iwaniecPaperQ rank level (iwaniecPaperXi level - 1) <
        (5 * Real.log (Real.log level) / iwaniecPaperXi level) ^ iwaniecPaperXi level := by
  have hmargin := tendsto_iwaniecPaperXi_atTop.eventually eventually_iwaniecQFar_rounding_margin
  filter_upwards [eventually_iwaniecPaperQ_far_factorial_bound, hmargin,
    tendsto_iwaniecLogLog_atTop.eventually_ge_atTop 1,
    tendsto_iwaniecPaperXi_div_loglog_atTop.eventually_ge_atTop 6]
    with level hfactorial hround ht hratio
  have hT : 0 < Real.log (Real.log level) := by linarith
  have hscale := (le_div_iff₀ hT).mp hratio
  have hsmall : 5 * Real.log (Real.log level) < iwaniecPaperXi level := by linarith
  have hK := (iwaniecQFarDepth_bounds hfactorial.2.1).2.1.le
  refine ⟨hfactorial.1, hround.1, ?_⟩
  intro rank
  exact (hfactorial.2.2 rank).trans_lt
    (iwaniecQFar_rounded_power_lt hround.1 hround.2 ht hsmall hK)

/-- The source exponential far-tail rate, not an asymptotic placeholder.
No support-count bound or extra factor of level occurs in this mass estimate. -/
theorem eventually_iwaniecPaperQ_far_source_bound :
    ∀ᶠ level : Real in atTop, 1 < level ∧ ∀ rank : Nat,
      iwaniecPaperQ rank level (iwaniecPaperXi level - 1) <
        Real.exp (-iwaniecPaperXi level * Real.log (iwaniecPaperXi level) +
          iwaniecPaperXi level * Real.log (Real.log (iwaniecPaperXi level)) + 2 * iwaniecPaperXi level) := by
  filter_upwards [eventually_iwaniecPaperQ_far_power_bound, eventually_iwaniecQ_loglog_le_four_thirds_log_xi,
    tendsto_iwaniecLogLog_atTop.eventually_ge_atTop 1] with level hpower hlog ht
  refine ⟨hpower.1, ?_⟩
  intro rank
  exact (hpower.2.2 rank).trans
    (iwaniecQFar_power_lt_exponential (by linarith [hpower.2.1]) (by linarith) hlog.2)

end

end Erdos1212Kernel
