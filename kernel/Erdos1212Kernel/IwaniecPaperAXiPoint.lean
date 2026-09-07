import Erdos1212Kernel.IwaniecXiRoundedBound
import Erdos1212Kernel.IwaniecXiScaleGrowth

namespace Erdos1212Kernel

noncomputable section

open Filter

def iwaniecXiShortMajorant (level : Real) : Real :=
  3 * level * Real.exp (-Real.log level / Real.log (2 * iwaniecPaperXi level))

def iwaniecXiLongMajorant (level : Real) : Real :=
  2 * level *
    (3 * Real.log (Real.log level) / iwaniecXiSplit (iwaniecPaperXi level)) ^
      iwaniecXiSplit (iwaniecPaperXi level)

/-- The actual paper far point, uniformly in every rank.  All growth and
rounding hypotheses of the two estimates have now been discharged. -/
theorem eventually_iwaniecPaperA_at_xi_sub_one :
    ∀ᶠ level : Real in atTop, ∀ rank : Nat,
      (iwaniecPaperA rank level (iwaniecPaperXi level - 1) : Real) ≤
        iwaniecXiShortMajorant level + iwaniecXiLongMajorant level := by
  have hslack := tendsto_iwaniecPaperXi_atTop.eventually
    eventually_iwaniecXiSplit_slack
  filter_upwards [eventually_iwaniecPaperA_rounded_xi_bound, hslack,
    tendsto_iwaniecLogLog_atTop.eventually (eventually_gt_atTop (0 : Real)),
    eventually_iwaniecPaperXiSplit_ge_six_loglog]
    with level hbound hxi hloglog hsplit
  intro rank
  exact hbound rank (iwaniecPaperXi level) hxi.1 hxi.2.1 hxi.2.2 hloglog hsplit

end

end Erdos1212Kernel
