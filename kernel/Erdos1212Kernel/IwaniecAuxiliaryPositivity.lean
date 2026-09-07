import Erdos1212Kernel.IwaniecAuxiliaryConservation
import Mathlib.Topology.Order.Compact

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem iwaniecAuxM_initial_pos
    {s : Real} (hs : s ∈ Set.Icc (2 : Real) 3) : 0 < iwaniecAuxM s := by
  rw [iwaniecAuxM_initial hs.2]
  have hlog := Real.log_le_log (show 0 < s - 1 by linarith [hs.1])
    (show s - 1 ≤ (2 : Real) by linarith [hs.2])
  have hlogTwo := Real.log_le_sub_one_of_pos (show (0 : Real) < 2 by norm_num)
  have hinv : 0 < (1 : Real) / (s - 1) := one_div_pos.mpr (by linarith [hs.1])
  linarith

theorem iwaniecAuxMWindowWeight_pos {s : Real} (hs : 2 ≤ s) :
    0 < iwaniecAuxMWindowWeight s := by
  unfold iwaniecAuxMWindowWeight
  have hden : (1 : Real) < 2 * s ^ 2 := by nlinarith
  have hdiv : (1 : Real) / (2 * s ^ 2) < 1 := by
    rw [div_lt_iff₀ (by linarith : 0 < 2 * s ^ 2)]
    linarith
  linarith

theorem iwaniecAuxMCoefficient_pos {s : Real} (hs : 3 ≤ s) :
    0 < iwaniecAuxMCoefficient s := by
  unfold iwaniecAuxMCoefficient
  apply div_pos
  · nlinarith [sq_nonneg (s - 3)]
  · linarith

/-- Strict positivity from the paper's exact conserved weighted window.
The earliest nonpositive point would have a positive window integral and
a nonpositive left side, which is impossible. -/
theorem iwaniecAuxM_pos {s : Real} (hs : 2 ≤ s) : 0 < iwaniecAuxM s := by
  by_contra hnot
  have hsNonpos : iwaniecAuxM s ≤ 0 := le_of_not_gt hnot
  have hsHigh : 3 < s := by
    by_contra hnotHigh
    have hpos := iwaniecAuxM_initial_pos ⟨hs, le_of_not_gt hnotHigh⟩
    linarith
  let bad : Set Real := Set.Icc 3 s ∩ iwaniecAuxM ⁻¹' Set.Iic 0
  have hcont : ContinuousOn iwaniecAuxM (Set.Icc (3 : Real) s) := by
    apply iwaniecAuxM_continuousOn.mono
    intro x hx
    change (2 : Real) ≤ x
    linarith [hx.1]
  have hclosed : IsClosed bad :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hcompact : IsCompact bad := isCompact_Icc.of_isClosed_subset hclosed Set.inter_subset_left
  have hnonempty : bad.Nonempty := ⟨s, ⟨⟨hsHigh.le, le_rfl⟩, hsNonpos⟩⟩
  obtain ⟨a, ha⟩ := hcompact.exists_isLeast hnonempty
  have haThree : 3 ≤ a := ha.1.1.1
  have haUpper : a ≤ s := ha.1.1.2
  have haNonpos : iwaniecAuxM a ≤ 0 := ha.1.2
  have hbefore : ∀ x : Real, 2 ≤ x → x < a → 0 < iwaniecAuxM x := by
    intro x hxTwo hxa
    by_cases hxThree : x ≤ 3
    · exact iwaniecAuxM_initial_pos ⟨hxTwo, hxThree⟩
    · by_contra hxNot
      have hxNonpos : iwaniecAuxM x ≤ 0 := le_of_not_gt hxNot
      have hxBad : x ∈ bad := ⟨⟨(lt_of_not_ge hxThree).le, hxa.le.trans haUpper⟩, hxNonpos⟩
      have hax : a ≤ x := ha.2 hxBad
      linarith
  have hint : IntervalIntegrable iwaniecAuxMWindowKernel volume (a - 1) a :=
    iwaniecIntervalIntegrable_of_continuousOn_one _ iwaniecAuxMWindowKernel_continuousOn
      (by linarith) (by linarith)
  have hIntegral : 0 < ∫ x in (a - 1)..a, iwaniecAuxMWindowKernel x := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hint _ (by linarith)
    intro x hx
    have hxTwo : 2 ≤ x := by linarith [hx.1]
    exact mul_pos (iwaniecAuxMWindowWeight_pos hxTwo) (hbefore x hxTwo hx.2)
  have hidentity := iwaniecAuxM_window_identity haThree
  change iwaniecAuxMCoefficient a * iwaniecAuxM a =
    ∫ x in (a - 1)..a, iwaniecAuxMWindowKernel x at hidentity
  have hleft : iwaniecAuxMCoefficient a * iwaniecAuxM a ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (iwaniecAuxMCoefficient_pos haThree).le haNonpos
  linarith

theorem iwaniecAuxM_hasDerivAt_negative {s : Real} (hs : 3 < s) :
    deriv iwaniecAuxM s < 0 := by
  rw [(iwaniecAuxM_hasDerivAt hs).deriv]
  have hlag := iwaniecAuxM_pos (s := s - 1) (by linarith)
  have hfactor : -s / (s - 1) ^ 2 < 0 := div_neg_of_neg_of_pos
    (by linarith) (sq_pos_of_pos (by linarith))
  exact mul_neg_of_neg_of_pos hfactor hlag

end

end Erdos1212Kernel
