import Erdos1212Kernel.IwaniecDickmanConservation
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1400000

theorem iwaniecDickman_pos {s : Real} (hs : 0 ≤ s) : 0 < iwaniecDickman s := by
  by_contra hnot
  have hsBad : iwaniecDickman s ≤ 0 := le_of_not_gt hnot
  have hsHigh : 1 < s := by
    by_contra hnotHigh
    rw [iwaniecDickman_initial (le_of_not_gt hnotHigh)] at hsBad
    linarith
  let bad : Set Real := Set.Icc 1 s ∩ iwaniecDickman ⁻¹' Set.Iic 0
  have hc : ContinuousOn iwaniecDickman (Set.Icc (1 : Real) s) := iwaniecDickman_continuous.continuousOn
  have hclosed : IsClosed bad := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hcompact : IsCompact bad := isCompact_Icc.of_isClosed_subset hclosed Set.inter_subset_left
  obtain ⟨a, ha⟩ := hcompact.exists_isLeast (show bad.Nonempty from ⟨s, ⟨⟨hsHigh.le, le_rfl⟩, hsBad⟩⟩)
  have haOne : 1 ≤ a := ha.1.1.1
  have haUpper : a ≤ s := ha.1.1.2
  have haBad : iwaniecDickman a ≤ 0 := ha.1.2
  have hbefore : ∀ x : Real, 0 ≤ x → x < a → 0 < iwaniecDickman x := by
    intro x hx hxa
    by_cases hxOne : x ≤ 1
    · rw [iwaniecDickman_initial hxOne]
      norm_num
    · by_contra hnotx
      have hxBad : x ∈ bad := ⟨⟨(lt_of_not_ge hxOne).le, hxa.le.trans haUpper⟩, le_of_not_gt hnotx⟩
      have hax := ha.2 hxBad
      linarith
  have hi : 0 < ∫ x in (a - 1)..a, iwaniecDickman x := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (iwaniecDickman_continuous.intervalIntegrable (a - 1) a)
      (fun x hx => hbefore x (by linarith [hx.1]) hx.2) (by linarith)
  have hw := iwaniecDickman_window_identity haOne
  have hleft : a * iwaniecDickman a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) haBad
  linarith

theorem iwaniecDickman_strictAntiOn_high : StrictAntiOn iwaniecDickman (Set.Ici (1 : Real)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici (1 : Real)) iwaniecDickman_continuous.continuousOn
  intro s hs
  rw [interior_Ici] at hs
  rw [(iwaniecDickman_hasDerivAt hs).deriv]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (iwaniecDickman_pos (by linarith [hs.out]))) (by linarith [hs.out])

theorem iwaniecDickman_antitoneOn : AntitoneOn iwaniecDickman (Set.Ici (0 : Real)) := by
  intro x hx y hy hxy
  by_cases hyOne : y ≤ 1
  · rw [iwaniecDickman_initial (hxy.trans hyOne), iwaniecDickman_initial hyOne]
  · have hyHigh : 1 ≤ y := (lt_of_not_ge hyOne).le
    by_cases hxOne : x ≤ 1
    · have h := iwaniecDickman_strictAntiOn_high.antitoneOn (show (1 : Real) ∈ Set.Ici 1 by simp) hyHigh hyHigh
      rw [iwaniecDickman_initial (by norm_num : (1 : Real) ≤ 1)] at h
      rw [iwaniecDickman_initial hxOne]
      exact h
    · exact iwaniecDickman_strictAntiOn_high.antitoneOn (lt_of_not_ge hxOne).le hyHigh hxy

theorem iwaniecDickman_le_one {s : Real} (hs : 0 ≤ s) : iwaniecDickman s ≤ 1 := by
  have h := iwaniecDickman_antitoneOn (show (0 : Real) ∈ Set.Ici 0 by simp) hs hs
  rw [iwaniecDickman_initial (by norm_num : (0 : Real) ≤ 1)] at h
  exact h

end

end Erdos1212Kernel
