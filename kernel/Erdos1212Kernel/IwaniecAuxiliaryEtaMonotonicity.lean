import Erdos1212Kernel.IwaniecAuxiliaryEtaDifferential
import Erdos1212Kernel.IwaniecAuxiliaryEtaWindow

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

def iwaniecAuxHazardGap (s : Real) : Real := iwaniecAuxHazard s - iwaniecAuxHazard (s - 1)

theorem iwaniecAuxHazardGap_continuousOn :
    ContinuousOn iwaniecAuxHazardGap (Set.Ici (4 : Real)) := by
  have hshift : ContinuousOn (fun s : Real => iwaniecAuxHazard (s - 1)) (Set.Ici (4 : Real)) := by
    apply iwaniecAuxHazard_continuousOn.comp (continuousOn_id.sub continuousOn_const)
    intro s hs
    change (3 : Real) ≤ s - 1
    linarith [hs.out]
  exact (iwaniecAuxHazard_continuousOn.mono (Set.Ici_subset_Ici.mpr (by norm_num))).sub hshift

theorem iwaniecAuxHazardGap_four_pos : 0 < iwaniecAuxHazardGap 4 := by
  apply sub_pos.mpr
  apply iwaniecAuxHazard_lag_lt_of_eta_window (by norm_num : (4 : Real) ≤ 4)
  intro x hx
  have hxIcc : x ∈ Set.Icc (3 : Real) 4 := by norm_num at hx; exact hx
  norm_num only [show (4 : Real) - 1 = 3 by norm_num]
  exact iwaniecAuxEta_strictMonoOn_initial.monotoneOn (by norm_num) hxIcc hxIcc.1

/-- First contact of the continuous hazard increment, with the derivative
join at 4 kept out of both open derivative intervals. The exact two-window
producer rules out the first nonpositive increment. -/
theorem iwaniecAuxHazardGap_pos {s : Real} (hs : 4 ≤ s) : 0 < iwaniecAuxHazardGap s := by
  by_contra hnot
  have hsBad : iwaniecAuxHazardGap s ≤ 0 := le_of_not_gt hnot
  let bad : Set Real := Set.Icc 4 s ∩ iwaniecAuxHazardGap ⁻¹' Set.Iic 0
  have hc := iwaniecAuxHazardGap_continuousOn.mono (show Set.Icc (4 : Real) s ⊆ Set.Ici 4 from
    fun _ hx => hx.1)
  have hclosed : IsClosed bad := hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hcompact : IsCompact bad := isCompact_Icc.of_isClosed_subset hclosed Set.inter_subset_left
  have hnonempty : bad.Nonempty := ⟨s, ⟨⟨hs, le_rfl⟩, hsBad⟩⟩
  obtain ⟨a, ha⟩ := hcompact.exists_isLeast hnonempty
  have haFour : 4 ≤ a := ha.1.1.1
  have haUpper : a ≤ s := ha.1.1.2
  have haBad : iwaniecAuxHazardGap a ≤ 0 := ha.1.2
  have hbefore : ∀ x : Real, 4 ≤ x → x < a → 0 < iwaniecAuxHazardGap x := by
    intro x hx hxa
    by_contra hnotx
    have hxBad : x ∈ bad := ⟨⟨hx, hxa.le.trans haUpper⟩, le_of_not_gt hnotx⟩
    have hax := ha.2 hxBad
    linarith
  have hhigh : StrictMonoOn iwaniecAuxEta (Set.Icc (4 : Real) a) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc (4 : Real) a)
      (iwaniecAuxEta_continuousOn.mono (by
        intro x hx
        change (3 : Real) ≤ x
        linarith [hx.1]))
    intro x hx
    rw [interior_Icc] at hx
    rw [(iwaniecAuxEta_hasDerivAt_high hx.1).deriv]
    exact mul_pos (iwaniecAuxEta_pos (by linarith [hx.1])) (hbefore x hx.1.le hx.2)
  have hmono : MonotoneOn iwaniecAuxEta (Set.Icc (3 : Real) a) := by
    intro x hx y hy hxy
    by_cases hyFour : y ≤ 4
    · exact iwaniecAuxEta_strictMonoOn_initial.monotoneOn
        ⟨hx.1, hxy.trans hyFour⟩ ⟨hy.1, hyFour⟩ hxy
    · have hyHigh : 4 ≤ y := (lt_of_not_ge hyFour).le
      by_cases hxFour : x ≤ 4
      · exact (iwaniecAuxEta_strictMonoOn_initial.monotoneOn ⟨hx.1, hxFour⟩ (by norm_num) hxFour).trans
          (hhigh.monotoneOn ⟨le_rfl, haFour⟩ ⟨hyHigh, hy.2⟩ hyHigh)
      · exact hhigh.monotoneOn ⟨(lt_of_not_ge hxFour).le, hx.2⟩ ⟨hyHigh, hy.2⟩ hxy
  have hinc := iwaniecAuxHazard_lag_lt_of_eta_window haFour (fun x hx =>
    hmono ⟨by linarith, by linarith⟩ ⟨by linarith [hx.1], hx.2⟩ hx.1)
  have hpos : 0 < iwaniecAuxHazardGap a := sub_pos.mpr hinc
  linarith

theorem iwaniecAuxEta_strictMonoOn_high : StrictMonoOn iwaniecAuxEta (Set.Ici (4 : Real)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici (4 : Real))
    (iwaniecAuxEta_continuousOn.mono (Set.Ici_subset_Ici.mpr (by norm_num)))
  intro s hs
  rw [interior_Ici] at hs
  rw [(iwaniecAuxEta_hasDerivAt_high hs).deriv]
  exact mul_pos (iwaniecAuxEta_pos (by linarith [hs.out])) (iwaniecAuxHazardGap_pos hs.le)

theorem iwaniecAuxEta_monotoneOn : MonotoneOn iwaniecAuxEta (Set.Ici (3 : Real)) := by
  intro x hx y hy hxy
  by_cases hyFour : y ≤ 4
  · exact iwaniecAuxEta_strictMonoOn_initial.monotoneOn
      ⟨hx, hxy.trans hyFour⟩ ⟨hy, hyFour⟩ hxy
  · have hyHigh : 4 ≤ y := (lt_of_not_ge hyFour).le
    by_cases hxFour : x ≤ 4
    · exact (iwaniecAuxEta_strictMonoOn_initial.monotoneOn ⟨hx, hxFour⟩ (by norm_num) hxFour).trans
        (iwaniecAuxEta_strictMonoOn_high.monotoneOn (by norm_num) hyHigh hyHigh)
    · exact iwaniecAuxEta_strictMonoOn_high.monotoneOn (lt_of_not_ge hxFour).le hyHigh hxy

end

end Erdos1212Kernel
