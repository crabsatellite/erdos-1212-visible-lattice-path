import Erdos1212Kernel.IwaniecSieveSeriesMonotonicity
import Erdos1212Kernel.IwaniecReciprocalLogConstantWeight

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

/-- The paper's upper cutoff, including its endpoint. -/
def iwaniecReciprocalLogProfileDomain (L start : Real) : Set Real :=
  Set.Ioc 1 (Real.exp (L / (start + 1)))

theorem iwaniecReciprocalLogProfileDomain_bounds
    {L start x : Real} (hL : 0 < L) (hstart : 0 < start)
    (hx : x ∈ iwaniecReciprocalLogProfileDomain L start) :
    0 < Real.log x ∧ Real.log x < L ∧ start ≤ L / Real.log x - 1 := by
  have hxOne : 1 < x := hx.1
  have hlogPos : 0 < Real.log x := Real.log_pos hxOne
  have hstartOne : 0 < start + 1 := by linarith
  have hlogUpper : Real.log x ≤ L / (start + 1) := by
    exact (Real.log_le_iff_le_exp (zero_lt_one.trans hxOne)).2 hx.2
  have hdivL : L / (start + 1) < L := by
    rw [div_lt_iff₀ hstartOne]
    nlinarith
  refine ⟨hlogPos, hlogUpper.trans_lt hdivL, ?_⟩
  have hprod : (start + 1) * Real.log x ≤ L := by
    have h := (le_div_iff₀ hstartOne).1 hlogUpper
    nlinarith
  have hratio : start + 1 ≤ L / Real.log x :=
    (le_div_iff₀ hlogPos).2 hprod
  linarith

theorem iwaniecReciprocalLogProfileDomain_subset
    {L start : Real} (hL : 0 < L) (hstart : 0 < start) :
    iwaniecReciprocalLogProfileDomain L start ⊆ Set.Ioo 1 (Real.exp L) := by
  intro x hx
  have hbounds := iwaniecReciprocalLogProfileDomain_bounds hL hstart hx
  exact ⟨hx.1, (Real.log_lt_iff_lt_exp (zero_lt_one.trans hx.1)).1 hbounds.2.1⟩

theorem iwaniecReciprocalLogWeight_eq_profile_mul
    (L : Real) (profile : Real → Real) (x : Real) :
    iwaniecReciprocalLogWeight L profile x =
      profile (L / Real.log x - 1) * iwaniecReciprocalLogConstantWeight L x := by
  rw [iwaniecReciprocalLogConstantWeight_eq]
  rfl

theorem iwaniecReciprocalLogWeight_nonneg
    (profile : Real → Real) {L start x : Real}
    (hL : 0 < L) (hstart : 0 < start)
    (hprofile : ∀ s ∈ Set.Ici start, 0 ≤ profile s)
    (hx : x ∈ iwaniecReciprocalLogProfileDomain L start) :
    0 ≤ iwaniecReciprocalLogWeight L profile x := by
  rw [iwaniecReciprocalLogWeight_eq_profile_mul]
  have hbounds := iwaniecReciprocalLogProfileDomain_bounds hL hstart hx
  exact mul_nonneg (hprofile _ hbounds.2.2)
    (iwaniecReciprocalLogConstantWeight_pos
      (iwaniecReciprocalLogProfileDomain_subset hL hstart hx)).le

theorem iwaniecReciprocalLogWeight_continuousOn
    (profile : Real → Real) {L start : Real}
    (hL : 0 < L) (hstart : 0 < start)
    (hprofile : ContinuousOn profile (Set.Ici start)) :
    ContinuousOn (iwaniecReciprocalLogWeight L profile)
      (iwaniecReciprocalLogProfileDomain L start) := by
  have harg : ContinuousOn (fun x : Real => L / Real.log x - 1)
      (iwaniecReciprocalLogProfileDomain L start) := by
    refine (continuousOn_const.div ?_ ?_).sub continuousOn_const
    · exact Real.continuousOn_log.mono (fun x hx => by
        exact ne_of_gt (zero_lt_one.trans hx.1))
    · intro x hx
      exact (iwaniecReciprocalLogProfileDomain_bounds hL hstart hx).1.ne'
  have hcomp := hprofile.comp harg (fun x hx =>
    (iwaniecReciprocalLogProfileDomain_bounds hL hstart hx).2.2)
  have hweight := (iwaniecReciprocalLogConstantWeight_continuousOn L).mono
    (iwaniecReciprocalLogProfileDomain_subset hL hstart)
  have hmul := hcomp.mul hweight
  apply hmul.congr
  intro x hx
  exact iwaniecReciprocalLogWeight_eq_profile_mul L profile x

theorem iwaniecReciprocalLogWeight_monotoneOn
    (profile : Real → Real) {L start : Real}
    (hL : 0 < L) (hstart : 0 < start)
    (hprofileNonneg : ∀ s ∈ Set.Ici start, 0 ≤ profile s)
    (hprofileAnti : AntitoneOn profile (Set.Ici start)) :
    MonotoneOn (iwaniecReciprocalLogWeight L profile)
      (iwaniecReciprocalLogProfileDomain L start) := by
  intro x hx y hy hxy
  have hxBounds := iwaniecReciprocalLogProfileDomain_bounds hL hstart hx
  have hyBounds := iwaniecReciprocalLogProfileDomain_bounds hL hstart hy
  have harg : L / Real.log y - 1 ≤ L / Real.log x - 1 := by
    apply sub_le_sub_right
    rw [div_le_div_iff₀ hyBounds.1 hxBounds.1]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (zero_lt_one.trans hx.1) hxy) hL.le
  have hprofileLe := hprofileAnti hyBounds.2.2 hxBounds.2.2 harg
  have hweightLe := iwaniecReciprocalLogConstantWeight_monotoneOn L
    (iwaniecReciprocalLogProfileDomain_subset hL hstart hx)
    (iwaniecReciprocalLogProfileDomain_subset hL hstart hy) hxy
  rw [iwaniecReciprocalLogWeight_eq_profile_mul,
    iwaniecReciprocalLogWeight_eq_profile_mul]
  exact mul_le_mul hprofileLe hweightLe
    (iwaniecReciprocalLogConstantWeight_pos
      (iwaniecReciprocalLogProfileDomain_subset hL hstart hx)).le
    (hprofileNonneg _ hyBounds.2.2)

end

end Erdos1212Kernel
