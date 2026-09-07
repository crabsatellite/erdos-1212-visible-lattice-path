import Erdos1212Kernel.IwaniecSieveSeriesDifferential

namespace Erdos1212Kernel

noncomputable section

open Filter

set_option maxHeartbeats 1800000

def iwaniecSieveNormalizationC : Real :=
  iwaniecOddSieveSeries 3 + 3

/-- Iwaniec's continuation of `M=f+F` from page 9 back to `[2,3]`. -/
def iwaniecMExtended (s : Real) : Real :=
  if s ≤ 3 then
    iwaniecSieveNormalizationC - s + iwaniecEvenSieveSeries s
  else
    iwaniecEvenSieveSeries s + iwaniecOddSieveSeries s

theorem iwaniecSieveNormalizationC_pos :
    0 < iwaniecSieveNormalizationC := by
  unfold iwaniecSieveNormalizationC
  have hnonneg := iwaniecOddSieveSeries_nonneg (by norm_num : (1 : Real) ≤ 3)
  linarith

theorem iwaniecMExtended_of_le_three
    {s : Real} (hs : s ≤ 3) :
    iwaniecMExtended s =
      iwaniecSieveNormalizationC - s + iwaniecEvenSieveSeries s := by
  simp [iwaniecMExtended, hs]

theorem iwaniecMExtended_of_three_lt
    {s : Real} (hs : 3 < s) :
    iwaniecMExtended s =
      iwaniecEvenSieveSeries s + iwaniecOddSieveSeries s := by
  simp [iwaniecMExtended, not_le.mpr hs]

theorem iwaniecMExtended_of_three_le
    {s : Real} (hs : 3 ≤ s) :
    iwaniecMExtended s =
      iwaniecEvenSieveSeries s + iwaniecOddSieveSeries s := by
  rcases hs.eq_or_lt with heq | hlt
  · subst s
    rw [iwaniecMExtended_of_le_three (le_refl (3 : Real))]
    unfold iwaniecSieveNormalizationC
    ring
  · exact iwaniecMExtended_of_three_lt hlt

theorem iwaniecMExtended_continuousOn :
    ContinuousOn iwaniecMExtended (Set.Ici (2 : Real)) := by
  let left := fun s : Real =>
    iwaniecSieveNormalizationC - s + iwaniecEvenSieveSeries s
  let right := fun s : Real =>
    iwaniecEvenSieveSeries s + iwaniecOddSieveSeries s
  have hpiece : ContinuousOn (fun s : Real => if s ≤ 3 then left s else right s)
      (Set.Ici (2 : Real)) := by
    apply ContinuousOn.if (p := fun s : Real => s ≤ 3)
    · intro s hs
      have hset : {t : Real | t ≤ 3} = Set.Iic 3 := by ext; simp
      have hsFront : s ∈ frontier (Set.Iic (3 : Real)) := by
        simpa [hset] using hs.2
      have hsEq : s = 3 := by simpa using frontier_Iic_subset (3 : Real) hsFront
      subst s
      dsimp [left, right, iwaniecSieveNormalizationC]
      ring
    · have hleft : ContinuousOn left (Set.Ici (2 : Real)) := by
        dsimp [left]
        exact (continuousOn_const.sub continuousOn_id).add
          iwaniecEvenSieveSeries_continuousOn
      exact hleft.mono Set.inter_subset_left
    · have hright : ContinuousOn right (Set.Ici (3 : Real)) := by
        dsimp [right]
        exact (iwaniecEvenSieveSeries_continuousOn.mono
          (Set.Ici_subset_Ici.mpr (by norm_num))).add
          (iwaniecOddSieveSeries_continuousOn.mono
            (Set.Ici_subset_Ici.mpr (by norm_num)))
      apply hright.mono
      intro s hs
      have hsClosure := hs.2
      have hset : {t : Real | ¬t ≤ 3} = Set.Ioi 3 := by ext; simp
      rw [hset, closure_Ioi] at hsClosure
      exact hsClosure
  apply hpiece.congr
  intro s hs
  by_cases hthree : s ≤ 3
  · simp [iwaniecMExtended, hthree, left]
  · simp [iwaniecMExtended, hthree, right]

theorem iwaniecMExtended_hasDerivAt_of_three_lt_of_lt_four
    {s : Real} (hlower : 3 < s) (hupper : s < 4) :
    HasDerivAt iwaniecMExtended
      (-iwaniecMExtended (s - 1) / (s - 1)) s := by
  have hf := iwaniecEvenSieveSeries_hasDerivAt_of_lt_four
    (by linarith : 2 < s) hupper
  have hF := iwaniecOddSieveSeries_hasDerivAt hlower
  have hsum := hf.add hF
  have heq : iwaniecMExtended =ᶠ[nhds s]
      (fun x : Real => iwaniecEvenSieveSeries x + iwaniecOddSieveSeries x) := by
    filter_upwards [Ioi_mem_nhds hlower] with x hx
    exact iwaniecMExtended_of_three_lt hx
  have hraw := hsum.congr_of_eventuallyEq heq
  refine hraw.congr_deriv ?_
  rw [iwaniecMExtended_of_le_three (by linarith : s - 1 ≤ 3)]
  unfold iwaniecOddSeriesKernel iwaniecEvenSeriesKernel
  rw [iwaniecOddSieveSeries_eq_three (by linarith : 1 ≤ s - 1)
      (by linarith : s - 1 ≤ 3)]
  unfold iwaniecSieveNormalizationC
  field_simp [show s - 1 ≠ 0 by linarith]
  ring

theorem iwaniecMExtended_hasDerivAt_of_four_lt
    {s : Real} (hs : 4 < s) :
    HasDerivAt iwaniecMExtended
      (-iwaniecMExtended (s - 1) / (s - 1)) s := by
  have hf := iwaniecEvenSieveSeries_hasDerivAt_of_four_lt hs
  have hF := iwaniecOddSieveSeries_hasDerivAt (by linarith : 3 < s)
  have hsum := hf.add hF
  have heq : iwaniecMExtended =ᶠ[nhds s]
      (fun x : Real => iwaniecEvenSieveSeries x + iwaniecOddSieveSeries x) := by
    filter_upwards [Ioi_mem_nhds (by linarith : 3 < s)] with x hx
    exact iwaniecMExtended_of_three_lt hx
  have hraw := hsum.congr_of_eventuallyEq heq
  refine hraw.congr_deriv ?_
  rw [iwaniecMExtended_of_three_lt (by linarith : 3 < s - 1)]
  unfold iwaniecOddSeriesKernel iwaniecEvenSeriesKernel
  field_simp [show s - 1 ≠ 0 by linarith]
  ring

theorem iwaniecMExtended_hasDerivAt_four :
    HasDerivAt iwaniecMExtended
      (-iwaniecMExtended (4 - 1) / (4 - 1)) 4 := by
  have hf := iwaniecEvenSieveSeries_hasDerivAt_four
  have hF := iwaniecOddSieveSeries_hasDerivAt (by norm_num : (3 : Real) < 4)
  have hsum := hf.add hF
  have heq : iwaniecMExtended =ᶠ[nhds (4 : Real)]
      (fun x : Real => iwaniecEvenSieveSeries x + iwaniecOddSieveSeries x) := by
    filter_upwards [Ioi_mem_nhds (show (3 : Real) < 4 by norm_num)] with x hx
    exact iwaniecMExtended_of_three_lt hx
  have hraw := hsum.congr_of_eventuallyEq heq
  refine hraw.congr_deriv ?_
  rw [iwaniecMExtended_of_le_three (by norm_num : (4 : Real) - 1 ≤ 3)]
  unfold iwaniecOddSeriesKernel iwaniecEvenSeriesKernel
  unfold iwaniecSieveNormalizationC
  norm_num
  ring

theorem iwaniecMExtended_hasDerivAt
    {s : Real} (hs : 3 < s) :
    HasDerivAt iwaniecMExtended
      (-iwaniecMExtended (s - 1) / (s - 1)) s := by
  rcases lt_trichotomy s 4 with hlt | heq | hgt
  · exact iwaniecMExtended_hasDerivAt_of_three_lt_of_lt_four hs hlt
  · subst s
    exact iwaniecMExtended_hasDerivAt_four
  · exact iwaniecMExtended_hasDerivAt_of_four_lt hgt

end

end Erdos1212Kernel
