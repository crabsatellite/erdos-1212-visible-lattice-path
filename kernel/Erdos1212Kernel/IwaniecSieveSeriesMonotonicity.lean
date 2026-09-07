import Erdos1212Kernel.IwaniecSieveSeriesDifferential

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1600000

theorem iwaniecOddSieveSeries_antitoneOn_Ici_three :
    AntitoneOn iwaniecOddSieveSeries (Set.Ici (3 : Real)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (3 : Real))
    (iwaniecOddSieveSeries_continuousOn.mono
      (Set.Ici_subset_Ici.mpr (by norm_num)))
  · intro s hs
    rw [interior_Ici] at hs
    exact (iwaniecOddSieveSeries_hasDerivAt hs).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    change (3 : Real) < s at hs
    rw [iwaniecOddSieveSeries_deriv_eq hs]
    have hden : 0 ≤ s - 1 := by linarith
    have heven : 0 ≤ iwaniecEvenSieveSeries (s - 1) :=
      iwaniecEvenSieveSeries_nonneg (by linarith)
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr heven) hden

theorem iwaniecOddSieveSeries_antitoneOn :
    AntitoneOn iwaniecOddSieveSeries (Set.Ici (1 : Real)) := by
  intro x hx y hy hxy
  change (1 : Real) ≤ x at hx
  change (1 : Real) ≤ y at hy
  by_cases hyThree : y ≤ 3
  · rw [iwaniecOddSieveSeries_eq_three hx (hxy.trans hyThree),
      iwaniecOddSieveSeries_eq_three hy hyThree]
  · have hyHigh : 3 ≤ y := le_of_not_ge hyThree
    by_cases hxThree : x ≤ 3
    · rw [iwaniecOddSieveSeries_eq_three hx hxThree]
      exact iwaniecOddSieveSeries_antitoneOn_Ici_three
        (show (3 : Real) ∈ Set.Ici 3 by simp)
        (show y ∈ Set.Ici 3 by exact hyHigh) hyHigh
    · have hxHigh : 3 ≤ x := le_of_not_ge hxThree
      exact iwaniecOddSieveSeries_antitoneOn_Ici_three hxHigh hyHigh hxy

theorem iwaniecEvenSieveSeries_deriv_nonpos
    {s : Real} (hs : 2 < s) :
    deriv iwaniecEvenSieveSeries s ≤ 0 := by
  rcases lt_trichotomy s 4 with hlt | heq | hgt
  · rw [iwaniecEvenSieveSeries_deriv_eq_of_lt_four hs hlt]
    have hdenPos : 0 < s - 1 := by linarith
    have hodd : 0 ≤ iwaniecOddSieveSeries (s - 1) :=
      iwaniecOddSieveSeries_nonneg (by linarith)
    have hfirst : -iwaniecOddSieveSeries (s - 1) / (s - 1) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hodd) hdenPos.le
    have hratio : 1 ≤ (3 : Real) / (s - 1) := by
      rw [le_div_iff₀ hdenPos]
      linarith
    linarith
  · subst s
    rw [(iwaniecEvenSieveSeries_hasDerivAt_four).deriv]
    unfold iwaniecOddSeriesKernel
    have hodd : 0 ≤ iwaniecOddSieveSeries ((4 : Real) - 1) :=
      iwaniecOddSieveSeries_nonneg (by norm_num)
    exact neg_nonpos.mpr (div_nonneg hodd (by norm_num))
  · rw [iwaniecEvenSieveSeries_deriv_eq_of_four_lt hgt]
    have hdenPos : 0 < s - 1 := by linarith
    have hodd : 0 ≤ iwaniecOddSieveSeries (s - 1) :=
      iwaniecOddSieveSeries_nonneg (by linarith)
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hodd) hdenPos.le

theorem iwaniecEvenSieveSeries_antitoneOn :
    AntitoneOn iwaniecEvenSieveSeries (Set.Ici (2 : Real)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici (2 : Real))
    iwaniecEvenSieveSeries_continuousOn
  · intro s hs
    rw [interior_Ici] at hs
    rcases lt_trichotomy s 4 with hlt | heq | hgt
    · exact (iwaniecEvenSieveSeries_hasDerivAt_of_lt_four hs hlt).differentiableAt.differentiableWithinAt
    · subst s
      exact iwaniecEvenSieveSeries_hasDerivAt_four.differentiableAt.differentiableWithinAt
    · exact (iwaniecEvenSieveSeries_hasDerivAt_of_four_lt hgt).differentiableAt.differentiableWithinAt
  · intro s hs
    rw [interior_Ici] at hs
    exact iwaniecEvenSieveSeries_deriv_nonpos hs

def iwaniecParitySieveProfile (r : Nat) (s : Real) : Real :=
  if Even r then iwaniecEvenSieveSeries s else iwaniecOddSieveSeries s

theorem iwaniecParitySieveProfile_nonneg
    (r : Nat) {s : Real} (hs : 2 ≤ s) :
    0 ≤ iwaniecParitySieveProfile r s := by
  unfold iwaniecParitySieveProfile
  split
  · exact iwaniecEvenSieveSeries_nonneg hs
  · exact iwaniecOddSieveSeries_nonneg (by linarith)

theorem iwaniecParitySieveProfile_continuousOn
    (r : Nat) :
    ContinuousOn (iwaniecParitySieveProfile r) (Set.Ici (2 : Real)) := by
  unfold iwaniecParitySieveProfile
  split
  · exact iwaniecEvenSieveSeries_continuousOn
  · exact iwaniecOddSieveSeries_continuousOn.mono
      (Set.Ici_subset_Ici.mpr (by norm_num))

theorem iwaniecParitySieveProfile_antitoneOn
    (r : Nat) :
    AntitoneOn (iwaniecParitySieveProfile r) (Set.Ici (2 : Real)) := by
  unfold iwaniecParitySieveProfile
  split
  · exact iwaniecEvenSieveSeries_antitoneOn
  · exact iwaniecOddSieveSeries_antitoneOn.mono
      (Set.Ici_subset_Ici.mpr (by norm_num))

/-- Exact lower endpoint for the parity-dependent profile: 2 for `f`, 1 for
`F`.  In Corollary 1 the corresponding `alpha` endpoint is one larger. -/
def iwaniecParityProfileStart (r : Nat) : Real :=
  if Even r then 2 else 1

theorem one_le_iwaniecParityProfileStart (r : Nat) :
    1 ≤ iwaniecParityProfileStart r := by
  unfold iwaniecParityProfileStart
  split <;> norm_num

theorem iwaniecParitySieveProfile_nonneg_exactDomain
    (r : Nat) {s : Real} (hs : iwaniecParityProfileStart r ≤ s) :
    0 ≤ iwaniecParitySieveProfile r s := by
  unfold iwaniecParityProfileStart at hs
  unfold iwaniecParitySieveProfile
  split_ifs at hs ⊢ with hr
  · exact iwaniecEvenSieveSeries_nonneg hs
  · exact iwaniecOddSieveSeries_nonneg hs

theorem iwaniecParitySieveProfile_continuousOn_exactDomain (r : Nat) :
    ContinuousOn (iwaniecParitySieveProfile r)
      (Set.Ici (iwaniecParityProfileStart r)) := by
  unfold iwaniecParitySieveProfile iwaniecParityProfileStart
  split_ifs with hr
  · exact iwaniecEvenSieveSeries_continuousOn
  · exact iwaniecOddSieveSeries_continuousOn

theorem iwaniecParitySieveProfile_antitoneOn_exactDomain (r : Nat) :
    AntitoneOn (iwaniecParitySieveProfile r)
      (Set.Ici (iwaniecParityProfileStart r)) := by
  unfold iwaniecParitySieveProfile iwaniecParityProfileStart
  split_ifs with hr
  · exact iwaniecEvenSieveSeries_antitoneOn
  · exact iwaniecOddSieveSeries_antitoneOn

end

end Erdos1212Kernel
