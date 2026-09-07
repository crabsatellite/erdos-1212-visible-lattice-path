import Erdos1212Kernel.IwaniecPaperStoppedBase

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

/-- The paper's stopped d-rank mass. Odd ranks use exactly the stated
constant extension below s=3; ranks 0 and 1 are zero padding on y>1. -/
def iwaniecPaperD (rank : Nat) (level s : Real) : Real :=
  iwaniecPaperStoppedLayer (if Even rank then 0 else 1) level
    (Real.exp (Real.log level / (if Even rank then s else max 3 s))) rank

/-- The finite sum of d-masses with the same parity as the terminal
rank. The zero ranks 0 and 1 are verified below, not charged as units. -/
def iwaniecPaperQ (rank : Nat) (level s : Real) : Real :=
  ∑ k ∈ Finset.range (rank + 1), if (Even k ↔ Even rank) then iwaniecPaperD k level s else 0

@[simp] theorem iwaniecPaperD_zero (level s : Real) : iwaniecPaperD 0 level s = 0 := by
  unfold iwaniecPaperD
  exact iwaniecPaperStoppedLayer_zero _ _ _

theorem iwaniecPaperD_nonneg (rank : Nat) (level s : Real) : 0 ≤ iwaniecPaperD rank level s :=
  iwaniecPaperStoppedLayer_nonneg _ _ _ _

theorem iwaniecPaperD_one {level : Real} (hy : 1 < level) (s : Real) :
    iwaniecPaperD 1 level s = 0 := by
  classical
  have hodd : ¬Even (1 : Nat) := by decide
  simp only [iwaniecPaperD, if_neg hodd]
  rw [iwaniecPaperStoppedLayer_one_odd]
  apply Finset.sum_eq_zero
  intro p hp
  have hcutoff : Real.exp (Real.log level / max 3 s) ≤ Real.exp (Real.log level / 3) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (Real.log_pos hy).le (by norm_num) (le_max_left 3 s))
  have hplt := (mem_iwaniecStrictPrimePool.mp hp).2.trans_le hcutoff
  have hcube := pow_lt_pow_left₀ hplt (Nat.cast_nonneg p : (0 : Real) ≤ p) (by norm_num : (3 : Nat) ≠ 0)
  rw [iwaniec_exp_log_third_cube (zero_lt_one.trans hy)] at hcube
  rw [if_neg (not_le.mpr hcube)]

theorem iwaniecPaperD_two_eq_d2 (level s : Real) : iwaniecPaperD 2 level s = iwaniecPaperD2 level s := by
  have he : Even (2 : Nat) := ⟨1, rfl⟩
  simp only [iwaniecPaperD, if_pos he, iwaniecPaperStoppedLayer_two_eq_d2, iwaniecPaperD2]

theorem iwaniecPaperD_odd_initial {rank : Nat} (hr : ¬Even rank) (level : Real) {s : Real}
    (hs1 : 1 ≤ s) (hs3 : s ≤ 3) : iwaniecPaperD rank level s = iwaniecPaperD rank level 3 := by
  simp only [iwaniecPaperD, if_neg hr, max_eq_left hs3, max_self]

theorem iwaniecPaperQ_nonneg (rank : Nat) (level s : Real) : 0 ≤ iwaniecPaperQ rank level s := by
  unfold iwaniecPaperQ
  apply Finset.sum_nonneg
  intro k hk
  split
  · exact iwaniecPaperD_nonneg k level s
  · exact le_rfl

@[simp] theorem iwaniecPaperQ_zero (level s : Real) : iwaniecPaperQ 0 level s = 0 := by
  simp [iwaniecPaperQ]

theorem iwaniecPaperQ_one {level : Real} (hy : 1 < level) (s : Real) : iwaniecPaperQ 1 level s = 0 := by
  norm_num [iwaniecPaperQ, Finset.sum_range_succ, iwaniecPaperD_one hy s]

theorem iwaniecPaperQ_two_eq_d2 (level s : Real) : iwaniecPaperQ 2 level s = iwaniecPaperD2 level s := by
  norm_num [iwaniecPaperQ, Finset.sum_range_succ, iwaniecPaperD_two_eq_d2]

/-- The even Q sum is precisely the cumulative stopped mass on the
original complete prime pool; off-parity layers vanish by a proved result. -/
theorem iwaniecPaperQ_even_eq_partial {rank : Nat} (hr : Even rank) (level s : Real) :
    iwaniecPaperQ rank level s =
      iwaniecPaperStoppedPartial 0 level (Real.exp (Real.log level / s)) rank := by
  classical
  rw [iwaniecPaperQ, iwaniecPaperStoppedPartial_eq_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases he : Even k
  · have hiff : Even k ↔ Even rank := ⟨fun _ => hr, fun _ => he⟩
    simp only [if_pos hiff, iwaniecPaperD, if_pos he]
  · have hn : ¬(Even k ↔ Even rank) := fun hh => he (hh.mpr hr)
    rw [if_neg hn]
    exact (iwaniecPaperStoppedLayer_parity 0 level (Real.exp (Real.log level / s)) k (by simpa using he)).symm

/-- Odd Q uses the original constant extension. The potential first
failure at rank one has already been proved zero on y>1. -/
theorem iwaniecPaperQ_odd_eq_partial {rank : Nat} (hr : ¬Even rank) (level s : Real) :
    iwaniecPaperQ rank level s =
      iwaniecPaperStoppedPartial 1 level (Real.exp (Real.log level / max 3 s)) rank := by
  classical
  rw [iwaniecPaperQ, iwaniecPaperStoppedPartial_eq_sum]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases he : Even k
  · have hn : ¬(Even k ↔ Even rank) := fun hh => hr (hh.mp he)
    rw [if_neg hn]
    have hp : ¬Even (1 + k) := by
      intro hh
      obtain ⟨a, ha⟩ := he
      obtain ⟨b, hb⟩ := hh
      omega
    exact (iwaniecPaperStoppedLayer_parity 1 level (Real.exp (Real.log level / max 3 s)) k hp).symm
  · have hiff : Even k ↔ Even rank := ⟨fun hh => (he hh).elim, fun hh => (hr hh).elim⟩
    simp only [if_pos hiff, iwaniecPaperD, if_neg he]

end

end Erdos1212Kernel
