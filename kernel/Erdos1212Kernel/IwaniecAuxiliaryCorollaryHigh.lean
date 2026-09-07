import Erdos1212Kernel.IwaniecAuxiliaryLemmaTen
import Erdos1212Kernel.IwaniecAuxiliaryMonotonicity

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1600000

/-- The literal quotient in the corollary to source Lemma 10. -/
def iwaniecAuxCorollaryRatio (rank : Nat) (s : Real) : Real :=
  iwaniecAuxG (rank + 1) s * (s - 1) ^ 2 * Real.log s /
    (iwaniecAuxG rank (s - 1) * s)

theorem iwaniecAuxG_le_two (rank : Nat) {s : Real} (hs : 2 ≤ s) : iwaniecAuxG rank s ≤ 2 := by
  have hb := (iwaniecAuxG_bounds rank hs).2
  have hM := iwaniecAuxM_le_three hs
  linarith

theorem iwaniecAuxCorollaryRatio_lt_eight (rank : Nat) {s : Real} (hs : 6 ≤ s) :
    iwaniecAuxCorollaryRatio rank s < 8 := by
  have hsPos : 0 < s := by linarith
  have hlog : 0 ≤ Real.log s := Real.log_nonneg (by linarith)
  have hM := iwaniecAuxM_pos (s := s) (by linarith)
  have hlag := iwaniecAuxM_pos (s := s - 1) (by linarith)
  have hGPos := iwaniecAuxG_pos rank (s := s - 1) (by linarith)
  have htop := (iwaniecAuxG_bounds (rank + 1) (s := s) (by linarith)).2
  have hbottom := (iwaniecAuxG_bounds rank (s := s - 1) (by linarith)).1
  have hsq : (s - 1) ^ 2 ≤ s ^ 2 := by nlinarith
  have hmain := iwaniecAuxM_s_log_lt_four_lag hs
  have hfirst : iwaniecAuxG (rank + 1) s * (s - 1) ^ 2 * Real.log s ≤
      (2 * iwaniecAuxM s / 3) * s ^ 2 * Real.log s := by
    apply mul_le_mul_of_nonneg_right _ hlog
    exact mul_le_mul htop hsq (sq_nonneg (s - 1)) (by positivity)
  have hsecond : (2 * iwaniecAuxM s / 3) * s ^ 2 * Real.log s <
      (8 * iwaniecAuxM (s - 1) / 3) * s := by
    have h := mul_lt_mul_of_pos_right hmain (show 0 < 2 * s / 3 by linarith)
    convert h using 1 <;> ring
  have hthird : (8 * iwaniecAuxM (s - 1) / 3) * s ≤
      8 * (iwaniecAuxG rank (s - 1) * s) := by
    have h := mul_le_mul_of_nonneg_right hbottom (show 0 ≤ 8 * s by linarith)
    convert h using 1 <;> ring
  unfold iwaniecAuxCorollaryRatio
  rw [div_lt_iff₀ (mul_pos hGPos hsPos)]
  exact (hfirst.trans_lt hsecond).trans_le hthird

theorem iwaniecAuxCorollaryRatio_initial_bound
    (rank : Nat) {s : Real} (hs : s ∈ Set.Icc (3 : Real) 6) :
    iwaniecAuxCorollaryRatio rank s ≤ 300 / iwaniecAuxM 5 := by
  have hsPos : 0 < s := by linarith [hs.1]
  have hlog : 0 ≤ Real.log s := Real.log_nonneg (by linarith [hs.1])
  have hlogUpper : Real.log s ≤ 6 := by
    have h := Real.log_le_sub_one_of_pos hsPos
    linarith [hs.2]
  have hsq : (s - 1) ^ 2 ≤ 25 := by nlinarith [hs.1, hs.2]
  have htop := iwaniecAuxG_le_two (rank + 1) (s := s) (by linarith [hs.1])
  have htopPos := iwaniecAuxG_pos (rank + 1) (s := s) (by linarith [hs.1])
  have hbottomPos := iwaniecAuxG_pos rank (s := s - 1) (by linarith [hs.1])
  have hM5 := iwaniecAuxM_pos (s := 5) (by norm_num)
  have hMprev : iwaniecAuxM 5 ≤ iwaniecAuxM (s - 1) :=
    iwaniecAuxM_antitoneOn (show 2 ≤ s - 1 by linarith [hs.1]) (by norm_num) (by linarith [hs.2])
  have hbottom := (iwaniecAuxG_bounds rank (s := s - 1) (by linarith [hs.1])).1
  have hden : iwaniecAuxM 5 ≤ iwaniecAuxG rank (s - 1) * s := by
    have hthree : 3 * iwaniecAuxG rank (s - 1) ≤ iwaniecAuxG rank (s - 1) * s := by
      nlinarith [hs.1]
    linarith
  have hnum : iwaniecAuxG (rank + 1) s * (s - 1) ^ 2 * Real.log s ≤ 300 := by
    have hprod := mul_le_mul htop hsq (sq_nonneg (s - 1)) (by norm_num : (0 : Real) ≤ 2)
    have hscaled := mul_le_mul hprod hlogUpper hlog (by norm_num : (0 : Real) ≤ 2 * 25)
    norm_num at hscaled
    exact hscaled
  unfold iwaniecAuxCorollaryRatio
  have hnumNonneg : 0 ≤ iwaniecAuxG (rank + 1) s * (s - 1) ^ 2 * Real.log s :=
    mul_nonneg (mul_nonneg htopPos.le (sq_nonneg (s - 1))) hlog
  exact (div_le_div_of_nonneg_left hnumNonneg hM5 hden).trans
    (div_le_div_of_nonneg_right hnum hM5.le)

end

end Erdos1212Kernel
