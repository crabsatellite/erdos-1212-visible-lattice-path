import Erdos1212Kernel.TaoZetaPoleRemovedHighDisk

namespace Erdos1212Kernel

noncomputable section

open Metric Set

set_option maxHeartbeats 1900000

theorem exists_taoPNT_zero_free_disk_parameter :
    ∃ d : Real, 0 < d ∧
      ∀ t : Real,
        1 ≤ Real.log (taoPNTFrequency t) →
        let δ := d / Real.log (taoPNTFrequency t)
        let α := 1 + δ / 100
        let β := 1 - δ
        let R := 4 * δ
        0 < δ ∧ R ≤ 1 ∧ 1 < α ∧ α + R ≤ 2 ∧ 0 < β ∧ β < 1 ∧
          ((β : Complex) + (t : Complex) * Complex.I) ∈
            ball ((α : Complex) + (t : Complex) * Complex.I) (R / 3) ∧
          ∀ w ∈ ball ((α : Complex) + (t : Complex) * Complex.I) R,
            taoZetaPoleRemoved w ≠ 0 := by
  obtain ⟨c, hc, hzero⟩ := exists_riemannZeta_global_zero_free_region_log
  let d : Real := min (c / 1000) (1 / 1000)
  have hd : 0 < d := lt_min (div_pos hc (by norm_num)) (by norm_num)
  have hdc : d ≤ c / 1000 := min_le_left _ _
  have hdsmall : d ≤ 1 / 1000 := min_le_right _ _
  refine ⟨d, hd, ?_⟩
  intro t hL1
  let L : Real := Real.log (taoPNTFrequency t)
  let δ : Real := d / L
  let α : Real := 1 + δ / 100
  let β : Real := 1 - δ
  let R : Real := 4 * δ
  have hL : 0 < L := by dsimp [L]; linarith
  have hδ : 0 < δ := div_pos hd hL
  have hδle : δ ≤ d := by
    dsimp [δ]
    exact (div_le_iff₀ hL).2 (by
      have hd0 : 0 ≤ d := hd.le
      nlinarith)
  have hR1 : R ≤ 1 := by
    dsimp [R]
    linarith
  have hα : 1 < α := by dsimp [α]; linarith
  have hright : α + R ≤ 2 := by
    dsimp [α, R]
    have : δ ≤ 1 / 1000 := hδle.trans hdsmall
    linarith
  have hβ0 : 0 < β := by
    dsimp [β]
    have : δ ≤ 1 / 1000 := hδle.trans hdsmall
    linarith
  have hβ1 : β < 1 := by dsimp [β]; linarith
  have htarget : ((β : Complex) + (t : Complex) * Complex.I) ∈
      ball ((α : Complex) + (t : Complex) * Complex.I) (R / 3) := by
    rw [mem_ball, Complex.dist_eq]
    have hdiff : ((β : Complex) + (t : Complex) * Complex.I) -
        ((α : Complex) + (t : Complex) * Complex.I) =
        ((β - α : Real) : Complex) := by push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
    have hba : β - α = -(101 / 100 : Real) * δ := by
      dsimp [β, α]
      ring
    rw [hba, abs_mul, abs_neg, abs_of_nonneg hδ.le]
    norm_num
    dsimp [R]
    nlinarith
  refine ⟨hδ, hR1, hα, hright, hβ0, hβ1, htarget, ?_⟩
  intro w hw
  by_cases hw1 : w = 1
  · subst w
    simp
  · apply taoZetaPoleRemoved_ne_zero_of_eq_one_or_zeta_ne_zero
    right
    have hdist : dist w ((α : Complex) + (t : Complex) * Complex.I) < R :=
      mem_ball.mp hw
    have hreDist := abs_re_sub_le_dist w
      ((α : Complex) + (t : Complex) * Complex.I)
    have hcre : (((α : Complex) + (t : Complex) * Complex.I)).re = α := by simp
    rw [hcre] at hreDist
    have hwre : 1 - (399 / 100 : Real) * δ < w.re := by
      have habs : |w.re - α| < R := hreDist.trans_lt hdist
      rw [abs_lt] at habs
      dsimp [α, R] at habs
      linarith
    have him : |w.im - t| ≤
        dist w ((α : Complex) + (t : Complex) * Complex.I) := by
      have hi := Complex.abs_im_le_norm
        (w - ((α : Complex) + (t : Complex) * Complex.I))
      rw [Complex.dist_eq]
      convert hi using 1 <;> simp
    have him1 : |w.im - t| < 1 :=
      him.trans_lt (hdist.trans_le hR1)
    have habsIm : |w.im| ≤ |t| + 1 := by
      calc
        |w.im| = |(w.im - t) + t| := by rw [sub_add_cancel]
        _ ≤ |w.im - t| + |t| := abs_add_le _ _
        _ ≤ |t| + 1 := by linarith
    have hfreq : taoPNTFrequency w.im ≤ 2 * taoPNTFrequency t := by
      unfold taoPNTFrequency
      linarith [abs_nonneg t]
    have hfreqW : 0 < taoPNTFrequency w.im := by
      unfold taoPNTFrequency
      linarith [abs_nonneg w.im]
    have hfreqT : 0 < taoPNTFrequency t := by
      exact (taoPNTFrequency_gt_one t).trans' zero_lt_one
    have hlogWpos : 0 < Real.log (taoPNTFrequency w.im) :=
      Real.log_pos (taoPNTFrequency_gt_one w.im)
    have hlogWle : Real.log (taoPNTFrequency w.im) ≤ 2 * L := by
      have hmono := Real.log_le_log hfreqW hfreq
      rw [Real.log_mul (by norm_num : (2 : Real) ≠ 0) hfreqT.ne'] at hmono
      have hlog2 : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
        norm_num at h
        exact h
      dsimp only [L]
      linarith
    have hloss : (399 / 100 : Real) * δ ≤
        c / Real.log (taoPNTFrequency w.im) := by
      have hfirst : (399 / 100 : Real) * δ ≤ c / (2 * L) := by
        rw [show (399 / 100 : Real) * δ =
            ((399 / 100 : Real) * d) / L by
              dsimp [δ]
              ring]
        rw [show c / (2 * L) = (c / 2) / L by ring]
        apply (div_le_div_iff_of_pos_right hL).2
        have hdc' : 1000 * d ≤ c := by linarith
        nlinarith
      have hsecond : c / (2 * L) ≤
          c / Real.log (taoPNTFrequency w.im) :=
        div_le_div_of_nonneg_left hc.le hlogWpos hlogWle
      exact hfirst.trans hsecond
    have hzeta := hzero w.im w.re (by
      have : 1 - c / Real.log (taoPNTFrequency w.im) ≤
          1 - (399 / 100 : Real) * δ := by linarith
      exact this.trans_lt hwre)
    simpa only [Complex.re_add_im] using hzeta

end

end Erdos1212Kernel
