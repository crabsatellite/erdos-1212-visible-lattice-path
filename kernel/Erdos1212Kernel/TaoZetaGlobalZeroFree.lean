import Erdos1212Kernel.TaoZetaZeroFreeRegion

namespace Erdos1212Kernel

noncomputable section

open Metric

set_option maxHeartbeats 1900000

theorem exists_pos_le_on_finset
    {α : Type*} [DecidableEq α] (S : Finset α) (f : α → Real)
    (hf : ∀ x ∈ S, 0 < f x) :
    ∃ g : Real, 0 < g ∧ ∀ x ∈ S, g ≤ f x := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert x S hx ih =>
      obtain ⟨g, hg, hgle⟩ := ih (fun y hy => hf y (Finset.mem_insert_of_mem hy))
      refine ⟨min g (f x), lt_min hg (hf x (by simp)), ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hgle y hy)

theorem exists_bounded_frequency_zeta_zero_free_strip
    (H : Real) (hH : 0 ≤ H) :
    ∃ g : Real, 0 < g ∧ ∀ (t β : Real),
      taoLogFrequency t ≤ H → 1 - g < β →
      riemannZeta ((β : Complex) + (t : Complex) * Complex.I) ≠ 0 := by
  let B : Real := 1 + 2 * Real.pi * H
  let S := taoZetaZerosInClosedBall 0 B
  obtain ⟨g, hg, hgle⟩ := exists_pos_le_on_finset S
    (fun ρ => 1 - ρ.re) (fun ρ hρ => by
      have hz := (mem_taoZetaZerosInClosedBall.mp hρ).2
      linarith [taoZetaZero_re_lt_one hz])
  let g0 : Real := min 1 g
  have hg0 : 0 < g0 := lt_min (by norm_num) hg
  refine ⟨g0, hg0, fun t β ht hβ => ?_⟩
  intro hzero
  have hβlt : β < 1 := by
    have := taoZetaZero_re_lt_one hzero
    simpa using this
  have hβpos : 0 < β := by
    have hg01 : g0 ≤ 1 := min_le_left _ _
    linarith
  have habsβ : |β| ≤ 1 := by rw [abs_of_pos hβpos]; exact hβlt.le
  have habst : |t| ≤ 2 * Real.pi * H := by
    unfold taoLogFrequency at ht
    have hpi : 0 < 2 * Real.pi := by positivity
    simpa only [mul_comm] using (div_le_iff₀ hpi).mp ht
  have hnorm : ‖(β : Complex) + (t : Complex) * Complex.I‖ ≤ B := by
    calc
      _ ≤ ‖(β : Complex)‖ + ‖(t : Complex) * Complex.I‖ := norm_add_le _ _
      _ = |β| + |t| := by simp
      _ ≤ 1 + 2 * Real.pi * H := add_le_add habsβ habst
      _ = B := rfl
  have hmem : (β : Complex) + (t : Complex) * Complex.I ∈ S := by
    unfold S
    rw [mem_taoZetaZerosInClosedBall]
    constructor
    · rw [dist_zero_right]
      exact hnorm
    · exact hzero
  have hgap := hgle ((β : Complex) + (t : Complex) * Complex.I) hmem
  have hg0g : g0 ≤ g := min_le_right _ _
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_zero] at hgap
  linarith

def taoPNTFrequency (t : Real) : Real := 3 + |t|

theorem taoPNTFrequency_gt_one (t : Real) : 1 < taoPNTFrequency t := by
  unfold taoPNTFrequency
  linarith [abs_nonneg t]

theorem exists_riemannZeta_global_zero_free_region_log :
    ∃ c : Real, 0 < c ∧ ∀ (t β : Real),
      1 - c / Real.log (taoPNTFrequency t) < β →
      riemannZeta ((β : Complex) + (t : Complex) * Complex.I) ≠ 0 := by
  obtain ⟨ch, H, hch, hhigh⟩ := exists_riemannZeta_zero_free_region_log
  let H0 : Real := max H 2
  have hH0 : 0 ≤ H0 := by unfold H0; linarith [le_max_right H 2]
  obtain ⟨gl, hgl, hlow⟩ := exists_bounded_frequency_zeta_zero_free_strip H0 hH0
  let c : Real := min ch (gl * Real.log 3)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hc : 0 < c := lt_min hch (mul_pos hgl hlog3)
  refine ⟨c, hc, fun t β hβ => ?_⟩
  by_cases ht : H0 ≤ taoLogFrequency t
  · apply hhigh t β ((le_max_left H 2).trans ht)
    have hTtwo : 2 ≤ taoLogFrequency t := (le_max_right H 2).trans ht
    have hTpos : 0 < taoLogFrequency t := by linarith
    have hlogT : 0 < Real.log (taoLogFrequency t) := by
      exact Real.log_pos (by linarith)
    have hfreqCompare : taoLogFrequency t ≤ taoPNTFrequency t := by
      unfold taoLogFrequency taoPNTFrequency
      have hden : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      have := div_le_self (abs_nonneg t) hden
      linarith
    have hlogCompare : Real.log (taoLogFrequency t) ≤
        Real.log (taoPNTFrequency t) := Real.log_le_log hTpos hfreqCompare
    have hcch : c ≤ ch := min_le_left _ _
    have hfrac : c / Real.log (taoPNTFrequency t) ≤
        ch / Real.log (taoLogFrequency t) := by
      calc
        c / Real.log (taoPNTFrequency t) ≤ ch / Real.log (taoPNTFrequency t) :=
          div_le_div_of_nonneg_right hcch
            (Real.log_pos (taoPNTFrequency_gt_one t)).le
        _ ≤ ch / Real.log (taoLogFrequency t) :=
          div_le_div_of_nonneg_left hch.le hlogT hlogCompare
    linarith
  · have hbounded : taoLogFrequency t ≤ H0 := le_of_not_ge ht
    apply hlow t β hbounded
    have hlogF : Real.log 3 ≤ Real.log (taoPNTFrequency t) :=
      Real.log_le_log (by norm_num) (by unfold taoPNTFrequency; linarith [abs_nonneg t])
    have hcgl : c ≤ gl * Real.log 3 := min_le_right _ _
    have hfrac : c / Real.log (taoPNTFrequency t) ≤ gl := by
      apply (div_le_iff₀ (Real.log_pos (taoPNTFrequency_gt_one t))).2
      have := mul_le_mul_of_nonneg_left hlogF hgl.le
      linarith
    linarith

theorem exists_riemannZeta_zero_free_rectangles :
    ∃ c : Real, 0 < c ∧ ∀ (H t β : Real), 0 ≤ H → |t| ≤ H →
      1 - c / Real.log (3 + H) < β →
      riemannZeta ((β : Complex) + (t : Complex) * Complex.I) ≠ 0 := by
  obtain ⟨c, hc, hglobal⟩ := exists_riemannZeta_global_zero_free_region_log
  refine ⟨c, hc, fun H t β hH ht hβ => hglobal t β ?_⟩
  have hlocal : taoPNTFrequency t ≤ 3 + H := by
    unfold taoPNTFrequency
    linarith
  have hlogLocal : Real.log (taoPNTFrequency t) ≤ Real.log (3 + H) :=
    Real.log_le_log (by unfold taoPNTFrequency; linarith [abs_nonneg t]) hlocal
  have hlogPos : 0 < Real.log (taoPNTFrequency t) :=
    Real.log_pos (taoPNTFrequency_gt_one t)
  have hlogH : 0 < Real.log (3 + H) := Real.log_pos (by linarith)
  have hfrac : c / Real.log (3 + H) ≤ c / Real.log (taoPNTFrequency t) :=
    div_le_div_of_nonneg_left hc.le hlogPos hlogLocal
  linarith

end

end Erdos1212Kernel
