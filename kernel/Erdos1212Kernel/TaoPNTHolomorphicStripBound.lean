import Erdos1212Kernel.TaoPerronLeftBoundaryBound

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

theorem exists_taoPNT_fixed_holomorphic_high_strip :
    ∃ d C U₀ : Real, 0 < d ∧ 0 < C ∧
      ∀ H t γ : Real,
        0 ≤ H → |t| ≤ H → U₀ ≤ taoLogFrequency t →
        let L := Real.log (3 + H)
        let β := 1 - d / L
        β ≤ γ → γ ≤ 1 + d / L →
        taoZetaPoleRemoved ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0 ∧
        ‖logDeriv taoZetaPoleRemoved
          ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤ C * L ^ 2 := by
  obtain ⟨d, C, U₀, hd, hC, hstrip⟩ :=
    exists_eventual_taoPNT_poleRemoved_logDerivative_log_sq
  refine ⟨d, C, U₀, hd, hC, ?_⟩
  intro H t γ hH ht hhigh
  let Pt : Real := taoPNTFrequency t
  let PH : Real := 3 + H
  let Lt : Real := Real.log Pt
  let LH : Real := Real.log PH
  let βt : Real := 1 - d / Lt
  let βH : Real := 1 - d / LH
  change βH ≤ γ → γ ≤ 1 + d / LH →
    taoZetaPoleRemoved ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0 ∧
      ‖logDeriv taoZetaPoleRemoved
        ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤ C * LH ^ 2
  intro hβHγ hγ1
  have hPt : 1 < Pt := taoPNTFrequency_gt_one t
  have hPH : 1 < PH := by dsimp [PH]; linarith
  have hPtpos : 0 < Pt := hPt.trans' zero_lt_one
  have hPtPH : Pt ≤ PH := by
    dsimp [Pt, PH]
    unfold taoPNTFrequency
    linarith
  have hlogOrder : Lt ≤ LH := by
    dsimp [Lt, LH]
    exact Real.log_le_log hPtpos hPtPH
  have hLt : 0 < Lt := by dsimp [Lt]; exact Real.log_pos hPt
  have hLH : 0 < LH := by dsimp [LH]; exact Real.log_pos hPH
  have hdiv : d / LH ≤ d / Lt :=
    div_le_div_of_nonneg_left hd.le hLt hlogOrder
  have hβ : βt ≤ βH := by dsimp [βt, βH]; linarith
  obtain ⟨hbound, hzeta⟩ := hstrip t hhigh γ (hβ.trans hβHγ) (by linarith)
  have hsq : Lt ^ 2 ≤ LH ^ 2 := by nlinarith
  have hHnz : taoZetaPoleRemoved
      ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0 := by
    by_cases hs1 : ((γ : Complex) + (t : Complex) * Complex.I) = 1
    · rw [hs1]
      simp
    · rw [taoZetaPoleRemoved_of_ne_one hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1) hzeta
  refine ⟨hHnz, ?_⟩
  exact hbound.trans (mul_le_mul_of_nonneg_left hsq hC.le)

theorem exists_taoPNT_fixed_holomorphic_global_strip :
    ∃ d C H₀ : Real, 0 < d ∧ 0 < C ∧
      ∀ H t γ : Real,
        H₀ ≤ H → |t| ≤ H →
        let L := Real.log (3 + H)
        let β := 1 - d / L
        0 < β ∧ β < 1 ∧
        (β ≤ γ → γ ≤ 1 + d / L →
          taoZetaPoleRemoved ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0 ∧
          ‖logDeriv taoZetaPoleRemoved
            ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤ C * L ^ 2) := by
  obtain ⟨d, Ch, U₀, hd, hCh, hhigh⟩ :=
    exists_taoPNT_fixed_holomorphic_high_strip
  let A : Real := max U₀ 0
  obtain ⟨e, K, he, hehalf, hK, hlow⟩ :=
    exists_taoPNT_low_frequency_poleRemoved_bound A (le_max_right _ _)
  let C : Real := max Ch K
  have hC : 0 < C := hCh.trans_le (le_max_left _ _)
  let B : Real := max 1 (d / e)
  let H₀ : Real := Real.exp B
  refine ⟨d, C, H₀, hd, hC, ?_⟩
  intro H t γ hH ht
  let L : Real := Real.log (3 + H)
  let β : Real := 1 - d / L
  change 0 < β ∧ β < 1 ∧
    (β ≤ γ → γ ≤ 1 + d / L →
      taoZetaPoleRemoved ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0 ∧
      ‖logDeriv taoZetaPoleRemoved
        ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤ C * L ^ 2)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBde : d / e ≤ B := le_max_right _ _
  have hHpos : 0 < H := by
    dsimp [H₀] at hH
    linarith [Real.exp_pos B]
  have hlogLower : B ≤ L := by
    have hmono := Real.log_le_log (Real.exp_pos B)
      (show Real.exp B ≤ 3 + H by
        dsimp [H₀] at hH
        linarith)
    rw [Real.log_exp] at hmono
    simpa only [L] using hmono
  have hL1 : 1 ≤ L := hB1.trans hlogLower
  have hL : 0 < L := by linarith
  have hde : d / L ≤ e := by
    apply (div_le_iff₀ hL).2
    have := (div_le_iff₀ he).1 hBde
    nlinarith
  have hβ0 : 0 < β := by dsimp [β]; linarith [hehalf]
  have hβ1 : β < 1 := by dsimp [β]; linarith [div_pos hd hL]
  refine ⟨hβ0, hβ1, ?_⟩
  intro hβγ hγ1
  by_cases hfreq : U₀ ≤ taoLogFrequency t
  · obtain ⟨hHnz, hb⟩ := hhigh H t γ hHpos.le ht hfreq hβγ hγ1
    exact ⟨hHnz, hb.trans (mul_le_mul_of_nonneg_right
      (le_max_left Ch K) (sq_nonneg L))⟩
  · have hfreqA : taoLogFrequency t ≤ A := by
      have hlt := (lt_of_not_ge hfreq).le
      exact hlt.trans (le_max_left _ _)
    have hβstrip : 1 - e ≤ β := by dsimp [β]; linarith
    obtain ⟨hHnz, hb⟩ := hlow t γ hfreqA (hβstrip.trans hβγ) (by linarith)
    exact ⟨hHnz, (hb.trans (le_max_right Ch K)).trans
      (by have hLsq : 1 ≤ L ^ 2 := one_le_pow₀ hL1
          have hC0 : 0 ≤ C := hC.le
          nlinarith)⟩

end

end Erdos1212Kernel
