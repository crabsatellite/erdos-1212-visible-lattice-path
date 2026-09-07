import Erdos1212Kernel.TaoPNTLogDerivativeLow

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

theorem exists_taoPNT_fixed_left_global_logDerivative_log_sq :
    ∃ d C H₀ : Real, 0 < d ∧ 0 < C ∧
      ∀ H t : Real,
        H₀ ≤ H → |t| ≤ H →
        let L := Real.log (3 + H)
        let β := 1 - d / L
        0 < β ∧ β < 1 ∧
          (‖taoZetaLogDerivative
              ((β : Complex) + (t : Complex) * Complex.I)‖ ≤
            C * L ^ 2) ∧
          riemannZeta ((β : Complex) + (t : Complex) * Complex.I) ≠ 0 := by
  obtain ⟨d, Ch, U₀, hd, hCh, hhigh⟩ :=
    exists_taoPNT_fixed_left_logDerivative_log_sq
  let A : Real := max U₀ 0
  have hA : 0 ≤ A := le_max_right _ _
  obtain ⟨e, K, he, hehalf, hK, hlow⟩ :=
    exists_taoPNT_low_frequency_poleRemoved_bound A hA
  let C : Real := max Ch (1 / d + K)
  have hC : 0 < C := hCh.trans_le (le_max_left _ _)
  let B : Real := max 1 (d / e)
  let H₀ : Real := Real.exp B
  refine ⟨d, C, H₀, hd, hC, ?_⟩
  intro H t hH ht
  let L : Real := Real.log (3 + H)
  let β : Real := 1 - d / L
  have hB1 : 1 ≤ B := le_max_left _ _
  have hBde : d / e ≤ B := le_max_right _ _
  have hHpos : 0 < H := by
    have hexp : 0 < Real.exp B := Real.exp_pos B
    dsimp [H₀] at hH
    linarith
  have harg : 0 < 3 + H := by linarith
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
    have hmul : d ≤ e * B := by
      have := (div_le_iff₀ he).1 hBde
      nlinarith
    nlinarith
  have hβ0 : 0 < β := by
    dsimp [β]
    have : e ≤ 1 / 2 := hehalf
    linarith
  have hβ1 : β < 1 := by
    dsimp [β]
    have := div_pos hd hL
    linarith
  have hpair :
      (‖taoZetaLogDerivative
          ((β : Complex) + (t : Complex) * Complex.I)‖ ≤ C * L ^ 2) ∧
        riemannZeta ((β : Complex) + (t : Complex) * Complex.I) ≠ 0 := by
    by_cases hfreq : U₀ ≤ taoLogFrequency t
    · have hh := hhigh H t hHpos.le ht hfreq
      obtain ⟨hb, hz⟩ := hh β le_rfl hβ1.le
      exact ⟨hb.trans (mul_le_mul_of_nonneg_right (le_max_left Ch (1 / d + K))
        (sq_nonneg L)), hz⟩
    · have hfreqA : taoLogFrequency t ≤ A := by
        dsimp [A]
        have hlt : taoLogFrequency t < U₀ := lt_of_not_ge hfreq
        exact hlt.le.trans (le_max_left _ _)
      have hβstrip : 1 - e ≤ β := by dsimp [β]; linarith
      obtain ⟨hHnz, hHbound⟩ := hlow t β hfreqA hβstrip (by linarith [he])
      let s : Complex := (β : Complex) + (t : Complex) * Complex.I
      have hs1 : s ≠ 1 := by
        intro hs
        have hre := congrArg Complex.re hs
        simp [s] at hre
        linarith
      have hzeta : riemannZeta s ≠ 0 := by
        intro hz
        rw [taoZetaPoleRemoved_of_ne_one hs1, hz, mul_zero] at hHnz
        exact hHnz rfl
      have hfull := norm_taoZetaLogDerivative_le_of_poleRemoved_bound
        hs1 hzeta (B := K) (by simpa only [s] using hHbound)
      have hreNorm : d / L ≤ ‖s - 1‖ := by
        have hre := Complex.abs_re_le_norm (s - 1)
        have hdL : 0 ≤ d / L := (div_pos hd hL).le
        simpa [s, β, abs_of_nonneg hdL] using hre
      have hpole : 1 / ‖s - 1‖ ≤ L / d := by
        have hdLpos : 0 < d / L := div_pos hd hL
        have hinv := one_div_le_one_div_of_le hdLpos hreNorm
        calc
          1 / ‖s - 1‖ ≤ 1 / (d / L) := hinv
          _ = L / d := by field_simp [hd.ne', hL.ne']
      have hlowBound : L / d + K ≤ (1 / d + K) * L ^ 2 := by
        have hK0 : 0 ≤ K := hK.le
        have hLsq : 1 ≤ L ^ 2 := one_le_pow₀ hL1
        have hLin : L ≤ L ^ 2 := by nlinarith
        have hdInv : 0 < 1 / d := one_div_pos.mpr hd
        calc
          L / d + K = (1 / d) * L + K := by ring
          _ ≤ (1 / d) * L ^ 2 + K * L ^ 2 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hLin hdInv.le)
              (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hLsq hK0)
          _ = (1 / d + K) * L ^ 2 := by ring
      have hCdom : 1 / d + K ≤ C := le_max_right _ _
      exact ⟨hfull.trans (add_le_add_left hpole K) |>.trans hlowBound |>.trans
          (mul_le_mul_of_nonneg_right hCdom (sq_nonneg L)),
        by simpa only [s] using hzeta⟩
  simpa only [L, β] using
    (show 0 < β ∧ β < 1 ∧
        ‖taoZetaLogDerivative
          ((β : Complex) + (t : Complex) * Complex.I)‖ ≤ C * L ^ 2 ∧
        riemannZeta ((β : Complex) + (t : Complex) * Complex.I) ≠ 0 from
      ⟨hβ0, hβ1, hpair.1, hpair.2⟩)

end

end Erdos1212Kernel
