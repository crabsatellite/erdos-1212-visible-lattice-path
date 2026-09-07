import Erdos1212Kernel.TaoPNTHolomorphicStripBound

namespace Erdos1212Kernel

noncomputable section

open Set Complex

set_option maxHeartbeats 1900000

theorem taoPerron_horizontal_boundary_bound_of_strip
    {δ C L H x : Real} (hδpos : 0 < δ) (hC : 0 ≤ C)
    (hHpos : 0 < H) (hx : 1 ≤ x)
    (hstrip : ∀ T u : Real, |T| ≤ H → 1 - δ ≤ u → u ≤ 1 + δ →
      taoZetaPoleRemoved ((u : Complex) + (T : Complex) * I) ≠ 0 ∧
      ‖logDeriv taoZetaPoleRemoved ((u : Complex) + (T : Complex) * I)‖ ≤ C * L ^ 2) :
        let β := 1 - δ
        let σ := 1 + δ
        ‖(∫ u : Real in β..σ,
              taoPerronFullIntegrand x
                ((u : Complex) + ((-H : Real) : Complex) * Complex.I)) -
            ∫ u : Real in β..σ,
              taoPerronFullIntegrand x
                ((u : Complex) + (H : Complex) * Complex.I)‖ ≤
          4 * δ * (1 / H + C * L ^ 2) * x ^ σ * (1 / H ^ 2) := by
  let β : Real := 1 - δ
  let σ : Real := 1 + δ
  have hβσ : β ≤ σ := by dsimp [β, σ]; linarith
  have hpoint (T u : Real) (hT : T = H ∨ T = -H)
      (huβ : β ≤ u) (huσ : u ≤ σ) :
      ‖taoPerronFullIntegrand x
          ((u : Complex) + (T : Complex) * Complex.I)‖ ≤
        (1 / H + C * L ^ 2) * x ^ σ * (1 / H ^ 2) := by
    have hTabs : |T| = H := by rcases hT with rfl | rfl <;> simp [hHpos.le]
    obtain ⟨hHnz, hHlog⟩ := hstrip T u hTabs.le huβ huσ
    let s : Complex := (u : Complex) + (T : Complex) * Complex.I
    have hs1 : s ≠ 1 := by
      intro hs
      have him := congrArg Complex.im hs
      simp [s] at him
      have hTne : T ≠ 0 := by intro h; rw [h, abs_zero] at hTabs; linarith
      exact hTne him
    have hzeta : riemannZeta s ≠ 0 := by
      intro hz
      rw [taoZetaPoleRemoved_of_ne_one hs1, hz, mul_zero] at hHnz
      exact hHnz rfl
    have hlogFull := norm_taoZetaLogDerivative_le_of_poleRemoved_bound
      hs1 hzeta (B := C * L ^ 2) (by simpa only [s] using hHlog)
    have himNorm : H ≤ ‖s - 1‖ := by
      have hi := Complex.abs_im_le_norm (s - 1)
      simpa [s, hTabs] using hi
    have hpole : 1 / ‖s - 1‖ ≤ 1 / H :=
      one_div_le_one_div_of_le hHpos himNorm
    have hlogBound : ‖taoZetaLogDerivative s‖ ≤ 1 / H + C * L ^ 2 :=
      hlogFull.trans (add_le_add_left hpole _)
    have hfactor0 := norm_taoPerronAnalyticFactor_horizontal_le
      (x := x) (u := u) (T := T) (by linarith) (by
        intro hT0
        rw [hT0, abs_zero] at hTabs
        linarith)
    have hpow : x ^ u ≤ x ^ σ :=
      Real.rpow_le_rpow_of_exponent_le hx huσ
    have hfactor : ‖taoPerronAnalyticFactor x s‖ ≤
        x ^ σ * (1 / H ^ 2) := by
      have hsq : T ^ 2 = H ^ 2 := by nlinarith [sq_abs T, sq_abs H, hTabs]
      simpa only [s, hsq] using hfactor0.trans
        (mul_le_mul_of_nonneg_right hpow (by positivity : 0 ≤ 1 / T ^ 2))
    unfold taoPerronFullIntegrand
    rw [norm_mul]
    have hm := mul_le_mul hlogBound hfactor (norm_nonneg
      (taoPerronAnalyticFactor x s)) (by positivity : 0 ≤ 1 / H + C * L ^ 2)
    simpa only [s, mul_assoc] using hm
  have hbottom := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := β) (b := σ)
    (C := (1 / H + C * L ^ 2) * x ^ σ * (1 / H ^ 2))
    (fun u hu => by
      have hu' := Set.uIoc_subset_uIcc hu
      rw [Set.uIcc_of_le hβσ] at hu'
      exact hpoint (-H) u (Or.inr rfl) hu'.1 hu'.2)
  have htop := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := β) (b := σ)
    (C := (1 / H + C * L ^ 2) * x ^ σ * (1 / H ^ 2))
    (fun u hu => by
      have hu' := Set.uIoc_subset_uIcc hu
      rw [Set.uIcc_of_le hβσ] at hu'
      exact hpoint H u (Or.inl rfl) hu'.1 hu'.2)
  have hwidth : |σ - β| = 2 * δ := by
    dsimp [σ, β]
    rw [abs_of_pos (by linarith)]
    ring
  calc
    ‖(∫ u : Real in β..σ, taoPerronFullIntegrand x (↑u + ↑(-H) * Complex.I)) -
        ∫ u : Real in β..σ, taoPerronFullIntegrand x (↑u + ↑H * Complex.I)‖ ≤
      ‖∫ u : Real in β..σ, taoPerronFullIntegrand x (↑u + ↑(-H) * Complex.I)‖ +
        ‖∫ u : Real in β..σ, taoPerronFullIntegrand x (↑u + ↑H * Complex.I)‖ := norm_sub_le _ _
    _ ≤ 2 * ((1 / H + C * L ^ 2) * x ^ σ * (1 / H ^ 2) * |σ - β|) := by linarith
    _ = 4 * δ * (1 / H + C * L ^ 2) * x ^ σ * (1 / H ^ 2) := by
      rw [hwidth]
      ring

theorem exists_taoPerron_horizontal_boundary_bound :
    ∃ d C H₀ : Real, 0 < d ∧ 0 < C ∧
      ∀ H x : Real,
        H₀ ≤ H → 1 ≤ x →
        let L := Real.log (3 + H)
        let δ := d / L
        let β := 1 - δ
        let σ := 1 + δ
        ‖(∫ u : Real in β..σ,
              taoPerronFullIntegrand x ((u : Complex) + ((-H : Real) : Complex) * I)) -
            ∫ u : Real in β..σ,
              taoPerronFullIntegrand x ((u : Complex) + (H : Complex) * I)‖ ≤
          4 * δ * (1 / H + C * L ^ 2) * x ^ σ * (1 / H ^ 2) := by
  obtain ⟨d, C, H₁, hd, hC, hstrip⟩ := exists_taoPNT_fixed_holomorphic_global_strip
  refine ⟨d, C, max H₁ 1, hd, hC, ?_⟩
  intro H x hH hx
  have hH1 := (le_max_left H₁ 1).trans hH
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one ((le_max_right H₁ 1).trans hH)
  have hLpos : 0 < Real.log (3 + H) := Real.log_pos (by linarith)
  apply taoPerron_horizontal_boundary_bound_of_strip (div_pos hd hLpos) hC.le hHpos hx
  intro T u hT hu0 hu1
  exact (hstrip H T u hH1 hT).2.2 hu0 hu1

end

end Erdos1212Kernel
