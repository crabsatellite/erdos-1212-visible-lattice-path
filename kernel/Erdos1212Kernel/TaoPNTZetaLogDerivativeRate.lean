import Erdos1212Kernel.TaoPNTLogDerivativeRate

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 1900000

theorem exists_eventual_taoPNT_zetaLogDerivative_log_sq :
    ∃ d C U₀ : Real, 0 < d ∧ 0 < C ∧
      ∀ t : Real,
        U₀ ≤ taoLogFrequency t →
        let L := Real.log (taoPNTFrequency t)
        let δ := d / L
        let β := 1 - δ
        ∀ γ : Real, β ≤ γ → γ ≤ 1 →
          (‖taoZetaLogDerivative
              ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤
            C * L ^ 2) ∧
            riemannZeta ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0 := by
  obtain ⟨d, C₀, U₁, hd, hC₀, hraw⟩ :=
    exists_eventual_taoPNT_poleRemoved_logDerivative_log_sq
  obtain ⟨Ul, hUl⟩ := Filter.eventually_atTop.1
    (Real.tendsto_log_atTop.eventually_ge_atTop 1)
  let C : Real := C₀ + 1
  let U₀ : Real := max U₁ (max Ul 4)
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨d, C, U₀, hd, hC, ?_⟩
  intro t ht
  let U : Real := taoLogFrequency t
  let P : Real := taoPNTFrequency t
  let L : Real := Real.log P
  let δ : Real := d / L
  let β : Real := 1 - δ
  have hU1 : U₁ ≤ U := by dsimp [U, U₀] at ht ⊢; linarith [le_max_left U₁ (max Ul 4)]
  have hUlU : Ul ≤ U := by dsimp [U, U₀] at ht ⊢; linarith [le_max_right U₁ (max Ul 4), le_max_left Ul 4]
  have hU4 : 4 ≤ U := by dsimp [U, U₀] at ht ⊢; linarith [le_max_right U₁ (max Ul 4), le_max_right Ul 4]
  have hlogU : 1 ≤ Real.log U := hUl U hUlU
  have hUpos : 0 < U := by linarith
  have htU : |t| = (2 * Real.pi) * U := by
    dsimp [U]
    unfold taoLogFrequency
    field_simp [Real.pi_ne_zero]
  have hPpos : 0 < P := by
    dsimp [P]
    exact (taoPNTFrequency_gt_one t).trans' zero_lt_one
  have hUP : U ≤ P := by
    dsimp [P]
    unfold taoPNTFrequency
    rw [htU]
    have hpi := Real.pi_gt_three
    nlinarith
  have hlogP : 1 ≤ L := by
    dsimp [L]
    exact hlogU.trans (Real.log_le_log hUpos hUP)
  change ∀ γ : Real, β ≤ γ → γ ≤ 1 →
    (‖taoZetaLogDerivative
        ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤ C * L ^ 2) ∧
      riemannZeta ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0
  intro γ hβγ hγ1
  have hδpos : 0 < δ := div_pos hd (by dsimp [L]; linarith)
  obtain ⟨hH, hzeta⟩ := hraw t hU1 γ hβγ (by linarith)
  let s : Complex := (γ : Complex) + (t : Complex) * Complex.I
  have hs1 : s ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp [s] at him
    subst t
    norm_num [U, taoLogFrequency] at hU4
  have him : |t| ≤ ‖s - 1‖ := by
    have hi := Complex.abs_im_le_norm (s - 1)
    simpa [s] using hi
  have htOne : 1 ≤ |t| := by
    rw [htU]
    have hpi := Real.pi_gt_three
    nlinarith
  have hpole : 1 / ‖s - 1‖ ≤ 1 := by
    apply (div_le_one₀ (norm_pos_iff.mpr (sub_ne_zero.mpr hs1))).2
    exact htOne.trans him
  have hfull := norm_taoZetaLogDerivative_le_of_poleRemoved_bound
    hs1 (by simpa only [s] using hzeta)
      (B := C₀ * L ^ 2) (by simpa only [s, β, δ, L] using hH)
  have hLsq : 1 ≤ L ^ 2 := one_le_pow₀ hlogP
  refine ⟨?_, by simpa only [s, β, δ, L] using hzeta⟩
  calc
    ‖taoZetaLogDerivative s‖ ≤ 1 / ‖s - 1‖ + C₀ * L ^ 2 := hfull
    _ ≤ 1 + C₀ * L ^ 2 := add_le_add_left hpole _
    _ ≤ C * L ^ 2 := by dsimp [C]; nlinarith

end

end Erdos1212Kernel
