import Erdos1212Kernel.TaoPNTScaleComparison

namespace Erdos1212Kernel

noncomputable section

open Filter Metric Set Topology

set_option maxHeartbeats 1900000

theorem exists_eventual_taoPNT_poleRemoved_logDerivative_bound :
    ∃ d U₀ : Real, 0 < d ∧
      ∀ t : Real,
        U₀ ≤ taoLogFrequency t →
        let L := Real.log (taoPNTFrequency t)
        let δ := d / L
        let α := 1 + δ / 100
        let β := 1 - δ
        let R := 4 * δ
        ∀ γ : Real, β ≤ γ → γ ≤ 1 + δ →
          (‖logDeriv taoZetaPoleRemoved
              ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤
            24 * (1 + Real.log ((2 : Real) ^ 52 *
                taoLogFrequency t * (Real.log (taoLogFrequency t)) ^ 2) -
              Real.log (α - 1) +
              4 * Real.log (1 + 1 / (α - 1))) / R) ∧
            riemannZeta ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0 := by
  obtain ⟨d, hd, hgeom⟩ := exists_taoPNT_zero_free_disk_parameter
  obtain ⟨Un, hUn⟩ := exists_taoNearbyFrequencyThreshold
  obtain ⟨Us, hUs⟩ := exists_taoPNT_delta_zeroFreeBaseRadius_threshold d hd.le
  obtain ⟨Ul, hUl⟩ := Filter.eventually_atTop.1
    (Real.tendsto_log_atTop.eventually_ge_atTop 1)
  let U₀ : Real := max (max Un Us) (max Ul 4)
  refine ⟨d, U₀, hd, ?_⟩
  intro t ht
  let U : Real := taoLogFrequency t
  let L : Real := Real.log (taoPNTFrequency t)
  let δ : Real := d / L
  let α : Real := 1 + δ / 100
  let β : Real := 1 - δ
  let R : Real := 4 * δ
  have hUnU : Un ≤ U := by dsimp [U, U₀] at ht ⊢; linarith [le_max_left (max Un Us) (max Ul 4), le_max_left Un Us]
  have hUsU : Us ≤ U := by dsimp [U, U₀] at ht ⊢; linarith [le_max_left (max Un Us) (max Ul 4), le_max_right Un Us]
  have hUlU : Ul ≤ U := by dsimp [U, U₀] at ht ⊢; linarith [le_max_right (max Un Us) (max Ul 4), le_max_left Ul 4]
  have hU4 : 4 ≤ U := by dsimp [U, U₀] at ht ⊢; linarith [le_max_right (max Un Us) (max Ul 4), le_max_right Ul 4]
  have hlogU : 1 ≤ Real.log U := hUl U hUlU
  have hUpos : 0 < U := by linarith
  have htU : |t| = (2 * Real.pi) * U := by
    dsimp [U]
    unfold taoLogFrequency
    field_simp [Real.pi_ne_zero]
  have hPNT : taoPNTFrequency t = 3 + (2 * Real.pi) * U := by
    unfold taoPNTFrequency
    rw [htU]
  have hUPNT : U ≤ taoPNTFrequency t := by
    rw [hPNT]
    have hpi := Real.pi_gt_three
    nlinarith
  have hLP : 1 ≤ L := by
    dsimp [L]
    exact hlogU.trans (Real.log_le_log hUpos hUPNT)
  obtain ⟨hδ, hR1, hα, hright, hβ0, hβ1, htarget, hHnz⟩ :=
    hgeom t hLP
  have hscale0 := hUs U hUsU
  have hscale : (399 / 100 : Real) * δ ≤
      taoZeroFreeBaseRadius U / 4 := by
    dsimp [δ, L]
    rw [hPNT]
    exact hscale0
  have hleft : 1 - taoZeroFreeBaseRadius U / 4 ≤ α - R := by
    dsimp [α, R]
    linarith
  have hnear : ∀ V ∈ Set.Icc (U - 1) (U + 1),
      TaoLittlewoodFinalFrequencyConditions V ∧
      4 ≤ V ∧ 1 ≤ Real.log V ∧
      taoZeroFreeBaseRadius U / 4 ≤
        taoLittlewoodWidth V (taoLittlewoodR V) ∧
      Real.log V ≤ 2 * Real.log U := by
    intro V hV
    exact hUn U V hUnU hV
  have hRpos : 0 < R := by dsimp [R]; positivity
  change ∀ γ : Real, β ≤ γ → γ ≤ 1 + δ →
    (‖logDeriv taoZetaPoleRemoved
        ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤
      24 * (1 + Real.log ((2 : Real) ^ 52 * U * (Real.log U) ^ 2) -
        Real.log (α - 1) +
        4 * Real.log (1 + 1 / (α - 1))) / R) ∧
      riemannZeta ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0
  intro γ hβγ hγ1
  have htargetγ : ((γ : Complex) + (t : Complex) * Complex.I) ∈
      ball ((α : Complex) + (t : Complex) * Complex.I) (R / 3) := by
    rw [mem_ball, Complex.dist_eq]
    have hdiff : ((γ : Complex) + (t : Complex) * Complex.I) -
        ((α : Complex) + (t : Complex) * Complex.I) =
        ((γ - α : Real) : Complex) := by push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_lt]
    dsimp [α, β, R] at hβγ hγ1 ⊢
    constructor <;> nlinarith
  have hmain := norm_logDeriv_taoZetaPoleRemoved_le_high_disk
    (t := t) (α := α) (R := R) (U := U)
    (z := ((γ : Complex) + (t : Complex) * Complex.I))
    rfl hU4 hlogU hRpos hR1 hα hleft hright hnear hHnz htargetγ
  have htargetR : ((γ : Complex) + (t : Complex) * Complex.I) ∈
      ball ((α : Complex) + (t : Complex) * Complex.I) R :=
    (ball_subset_ball (by linarith : R / 3 ≤ R)) htargetγ
  have hHtarget := hHnz _ htargetR
  have hs1 : ((γ : Complex) + (t : Complex) * Complex.I) ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp at him
    subst t
    norm_num [U, taoLogFrequency] at hU4
  have hzeta : riemannZeta
      ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0 := by
    intro hz
    rw [taoZetaPoleRemoved_of_ne_one hs1, hz, mul_zero] at hHtarget
    exact hHtarget rfl
  exact ⟨by simpa only [U, L, δ, α, β, R] using hmain, hzeta⟩

end

end Erdos1212Kernel
