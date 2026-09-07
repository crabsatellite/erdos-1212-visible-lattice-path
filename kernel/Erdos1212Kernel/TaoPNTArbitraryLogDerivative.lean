import Erdos1212Kernel.TaoPNTArbitraryDisk
import Erdos1212Kernel.TaoPNTLogDerivativeRate

namespace Erdos1212Kernel

noncomputable section

open Filter Metric Set Topology

set_option maxHeartbeats 650000

theorem exists_taoPNT_logDerivative_log_sq_any_parameter (d : Real) (hd : 0 < d) :
    ∃ C U₀ : Real, 0 < C ∧ ∀ t : Real, U₀ ≤ taoLogFrequency t →
      let L := Real.log (taoPNTFrequency t)
      let δ := d / L
      ∀ γ : Real, 1 - δ ≤ γ → γ ≤ 1 + δ →
        taoZetaPoleRemoved ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0 ∧
        ‖logDeriv taoZetaPoleRemoved ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤ C * L ^ 2 := by
  obtain ⟨Ug, hgeom⟩ := exists_taoPNT_zero_free_disks_any_parameter d hd
  obtain ⟨Un, hnear⟩ := exists_taoNearbyFrequencyThreshold
  obtain ⟨Us, hscale⟩ := exists_taoPNT_delta_zeroFreeBaseRadius_threshold d hd.le
  obtain ⟨Ul, hlog⟩ := Filter.eventually_atTop.1 (Real.tendsto_log_atTop.eventually_ge_atTop 1)
  let U₀ := max Ug (max Un (max Us (max Ul 4)))
  let C := 6 * taoPNTBorelConstant d / d
  have hB : 0 < taoPNTBorelConstant d := by
    unfold taoPNTBorelConstant
    positivity
  have hC : 0 < C := div_pos (mul_pos (by norm_num) hB) hd
  refine ⟨C, U₀, hC, ?_⟩
  intro t ht
  let U := taoLogFrequency t
  let P := taoPNTFrequency t
  let L := Real.log P
  let δ := d / L
  let α := 1 + δ / 100
  let R := 4 * δ
  have hUg : Ug ≤ U := (le_max_left _ _).trans ht
  have hUn : Un ≤ U := (le_max_left _ _).trans ((le_max_right _ _).trans ht)
  have hUs : Us ≤ U := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ht))
  have hUl : Ul ≤ U := (le_max_left _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ht)))
  have hU4 : 4 ≤ U := (le_max_right _ _).trans ((le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ht)))
  have hlogU : 1 ≤ Real.log U := hlog U hUl
  have hUpos : 0 < U := by linarith only [hU4]
  have hPpos : 0 < P := (taoPNTFrequency_gt_one t).trans' zero_lt_one
  have habs : |t| = 2 * Real.pi * U := by dsimp [U, taoLogFrequency]; field_simp
  have hP : P = 3 + 2 * Real.pi * U := by dsimp [P, taoPNTFrequency]; rw [habs]
  have hUP : U ≤ P := by rw [hP]; nlinarith only [hU4, Real.pi_gt_three]
  have hL1 : 1 ≤ L := hlogU.trans (Real.log_le_log hUpos hUP)
  have hLpos : 0 < L := by linarith only [hL1]
  obtain ⟨hδ, hR1, hα, hright, hHnz⟩ := hgeom t hUg
  have hsc : (399 / 100 : Real) * δ ≤ taoZeroFreeBaseRadius U / 4 := by
    have hs := hscale U hUs
    dsimp [δ, L]
    rw [hP]
    exact hs
  have hleft : 1 - taoZeroFreeBaseRadius U / 4 ≤ α - R := by
    dsimp [α, R]
    linarith only [hsc]
  have hRpos : 0 < R := by dsimp [R]; positivity
  change ∀ γ : Real, 1 - δ ≤ γ → γ ≤ 1 + δ →
    taoZetaPoleRemoved ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0 ∧
    ‖logDeriv taoZetaPoleRemoved ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤ C * L ^ 2
  intro γ hlow hhigh
  have htarget : ((γ : Complex) + (t : Complex) * Complex.I) ∈
      ball ((α : Complex) + (t : Complex) * Complex.I) (R / 3) := by
    rw [mem_ball, Complex.dist_eq]
    have heq : ((γ : Complex) + (t : Complex) * Complex.I) -
        ((α : Complex) + (t : Complex) * Complex.I) = ((γ - α : Real) : Complex) := by
      push_cast
      ring
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_lt]
    dsimp [α, R]
    constructor <;> linarith only [hlow, hhigh, hδ]
  have hraw := norm_logDeriv_taoZetaPoleRemoved_le_high_disk
    (t := t) (α := α) (R := R) (U := U)
    (z := ((γ : Complex) + (t : Complex) * Complex.I))
    rfl hU4 hlogU hRpos hR1 hα hleft hright (fun V hV => hnear U V hUn hV) hHnz htarget
  have hnum := taoPNT_borel_numerator_le hd hUpos hPpos hlogU hUP hL1
  have hraw' : ‖logDeriv taoZetaPoleRemoved ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤
      24 * (taoPNTBorelConstant d * L) / R := by
    apply hraw.trans
    apply div_le_div_of_nonneg_right _ hRpos.le
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    simpa only [α, δ, L, add_sub_cancel_left] using hnum
  refine ⟨hHnz _ ((ball_subset_ball (by linarith : R / 3 ≤ R)) htarget), ?_⟩
  have heq : 24 * (taoPNTBorelConstant d * L) / R = C * L ^ 2 := by
    dsimp [R, δ, C]
    field_simp [hd.ne', hLpos.ne']
    <;> ring
  rwa [heq] at hraw'

end

end Erdos1212Kernel
