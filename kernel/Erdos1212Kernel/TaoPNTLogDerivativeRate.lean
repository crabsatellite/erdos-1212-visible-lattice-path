import Erdos1212Kernel.TaoPNTLogDerivativeHigh

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 1900000

def taoPNTBorelConstant (d : Real) : Real :=
  200 + |Real.log d| + 400 / d

theorem taoPNT_borel_numerator_le
    {d U P : Real} (hd : 0 < d) (hU : 0 < U) (hP : 0 < P)
    (hlogU : 1 ≤ Real.log U) (hUP : U ≤ P)
    (hlogP : 1 ≤ Real.log P) :
    1 + Real.log ((2 : Real) ^ 52 * U * (Real.log U) ^ 2) -
        Real.log (d / Real.log P / 100) +
        4 * Real.log (1 + 1 / (d / Real.log P / 100)) ≤
      taoPNTBorelConstant d * Real.log P := by
  let LU : Real := Real.log U
  let LP : Real := Real.log P
  have hLU : 0 < LU := by dsimp [LU]; linarith
  have hLP : 0 < LP := by dsimp [LP]; linarith
  have hLULP : LU ≤ LP := by
    dsimp [LU, LP]
    exact Real.log_le_log hU hUP
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 2)
    norm_num at h
    exact h
  have hlogLU : Real.log LU ≤ LU := by
    have h := Real.log_le_sub_one_of_pos hLU
    linarith
  have hlogE :
      Real.log ((2 : Real) ^ 52 * U * LU ^ 2) ≤ 55 * LP := by
    rw [Real.log_mul
      (mul_ne_zero (pow_ne_zero 52 (by norm_num : (2 : Real) ≠ 0)) hU.ne')
      (pow_ne_zero 2 hLU.ne'),
      Real.log_mul (pow_ne_zero 52 (by norm_num : (2 : Real) ≠ 0)) hU.ne',
      Real.log_pow, Real.log_pow]
    norm_num
    nlinarith
  have hlog100 : Real.log 100 ≤ 100 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : Real) < 100)
    linarith
  have hlogLP : Real.log LP ≤ LP := by
    have h := Real.log_le_sub_one_of_pos hLP
    linarith
  have ha : d / LP / 100 = d / (100 * LP) := by ring
  have hloga : -Real.log (d / LP / 100) ≤
      |Real.log d| + 100 + LP := by
    rw [ha, Real.log_div hd.ne' (mul_ne_zero (by norm_num) hLP.ne'),
      Real.log_mul (by norm_num : (100 : Real) ≠ 0) hLP.ne']
    have habs : -Real.log d ≤ |Real.log d| := neg_le_abs _
    linarith
  have hainv : 1 / (d / LP / 100) = 100 * LP / d := by
    field_simp [hd.ne', hLP.ne']
  have hlogOne : Real.log (1 + 1 / (d / LP / 100)) ≤
      100 * LP / d := by
    have harg : 0 < 1 + 1 / (d / LP / 100) := by positivity
    have h := Real.log_le_sub_one_of_pos harg
    calc
      Real.log (1 + 1 / (d / LP / 100)) ≤
          1 / (d / LP / 100) := by
        simpa only [add_sub_cancel_left] using h
      _ = 100 * LP / d := hainv
  have hconst : 1 + |Real.log d| + 100 ≤
      (101 + |Real.log d|) * LP := by
    have habs0 : 0 ≤ |Real.log d| := abs_nonneg _
    nlinarith
  dsimp [taoPNTBorelConstant]
  dsimp [LU, LP] at hlogE hloga hlogOne hconst hLULP hLU hLP ⊢
  have hfour : 4 * Real.log (1 + 1 / (d / Real.log P / 100)) ≤
      4 * (100 * Real.log P / d) :=
    mul_le_mul_of_nonneg_left hlogOne (by norm_num)
  calc
    1 + Real.log ((2 : Real) ^ 52 * U * (Real.log U) ^ 2) -
          Real.log (d / Real.log P / 100) +
          4 * Real.log (1 + 1 / (d / Real.log P / 100)) ≤
        1 + 55 * Real.log P +
          (|Real.log d| + 100 + Real.log P) +
          4 * (100 * Real.log P / d) := by
      rw [sub_eq_add_neg]
      exact add_le_add (add_le_add (add_le_add le_rfl hlogE) hloga) hfour
    _ = (56 + 400 / d) * Real.log P +
          (1 + |Real.log d| + 100) := by
      field_simp [hd.ne']
      ring
    _ ≤ (56 + 400 / d) * Real.log P +
          (101 + |Real.log d|) * Real.log P :=
      add_le_add_right hconst _
    _ ≤ (200 + |Real.log d| + 400 / d) * Real.log P := by
      have hLP0 : 0 ≤ Real.log P := by linarith
      nlinarith

theorem exists_eventual_taoPNT_poleRemoved_logDerivative_log_sq :
    ∃ d C U₀ : Real, 0 < d ∧ 0 < C ∧
      ∀ t : Real,
        U₀ ≤ taoLogFrequency t →
        let L := Real.log (taoPNTFrequency t)
        let δ := d / L
        let β := 1 - δ
        ∀ γ : Real, β ≤ γ → γ ≤ 1 + δ →
          (‖logDeriv taoZetaPoleRemoved
              ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤
            C * L ^ 2) ∧
            riemannZeta ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0 := by
  obtain ⟨d, U₁, hd, hraw⟩ :=
    exists_eventual_taoPNT_poleRemoved_logDerivative_bound
  let C : Real := 6 * taoPNTBorelConstant d / d
  obtain ⟨Ul, hUl⟩ := Filter.eventually_atTop.1
    (Real.tendsto_log_atTop.eventually_ge_atTop 1)
  let U₀ : Real := max U₁ (max Ul 4)
  have hQpos : 0 < taoPNTBorelConstant d := by
    unfold taoPNTBorelConstant
    have habs := abs_nonneg (Real.log d)
    have hinv : 0 < 400 / d := div_pos (by norm_num) hd
    linarith
  have hC : 0 < C := div_pos (mul_pos (by norm_num) hQpos) hd
  refine ⟨d, C, U₀, hd, hC, ?_⟩
  intro t ht
  let U : Real := taoLogFrequency t
  let P : Real := taoPNTFrequency t
  let L : Real := Real.log P
  let δ : Real := d / L
  let α : Real := 1 + δ / 100
  let β : Real := 1 - δ
  let R : Real := 4 * δ
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
  have hnum := taoPNT_borel_numerator_le hd hUpos hPpos hlogU hUP hlogP
  have hrawt := hraw t hU1
  have hδ : 0 < δ := div_pos hd (by dsimp [L]; linarith)
  have hR : R = 4 * δ := rfl
  have hbound : 24 *
      (1 + Real.log ((2 : Real) ^ 52 * U * (Real.log U) ^ 2) -
        Real.log (α - 1) +
        4 * Real.log (1 + 1 / (α - 1))) / R ≤ C * L ^ 2 := by
    have hαsub : α - 1 = δ / 100 := by dsimp [α]; ring
    rw [hαsub]
    have hnum' : 1 + Real.log ((2 : Real) ^ 52 * U * (Real.log U) ^ 2) -
        Real.log (δ / 100) +
        4 * Real.log (1 + 1 / (δ / 100)) ≤
        taoPNTBorelConstant d * L := by
      simpa only [δ, L, U, P] using hnum
    have hRpos : 0 < R := by dsimp [R]; positivity
    calc
      24 * (1 + Real.log ((2 : Real) ^ 52 * U * (Real.log U) ^ 2) -
          Real.log (δ / 100) +
          4 * Real.log (1 + 1 / (δ / 100))) / R ≤
        24 * (taoPNTBorelConstant d * L) / R :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hnum' (by norm_num)) hRpos.le
      _ = C * L ^ 2 := by
        dsimp [C, R, δ]
        field_simp [hd.ne', (by dsimp [L]; linarith : L ≠ 0)]
        ring
  change ∀ γ : Real, β ≤ γ → γ ≤ 1 + δ →
    (‖logDeriv taoZetaPoleRemoved
        ((γ : Complex) + (t : Complex) * Complex.I)‖ ≤ C * L ^ 2) ∧
      riemannZeta ((γ : Complex) + (t : Complex) * Complex.I) ≠ 0
  intro γ hβγ hγ1
  have hrawγ := hrawt γ hβγ hγ1
  exact ⟨hrawγ.1.trans hbound, hrawγ.2⟩

end

end Erdos1212Kernel
