import Erdos1212Kernel.TaoLittlewoodEulerAbsorption

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

/-- Fully explicit Littlewood bound for the canonical Riemann zeta
function. Every analytic, dyadic, cutoff, and scalar input is a proved
producer; the displayed hypotheses are only the eventual frequency
conditions and membership in the literal strip. -/
theorem riemannZeta_norm_le_littlewood_log_sq
    (t σ : Real)
    (hcond : TaoLittlewoodFrequencyConditions (taoLogFrequency t))
    (hwidth8 : taoLittlewoodWidth (taoLogFrequency t)
      (taoLittlewoodR (taoLogFrequency t)) ≤ (1 : Real) / 8)
    (hlogQuarter : Real.log (taoLogFrequency t) ≤
      (taoLogFrequency t) ^ (1 / 4 : Real))
    (hT2 : 2 ≤ taoLogFrequency t)
    (hσlower : 1 - taoLittlewoodWidth (taoLogFrequency t)
      (taoLittlewoodR (taoLogFrequency t)) ≤ σ)
    (hσupper : σ ≤ 1) :
    ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤
      (2 : Real) ^ 46 * (Real.log (taoLogFrequency t)) ^ 2 := by
  let T := taoLogFrequency t
  let J := taoLittlewoodJ T
  let R := taoLittlewoodR T
  let L := Real.log T
  have hT : 1 < T := hcond.1
  have hL : 1 < L := hcond.2.1
  have hdelta : 1 - σ ≤ (1 : Real) / 8 := by
    have : 1 - σ ≤ taoLittlewoodWidth T R := by
      dsimp only [T, R] at hσlower ⊢
      linarith
    exact this.trans (by simpa only [T, R] using hwidth8)
  have hσ : (7 : Real) / 8 ≤ σ :=
    taoLittlewood_strip_sigma_lower hwidth8 hσlower
  have hbase := riemannZeta_norm_le_littlewood_extended_canonical t σ
    hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2 hσlower hσupper
  let A : Real := (((2 ^ (2 * J) : Nat) : Real)) ^ (1 - σ) *
    Real.log (2 + T) / Real.sqrt T
  let B : Real := Real.sqrt T * (((2 ^ J : Nat) : Real)) ^ (-σ)
  let C : Real := (((2 ^ (2 * J) : Nat) : Real)) ^ (1 - σ) /
    ‖((σ : Complex) + (t : Complex) * Complex.I) - 1‖
  let D : Real := ‖(σ : Complex) + (t : Complex) * Complex.I‖ *
    (((2 ^ (2 * J) : Nat) : Real)) ^ (-σ) * (1 + 1 / σ)
  have hA : A ≤ 2 := by
    unfold A
    exact taoLittlewood_high_tail_first_le_two hT2 hσupper hdelta
      (by simpa only [T] using hlogQuarter)
  have hB : B ≤ 2 := by
    unfold B
    exact taoLittlewood_high_tail_second_le_two hT2 hσupper hdelta
  have hC : C ≤ 1 := by
    unfold C
    exact taoLittlewood_euler_correction_le_one hT2 hσupper hdelta
  have hD : D ≤ 128 := by
    unfold D
    exact taoLittlewood_euler_remainder_le_128 hT2 hσupper hdelta hσ
  have hJ : (J : Real) ≤ 2 * L := by
    dsimp only [J, L, T]
    exact taoLittlewoodJ_cast_le_two_log hT.le
  have hlog : Real.log (2 + T) ≤ 2 * L := by
    dsimp only [L]
    exact taoLittlewood_log_two_add_le_two_log hT2
  have hL0 : 0 ≤ L := by linarith
  have hJ0 : (0 : Real) ≤ J := by positivity
  have hlog0 : 0 ≤ Real.log (2 + T) := Real.log_nonneg (by linarith)
  have hmain : (J : Real) * (L + (2 : Real) ^ 42 * Real.log (2 + T)) ≤
      (2 : Real) ^ 45 * L ^ 2 := by
    have hbracket : L + (2 : Real) ^ 42 * Real.log (2 + T) ≤
        (1 + (2 : Real) ^ 43) * L := by
      calc
        _ ≤ L + (2 : Real) ^ 42 * (2 * L) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog
            (pow_nonneg (by norm_num : (0 : Real) ≤ 2) 42))
        _ = _ := by ring
    calc
      _ ≤ (2 * L) * ((1 + (2 : Real) ^ 43) * L) :=
        mul_le_mul hJ hbracket
          (add_nonneg hL0 (mul_nonneg (by positivity) hlog0))
          (mul_nonneg (by norm_num) hL0)
      _ = (2 * (1 + (2 : Real) ^ 43)) * L ^ 2 := by ring
      _ ≤ (2 : Real) ^ 45 * L ^ 2 :=
        mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg L)
  have htail : (J : Real) * ((2 : Real) ^ 20 * (A + B)) ≤
      (2 : Real) ^ 23 * L ^ 2 := by
    have hA0 : 0 ≤ A := by unfold A; positivity
    have hB0 : 0 ≤ B := by unfold B; positivity
    have hab : A + B ≤ 4 := by linarith
    have hLsq : L ≤ L ^ 2 := by nlinarith
    calc
      _ ≤ (2 * L) * ((2 : Real) ^ 20 * 4) :=
        mul_le_mul hJ (mul_le_mul_of_nonneg_left hab (by positivity))
          (mul_nonneg (by positivity) (add_nonneg hA0 hB0))
          (mul_nonneg (by norm_num) hL0)
      _ = (2 : Real) ^ 23 * L := by norm_num; ring
      _ ≤ (2 : Real) ^ 23 * L ^ 2 :=
        mul_le_mul_of_nonneg_left hLsq (by positivity)
  have hCL : C ≤ L ^ 2 := hC.trans (by nlinarith)
  have hDL : D ≤ 128 * L ^ 2 := hD.trans (by nlinarith [sq_nonneg L])
  have hbase' : ‖riemannZeta ((σ : Complex) + (t : Complex) * Complex.I)‖ ≤
      (J : Real) * (L + (2 : Real) ^ 42 * Real.log (2 + T)) +
        (J : Real) * ((2 : Real) ^ 20 * (A + B)) + C + D := by
    simpa only [T, J, R, L, A, B, C, D] using hbase
  apply hbase'.trans
  calc
    _ ≤ (2 : Real) ^ 45 * (Real.log (taoLogFrequency t)) ^ 2 +
        (2 : Real) ^ 23 * (Real.log (taoLogFrequency t)) ^ 2 +
        (Real.log (taoLogFrequency t)) ^ 2 +
        128 * (Real.log (taoLogFrequency t)) ^ 2 :=
      add_le_add (add_le_add (add_le_add hmain htail) hCL) hDL
    _ ≤ (2 : Real) ^ 46 * (Real.log (taoLogFrequency t)) ^ 2 := by
      have hsquare : 0 ≤ (Real.log (taoLogFrequency t)) ^ 2 := sq_nonneg _
      nlinarith

end

end Erdos1212Kernel
