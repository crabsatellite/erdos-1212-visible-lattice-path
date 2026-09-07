import Erdos1212Kernel.TaoZetaCanonicalResidual

namespace Erdos1212Kernel

noncomputable section

open Filter Metric Topology

set_option maxHeartbeats 1900000

def taoCanonicalResidualConstant (a : Real) : Real :=
  3200 * (7 + 48 * Real.log 2 + 4 * Real.log (1 + 1 / a))

theorem taoCanonicalResidual_raw_le_linear
    {a η T R : Real} (ha : 0 < a)
    (hL : 1 < Real.log T) (hll : 1 ≤ Real.log (Real.log T))
    (hR : taoZeroFreeBaseRadius T / 8 < R)
    (hη : a / Real.log T ≤ η) :
    4 * (1 + Real.log ((2 : Real) ^ 48 * (Real.log T) ^ 2) +
      4 * Real.log (1 + 1 / η)) / R ≤
        taoCanonicalResidualConstant a * Real.log T := by
  let L : Real := Real.log T
  let l : Real := Real.log L
  let K : Real := 7 + 48 * Real.log 2 + 4 * Real.log (1 + 1 / a)
  have hLpos : 0 < L := by unfold L; linarith
  have hlpos : 0 < l := by unfold l; linarith
  have hapos : 0 < a := ha
  have hηpos : 0 < η := (div_pos ha hLpos).trans_le hη
  have hInv : 1 / η ≤ L / a := by
    calc
      1 / η ≤ 1 / (a / L) := one_div_le_one_div_of_le (div_pos ha hLpos) hη
      _ = L / a := by field_simp [ha.ne', hLpos.ne']
  have hCLog : Real.log ((2 : Real) ^ 48 * L ^ 2) =
      48 * Real.log 2 + 2 * l := by
    rw [Real.log_mul (pow_ne_zero 48 (by norm_num : (2 : Real) ≠ 0))
      (pow_ne_zero 2 hLpos.ne'), Real.log_pow, Real.log_pow]
    norm_num
    rfl
  have hlogArg : Real.log (1 + 1 / η) ≤ Real.log (1 + 1 / a) + l := by
    have hL1 : 1 ≤ L := by linarith
    have harg : 1 + 1 / η ≤ (1 + 1 / a) * L := by
      have haInv : 0 ≤ 1 / a := by positivity
      have hfirst : 1 + 1 / η ≤ 1 + L / a := add_le_add_right hInv 1
      apply hfirst.trans
      field_simp [ha.ne']
      nlinarith
    have hfacpos : 0 < 1 + 1 / a := by positivity
    calc
      Real.log (1 + 1 / η) ≤ Real.log ((1 + 1 / a) * L) :=
        Real.log_le_log (by positivity) harg
      _ = Real.log (1 + 1 / a) + l := by
        rw [Real.log_mul hfacpos.ne' hLpos.ne']
  have hKpos : 0 < K := by
    unfold K
    have hlog2 := Real.log_nonneg (by norm_num : (1 : Real) ≤ 2)
    have haInv : 0 ≤ 1 / a := by positivity
    have hloga := Real.log_nonneg (by linarith : (1 : Real) ≤ 1 + 1 / a)
    linarith
  have hM :
      1 + Real.log ((2 : Real) ^ 48 * L ^ 2) +
          4 * Real.log (1 + 1 / η) ≤ K * l := by
    rw [hCLog]
    have hconst0 : 0 ≤ 1 + 48 * Real.log 2 + 4 * Real.log (1 + 1 / a) := by
      have hlog2 := Real.log_nonneg (by norm_num : (1 : Real) ≤ 2)
      have haInv : 0 ≤ 1 / a := by positivity
      have hloga := Real.log_nonneg (by linarith : (1 : Real) ≤ 1 + 1 / a)
      linarith
    have hconst := mul_le_mul_of_nonneg_left hll hconst0
    change 1 + (48 * Real.log 2 + 2 * l) + 4 * Real.log (1 + 1 / η) ≤
      (7 + 48 * Real.log 2 + 4 * Real.log (1 + 1 / a)) * l
    nlinarith
  have hRlower : l / (800 * L) < R := by
    unfold taoZeroFreeBaseRadius at hR
    convert hR using 1 <;> ring
  have hfracpos : 0 < l / (800 * L) := by positivity
  have hRpos : 0 < R := hfracpos.trans hRlower
  apply (div_le_iff₀ hRpos).2
  have hcross' := (div_lt_iff₀ (by positivity : 0 < 800 * L)).mp hRlower
  have hcross : 800 * L * R > l := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hM (by norm_num : (0 : Real) ≤ 4)
  unfold taoCanonicalResidualConstant
  change 4 * (1 + Real.log ((2 : Real) ^ 48 * L ^ 2) +
      4 * Real.log (1 + 1 / η)) ≤ 3200 * K * L * R
  nlinarith [mul_pos hKpos (sub_pos.mpr hcross)]

theorem exists_taoCanonicalAdjustedResidual_common_shift
    (y η amin : Real) (hamin : 0 < amin)
    (hL : 1 < Real.log (taoLogFrequency y))
    (hll : 1 ≤ Real.log (Real.log (taoLogFrequency y)))
    (hqhalf : taoZeroFreeBaseRadius (taoLogFrequency y) / 4 ≤ 1 / 2)
    (hηhalf : η ≤ 1 / 2)
    (hqimag : taoZeroFreeBaseRadius (taoLogFrequency y) / 4 < |y|)
    (hηlower : amin / Real.log (taoLogFrequency y) ≤ η)
    (hnear : ∀ U ∈ Set.Icc (taoLogFrequency y - 1)
        (taoLogFrequency y + 1),
      TaoLittlewoodFinalFrequencyConditions U ∧
      4 ≤ U ∧ 1 ≤ Real.log U ∧
      taoZeroFreeBaseRadius (taoLogFrequency y) / 4 ≤
        taoLittlewoodWidth U (taoLittlewoodR U) ∧
      Real.log U ≤ 2 * Real.log (taoLogFrequency y)) :
    ∃ R : Real, ∃ G : Complex → Complex,
      R ∈ Set.Ioo (taoZeroFreeBaseRadius (taoLogFrequency y) / 8)
        (taoZeroFreeBaseRadius (taoLogFrequency y) / 4) ∧
      (∀ ρ : Complex, riemannZeta ρ = 0 →
        dist ρ (((1 + η : Real) : Complex) + (y : Complex) * Complex.I) ≠ R) ∧
      (∀ z ∈ closedBall
        (((1 + η : Real) : Complex) + (y : Complex) * Complex.I) R, G z ≠ 0) ∧
      taoZetaLogDerivative
          (((1 + η : Real) : Complex) + (y : Complex) * Complex.I) +
          taoZetaAdjustedReciprocalSum
            (((1 + η : Real) : Complex) + (y : Complex) * Complex.I) R =
        -logDeriv G (((1 + η : Real) : Complex) + (y : Complex) * Complex.I) ∧
      ‖logDeriv G (((1 + η : Real) : Complex) + (y : Complex) * Complex.I)‖ ≤
        taoCanonicalResidualConstant amin * Real.log (taoLogFrequency y) := by
  let L : Real := Real.log (taoLogFrequency y)
  let b : Real := η * L
  have hLpos : 0 < L := by unfold L; linarith
  have hηpos : 0 < η := (div_pos hamin hLpos).trans_le hηlower
  have hb : 0 < b := mul_pos hηpos hLpos
  have hbdiv : b / L = η := by unfold b; field_simp [hLpos.ne']
  have hshift : b / Real.log (taoLogFrequency y) = η := by
    simpa only [L] using hbdiv
  obtain ⟨R, G, hRmem, hSphere, _hG, hGnz, hexact, hraw⟩ :=
    exists_taoCanonicalAdjustedResidual_of_nearby_conditions b y hb hL hqhalf
      (by rw [hbdiv]; exact hηhalf) hqimag hnear
  have hscalar := taoCanonicalResidual_raw_le_linear hamin hL hll hRmem.1 hηlower
  refine ⟨R, G, hRmem, ?_, ?_, ?_, ?_⟩
  · simpa only [hshift] using hSphere
  · simpa only [hshift] using hGnz
  · simpa only [hshift] using hexact
  · have hraw' :
        ‖logDeriv G (((1 + η : Real) : Complex) + (y : Complex) * Complex.I)‖ ≤
          4 * (1 + Real.log
              ((2 : Real) ^ 48 * (Real.log (taoLogFrequency y)) ^ 2) +
            4 * Real.log (1 + 1 / η)) / R := by
      simpa only [hshift, add_sub_cancel_left] using hraw
    exact hraw'.trans hscalar

theorem exists_eventual_taoCanonicalAdjustedResidual_linear
    (a : Real) (ha : 0 < a) :
    ∃ Q T₀ : Real, Q = taoCanonicalResidualConstant a ∧ 0 < Q ∧ ∀ t : Real,
      T₀ ≤ taoLogFrequency t →
      ∃ R : Real, ∃ G : Complex → Complex,
        R ∈ Set.Ioo (taoZeroFreeBaseRadius (taoLogFrequency t) / 8)
          (taoZeroFreeBaseRadius (taoLogFrequency t) / 4) ∧
        (∀ ρ : Complex, riemannZeta ρ = 0 →
          dist ρ
            (((1 + a / Real.log (taoLogFrequency t) : Real) : Complex) +
              (t : Complex) * Complex.I) ≠ R) ∧
        (∀ z ∈ closedBall
          (((1 + a / Real.log (taoLogFrequency t) : Real) : Complex) +
            (t : Complex) * Complex.I) R, G z ≠ 0) ∧
        taoZetaLogDerivative
            (((1 + a / Real.log (taoLogFrequency t) : Real) : Complex) +
              (t : Complex) * Complex.I) +
            taoZetaAdjustedReciprocalSum
              (((1 + a / Real.log (taoLogFrequency t) : Real) : Complex) +
                (t : Complex) * Complex.I) R =
          -logDeriv G
            (((1 + a / Real.log (taoLogFrequency t) : Real) : Complex) +
              (t : Complex) * Complex.I) ∧
        ‖logDeriv G
            (((1 + a / Real.log (taoLogFrequency t) : Real) : Complex) +
              (t : Complex) * Complex.I)‖ ≤
          Q * Real.log (taoLogFrequency t) := by
  obtain ⟨Tnear, hnear⟩ := exists_taoNearbyFrequencyThreshold
  let K : Real := 7 + 48 * Real.log 2 + 4 * Real.log (1 + 1 / a)
  let Q : Real := taoCanonicalResidualConstant a
  have hKpos : 0 < K := by
    unfold K
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have haInv : 0 ≤ 1 / a := by positivity
    have hloga : 0 ≤ Real.log (1 + 1 / a) :=
      Real.log_nonneg (by linarith)
    linarith
  have hQpos : 0 < Q := by unfold Q taoCanonicalResidualConstant; positivity
  have hevent : ∀ᶠ T : Real in atTop,
      Tnear ≤ T ∧ 1 < Real.log T ∧
      1 ≤ Real.log (Real.log T) ∧
      2 * a ≤ Real.log T ∧ 1 ≤ T := by
    filter_upwards [eventually_ge_atTop Tnear,
      Real.tendsto_log_atTop.eventually_gt_atTop 1,
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1,
      Real.tendsto_log_atTop.eventually_ge_atTop (2 * a),
      eventually_ge_atTop 1] with T hTnear hL hll haL hT1
    exact ⟨hTnear, hL, hll, haL, hT1⟩
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨Q, T₀, rfl, hQpos, fun t ht => ?_⟩
  let T : Real := taoLogFrequency t
  let L : Real := Real.log T
  let l : Real := Real.log L
  obtain ⟨hTnear, hL, hll, haL, hT1⟩ := hT₀ T (by simpa only [T] using ht)
  have hTpos : 0 < T := by linarith
  have hLpos : 0 < L := by unfold L; linarith
  have hlpos : 0 < l := by unfold l; linarith
  have hlogLle : l ≤ L := by
    have h := Real.log_le_sub_one_of_pos hLpos
    dsimp only [l]
    linarith
  have hqsmall : taoZeroFreeBaseRadius T / 4 ≤ 1 / 400 := by
    unfold taoZeroFreeBaseRadius
    change l / (100 * L) / 4 ≤ 1 / 400
    rw [div_div]
    apply (div_le_div_iff₀ (by positivity : 0 < (100 * L) * 4)
      (by norm_num : (0 : Real) < 400)).2
    nlinarith
  have hqhalf : taoZeroFreeBaseRadius T / 4 ≤ 1 / 2 :=
    hqsmall.trans (by norm_num)
  have hahalf : a / L ≤ 1 / 2 := by
    apply (div_le_iff₀ hLpos).2
    nlinarith
  have habs : |t| = (2 * Real.pi) * T := by
    unfold T taoLogFrequency
    field_simp [Real.pi_ne_zero]
  have hqimag : taoZeroFreeBaseRadius T / 4 < |t| := by
    rw [habs]
    have hpi := Real.pi_gt_three
    nlinarith
  have hnearT : ∀ U ∈ Set.Icc (T - 1) (T + 1),
      TaoLittlewoodFinalFrequencyConditions U ∧
      4 ≤ U ∧ 1 ≤ Real.log U ∧
      taoZeroFreeBaseRadius T / 4 ≤
        taoLittlewoodWidth U (taoLittlewoodR U) ∧
      Real.log U ≤ 2 * Real.log T :=
    fun U hU => hnear T U hTnear hU
  obtain ⟨R, G, hRmem, hSphere, _hG, hGnz, hexact, hraw⟩ :=
    exists_taoCanonicalAdjustedResidual_of_nearby_conditions a t ha
      (by simpa only [T] using hL) (by simpa only [T] using hqhalf)
      (by simpa only [T, L] using hahalf) (by simpa only [T] using hqimag)
      (by simpa only [T] using hnearT)
  have hCLog : Real.log ((2 : Real) ^ 48 * L ^ 2) =
      48 * Real.log 2 + 2 * l := by
    rw [Real.log_mul (pow_ne_zero 48 (by norm_num : (2 : Real) ≠ 0))
      (pow_ne_zero 2 hLpos.ne'), Real.log_pow, Real.log_pow]
    norm_num
    rfl
  have hrecip : 1 / ((1 + a / L) - 1) = L / a := by
    field_simp [ha.ne', hLpos.ne']
    ring
  have hlogArg : Real.log (1 + L / a) ≤ Real.log (1 + 1 / a) + l := by
    have haInv : 0 ≤ 1 / a := by positivity
    have harg : 1 + L / a ≤ (1 + 1 / a) * L := by
      have hL1 : 1 ≤ L := by linarith
      field_simp [ha.ne']
      nlinarith
    have hfacpos : 0 < 1 + 1 / a := by positivity
    calc
      Real.log (1 + L / a) ≤ Real.log ((1 + 1 / a) * L) :=
        Real.log_le_log (by positivity) harg
      _ = Real.log (1 + 1 / a) + l := by
        rw [Real.log_mul hfacpos.ne' hLpos.ne']
  have hM :
      1 + Real.log ((2 : Real) ^ 48 * L ^ 2) +
          4 * Real.log (1 + 1 / ((1 + a / L) - 1)) ≤ K * l := by
    rw [hCLog, hrecip]
    have hconst : 1 + 48 * Real.log 2 + 4 * Real.log (1 + 1 / a) ≤
        (1 + 48 * Real.log 2 + 4 * Real.log (1 + 1 / a)) * l := by
      have hconst0 : 0 ≤ 1 + 48 * Real.log 2 + 4 * Real.log (1 + 1 / a) := by
        have hlog2 := Real.log_nonneg (by norm_num : (1 : Real) ≤ 2)
        have haInv : 0 ≤ 1 / a := by positivity
        have hloga := Real.log_nonneg (by linarith : (1 : Real) ≤ 1 + 1 / a)
        linarith
      have hmul := mul_le_mul_of_nonneg_left hll hconst0
      simpa only [mul_one] using hmul
    dsimp only [K]
    nlinarith
  have hRlower : l / (800 * L) < R := by
    have := hRmem.1
    unfold taoZeroFreeBaseRadius at this
    convert this using 1 <;> ring
  have hlinear :
      4 * (1 + Real.log ((2 : Real) ^ 48 * L ^ 2) +
        4 * Real.log (1 + 1 / ((1 + a / L) - 1))) / R ≤ Q * L := by
    have hfracpos : 0 < l / (800 * L) := by positivity
    have hRpos : 0 < R := hfracpos.trans hRlower
    apply (div_le_iff₀ hRpos).2
    have hcross' := (div_lt_iff₀ (by positivity : 0 < 800 * L)).mp hRlower
    have hcross : 800 * L * R > l := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hM (by norm_num : (0 : Real) ≤ 4)
    dsimp only [Q, taoCanonicalResidualConstant]
    have hKl : 0 < K * l := mul_pos hKpos hlpos
    nlinarith [mul_pos hKpos (sub_pos.mpr hcross)]
  refine ⟨R, G, ?_, hSphere, ?_, ?_, ?_⟩
  · simpa only [T] using hRmem
  · simpa only [T, L] using hGnz
  · simpa only [T, L] using hexact
  · have hlinear' :
        4 * (1 + Real.log
            ((2 : Real) ^ 48 * (Real.log (taoLogFrequency t)) ^ 2) +
          4 * Real.log
            (1 + 1 / ((1 + a / Real.log (taoLogFrequency t)) - 1))) / R ≤
          Q * Real.log (taoLogFrequency t) := by
      simpa only [T, L] using hlinear
    exact hraw.trans hlinear'

end

end Erdos1212Kernel
