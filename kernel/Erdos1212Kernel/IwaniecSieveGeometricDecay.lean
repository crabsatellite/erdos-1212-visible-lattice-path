import Erdos1212Kernel.IwaniecSieveFunctionRegularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

set_option maxHeartbeats 1800000

def iwaniecBaseProfile (s : Real) : Real :=
  iwaniecGTwo s * s⁻¹ * Real.exp s

def iwaniecBaseProfileSet : Set Real :=
  iwaniecBaseProfile '' Set.Icc (2 : Real) 4

noncomputable def iwaniecBaseA : Real :=
  sSup iwaniecBaseProfileSet

theorem iwaniecBaseProfileSet_nonempty :
    iwaniecBaseProfileSet.Nonempty := by
  exact ⟨iwaniecBaseProfile 2, 2, ⟨by norm_num, by norm_num⟩, rfl⟩

theorem iwaniecBaseProfile_nonneg
    {s : Real} (hs : s ∈ Set.Icc (2 : Real) 4) :
    0 ≤ iwaniecBaseProfile s := by
  unfold iwaniecBaseProfile
  exact mul_nonneg
    (mul_nonneg (iwaniecGTwo_nonneg hs.1 hs.2) (inv_nonneg.mpr (by linarith [hs.1])))
    (le_of_lt (Real.exp_pos s))

theorem iwaniecBaseProfile_le_explicit
    {s : Real} (hs : s ∈ Set.Icc (2 : Real) 4) :
    iwaniecBaseProfile s ≤
      (3 * Real.log 3) * (2 : Real)⁻¹ * Real.exp 4 := by
  unfold iwaniecBaseProfile
  have hgLower := iwaniecGTwo_nonneg hs.1 hs.2
  have hgUpper := iwaniecGTwo_le_three_mul_log_three hs.1
  have hsPos : (0 : Real) < s := by linarith [hs.1]
  have hinv : s⁻¹ ≤ (2 : Real)⁻¹ :=
    (inv_le_inv₀ hsPos (by norm_num)).2 hs.1
  have hlog : 0 ≤ (3 : Real) * Real.log 3 :=
    mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  have hexp := Real.exp_le_exp.mpr hs.2
  calc
    iwaniecGTwo s * s⁻¹ * Real.exp s ≤
        (3 * Real.log 3) * s⁻¹ * Real.exp s := by
      gcongr
    _ ≤ (3 * Real.log 3) * (2 : Real)⁻¹ * Real.exp s := by
      gcongr
    _ ≤ (3 * Real.log 3) * (2 : Real)⁻¹ * Real.exp 4 := by
      gcongr

theorem iwaniecBaseProfileSet_bddAbove :
    BddAbove iwaniecBaseProfileSet := by
  refine ⟨(3 * Real.log 3) * (2 : Real)⁻¹ * Real.exp 4, ?_⟩
  intro value hvalue
  obtain ⟨s, hs, rfl⟩ := hvalue
  exact iwaniecBaseProfile_le_explicit hs

theorem iwaniecBaseProfile_le_baseA
    {s : Real} (hs : s ∈ Set.Icc (2 : Real) 4) :
    iwaniecBaseProfile s ≤ iwaniecBaseA := by
  unfold iwaniecBaseA
  exact le_csSup iwaniecBaseProfileSet_bddAbove ⟨s, hs, rfl⟩

theorem iwaniecBaseA_nonneg : 0 ≤ iwaniecBaseA := by
  have hle := iwaniecBaseProfile_le_baseA
    (s := (2 : Real)) ⟨by norm_num, by norm_num⟩
  exact (iwaniecBaseProfile_nonneg
    (s := (2 : Real)) ⟨by norm_num, by norm_num⟩).trans hle

/-- The defining base inequality for `a` in Iwaniec 1971, Lemma 4. -/
theorem iwaniecGTwo_le_baseA_mul
    {s : Real} (hlower : 2 ≤ s) :
    iwaniecGTwo s ≤ iwaniecBaseA * s * Real.exp (-s) := by
  by_cases hupper : s ≤ 4
  · have hprofile := iwaniecBaseProfile_le_baseA
      (s := s) ⟨hlower, hupper⟩
    have hscale : 0 ≤ s * Real.exp (-s) := by positivity
    have hscaled := mul_le_mul_of_nonneg_right hprofile hscale
    have hs : s ≠ 0 := by linarith
    have hexp : Real.exp s * Real.exp (-s) = 1 := by
      rw [← Real.exp_add]
      simp
    unfold iwaniecBaseProfile at hscaled
    calc
      iwaniecGTwo s =
          (iwaniecGTwo s * s⁻¹ * Real.exp s) *
            (s * Real.exp (-s)) := by
        symm
        calc
          (iwaniecGTwo s * s⁻¹ * Real.exp s) *
              (s * Real.exp (-s)) =
            iwaniecGTwo s * (s⁻¹ * s) *
              (Real.exp s * Real.exp (-s)) := by ring
          _ = iwaniecGTwo s := by
            rw [inv_mul_cancel₀ hs, hexp]
            ring
      _ ≤ iwaniecBaseA * (s * Real.exp (-s)) := hscaled
      _ = _ := by ring
  · rw [iwaniecGTwo_eq_zero_of_four_le (by linarith)]
    exact mul_nonneg
      (mul_nonneg iwaniecBaseA_nonneg (by linarith))
      (le_of_lt (Real.exp_pos _))

theorem intervalIntegral_exp_one_sub
    {a b : Real} :
    (∫ t in a..b, Real.exp (1 - t)) =
      Real.exp (1 - a) - Real.exp (1 - b) := by
  let primitive := fun t : Real => -Real.exp (1 - t)
  have hderiv : ∀ t : Real,
      HasDerivAt primitive (Real.exp (1 - t)) t := by
    intro t
    dsimp [primitive]
    have h := ((hasDerivAt_const t (1 : Real)).sub (hasDerivAt_id t)).exp.neg
    simp only [Pi.sub_apply, id_eq] at h
    convert h using 1 <;> ring
  have hint : IntervalIntegrable (fun t : Real => Real.exp (1 - t)) volume a b :=
    (by fun_prop : Continuous fun t : Real => Real.exp (1 - t)).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ht => hderiv t) hint]
  dsimp [primitive]
  ring

theorem intervalIntegral_exp_one_sub_le
    {a b : Real} (hab : a ≤ b) :
    (∫ t in a..b, Real.exp (1 - t)) ≤ Real.exp (1 - a) := by
  rw [intervalIntegral_exp_one_sub]
  exact sub_le_self _ (le_of_lt (Real.exp_pos _))

theorem intervalIntegral_one_div_sub_one
    {s : Real} (hlower : 1 < s) (hupper : s ≤ 4) :
    (∫ t in s..(4 : Real), (1 : Real) / (t - 1)) =
      Real.log (3 / (s - 1)) := by
  let primitive := fun t : Real => Real.log (t - 1)
  have hderiv : ∀ t ∈ Set.uIcc s (4 : Real),
      HasDerivAt primitive ((1 : Real) / (t - 1)) t := by
    intro t ht
    have htBounds : t ∈ Set.Icc s (4 : Real) := by
      simpa [Set.uIcc_of_le hupper] using ht
    have htNe : t - 1 ≠ 0 := by linarith [htBounds.1]
    dsimp [primitive]
    simpa [one_div] using ((hasDerivAt_id t).sub_const 1).log htNe
  have hint : IntervalIntegrable (fun t : Real => (1 : Real) / (t - 1))
      volume s 4 := by
    have hcont : ContinuousOn (fun t : Real => (1 : Real) / (t - 1))
        (Set.Icc s (4 : Real)) := by
      have hsub : ContinuousOn (fun t : Real => t - 1)
          (Set.Icc s (4 : Real)) := by fun_prop
      apply continuousOn_const.div hsub
      intro t ht
      linarith [ht.1]
    have hc : ContinuousOn (fun t : Real => (1 : Real) / (t - 1))
        (Set.uIcc s (4 : Real)) := by
      rw [Set.uIcc_of_le hupper]
      exact hcont
    exact hc.intervalIntegrable
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  dsimp [primitive]
  rw [show (4 : Real) - 1 = 3 by norm_num, ← Real.log_div
    (by norm_num : (3 : Real) ≠ 0) (by linarith : s - 1 ≠ 0)]

theorem iwaniecGEven_succ_decompose_at_four
    (n : Nat) {s : Real} (hlower : 2 ≤ s) (hupper : s ≤ 4) :
    iwaniecGEven (n + 1) s =
      iwaniecGEven (n + 1) 4 +
        iwaniecGOdd n 3 * Real.log (3 / (s - 1)) := by
  let upper : Real := 6 + 2 * n
  let actual := fun t : Real => iwaniecGOdd n (t - 1) / (t - 1)
  have hn : (0 : Real) ≤ n := by positivity
  have hfourUpper : (4 : Real) ≤ upper := by
    dsimp [upper]
    linarith
  have hsUpper : s ≤ upper := hupper.trans hfourUpper
  have hactualCont : ContinuousOn actual (Set.Icc s upper) := by
    have hodd := (iwaniecGEven_GOdd_continuousOn n).2
    have hshift : ContinuousOn (fun t : Real => iwaniecGOdd n (t - 1))
        (Set.Icc s upper) := by
      have hsub : ContinuousOn (fun t : Real => t - 1)
          (Set.Icc s upper) := by fun_prop
      apply hodd.comp hsub
      intro t ht
      change t - 1 ∈ Set.Icc (1 : Real) (5 + 2 * n)
      constructor
      · linarith [ht.1]
      · dsimp [upper] at ht ⊢
        linarith [ht.2]
    dsimp [actual]
    have hsub : ContinuousOn (fun t : Real => t - 1)
        (Set.Icc s upper) := by fun_prop
    apply hshift.div hsub
    intro t ht
    change t - 1 ≠ 0
    linarith [ht.1]
  have hsplit : (∫ t in s..upper, actual t) =
      (∫ t in s..(4 : Real), actual t) + ∫ t in (4 : Real)..upper, actual t := by
    have hsFourInt : IntervalIntegrable actual volume s 4 := by
      have hc : ContinuousOn actual (Set.uIcc s (4 : Real)) := by
        rw [Set.uIcc_of_le hupper]
        apply hactualCont.mono
        intro t ht
        exact ⟨ht.1, ht.2.trans hfourUpper⟩
      exact hc.intervalIntegrable
    have hFourUpperInt : IntervalIntegrable actual volume 4 upper := by
      have hc : ContinuousOn actual (Set.uIcc (4 : Real) upper) := by
        rw [Set.uIcc_of_le hfourUpper]
        apply hactualCont.mono
        intro t ht
        exact ⟨hupper.trans ht.1, ht.2⟩
      exact hc.intervalIntegrable
    exact (intervalIntegral.integral_add_adjacent_intervals
      hsFourInt hFourUpperInt).symm
  have hconstant : (∫ t in s..(4 : Real), actual t) =
      iwaniecGOdd n 3 * Real.log (3 / (s - 1)) := by
    calc
      (∫ t in s..(4 : Real), actual t) =
          ∫ t in s..(4 : Real), iwaniecGOdd n 3 * ((1 : Real) / (t - 1)) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htBounds : t ∈ Set.Icc s (4 : Real) := by
          simpa [Set.uIcc_of_le hupper] using ht
        have hoddConst := iwaniecGOdd_of_le_three n (s := t - 1) (by
          linarith [htBounds.2])
        dsimp [actual]
        rw [hoddConst]
        ring
      _ = iwaniecGOdd n 3 *
          (∫ t in s..(4 : Real), (1 : Real) / (t - 1)) := by
        rw [intervalIntegral.integral_const_mul]
      _ = _ := by rw [intervalIntegral_one_div_sub_one (by linarith) hupper]
  rw [iwaniecGEven_succ n hsUpper, iwaniecGEven_succ n hfourUpper]
  dsimp [upper, actual] at hsplit hconstant ⊢
  linarith

theorem three_le_mul_exp_three_sub
    {s : Real} (hlower : 1 ≤ s) (hupper : s ≤ 3) :
    3 ≤ s * Real.exp (3 - s) := by
  have hsPos : 0 < s := by linarith
  have hxPos : 0 < (3 : Real) / s := div_pos (by norm_num) hsPos
  have hlogUpper := Real.log_le_sub_one_of_pos hxPos
  have hratio : (3 : Real) / s - 1 ≤ 3 - s := by
    field_simp [hsPos.ne']
    nlinarith
  have hlog : Real.log ((3 : Real) / s) ≤ 3 - s := hlogUpper.trans hratio
  have hexp : (3 : Real) / s ≤ Real.exp (3 - s) := by
    rw [← Real.exp_log hxPos]
    exact Real.exp_le_exp.mpr hlog
  have hscaled := mul_le_mul_of_nonneg_left hexp (le_of_lt hsPos)
  field_simp [hsPos.ne'] at hscaled
  nlinarith

theorem iwaniecGOdd_integral_le_of_even_bound
    (n : Nat) {C s : Real} (hC : 0 ≤ C) (hs : 3 ≤ s)
    (hbound : ∀ u : Real, 2 ≤ u →
      iwaniecGEven n u ≤ C * u * Real.exp (-u)) :
    iwaniecGOdd n s ≤ C * Real.exp (1 - s) := by
  by_cases hupper : s ≤ 5 + 2 * (n : Real)
  ·
    let upper : Real := 5 + 2 * n
    let actual := fun t : Real => iwaniecGEven n (t - 1) / (t - 1)
    let majorant := fun t : Real => C * Real.exp (1 - t)
    have hactualCont : ContinuousOn actual (Set.Icc s upper) := by
      have heven := (iwaniecGEven_GOdd_continuousOn n).1
      have hshift : ContinuousOn (fun t : Real => iwaniecGEven n (t - 1))
          (Set.Icc s upper) := by
        have hsub : ContinuousOn (fun t : Real => t - 1)
            (Set.Icc s upper) := by fun_prop
        apply heven.comp hsub
        intro t ht
        change t - 1 ∈ Set.Icc (2 : Real) (4 + 2 * n)
        constructor
        · linarith [ht.1]
        · dsimp [upper] at ht ⊢
          linarith [ht.2]
      dsimp [actual]
      have hsub : ContinuousOn (fun t : Real => t - 1)
          (Set.Icc s upper) := by fun_prop
      apply hshift.div hsub
      intro t ht
      change t - 1 ≠ 0
      linarith [ht.1]
    have hmajorantCont : ContinuousOn majorant (Set.Icc s upper) := by
      dsimp [majorant]
      fun_prop
    have hmono :
        (∫ t in s..upper, actual t) ≤ ∫ t in s..upper, majorant t := by
      have hactualInt : IntervalIntegrable actual volume s upper := by
        have hc : ContinuousOn actual (Set.uIcc s upper) := by
          rw [Set.uIcc_of_le hupper]
          exact hactualCont
        exact hc.intervalIntegrable
      have hmajorantInt : IntervalIntegrable majorant volume s upper := by
        have hc : ContinuousOn majorant (Set.uIcc s upper) := by
          rw [Set.uIcc_of_le hupper]
          exact hmajorantCont
        exact hc.intervalIntegrable
      apply intervalIntegral.integral_mono_on hupper
        hactualInt hmajorantInt
      intro t ht
      have htPos : 0 < t - 1 := by linarith [ht.1]
      have hpoint := hbound (t - 1) (by linarith [ht.1])
      dsimp [actual, majorant]
      apply (div_le_iff₀ htPos).2
      have hexpEq : Real.exp (-(t - 1)) = Real.exp (1 - t) := by ring_nf
      rw [hexpEq] at hpoint
      nlinarith
    calc
      iwaniecGOdd n s = ∫ t in s..upper, actual t := by
        simpa [upper, actual] using iwaniecGOdd_of_three_le n hs hupper
      _ ≤ ∫ t in s..upper, majorant t := hmono
      _ = C * (∫ t in s..upper, Real.exp (1 - t)) := by
        dsimp [majorant]
        rw [intervalIntegral.integral_const_mul]
      _ ≤ C * Real.exp (1 - s) := by
        gcongr
        exact intervalIntegral_exp_one_sub_le hupper
  · rw [iwaniecGOdd_eq_zero n (le_of_not_ge hupper)]
    positivity

theorem iwaniecGOdd_le_of_even_geometricBound
    (n : Nat) {C s : Real} (hC : 0 ≤ C) (hs : 1 ≤ s)
    (hbound : ∀ u : Real, 2 ≤ u →
      iwaniecGEven n u ≤ C * u * Real.exp (-u)) :
    iwaniecGOdd n s ≤
      Real.exp 1 / 3 * C * s * Real.exp (-s) := by
  by_cases hthree : s ≤ 3
  · rw [iwaniecGOdd_of_le_three n hthree]
    have hthreeBound := iwaniecGOdd_integral_le_of_even_bound
      n hC (s := (3 : Real)) (by norm_num) hbound
    have hshape := three_le_mul_exp_three_sub hs hthree
    have htargetShape : Real.exp (1 - (3 : Real)) ≤
        Real.exp 1 / 3 * s * Real.exp (-s) := by
      let scale := Real.exp (-2) / 3
      have hscale : 0 ≤ scale := by dsimp [scale]; positivity
      have hscaled := mul_le_mul_of_nonneg_left hshape hscale
      have hprodLeft : scale * 3 = Real.exp (1 - (3 : Real)) := by
        dsimp [scale]
        ring
      have hprodOne : Real.exp (-2) * Real.exp (3 - s) =
          Real.exp (1 - s) := by
        rw [← Real.exp_add]
        congr 1 <;> ring
      have hprodTwo : Real.exp 1 * Real.exp (-s) =
          Real.exp (1 - s) := by
        rw [← Real.exp_add]
        congr 1 <;> ring
      calc
        Real.exp (1 - (3 : Real)) = scale * 3 := hprodLeft.symm
        _ ≤ scale * (s * Real.exp (3 - s)) := hscaled
        _ = Real.exp 1 / 3 * s * Real.exp (-s) := by
          calc
            scale * (s * Real.exp (3 - s)) =
                s / 3 * (Real.exp (-2) * Real.exp (3 - s)) := by
              dsimp [scale]
              ring
            _ = s / 3 * Real.exp (1 - s) := by rw [hprodOne]
            _ = s / 3 * (Real.exp 1 * Real.exp (-s)) := by rw [hprodTwo]
            _ = _ := by ring
    have hscaled := mul_le_mul_of_nonneg_left htargetShape hC
    calc
      iwaniecGOdd n 3 ≤ C * Real.exp (1 - (3 : Real)) := hthreeBound
      _ ≤ C * (Real.exp 1 / 3 * s * Real.exp (-s)) := hscaled
      _ = _ := by ring
  · have hfirst := iwaniecGOdd_integral_le_of_even_bound n hC
      (le_of_not_ge hthree) hbound
    have hsThree : 3 ≤ s := le_of_not_ge hthree
    have hcoeff : Real.exp 1 ≤ Real.exp 1 / 3 * s := by
      have he : 0 < Real.exp 1 := Real.exp_pos _
      nlinarith
    have hexpOne : Real.exp (1 - s) = Real.exp 1 * Real.exp (-s) := by
      rw [← Real.exp_add]
      congr 1 <;> ring
    have hshape : Real.exp (1 - s) ≤
        Real.exp 1 / 3 * s * Real.exp (-s) := by
      rw [hexpOne]
      exact mul_le_mul_of_nonneg_right hcoeff (le_of_lt (Real.exp_pos _))
    have hscaled := mul_le_mul_of_nonneg_left hshape hC
    calc
      iwaniecGOdd n s ≤ C * Real.exp (1 - s) := hfirst
      _ ≤ C * (Real.exp 1 / 3 * s * Real.exp (-s)) := hscaled
      _ = _ := by ring

theorem iwaniecGEven_succ_integral_le_of_odd_bound
    (n : Nat) {D s : Real} (hD : 0 ≤ D) (hs : 2 ≤ s)
    (hbound : ∀ u : Real, 1 ≤ u →
      iwaniecGOdd n u ≤ D * u * Real.exp (-u)) :
    iwaniecGEven (n + 1) s ≤ D * Real.exp (1 - s) := by
  by_cases hupper : s ≤ 6 + 2 * (n : Real)
  · let upper : Real := 6 + 2 * n
    let actual := fun t : Real => iwaniecGOdd n (t - 1) / (t - 1)
    let majorant := fun t : Real => D * Real.exp (1 - t)
    have hactualCont : ContinuousOn actual (Set.Icc s upper) := by
      have hodd := (iwaniecGEven_GOdd_continuousOn n).2
      have hshift : ContinuousOn (fun t : Real => iwaniecGOdd n (t - 1))
          (Set.Icc s upper) := by
        have hsub : ContinuousOn (fun t : Real => t - 1)
            (Set.Icc s upper) := by fun_prop
        apply hodd.comp hsub
        intro t ht
        change t - 1 ∈ Set.Icc (1 : Real) (5 + 2 * n)
        constructor
        · linarith [ht.1]
        · dsimp [upper] at ht ⊢
          linarith [ht.2]
      dsimp [actual]
      have hsub : ContinuousOn (fun t : Real => t - 1)
          (Set.Icc s upper) := by fun_prop
      apply hshift.div hsub
      intro t ht
      change t - 1 ≠ 0
      linarith [ht.1]
    have hmajorantCont : ContinuousOn majorant (Set.Icc s upper) := by
      dsimp [majorant]
      fun_prop
    have hmono :
        (∫ t in s..upper, actual t) ≤ ∫ t in s..upper, majorant t := by
      have hactualInt : IntervalIntegrable actual volume s upper := by
        have hc : ContinuousOn actual (Set.uIcc s upper) := by
          rw [Set.uIcc_of_le hupper]
          exact hactualCont
        exact hc.intervalIntegrable
      have hmajorantInt : IntervalIntegrable majorant volume s upper := by
        have hc : ContinuousOn majorant (Set.uIcc s upper) := by
          rw [Set.uIcc_of_le hupper]
          exact hmajorantCont
        exact hc.intervalIntegrable
      apply intervalIntegral.integral_mono_on hupper hactualInt hmajorantInt
      intro t ht
      have htPos : 0 < t - 1 := by linarith [ht.1]
      have hpoint := hbound (t - 1) (by linarith [ht.1])
      dsimp [actual, majorant]
      apply (div_le_iff₀ htPos).2
      have hexpEq : Real.exp (-(t - 1)) = Real.exp (1 - t) := by ring_nf
      rw [hexpEq] at hpoint
      nlinarith
    calc
      iwaniecGEven (n + 1) s = ∫ t in s..upper, actual t := by
        simpa [upper, actual] using iwaniecGEven_succ n hupper
      _ ≤ ∫ t in s..upper, majorant t := hmono
      _ = D * (∫ t in s..upper, Real.exp (1 - t)) := by
        dsimp [majorant]
        rw [intervalIntegral.integral_const_mul]
      _ ≤ D * Real.exp (1 - s) := by
        gcongr
        exact intervalIntegral_exp_one_sub_le hupper
  · rw [iwaniecGEven_succ_eq_zero n (le_of_not_ge hupper)]
    positivity

theorem iwaniecGEven_succ_high_geometricBound
    (n : Nat) {C s : Real} (hC : 0 ≤ C) (hs : 4 ≤ s)
    (hbound : ∀ u : Real, 1 ≤ u →
      iwaniecGOdd n u ≤ Real.exp 1 / 3 * C * u * Real.exp (-u)) :
    iwaniecGEven (n + 1) s ≤
      C * iwaniecContractionA * s * Real.exp (-s) := by
  let D := Real.exp 1 / 3 * C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hfirst := iwaniecGEven_succ_integral_le_of_odd_bound
    n hD (s := s) (by linarith) (by simpa [D] using hbound)
  have hexpOne : Real.exp (1 - s) = Real.exp 1 * Real.exp (-s) := by
    rw [← Real.exp_add]
    congr 1 <;> ring
  have hnumeric : Real.exp 1 ^ 2 / 3 ≤ iwaniecContractionA * s := by
    have hA := (exp_one_sq_div_twelve_lt_iwaniecContractionA).le
    calc
      Real.exp 1 ^ 2 / 3 = 4 * (Real.exp 1 ^ 2 / 12) := by ring
      _ ≤ 4 * iwaniecContractionA :=
        mul_le_mul_of_nonneg_left hA (by norm_num)
      _ ≤ iwaniecContractionA * s := by
        nlinarith [mul_le_mul_of_nonneg_left hs iwaniecContractionA_nonneg]
  have hshape : D * Real.exp (1 - s) ≤
      C * iwaniecContractionA * s * Real.exp (-s) := by
    dsimp [D]
    rw [hexpOne]
    have hscaled := mul_le_mul_of_nonneg_right hnumeric
      (mul_nonneg hC (le_of_lt (Real.exp_pos (-s))))
    calc
      Real.exp 1 / 3 * C * (Real.exp 1 * Real.exp (-s)) =
          (C * Real.exp (-s)) * (Real.exp 1 ^ 2 / 3) := by ring
      _ ≤ (C * Real.exp (-s)) * (iwaniecContractionA * s) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
      _ = C * iwaniecContractionA * s * Real.exp (-s) := by ring
  exact hfirst.trans hshape

theorem iwaniecGEven_succ_low_geometricBound
    (n : Nat) {C s : Real} (hC : 0 ≤ C)
    (hlower : 2 ≤ s) (hupper : s ≤ 4)
    (hbound : ∀ u : Real, 1 ≤ u →
      iwaniecGOdd n u ≤ Real.exp 1 / 3 * C * u * Real.exp (-u)) :
    iwaniecGEven (n + 1) s ≤
      C * iwaniecContractionA * s * Real.exp (-s) := by
  let D := Real.exp 1 / 3 * C
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hfour := iwaniecGEven_succ_integral_le_of_odd_bound
    n hD (s := (4 : Real)) (by norm_num) (by simpa [D] using hbound)
  have hthree := hbound (3 : Real) (by norm_num)
  have hratio : 1 ≤ (3 : Real) / (s - 1) := by
    have hden : 0 < s - 1 := by linarith
    rw [le_div_iff₀ hden]
    linarith
  have hlogNonneg : 0 ≤ Real.log (3 / (s - 1)) := Real.log_nonneg hratio
  have hthreeScaled := mul_le_mul_of_nonneg_right hthree hlogNonneg
  have hdecomp := iwaniecGEven_succ_decompose_at_four n hlower hupper
  have hcoarse : iwaniecGEven (n + 1) s ≤
      D * Real.exp (-3) *
        (1 + 3 * Real.log (3 / (s - 1))) := by
    rw [show (1 : Real) - 4 = -3 by norm_num] at hfour
    calc
      iwaniecGEven (n + 1) s =
          iwaniecGEven (n + 1) 4 +
            iwaniecGOdd n 3 * Real.log (3 / (s - 1)) := hdecomp
      _ ≤ D * Real.exp (-3) +
          (Real.exp 1 / 3 * C * 3 * Real.exp (-3)) *
            Real.log (3 / (s - 1)) :=
        add_le_add hfour hthreeScaled
      _ = D * Real.exp (-3) *
          (1 + 3 * Real.log (3 / (s - 1))) := by
        dsimp [D]
        ring
  have hpsi := iwaniecPsi_le_two hlower hupper
  have hpsiScaled := mul_le_mul_of_nonneg_left hpsi
    (by positivity : 0 ≤ Real.exp 1 / 3)
  have hpsiA : Real.exp 1 / 3 * iwaniecPsi s ≤ iwaniecContractionA := by
    simpa [iwaniecContractionA] using hpsiScaled
  have hscale : 0 ≤ C * s * Real.exp (-s) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hpsiA hscale
  have hsNe : s ≠ 0 := by linarith
  have hexp : Real.exp (s - 3) * Real.exp (-s) = Real.exp (-3) := by
    rw [← Real.exp_add]
    congr 1 <;> ring
  have hidentity : D * Real.exp (-3) *
        (1 + 3 * Real.log (3 / (s - 1))) =
      (Real.exp 1 / 3 * iwaniecPsi s) *
        (C * s * Real.exp (-s)) := by
    dsimp [D, iwaniecPsi]
    field_simp [hsNe]
    rw [mul_assoc C, hexp]
  calc
    iwaniecGEven (n + 1) s ≤ D * Real.exp (-3) *
        (1 + 3 * Real.log (3 / (s - 1))) := hcoarse
    _ = (Real.exp 1 / 3 * iwaniecPsi s) *
        (C * s * Real.exp (-s)) := hidentity
    _ ≤ iwaniecContractionA * (C * s * Real.exp (-s)) := hscaled
    _ = _ := by ring

theorem iwaniecGEven_succ_geometricBound
    (n : Nat) {C s : Real} (hC : 0 ≤ C) (hs : 2 ≤ s)
    (hbound : ∀ u : Real, 1 ≤ u →
      iwaniecGOdd n u ≤ Real.exp 1 / 3 * C * u * Real.exp (-u)) :
    iwaniecGEven (n + 1) s ≤
      C * iwaniecContractionA * s * Real.exp (-s) := by
  by_cases hupper : s ≤ 4
  · exact iwaniecGEven_succ_low_geometricBound n hC hs hupper hbound
  · exact iwaniecGEven_succ_high_geometricBound n hC
      (le_of_not_ge hupper) hbound

/-- Iwaniec 1971, Lemma 4, equations (3.4)--(3.5). -/
theorem iwaniecGEven_GOdd_geometricBound (n : Nat) :
    (∀ s : Real, 2 ≤ s →
      iwaniecGEven n s ≤
        iwaniecBaseA * iwaniecContractionA ^ n * s * Real.exp (-s)) ∧
    (∀ s : Real, 1 ≤ s →
      iwaniecGOdd n s ≤
        Real.exp 1 / 3 * iwaniecBaseA *
          iwaniecContractionA ^ n * s * Real.exp (-s)) := by
  induction n with
  | zero =>
      have heven : ∀ s : Real, 2 ≤ s →
          iwaniecGEven 0 s ≤
            iwaniecBaseA * iwaniecContractionA ^ 0 * s * Real.exp (-s) := by
        intro s hs
        rw [iwaniecGEven_zero]
        simpa using iwaniecGTwo_le_baseA_mul hs
      have hodd : ∀ s : Real, 1 ≤ s →
          iwaniecGOdd 0 s ≤ Real.exp 1 / 3 * iwaniecBaseA *
            iwaniecContractionA ^ 0 * s * Real.exp (-s) := by
        intro s hs
        have hraw := iwaniecGOdd_le_of_even_geometricBound
          0 iwaniecBaseA_nonneg hs (fun u hu => by simpa using heven u hu)
        simpa [mul_assoc] using hraw
      exact ⟨heven, hodd⟩
  | succ n ih =>
      let C := iwaniecBaseA * iwaniecContractionA ^ n
      have hC : 0 ≤ C := mul_nonneg iwaniecBaseA_nonneg
        (pow_nonneg iwaniecContractionA_nonneg _)
      have heven : ∀ s : Real, 2 ≤ s →
          iwaniecGEven (n + 1) s ≤
            iwaniecBaseA * iwaniecContractionA ^ (n + 1) *
              s * Real.exp (-s) := by
        intro s hs
        have hraw := iwaniecGEven_succ_geometricBound n hC hs
          (fun u hu => by simpa [C, mul_assoc] using ih.2 u hu)
        simpa [C, pow_succ, mul_assoc] using hraw
      have CnextNonneg :
          0 ≤ iwaniecBaseA * iwaniecContractionA ^ (n + 1) :=
        mul_nonneg iwaniecBaseA_nonneg
          (pow_nonneg iwaniecContractionA_nonneg _)
      exact ⟨heven, by
        intro s hs
        have hraw := iwaniecGOdd_le_of_even_geometricBound
          (n + 1) CnextNonneg hs heven
        simpa [mul_assoc] using hraw⟩

theorem iwaniecGEven_geometricBound
    (n : Nat) {s : Real} (hs : 2 ≤ s) :
    iwaniecGEven n s ≤
      iwaniecBaseA * iwaniecContractionA ^ n * s * Real.exp (-s) :=
  (iwaniecGEven_GOdd_geometricBound n).1 s hs

theorem iwaniecGOdd_geometricBound
    (n : Nat) {s : Real} (hs : 1 ≤ s) :
    iwaniecGOdd n s ≤
      Real.exp 1 / 3 * iwaniecBaseA *
        iwaniecContractionA ^ n * s * Real.exp (-s) :=
  (iwaniecGEven_GOdd_geometricBound n).2 s hs

theorem summable_iwaniecGEven {s : Real} (hs : 2 ≤ s) :
    Summable (fun n : Nat => iwaniecGEven n s) := by
  let constant := iwaniecBaseA * s * Real.exp (-s)
  have hgeom := summable_geometric_of_lt_one
    iwaniecContractionA_nonneg iwaniecContractionA_lt_one
  have hmajor : Summable (fun n : Nat => constant * iwaniecContractionA ^ n) :=
    hgeom.mul_left constant
  apply hmajor.of_nonneg_of_le
  · intro n
    exact iwaniecGEven_nonneg n hs
  · intro n
    dsimp [constant]
    have h := iwaniecGEven_geometricBound n hs
    nlinarith

theorem summable_iwaniecGOdd {s : Real} (hs : 1 ≤ s) :
    Summable (fun n : Nat => iwaniecGOdd n s) := by
  let constant := Real.exp 1 / 3 * iwaniecBaseA * s * Real.exp (-s)
  have hgeom := summable_geometric_of_lt_one
    iwaniecContractionA_nonneg iwaniecContractionA_lt_one
  have hmajor : Summable (fun n : Nat => constant * iwaniecContractionA ^ n) :=
    hgeom.mul_left constant
  apply hmajor.of_nonneg_of_le
  · intro n
    exact iwaniecGOdd_nonneg n hs
  · intro n
    dsimp [constant]
    have h := iwaniecGOdd_geometricBound n hs
    nlinarith

theorem iwaniecEvenSieveSeries_nonneg
    {s : Real} (hs : 2 ≤ s) :
    0 ≤ iwaniecEvenSieveSeries s := by
  unfold iwaniecEvenSieveSeries
  exact tsum_nonneg fun n => iwaniecGEven_nonneg n hs

theorem iwaniecOddSieveSeries_nonneg
    {s : Real} (hs : 1 ≤ s) :
    0 ≤ iwaniecOddSieveSeries s := by
  unfold iwaniecOddSieveSeries
  exact tsum_nonneg fun n => iwaniecGOdd_nonneg n hs

theorem iwaniecEvenSieveSeries_le_geometric
    {s : Real} (hs : 2 ≤ s) :
    iwaniecEvenSieveSeries s ≤
      (iwaniecBaseA * s * Real.exp (-s)) *
        (1 - iwaniecContractionA)⁻¹ := by
  let constant := iwaniecBaseA * s * Real.exp (-s)
  have hgeom := hasSum_geometric_of_lt_one
    iwaniecContractionA_nonneg iwaniecContractionA_lt_one
  have hmajor := hgeom.mul_left constant
  have hle := (summable_iwaniecGEven hs).tsum_le_tsum
    (fun n => by
      have h := iwaniecGEven_geometricBound n hs
      dsimp [constant]
      nlinarith)
    hmajor.summable
  unfold iwaniecEvenSieveSeries
  calc
    (∑' n : Nat, iwaniecGEven n s) ≤
        ∑' n : Nat, constant * iwaniecContractionA ^ n := hle
    _ = constant * (1 - iwaniecContractionA)⁻¹ := hmajor.tsum_eq
    _ = _ := rfl

theorem iwaniecOddSieveSeries_le_geometric
    {s : Real} (hs : 1 ≤ s) :
    iwaniecOddSieveSeries s ≤
      (Real.exp 1 / 3 * iwaniecBaseA * s * Real.exp (-s)) *
        (1 - iwaniecContractionA)⁻¹ := by
  let constant := Real.exp 1 / 3 * iwaniecBaseA * s * Real.exp (-s)
  have hgeom := hasSum_geometric_of_lt_one
    iwaniecContractionA_nonneg iwaniecContractionA_lt_one
  have hmajor := hgeom.mul_left constant
  have hle := (summable_iwaniecGOdd hs).tsum_le_tsum
    (fun n => by
      have h := iwaniecGOdd_geometricBound n hs
      dsimp [constant]
      nlinarith)
    hmajor.summable
  unfold iwaniecOddSieveSeries
  calc
    (∑' n : Nat, iwaniecGOdd n s) ≤
        ∑' n : Nat, constant * iwaniecContractionA ^ n := hle
    _ = constant * (1 - iwaniecContractionA)⁻¹ := hmajor.tsum_eq
    _ = _ := rfl

theorem iwaniecEvenSievePartialSum_tendsto
    {s : Real} (hs : 2 ≤ s) :
    Filter.Tendsto (fun m => iwaniecEvenSievePartialSum m s)
      Filter.atTop (nhds (iwaniecEvenSieveSeries s)) := by
  exact (summable_iwaniecGEven hs).hasSum.tendsto_sum_nat

theorem iwaniecOddSievePartialSum_tendsto
    {s : Real} (hs : 1 ≤ s) :
    Filter.Tendsto (fun m => iwaniecOddSievePartialSum m s)
      Filter.atTop (nhds (iwaniecOddSieveSeries s)) := by
  exact (summable_iwaniecGOdd hs).hasSum.tendsto_sum_nat

end

end Erdos1212Kernel
