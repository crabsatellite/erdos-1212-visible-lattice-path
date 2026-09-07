import Erdos1212Kernel.IwaniecSieveGeometricDecay
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral

set_option maxHeartbeats 1800000

/-!
# Iwaniec 1971, Section 3: passage from the recursive terms to the full series

The definitions of `iwaniecGEven` and `iwaniecGOdd` use finite upper limits,
because every individual term has compact support.  Equations (3.6)--(3.7)
are written with an upper limit of infinity.  This file proves that transport
term by term and then justifies the exchange of the infinite sum and integral.
-/

def iwaniecOddKernel (n : Nat) (t : Real) : Real :=
  iwaniecGOdd n (t - 1) / (t - 1)

def iwaniecEvenKernel (n : Nat) (t : Real) : Real :=
  iwaniecGEven n (t - 1) / (t - 1)

private theorem iwaniecOddKernel_Ioi_data
    (n : Nat) {s : Real} (hs : 2 ≤ s) :
    IntegrableOn (iwaniecOddKernel n) (Set.Ioi s) ∧
      ((∫ t in Set.Ioi s, iwaniecOddKernel n t) =
        iwaniecGEven (n + 1) s) := by
  let upper : Real := 6 + 2 * n
  by_cases hupper : s ≤ upper
  · have hcontinuous :
        ContinuousOn (iwaniecOddKernel n) (Set.Icc s upper) := by
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
      change ContinuousOn
        (fun t : Real => iwaniecGOdd n (t - 1) / (t - 1))
        (Set.Icc s upper)
      have hsub : ContinuousOn (fun t : Real => t - 1)
          (Set.Icc s upper) := by fun_prop
      apply hshift.div hsub
      intro t ht
      change t - 1 ≠ 0
      linarith [ht.1]
    have hinterval : IntervalIntegrable (iwaniecOddKernel n) volume s upper := by
      apply ContinuousOn.intervalIntegrable
      simpa [Set.uIcc_of_le hupper] using hcontinuous
    have htailZero : ∀ t ∈ Set.Ioi upper, iwaniecOddKernel n t = 0 := by
      intro t ht
      have hboundary : (5 : Real) + 2 * n ≤ t - 1 := by
        have ht' : upper < t := ht
        dsimp [upper] at ht'
        linarith
      simp [iwaniecOddKernel, iwaniecGOdd_eq_zero_of_boundary n hboundary]
    have htailIntegrable :
        IntegrableOn (iwaniecOddKernel n) (Set.Ioi upper) := by
      exact IntegrableOn.congr_fun integrableOn_zero
        (fun t ht => (htailZero t ht).symm) measurableSet_Ioi
    have hwhole : IntegrableOn (iwaniecOddKernel n) (Set.Ioi s) := by
      have hleft :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hupper).1 hinterval
      have hunion := hleft.union htailIntegrable
      simpa [Set.Ioc_union_Ioi_eq_Ioi hupper] using hunion
    refine And.intro hwhole ?_
    have hadd := intervalIntegral.integral_interval_add_Ioi'
      hinterval htailIntegrable
    have htailIntegral :
        (∫ t in Set.Ioi upper, iwaniecOddKernel n t) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero htailZero
    rw [htailIntegral, add_zero] at hadd
    calc
      (∫ t in Set.Ioi s, iwaniecOddKernel n t) =
          ∫ t in Set.Ioc s upper, iwaniecOddKernel n t := by
        simpa [intervalIntegral.integral_of_le hupper] using hadd.symm
      _ = (∫ t in s..upper, iwaniecOddKernel n t) := by
        rw [intervalIntegral.integral_of_le hupper]
      _ = iwaniecGEven (n + 1) s := by
        simpa [upper, iwaniecOddKernel] using (iwaniecGEven_succ n hupper).symm
  · have hsUpper : upper ≤ s := le_of_not_ge hupper
    have hzero : ∀ t ∈ Set.Ioi s, iwaniecOddKernel n t = 0 := by
      intro t ht
      have hboundary : (5 : Real) + 2 * n ≤ t - 1 := by
        have ht' : s < t := ht
        dsimp [upper] at hsUpper
        linarith [ht']
      simp [iwaniecOddKernel, iwaniecGOdd_eq_zero_of_boundary n hboundary]
    have hintegrable : IntegrableOn (iwaniecOddKernel n) (Set.Ioi s) :=
      IntegrableOn.congr_fun integrableOn_zero
        (fun t ht => (hzero t ht).symm) measurableSet_Ioi
    refine And.intro hintegrable ?_
    rw [setIntegral_eq_zero_of_forall_eq_zero hzero]
    exact (iwaniecGEven_succ_eq_zero n hsUpper).symm

private theorem iwaniecEvenKernel_Ioi_data
    (n : Nat) {s : Real} (hs : 3 ≤ s) :
    IntegrableOn (iwaniecEvenKernel n) (Set.Ioi s) ∧
      ((∫ t in Set.Ioi s, iwaniecEvenKernel n t) =
        iwaniecGOdd n s) := by
  let upper : Real := 5 + 2 * n
  by_cases hupper : s ≤ upper
  · have hcontinuous :
        ContinuousOn (iwaniecEvenKernel n) (Set.Icc s upper) := by
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
      change ContinuousOn
        (fun t : Real => iwaniecGEven n (t - 1) / (t - 1))
        (Set.Icc s upper)
      have hsub : ContinuousOn (fun t : Real => t - 1)
          (Set.Icc s upper) := by fun_prop
      apply hshift.div hsub
      intro t ht
      change t - 1 ≠ 0
      linarith [ht.1]
    have hinterval : IntervalIntegrable (iwaniecEvenKernel n) volume s upper := by
      apply ContinuousOn.intervalIntegrable
      simpa [Set.uIcc_of_le hupper] using hcontinuous
    have htailZero : ∀ t ∈ Set.Ioi upper, iwaniecEvenKernel n t = 0 := by
      intro t ht
      have hboundary : (4 : Real) + 2 * n ≤ t - 1 := by
        have ht' : upper < t := ht
        dsimp [upper] at ht'
        linarith
      simp [iwaniecEvenKernel, iwaniecGEven_eq_zero_of_boundary n hboundary]
    have htailIntegrable :
        IntegrableOn (iwaniecEvenKernel n) (Set.Ioi upper) := by
      exact IntegrableOn.congr_fun integrableOn_zero
        (fun t ht => (htailZero t ht).symm) measurableSet_Ioi
    have hwhole : IntegrableOn (iwaniecEvenKernel n) (Set.Ioi s) := by
      have hleft :=
        (intervalIntegrable_iff_integrableOn_Ioc_of_le hupper).1 hinterval
      have hunion := hleft.union htailIntegrable
      simpa [Set.Ioc_union_Ioi_eq_Ioi hupper] using hunion
    refine And.intro hwhole ?_
    have hadd := intervalIntegral.integral_interval_add_Ioi'
      hinterval htailIntegrable
    have htailIntegral :
        (∫ t in Set.Ioi upper, iwaniecEvenKernel n t) = 0 :=
      setIntegral_eq_zero_of_forall_eq_zero htailZero
    rw [htailIntegral, add_zero] at hadd
    calc
      (∫ t in Set.Ioi s, iwaniecEvenKernel n t) =
          ∫ t in Set.Ioc s upper, iwaniecEvenKernel n t := by
        simpa [intervalIntegral.integral_of_le hupper] using hadd.symm
      _ = (∫ t in s..upper, iwaniecEvenKernel n t) := by
        rw [intervalIntegral.integral_of_le hupper]
      _ = iwaniecGOdd n s := by
        simpa [upper, iwaniecEvenKernel] using
          (iwaniecGOdd_of_three_le n hs hupper).symm
  · have hsUpper : upper ≤ s := le_of_not_ge hupper
    have hzero : ∀ t ∈ Set.Ioi s, iwaniecEvenKernel n t = 0 := by
      intro t ht
      have hboundary : (4 : Real) + 2 * n ≤ t - 1 := by
        have ht' : s < t := ht
        dsimp [upper] at hsUpper
        linarith [ht']
      simp [iwaniecEvenKernel, iwaniecGEven_eq_zero_of_boundary n hboundary]
    have hintegrable : IntegrableOn (iwaniecEvenKernel n) (Set.Ioi s) :=
      IntegrableOn.congr_fun integrableOn_zero
        (fun t ht => (hzero t ht).symm) measurableSet_Ioi
    refine And.intro hintegrable ?_
    rw [setIntegral_eq_zero_of_forall_eq_zero hzero]
    exact (iwaniecGOdd_eq_zero n hsUpper).symm

theorem iwaniecGEven_succ_eq_integral_Ioi
    (n : Nat) {s : Real} (hs : 2 ≤ s) :
    iwaniecGEven (n + 1) s =
      ∫ t in Set.Ioi s, iwaniecOddKernel n t :=
  (iwaniecOddKernel_Ioi_data n hs).2.symm

theorem iwaniecOddKernel_integrableOn_Ioi
    (n : Nat) {s : Real} (hs : 2 ≤ s) :
    IntegrableOn (iwaniecOddKernel n) (Set.Ioi s) :=
  (iwaniecOddKernel_Ioi_data n hs).1

theorem iwaniecGOdd_eq_integral_Ioi
    (n : Nat) {s : Real} (hs : 3 ≤ s) :
    iwaniecGOdd n s =
      ∫ t in Set.Ioi s, iwaniecEvenKernel n t :=
  (iwaniecEvenKernel_Ioi_data n hs).2.symm

theorem iwaniecEvenKernel_integrableOn_Ioi
    (n : Nat) {s : Real} (hs : 3 ≤ s) :
    IntegrableOn (iwaniecEvenKernel n) (Set.Ioi s) :=
  (iwaniecEvenKernel_Ioi_data n hs).1

private theorem iwaniecOddKernel_nonneg
    (n : Nat) {s t : Real} (hs : 2 ≤ s) (ht : t ∈ Set.Ioi s) :
    0 ≤ iwaniecOddKernel n t := by
  have ht' : s < t := ht
  have hden : 0 < t - 1 := by linarith
  exact div_nonneg (iwaniecGOdd_nonneg n (by linarith [ht'])) hden.le

private theorem iwaniecEvenKernel_nonneg
    (n : Nat) {s t : Real} (hs : 3 ≤ s) (ht : t ∈ Set.Ioi s) :
    0 ≤ iwaniecEvenKernel n t := by
  have ht' : s < t := ht
  have hden : 0 < t - 1 := by linarith
  exact div_nonneg (iwaniecGEven_nonneg n (by linarith [ht'])) hden.le

/-- The odd recursive kernels may be summed under the improper integral. -/
theorem iwaniec_tsum_integral_oddKernel
    {s : Real} (hs : 2 ≤ s) :
    (∑' n : Nat, ∫ t in Set.Ioi s, iwaniecOddKernel n t) =
      ∫ t in Set.Ioi s, ∑' n : Nat, iwaniecOddKernel n t := by
  have hterm : ∀ n : Nat,
      Integrable (iwaniecOddKernel n) (volume.restrict (Set.Ioi s)) :=
    fun n => (iwaniecOddKernel_Ioi_data n hs).1
  have hnorm (n : Nat) :
      (∫ t in Set.Ioi s, norm (iwaniecOddKernel n t)) =
        iwaniecGEven (n + 1) s := by
    calc
      (∫ t in Set.Ioi s, norm (iwaniecOddKernel n t)) =
          ∫ t in Set.Ioi s, iwaniecOddKernel n t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact Real.norm_of_nonneg (iwaniecOddKernel_nonneg n hs ht)
      _ = iwaniecGEven (n + 1) s :=
        (iwaniecOddKernel_Ioi_data n hs).2
  have hshift : Summable (fun n : Nat => iwaniecGEven (n + 1) s) :=
    (summable_nat_add_iff 1).2 (summable_iwaniecGEven hs)
  have hnormSum : Summable (fun n : Nat =>
      ∫ t in Set.Ioi s, norm (iwaniecOddKernel n t)) := by
    simpa only [hnorm] using hshift
  exact integral_tsum_of_summable_integral_norm hterm hnormSum

/-- The even recursive kernels may be summed under the improper integral. -/
theorem iwaniec_tsum_integral_evenKernel
    {s : Real} (hs : 3 ≤ s) :
    (∑' n : Nat, ∫ t in Set.Ioi s, iwaniecEvenKernel n t) =
      ∫ t in Set.Ioi s, ∑' n : Nat, iwaniecEvenKernel n t := by
  have hterm : ∀ n : Nat,
      Integrable (iwaniecEvenKernel n) (volume.restrict (Set.Ioi s)) :=
    fun n => (iwaniecEvenKernel_Ioi_data n hs).1
  have hnorm (n : Nat) :
      (∫ t in Set.Ioi s, norm (iwaniecEvenKernel n t)) =
        iwaniecGOdd n s := by
    calc
      (∫ t in Set.Ioi s, norm (iwaniecEvenKernel n t)) =
          ∫ t in Set.Ioi s, iwaniecEvenKernel n t := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact Real.norm_of_nonneg (iwaniecEvenKernel_nonneg n hs ht)
      _ = iwaniecGOdd n s := (iwaniecEvenKernel_Ioi_data n hs).2
  have hnormSum : Summable (fun n : Nat =>
      ∫ t in Set.Ioi s, norm (iwaniecEvenKernel n t)) := by
    simpa only [hnorm] using (summable_iwaniecGOdd (by linarith : 1 ≤ s))
  exact integral_tsum_of_summable_integral_norm hterm hnormSum

/-- Iwaniec 1971, equation (3.6). -/
theorem iwaniecEvenSieveSeries_eq_integral_Ioi_add_gTwo
    {s : Real} (hs : 2 ≤ s) :
    iwaniecEvenSieveSeries s =
      (∫ t in Set.Ioi s, iwaniecOddSieveSeries (t - 1) / (t - 1)) +
        iwaniecGTwo s := by
  have htail :
      (∑' n : Nat, iwaniecGEven (n + 1) s) =
        ∫ t in Set.Ioi s, iwaniecOddSieveSeries (t - 1) / (t - 1) := by
    calc
      (∑' n : Nat, iwaniecGEven (n + 1) s) =
          ∑' n : Nat, ∫ t in Set.Ioi s, iwaniecOddKernel n t := by
        apply tsum_congr
        intro n
        exact iwaniecGEven_succ_eq_integral_Ioi n hs
      _ = (∫ t in Set.Ioi s, ∑' n : Nat, iwaniecOddKernel n t) :=
        iwaniec_tsum_integral_oddKernel hs
      _ = (∫ t in Set.Ioi s,
          iwaniecOddSieveSeries (t - 1) / (t - 1)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t _ht
        simp only [iwaniecOddKernel, iwaniecOddSieveSeries, tsum_div_const]
  unfold iwaniecEvenSieveSeries
  calc
    (∑' n : Nat, iwaniecGEven n s) =
        (∑ n ∈ Finset.range 1, iwaniecGEven n s) +
          ∑' n : Nat, iwaniecGEven (n + 1) s :=
      ((summable_iwaniecGEven hs).sum_add_tsum_nat_add 1).symm
    _ = iwaniecGTwo s + ∑' n : Nat, iwaniecGEven (n + 1) s := by
      simp [iwaniecGEven_zero]
    _ = iwaniecGTwo s +
        (∫ t in Set.Ioi s,
          iwaniecOddSieveSeries (t - 1) / (t - 1)) := by rw [htail]
    _ = _ := add_comm _ _

/-- Iwaniec 1971, the first branch of equation (3.7). -/
theorem iwaniecOddSieveSeries_eq_integral_Ioi
    {s : Real} (hs : 3 ≤ s) :
    iwaniecOddSieveSeries s =
      ∫ t in Set.Ioi s, iwaniecEvenSieveSeries (t - 1) / (t - 1) := by
  unfold iwaniecOddSieveSeries
  calc
    (∑' n : Nat, iwaniecGOdd n s) =
        ∑' n : Nat, ∫ t in Set.Ioi s, iwaniecEvenKernel n t := by
      apply tsum_congr
      intro n
      exact iwaniecGOdd_eq_integral_Ioi n hs
    _ = (∫ t in Set.Ioi s, ∑' n : Nat, iwaniecEvenKernel n t) :=
      iwaniec_tsum_integral_evenKernel hs
    _ = (∫ t in Set.Ioi s,
        iwaniecEvenSieveSeries (t - 1) / (t - 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t _ht
      simp only [iwaniecEvenKernel, iwaniecEvenSieveSeries, tsum_div_const]

/-- Iwaniec 1971, the constant branch of equation (3.7). -/
theorem iwaniecOddSieveSeries_eq_three
    {s : Real} (_hs : 1 ≤ s) (hthree : s ≤ 3) :
    iwaniecOddSieveSeries s = iwaniecOddSieveSeries 3 := by
  unfold iwaniecOddSieveSeries
  apply tsum_congr
  intro n
  exact iwaniecGOdd_of_le_three n hthree

end

end Erdos1212Kernel
