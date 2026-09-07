import Erdos1212Kernel.IwaniecWeightedLogIncrementShift

namespace Erdos1212Kernel

noncomputable section

open Filter MeasureTheory intervalIntegral

set_option maxHeartbeats 1600000

def iwaniecWeightedLogKernelIntegral
    (b : Real → Real) (lower upper : Real) : Real :=
  ∫ x in lower..upper, b x * iwaniecLogKernel x

theorem sum_unitInterval_integrals
    (f : Real → Real) {B A : Nat} (hBA : B ≤ A)
    (hf : ContinuousOn f
      (Set.Icc (((B - 1 : Nat) : Real)) (A : Real))) :
    (∑ n ∈ Finset.Icc B A,
      ∫ x in ((n - 1 : Nat) : Real)..(n : Real), f x) =
        ∫ x in ((B - 1 : Nat) : Real)..(A : Real), f x := by
  induction A, hBA using Nat.le_induction with
  | base => simp
  | succ A hBA ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hleftCont : ContinuousOn f
          (Set.Icc (((B - 1 : Nat) : Real)) (A : Real)) := by
        apply hf.mono
        intro x hx
        exact ⟨hx.1, hx.2.trans (by norm_cast; omega)⟩
      rw [ih hleftCont]
      have hpred : A + 1 - 1 = A := by omega
      rw [hpred]
      rw [intervalIntegral.integral_add_adjacent_intervals]
      · apply ContinuousOn.intervalIntegrable
        have hleftOrder : ((B - 1 : Nat) : Real) ≤ (A : Real) := by
          norm_cast
          omega
        rw [Set.uIcc_of_le hleftOrder]
        exact hleftCont
      · apply ContinuousOn.intervalIntegrable
        have hunitOrder : (A : Real) ≤ ((A + 1 : Nat) : Real) := by
          norm_cast
          omega
        rw [Set.uIcc_of_le hunitOrder]
        apply hf.mono
        intro x hx
        exact ⟨by
          have hpred : ((B - 1 : Nat) : Real) ≤ (A : Real) := by
            norm_cast
            omega
          exact hpred.trans hx.1, hx.2⟩

theorem iwaniecWeightedLogKernel_pastUnit_le_increment
    (b : Real → Real) {n : Nat} (hn : 3 ≤ n)
    (hbCont : ContinuousOn b
      (Set.Icc (((n - 1 : Nat) : Real)) (n : Real)))
    (hbMono : MonotoneOn b
      (Set.Icc (((n - 1 : Nat) : Real)) (n : Real))) :
    iwaniecWeightedLogKernelIntegral b ((n - 1 : Nat) : Real) (n : Real) ≤
      b n * (iwaniecLogLogValue n - iwaniecLogLogValue (n - 1)) := by
  rw [iwaniecLogLogIncrement_eq_intervalIntegral hn]
  unfold iwaniecWeightedLogKernelIntegral
  have horder : ((n - 1 : Nat) : Real) ≤ (n : Real) := by
    norm_cast
    omega
  have hkernelCont : ContinuousOn iwaniecLogKernel
      (Set.Icc (((n - 1 : Nat) : Real)) (n : Real)) := by
    apply iwaniecLogKernel_continuousOn_Ioi_one.mono
    intro x hx
    have hpred : (2 : Real) ≤ ((n - 1 : Nat) : Real) := by
      norm_cast
      omega
    exact lt_of_lt_of_le one_lt_two (hpred.trans hx.1)
  have hactualInt : IntervalIntegrable
      (fun x => b x * iwaniecLogKernel x) volume
      ((n - 1 : Nat) : Real) (n : Real) :=
    (by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le horder]
      simpa only [Pi.mul_apply] using hbCont.mul hkernelCont)
  have hupperInt : IntervalIntegrable
      (fun x => b n * iwaniecLogKernel x) volume
      ((n - 1 : Nat) : Real) (n : Real) :=
    (by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le horder]
      simpa only [Pi.mul_apply] using
        (continuousOn_const.mul hkernelCont :
          ContinuousOn ((fun _x : Real => b n) * iwaniecLogKernel)
            (Set.Icc (((n - 1 : Nat) : Real)) (n : Real))))
  have hmono :
      (∫ x in ((n - 1 : Nat) : Real)..(n : Real),
        b x * iwaniecLogKernel x) ≤
      ∫ x in ((n - 1 : Nat) : Real)..(n : Real),
        b n * iwaniecLogKernel x := by
    apply intervalIntegral.integral_mono_on horder hactualInt hupperInt
    intro x hx
    apply mul_le_mul_of_nonneg_right
    · apply hbMono hx
      exact ⟨horder, le_rfl⟩
      exact hx.2
    · exact (iwaniecLogKernel_pos
        (show (1 : Real) < x by
          have hpred : (2 : Real) ≤ ((n - 1 : Nat) : Real) := by
            norm_cast
            omega
          exact lt_of_lt_of_le one_lt_two (hpred.trans hx.1))).le
  simpa only [intervalIntegral.integral_const_mul] using hmono

theorem iwaniecWeightedLogKernel_nextIncrement_le_futureUnit
    (b : Real → Real) {n : Nat} (hn : 3 ≤ n)
    (hbCont : ContinuousOn b
      (Set.Icc (n : Real) ((n + 1 : Nat) : Real)))
    (hbMono : MonotoneOn b
      (Set.Icc (n : Real) ((n + 1 : Nat) : Real))) :
    b n * (iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n) ≤
      iwaniecWeightedLogKernelIntegral b (n : Real) (n + 1 : Nat) := by
  have hpred : n + 1 - 1 = n := by omega
  have hinc := iwaniecLogLogIncrement_eq_intervalIntegral
    (show 3 ≤ n + 1 by omega)
  rw [hpred] at hinc
  rw [hinc]
  unfold iwaniecWeightedLogKernelIntegral
  have horder : (n : Real) ≤ ((n + 1 : Nat) : Real) := by norm_cast; omega
  have hkernelCont : ContinuousOn iwaniecLogKernel
      (Set.Icc (n : Real) ((n + 1 : Nat) : Real)) := by
    apply iwaniecLogKernel_continuousOn_Ioi_one.mono
    intro x hx
    have hnReal : (3 : Real) ≤ n := by exact_mod_cast hn
    exact lt_of_lt_of_le (by norm_num : (1 : Real) < 3) (hnReal.trans hx.1)
  have hlowerInt : IntervalIntegrable
      (fun x => b n * iwaniecLogKernel x) volume
      (n : Real) ((n + 1 : Nat) : Real) :=
    (by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le horder]
      simpa only [Pi.mul_apply] using
        (continuousOn_const.mul hkernelCont :
          ContinuousOn ((fun _x : Real => b n) * iwaniecLogKernel)
            (Set.Icc (n : Real) ((n + 1 : Nat) : Real))))
  have hactualInt : IntervalIntegrable
      (fun x => b x * iwaniecLogKernel x) volume
      (n : Real) ((n + 1 : Nat) : Real) :=
    (by
      apply ContinuousOn.intervalIntegrable
      rw [Set.uIcc_of_le horder]
      simpa only [Pi.mul_apply] using hbCont.mul hkernelCont)
  have hmono :
      (∫ x in (n : Real)..((n + 1 : Nat) : Real),
        b n * iwaniecLogKernel x) ≤
      ∫ x in (n : Real)..((n + 1 : Nat) : Real),
        b x * iwaniecLogKernel x := by
    apply intervalIntegral.integral_mono_on horder hlowerInt hactualInt
    intro x hx
    apply mul_le_mul_of_nonneg_right
    · apply hbMono
      · exact ⟨le_rfl, horder⟩
      · exact hx
      · exact hx.1
    · exact (iwaniecLogKernel_pos
        (show (1 : Real) < x by
          have hnReal : (3 : Real) ≤ n := by exact_mod_cast hn
          exact lt_of_lt_of_le (by norm_num : (1 : Real) < 3)
            (hnReal.trans hx.1))).le
  simpa only [intervalIntegral.integral_const_mul] using hmono

theorem iwaniecWeightedIncrement_le_ratio_mul_futureUnit
    (b : Real → Real) {n : Nat} (hn : 3 ≤ n)
    (hbNonneg : 0 ≤ b n)
    (hbCont : ContinuousOn b
      (Set.Icc (n : Real) ((n + 1 : Nat) : Real)))
    (hbMono : MonotoneOn b
      (Set.Icc (n : Real) ((n + 1 : Nat) : Real))) :
    b n * (iwaniecLogLogValue n - iwaniecLogLogValue (n - 1)) ≤
      iwaniecLogKernelTwoStepRatio (n - 1) *
        iwaniecWeightedLogKernelIntegral b (n : Real) (n + 1 : Nat) := by
  have hlocal := iwaniecLogLogIncrement_le_ratio_mul_next hn
  have hratioNonneg : 0 ≤ iwaniecLogKernelTwoStepRatio (n - 1) :=
    zero_le_one.trans (one_le_iwaniecLogKernelTwoStepRatio (by omega))
  calc
    b n * (iwaniecLogLogValue n - iwaniecLogLogValue (n - 1)) ≤
      b n * (iwaniecLogKernelTwoStepRatio (n - 1) *
        (iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n)) :=
      mul_le_mul_of_nonneg_left hlocal hbNonneg
    _ = iwaniecLogKernelTwoStepRatio (n - 1) *
        (b n * (iwaniecLogLogValue (n + 1) - iwaniecLogLogValue n)) := by
      ring
    _ ≤ iwaniecLogKernelTwoStepRatio (n - 1) *
        iwaniecWeightedLogKernelIntegral b (n : Real) (n + 1 : Nat) := by
      exact mul_le_mul_of_nonneg_left
        (iwaniecWeightedLogKernel_nextIncrement_le_futureUnit
          b hn hbCont hbMono) hratioNonneg

theorem iwaniecWeightedLogKernelIntegral_le_logLogIncrement
    (b : Real → Real) {B A : Nat} (hB : 3 ≤ B) (hBA : B ≤ A)
    (hbCont : ContinuousOn b
      (Set.Icc (((B - 1 : Nat) : Real)) (A : Real)))
    (hbMono : MonotoneOn b
      (Set.Icc (((B - 1 : Nat) : Real)) (A : Real))) :
    iwaniecWeightedLogKernelIntegral b ((B - 1 : Nat) : Real) (A : Real) ≤
      iwaniecLogLogIncrementWeightedInterval (fun n => b n) B A := by
  have hkernelCont : ContinuousOn iwaniecLogKernel
      (Set.Icc (((B - 1 : Nat) : Real)) (A : Real)) := by
    apply iwaniecLogKernel_continuousOn_Ioi_one.mono
    intro x hx
    have hpred : (2 : Real) ≤ ((B - 1 : Nat) : Real) := by
      norm_cast
      omega
    exact lt_of_lt_of_le one_lt_two (hpred.trans hx.1)
  have hfCont : ContinuousOn
      (fun x => b x * iwaniecLogKernel x)
      (Set.Icc (((B - 1 : Nat) : Real)) (A : Real)) := by
    simpa only [Pi.mul_apply] using hbCont.mul hkernelCont
  unfold iwaniecWeightedLogKernelIntegral
  rw [← sum_unitInterval_integrals
    (fun x => b x * iwaniecLogKernel x) hBA hfCont]
  unfold iwaniecLogLogIncrementWeightedInterval
  apply Finset.sum_le_sum
  intro n hn
  have hnData := Finset.mem_Icc.mp hn
  apply iwaniecWeightedLogKernel_pastUnit_le_increment b
    (hB.trans hnData.1)
  · apply hbCont.mono
    intro x hx
    exact ⟨by
      have hglobal : ((B - 1 : Nat) : Real) ≤ ((n - 1 : Nat) : Real) := by
        norm_cast
        omega
      exact hglobal.trans hx.1, hx.2.trans (by exact_mod_cast hnData.2)⟩
  · apply hbMono.mono
    intro x hx
    exact ⟨by
      have hglobal : ((B - 1 : Nat) : Real) ≤ ((n - 1 : Nat) : Real) := by
        norm_cast
        omega
      exact hglobal.trans hx.1, hx.2.trans (by exact_mod_cast hnData.2)⟩

theorem iwaniecLogLogIncrement_le_weightedLogKernelIntegral
    (b : Real → Real) {B A : Nat} {rho : Real}
    (hB : 3 ≤ B) (hBA : B ≤ A) (hrho : 0 ≤ rho)
    (hbCont : ContinuousOn b
      (Set.Icc (B : Real) ((A + 1 : Nat) : Real)))
    (hbMono : MonotoneOn b
      (Set.Icc (B : Real) ((A + 1 : Nat) : Real)))
    (hbNonneg : ∀ x ∈ Set.Icc (B : Real) ((A + 1 : Nat) : Real),
      0 ≤ b x)
    (hratio : ∀ k : Nat, B - 1 ≤ k →
      iwaniecLogKernelTwoStepRatio k ≤ rho) :
    iwaniecLogLogIncrementWeightedInterval (fun n => b n) B A ≤
      rho * iwaniecWeightedLogKernelIntegral b (B : Real) (A + 1 : Nat) := by
  have hkernelCont : ContinuousOn iwaniecLogKernel
      (Set.Icc (B : Real) ((A + 1 : Nat) : Real)) := by
    apply iwaniecLogKernel_continuousOn_Ioi_one.mono
    intro x hx
    have hBReal : (3 : Real) ≤ B := by exact_mod_cast hB
    exact lt_of_lt_of_le (by norm_num : (1 : Real) < 3) (hBReal.trans hx.1)
  have hfCont : ContinuousOn
      (fun x => b x * iwaniecLogKernel x)
      (Set.Icc (B : Real) ((A + 1 : Nat) : Real)) := by
    simpa only [Pi.mul_apply] using hbCont.mul hkernelCont
  have hsum :
      iwaniecLogLogIncrementWeightedInterval (fun n => b n) B A ≤
        ∑ n ∈ Finset.Icc B A,
          rho * iwaniecWeightedLogKernelIntegral b (n : Real) (n + 1 : Nat) := by
    unfold iwaniecLogLogIncrementWeightedInterval
    apply Finset.sum_le_sum
    intro n hn
    have hnData := Finset.mem_Icc.mp hn
    have hBn : (B : Real) ≤ (n : Real) := by exact_mod_cast hnData.1
    have hnSuccA : ((n + 1 : Nat) : Real) ≤ ((A + 1 : Nat) : Real) := by
      exact_mod_cast (show n + 1 ≤ A + 1 by omega)
    have hunitCont : ContinuousOn b
        (Set.Icc (n : Real) ((n + 1 : Nat) : Real)) := by
      apply hbCont.mono
      intro x hx
      exact ⟨hBn.trans hx.1, hx.2.trans hnSuccA⟩
    have hunitMono : MonotoneOn b
        (Set.Icc (n : Real) ((n + 1 : Nat) : Real)) := by
      apply hbMono.mono
      intro x hx
      exact ⟨hBn.trans hx.1, hx.2.trans hnSuccA⟩
    have hlocal := iwaniecWeightedIncrement_le_ratio_mul_futureUnit b
      (hB.trans hnData.1)
      (hbNonneg n ⟨hBn,
        by exact_mod_cast (show n ≤ A + 1 by omega)⟩)
      hunitCont hunitMono
    have hunitNonneg : 0 ≤
        iwaniecWeightedLogKernelIntegral b (n : Real) (n + 1 : Nat) := by
      unfold iwaniecWeightedLogKernelIntegral
      apply intervalIntegral.integral_nonneg (by norm_cast; omega)
      intro x hx
      have hnA : ((n + 1 : Nat) : Real) ≤ ((A + 1 : Nat) : Real) := by
        exact_mod_cast (show n + 1 ≤ A + 1 by omega)
      exact mul_nonneg
        (hbNonneg x ⟨hBn.trans hx.1, hx.2.trans hnA⟩)
        (iwaniecLogKernel_pos (by
          have hBReal : (3 : Real) ≤ B := by exact_mod_cast hB
          exact lt_of_lt_of_le (by norm_num : (1 : Real) < 3)
            (hBReal.trans (hBn.trans hx.1)))).le
    exact hlocal.trans (mul_le_mul_of_nonneg_right
      (hratio (n - 1) (by omega)) hunitNonneg)
  calc
    iwaniecLogLogIncrementWeightedInterval (fun n => b n) B A ≤
        ∑ n ∈ Finset.Icc B A,
          rho * iwaniecWeightedLogKernelIntegral b (n : Real) (n + 1 : Nat) :=
      hsum
    _ = rho * ∑ n ∈ Finset.Icc B A,
        iwaniecWeightedLogKernelIntegral b (n : Real) (n + 1 : Nat) := by
      rw [Finset.mul_sum]
    _ = rho * iwaniecWeightedLogKernelIntegral b (B : Real) (A + 1 : Nat) := by
      apply congrArg (fun value : Real => rho * value)
      have hpartition := sum_unitInterval_integrals
        (fun x => b x * iwaniecLogKernel x)
        (B := B + 1) (A := A + 1) (by omega)
        (by
          simpa using hfCont)
      have hshift := sum_Icc_succ_shift
        (fun m => iwaniecWeightedLogKernelIntegral b
          ((m - 1 : Nat) : Real) (m : Real)) hBA
      calc
        (∑ n ∈ Finset.Icc B A,
            iwaniecWeightedLogKernelIntegral b (n : Real) (n + 1 : Nat)) =
          ∑ m ∈ Finset.Icc (B + 1) (A + 1),
            iwaniecWeightedLogKernelIntegral b
              ((m - 1 : Nat) : Real) (m : Real) := by
            simpa using hshift
        _ = iwaniecWeightedLogKernelIntegral b (B : Real) (A + 1 : Nat) := by
          simpa [iwaniecWeightedLogKernelIntegral] using hpartition

/-- Qualitative main-term sandwich with the exact paper kernel.  The two
one-unit endpoint shifts are explicit and the multiplicative distortion is
uniformly `1 + delta` once the lower endpoint is large. -/
theorem eventually_iwaniecWeightedIntegral_logIncrement_sandwich
    {delta : Real} (hdelta : 0 < delta) :
    ∃ B₀ : Nat, ∀ B A : Nat, ∀ b : Real → Real,
      B₀ ≤ B → B ≤ A →
      ContinuousOn b
        (Set.Icc (((B - 1 : Nat) : Real)) ((A + 1 : Nat) : Real)) →
      MonotoneOn b
        (Set.Icc (((B - 1 : Nat) : Real)) ((A + 1 : Nat) : Real)) →
      (∀ x ∈ Set.Icc (((B - 1 : Nat) : Real)) ((A + 1 : Nat) : Real),
        0 ≤ b x) →
      iwaniecWeightedLogKernelIntegral b ((B - 1 : Nat) : Real) (A : Real) ≤
        iwaniecLogLogIncrementWeightedInterval (fun n => b n) B A ∧
      iwaniecLogLogIncrementWeightedInterval (fun n => b n) B A ≤
        (1 + delta) *
          iwaniecWeightedLogKernelIntegral b (B : Real) (A + 1 : Nat) := by
  have hratioEvent :=
    eventually_iwaniecLogKernelTwoStepRatio_le_one_add hdelta
  rw [eventually_atTop] at hratioEvent
  obtain ⟨K₀, hK₀⟩ := hratioEvent
  refine ⟨max 3 (K₀ + 1), ?_⟩
  intro B A b hB hBA hbCont hbMono hbNonneg
  have hBThree : 3 ≤ B :=
    (Nat.le_max_left 3 (K₀ + 1)).trans hB
  have hBK : K₀ + 1 ≤ B :=
    (Nat.le_max_right 3 (K₀ + 1)).trans hB
  constructor
  · apply iwaniecWeightedLogKernelIntegral_le_logLogIncrement b
      hBThree hBA
    · apply hbCont.mono
      intro x hx
      exact ⟨hx.1, hx.2.trans (by exact_mod_cast (show A ≤ A + 1 by omega))⟩
    · apply hbMono.mono
      intro x hx
      exact ⟨hx.1, hx.2.trans (by exact_mod_cast (show A ≤ A + 1 by omega))⟩
  · apply iwaniecLogLogIncrement_le_weightedLogKernelIntegral b
      hBThree hBA (by linarith)
    · apply hbCont.mono
      intro x hx
      have hpred : ((B - 1 : Nat) : Real) ≤ (B : Real) := by
        norm_cast
        omega
      exact ⟨hpred.trans hx.1, hx.2⟩
    · apply hbMono.mono
      intro x hx
      have hpred : ((B - 1 : Nat) : Real) ≤ (B : Real) := by
        norm_cast
        omega
      exact ⟨hpred.trans hx.1, hx.2⟩
    · intro x hx
      apply hbNonneg x
      have hpred : ((B - 1 : Nat) : Real) ≤ (B : Real) := by
        norm_cast
        omega
      exact ⟨hpred.trans hx.1, hx.2⟩
    · intro k hk
      apply hK₀
      omega

/-- Qualitative weighted-prime version of Iwaniec 1971, Lemma 13.  It keeps
the endpoint shifts explicit and isolates the Mertens error as the additive
`2 * epsilon * b(A)` term. -/
theorem eventually_iwaniecWeightedPrimeIntegral_sandwich
    {epsilon delta : Real} (hepsilon : 0 < epsilon) (hdelta : 0 < delta) :
    ∃ B₀ : Nat, ∀ B A : Nat, ∀ b : Real → Real,
      B₀ ≤ B → B ≤ A →
      ContinuousOn b
        (Set.Icc (((B - 1 : Nat) : Real)) ((A + 1 : Nat) : Real)) →
      MonotoneOn b
        (Set.Icc (((B - 1 : Nat) : Real)) ((A + 1 : Nat) : Real)) →
      (∀ x ∈ Set.Icc (((B - 1 : Nat) : Real)) ((A + 1 : Nat) : Real),
        0 ≤ b x) →
      iwaniecWeightedLogKernelIntegral b ((B - 1 : Nat) : Real) (A : Real) -
          2 * epsilon * b A ≤
        iwaniecPrimeReciprocalWeightedInterval (fun n => b n) B A ∧
      iwaniecPrimeReciprocalWeightedInterval (fun n => b n) B A ≤
        (1 + delta) *
            iwaniecWeightedLogKernelIntegral b (B : Real) (A + 1 : Nat) +
          2 * epsilon * b A := by
  obtain ⟨B₁, hB₁⟩ :=
    eventually_iwaniecWeightedIntegral_logIncrement_sandwich hdelta
  obtain ⟨B₂, hB₂⟩ :=
    eventually_iwaniecPrimeReciprocalWeightedInterval_sub_logAbel_le
      hepsilon
  refine ⟨max B₁ (B₂ + 1), ?_⟩
  intro B A b hB hBA hbCont hbMono hbNonneg
  have hmain := hB₁ B A b ((Nat.le_max_left B₁ (B₂ + 1)).trans hB)
    hBA hbCont hbMono hbNonneg
  have hdiscNonneg : ∀ n ∈ Finset.Icc B A, 0 ≤ b n := by
    intro n hn
    have hnData := Finset.mem_Icc.mp hn
    apply hbNonneg n
    constructor
    · have hpred : ((B - 1 : Nat) : Real) ≤ (B : Real) := by
        norm_cast
        omega
      exact hpred.trans (by exact_mod_cast hnData.1)
    · exact_mod_cast (show n ≤ A + 1 by omega)
  have hdiscIncreasing :
      ∀ n ∈ Finset.Ico B A,
        b (n : Real) ≤ b ((n + 1 : Nat) : Real) := by
    intro n hn
    have hnData := Finset.mem_Ico.mp hn
    apply hbMono
    · constructor
      · have hpred : ((B - 1 : Nat) : Real) ≤ (B : Real) := by
          norm_cast
          omega
        exact hpred.trans (by exact_mod_cast hnData.1)
      · exact_mod_cast (show n ≤ A + 1 by omega)
    · constructor
      · have hpred : ((B - 1 : Nat) : Real) ≤ (B : Real) := by
          norm_cast
          omega
        exact hpred.trans (by exact_mod_cast (show B ≤ n + 1 by omega))
      · exact_mod_cast (show n + 1 ≤ A + 1 by omega)
    · exact_mod_cast (show n ≤ n + 1 by omega)
  have herror := hB₂ B A (fun n => b n)
    ((Nat.le_max_right B₁ (B₂ + 1)).trans hB)
    hBA hdiscNonneg hdiscIncreasing
  rw [iwaniecPrimeReciprocalLogAbel_eq_logLogIncrementWeightedInterval
    (fun n => b n) hBA] at herror
  rw [abs_le] at herror
  constructor <;> linarith [hmain.1, hmain.2, herror.1, herror.2]

/-- Target-interval form: the only non-Mertens losses are the arbitrarily
small multiplicative distortion and the explicit final unit interval. -/
theorem eventually_iwaniecWeightedPrimeIntegral_target_bounds
    {epsilon delta : Real} (hepsilon : 0 < epsilon) (hdelta : 0 < delta) :
    ∃ B₀ : Nat, ∀ B A : Nat, ∀ b : Real → Real,
      B₀ ≤ B → B ≤ A →
      ContinuousOn b
        (Set.Icc (((B - 1 : Nat) : Real)) ((A + 1 : Nat) : Real)) →
      MonotoneOn b
        (Set.Icc (((B - 1 : Nat) : Real)) ((A + 1 : Nat) : Real)) →
      (∀ x ∈ Set.Icc (((B - 1 : Nat) : Real)) ((A + 1 : Nat) : Real),
        0 ≤ b x) →
      iwaniecWeightedLogKernelIntegral b (B : Real) (A : Real) -
          2 * epsilon * b A ≤
        iwaniecPrimeReciprocalWeightedInterval (fun n => b n) B A ∧
      iwaniecPrimeReciprocalWeightedInterval (fun n => b n) B A ≤
        iwaniecWeightedLogKernelIntegral b (B : Real) (A : Real) +
          delta * iwaniecWeightedLogKernelIntegral b (B : Real) (A : Real) +
          (1 + delta) *
            iwaniecWeightedLogKernelIntegral b (A : Real) (A + 1 : Nat) +
          2 * epsilon * b A := by
  obtain ⟨B₀, hB₀⟩ :=
    eventually_iwaniecWeightedPrimeIntegral_sandwich hepsilon hdelta
  refine ⟨max 3 B₀, ?_⟩
  intro B A b hB hBA hbCont hbMono hbNonneg
  have hBThree : 3 ≤ B := (Nat.le_max_left 3 B₀).trans hB
  have hBBase : B₀ ≤ B := (Nat.le_max_right 3 B₀).trans hB
  have hsandwich := hB₀ B A b hBBase hBA hbCont hbMono hbNonneg
  let f := fun x : Real => b x * iwaniecLogKernel x
  have hfCont : ContinuousOn f
      (Set.Icc (((B - 1 : Nat) : Real)) ((A + 1 : Nat) : Real)) := by
    have hkernelCont : ContinuousOn iwaniecLogKernel
        (Set.Icc (((B - 1 : Nat) : Real)) ((A + 1 : Nat) : Real)) := by
      apply iwaniecLogKernel_continuousOn_Ioi_one.mono
      intro x hx
      have hpred : (2 : Real) ≤ ((B - 1 : Nat) : Real) := by
        norm_cast
        omega
      exact lt_of_lt_of_le one_lt_two (hpred.trans hx.1)
    dsimp [f]
    simpa only [Pi.mul_apply] using hbCont.mul hkernelCont
  have hleftNonneg :
      0 ≤ iwaniecWeightedLogKernelIntegral b
        ((B - 1 : Nat) : Real) (B : Real) := by
    unfold iwaniecWeightedLogKernelIntegral
    apply intervalIntegral.integral_nonneg (by norm_cast; omega)
    intro x hx
    exact mul_nonneg (hbNonneg x ⟨hx.1,
      hx.2.trans (by exact_mod_cast (show B ≤ A + 1 by omega))⟩)
      (iwaniecLogKernel_pos (by
        have hpred : (2 : Real) ≤ ((B - 1 : Nat) : Real) := by
          norm_cast
          omega
        exact lt_of_lt_of_le one_lt_two (hpred.trans hx.1))).le
  have hpastSplit :
      iwaniecWeightedLogKernelIntegral b ((B - 1 : Nat) : Real) (A : Real) =
        iwaniecWeightedLogKernelIntegral b ((B - 1 : Nat) : Real) (B : Real) +
          iwaniecWeightedLogKernelIntegral b (B : Real) (A : Real) := by
    unfold iwaniecWeightedLogKernelIntegral
    symm
    apply intervalIntegral.integral_add_adjacent_intervals
    · apply ContinuousOn.intervalIntegrable
      have horder : ((B - 1 : Nat) : Real) ≤ (B : Real) := by
        norm_cast
        omega
      rw [Set.uIcc_of_le horder]
      apply hfCont.mono
      intro x hx
      exact ⟨hx.1, hx.2.trans (by exact_mod_cast (show B ≤ A + 1 by omega))⟩
    · apply ContinuousOn.intervalIntegrable
      have horder : (B : Real) ≤ (A : Real) := by exact_mod_cast hBA
      rw [Set.uIcc_of_le horder]
      apply hfCont.mono
      intro x hx
      have hpred : ((B - 1 : Nat) : Real) ≤ (B : Real) := by
        norm_cast
        omega
      exact ⟨hpred.trans hx.1,
        hx.2.trans (by exact_mod_cast (show A ≤ A + 1 by omega))⟩
  have hfutureSplit :
      iwaniecWeightedLogKernelIntegral b (B : Real) (A + 1 : Nat) =
        iwaniecWeightedLogKernelIntegral b (B : Real) (A : Real) +
          iwaniecWeightedLogKernelIntegral b (A : Real) (A + 1 : Nat) := by
    unfold iwaniecWeightedLogKernelIntegral
    symm
    apply intervalIntegral.integral_add_adjacent_intervals
    · apply ContinuousOn.intervalIntegrable
      have horder : (B : Real) ≤ (A : Real) := by exact_mod_cast hBA
      rw [Set.uIcc_of_le horder]
      apply hfCont.mono
      intro x hx
      have hpred : ((B - 1 : Nat) : Real) ≤ (B : Real) := by
        norm_cast
        omega
      exact ⟨hpred.trans hx.1,
        hx.2.trans (by exact_mod_cast (show A ≤ A + 1 by omega))⟩
    · apply ContinuousOn.intervalIntegrable
      have horder : (A : Real) ≤ ((A + 1 : Nat) : Real) := by
        norm_cast
        omega
      rw [Set.uIcc_of_le horder]
      apply hfCont.mono
      intro x hx
      have hpred : ((B - 1 : Nat) : Real) ≤ (A : Real) := by
        norm_cast
        omega
      exact ⟨hpred.trans hx.1, hx.2⟩
  rw [hpastSplit] at hsandwich
  rw [hfutureSplit] at hsandwich
  constructor
  · linarith [hsandwich.1]
  · nlinarith [hsandwich.2]

end

end Erdos1212Kernel
