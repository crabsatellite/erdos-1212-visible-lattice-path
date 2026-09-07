import Erdos1212Kernel.IwaniecRealPrimeInterval

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral Set

set_option maxHeartbeats 700000

/-- Literal real-endpoint weighted prime interval with the source's
coefficient-one error, including the initial endpoint B=2. -/
theorem exists_iwaniecLemma13_real_constant :
    ∃ C : Real, 0 < C ∧ ∀ (b : Real → Real) (B A : Real), 2 ≤ B → B ≤ A →
      MonotoneOn b (Icc B A) → (∀ x ∈ Icc B A, 0 ≤ b x) →
      |iwaniecPrimeReciprocalWeightedRealInterval b B A -
        (∫ x in B..A, b x / (x * Real.log x))| ≤
          C * b A * Real.exp (-Real.sqrt (Real.log B)) := by
  obtain ⟨C₀, hC₀, hnatural⟩ := exists_iwaniecLemma13_natural_two_constant
  let K := iwaniecRealEndpointConstant
  let C := C₀ + 2 * K
  have hK : 0 < K := iwaniecRealEndpointConstant_pos
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro b B A hB hBA hbMono hbNonneg
  have hB0 : 0 < B := by linarith
  have hA0 : 0 ≤ A := by linarith
  have hbA : 0 ≤ b A := hbNonneg A ⟨hBA, le_rfl⟩
  let N := Nat.ceil B
  let M := Nat.floor A
  have hBN : B ≤ (N : Real) := Nat.le_ceil B
  have hMA : (M : Real) ≤ A := Nat.floor_le hA0
  have hNshort : (N : Real) < B + 1 := Nat.ceil_lt_add_one hB0.le
  have hMshort : A < (M : Real) + 1 := Nat.lt_floor_add_one A
  have hsubmono {u v : Real} (hBu : B ≤ u) (hvA : v ≤ A) : MonotoneOn b (Icc u v) :=
    hbMono.mono (fun _ hx => ⟨hBu.trans hx.1, hx.2.trans hvA⟩)
  have hsubbound {u v : Real} (hBu : B ≤ u) (hvA : v ≤ A) :
      ∀ x ∈ Icc u v, 0 ≤ b x ∧ b x ≤ b A := by
    intro x hx
    have hxBA : x ∈ Icc B A := ⟨hBu.trans hx.1, hx.2.trans hvA⟩
    exact ⟨hbNonneg x hxBA, hbMono hxBA ⟨hBA, le_rfl⟩ hxBA.2⟩
  by_cases hNM : N ≤ M
  · have hNMreal : (N : Real) ≤ M := by exact_mod_cast hNM
    have hNA : (N : Real) ≤ A := hNMreal.trans hMA
    have hBM : B ≤ (M : Real) := hBN.trans hNMreal
    have hNtwo : 2 ≤ N := by exact_mod_cast hB.trans hBN
    have hnat := hnatural b N M hNtwo hNM (hsubmono hBN hMA)
      (fun x hx => (hsubbound hBN hMA x hx).1)
    have hweight : b M ≤ b A := hbMono ⟨hBM, hMA⟩ ⟨hBA, le_rfl⟩ hMA
    have hdecay : Real.exp (-Real.sqrt (Real.log (N : Real))) ≤ Real.exp (-Real.sqrt (Real.log B)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg (Real.sqrt_le_sqrt (Real.log_le_log hB0 hBN))
    have hnat' : |iwaniecPrimeReciprocalWeightedInterval (fun n => b n) N M -
        (∫ x in (N : Real)..(M : Real), b x / (x * Real.log x))| ≤
        C₀ * b A * Real.exp (-Real.sqrt (Real.log B)) := by
      exact hnat.trans (mul_le_mul (mul_le_mul_of_nonneg_left hweight hC₀.le) hdecay
        (Real.exp_pos _).le (mul_nonneg hC₀.le hbA))
    have hleft := iwaniecShortWeightedIntegral_source_bound b hB le_rfl hBN
      (show (N : Real) - B ≤ 1 by linarith) (hsubbound le_rfl hNA)
    have hright := iwaniecShortWeightedIntegral_source_bound b hB hBM hMA
      (show A - (M : Real) ≤ 1 by linarith) (hsubbound hBM le_rfl)
    have hiBN := iwaniecWeightedIntegral_intervalIntegrable b (show 1 < B by linarith)
      hBN (hsubmono le_rfl hNA)
    have hiNM := iwaniecWeightedIntegral_intervalIntegrable b (show 1 < (N : Real) by linarith)
      hNMreal (hsubmono hBN hMA)
    have hiMA := iwaniecWeightedIntegral_intervalIntegrable b (show 1 < (M : Real) by linarith)
      hMA (hsubmono hBM le_rfl)
    have hsplit1 := intervalIntegral.integral_add_adjacent_intervals hiBN hiNM
    have hsplit2 := intervalIntegral.integral_add_adjacent_intervals (hiBN.trans hiNM) hiMA
    have hdecomp : iwaniecPrimeReciprocalWeightedRealInterval b B A -
        (∫ x in B..A, b x / (x * Real.log x)) =
        (iwaniecPrimeReciprocalWeightedInterval (fun n => b n) N M -
          (∫ x in (N : Real)..(M : Real), b x / (x * Real.log x))) -
        (∫ x in B..(N : Real), b x / (x * Real.log x)) -
        (∫ x in (M : Real)..A, b x / (x * Real.log x)) := by
      rw [iwaniecWeightedRealInterval_eq_ceil_floor, ← hsplit2, ← hsplit1]
      ring
    rw [hdecomp]
    have htri := (abs_sub
      (iwaniecPrimeReciprocalWeightedInterval (fun n => b n) N M -
        (∫ x in (N : Real)..(M : Real), b x / (x * Real.log x)) -
        (∫ x in B..(N : Real), b x / (x * Real.log x)))
      (∫ x in (M : Real)..A, b x / (x * Real.log x))).trans
      (add_le_add (abs_sub _ _) le_rfl)
    have herr := htri.trans (add_le_add (add_le_add hnat' hleft) hright)
    convert herr using 1 <;> dsimp [C, K] <;> ring
  · have hMN : M < N := Nat.lt_of_not_ge hNM
    rw [iwaniecWeightedRealInterval_eq_zero_of_no_integer b hMN, zero_sub, abs_neg]
    have hlen : A - B ≤ 1 := by
      have hMNreal : (M : Real) + 1 ≤ N := by exact_mod_cast (show M + 1 ≤ N by omega)
      linarith only [hMshort, hMNreal, hNshort]
    have hshort := iwaniecShortWeightedIntegral_source_bound b hB le_rfl hBA hlen
      (hsubbound le_rfl le_rfl)
    have hKC : K ≤ C := by dsimp [C]; linarith
    exact hshort.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKC hbA)
      (Real.exp_pos _).le)

end

end Erdos1212Kernel
