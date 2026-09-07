import Erdos1212Kernel.IwaniecLemma14Initial

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

def iwaniecPrimeLogReciprocalRealInterval (B A : Real) : Real :=
  ∑ p ∈ (Nat.primesLE (Nat.floor A)).filter (fun p : Nat => B ≤ (p : Real)),
    1 / ((p : Real) * Real.log (p : Real))

theorem iwaniecPrimeLogReciprocalRealInterval_eq_ceil_floor (B A : Real) :
    iwaniecPrimeLogReciprocalRealInterval B A =
      iwaniecPrimeLogReciprocalNatInterval (Nat.ceil B) (Nat.floor A) := by
  unfold iwaniecPrimeLogReciprocalRealInterval iwaniecPrimeLogReciprocalNatInterval
  apply Finset.sum_congr
  · ext p
    simp only [Finset.mem_filter, Nat.ceil_le]
  · intro p hp
    rfl

/-- Literal Lemma 14, for every pair of real endpoints a>=b>=2,
with one absolute constant and the exact exp(-sqrt(log b)) rate. -/
theorem exists_iwaniecLemma14_real_constant :
    ∃ C : Real, 0 < C ∧ ∀ B A : Real, 2 ≤ B → B ≤ A →
      |iwaniecPrimeLogReciprocalRealInterval B A -
        ((Real.log B)⁻¹ - (Real.log A)⁻¹)| ≤
          C * Real.exp (-Real.sqrt (Real.log B)) := by
  obtain ⟨C₀, hC₀, hnat⟩ := exists_iwaniecLemma14_natural_two_constant
  let C : Real := C₀ + 16 * Real.exp 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro B A hB hBA
  have hB0 : 0 < B := by linarith
  have hA0 : 0 < A := hB0.trans_le hBA
  let N := Nat.ceil B
  let M := Nat.floor A
  have hBN : B ≤ (N : Real) := Nat.le_ceil B
  have hMA : (M : Real) ≤ A := Nat.floor_le hA0.le
  have hNshort : (N : Real) < B + 1 := Nat.ceil_lt_add_one hB0.le
  have hMshort : A < (M : Real) + 1 := Nat.lt_floor_add_one A
  have hN2 : 2 ≤ N := by exact_mod_cast hB.trans hBN
  have hround : 8 / B ≤ 8 * Real.exp 1 * Real.exp (-Real.sqrt (Real.log B)) := by
    have hh := mul_le_mul_of_nonneg_left
      (iwaniec_inverse_le_sqrt_log_exponential (show 1 ≤ B by linarith)) (by norm_num : (0 : Real) ≤ 8)
    convert hh using 1 <;> ring
  rw [iwaniecPrimeLogReciprocalRealInterval_eq_ceil_floor]
  change |iwaniecPrimeLogReciprocalNatInterval N M -
    ((Real.log B)⁻¹ - (Real.log A)⁻¹)| ≤ C * Real.exp (-Real.sqrt (Real.log B))
  by_cases hNM : N ≤ M
  · have hNMreal : (N : Real) ≤ M := by exact_mod_cast hNM
    have hh := hnat N M hN2 hNM
    have hdecay : Real.exp (-Real.sqrt (Real.log (N : Real))) ≤ Real.exp (-Real.sqrt (Real.log B)) :=
      Real.exp_le_exp.mpr (neg_le_neg (Real.sqrt_le_sqrt (Real.log_le_log hB0 hBN)))
    have hsrc : |iwaniecPrimeLogReciprocalNatInterval N M -
        ((Real.log (N : Real))⁻¹ - (Real.log (M : Real))⁻¹)| ≤
        C₀ * Real.exp (-Real.sqrt (Real.log B)) :=
      hh.trans (mul_le_mul_of_nonneg_left hdecay hC₀.le)
    have hleft : |(Real.log (N : Real))⁻¹ - (Real.log B)⁻¹| ≤ 8 / B := by
      rw [abs_sub_comm]
      exact (iwaniec_log_reciprocal_nearby_two hB (by linarith) hBN).trans
        (div_le_div_of_nonneg_left (by norm_num) hB0 hBN)
    have hM2 : (2 : Real) ≤ M := hB.trans (hBN.trans hNMreal)
    have hright : |(Real.log (M : Real))⁻¹ - (Real.log A)⁻¹| ≤ 8 / B :=
      (iwaniec_log_reciprocal_nearby_two hM2 (by linarith) hMA).trans
        (div_le_div_of_nonneg_left (by norm_num) hB0 hBA)
    have hsplit : iwaniecPrimeLogReciprocalNatInterval N M -
        ((Real.log B)⁻¹ - (Real.log A)⁻¹) =
        (iwaniecPrimeLogReciprocalNatInterval N M -
          ((Real.log (N : Real))⁻¹ - (Real.log (M : Real))⁻¹)) +
        ((Real.log (N : Real))⁻¹ - (Real.log B)⁻¹) -
        ((Real.log (M : Real))⁻¹ - (Real.log A)⁻¹) := by ring
    rw [hsplit]
    calc
      _ ≤ |(iwaniecPrimeLogReciprocalNatInterval N M -
          ((Real.log (N : Real))⁻¹ - (Real.log (M : Real))⁻¹)) +
          ((Real.log (N : Real))⁻¹ - (Real.log B)⁻¹)| +
          |(Real.log (M : Real))⁻¹ - (Real.log A)⁻¹| := abs_sub _ _
      _ ≤ (|iwaniecPrimeLogReciprocalNatInterval N M -
          ((Real.log (N : Real))⁻¹ - (Real.log (M : Real))⁻¹)| +
          |(Real.log (N : Real))⁻¹ - (Real.log B)⁻¹|) +
          |(Real.log (M : Real))⁻¹ - (Real.log A)⁻¹| := add_le_add (abs_add_le _ _) le_rfl
      _ ≤ (C₀ * Real.exp (-Real.sqrt (Real.log B)) +
          8 * Real.exp 1 * Real.exp (-Real.sqrt (Real.log B))) +
          8 * Real.exp 1 * Real.exp (-Real.sqrt (Real.log B)) :=
        add_le_add (add_le_add hsrc (hleft.trans hround)) (hright.trans hround)
      _ = _ := by dsimp [C]; ring
  · have hMN : M < N := Nat.lt_of_not_ge hNM
    rw [iwaniecPrimeLogReciprocalNatInterval_eq_zero_of_lt hMN, zero_sub, abs_neg]
    have hMNreal : (M : Real) + 1 ≤ N := by exact_mod_cast (show M + 1 ≤ N by omega)
    have hshort : A - 1 ≤ B := by linarith
    have hsmall : |(Real.log B)⁻¹ - (Real.log A)⁻¹| ≤ 8 / B :=
      (iwaniec_log_reciprocal_nearby_two hB hshort hBA).trans
        (div_le_div_of_nonneg_left (by norm_num) hB0 hBA)
    have hcoef : 8 * Real.exp 1 ≤ C := by dsimp [C]; linarith [Real.exp_pos (1 : Real)]
    exact hsmall.trans (hround.trans (mul_le_mul_of_nonneg_right hcoef (Real.exp_pos _).le))

end

end Erdos1212Kernel
