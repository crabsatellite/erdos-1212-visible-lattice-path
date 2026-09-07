import Erdos1212Kernel.IwaniecLemma13Real
import Erdos1212Kernel.IwaniecPaperD2InnerSourceRate

namespace Erdos1212Kernel

noncomputable section

open MeasureTheory intervalIntegral Set

set_option maxHeartbeats 550000

def iwaniecClosedPrimeBand (B A : Real) : Finset Nat :=
  (Nat.primesLE (Nat.floor A)).filter (fun p : Nat => B ≤ (p : Real))

def iwaniecClosedPrimeReciprocalMass (B A : Real) : Real :=
  ∑ p ∈ iwaniecClosedPrimeBand B A, (p : Real)⁻¹

theorem mem_iwaniecClosedPrimeBand {B A : Real} (hA : 0 ≤ A) (p : Nat) :
    p ∈ iwaniecClosedPrimeBand B A ↔ p.Prime ∧ B ≤ (p : Real) ∧ (p : Real) ≤ A :=
  iwaniec_real_prime_interval_mem hA p

theorem iwaniecClosedPrimeReciprocalMass_eq_weighted (B A : Real) :
    iwaniecClosedPrimeReciprocalMass B A =
      iwaniecPrimeReciprocalWeightedRealInterval (fun _ => 1) B A := by
  unfold iwaniecClosedPrimeReciprocalMass iwaniecClosedPrimeBand iwaniecPrimeReciprocalWeightedRealInterval
  simp only [one_div]

theorem iwaniec_log_kernel_integral {a b : Real} (ha : 1 < a) (hab : a ≤ b) :
    (∫ x in a..b, 1 / (x * Real.log x)) = Real.log (Real.log b) - Real.log (Real.log a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    have hx1 : 1 < x := ha.trans_le hx.1
    have hx0 : x ≠ 0 := (zero_lt_one.trans hx1).ne'
    have hl0 : Real.log x ≠ 0 := (Real.log_pos hx1).ne'
    convert (Real.hasDerivAt_log hx0).log hl0 using 1 <;> field_simp <;> ring
  · exact iwaniecLogKernel_intervalIntegrable ha (ha.trans_le hab)

/-- Uniform reciprocal mass on the exact power interval containing
both primes of every nonzero d2 pair. The finite comparison into this
interval is supplied separately before it is consumed. -/
theorem exists_iwaniecPrimePowerBand_mass_bound :
    ∃ K : Real, 0 < K ∧ ∀ L : Real, 6 * Real.log 2 ≤ L →
      iwaniecClosedPrimeReciprocalMass (Real.exp (L / 6)) (Real.exp (L / 2)) ≤ K := by
  obtain ⟨C, hC, hsrc⟩ := exists_iwaniecLemma13_real_constant
  refine ⟨C + Real.log 3, add_pos hC (Real.log_pos (by norm_num)), ?_⟩
  intro L hL
  have hL0 : 0 < L := by have hh := Real.log_pos (show (1 : Real) < 2 by norm_num); linarith
  have hB : 2 ≤ Real.exp (L / 6) := by
    calc
      (2 : Real) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (L / 6) := Real.exp_le_exp.mpr (by linarith)
  have hBA : Real.exp (L / 6) ≤ Real.exp (L / 2) := Real.exp_le_exp.mpr (by linarith)
  have hh := hsrc (fun _ => 1) (Real.exp (L / 6)) (Real.exp (L / 2)) hB hBA
    (fun _ _ _ _ _ => le_rfl) (fun _ _ => by norm_num)
  have hmain : (∫ x in (Real.exp (L / 6))..(Real.exp (L / 2)), 1 / (x * Real.log x)) = Real.log 3 := by
    rw [iwaniec_log_kernel_integral (by linarith) hBA, Real.log_exp, Real.log_exp]
    rw [← Real.log_div (by positivity : L / 2 ≠ 0) (by positivity : L / 6 ≠ 0)]
    congr 1
    field_simp [hL0.ne']
    <;> ring
  rw [hmain, mul_one] at hh
  have he : Real.exp (-Real.sqrt (Real.log (Real.exp (L / 6)))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg _))
  have hbound := hh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left he hC.le)
  rw [← iwaniecClosedPrimeReciprocalMass_eq_weighted] at hbound
  have hu := (le_abs_self (iwaniecClosedPrimeReciprocalMass (Real.exp (L / 6)) (Real.exp (L / 2)) - Real.log 3)).trans hbound
  linarith

theorem iwaniec_log_level_sixtyfour {level : Real} (hy : 64 ≤ level) :
    6 * Real.log 2 ≤ Real.log level := by
  have hh := Real.log_le_log (by norm_num : (0 : Real) < 64) hy
  rw [show (64 : Real) = 2 ^ 6 by norm_num, Real.log_pow] at hh
  norm_num only [Nat.cast_ofNat] at hh
  exact hh

end

end Erdos1212Kernel
