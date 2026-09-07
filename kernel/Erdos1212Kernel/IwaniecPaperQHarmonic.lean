import Erdos1212Kernel.IwaniecStoppedWordHarmonic
import Erdos1212Kernel.IwaniecAuxiliaryMonotonicity

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem iwaniecPaperCutoff_prime_square_lt {level s : Real} (hy : 1 < level) (hs : 2 ≤ s)
    {p : Nat} (hp : p ∈ iwaniecStrictPrimePool (Real.exp (Real.log level / s))) : (p : Real) ^ 2 < level := by
  have hcutoff := Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (Real.log_pos hy).le (by norm_num : (0 : Real) < 2) hs)
  have hlt := (mem_iwaniecStrictPrimePool.mp hp).2.trans_le hcutoff
  have hpow := pow_lt_pow_left₀ hlt (Nat.cast_nonneg p : (0 : Real) ≤ p) (by norm_num : (2 : Nat) ≠ 0)
  have hroot : (Real.exp (Real.log level / 2)) ^ 2 = level := by
    simpa only [Nat.cast_ofNat] using iwaniec_exp_log_div_nat_pow (zero_lt_one.trans hy) (by norm_num : 0 < (2 : Nat))
  rwa [hroot] at hpow

theorem iwaniecStoppedWordSupport_even_product {level z : Real} (hy : 1 < level)
    (hcutoff : ∀ p ∈ iwaniecStrictPrimePool z, (p : Real) ^ 2 < level) (rank : Nat)
    (word : List Nat) (hw : word ∈ iwaniecStoppedWordSupport 0 level z rank) : (word.prod : Real) < level := by
  have hd := iwaniecStoppedWordSupport_data hw
  have hp : ∀ p ∈ word, 0 < p := fun p h => (hd.1 p h).1.pos
  have hsq : ∀ p ∈ word, (p : Real) ^ 2 < level := fun p h => hcutoff p (mem_iwaniecStrictPrimePool.mpr (hd.1 p h))
  exact (iwaniecCubicStoppedWord_product_bounds word hp hd.2.1 level hy).1 hd.2.2 hsq

theorem iwaniecStoppedWordSupport_odd_product {level z : Real} (hy : 1 < level)
    (hcutoff : ∀ p ∈ iwaniecStrictPrimePool z, (p : Real) ^ 3 < level) (rank : Nat)
    (word : List Nat) (hw : word ∈ iwaniecStoppedWordSupport 1 level z rank) : (word.prod : Real) < level := by
  have hd := iwaniecStoppedWordSupport_data hw
  have hp : ∀ p ∈ word, 0 < p := fun p h => (hd.1 p h).1.pos
  have hc : ∀ p ∈ word, (p : Real) ^ 3 < level := fun p h => hcutoff p (mem_iwaniecStrictPrimePool.mpr (hd.1 p h))
  exact (iwaniecCubicStoppedWord_product_bounds word hp hd.2.1 level hy).2 hd.2.2 hc

/-- Source equation (4.8), with the actual Q mass. Every product and
weight premise of the generic harmonic comparison is discharged here. -/
theorem iwaniecPaperQ_add_one_le_harmonic (rank : Nat) {level s : Real}
    (hy : 1 < level) (hs : iwaniecAuxGStart rank ≤ s) :
    iwaniecPaperQ rank level s + 1 ≤ (harmonic (Nat.floor level) : Real) := by
  by_cases hr : Even rank
  · have hs2 : 2 ≤ s := by simpa only [iwaniecAuxGStart, if_pos hr] using hs
    rw [iwaniecPaperQ_even_eq_partial hr]
    apply iwaniecStoppedPartial_add_one_le_harmonic 0 rank hy
    exact iwaniecStoppedWordSupport_even_product hy
      (fun p hp => iwaniecPaperCutoff_prime_square_lt hy hs2 hp) rank
  · rw [iwaniecPaperQ_odd_eq_partial hr]
    apply iwaniecStoppedPartial_add_one_le_harmonic 1 rank hy
    exact iwaniecStoppedWordSupport_odd_product hy
      (fun p hp => iwaniecPaperCutoff_prime_cube_lt hy (le_max_left 3 s) hp) rank

theorem iwaniecPaperQ_lt_harmonic (rank : Nat) {level s : Real}
    (hy : 1 < level) (hs : iwaniecAuxGStart rank ≤ s) :
    iwaniecPaperQ rank level s < (harmonic (Nat.floor level) : Real) := by
  have hh := iwaniecPaperQ_add_one_le_harmonic rank hy hs
  linarith

theorem iwaniecPaperQ_lt_one_add_log (rank : Nat) {level s : Real}
    (hy : 1 < level) (hs : iwaniecAuxGStart rank ≤ s) :
    iwaniecPaperQ rank level s < 1 + Real.log level :=
  (iwaniecPaperQ_lt_harmonic rank hy hs).trans_le (harmonic_floor_le_one_add_log level hy.le)

theorem iwaniecPaperQ_bounded_level_log_bound (rank : Nat) {level Y s : Real}
    (hy : 1 < level) (hY : level ≤ Y) (hs : iwaniecAuxGStart rank ≤ s) :
    iwaniecPaperQ rank level s < 1 + Real.log Y := by
  have hh := iwaniecPaperQ_lt_one_add_log rank hy hs
  have hlog := Real.log_le_log (zero_lt_one.trans hy) hY
  linarith

end

end Erdos1212Kernel
