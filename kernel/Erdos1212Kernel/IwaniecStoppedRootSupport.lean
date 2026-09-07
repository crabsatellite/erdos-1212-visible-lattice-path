import Erdos1212Kernel.IwaniecStoppedParameterTransport
import Erdos1212Kernel.IwaniecPaperABandRecursion

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem iwaniec_exp_log_div_nat_pow {level : Real} (hy : 0 < level) {m : Nat} (hm : 0 < m) :
    (Real.exp (Real.log level / (m : Real))) ^ m = level := by
  have hm0 : (m : Real) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  calc
    _ = Real.exp ((m : Real) * (Real.log level / (m : Real))) := (Real.exp_nat_mul _ m).symm
    _ = Real.exp (Real.log level) := by congr 1; field_simp [hm0]
    _ = level := Real.exp_log hy

theorem iwaniec_nat_root_band_iff {level : Real} (hy : 0 < level) {m : Nat} (hm : 0 < m) (p : Nat) :
    level ≤ (p : Real) ^ m ↔ Real.exp (Real.log level / (m : Real)) ≤ (p : Real) := by
  have hroot := iwaniec_exp_log_div_nat_pow hy hm
  constructor
  · intro hh
    by_contra hn
    have hp := pow_lt_pow_left₀ (lt_of_not_ge hn) (Nat.cast_nonneg p : (0 : Real) ≤ p) (Nat.ne_of_gt hm)
    rw [hroot] at hp
    exact (not_lt_of_ge hh) hp
  · intro hh
    have hp := pow_le_pow_left₀ (Real.exp_pos _).le hh m
    rwa [hroot] at hp

theorem iwaniecPaperStoppedLayer_first_prime_root_band {level : Real} (hy : 0 < level)
    (offset : Nat) (z : Real) (k : Nat) :
    iwaniecPaperStoppedLayer offset level z (k + 1) =
      ∑ p ∈ iwaniecStrictPrimeBand (Real.exp (Real.log level / ((k + 3 : Nat) : Real))) z,
        if Even offset ∨ (p : Real) ^ 3 < level then
          (p : Real)⁻¹ * iwaniecPaperStoppedLayer (offset + 1) (level / p) p k
        else if k = 0 then (p : Real)⁻¹ * iwaniecPaperR (p : Real) else 0 := by
  classical
  rw [iwaniecPaperStoppedLayer_first_prime_power_band]
  apply Finset.sum_congr
  · ext p
    simp only [iwaniecStrictPrimeBand, Finset.mem_filter, iwaniec_nat_root_band_iff hy (by omega : 0 < k + 3) p]
  · intro p hp
    rfl

theorem iwaniecPaperStoppedLayer_zero_of_parameter (rank offset : Nat) {level s : Real}
    (hy : 1 < level) (hs : (rank : Real) + 2 ≤ s) :
    iwaniecPaperStoppedLayer offset level (Real.exp (Real.log level / s)) rank = 0 := by
  apply iwaniecPaperStoppedLayer_eq_zero_of_power
  have hs0 : 0 < s := by have hr0 : (0 : Real) ≤ rank := Nat.cast_nonneg rank; linarith
  have hsr : ((rank + 2 : Nat) : Real) ≤ s := by simpa only [Nat.cast_add, Nat.cast_ofNat] using hs
  calc
    _ = Real.exp (((rank + 2 : Nat) : Real) * (Real.log level / s)) := (Real.exp_nat_mul _ (rank + 2)).symm
    _ ≤ Real.exp (Real.log level) := by
      apply Real.exp_le_exp.mpr
      rw [← mul_div_assoc, div_le_iff₀ hs0]
      have hh := mul_le_mul_of_nonneg_right hsr (Real.log_pos hy).le
      nlinarith only [hh]
    _ = level := Real.exp_log (zero_lt_one.trans hy)

theorem iwaniecPaperD_zero_of_parameter (rank : Nat) {level s : Real}
    (hy : 1 < level) (hs : (rank : Real) + 2 ≤ s) : iwaniecPaperD rank level s = 0 := by
  unfold iwaniecPaperD
  by_cases hr : Even rank
  · simp only [if_pos hr]
    exact iwaniecPaperStoppedLayer_zero_of_parameter rank 0 hy hs
  · simp only [if_neg hr]
    exact iwaniecPaperStoppedLayer_zero_of_parameter rank 1 hy (hs.trans (le_max_right 3 s))

theorem iwaniecPaperQ_zero_of_parameter (rank : Nat) {level s : Real}
    (hy : 1 < level) (hs : (rank : Real) + 2 ≤ s) : iwaniecPaperQ rank level s = 0 := by
  unfold iwaniecPaperQ
  apply Finset.sum_eq_zero
  intro k hk
  have hkr : k ≤ rank := by have hh := Finset.mem_range.mp hk; omega
  have hkrR : (k : Real) ≤ rank := by exact_mod_cast hkr
  have hsk : (k : Real) + 2 ≤ s := by linarith
  split
  · exact iwaniecPaperD_zero_of_parameter k hy hsk
  · rfl

/-- A first prime below the paper's rank-dependent root gives a child
parameter beyond the entire support of the child d/Q mass. -/
theorem iwaniecStoppedChild_parameter_below_root (rank : Nat) {level : Real} (hy : 1 < level)
    {p : Nat} (hp : p.Prime)
    (hsmall : (p : Real) < Real.exp (Real.log level / ((rank + 3 : Nat) : Real))) :
    (rank : Real) + 2 ≤ Real.log level / Real.log (p : Real) - 1 := by
  have hp0 : (0 : Real) < p := by exact_mod_cast hp.pos
  have hp1 : (1 : Real) < p := by exact_mod_cast hp.one_lt
  have hlog := Real.log_lt_log hp0 hsmall
  rw [Real.log_exp] at hlog
  have hden : (0 : Real) < (rank + 3 : Nat) := by positivity
  have hprod := (lt_div_iff₀ hden).mp hlog
  have ht : ((rank + 3 : Nat) : Real) < Real.log level / Real.log (p : Real) :=
    (lt_div_iff₀ (Real.log_pos hp1)).mpr (by nlinarith only [hprod])
  norm_num only [Nat.cast_add, Nat.cast_ofNat] at ht
  linarith only [ht]

end

end Erdos1212Kernel
