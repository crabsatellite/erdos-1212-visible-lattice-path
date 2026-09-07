import Erdos1212Kernel.IwaniecLemma14Strict

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 500000

/-- The inner logarithmic sum in the displayed proof of Lemma 16,
with the original failed cubic condition and strict second-prime cutoff. -/
def iwaniecPaperD2LogInner (level : Real) (p : Nat) : Real :=
  ∑ q ∈ iwaniecStrictPrimePool (p : Real),
    if level / p ≤ (q : Real) ^ 3 then 1 / ((q : Real) * Real.log (q : Real)) else 0

theorem iwaniec_exp_log_third_cube {u : Real} (hu : 0 < u) :
    (Real.exp (Real.log u / 3)) ^ 3 = u := by
  calc
    _ = Real.exp (3 * (Real.log u / 3)) := (Real.exp_nat_mul _ 3).symm
    _ = Real.exp (Real.log u) := by congr 1; ring
    _ = u := Real.exp_log hu

theorem iwaniec_cube_root_band_iff {u : Real} (hu : 0 < u) (q : Nat) :
    u ≤ (q : Real) ^ 3 ↔ Real.exp (Real.log u / 3) ≤ (q : Real) := by
  have hc := iwaniec_exp_log_third_cube hu
  constructor
  · intro h
    by_contra hn
    have hp := pow_lt_pow_left₀ (lt_of_not_ge hn) (Nat.cast_nonneg q : (0 : Real) ≤ q) (by norm_num : (3 : Nat) ≠ 0)
    rw [hc] at hp
    exact (not_lt_of_ge h) hp
  · intro h
    have hp := pow_le_pow_left₀ (Real.exp_pos _).le h 3
    rwa [hc] at hp

theorem iwaniecPaperD2LogInner_eq_strictInterval {level : Real} (p : Nat)
    (hu : 0 < level / p) :
    iwaniecPaperD2LogInner level p =
      iwaniecPrimeLogReciprocalStrictInterval (Real.exp (Real.log (level / p) / 3)) p := by
  classical
  unfold iwaniecPaperD2LogInner iwaniecPrimeLogReciprocalStrictInterval
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [iwaniec_cube_root_band_iff hu q]

/-- Consume Lemma 14 in the actual inner sum of Lemma 16. These are
analytic domain conditions, not a new estimate supplied as a premise. -/
theorem exists_iwaniecPaperD2LogInner_unit_error :
    ∃ C : Real, 0 < C ∧ ∀ (level : Real) (p : Nat), p.Prime →
      8 ≤ level / p → level ≤ (p : Real) ^ 4 →
      |iwaniecPaperD2LogInner level p -
        (3 / Real.log (level / p) - (Real.log (p : Real))⁻¹)| ≤
          C * Real.exp (-Real.sqrt (Real.log (level / p) / 3)) := by
  obtain ⟨C, hC, hstrict⟩ := exists_iwaniecLemma14_strict_prime_upper_constant
  refine ⟨C, hC, ?_⟩
  intro level p hp hu8 hquartic
  have hp0 : (0 : Real) < p := by exact_mod_cast hp.pos
  have hu0 : 0 < level / p := by linarith
  let B := Real.exp (Real.log (level / p) / 3)
  have hcube : B ^ 3 = level / p := iwaniec_exp_log_third_cube hu0
  have hB0 : 0 < B := Real.exp_pos _
  have hB2 : 2 ≤ B := by
    by_contra hn
    have hh := pow_lt_pow_left₀ (lt_of_not_ge hn) hB0.le (by norm_num : (3 : Nat) ≠ 0)
    rw [hcube] at hh
    norm_num only [show (2 : Real) ^ 3 = 8 by norm_num] at hh
    linarith
  have hchild : level / p ≤ (p : Real) ^ 3 := by
    apply (div_le_iff₀ hp0).mpr
    convert hquartic using 1 <;> ring
  have hBp : B ≤ (p : Real) := (iwaniec_cube_root_band_iff hu0 p).mp hchild
  have hh := hstrict B p hp hB2 hBp
  have hlog : Real.log B = Real.log (level / p) / 3 := Real.log_exp _
  have hinv : (Real.log (level / p) / 3)⁻¹ = 3 / Real.log (level / p) := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  rw [hlog, hinv] at hh
  rw [iwaniecPaperD2LogInner_eq_strictInterval p hu0]
  exact hh

end

end Erdos1212Kernel
