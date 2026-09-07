import Erdos1212Kernel.IwaniecParityProfileRecursion
import Erdos1212Kernel.IwaniecEffectiveWeightedCorollaries

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem iwaniecPaperQChild_main_eq_source (rank : Nat) {level : Real}
    (hy : 1 < level) {p : Nat} (hp : p.Prime) :
    iwaniecPaperQChildMainTerm rank level p =
      iwaniecParityReciprocalLogWeight rank (Real.log level) p / (p : Real) := by
  have hp0 : (0 : Real) < p := by exact_mod_cast hp.pos
  unfold iwaniecPaperQChildMainTerm
  rw [iwaniecPaperChild_logParameter (zero_lt_one.trans hy) hp,
    Real.log_div (zero_lt_one.trans hy).ne' hp0.ne']
  rfl

theorem iwaniecCorollaryOneMain_exp_endpoints (rank : Nat) {L s T : Real}
    (hL : L ≠ 0) (hs : s ≠ 0) (hT : T ≠ 0) :
    iwaniecCorollaryOneMain rank L (Real.exp (L / T)) (Real.exp (L / s)) =
      (∫ t in s..T, iwaniecParitySieveProfile rank (t - 1) / (t - 1)) / L := by
  have hqs : L / (L / s) = s := by field_simp [hL, hs]
  have hqT : L / (L / T) = T := by field_simp [hL, hT]
  unfold iwaniecCorollaryOneMain
  rw [Real.log_exp, Real.log_exp, hqs, hqT]
  ring

/-- Effective Corollary 1 on the exact Q band. The xi-1 lower cutoff
is included into the real-endpoint xi interval, and its orientation is
proved before the finite integral is used. -/
theorem exists_iwaniecPaperQBand_child_main_integral_bound :
    ∃ K : Real, 0 < K ∧ ∀ (rank : Nat) (level s : Real), 1 < level →
      iwaniecAuxSZero ≤ iwaniecPaperXi level →
      iwaniecCorollaryThreeDomainStart rank ≤ s → s ≤ iwaniecPaperXi level →
      (∑ p ∈ iwaniecStrictPrimeBand
        (Real.exp (Real.log level / (iwaniecPaperXi level - 1))) (Real.exp (Real.log level / s)),
        iwaniecPaperQChildMainTerm rank level p) ≤
      (∫ t in s..iwaniecPaperXi level, iwaniecParitySieveProfile rank (t - 1) / (t - 1)) / Real.log level +
        K * iwaniecParityReciprocalLogWeight rank (Real.log level) (Real.exp (Real.log level / s)) *
          Real.exp (-Real.sqrt (Real.log level / iwaniecPaperXi level)) := by
  obtain ⟨K, hK, hsource⟩ := exists_iwaniecPrimeWeightedCorollaryOne_effective
  refine ⟨K, hK, ?_⟩
  intro rank level s hy hξ hs hsξ
  have hL := Real.log_pos hy
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  have hs0 : 0 < s := by linarith
  have hξ0 : 0 < iwaniecPaperXi level := by linarith [iwaniecAuxSZero_large]
  have hξsub : 0 < iwaniecPaperXi level - 1 := by linarith [iwaniecAuxSZero_large]
  let B := Real.exp (Real.log level / iwaniecPaperXi level)
  let A := Real.exp (Real.log level / s)
  let R := Real.exp (Real.log level / (iwaniecPaperXi level - 1))
  have hB : 2 ≤ B := iwaniecCorollaryThree_left_cutoff_two hy hξ
  have hBA : B ≤ A := Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hL.le hs0 hsξ)
  have hBR : B ≤ R := Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hL.le hξsub (by linarith))
  have hstart : 0 < iwaniecParityProfileStart rank + 1 := by
    linarith [one_le_iwaniecParityProfileStart rank]
  have hcut : A ≤ Real.exp (Real.log level / (iwaniecParityProfileStart rank + 1)) :=
    Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hL.le hstart hs)
  have hnonneg : ∀ x ∈ Set.Icc B A, 0 ≤ iwaniecParityReciprocalLogWeight rank (Real.log level) x := by
    intro x hx
    exact iwaniecParityReciprocalLogWeight_nonneg rank hL
      ⟨by linarith [hx.1], hx.2.trans hcut⟩
  have hsum := iwaniecStrictPrimeBand_weighted_le_real
    (iwaniecParityReciprocalLogWeight rank (Real.log level)) hB hBA hBR hnonneg
  have heq : (∑ p ∈ iwaniecStrictPrimeBand R A, iwaniecPaperQChildMainTerm rank level p) =
      ∑ p ∈ iwaniecStrictPrimeBand R A, iwaniecParityReciprocalLogWeight rank (Real.log level) p / (p : Real) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact iwaniecPaperQChild_main_eq_source rank hy
      (mem_iwaniecStrictPrimePool.mp (Finset.mem_filter.mp hp).1).1
  have hsourceBound := hsource rank (Real.log level) B A hL hB hBA hcut
  have hupper := (le_abs_self
    (iwaniecPrimeReciprocalWeightedRealInterval (iwaniecParityReciprocalLogWeight rank (Real.log level)) B A -
      iwaniecCorollaryOneMain rank (Real.log level) B A)).trans hsourceBound
  rw [iwaniecCorollaryOneMain_exp_endpoints rank hL.ne' hs0.ne' hξ0.ne'] at hupper
  dsimp only [B] at hupper
  rw [Real.log_exp] at hupper
  rw [heq]
  linarith only [hsum, hupper]

/-- The full successor profile now consumes the finite main integral,
with the matching g2 correction ready for Lemma 16. -/
theorem exists_iwaniecPaperQBand_child_main_profile_bound :
    ∃ K : Real, 0 < K ∧ ∀ (rank : Nat) (level s : Real), 1 < level →
      iwaniecAuxSZero ≤ iwaniecPaperXi level →
      iwaniecCorollaryThreeDomainStart rank ≤ s → s ≤ iwaniecPaperXi level →
      (∑ p ∈ iwaniecStrictPrimeBand
        (Real.exp (Real.log level / (iwaniecPaperXi level - 1))) (Real.exp (Real.log level / s)),
        iwaniecPaperQChildMainTerm rank level p) +
        (if Even (rank + 1) then iwaniecGTwo s else 0) / Real.log level ≤
      iwaniecParitySieveProfile (rank + 1) s / Real.log level +
        K * iwaniecParityReciprocalLogWeight rank (Real.log level) (Real.exp (Real.log level / s)) *
          Real.exp (-Real.sqrt (Real.log level / iwaniecPaperXi level)) := by
  obtain ⟨K, hK, hmain⟩ := exists_iwaniecPaperQBand_child_main_integral_bound
  refine ⟨K, hK, ?_⟩
  intro rank level s hy hξ hs hsξ
  have hm := hmain rank level s hy hξ hs hsξ
  have hp := div_le_div_of_nonneg_right
    (iwaniecParitySieveProfile_finite_integral_bound rank hs hsξ
      (by linarith [iwaniecAuxSZero_large] : 4 ≤ iwaniecPaperXi level)) (Real.log_pos hy).le
  rw [add_div] at hp
  linarith only [hm, hp]

end

end Erdos1212Kernel
