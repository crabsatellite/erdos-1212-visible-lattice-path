import Erdos1212Kernel.IwaniecCorollaryThreeHigh
import Erdos1212Kernel.IwaniecCorollaryThreeLow
import Erdos1212Kernel.IwaniecCorollaryThreeSmallWeight
import Erdos1212Kernel.IwaniecRealPrimeIntervalBounds

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 700000

theorem iwaniecCorollaryThree_two_piece_bound {F T₀ T a b : Real}
    (hF : 0 ≤ F) (hT : T₀ ≤ T) (ha : 0 ≤ a) :
    F * T₀ * (1 + a) + F * ((T - T₀) + b * T) ≤ F * T * (1 + a + b) := by
  have hh := mul_le_mul_of_nonneg_left hT (mul_nonneg hF ha)
  nlinarith only [hh]

/-- The two cases of the actual Corollary 3 prime estimate, on the
shifted-G domain used by the count recursions. The scan's lower endpoint
is different and is not silently identified with this checked domain. -/
theorem exists_iwaniecCorollaryThree_exactDomain_constant :
    ∃ C : Real, 0 < C ∧ ∀ (rank : Nat) (level s : Real), 1 < level →
      iwaniecAuxSZero ≤ iwaniecPaperXi level →
      iwaniecCorollaryThreeDomainStart rank ≤ s → s ≤ iwaniecPaperXi level →
      iwaniecCorollaryThreePrimeSum rank level s ≤
        (iwaniecAuxWeightPower level (max iwaniecAuxSZero s) * iwaniecAuxG (rank + 1) s /
          Real.log level ^ 2) *
        (1 + 100 * C * iwaniecPaperXi level ^ 2 *
          Real.exp (-Real.sqrt (Real.log level / iwaniecPaperXi level))) := by
  obtain ⟨Ch, hCh, hhigh⟩ := exists_iwaniecCorollaryThree_high_constant
  obtain ⟨Cl, _hCl, hlow⟩ := exists_iwaniecCorollaryThree_low_constant
  let C := max Ch Cl
  have hC : 0 < C := hCh.trans_le (le_max_left _ _)
  have hChC : Ch ≤ C := le_max_left _ _
  have hClC : Cl ≤ C := le_max_right _ _
  refine ⟨C, hC, ?_⟩
  intro rank level s hy hξ hs hsξ
  let L := Real.log level
  let ξ := iwaniecPaperXi level
  let E := Real.exp (-Real.sqrt (L / ξ))
  let D := ξ ^ 2 * E
  have hD : 0 ≤ D := mul_nonneg (sq_nonneg ξ) (Real.exp_pos _).le
  have hL : 0 < L := Real.log_pos hy
  have hs2 := (iwaniecCorollaryThreeDomainStart_bounds rank).1.trans hs
  have hspos : 0 < s := by linarith
  have hs0pos : 0 < iwaniecAuxSZero := by linarith [iwaniecAuxSZero_large]
  have hG : 0 ≤ iwaniecAuxG (rank + 1) s := (iwaniecAuxG_pos (rank + 1) hs2).le
  by_cases hbig : iwaniecAuxSZero ≤ s
  · rw [max_eq_right hbig]
    have hh := hhigh rank level s hy hbig hsξ
    have hcoeff : 1 + 20 * Ch * D ≤ 1 + 100 * C * D := by
      have hc : 20 * Ch ≤ 100 * C := by linarith
      have hm := mul_le_mul_of_nonneg_right hc hD
      linarith only [hm]
    have hfactor : 0 ≤ iwaniecAuxTau rank level s / L ^ 2 :=
      div_nonneg (iwaniecAuxTau_pos rank level hs2).le (sq_nonneg L)
    have hscaled := mul_le_mul_of_nonneg_left hcoeff hfactor
    have hh' : iwaniecCorollaryThreePrimeSum rank level s ≤
        (iwaniecAuxTau rank level s / L ^ 2) * (1 + 20 * Ch * D) := by
      convert hh using 1 <;> dsimp [D, E, L, ξ] <;> ring
    have hresult := hh'.trans hscaled
    convert hresult using 1 <;> dsimp [iwaniecAuxTau, D, E, L, ξ] <;> ring
  · have hsmall : s ≤ iwaniecAuxSZero := le_of_not_ge hbig
    rw [max_eq_left hsmall]
    let B := iwaniecExpReciprocalScale L ξ
    let M := iwaniecExpReciprocalScale L iwaniecAuxSZero
    let A := iwaniecExpReciprocalScale L s
    let w := iwaniecCorollaryThreePrimeWeight rank level
    let v := iwaniecAuxPrimeSquaredWeight rank level
    let F := iwaniecAuxWeightPower level iwaniecAuxSZero
    let T₀ := iwaniecAuxG (rank + 1) iwaniecAuxSZero / L ^ 2
    let T := iwaniecAuxG (rank + 1) s / L ^ 2
    have hF : 0 ≤ F := (iwaniecAuxWeightPower_pos level (by linarith [iwaniecAuxSZero_large])).le
    have hT : 0 ≤ T := div_nonneg hG (sq_nonneg L)
    have hB : 2 ≤ B := iwaniecCorollaryThree_left_cutoff_two hy hξ
    have hBM : B ≤ M := Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hL.le hs0pos hξ)
    have hMA : M ≤ A := Real.exp_le_exp.mpr (div_le_div_of_nonneg_left hL.le hspos hsmall)
    have hsplit := iwaniecWeightedRealInterval_split_upper w hB hBM hMA
      (fun x hx => (iwaniecCorollaryThreePrimeWeight_pos_exactDomain rank hy hs hsξ hx).le)
    have hsmallweight := iwaniecWeightedRealInterval_mono_scaled w v (hB.trans hBM) hMA
      (fun x hx => iwaniecCorollaryThreePrimeWeight_small_bound rank hy hs hsmall hx)
    have hhigh0 := hhigh rank level iwaniecAuxSZero hy le_rfl hξ
    have hhigh' : iwaniecPrimeReciprocalWeightedRealInterval w B M ≤ F * T₀ * (1 + 20 * Ch * D) := by
      convert hhigh0 using 1 <;> dsimp [iwaniecCorollaryThreePrimeSum, iwaniecAuxTau, w, B, M, F, T₀, D, E, L, ξ] <;> ring
    have hlow0 := hlow rank level s hy hs hsmall hξ
    have hlow' : iwaniecPrimeReciprocalWeightedRealInterval v M A ≤ (T - T₀) + 32 * Cl * D * T := by
      convert hlow0 using 1 <;> dsimp [v, M, A, T, T₀, D, E, L, ξ] <;> ring
    have hGstart : iwaniecAuxGStart (rank + 1) ≤ s := by
      unfold iwaniecAuxGStart
      split_ifs <;> linarith only [hs2]
    have hGorder := iwaniecAuxG_antitoneOn_exactDomain (rank + 1) hGstart (hGstart.trans hsmall) hsmall
    have hTorder : T₀ ≤ T := div_le_div_of_nonneg_right hGorder (sq_nonneg L)
    have hpieces := iwaniecCorollaryThree_two_piece_bound (b := 32 * Cl * D) hF hTorder
      (show 0 ≤ 20 * Ch * D by positivity)
    have hcoeff : 1 + 20 * Ch * D + 32 * Cl * D ≤ 1 + 100 * C * D := by
      have hc : 20 * Ch + 32 * Cl ≤ 100 * C := by linarith
      have hm := mul_le_mul_of_nonneg_right hc hD
      nlinarith only [hm]
    have hfinal := mul_le_mul_of_nonneg_left hcoeff (mul_nonneg hF hT)
    have hsum : iwaniecCorollaryThreePrimeSum rank level s ≤
        F * T₀ * (1 + 20 * Ch * D) + F * ((T - T₀) + 32 * Cl * D * T) := by
      exact hsplit.trans (add_le_add hhigh' (hsmallweight.trans (mul_le_mul_of_nonneg_left hlow' hF)))
    have hresult := hsum.trans (hpieces.trans hfinal)
    convert hresult using 1 <;> dsimp [F, T, D, E, L, ξ] <;> ring

end

end Erdos1212Kernel
