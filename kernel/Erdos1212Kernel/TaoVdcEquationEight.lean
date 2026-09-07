import Erdos1212Kernel.TaoVdcCrossOrderBounds

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1900000

def taoVdcBareMax (k : Nat) (N T : Real) : Real :=
  max (taoVdcBareFirst k N T) (taoVdcSecond k N T)

theorem taoVdcThreshold_le_pred {k : Nat} (hk : 2 ≤ k) :
    taoVdcThreshold k ≤ (k - 1 : Nat) := by
  unfold taoVdcThreshold
  have ha := taoVdcAlpha_le_one k
  norm_num at ha ⊢
  have hkR : ((k - 1 : Nat) : Real) = (k : Real) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  rw [hkR]
  linarith

theorem taoVdcEquationEight {N T : Real} (hN : 1 ≤ N) (hT : 0 < T) (hNT : N ≤ T)
    (k : Nat) (hk : 2 ≤ k) (hupper : T ≤ N ^ k) :
    ∃ j ∈ Finset.Icc 2 k,
      taoVdcBareMax j N T ≤ taoVdcSecond k N T := by
  induction k, hk using Nat.le_induction with
  | base =>
      refine ⟨2, by simp, ?_⟩
      unfold taoVdcBareMax
      apply max_le
      · apply taoVdc_high_threshold_bound (k := 2) (by norm_num) hN hT
        norm_num [taoVdcThreshold, taoVdcAlpha]
        exact hNT
      · exact le_rfl
  | succ n hn ih =>
      have hK : 3 ≤ n + 1 := by omega
      by_cases hthreshold : N ^ (taoVdcThreshold (n + 1)) ≤ T
      · refine ⟨n + 1, Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩, ?_⟩
        unfold taoVdcBareMax
        exact max_le (taoVdc_high_threshold_bound (by omega) hN hT hthreshold) le_rfl
      · have hlow : T ≤ N ^ (taoVdcThreshold (n + 1)) := (lt_of_not_ge hthreshold).le
        have hexp := taoVdcThreshold_le_pred (k := n + 1) (by omega)
        have hpow := Real.rpow_le_rpow_of_exponent_le hN hexp
        rw [Real.rpow_natCast] at hpow
        have hnupper : T ≤ N ^ n := hlow.trans hpow
        obtain ⟨j, hj, hjbound⟩ := ih hnupper
        refine ⟨j, Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hj).1,
          (Finset.mem_Icc.mp hj).2.trans (by omega)⟩, ?_⟩
        exact hjbound.trans (taoVdc_low_threshold_bound hK hN hT hlow)

end

end Erdos1212Kernel
