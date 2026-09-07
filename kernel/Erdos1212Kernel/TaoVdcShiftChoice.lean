import Erdos1212Kernel.TaoVdcRegimes

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1600000

def taoVdcRealShift (k : Nat) (N T : Real) : Real := (N ^ k / T) ^ (2 * taoVdcBeta k)
def taoVdcShift (k : Nat) (N : Nat) (T : Real) : Nat := ⌊taoVdcRealShift k N T⌋₊

theorem taoVdcRealShift_bounds {k : Nat} (hk : 3 ≤ k) {N T : Real}
    (hN : 1 ≤ N) (hT : 1 ≤ T) (hupper : T ≤ N ^ k) :
    1 ≤ taoVdcRealShift k N T ∧ taoVdcRealShift k N T ≤ N := by
  have hNp : 0 < N := by linarith
  have hTp : 0 < T := by linarith
  have hbeta := taoVdcBeta_pos (by omega : 2 ≤ k)
  have hQlow : 1 ≤ N ^ k / T := (le_div_iff₀ hTp).2 (by simpa using hupper)
  have hQhigh : N ^ k / T ≤ N ^ k := (div_le_iff₀ hTp).2 (by nlinarith [mul_le_mul_of_nonneg_left hT (show 0 ≤ N ^ k by positivity)])
  constructor
  · exact Real.one_le_rpow hQlow (by positivity)
  · unfold taoVdcRealShift
    calc
      _ ≤ (N ^ k) ^ (2 * taoVdcBeta k) := Real.rpow_le_rpow (by positivity) hQhigh (by positivity)
      _ = N ^ ((k : Real) * (2 * taoVdcBeta k)) := by rw [Real.rpow_mul hNp.le, Real.rpow_natCast]
      _ ≤ N ^ (1 : Real) := Real.rpow_le_rpow_of_exponent_le hN (taoVdc_order_beta_le_half hk)
      _ = N := Real.rpow_one N

theorem taoVdcShift_admissible {k : Nat} (hk : 3 ≤ k) {N : Nat} {T : Real}
    (hN : 0 < N) (hT : 1 ≤ T) (hupper : T ≤ (N : Real) ^ k) :
    0 < taoVdcShift k N T ∧ taoVdcShift k N T ≤ N ∧
      taoVdcRealShift k N T / 2 ≤ (taoVdcShift k N T : Real) ∧
      (taoVdcShift k N T : Real) ≤ taoVdcRealShift k N T := by
  have hN1 : 1 ≤ (N : Real) := by exact_mod_cast hN
  obtain ⟨hRlo, hRhi⟩ := taoVdcRealShift_bounds hk hN1 hT hupper
  exact ⟨Nat.floor_pos.mpr hRlo, Nat.floor_le_of_le hRhi, taoSecondDerivative_floor_half hRlo⟩

theorem taoVdcShift_negative_power {k : Nat} (hk : 3 ≤ k) {N : Nat} {T p : Real}
    (hN : 0 < N) (hT : 1 ≤ T) (hupper : T ≤ (N : Real) ^ k) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    (taoVdcShift k N T : Real) ^ (-p) ≤ 2 * (taoVdcRealShift k N T) ^ (-p) := by
  obtain ⟨hH, _hHN, hhalf, _hfull⟩ := taoVdcShift_admissible hk hN hT hupper
  have hR : 0 < taoVdcRealShift k N T := by
    have hh := (taoVdcRealShift_bounds hk (by exact_mod_cast hN) hT hupper).1
    linarith
  have htwo : (2 : Real) ^ p ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : Real) ≤ 2) hp1
  calc
    _ ≤ (taoVdcRealShift k N T / 2) ^ (-p) := Real.rpow_le_rpow_of_nonpos (by positivity) hhalf (by linarith)
    _ = (taoVdcRealShift k N T) ^ (-p) * (2 : Real) ^ p := by
      rw [Real.div_rpow hR.le (by norm_num), Real.rpow_neg (by norm_num : (0 : Real) ≤ 2)]
      exact div_inv_eq_mul _ _
    _ ≤ (taoVdcRealShift k N T) ^ (-p) * 2 := mul_le_mul_of_nonneg_left htwo (Real.rpow_nonneg hR.le _)
    _ = _ := by ring

theorem taoVdcShift_positive_power {k : Nat} (hk : 3 ≤ k) {N : Nat} {T p : Real}
    (hN : 0 < N) (hT : 1 ≤ T) (hupper : T ≤ (N : Real) ^ k) (hp : 0 ≤ p) :
    (taoVdcShift k N T : Real) ^ p ≤ (taoVdcRealShift k N T) ^ p := by
  have hH := taoVdcShift_admissible hk hN hT hupper
  exact Real.rpow_le_rpow (by positivity) hH.2.2.2 hp

end

end Erdos1212Kernel
