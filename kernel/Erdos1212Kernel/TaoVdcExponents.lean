import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1500000

def taoVdcAlpha (k : Nat) : Real := 1 / (2 : Real) ^ (k - 2)
def taoVdcBeta (k : Nat) : Real := 1 / ((2 : Real) ^ k - 2)

theorem taoVdcAlpha_pos (k : Nat) : 0 < taoVdcAlpha k := by unfold taoVdcAlpha; positivity

theorem taoVdcAlpha_le_one (k : Nat) : taoVdcAlpha k ≤ 1 := by
  unfold taoVdcAlpha
  apply (div_le_iff₀ (by positivity : (0 : Real) < 2 ^ (k - 2))).2
  simpa using (one_le_pow₀ (by norm_num : (1 : Real) ≤ 2) : (1 : Real) ≤ 2 ^ (k - 2))

theorem taoVdcBeta_pos {k : Nat} (hk : 2 ≤ k) : 0 < taoVdcBeta k := by
  have hpow : (2 : Real) ^ 2 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  unfold taoVdcBeta
  norm_num at hpow
  have hden : 0 < (2 : Real) ^ k - 2 := by linarith
  positivity

theorem taoVdcBeta_le_half {k : Nat} (hk : 2 ≤ k) : taoVdcBeta k ≤ 1 / 2 := by
  have hpow : (2 : Real) ^ 2 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  norm_num at hpow
  unfold taoVdcBeta
  exact one_div_le_one_div_of_le (by norm_num) (by linarith)

theorem taoVdcAlpha_two : taoVdcAlpha 2 = 1 := by norm_num [taoVdcAlpha]
theorem taoVdcBeta_two : taoVdcBeta 2 = 1 / 2 := by norm_num [taoVdcBeta]

theorem taoVdcAlpha_succ {k : Nat} (hk : 2 ≤ k) :
    taoVdcAlpha (k + 1) = taoVdcAlpha k / 2 := by
  have hindex : k + 1 - 2 = (k - 2) + 1 := by omega
  unfold taoVdcAlpha
  rw [hindex, pow_succ]
  ring

theorem taoVdcBeta_succ {k : Nat} (hk : 2 ≤ k) :
    taoVdcBeta (k + 1) = taoVdcBeta k / (2 * (1 + taoVdcBeta k)) := by
  have hpow : (2 : Real) ^ 2 ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  norm_num at hpow
  have hden : (2 : Real) ^ k - 2 ≠ 0 := by linarith
  unfold taoVdcBeta
  rw [pow_succ]
  field_simp [hden]
  <;> ring

/-- For k>=3 this is the exact source A-exponent 1/2^(k-3).
Using twice alpha also retains the source value 2 at k=2. -/
theorem taoVdc_source_amplitude_exponent {k : Nat} (hk : 3 ≤ k) :
    2 * taoVdcAlpha k = 1 / (2 : Real) ^ (k - 3) := by
  have hindex : k - 2 = (k - 3) + 1 := by omega
  unfold taoVdcAlpha
  rw [hindex, pow_succ]
  field_simp

end

end Erdos1212Kernel
