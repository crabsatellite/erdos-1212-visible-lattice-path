import Erdos1212Kernel.IwaniecUnscaledMovingMargin

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

/-- Vaughan (1977), equation (7), before any logarithmic transport. -/
def vaughanSieveCutoff (A level : Real) : Real := Real.sqrt level * Real.exp (-A)

def vaughanSieveParameter (A level : Real) : Real := Real.log level / Real.log (vaughanSieveCutoff A level)

def vaughanSieveDelta (A level : Real) : Real := vaughanSieveParameter A level - 2

theorem vaughanSieveCutoff_pos (A : Real) {level : Real} (hy : 0 < level) :
    0 < vaughanSieveCutoff A level := mul_pos (Real.sqrt_pos.mpr hy) (Real.exp_pos _)

theorem vaughanSieveCutoff_eq_exp (A : Real) {level : Real} (hy : 0 < level) :
    vaughanSieveCutoff A level = Real.exp (Real.log level / 2 - A) := by
  have hroot : Real.sqrt level = Real.exp (Real.log level / 2) := by
    rw [Real.exp_half, Real.exp_log hy]
  unfold vaughanSieveCutoff
  rw [hroot, ← Real.exp_add]
  congr 1 <;> ring

theorem vaughanSieveCutoff_log (A : Real) {level : Real} (hy : 0 < level) :
    Real.log (vaughanSieveCutoff A level) = Real.log level / 2 - A := by
  rw [vaughanSieveCutoff_eq_exp A hy, Real.log_exp]

theorem vaughanSieveParameter_eq (A : Real) {level : Real} (hy : 0 < level) :
    vaughanSieveParameter A level = Real.log level / (Real.log level / 2 - A) := by
  rw [vaughanSieveParameter, vaughanSieveCutoff_log A hy]

theorem vaughanSieveDenominator_pos {A level : Real}
    (hy : 1 < level) (hlog : 6 * A ≤ Real.log level) : 0 < Real.log level / 2 - A := by
  have hL := Real.log_pos hy
  linarith only [hL, hlog]

theorem vaughanSieveParameter_bounds {A level : Real}
    (hA : 0 ≤ A) (hy : 1 < level) (hlog : 6 * A ≤ Real.log level) :
    2 ≤ vaughanSieveParameter A level ∧ vaughanSieveParameter A level ≤ 3 := by
  rw [vaughanSieveParameter_eq A (zero_lt_one.trans hy)]
  have hd := vaughanSieveDenominator_pos hy hlog
  constructor
  · apply (le_div_iff₀ hd).mpr
    linarith only [hA]
  · apply (div_le_iff₀ hd).mpr
    linarith only [hlog]

theorem vaughanSieveDelta_eq {A level : Real}
    (hy : 1 < level) (hlog : 6 * A ≤ Real.log level) :
    vaughanSieveDelta A level = 2 * A / (Real.log level / 2 - A) := by
  rw [vaughanSieveDelta, vaughanSieveParameter_eq A (zero_lt_one.trans hy)]
  have hd := (vaughanSieveDenominator_pos hy hlog).ne'
  apply (eq_div_iff hd).mpr
  rw [sub_mul, div_mul_cancel₀ _ hd]
  ring

theorem vaughanSieveDelta_bounds {A level : Real}
    (hA : 0 ≤ A) (hy : 1 < level) (hlog : 6 * A ≤ Real.log level) :
    0 ≤ vaughanSieveDelta A level ∧ vaughanSieveDelta A level ≤ 1 := by
  obtain ⟨hl, hu⟩ := vaughanSieveParameter_bounds hA hy hlog
  unfold vaughanSieveDelta
  constructor <;> linarith only [hl, hu]

theorem vaughanSieveDelta_lower {A level : Real}
    (hA : 0 ≤ A) (hy : 1 < level) (hlog : 6 * A ≤ Real.log level) :
    4 * A / Real.log level ≤ vaughanSieveDelta A level := by
  rw [vaughanSieveDelta_eq hy hlog]
  calc
    _ = 2 * A / (Real.log level / 2) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (vaughanSieveDenominator_pos hy hlog) (by linarith)

/-- The reciprocal-log cutoff really is the original square-root
cutoff, not a replacement at a nearby natural or logarithmic scale. -/
theorem vaughanSieve_cutoff_transport {A level : Real}
    (hy : 1 < level) (hlog : 6 * A ≤ Real.log level) :
    Real.exp (Real.log level / (2 + vaughanSieveDelta A level)) = vaughanSieveCutoff A level := by
  have hL := (Real.log_pos hy).ne'
  have hX : Real.log (vaughanSieveCutoff A level) ≠ 0 := by
    rw [vaughanSieveCutoff_log A (zero_lt_one.trans hy)]
    exact (vaughanSieveDenominator_pos hy hlog).ne'
  have hs : 2 + vaughanSieveDelta A level = vaughanSieveParameter A level := by
    unfold vaughanSieveDelta
    ring
  rw [hs, vaughanSieveParameter]
  have hquot : Real.log level / (Real.log level / Real.log (vaughanSieveCutoff A level)) =
      Real.log (vaughanSieveCutoff A level) := by field_simp [hL, hX]
  rw [hquot, Real.exp_log (vaughanSieveCutoff_pos A (zero_lt_one.trans hy))]

end

end Erdos1212Kernel
