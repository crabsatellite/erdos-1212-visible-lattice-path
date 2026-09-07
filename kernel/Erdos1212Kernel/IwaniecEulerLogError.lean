import Erdos1212Kernel.IwaniecEulerTailBound
import Erdos1212Kernel.IwaniecQuadratureSourceRate

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

def iwaniecEulerLogRemainder (N : Nat) : Real :=
  Real.log (Erdos696.Mertens.mertensProd N) + Real.log (Real.log (N : Real)) +
    Real.eulerMascheroniConstant

theorem iwaniecEulerLogRemainder_eq (N : Nat) :
    iwaniecEulerLogRemainder N = -iwaniecPrimeReciprocalRemainder N +
      (Erdos696.Mertens.mertensH' - Erdos696.Mertens.mertensTail N) := by
  unfold iwaniecEulerLogRemainder
  rw [Erdos696.Mertens.log_mertensProd_eq]
  unfold iwaniecPrimeReciprocalRemainder Erdos696.Mertens.meisselMertensConstant
  ring

theorem exists_iwaniecEulerLogRemainder_unit_error :
    ∃ C : Real, 0 < C ∧ ∀ N : Nat, 1 ≤ N →
      |iwaniecEulerLogRemainder N| ≤ C * Real.exp (-Real.sqrt (Real.log (N : Real))) := by
  obtain ⟨A, hA, hprime⟩ := exists_iwaniecPrimeReciprocalRemainder_unit_error_all
  refine ⟨A + Real.exp 1, by positivity, ?_⟩
  intro N hN
  have htail := (iwaniecMertensTail_limit_bound hN).2
  have hrate := iwaniec_inverse_le_sqrt_log_exponential (show (1 : Real) ≤ N by exact_mod_cast hN)
  rw [iwaniecEulerLogRemainder_eq]
  calc
    _ ≤ |-iwaniecPrimeReciprocalRemainder N| +
        |Erdos696.Mertens.mertensH' - Erdos696.Mertens.mertensTail N| := abs_add_le _ _
    _ ≤ A * Real.exp (-Real.sqrt (Real.log (N : Real))) +
        Real.exp 1 * Real.exp (-Real.sqrt (Real.log (N : Real))) := by
      rw [abs_neg]
      exact add_le_add (hprime N) (htail.trans hrate)
    _ = _ := by ring

theorem iwaniec_mertensProd_pos (N : Nat) : 0 < Erdos696.Mertens.mertensProd N := by
  unfold Erdos696.Mertens.mertensProd
  apply Finset.prod_pos
  intro p hp
  exact Erdos696.Mertens.one_sub_inv_prime_pos p (Finset.mem_filter.mp hp).2

theorem iwaniecEulerLogRemainder_exp_identity {N : Nat} (hN : 2 ≤ N) :
    Erdos696.Mertens.mertensProd N =
      (Real.exp (-Real.eulerMascheroniConstant) / Real.log (N : Real)) *
        Real.exp (iwaniecEulerLogRemainder N) := by
  have hlog : 0 < Real.log (N : Real) := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hprod := iwaniec_mertensProd_pos N
  have hcancel : Real.exp (-Real.eulerMascheroniConstant) * Real.exp Real.eulerMascheroniConstant = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  unfold iwaniecEulerLogRemainder
  rw [Real.exp_add, Real.exp_add, Real.exp_log hprod, Real.exp_log hlog]
  calc
    _ = Erdos696.Mertens.mertensProd N *
        (Real.exp (-Real.eulerMascheroniConstant) * Real.exp Real.eulerMascheroniConstant) := by rw [hcancel, mul_one]
    _ = _ := by field_simp [hlog.ne'] <;> ring

end

end Erdos1212Kernel
