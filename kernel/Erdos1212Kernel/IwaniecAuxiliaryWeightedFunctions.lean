import Erdos1212Kernel.IwaniecAuxiliaryGKernel
import Erdos1212Kernel.IwaniecAuxiliaryWeightCalculus

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1200000

def iwaniecAuxTau (rank : Nat) (level s : Real) : Real :=
  iwaniecAuxWeightPower level s * iwaniecAuxG (rank + 1) s

def iwaniecAuxMu (rank : Nat) (level s : Real) : Real :=
  iwaniecAuxWeightLowerPower level s * iwaniecAuxG (rank + 1) s

def iwaniecAuxWeightedIntegrand (rank : Nat) (level s : Real) : Real :=
  iwaniecAuxWeightLowerPower level s * iwaniecAuxG rank (s - 1) * s / (s - 1) ^ 2

theorem iwaniecAuxWeightedIntegrand_eq (rank : Nat) (level s : Real) :
    iwaniecAuxWeightedIntegrand rank level s =
      iwaniecAuxWeightLowerPower level s * iwaniecAuxGKernel rank s := by
  unfold iwaniecAuxWeightedIntegrand iwaniecAuxGKernel
  ring

theorem iwaniecAuxTau_pos (rank : Nat) (level : Real) {s : Real} (hs : 2 ≤ s) :
    0 < iwaniecAuxTau rank level s :=
  mul_pos (iwaniecAuxWeightPower_pos level (by linarith)) (iwaniecAuxG_pos (rank + 1) hs)

theorem iwaniecAuxMu_pos (rank : Nat) (level : Real) {s : Real} (hs : 2 ≤ s) :
    0 < iwaniecAuxMu rank level s :=
  mul_pos (iwaniecAuxWeightLowerPower_pos level (by linarith)) (iwaniecAuxG_pos (rank + 1) hs)

theorem iwaniecAuxWeightedIntegrand_pos (rank : Nat) (level : Real) {s : Real} (hs : 3 ≤ s) :
    0 < iwaniecAuxWeightedIntegrand rank level s := by
  rw [iwaniecAuxWeightedIntegrand_eq]
  exact mul_pos (iwaniecAuxWeightLowerPower_pos level (by linarith)) (iwaniecAuxGKernel_pos rank hs)

theorem iwaniecAuxTau_hasDerivAt (rank : Nat)
    {level s : Real} (hy : 1 < level) (hs : 3 < s) :
    HasDerivAt (iwaniecAuxTau rank level)
      (iwaniecAuxWeightPower level s *
        (iwaniecAuxWeightLogDerivative level s * iwaniecAuxG (rank + 1) s - iwaniecAuxGKernel rank s)) s := by
  have h := (iwaniecAuxWeightPower_hasDerivAt hy (show 1 ≤ s by linarith)).mul
    (iwaniecAuxG_succ_hasDerivAt rank hs)
  convert h using 1 <;> ring

/-- The exact sign from the derivative of the source's tau. The weight
derivative subtracts from the positive G-kernel term in `-tau'`. -/
theorem neg_deriv_iwaniecAuxTau (rank : Nat)
    {level s : Real} (hy : 1 < level) (hs : 3 < s) :
    -deriv (iwaniecAuxTau rank level) s =
      iwaniecAuxWeightPower level s *
        (iwaniecAuxGKernel rank s - iwaniecAuxWeightLogDerivative level s * iwaniecAuxG (rank + 1) s) := by
  rw [(iwaniecAuxTau_hasDerivAt rank hy hs).deriv]
  ring

theorem iwaniecAuxMu_eq_tau_div_base (rank : Nat)
    (level : Real) {s : Real} (hs : 1 ≤ s) :
    iwaniecAuxMu rank level s = iwaniecAuxTau rank level s / iwaniecAuxWeightBase level s ^ 5 := by
  unfold iwaniecAuxMu iwaniecAuxTau
  rw [iwaniecAuxWeightPower_split level hs]
  field_simp [(iwaniecAuxWeightBase_pos level hs).ne']

end

end Erdos1212Kernel
