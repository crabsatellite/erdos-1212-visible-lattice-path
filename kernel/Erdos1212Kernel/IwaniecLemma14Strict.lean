import Erdos1212Kernel.IwaniecLemma14Real
import Erdos1212Kernel.IwaniecPaperD2Support
import Erdos1212Kernel.IwaniecRealPrimeInterval

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 500000

def iwaniecPrimeLogReciprocalStrictInterval (B A : Real) : Real :=
  ∑ q ∈ (iwaniecStrictPrimePool A).filter (fun q : Nat => B ≤ (q : Real)),
    1 / ((q : Real) * Real.log (q : Real))

/-- The upper prime is removed exactly, not absorbed by changing the
finite prime carrier. -/
theorem iwaniecPrimeLogReciprocalInterval_prime_upper (B : Real) {p : Nat}
    (hp : p.Prime) (hBp : B ≤ (p : Real)) :
    iwaniecPrimeLogReciprocalRealInterval B p =
      iwaniecPrimeLogReciprocalStrictInterval B p + 1 / ((p : Real) * Real.log (p : Real)) := by
  classical
  have hset : (Nat.primesLE p).filter (fun q : Nat => B ≤ (q : Real)) =
      insert p ((iwaniecStrictPrimePool (p : Real)).filter (fun q : Nat => B ≤ (q : Real))) := by
    ext q
    simp only [Finset.mem_filter, Nat.mem_primesLE, Finset.mem_insert, mem_iwaniecStrictPrimePool]
    constructor
    · rintro ⟨⟨hqp, hqPrime⟩, hBq⟩
      by_cases heq : q = p
      · exact Or.inl heq
      · exact Or.inr ⟨⟨hqPrime, by exact_mod_cast (show q < p by omega)⟩, hBq⟩
    · rintro (rfl | ⟨⟨hqPrime, hqp⟩, hBq⟩)
      · exact ⟨⟨le_rfl, hp⟩, hBp⟩
      · exact ⟨⟨by exact_mod_cast hqp.le, hqPrime⟩, hBq⟩
  have hnot : p ∉ (iwaniecStrictPrimePool (p : Real)).filter (fun q : Nat => B ≤ (q : Real)) := by
    intro hh
    have hlt := (mem_iwaniecStrictPrimePool.mp (Finset.mem_filter.mp hh).1).2
    exact (lt_irrefl (p : Real)) hlt
  unfold iwaniecPrimeLogReciprocalRealInterval iwaniecPrimeLogReciprocalStrictInterval
  rw [Nat.floor_natCast, hset, Finset.sum_insert hnot]
  exact add_comm _ _

theorem exists_iwaniecLemma14_strict_prime_upper_constant :
    ∃ C : Real, 0 < C ∧ ∀ (B : Real) (p : Nat), p.Prime → 2 ≤ B → B ≤ (p : Real) →
      |iwaniecPrimeLogReciprocalStrictInterval B p -
        ((Real.log B)⁻¹ - (Real.log (p : Real))⁻¹)| ≤
          C * Real.exp (-Real.sqrt (Real.log B)) := by
  obtain ⟨C₀, hC₀, hclosed⟩ := exists_iwaniecLemma14_real_constant
  refine ⟨C₀ + iwaniecRealEndpointConstant, add_pos hC₀ iwaniecRealEndpointConstant_pos, ?_⟩
  intro B p hp hB hBp
  have hp2 : (2 : Real) ≤ p := hB.trans hBp
  have hK := (iwaniecLogKernel_antitoneOn_Ici_two hB hp2 hBp).trans (iwaniecLogKernel_source_rate_two hB)
  have hK0 : 0 ≤ iwaniecLogKernel (p : Real) := (iwaniecLogKernel_pos (by linarith)).le
  have hsplit : iwaniecPrimeLogReciprocalStrictInterval B p -
      ((Real.log B)⁻¹ - (Real.log (p : Real))⁻¹) =
      (iwaniecPrimeLogReciprocalRealInterval B p -
        ((Real.log B)⁻¹ - (Real.log (p : Real))⁻¹)) - iwaniecLogKernel (p : Real) := by
    rw [iwaniecPrimeLogReciprocalInterval_prime_upper B hp hBp]
    unfold iwaniecLogKernel
    ring
  rw [hsplit]
  calc
    _ ≤ |iwaniecPrimeLogReciprocalRealInterval B p -
        ((Real.log B)⁻¹ - (Real.log (p : Real))⁻¹)| + |iwaniecLogKernel (p : Real)| := abs_sub _ _
    _ ≤ C₀ * Real.exp (-Real.sqrt (Real.log B)) +
        iwaniecRealEndpointConstant * Real.exp (-Real.sqrt (Real.log B)) := by
      rw [abs_of_nonneg hK0]
      exact add_le_add (hclosed B p hB hBp) hK
    _ = _ := by ring

end

end Erdos1212Kernel
