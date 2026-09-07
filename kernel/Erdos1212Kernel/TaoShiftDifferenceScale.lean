import Erdos1212Kernel.TaoShiftDifferenceBounds

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 1500000

/-- At every derivative order, the source parameter changes from T to
h*T/N while the original ambient scale N and the factor A are retained. -/
theorem taoShiftDifference_scaled_bounds (g g' : Real → Real) (j : Nat) {L U h x A N T : Real}
    (hA : 0 < A) (hN : 0 < N) (hT : 0 < T) (hh : 0 ≤ h)
    (hg : ∀ t ∈ Set.Icc L U, HasDerivAt g (g' t) t)
    (hc : ContinuousOn g' (Set.Icc L U))
    (hlow : ∀ t ∈ Set.Icc L U, T / (A * N ^ (j + 1)) ≤ |g' t|)
    (hhigh : ∀ t ∈ Set.Icc L U, |g' t| ≤ A * T / N ^ (j + 1))
    (hx : x ∈ Set.Icc L (U - h)) :
    (h * T / N) / (A * N ^ j) ≤ |taoShiftDifference g h x| ∧
      |taoShiftDifference g h x| ≤ A * (h * T / N) / N ^ j := by
  have hδ : 0 < T / (A * N ^ (j + 1)) := by positivity
  have hb := taoShiftDifference_bounds g g' hδ hh hg hc hlow hhigh hx
  have hlo : h * (T / (A * N ^ (j + 1))) = (h * T / N) / (A * N ^ j) := by
    rw [pow_succ]
    field_simp
    <;> ring
  have hhi : h * (A * T / N ^ (j + 1)) = A * (h * T / N) / N ^ j := by
    rw [pow_succ]
    field_simp
    <;> ring
  simpa only [hlo, hhi] using hb

end

end Erdos1212Kernel
