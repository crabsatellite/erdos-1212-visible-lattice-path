import Erdos1212Kernel

open Filter MeasureTheory

namespace Erdos1212Kernel

/-- Literal displayed theorem, independently elaborated at the final audit boundary. -/
theorem algebraicCorridor_literal_paper_endpoint :
    ∀ᵐ α : ℝ ∂volume.restrict (Set.Ioo (4 / 3 : ℝ) (5 / 3 : ℝ)),
      ∃ P : ℕ → LatticePoint, Function.Injective P ∧
        (∀ n, SafePoint (P n)) ∧
        (∀ n, Adjacent (P n) (P (n + 1))) ∧
        Tendsto (fun n => ((P n).x : ℝ) / ((P n).y : ℝ)) atTop (nhds α) :=
  CorridorScale.algebraicCorridor_paper_close

#check (CorridorScale.erdos1212_fullClose_from_algebraic_corridors : Erdos1212FullClose)
#check (CorridorScale.algebraicCorridor_paper_close : AlgebraicCorridorPaperStatement)
#print axioms CorridorScale.erdos1212_fullClose_from_algebraic_corridors
#print axioms CorridorScale.algebraicCorridor_paper_close
#print axioms algebraicCorridor_literal_paper_endpoint

end Erdos1212Kernel
