import Erdos1212Kernel.IwaniecPaperDQ

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 600000

theorem iwaniecPaperQ_even_succ (n : Nat) (level s : Real) :
    iwaniecPaperQ (2 * n + 2) level s =
      iwaniecPaperQ (2 * n) level s + iwaniecPaperD (2 * n + 2) level s := by
  classical
  have he : Even (2 * n) := ⟨n, by omega⟩
  have he2 : Even (2 * n + 2) := ⟨n + 1, by omega⟩
  have ho : ¬Even (2 * n + 1) := by
    simp only [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    omega
  unfold iwaniecPaperQ
  simp only [he, he2, iff_true]
  conv_lhs => rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp only [he2, ho, if_false, if_true, add_zero]

theorem iwaniecPaperQ_odd_succ (n : Nat) (level s : Real) :
    iwaniecPaperQ (2 * n + 3) level s =
      iwaniecPaperQ (2 * n + 1) level s + iwaniecPaperD (2 * n + 3) level s := by
  classical
  have ho1 : ¬Even (2 * n + 1) := by
    simp only [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    omega
  have ho3 : ¬Even (2 * n + 3) := by
    simp only [even_iff_two_dvd, Nat.dvd_iff_mod_eq_zero]
    omega
  have he2 : Even (2 * n + 2) := ⟨n + 1, by omega⟩
  unfold iwaniecPaperQ
  simp only [ho1, ho3, iff_false]
  conv_lhs => rw [Finset.sum_range_succ, Finset.sum_range_succ]
  simp [he2, ho3]

/-- The literal even finite sum on printed page 22. -/
theorem iwaniecPaperQ_even_source_sum (n : Nat) (level s : Real) :
    iwaniecPaperQ (2 * n) level s =
      ∑ i ∈ Finset.range n, iwaniecPaperD (2 * i + 2) level s := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hn : 2 * (n + 1) = 2 * n + 2 := by omega
      rw [hn, iwaniecPaperQ_even_succ, Finset.sum_range_succ, ih]

/-- The literal odd finite sum; the apparent rank-one padding is
removed by its proved vanishing on the paper's positive level domain. -/
theorem iwaniecPaperQ_odd_source_sum (n : Nat) {level : Real} (hy : 1 < level) (s : Real) :
    iwaniecPaperQ (2 * n + 1) level s =
      ∑ i ∈ Finset.range n, iwaniecPaperD (2 * i + 3) level s := by
  induction n with
  | zero => simp [iwaniecPaperQ_one hy s]
  | succ n ih =>
      have hn : 2 * (n + 1) + 1 = 2 * n + 3 := by omega
      rw [hn, iwaniecPaperQ_odd_succ, Finset.sum_range_succ, ih]

theorem iwaniecPaperQ_odd_initial {rank : Nat} (hr : ¬Even rank) (level : Real) {s : Real}
    (hs1 : 1 ≤ s) (hs3 : s ≤ 3) : iwaniecPaperQ rank level s = iwaniecPaperQ rank level 3 := by
  rw [iwaniecPaperQ_odd_eq_partial hr, iwaniecPaperQ_odd_eq_partial hr]
  simp only [max_eq_left hs3, max_self]

/-- Consume the paper's Q_(2r) in the original finite weighted main
term, with the successful depth-2r tail explicitly retained. -/
theorem iwaniecCubicWeightedMainExpansion_paperQ {r y : Nat} (hr : 0 < r) (s : Real) :
    iwaniecCubicWeightedMainExpansion r y (iwaniecStrictPrimePool (Real.exp (Real.log (y : Real) / s))) =
      iwaniecPaperR (Real.exp (Real.log (y : Real) / s)) - iwaniecPaperQ (2 * r) y s -
        iwaniecSurvivalLayer (iwaniecCubicEvenRestriction y) iwaniecReciprocalFactorWeight []
          (iwaniecDescendingFactors (iwaniecStrictPrimePool (Real.exp (Real.log (y : Real) / s)))) (2 * r) := by
  have he : Even (2 * r) := ⟨r, by omega⟩
  rw [iwaniecPaperQ_even_eq_partial he]
  exact iwaniecCubicWeightedMainExpansion_stopped_partial hr _

theorem iwaniecCubicWeightedMainExpansion_paperQ_no_tail {r y : Nat} (hr : 0 < r) (s : Real)
    (hcard : (iwaniecStrictPrimePool (Real.exp (Real.log (y : Real) / s))).card < 2 * r) :
    iwaniecCubicWeightedMainExpansion r y (iwaniecStrictPrimePool (Real.exp (Real.log (y : Real) / s))) =
      iwaniecPaperR (Real.exp (Real.log (y : Real) / s)) - iwaniecPaperQ (2 * r) y s := by
  have he : Even (2 * r) := ⟨r, by omega⟩
  rw [iwaniecPaperQ_even_eq_partial he]
  exact iwaniecCubicWeightedMainExpansion_stopped_partial_no_tail hr _ hcard

theorem exists_iwaniecPaperQ_two_bound :
    ∃ C : Real, 0 < C ∧ ∀ level s : Real, 1 < level → 2 ≤ s →
      Real.exp Real.eulerMascheroniConstant * iwaniecPaperQ 2 level s <
        iwaniecGTwo s / Real.log level + C * Real.exp (-Real.sqrt (Real.log level / 6)) := by
  obtain ⟨C, hC, hbase⟩ := exists_iwaniecLemma16_constant
  refine ⟨C, hC, ?_⟩
  intro level s hy hs
  rw [iwaniecPaperQ_two_eq_d2]
  exact hbase level s hy hs

end

end Erdos1212Kernel
