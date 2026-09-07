import Erdos1212Kernel.IwaniecPaperSupportFinite
import Erdos1212Kernel.IwaniecPaperABandRecursion

namespace Erdos1212Kernel

noncomputable section

set_option maxHeartbeats 650000

theorem iwaniecPaperFiniteSupport_mono_cutoff (rank : Nat) (level : Real)
    {z Z : Real} (hz : z ≤ Z) :
    iwaniecPaperFiniteSupport rank level z ⊆ iwaniecPaperFiniteSupport rank level Z := by
  classical
  intro xs hxs
  obtain ⟨hordered, hdata⟩ := Finset.mem_filter.mp hxs
  have hsub := mem_iwaniecOrderedFactorSublists.mp hordered
  have hpool := iwaniecDescendingFactors_sublist_of_subset (iwaniecStrictPrimePool_mono hz)
  exact Finset.mem_filter.mpr ⟨mem_iwaniecOrderedFactorSublists.mpr (hsub.trans hpool), hdata⟩

theorem iwaniecPaperA_antitone_parameter (rank : Nat) {level s S : Real}
    (hy : 1 < level) (hs : 0 < s) (hsS : s ≤ S) :
    iwaniecPaperA rank level S ≤ iwaniecPaperA rank level s := by
  have hh := Finset.card_le_card (iwaniecPaperFiniteSupport_mono_cutoff rank level
    (iwaniecPaperCutoff_antitone hy hs hsS))
  simpa only [iwaniecPaperFiniteSupport_card, iwaniecPaperA] using hh

theorem iwaniecCubicFirst_all_cube_lt {level : Real} (xs : List Nat)
    (horder : xs.Pairwise (fun p q => q ≤ p)) (hadm : iwaniecCubicRealAdmissible 1 level xs) :
    ∀ p ∈ xs, (p : Real) ^ 3 < level := by
  cases xs with
  | nil => simp
  | cons q tail =>
      have hhead : (q : Real) ^ 3 < level := by simpa [iwaniecCubicRealAdmissible] using hadm.1
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact hhead
      · have hpq := (List.pairwise_cons.mp horder).1 p hp
        exact (pow_le_pow_left₀ (Nat.cast_nonneg p : (0 : Real) ≤ p)
          (by exact_mod_cast hpq) 3).trans_lt hhead

theorem iwaniec_cube_lt_imp_lt_cutoff {level : Real} (hy : 1 < level) {p : Nat}
    (hp : (p : Real) ^ 3 < level) : (p : Real) < Real.exp (Real.log level / 3) := by
  have hcube : (Real.exp (Real.log level / 3)) ^ 3 = level := by
    calc
      _ = Real.exp (3 * (Real.log level / 3)) := (Real.exp_nat_mul (Real.log level / 3) 3).symm
      _ = Real.exp (Real.log level) := by congr 1; ring
      _ = level := Real.exp_log (show 0 < level by linarith)
  by_contra hn
  have hpow := pow_le_pow_left₀ (Real.exp_pos (Real.log level / 3)).le (le_of_not_gt hn) 3
  rw [hcube] at hpow
  linarith

theorem iwaniecPaperFiniteSupport_even_capped {rank : Nat} (hr : Even rank)
    {level z : Real} (hy : 1 < level) (hz : Real.exp (Real.log level / 3) ≤ z) :
    iwaniecPaperFiniteSupport rank level z =
      iwaniecPaperFiniteSupport rank level (Real.exp (Real.log level / 3)) := by
  classical
  apply Finset.Subset.antisymm _ (iwaniecPaperFiniteSupport_mono_cutoff rank level hz)
  intro xs hxs
  obtain ⟨hordered, hdata⟩ := Finset.mem_filter.mp hxs
  have hsub := mem_iwaniecOrderedFactorSublists.mp hordered
  have hadm : iwaniecCubicRealAdmissible 1 level xs := by simpa only [if_pos hr] using hdata.2.1
  have horder := (Finset.pairwise_sort (iwaniecStrictPrimePool z) (fun p q : Nat => q ≤ p)).sublist hsub
  have hcubes := iwaniecCubicFirst_all_cube_lt xs horder hadm
  have hsubset : xs.toFinset ⊆ iwaniecStrictPrimePool (Real.exp (Real.log level / 3)) := by
    intro p hp
    have hpList := List.mem_toFinset.mp hp
    have hpOld : p ∈ iwaniecStrictPrimePool z := by
      simpa only [iwaniecDescendingFactors, Finset.mem_sort] using hsub.subset hpList
    exact mem_iwaniecStrictPrimePool.mpr
      ⟨(mem_iwaniecStrictPrimePool.mp hpOld).1, iwaniec_cube_lt_imp_lt_cutoff hy (hcubes p hpList)⟩
  have hnew := iwaniecDescendingFactors_sublist_of_subset hsubset
  rw [iwaniecDescendingFactors_toFinset_of_orderedSublist hsub] at hnew
  exact Finset.mem_filter.mpr ⟨mem_iwaniecOrderedFactorSublists.mpr hnew, hdata⟩

theorem iwaniecPaperA_even_initial {rank : Nat} (hr : Even rank)
    {level s : Real} (hy : 1 < level) (hs : 0 < s) (hs3 : s ≤ 3) :
    iwaniecPaperA rank level s = iwaniecPaperA rank level 3 := by
  have hcap := iwaniecPaperFiniteSupport_even_capped hr hy (iwaniecPaperCutoff_antitone hy hs hs3)
  have hh := congrArg Finset.card hcap
  simpa only [iwaniecPaperFiniteSupport_card, iwaniecPaperA] using hh

end

end Erdos1212Kernel
