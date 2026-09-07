import Erdos1212Kernel.AlgebraicCorridorTopPolynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Splits

namespace Erdos1212Kernel

noncomputable section

theorem multiset_const_pow_lt_prod_of_forall
    {α : Type*} (s : Multiset α) (f : α → ℝ) {r : ℝ}
    (hr : 0 < r) (hs : s ≠ 0) (h : ∀ a ∈ s, r < f a) :
    r ^ s.card < (s.map f).prod := by
  induction s using Multiset.induction_on with
  | empty => exact (hs rfl).elim
  | cons a s ih =>
      by_cases hs0 : s = 0
      · subst s
        simpa using h a (Multiset.mem_cons_self a 0)
      · have ha : r < f a := h a (Multiset.mem_cons_self a s)
        have htail : r ^ s.card < (s.map f).prod :=
          ih hs0 (fun b hb => h b (Multiset.mem_cons_of_mem hb))
        have htailPos : 0 < (s.map f).prod := (pow_pos hr _).trans htail
        have hmul := mul_lt_mul htail ha.le hr htailPos.le
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hmul

theorem exists_complex_root_norm_sub_le_rpow
    (p : Polynomial ℂ) (hp : p ≠ 0) (hdegree : 0 < p.natDegree)
    (x : ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hlead : 1 ≤ ‖p.leadingCoeff‖) (heval : ‖p.eval x‖ ≤ ε) :
    ∃ β ∈ p.roots,
      ‖x - β‖ ≤ ε ^ ((p.natDegree : ℝ)⁻¹) := by
  let r : ℝ := ε ^ ((p.natDegree : ℝ)⁻¹)
  by_cases hε0 : ε = 0
  · subst ε
    have heval0 : p.eval x = 0 := by
      apply norm_eq_zero.mp
      exact le_antisymm heval (norm_nonneg _)
    refine ⟨x, (Polynomial.mem_roots hp).mpr heval0, ?_⟩
    simp only [sub_self, norm_zero]
    exact Real.rpow_nonneg (by norm_num) _
  by_contra hnot
  push_neg at hnot
  have hsplits : p.Splits := IsAlgClosed.splits p
  have hcard : p.roots.card = p.natDegree := hsplits.natDegree_eq_card_roots.symm
  have hroots : p.roots ≠ 0 := by
    intro hz
    rw [hz] at hcard
    simp at hcard
    omega
  have hr : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (lt_of_le_of_ne hε (Ne.symm hε0)) _
  have hprod := multiset_const_pow_lt_prod_of_forall p.roots
    (fun β : ℂ => ‖x - β‖) hr hroots (fun β hβ => hnot β hβ)
  have hrpow : r ^ p.natDegree = ε := by
    dsimp [r]
    exact Real.rpow_inv_natCast_pow hε hdegree.ne'
  rw [hcard, hrpow] at hprod
  have hright : (p.roots.map fun β : ℂ => ‖x - β‖).prod =
      ‖(p.roots.map fun β : ℂ => x - β).prod‖ := by
    induction p.roots using Multiset.induction_on with
    | empty => simp
    | cons a s ih => simp [ih, norm_mul]
  rw [hright] at hprod
  have hevalEq := hsplits.eval_eq_prod_roots x
  have hevalNorm : ‖p.eval x‖ = ‖p.leadingCoeff‖ *
      ‖(p.roots.map fun β : ℂ => x - β).prod‖ := by
    rw [hevalEq, norm_mul]
  have hstrict : ε < ‖p.eval x‖ := by
    rw [hevalNorm]
    exact hprod.trans_le (le_mul_of_one_le_left (norm_nonneg _) hlead)
  linarith

end

end Erdos1212Kernel
