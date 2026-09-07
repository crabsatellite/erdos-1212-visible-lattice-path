import Erdos1212Kernel.TaoZetaEulerIdentification
import Mathlib.Analysis.Complex.LocallyUniformLimit

namespace Erdos1212Kernel

noncomputable section

def taoZetaUpperDomain : Set Complex := {s | 0 < s.re ∧ 0 < s.im}
def taoZetaLowerDomain : Set Complex := {s | 0 < s.re ∧ s.im < 0}

theorem taoZetaUpperDomain_isOpen : IsOpen taoZetaUpperDomain := by
  exact (isOpen_lt continuous_const Complex.continuous_re).and
    (isOpen_lt continuous_const Complex.continuous_im)

theorem taoZetaLowerDomain_isOpen : IsOpen taoZetaLowerDomain := by
  exact (isOpen_lt continuous_const Complex.continuous_re).and
    (isOpen_lt Complex.continuous_im continuous_const)

theorem taoZetaUpperDomain_convex : Convex Real taoZetaUpperDomain := by
  exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_gt 0)

theorem taoZetaLowerDomain_convex : Convex Real taoZetaLowerDomain := by
  exact (convex_halfSpace_re_gt 0).inter (convex_halfSpace_im_lt 0)

theorem taoZetaEulerApprox_differentiableOn (N : Nat) (hN : 1 ≤ N) :
    DifferentiableOn Complex (fun s => taoZetaEulerApprox s N) ({1}ᶜ) := by
  intro s hs
  unfold taoZetaEulerApprox
  have hs1 : s ≠ 1 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs
  have hsum : DifferentiableAt Complex
      (fun z => ∑ n ∈ Finset.Ico 1 N, (n : Complex) ^ (-z)) s := by
    have hterm : ∀ n ∈ Finset.Ico 1 N,
        DifferentiableAt Complex (fun z => (n : Complex) ^ (-z)) s := by
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Ico.mp hn).1
      have hn0 : (n : Complex) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      exact differentiableAt_id.neg.const_cpow (Or.inl hn0)
    exact (HasDerivAt.fun_sum (u := Finset.Ico 1 N)
      (fun n hn => (hterm n hn).hasDerivAt)).differentiableAt
  have hN0 : (N : Complex) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hinner : DifferentiableAt Complex (fun z : Complex => 1 - z) s :=
    (differentiableAt_const (c := (1 : Complex))).sub differentiableAt_id
  have hnum : DifferentiableAt Complex (fun z => (N : Complex) ^ (1 - z)) s :=
    hinner.const_cpow (c := (N : Complex)) (Or.inl hN0)
  have hden : DifferentiableAt Complex (fun z => z - 1) s :=
    differentiableAt_id.sub (differentiableAt_const (c := (1 : Complex)))
  exact (hsum.add (hnum.div hden (sub_ne_zero.mpr hs1))).differentiableWithinAt

theorem taoZetaEulerApprox_differentiableOn_upper (N : Nat) (hN : 1 ≤ N) :
    DifferentiableOn Complex (fun s => taoZetaEulerApprox s N) taoZetaUpperDomain :=
  (taoZetaEulerApprox_differentiableOn N hN).mono (by
    intro s hs
    have him : 0 < s.im := hs.2
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    rw [h] at him
    norm_num at him)

theorem taoZetaEulerApprox_differentiableOn_lower (N : Nat) (hN : 1 ≤ N) :
    DifferentiableOn Complex (fun s => taoZetaEulerApprox s N) taoZetaLowerDomain :=
  (taoZetaEulerApprox_differentiableOn N hN).mono (by
    intro s hs
    have him : s.im < 0 := hs.2
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    rw [h] at him
    norm_num at him)

end

end Erdos1212Kernel
