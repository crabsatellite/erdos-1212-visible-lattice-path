import Erdos1212Kernel.TaoPNTArbitraryStrip
import Erdos1212Kernel.TaoPerronErrorSimplification

namespace Erdos1212Kernel

noncomputable section

theorem exists_taoVonMangoldtRieszSum_two_term_error_any_parameter (d : Real) (hd : 0 < d) :
    ∃ D H₀ : Real, 0 < D ∧ 1 ≤ H₀ ∧ ∀ H x : Real, H₀ ≤ H → 1 ≤ x →
      let L := Real.log (3 + H)
      ‖taoVonMangoldtRieszSum x - (x : Complex) / 2‖ ≤
        D * L ^ 2 * (x ^ (1 - d / L) + x ^ (1 + d / L) / H) := by
  obtain ⟨C, H₁, hC, hH₁, hstrip⟩ := exists_taoPNT_global_strip_any_parameter d hd
  let H₀ := max H₁ (Real.exp 1)
  refine ⟨taoPerronScalarConstant d C, H₀, taoPerronScalarConstant_pos hd hC.le,
    hH₁.trans (le_max_left _ _), ?_⟩
  intro H x hH hx
  have hH1 : H₁ ≤ H := (le_max_left _ _).trans hH
  have hHone : 1 ≤ H := hH₁.trans hH1
  have hHpos : 0 < H := by linarith
  have hL : 1 ≤ Real.log (3 + H) := by
    have hh : Real.exp 1 ≤ 3 + H := by linarith [(le_max_right H₁ (Real.exp 1)).trans hH]
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hh
  obtain ⟨hδ, hhalf, _⟩ := hstrip H 0 1 hH1 (by simpa using hHpos.le)
  have hraw := taoVonMangoldtRieszSum_error_of_strip hδ (show d / Real.log (3 + H) < 1 by linarith)
    hC.le hHpos hx (fun t u ht hu0 hu1 => (hstrip H t u hH1 ht).2.2 hu0 hu1)
  exact hraw.trans (taoPerronErrorBudget_simplified hd hC.le hL hHone
    (by linarith : 0 < x) hhalf)

end

end Erdos1212Kernel
