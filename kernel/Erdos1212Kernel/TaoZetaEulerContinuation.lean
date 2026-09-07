import Erdos1212Kernel.TaoZetaEulerLocallyUniform

namespace Erdos1212Kernel

noncomputable section

open Filter Topology

set_option maxHeartbeats 1900000

theorem taoZetaEulerLimit_differentiableOn_upper :
    DifferentiableOn Complex taoZetaEulerLimit taoZetaUpperDomain := by
  have hF : ∀ᶠ N : Nat in atTop,
      DifferentiableOn Complex (fun s => taoZetaEulerApprox s N) taoZetaUpperDomain := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact taoZetaEulerApprox_differentiableOn_upper N hN
  exact taoZetaEulerApprox_tendstoLocallyUniformlyOn_upper.differentiableOn hF taoZetaUpperDomain_isOpen

theorem taoZetaEulerLimit_differentiableOn_lower :
    DifferentiableOn Complex taoZetaEulerLimit taoZetaLowerDomain := by
  have hF : ∀ᶠ N : Nat in atTop,
      DifferentiableOn Complex (fun s => taoZetaEulerApprox s N) taoZetaLowerDomain := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    exact taoZetaEulerApprox_differentiableOn_lower N hN
  exact taoZetaEulerApprox_tendstoLocallyUniformlyOn_lower.differentiableOn hF taoZetaLowerDomain_isOpen

theorem riemannZeta_differentiableOn_upper :
    DifferentiableOn Complex riemannZeta taoZetaUpperDomain := by
  intro s hs
  apply (differentiableAt_riemannZeta ?_).differentiableWithinAt
  intro h
  have him := hs.2
  rw [h] at him
  norm_num at him

theorem riemannZeta_differentiableOn_lower :
    DifferentiableOn Complex riemannZeta taoZetaLowerDomain := by
  intro s hs
  apply (differentiableAt_riemannZeta ?_).differentiableWithinAt
  intro h
  have him := hs.2
  rw [h] at him
  norm_num at him

theorem taoZetaEulerLimit_eq_riemannZeta_upper {s : Complex} (hs : s ∈ taoZetaUpperDomain) :
    taoZetaEulerLimit s = riemannZeta s := by
  have hfa : AnalyticOnNhd Complex taoZetaEulerLimit taoZetaUpperDomain :=
    taoZetaEulerLimit_differentiableOn_upper.analyticOnNhd taoZetaUpperDomain_isOpen
  have hga : AnalyticOnNhd Complex riemannZeta taoZetaUpperDomain :=
    riemannZeta_differentiableOn_upper.analyticOnNhd taoZetaUpperDomain_isOpen
  let z₀ : Complex := 2 + Complex.I
  have hz₀ : z₀ ∈ taoZetaUpperDomain := by
    constructor <;> norm_num [z₀]
  let V : Set Complex := {z | 1 < z.re ∧ 0 < z.im}
  have hVopen : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).and
      (isOpen_lt continuous_const Complex.continuous_im)
  have hVmem : V ∈ 𝓝 z₀ := hVopen.mem_nhds (by constructor <;> norm_num [V, z₀])
  have hevent : taoZetaEulerLimit =ᶠ[𝓝 z₀] riemannZeta := by
    filter_upwards [hVmem] with z hz
    exact taoZetaEulerLimit_eq_riemannZeta hz.1 (by
      intro h
      have him := hz.2
      rw [h] at him
      norm_num at him)
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga taoZetaUpperDomain_convex.isPreconnected
    hz₀ hevent hs

theorem taoZetaEulerLimit_eq_riemannZeta_lower {s : Complex} (hs : s ∈ taoZetaLowerDomain) :
    taoZetaEulerLimit s = riemannZeta s := by
  have hfa : AnalyticOnNhd Complex taoZetaEulerLimit taoZetaLowerDomain :=
    taoZetaEulerLimit_differentiableOn_lower.analyticOnNhd taoZetaLowerDomain_isOpen
  have hga : AnalyticOnNhd Complex riemannZeta taoZetaLowerDomain :=
    riemannZeta_differentiableOn_lower.analyticOnNhd taoZetaLowerDomain_isOpen
  let z₀ : Complex := 2 - Complex.I
  have hz₀ : z₀ ∈ taoZetaLowerDomain := by
    constructor <;> norm_num [z₀]
  let V : Set Complex := {z | 1 < z.re ∧ z.im < 0}
  have hVopen : IsOpen V :=
    (isOpen_lt continuous_const Complex.continuous_re).and
      (isOpen_lt Complex.continuous_im continuous_const)
  have hVmem : V ∈ 𝓝 z₀ := hVopen.mem_nhds (by constructor <;> norm_num [V, z₀])
  have hevent : taoZetaEulerLimit =ᶠ[𝓝 z₀] riemannZeta := by
    filter_upwards [hVmem] with z hz
    exact taoZetaEulerLimit_eq_riemannZeta hz.1 (by
      intro h
      have him := hz.2
      rw [h] at him
      norm_num at him)
  exact hfa.eqOn_of_preconnected_of_eventuallyEq hga taoZetaLowerDomain_convex.isPreconnected
    hz₀ hevent hs

end

end Erdos1212Kernel
