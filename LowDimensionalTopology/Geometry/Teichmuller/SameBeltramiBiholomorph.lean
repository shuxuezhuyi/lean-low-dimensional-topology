/- Released under Apache 2.0 license as described in the file LICENSE. -/
module

public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedUniqueness

/-!
# Equal Beltrami coefficients give a biholomorphic target change

The source carrier and both target complex structures are retained. The maps
may have different targets; their common measurable coefficient is specified
in the original source charts.

Adapted from Wu Xiaobin's Li-Zhong-QC-formalization, fixed commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0),
`Lemmas/UniformizedUniqueness.lean`, proof of `utm_d_biholomorphic`.
The Teichmüller-map premise is replaced by its actual QC and coefficient data,
and the two target carriers are independent. See `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open Set Metric Filter Topology MeasureTheory
open scoped ENNReal NNReal Real ComplexConjugate ContDiff Manifold

namespace LowDimensionalTopology.Geometry.Teichmuller

open LiZhongQC

universe u v w

/-- Two actual QC homeomorphisms with the same Beltrami coefficient differ by
biholomorphic postcomposition, including when their targets are different. -/
theorem sameBeltrami_biholomorphic
    {X : Type u} {Y : Type v} {Z : Type w}
    [TopologicalSpace X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
    [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]
    {f₀ : X ≃ₜ Y} {f : X ≃ₜ Z} {μ : X → ℂ → ℂ} {k : ℝ}
    (hf₀ : IsQCRS f₀) (hf : IsQCRS f) (hk : k < 1)
    (hBel : IsBeltramiDifferential μ k)
    (hμ₀ : ∀ x : X, ∀ᵐ z ∂(volume.restrict (localMapDomain f₀ x)),
      complexDilatation (localMapExpr f₀ x) z = μ x z)
    (hμf : ∀ x : X, ∀ᵐ z ∂(volume.restrict (localMapDomain f x)),
      complexDilatation (localMapExpr f x) z = μ x z) :
    IsBiholomorphic (f₀.symm.trans f) := by
  obtain ⟨K, hK⟩ := hf
  obtain ⟨K', hK'⟩ := hf₀
  set F := f₀.symm.trans f with hF
  refine (isKQCRS_one_iff F).1 ⟨le_rfl, fun y => ?_⟩
  refine s23_lg (s23_localMapDomain_isOpen F.continuous y) le_rfl
    (s23_c1_injOn_localMapExpr F.injective y) fun w₀ hw₀ => ?_
  obtain ⟨U, hUo, hw₀U, hUD, hU⟩ := s23_c_decomp f₀.symm f y hw₀
  set p₀ := (chartAt ℂ y).symm w₀ with hp₀
  set x₀ := f₀.symm p₀ with hx₀
  have hfx₀ : f₀ x₀ = p₀ := f₀.apply_symm_apply p₀
  -- the plane step on `D`
  set D := localMapDomain f x₀ ∩ localMapDomain f₀ x₀ with hD
  have hDo : IsOpen D :=
    (s23_localMapDomain_isOpen f.continuous x₀).inter (s23_localMapDomain_isOpen f₀.continuous x₀)
  have hL₂ : IsKQC (localMapExpr f x₀) D K :=
    ac_t_isKQC_restrict (hK.2 x₀) hDo inter_subset_left
  have hL₀ : IsKQC (localMapExpr f₀ x₀) D K' :=
    ac_t_isKQC_restrict (hK'.2 x₀) hDo inter_subset_right
  have hBD : IsBeltramiCoeff (μ x₀) D k := by
    have hsub : D ⊆ (chartAt ℂ x₀).target := fun z hz => hz.1.1
    exact ⟨(hBel.2 x₀).1.mono_set hsub,
      ae_restrict_of_ae_restrict_of_subset hsub (hBel.2 x₀).2⟩
  obtain ⟨φ, hφ, hφeq⟩ := same_dilatation_conformal hDo hk hBD
    (utm_d_genHomeo hL₀ (ae_restrict_of_ae_restrict_of_subset inter_subset_right (hμ₀ x₀)))
    (utm_d_genHomeo hL₂ (ae_restrict_of_ae_restrict_of_subset inter_subset_left (hμf x₀)))
  have hV : IsOpen (localMapExpr f₀ x₀ '' D) := isOpen_image_of_isKQC hL₀
  -- the neighbourhood `W` of `w₀`
  set W := U ∩ ((chartAt ℂ y).target ∩ (chartAt ℂ y).symm ⁻¹' (chartAt ℂ p₀).source) with hW
  have hWo : IsOpen W :=
    hUo.inter ((chartAt ℂ y).isOpen_inter_preimage_symm (chartAt ℂ p₀).open_source)
  have hWD : W ⊆ localMapDomain F y := inter_subset_left.trans hUD
  -- on `W` the expression is `T₃ ∘ φ ∘ T₁`
  have hform : ∀ w ∈ W, localMapExpr F y w =
      (chartTransition (f (f₀.symm y)) (f x₀) ∘ φ ∘ chartTransition p₀ y) w ∧
      DifferentiableAt ℂ (chartTransition (f (f₀.symm y)) (f x₀) ∘ φ ∘ chartTransition p₀ y) w := by
    intro w hw
    obtain ⟨hwU, hwt, hws⟩ := hw
    obtain ⟨h1, h2, h3, h4, h5⟩ := hU w hwU
    set u := chartTransition p₀ y w with hu
    set v := localMapExpr f₀.symm p₀ u with hv
    have h1s : f₀.symm ((chartAt ℂ p₀).symm u) ∈ (chartAt ℂ x₀).source := h1.2
    have hvs : (chartAt ℂ x₀).symm v = f₀.symm ((chartAt ℂ p₀).symm u) :=
      (chartAt ℂ x₀).left_inv h1s
    have hv0 : v ∈ localMapDomain f₀ x₀ := by
      refine ⟨(chartAt ℂ x₀).map_source h1s, ?_⟩
      show f₀ ((chartAt ℂ x₀).symm v) ∈ (chartAt ℂ (f₀ x₀)).source
      rw [hvs, hfx₀, Homeomorph.apply_symm_apply]
      exact (chartAt ℂ p₀).map_target h1.1
    have hvD : v ∈ D := ⟨h2, hv0⟩
    have hL₀v : localMapExpr f₀ x₀ v = u := by
      show chartAt ℂ (f₀ x₀) (f₀ ((chartAt ℂ x₀).symm v)) = u
      rw [hvs, hfx₀, Homeomorph.apply_symm_apply]
      exact (chartAt ℂ p₀).right_inv h1.1
    have hφv : φ u = localMapExpr f x₀ v := by rw [hφeq v hvD, hL₀v]
    refine ⟨by rw [h5, Function.comp_apply, Function.comp_apply, hφv], ?_⟩
    have hT₁ := (s23_transition p₀ y hwt hws).1
    have hφd : DifferentiableAt ℂ φ u :=
      (hφ.1 u ⟨v, hvD, hL₀v⟩).differentiableAt (hV.mem_nhds ⟨v, hvD, hL₀v⟩)
    have hT₃ : DifferentiableAt ℂ (chartTransition (f (f₀.symm y)) (f x₀)) (φ u) := by
      rw [hφv]
      exact (s23_transition (f (f₀.symm y)) (f x₀) h3 h4).1
    exact hT₃.comp w (hφd.comp w hT₁)
  refine ⟨W, hWo, ⟨hw₀U, hw₀.1, mem_chart_source ℂ p₀⟩, hWD,
    isKQC_one_of_conformal hWo ⟨fun w hw => ?_,
      (s23_c1_injOn_localMapExpr F.injective y).mono hWD, rfl⟩⟩
  refine ((hform w hw).2.congr_of_eventuallyEq ?_).differentiableWithinAt
  exact Filter.eventuallyEq_of_mem (hWo.mem_nhds hw) fun w' hw' => (hform w' hw').1

end LowDimensionalTopology.Geometry.Teichmuller
