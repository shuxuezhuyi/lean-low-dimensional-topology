/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.External.LiZhongQC.Ch07.S27_TeichmullerExistence

/-!
# Composition of actual normalized lifts

The covering equations and the actual normalized homeomorphic extensions
compose together. The source predicate uses one universe for the surfaces;
no compactness or coefficient assumption is required.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open LiZhongQC
universe u

/-- Composing actual normalized lifts composes their covering equations,
homeomorphic extensions and the three actual endpoint normalizations. -/
theorem normalizedLift_comp
    {S₀ S₁ S₂ : Type u}
    [TopologicalSpace S₀] [ChartedSpace ℂ S₀]
    [TopologicalSpace S₁] [ChartedSpace ℂ S₁]
    [TopologicalSpace S₂] [ChartedSpace ℂ S₂]
    {p₀ : ℍ → S₀} {p₁ : ℍ → S₁} {p₂ : ℍ → S₂}
    {f : S₀ ≃ₜ S₁} {g : S₁ ≃ₜ S₂}
    {F H : ℍ ≃ₜ ℍ} {GF GH : ExtPlane → ExtPlane}
    (hF : IsNormalizedLift p₀ p₁ f F GF)
    (hH : IsNormalizedLift p₁ p₂ g H GH) :
    IsNormalizedLift p₀ p₂ (f.trans g) (F.trans H) (GH ∘ GF) := by
  have hmaps : MapsTo (liftToC F) upperHalf upperHalf := by
    intro z hz
    rw [h23l_liftToC_eq F hz]
    exact (F _).coe_im_pos
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro τ
    change p₂ (H (F τ)) = g (f (p₀ τ))
    rw [hH.1, hF.1]
  · apply s13x_th_isHomeoExtension_congr (hH.2.1.comp hF.2.1 hmaps)
    intro z hz
    rw [Function.comp_apply, h23l_liftToC_eq F hz,
      h23l_liftToC_coe H (F (UpperHalfPlane.ofComplex z)),
      h23l_liftToC_eq (F.trans H) hz]
    rfl
  · simpa only [Function.comp_apply, hF.2.2.1] using hH.2.2.1
  · simpa only [Function.comp_apply, hF.2.2.2.1] using hH.2.2.2.1
  · simpa only [Function.comp_apply, hF.2.2.2.2] using hH.2.2.2.2

end LowDimensionalTopology.Geometry.Teichmuller
