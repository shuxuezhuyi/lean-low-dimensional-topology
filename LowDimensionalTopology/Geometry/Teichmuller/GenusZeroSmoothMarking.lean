module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.MarkedGenusZeroSurfaces
public import LowDimensionalTopology.Geometry.Teichmuller.ConformalSmooth

/-!
# Smooth positive markings between original genus-zero surfaces

Two genuine analytic sphere coordinates give a biholomorphism between the
unchanged original surfaces. Its induced real smooth equivalence preserves
both complex orientations. No smoothing hypothesis is used.
-/

@[expose] public section

noncomputable section

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Any two original closed genus-zero Riemann surfaces admit a positive real
smooth equivalence which is analytic in both directions in their original atlases. -/
theorem genus_zero_exists_positive_smooth_equiv
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y)
    (hR : R.HasGenus 0) (hS : S.HasGenus 0) :
    ∃ F : SmoothSurfaceEquiv R.toRiemannSurface S.toRiemannSurface,
      PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas F.toHomeomorph ∧
      RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas F.toHomeomorph ∧
      RiemannAnalyticMap S.toRiemannAtlas R.toRiemannAtlas F.toHomeomorph.symm := by
  obtain ⟨e, he, hei⟩ := genus_zero_exists_analytic_sphere_coordinate R.toRiemannSurface hR
  obtain ⟨f, hf, hfi⟩ := genus_zero_exists_analytic_sphere_coordinate S.toRiemannSurface hS
  let h : X ≃ₜ Y := e.trans f.symm
  have hh : RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas h := hfi.comp he
  have hhi : RiemannAnalyticMap S.toRiemannAtlas R.toRiemannAtlas h.symm := hei.comp hf
  refine ⟨SmoothSurfaceEquiv.ofConformalHomeomorph R.toRiemannSurface S.toRiemannSurface h hh,
    SmoothSurfaceEquiv.ofConformalHomeomorph_preservesComplexOrientation
      R.toRiemannSurface S.toRiemannSurface h hh, ?_, ?_⟩
  · simpa only [SmoothSurfaceEquiv.ofConformalHomeomorph_toHomeomorph] using hh
  · simpa only [SmoothSurfaceEquiv.ofConformalHomeomorph_toHomeomorph] using hhi

end LowDimensionalTopology.Geometry.Teichmuller
