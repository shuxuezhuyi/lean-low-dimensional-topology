module

public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.EuclideanQuotientSurfaces
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.AnalyticLifting
public import LowDimensionalTopology.Geometry.Surfaces.Covering.PlaneUniversalDeck

/-!
# Affine lifts of actual native complex-torus isomorphisms

This uses only the existing native analytic plane coverings and plane
analytic-automorphism classification. It supplies the geometric lift and lattice
transport needed before the arithmetic SL(2,Z) classification. It does not define
an ordered torus marking or assert the marked-torus parameter theorem.
-/

@[expose] public section

noncomputable section

open Set Module

namespace LowDimensionalTopology.Geometry.Surfaces

/-- An actual analytic homeomorphism of native complex tori lifts to an
invertible entire affine map of their original covering planes. -/
theorem ComplexTorusModel.analytic_homeomorph_has_affine_lift
    {b c : Basis (Fin 2) ℝ ℂ} (T : ComplexTorusModel b) (U : ComplexTorusModel c)
    (f : ComplexTorusCarrier ≃ₜ ComplexTorusCarrier)
    (hf : RiemannAnalyticMap T.surface.toRiemannAtlas U.surface.toRiemannAtlas f) :
    ∃ a d : ℂ, a ≠ 0 ∧
      ∀ z : ℂ, f (T.projection z) = U.projection (a * z + d) := by
  let C : RiemannUniversalCover U.surface :=
    { space := ℂ
      topology := inferInstance
      surface := complexPlaneRiemannSurface
      simplyConnected := inferInstance
      projection := f ∘ T.projection
      covering := T.covering.homeomorph_comp f
      surjective := f.surjective.comp T.surjective
      analytic_projection := hf.comp T.analytic_projection }
  let D : RiemannUniversalCover U.surface :=
    { space := ℂ
      topology := inferInstance
      surface := complexPlaneRiemannSurface
      simplyConnected := inferInstance
      projection := U.projection
      covering := U.covering
      surjective := U.surjective
      analytic_projection := U.analytic_projection }
  obtain ⟨w, hw⟩ := U.surjective (f (T.projection 0))
  obtain ⟨F, hF, _⟩ := C.existsUnique_analytic_homeomorph_over D 0 w hw.symm
  have hFa : AnalyticOnNhd ℂ F univ :=
    (complexPlaneRiemannSurface_analytic_iff F).mp hF.2.2.1
  obtain ⟨a, d, ha, hform⟩ := plane_analytic_automorphism_affine F hFa
  refine ⟨a, d, ha, ?_⟩
  intro z
  have hproj : U.projection (F z) = f (T.projection z) := congrFun hF.2.1 z
  rw [hform z] at hproj
  exact hproj.symm

/-- The actual affine lift carries precisely the two original integer period
lattices onto each other; the proof uses the real covering fibres and injectivity
of the given surface isomorphism. -/
theorem ComplexTorusModel.analytic_homeomorph_scales_period_lattice
    {b c : Basis (Fin 2) ℝ ℂ} (T : ComplexTorusModel b) (U : ComplexTorusModel c)
    (f : ComplexTorusCarrier ≃ₜ ComplexTorusCarrier)
    (hf : RiemannAnalyticMap T.surface.toRiemannAtlas U.surface.toRiemannAtlas f) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ v : ℂ,
      v ∈ Submodule.span ℤ (Set.range b) ↔
        a * v ∈ Submodule.span ℤ (Set.range c) := by
  obtain ⟨a, d, ha, hcomm⟩ := T.analytic_homeomorph_has_affine_lift U f hf
  have hzero : f (T.projection 0) = U.projection d := by
    simpa only [mul_zero, zero_add] using hcomm 0
  refine ⟨a, ha, ?_⟩
  intro v
  constructor
  · intro hv
    have hTv : T.projection v = T.projection 0 :=
      (T.fiber_iff v 0).mpr (by simpa only [sub_zero] using hv)
    have hUv : U.projection (a * v + d) = U.projection d :=
      (hcomm v).symm.trans ((congrArg f hTv).trans hzero)
    have hmem := (U.fiber_iff (a * v + d) d).mp hUv
    simpa only [add_sub_cancel_right] using hmem
  · intro hv
    have hUv : U.projection (a * v + d) = U.projection d :=
      (U.fiber_iff (a * v + d) d).mpr (by simpa only [add_sub_cancel_right] using hv)
    have hTv : T.projection v = T.projection 0 :=
      f.injective ((hcomm v).trans (hUv.trans hzero.symm))
    simpa only [sub_zero] using (T.fiber_iff v 0).mp hTv

end LowDimensionalTopology.Geometry.Surfaces
