module
public import LowDimensionalTopology.Geometry.Surfaces.Covering.PlaneCoverQuotient
public import LowDimensionalTopology.Geometry.Surfaces.Covering.SphereUniversalDeck
@[expose] public section
noncomputable section
open Module
namespace LowDimensionalTopology.Geometry.Surfaces

/-- An actual analytic plane cover classifies its base by the genuine three conformal
plane-quotient models, with no presumed translation-group description. -/
theorem riemannSurface_planeCover_conformal_classification {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) (p : ℂ → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap complexPlaneRiemannSurface.toRiemannAtlas R.toRiemannAtlas p)
    (hs : Function.Surjective p) :
    RiemannConformallyEquivalent R complexPlaneRiemannSurface ∨
      RiemannConformallyEquivalent R puncturedPlaneRiemannSurface ∨
        ∃ b : Basis (Fin 2) ℝ ℂ, ∃ T : ComplexTorusModel b, RiemannConformallyEquivalent R T.surface := by
  obtain ⟨H, hT, hD, hno, hQ⟩ := riemannSurface_planeCover_translationQuotient R p hp ha hs
  rcases translationPlaneQuotient_conformal_trichotomy H hT hD hno with h | h | ⟨b, T, h⟩
  · exact Or.inl (hQ.trans h)
  · exact Or.inr (Or.inl (hQ.trans h))
  · exact Or.inr (Or.inr ⟨b, T, hQ.trans h⟩)

/-- The plane alternative for the genuinely constructed universal cover gives the complete
plane/punctured-plane/torus alternatives for its base; uniformization itself is separate. -/
theorem RiemannUniversalCover.plane_model_conformal_classification
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X} (C : RiemannUniversalCover R)
    (hc : @RiemannConformallyEquivalent C.space ℂ C.topology _ C.surface complexPlaneRiemannSurface) :
    RiemannConformallyEquivalent R complexPlaneRiemannSurface ∨
      RiemannConformallyEquivalent R puncturedPlaneRiemannSurface ∨
        ∃ b : Basis (Fin 2) ℝ ℂ, ∃ T : ComplexTorusModel b, RiemannConformallyEquivalent R T.surface := by
  obtain ⟨H, hT, hD, hno, hQ⟩ := C.translationQuotient_of_conformallyEquivalent_plane hc
  rcases translationPlaneQuotient_conformal_trichotomy H hT hD hno with h | h | ⟨b, T, h⟩
  · exact Or.inl (hQ.trans h)
  · exact Or.inr (Or.inl (hQ.trans h))
  · exact Or.inr (Or.inr ⟨b, T, hQ.trans h⟩)

end LowDimensionalTopology.Geometry.Surfaces
