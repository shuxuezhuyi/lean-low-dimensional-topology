module

public import LowDimensionalTopology.Geometry.Teichmuller.FrickeGeodesicLength
public import Mathlib.Analysis.SpecialFunctions.Arcosh

@[expose] public section
noncomputable section
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))

/-- The literal Fricke value is arcosh of the trace square of its same full-period cover. -/
theorem frickeGeodesicLength_coordinates_eq_arcosh_of_covers
    (α : LiZhongQC.Loop X) (m : MarkedRiemannSurface.{0, 0} R)
    (M : HyperbolicSurfaceModel m.surface.toRiemannSurface) (q : OriginalClosedGeodesic M)
    (hq : LiZhongQC.FreelyHomotopic
      ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩ q.toLoop)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hdeck : ∀ z : ℍ, M.halfPlaneCover (A • z) = M.halfPlaneCover z)
    (ht : 4 < (Matrix.trace A.val) ^ 2)
    (hcov : LiZhongQC.Covers M.halfPlaneCover A q.toLoop) :
    frickeGeodesicLength R hg hgenus hA hAlt α
      ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
        ⟨TeichmullerSpace.mk m, rfl⟩⟩ =
      Real.arcosh ((Matrix.trace A.val) ^ 2 / 2 - 1) := by
  rw [frickeGeodesicLength_coordinates_eq R hg hgenus hA hAlt α m M q hq]
  let := m.surface.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  have htrace := q.trace_sq_eq_four_cosh_length_sq_of_covers hp A
    ((hΓ A).2 hdeck) ht hcov
  have hdouble := Real.cosh_two_mul (q.length.toReal / 2)
  have hcs := Real.cosh_sq_sub_sinh_sq (q.length.toReal / 2)
  have harg : 2 * (q.length.toReal / 2) = q.length.toReal := by ring
  rw [harg] at hdouble
  have hcosh : (Matrix.trace A.val) ^ 2 / 2 - 1 = Real.cosh q.length.toReal := by
    nlinarith only [htrace, hdouble, hcs]
  rw [hcosh, Real.arcosh_cosh ENNReal.toReal_nonneg]

end LowDimensionalTopology.Geometry.Teichmuller
