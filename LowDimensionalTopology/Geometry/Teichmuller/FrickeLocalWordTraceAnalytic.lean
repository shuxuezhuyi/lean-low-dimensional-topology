module

public import LowDimensionalTopology.Geometry.Teichmuller.FrickeLocalTraceAnalytic
public import LowDimensionalTopology.Geometry.Teichmuller.FrickeGeodesicLengthWordCovers

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Topology
namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R hg e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))

/-- A scalar trace-square germ for the original covering word extends the literal length locally. -/
theorem exists_local_analytic_frickeLength_extension_of_word_covers
    (α : LiZhongQC.Loop X) (hα : ¬ IsNullHomotopicLoop α)
    (w : FreeGroup (StandardLabels g))
    (v : nativeFrickeImage hA) (U : Set (Fin (6 * g - 6) → ℝ))
    (hU : U ∈ 𝓝 (v : Fin (6 * g - 6) → ℝ))
    (T : (Fin (6 * g - 6) → ℝ) → ℝ)
    (hT : AnalyticAt ℝ T (v : Fin (6 * g - 6) → ℝ)) (ht : 4 < T v)
    (hmatch : ∀ m : MarkedRiemannSurface.{0, 0} R,
      finiteFrickeCoordinates hA (TeichmullerSpace.mk m) ∈ U →
      T (finiteFrickeCoordinates hA (TeichmullerSpace.mk m)) =
        (Matrix.trace ((FreeGroup.lift (fun s =>
          (chosenCanonicalModel hA m).matrices ((edgeLabelEquiv g).symm s)) w).val)) ^ 2)
    (hcover : ∀ m : MarkedRiemannSurface.{0, 0} R,
      finiteFrickeCoordinates hA (TeichmullerSpace.mk m) ∈ U →
      let P := chosenCanonicalModel hA m
      let A := FreeGroup.lift (fun s => P.matrices ((edgeLabelEquiv g).symm s)) w
      ∃ β : LiZhongQC.Loop m.carrier,
        LiZhongQC.FreelyHomotopic
          ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩ β ∧
        (∀ z : ℍ, P.model.halfPlaneCover (A • z) = P.model.halfPlaneCover z) ∧
        LiZhongQC.Covers P.model.halfPlaneCover A β) :
    ∃ F : (Fin (6 * g - 6) → ℝ) → ℝ,
      AnalyticAt ℝ F (v : Fin (6 * g - 6) → ℝ) ∧
      ∃ W ∈ 𝓝 (v : Fin (6 * g - 6) → ℝ),
        ∀ t : nativeFrickeImage hA, (t : Fin (6 * g - 6) → ℝ) ∈ W →
          F t = frickeGeodesicLength R hg hgenus hA hAlt α t := by
  refine ⟨fun y => Real.arcosh (T y / 2 - 1),
    analyticAt_arcosh_traceSquare hT ht, U, hU, ?_⟩
  intro t htU
  obtain ⟨p, hp⟩ := (mem_nativeFrickeImage_iff hA t.val).mp t.property
  obtain ⟨m, rfl⟩ := Quotient.exists_rep p
  have heq : t = ⟨finiteFrickeCoordinates hA (TeichmullerSpace.mk m),
      ⟨TeichmullerSpace.mk m, rfl⟩⟩ := Subtype.ext hp.symm
  subst t
  obtain ⟨β, hβ, hdeck, hcov⟩ := hcover m htU
  let P := chosenCanonicalModel hA m
  let A := FreeGroup.lift (fun s => P.matrices ((edgeLabelEquiv g).symm s)) w
  have htrace := traceSquare_gt_four_of_essential_word_covers
    R hg hgenus α hα m P.model β hβ A hdeck hcov
  have hlen := frickeGeodesicLength_coordinates_eq_arcosh_of_word_covers
    R hg hgenus hA hAlt α m P.model β hβ A hdeck htrace hcov
  change Real.arcosh
      (T (finiteFrickeCoordinates hA (TeichmullerSpace.mk m)) / 2 - 1) = _
  rw [hmatch m htU]
  exact hlen.symm

end LowDimensionalTopology.Geometry.Teichmuller
