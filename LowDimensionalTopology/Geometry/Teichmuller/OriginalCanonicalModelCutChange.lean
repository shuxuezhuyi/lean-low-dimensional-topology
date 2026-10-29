module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalFuchsianModel
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalGeneratorMarkedSurface

/-!
# Changing an original cut with the same based ordered family

The endpoint casts place both sets of side loops at the same original point.
Equality of their actual based classes makes their lifts have equal endpoints.
Uniqueness for the same covering then identifies their whole deck actions.
Only the cut changes: the supplied model, lift point and all matrices remain.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

private theorem endpointDeck_action_eq_of_original_family
    {g : ℕ} (hg : 1 < g) (N : OriginalGeneratorMarkedSurface g)
    (E E' : OriginalOrientedCanonicalCut N.surface g
      (lt_trans Nat.zero_lt_one hg) N.point)
    (hEE : E.family = E'.family)
    (M : HyperbolicSurfaceModel N.surface.toRiemannSurface)
    (z₀ : ℍ) (hz₀ : M.halfPlaneCover z₀ = N.point)
    (i : Fin g × Fin 2) (z : ℍ) :
    M.markedPolygonEndpointDeck E.polygon z₀ (hz₀.trans E.basepoint_eq.symm) i • z =
      M.markedPolygonEndpointDeck E'.polygon z₀ (hz₀.trans E'.basepoint_eq.symm) i • z := by
  have hclass : pathClass (E.loop i) = pathClass (E'.loop i) := congrFun hEE i
  have hpaths : (E.loop i).Homotopic (E'.loop i) := by
    apply (FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mp
    exact congrArg CategoryTheory.End.asHom hclass
  let hE := hz₀.trans E.basepoint_eq.symm
  let hE' := hz₀.trans E'.basepoint_eq.symm
  let A := M.markedPolygonLoopLift E.polygon z₀ hE i
  let B := M.markedPolygonLoopLift E'.polygon z₀ hE' i
  have hA := M.markedPolygonLoopLift_spec E.polygon z₀ hE i
  have hB := M.markedPolygonLoopLift_spec E'.polygon z₀ hE' i
  have h₀ : (E.loop i : C(unitInterval, N.carrier)) 0 = M.halfPlaneCover z₀ :=
    (E.loop i).source.trans hz₀.symm
  have h₀' : (E'.loop i : C(unitInterval, N.carrier)) 0 = M.halfPlaneCover z₀ :=
    (E'.loop i).source.trans hz₀.symm
  have hend := M.halfPlaneCover_covering.liftPath_apply_one_eq_of_homotopicRel
    hpaths z₀ h₀ h₀'
  change A 1 = B 1 at hend
  rw [hA.2.2, hB.2.2] at hend
  let dE := M.markedPolygonEndpointDeck E.polygon z₀ hE i
  let dE' := M.markedPolygonEndpointDeck E'.polygon z₀ hE' i
  have hwhole : (fun w : ℍ => dE • w) = (fun w : ℍ => dE' • w) := by
    apply M.halfPlaneCover_covering.eq_of_comp_eq
      (continuous_const_smul dE) (continuous_const_smul dE') ?_ z₀ hend
    funext w
    change M.halfPlaneCover (dE • w) = M.halfPlaneCover (dE' • w)
    rw [deck.proj_smul dE w, deck.proj_smul dE' w]
  exact congrFun hwhole z

namespace NormalizedCanonicalFuchsianModel

/-- Two original cuts with the same point and all the same based ordered
classes support the same actual normalized model and every same matrix. -/
theorem exists_changeOriginalCanonicalCut
    {g : ℕ} (hg : 1 < g) (N : OriginalGeneratorMarkedSurface g)
    (E E' : OriginalOrientedCanonicalCut N.surface g
      (lt_trans Nat.zero_lt_one hg) N.point)
    (hEE : E.family = E'.family)
    (P : NormalizedCanonicalFuchsianModel hg E.polygon
      (MarkedRiemannSurface.refl N.surface)) :
    ∃ Q : NormalizedCanonicalFuchsianModel hg E'.polygon
        (MarkedRiemannSurface.refl N.surface),
      Q.model = P.model ∧ Q.liftBase = P.liftBase ∧ Q.matrices = P.matrices := by
  have hOld := P.liftBase_proj
  change P.model.halfPlaneCover P.liftBase = E.polygon.symm (boundaryBase g).val at hOld
  have hz₀ : P.model.halfPlaneCover P.liftBase = N.point := hOld.trans E.basepoint_eq
  refine ⟨
    { model := P.model
      liftBase := P.liftBase
      liftBase_proj := ?_
      matrices := P.matrices
      represents := ?_
      alpha_attracting := P.alpha_attracting
      beta_attracting_repelling := P.beta_attracting_repelling }, rfl, rfl, rfl⟩
  · change P.model.halfPlaneCover P.liftBase = E'.polygon.symm (boundaryBase g).val
    exact hz₀.trans E'.basepoint_eq.symm
  · intro i z
    have hP := P.represents i z
    change P.matrices i • z =
      P.model.markedPolygonEndpointDeck E.polygon P.liftBase
        (hz₀.trans E.basepoint_eq.symm) i • z at hP
    exact hP.trans
      (endpointDeck_action_eq_of_original_family hg N E E' hEE P.model
        P.liftBase hz₀ i z)

end NormalizedCanonicalFuchsianModel

end LowDimensionalTopology.Geometry.Teichmuller
