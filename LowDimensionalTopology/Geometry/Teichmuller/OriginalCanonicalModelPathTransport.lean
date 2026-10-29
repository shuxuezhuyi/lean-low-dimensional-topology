module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedCanonicalFuchsianModel
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalGeneratorMarkedSurface
public import LowDimensionalTopology.External.TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange

/-!
# A supplied original normalized model along one common path

Every ordered based class is transported through the same actual path.
Lifting that path once moves the lift point while retaining the original
cover and every matrix of the supplied normalized model. Monodromy of
concatenation and its compatibility with deck actions keep the endpoint
convention explicit throughout.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

namespace NormalizedCanonicalFuchsianModel

/-- A single actual common path transports the lift point of any supplied
normalized model, preserving its physical covering and all its matrices. -/
theorem exists_transportOriginalCanonicalPath
    {g : ℕ} (hg : 1 < g)
    (B N : OriginalGeneratorMarkedSurface g)
    (D : OriginalOrientedCanonicalCut B.surface g
      (lt_trans Nat.zero_lt_one hg) B.point)
    (hD : D.family = B.classes)
    (E : OriginalOrientedCanonicalCut N.surface g
      (lt_trans Nat.zero_lt_one hg) N.point)
    (hE : E.family = N.classes)
    (F : SmoothSurfaceEquiv B.surface.toRiemannSurface N.surface.toRiemannSurface)
    (hF : PreservesComplexOrientation B.surface.toRiemannAtlas
      N.surface.toRiemannAtlas F.toHomeomorph)
    (c : Path (F.toHomeomorph B.point) N.point)
    (hslots : ∀ i : Fin g × Fin 2,
      FundamentalGroup.fundamentalGroupMulEquivOfPath c
        (FundamentalGroup.map
          (⟨F.toHomeomorph, F.toHomeomorph.continuous⟩ : C(B.carrier, N.carrier))
          B.point (B.classes i)) = N.classes i) :
    let mF : MarkedRiemannSurface.{0, 0} B.surface :=
      { carrier := N.carrier
        topology := N.topology
        surface := N.surface
        marking := F
        orientation_preserving := hF }
    ∀ P : NormalizedCanonicalFuchsianModel hg D.polygon mF,
      ∃ (L : C(unitInterval, UpperHalfPlane))
        (Q : NormalizedCanonicalFuchsianModel hg E.polygon
          (MarkedRiemannSurface.refl N.surface)),
        (∀ t, P.model.halfPlaneCover (L t) = c t) ∧
          L 0 = P.liftBase ∧ L 1 = Q.liftBase ∧
          Q.model = P.model ∧ Q.matrices = P.matrices := by
  dsimp only
  intro P
  let M := P.model
  let eOld := F.toHomeomorph.symm.trans D.polygon
  have hzOld : M.halfPlaneCover P.liftBase = eOld.symm (boundaryBase g).val :=
    P.liftBase_proj
  have hz₀ : M.halfPlaneCover P.liftBase = F.toHomeomorph B.point :=
    hzOld.trans (congrArg F.toHomeomorph D.basepoint_eq)
  let cov := M.halfPlaneCover_covering
  let q := covering_deck_isQuotientCoveringMap cov M.halfPlaneCover_surjective
  let e₀ : M.halfPlaneCover ⁻¹' {F.toHomeomorph B.point} := ⟨P.liftBase, hz₀⟩
  let cq := Path.Homotopic.Quotient.mk c
  let e₁ : M.halfPlaneCover ⁻¹' {N.point} := cov.monodromy cq e₀
  let L := cov.liftPath c P.liftBase (c.source.trans hz₀.symm)
  have hL : M.halfPlaneCover ∘ L = c := cov.liftPath_lifts _ _ _
  have hL₀ : L 0 = P.liftBase := cov.liftPath_zero _ _ _
  have hL₁ : L 1 = e₁.val := (cov.coe_monodromy_mk c e₀).symm
  have hz₁ : M.halfPlaneCover e₁.val = E.polygon.symm (boundaryBase g).val :=
    e₁.property.trans E.basepoint_eq.symm
  have hrep : ∀ (i : Fin g × Fin 2) (z : ℍ), P.matrices i • z =
      M.markedPolygonEndpointDeck E.polygon e₁.val hz₁ i • z := by
    intro i z
    let α := (D.loop i).map F.toHomeomorph.continuous
    let β := E.loop i
    let aq := Path.Homotopic.Quotient.mk α
    let bq := Path.Homotopic.Quotient.mk β
    have hα : FundamentalGroup.map
        (⟨F.toHomeomorph, F.toHomeomorph.continuous⟩ : C(B.carrier, N.carrier))
        B.point (D.family i) = pathClass α :=
      TauCeti.FundamentalGroup.map_fromPath
        (⟨F.toHomeomorph, F.toHomeomorph.continuous⟩ : C(B.carrier, N.carrier))
        B.point (D.loop i)
    have hclasses : FundamentalGroup.fundamentalGroupMulEquivOfPath c
        (pathClass α) = pathClass β := by
      have h := hslots i
      rw [← congrFun hD i, ← congrFun hE i, hα] at h
      exact h
    rw [FundamentalGroup.fundamentalGroupMulEquivOfPath_apply] at hclasses
    have hclassq := congrArg CategoryTheory.End.asHom hclasses
    change cq.symm.trans (aq.trans cq) = bq at hclassq
    have hsq : aq.trans cq = cq.trans bq := by
      have he := congrArg (fun a => cq.trans a) hclassq
      simpa only [← Path.Homotopic.Quotient.trans_assoc,
        Path.Homotopic.Quotient.trans_symm, Path.Homotopic.Quotient.refl_trans] using he
    let dOld := M.markedPolygonEndpointDeck eOld P.liftBase hzOld i
    let dNew := M.markedPolygonEndpointDeck E.polygon e₁.val hz₁ i
    have hOld := M.markedPolygonLoopLift_spec eOld P.liftBase hzOld i
    have hNew := M.markedPolygonLoopLift_spec E.polygon e₁.val hz₁ i
    have hαm : cov.monodromy aq e₀ = q.toPermFiber (F.toHomeomorph B.point) dOld e₀ := by
      apply Subtype.ext
      calc
        _ = M.markedPolygonLoopLift eOld P.liftBase hzOld i 1 :=
          cov.monodromy_eq_apply_one
            (e := e₀) (Γ := M.markedPolygonLoopLift eOld P.liftBase hzOld i)
            (by funext t; exact congrFun hOld.1 t) hOld.2.1
        _ = dOld • P.liftBase := hOld.2.2
    have hβm : cov.monodromy bq e₁ = q.toPermFiber N.point dNew e₁ := by
      apply Subtype.ext
      calc
        _ = M.markedPolygonLoopLift E.polygon e₁.val hz₁ i 1 :=
          cov.monodromy_eq_apply_one
            (e := e₁) (Γ := M.markedPolygonLoopLift E.polygon e₁.val hz₁ i)
            (by funext t; exact congrFun hNew.1 t) hNew.2.1
        _ = dNew • e₁.val := hNew.2.2
    have hend : q.toPermFiber N.point dOld e₁ = q.toPermFiber N.point dNew e₁ := by
      calc
        _ = cov.monodromy cq
            (q.toPermFiber (F.toHomeomorph B.point) dOld e₀) :=
          (q.monodromy_toPermFiber (g := dOld) (γ := cq) (e := e₀)).symm
        _ = cov.monodromy cq (cov.monodromy aq e₀) := by rw [hαm]
        _ = cov.monodromy (aq.trans cq) e₀ :=
          (cov.monodromy_trans_apply aq cq e₀).symm
        _ = cov.monodromy (cq.trans bq) e₀ := by rw [hsq]
        _ = cov.monodromy bq e₁ := cov.monodromy_trans_apply cq bq e₀
        _ = q.toPermFiber N.point dNew e₁ := hβm
    have hwhole : (fun w : ℍ => dOld • w) = (fun w : ℍ => dNew • w) := by
      apply cov.eq_of_comp_eq
        (continuous_const_smul dOld) (continuous_const_smul dNew) ?_ e₁.val
        (congrArg Subtype.val hend)
      funext w
      change M.halfPlaneCover (dOld • w) = M.halfPlaneCover (dNew • w)
      rw [deck.proj_smul dOld w, deck.proj_smul dNew w]
    have hP := P.represents i z
    change P.matrices i • z = dOld • z at hP
    exact hP.trans (congrFun hwhole z)
  let Q : NormalizedCanonicalFuchsianModel hg E.polygon
      (MarkedRiemannSurface.refl N.surface) :=
    { model := P.model
      liftBase := e₁.val
      liftBase_proj := hz₁
      matrices := P.matrices
      represents := hrep
      alpha_attracting := P.alpha_attracting
      beta_attracting_repelling := P.beta_attracting_repelling }
  exact ⟨L, Q, fun t => congrFun hL t, hL₀, hL₁, rfl, rfl⟩

end NormalizedCanonicalFuchsianModel

end LowDimensionalTopology.Geometry.Teichmuller
