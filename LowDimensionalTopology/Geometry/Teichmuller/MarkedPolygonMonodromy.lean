module

public import LowDimensionalTopology.Geometry.Teichmuller.GeometricPolygonDeckMarking

/-!
# Actual monodromy for any given geometric polygon marking

The homeomorphism here is an arbitrary actual marking supplied by the caller,
not the homeomorphism selected from an unpointed genus existence witness.
All its positive polygon sides are pulled back as genuine original-surface
paths. Their actual covering endpoints give one multiplicative deck marking.
The result does not require, assert, or manufacture preservation of complex
orientation or existence of a normalized analytic frame.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Surfaces

open HandlePresentation
open LowDimensionalTopology.Geometry.Teichmuller

variable {X : Type*} [TopologicalSpace X] {g : ℕ}

/-- The genuine positive side loop of the given geometric marking. -/
def markedPolygonLoop (e : X ≃ₜ PolygonQuotient g) (d : Edge g) :
    Path (e.symm (boundaryBase g).val) (e.symm (boundaryBase g).val) :=
  (positivePolygonLoop d).map e.symm.continuous

/-- Fundamental-group transport for this actual given marking. -/
def markedPolygonFundamentalEquiv (hg : 0 < g) (e : X ≃ₜ PolygonQuotient g) :
    FundamentalGroup X (e.symm (boundaryBase g).val) ≃* LiZhongQC.surfaceGroup g :=
  (TauCeti.FundamentalGroup.homeomorphMulEquiv e.symm (boundaryBase g).val).symm.trans
    (polygonBoundaryFundamentalGroupMulEquivSurfaceGroup g hg)

private theorem markedPolygonLoop_image (hg : 0 < g) (e : X ≃ₜ PolygonQuotient g) :
    ∃ c : LiZhongQC.surfaceGroup g, ∀ d : Edge g,
      markedPolygonFundamentalEquiv hg e (pathClass (markedPolygonLoop e d)) =
        c * Inv.inv (α := LiZhongQC.surfaceGroup g) (PresentedGroup.of (edgeLabelEquiv g d)) * c⁻¹ := by
  have hmap (d : Edge g) :
      TauCeti.FundamentalGroup.homeomorphMulEquiv e.symm (boundaryBase g).val
        (polygonBoundaryClass g (pathClass (sideLoop (HandleCW.edgeSide d)))) =
      pathClass (markedPolygonLoop e d) := by
    rw [TauCeti.FundamentalGroup.homeomorphMulEquiv_apply,
      TauCeti.FundamentalGroup.mapOfEq_rfl, polygonBoundaryClass_eq_map]
    exact TauCeti.FundamentalGroup.map_fromPath
      (⟨e.symm, e.symm.continuous⟩ : C(PolygonQuotient g, X))
      (boundaryBase g).val (positivePolygonLoop d)
  obtain ⟨c, hc⟩ := polygonBoundary_sideLoop_images_up_to_common_conjugation g hg
  refine ⟨c, fun d => ?_⟩
  rw [← hmap d]
  exact (congrArg (polygonBoundaryFundamentalGroupMulEquivSurfaceGroup g hg)
    ((TauCeti.FundamentalGroup.homeomorphMulEquiv e.symm (boundaryBase g).val).symm_apply_apply
      (polygonBoundaryClass g (pathClass (sideLoop (HandleCW.edgeSide d)))))).trans (hc d)

/-- The actual positive side loops of the given original marking give the inverse
standard letters up to one common conjugation in the original surface group. -/
theorem markedPolygonLoop_images_up_to_common_conjugation
    (hg : 0 < g) (e : X ≃ₜ PolygonQuotient g) :
    ∃ c : LiZhongQC.surfaceGroup g, ∀ d : Edge g,
      markedPolygonFundamentalEquiv hg e (pathClass (markedPolygonLoop e d)) =
        c * Inv.inv (α := LiZhongQC.surfaceGroup g) (PresentedGroup.of (edgeLabelEquiv g d)) * c⁻¹ := by
  exact markedPolygonLoop_image hg e

variable {R : RiemannSurface X}

/-- The original cover's true opposite-valued endpoint monodromy at the given lift base. -/
def HyperbolicSurfaceModel.markedPolygonCoverEquiv (M : HyperbolicSurfaceModel R)
    (e : X ≃ₜ PolygonQuotient g) (z₀ : ℍ)
    (hz₀ : M.halfPlaneCover z₀ = e.symm (boundaryBase g).val) :
    FundamentalGroup X (e.symm (boundaryBase g).val) ≃* (deck M.halfPlaneCover)ᵐᵒᵖ :=
  (covering_deck_isQuotientCoveringMap M.halfPlaneCover_covering
    M.halfPlaneCover_surjective).fundamentalGroupEquiv ⟨z₀, hz₀⟩

/-- The actual endpoint deck transformation of this given marking's side path. -/
def HyperbolicSurfaceModel.markedPolygonEndpointDeck (M : HyperbolicSurfaceModel R)
    (e : X ≃ₜ PolygonQuotient g) (z₀ : ℍ)
    (hz₀ : M.halfPlaneCover z₀ = e.symm (boundaryBase g).val) (d : Edge g) :
    deck M.halfPlaneCover :=
  (M.markedPolygonCoverEquiv e z₀ hz₀ (pathClass (markedPolygonLoop e d))).unop

/-- The actual liftPath through the same original covering. -/
def HyperbolicSurfaceModel.markedPolygonLoopLift (M : HyperbolicSurfaceModel R)
    (e : X ≃ₜ PolygonQuotient g) (z₀ : ℍ)
    (hz₀ : M.halfPlaneCover z₀ = e.symm (boundaryBase g).val) (d : Edge g) :
    C(unitInterval, ℍ) :=
  M.halfPlaneCover_covering.liftPath (markedPolygonLoop e d) z₀
    ((markedPolygonLoop e d).source.trans hz₀.symm)

/-- The exact covering endpoint formula, including both lift conditions. -/
theorem HyperbolicSurfaceModel.markedPolygonLoopLift_spec (M : HyperbolicSurfaceModel R)
    (e : X ≃ₜ PolygonQuotient g) (z₀ : ℍ)
    (hz₀ : M.halfPlaneCover z₀ = e.symm (boundaryBase g).val) (d : Edge g) :
    M.halfPlaneCover ∘ M.markedPolygonLoopLift e z₀ hz₀ d = markedPolygonLoop e d ∧
      M.markedPolygonLoopLift e z₀ hz₀ d 0 = z₀ ∧
      M.markedPolygonLoopLift e z₀ hz₀ d 1 = M.markedPolygonEndpointDeck e z₀ hz₀ d • z₀ := by
  refine ⟨M.halfPlaneCover_covering.liftPath_lifts _ _ _,
    M.halfPlaneCover_covering.liftPath_zero _ _ _, ?_⟩
  let q := covering_deck_isQuotientCoveringMap M.halfPlaneCover_covering
    M.halfPlaneCover_surjective
  exact (q.unop_fundamentalGroupToMulOpposite_smul
    (e := ⟨z₀, hz₀⟩) (γ := pathClass (markedPolygonLoop e d))).symm

/-- Any given geometric polygon marking yields one actual deck-group marking.
The inverse letters and opposite monodromy cancel through one common conjugation. -/
theorem HyperbolicSurfaceModel.exists_markedPolygonDeckEquiv (M : HyperbolicSurfaceModel R)
    (hg : 0 < g) (e : X ≃ₜ PolygonQuotient g) (z₀ : ℍ)
    (hz₀ : M.halfPlaneCover z₀ = e.symm (boundaryBase g).val) :
    ∃ ρ : LiZhongQC.surfaceGroup g ≃* deck M.halfPlaneCover, ∀ d : Edge g,
      M.markedPolygonEndpointDeck e z₀ hz₀ d = ρ (PresentedGroup.of (edgeLabelEquiv g d)) := by
  let E := markedPolygonFundamentalEquiv hg e
  let C := M.markedPolygonCoverEquiv e z₀ hz₀
  let ρ : LiZhongQC.surfaceGroup g ≃* deck M.halfPlaneCover :=
    (E.symm.trans C).trans (MulEquiv.inv' (deck M.halfPlaneCover)).symm
  have hendpoint (γ : FundamentalGroup X (e.symm (boundaryBase g).val)) :
      (C γ).unop = (ρ (E γ))⁻¹ := by
    change (C γ).unop =
      ((MulEquiv.inv' (deck M.halfPlaneCover)).symm (C (E.symm (E γ))))⁻¹
    rw [E.symm_apply_apply]
    change (C γ).unop = ((C γ).unop⁻¹)⁻¹
    exact (inv_inv _).symm
  obtain ⟨c, hc⟩ := markedPolygonLoop_image hg e
  refine ⟨ρ.trans (MulAut.conj (ρ c)), fun d => ?_⟩
  change (C (pathClass (markedPolygonLoop e d))).unop = _
  rw [hendpoint, hc]
  change (ρ (c * Inv.inv (α := LiZhongQC.surfaceGroup g)
    (PresentedGroup.of (edgeLabelEquiv g d)) * c⁻¹))⁻¹ =
      ρ c * ρ (PresentedGroup.of (edgeLabelEquiv g d)) * (ρ c)⁻¹
  simp only [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc]
  let s : LiZhongQC.surfaceGroup g := PresentedGroup.of (edgeLabelEquiv g d)
  exact congrArg (fun b : deck M.halfPlaneCover => ρ c * (b * (ρ c)⁻¹))
    ((congrArg (fun b : deck M.halfPlaneCover => b⁻¹) (map_inv ρ s)).trans
      (inv_inv (ρ s)))

/-- The original covering supplies a lift base and one marking for every
actual side-loop lift of the given homeomorphism; none is an extra hypothesis. -/
theorem HyperbolicSurfaceModel.exists_markedPolygonLiftSystem (M : HyperbolicSurfaceModel R)
    (hg : 0 < g) (e : X ≃ₜ PolygonQuotient g) :
    ∃ z₀ : ℍ, ∃ hz₀ : M.halfPlaneCover z₀ = e.symm (boundaryBase g).val,
      ∃ ρ : LiZhongQC.surfaceGroup g ≃* deck M.halfPlaneCover, ∀ d : Edge g,
        M.halfPlaneCover ∘ M.markedPolygonLoopLift e z₀ hz₀ d = markedPolygonLoop e d ∧
          M.markedPolygonLoopLift e z₀ hz₀ d 0 = z₀ ∧
          M.markedPolygonLoopLift e z₀ hz₀ d 1 =
            ρ (PresentedGroup.of (edgeLabelEquiv g d)) • z₀ := by
  obtain ⟨z₀, hz₀⟩ := M.halfPlaneCover_surjective (e.symm (boundaryBase g).val)
  obtain ⟨ρ, hρ⟩ := M.exists_markedPolygonDeckEquiv hg e z₀ hz₀
  refine ⟨z₀, hz₀, ρ, fun d => ?_⟩
  have h := M.markedPolygonLoopLift_spec e z₀ hz₀ d
  rw [hρ d] at h
  exact h

/-- The complete coefficient nonvanishing for ANY actual given geometric
marking, retaining only the genuine final-b diagonal normalization condition. -/
theorem ClosedRiemannSurface.markedPolygon_matrices_bc_ne_zero
    (R : ClosedRiemannSurface X) (hg : 1 < g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (e : X ≃ₜ PolygonQuotient g) (z₀ : ℍ)
    (hz₀ : M.halfPlaneCover z₀ = e.symm (boundaryBase g).val)
    (A : Edge g → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : ∀ (d : Edge g) (z : ℍ), A d • z = M.markedPolygonEndpointDeck e z₀ hz₀ d • z)
    (hD01 : A (finalHandle hg, (1 : Fin 2)) 0 1 = 0)
    (hD10 : A (finalHandle hg, (1 : Fin 2)) 1 0 = 0)
    (d : Edge g) (hd : edgeLabelEquiv g d ≠ Sum.inr (finalHandle hg)) :
    A d 0 1 * A d 1 0 ≠ 0 := by
  let := R.compactSpace
  obtain ⟨ρ, hρ⟩ := M.exists_markedPolygonDeckEquiv (by omega) e z₀ hz₀
  let B : (Fin g ⊕ Fin g) → Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    fun s => A ((edgeLabelEquiv g).symm s)
  have hB (s : Fin g ⊕ Fin g) (z : ℍ) : B s • z = ρ (PresentedGroup.of s) • z := by
    simpa only [B, Equiv.apply_symm_apply] using
      (hA ((edgeLabelEquiv g).symm s) z).trans
        (congrArg (fun k : deck M.halfPlaneCover => k • z) (hρ ((edgeLabelEquiv g).symm s)))
  have hlabel : (edgeLabelEquiv g).symm (Sum.inr (finalHandle hg)) =
      (finalHandle hg, (1 : Fin 2)) := by
    apply (edgeLabelEquiv g).injective
    simp only [Equiv.apply_symm_apply, edgeLabelEquiv_b]
  obtain ⟨hb, hc⟩ := M.markedDeck_matrices_offDiagonal_ne_zero hg ρ B hB
    (by simpa only [B, hlabel] using hD01)
    (by simpa only [B, hlabel] using hD10) (edgeLabelEquiv g d) hd
  exact mul_ne_zero (by simpa only [B, Equiv.symm_apply_apply] using hb)
    (by simpa only [B, Equiv.symm_apply_apply] using hc)

end LowDimensionalTopology.Geometry.Surfaces
