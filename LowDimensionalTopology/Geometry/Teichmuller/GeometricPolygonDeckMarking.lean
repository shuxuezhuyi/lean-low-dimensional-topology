module

public import LowDimensionalTopology.Geometry.Teichmuller.PolygonSideMarking
public import LowDimensionalTopology.External.TauCeti.AlgebraicTopology.FundamentalGroup.Homeomorph
public import LowDimensionalTopology.External.TauCeti.AlgebraicTopology.FundamentalGroup.Basic

/-!
# Geometric side loops on the original surface and its actual covering

A genuine handle-genus witness supplies the marking homeomorphism to the
positive polygon. Pulling its actual positive side paths back gives loops on
the original surface. Endpoint monodromy uses the original half-plane cover.
Its opposite-group convention cancels the inverse letters in the explicit
polygon presentation. One common conjugation therefore identifies all these
geometric endpoint deck maps with the generators of one multiplicative marking.

The matrix consequence retains the actual normalization condition that the
final b-generator is diagonal. Existence of that normalization and a complete
Fricke coordinate model are separate obligations.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Surfaces

open HandlePresentation
open LowDimensionalTopology.Geometry.Teichmuller

variable {X : Type*} [TopologicalSpace X]

/-- The genuine positive-genus handle surface is the same positive polygon quotient. -/
def positiveHandlePolygonHomeomorph (g : ℕ) (hg : 0 < g) :
    CanonicalHandleSurface g ≃ₜ PolygonQuotient g := by
  cases g with
  | zero => omega
  | succ n => exact Homeomorph.refl _

/-- The actual marking homeomorphism supplied by the original handle genus. -/
def ClosedRiemannSurface.geometricPolygonHomeomorph (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g) : X ≃ₜ PolygonQuotient g :=
  (Classical.choice hgenus).trans (positiveHandlePolygonHomeomorph g hg)

/-- The inverse image of the actual polygon vertex on the original surface. -/
def ClosedRiemannSurface.geometricPolygonBase (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g) : X :=
  (R.geometricPolygonHomeomorph hg hgenus).symm (boundaryBase g).val

/-- A positive geometric polygon side, regarded as a path in the full polygon. -/
def positivePolygonLoop {g : ℕ} (d : Edge g) :
    Path (boundaryBase g).val (boundaryBase g).val :=
  (sideLoop (HandleCW.edgeSide d)).map continuous_subtype_val

/-- The actual positive side loop pulled back to the given original surface. -/
def ClosedRiemannSurface.geometricPolygonLoop (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g) (d : Edge g) :
    Path (R.geometricPolygonBase hg hgenus) (R.geometricPolygonBase hg hgenus) :=
  (positivePolygonLoop d).map (R.geometricPolygonHomeomorph hg hgenus).symm.continuous

/-- The genuine homeomorphism transport followed by the computed polygon presentation. -/
def ClosedRiemannSurface.geometricPolygonFundamentalEquiv (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g) :
    FundamentalGroup X (R.geometricPolygonBase hg hgenus) ≃* LiZhongQC.surfaceGroup g :=
  (TauCeti.FundamentalGroup.homeomorphMulEquiv
    (R.geometricPolygonHomeomorph hg hgenus).symm (boundaryBase g).val).symm.trans
      (polygonBoundaryFundamentalGroupMulEquivSurfaceGroup g hg)

private theorem inverse_marking_map_side (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g) (d : Edge g) :
    TauCeti.FundamentalGroup.homeomorphMulEquiv
      (R.geometricPolygonHomeomorph hg hgenus).symm (boundaryBase g).val
        (polygonBoundaryClass g (pathClass (sideLoop (HandleCW.edgeSide d)))) =
      pathClass (R.geometricPolygonLoop hg hgenus d) := by
  rw [TauCeti.FundamentalGroup.homeomorphMulEquiv_apply,
    TauCeti.FundamentalGroup.mapOfEq_rfl, polygonBoundaryClass_eq_map]
  exact TauCeti.FundamentalGroup.map_fromPath
    (⟨(R.geometricPolygonHomeomorph hg hgenus).symm,
      (R.geometricPolygonHomeomorph hg hgenus).symm.continuous⟩ : C(PolygonQuotient g, X))
    (boundaryBase g).val (positivePolygonLoop d)

/-- All actual original-surface side loops have the computed inverse letters
under one common conjugation, with no supplied loop-label correspondence. -/
theorem ClosedRiemannSurface.geometricPolygonLoop_images_up_to_common_conjugation
    (R : ClosedRiemannSurface X) {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g) :
    ∃ c : LiZhongQC.surfaceGroup g, ∀ d : Edge g,
      R.geometricPolygonFundamentalEquiv hg hgenus
        (pathClass (R.geometricPolygonLoop hg hgenus d)) =
      c * Inv.inv (α := LiZhongQC.surfaceGroup g) (PresentedGroup.of (edgeLabelEquiv g d)) * c⁻¹ := by
  obtain ⟨c, hc⟩ := polygonBoundary_sideLoop_images_up_to_common_conjugation g hg
  refine ⟨c, fun d => ?_⟩
  rw [← inverse_marking_map_side R hg hgenus d]
  exact (congrArg (polygonBoundaryFundamentalGroupMulEquivSurfaceGroup g hg)
    ((TauCeti.FundamentalGroup.homeomorphMulEquiv
      (R.geometricPolygonHomeomorph hg hgenus).symm (boundaryBase g).val).symm_apply_apply
        (polygonBoundaryClass g (pathClass (sideLoop (HandleCW.edgeSide d)))))).trans (hc d)

/-- A genuine lift of the polygon vertex, obtained from the same original cover. -/
def ClosedRiemannSurface.geometricPolygonLiftBase (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) : ℍ :=
  Classical.choose (M.halfPlaneCover_surjective (R.geometricPolygonBase hg hgenus))

/-- The chosen point lies over the actual geometric base vertex. -/
theorem ClosedRiemannSurface.geometricPolygonLiftBase_proj (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) :
    M.halfPlaneCover (R.geometricPolygonLiftBase hg hgenus M) =
      R.geometricPolygonBase hg hgenus :=
  Classical.choose_spec (M.halfPlaneCover_surjective (R.geometricPolygonBase hg hgenus))

/-- Actual endpoint monodromy on the original geometric basepoint. -/
def ClosedRiemannSurface.geometricPolygonCoverEquiv (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) :
    FundamentalGroup X (R.geometricPolygonBase hg hgenus) ≃*
      (deck M.halfPlaneCover)ᵐᵒᵖ :=
  (covering_deck_isQuotientCoveringMap M.halfPlaneCover_covering
    M.halfPlaneCover_surjective).fundamentalGroupEquiv
      ⟨R.geometricPolygonLiftBase hg hgenus M,
        R.geometricPolygonLiftBase_proj hg hgenus M⟩

/-- The genuine endpoint deck map of the actual original-surface side path. -/
def ClosedRiemannSurface.geometricPolygonEndpointDeck (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (d : Edge g) : deck M.halfPlaneCover :=
  (R.geometricPolygonCoverEquiv hg hgenus M
    (pathClass (R.geometricPolygonLoop hg hgenus d))).unop

/-- The actual covering lift of the pulled-back geometric side loop. -/
def ClosedRiemannSurface.geometricPolygonLoopLift (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (d : Edge g) : C(unitInterval, ℍ) :=
  M.halfPlaneCover_covering.liftPath (R.geometricPolygonLoop hg hgenus d)
    (R.geometricPolygonLiftBase hg hgenus M)
    ((R.geometricPolygonLoop hg hgenus d).source.trans
      (R.geometricPolygonLiftBase_proj hg hgenus M).symm)

/-- This is a lift through the original covering, point by point. -/
theorem ClosedRiemannSurface.geometricPolygonLoopLift_lifts (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (d : Edge g) :
    M.halfPlaneCover ∘ R.geometricPolygonLoopLift hg hgenus M d =
      R.geometricPolygonLoop hg hgenus d :=
  M.halfPlaneCover_covering.liftPath_lifts _ _ _

/-- The true lift starts at the point chosen over the geometric vertex. -/
theorem ClosedRiemannSurface.geometricPolygonLoopLift_zero (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (d : Edge g) :
    R.geometricPolygonLoopLift hg hgenus M d 0 = R.geometricPolygonLiftBase hg hgenus M :=
  M.halfPlaneCover_covering.liftPath_zero _ _ _

/-- The geometric deck map is the endpoint of the actual lifted side loop;
the opposite-group convention has not been replaced by an assumed action. -/
theorem ClosedRiemannSurface.geometricPolygonLoopLift_one (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (d : Edge g) :
    R.geometricPolygonLoopLift hg hgenus M d 1 =
      R.geometricPolygonEndpointDeck hg hgenus M d •
        R.geometricPolygonLiftBase hg hgenus M := by
  let q := covering_deck_isQuotientCoveringMap M.halfPlaneCover_covering
    M.halfPlaneCover_surjective
  let z : M.halfPlaneCover ⁻¹' {R.geometricPolygonBase hg hgenus} :=
    ⟨R.geometricPolygonLiftBase hg hgenus M,
      R.geometricPolygonLiftBase_proj hg hgenus M⟩
  exact (q.unop_fundamentalGroupToMulOpposite_smul
    (e := z) (γ := pathClass (R.geometricPolygonLoop hg hgenus d))).symm

/-- The actual geometric endpoint generators form a multiplicative marking.
The one common conjugator is derived from the explicit polygon presentation. -/
theorem ClosedRiemannSurface.exists_geometricPolygonDeckEquiv
    (R : ClosedRiemannSurface X) {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) :
    ∃ ρ : LiZhongQC.surfaceGroup g ≃* deck M.halfPlaneCover, ∀ d : Edge g,
      R.geometricPolygonEndpointDeck hg hgenus M d =
        ρ (PresentedGroup.of (edgeLabelEquiv g d)) := by
  let E := R.geometricPolygonFundamentalEquiv hg hgenus
  let C := R.geometricPolygonCoverEquiv hg hgenus M
  let ρ : LiZhongQC.surfaceGroup g ≃* deck M.halfPlaneCover :=
    (E.symm.trans C).trans (MulEquiv.inv' (deck M.halfPlaneCover)).symm
  have hendpoint (γ : FundamentalGroup X (R.geometricPolygonBase hg hgenus)) :
      (C γ).unop = (ρ (E γ))⁻¹ := by
    change (C γ).unop =
      ((MulEquiv.inv' (deck M.halfPlaneCover)).symm (C (E.symm (E γ))))⁻¹
    rw [E.symm_apply_apply]
    change (C γ).unop = ((C γ).unop⁻¹)⁻¹
    exact (inv_inv _).symm
  obtain ⟨c, hc⟩ := R.geometricPolygonLoop_images_up_to_common_conjugation hg hgenus
  refine ⟨ρ.trans (MulAut.conj (ρ c)), fun d => ?_⟩
  change (C (pathClass (R.geometricPolygonLoop hg hgenus d))).unop = _
  rw [hendpoint, hc]
  change (ρ (c * Inv.inv (α := LiZhongQC.surfaceGroup g)
    (PresentedGroup.of (edgeLabelEquiv g d)) * c⁻¹))⁻¹ =
      ρ c * ρ (PresentedGroup.of (edgeLabelEquiv g d)) * (ρ c)⁻¹
  simp only [map_mul, map_inv, mul_inv_rev, inv_inv, mul_assoc]
  let s : LiZhongQC.surfaceGroup g := PresentedGroup.of (edgeLabelEquiv g d)
  exact congrArg (fun b : deck M.halfPlaneCover => ρ c * (b * (ρ c)⁻¹))
    ((congrArg (fun b : deck M.halfPlaneCover => b⁻¹) (map_inv ρ s)).trans
      (inv_inv (ρ s)))

/-- The proved marking of the actual geometric endpoint deck maps. -/
def ClosedRiemannSurface.geometricPolygonDeckEquiv (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) :
    LiZhongQC.surfaceGroup g ≃* deck M.halfPlaneCover :=
  Classical.choose (R.exists_geometricPolygonDeckEquiv hg hgenus M)

/-- One proved marking identifies every geometric side, rather than separately
conjugating individual generator matrices. -/
theorem ClosedRiemannSurface.geometricPolygonEndpointDeck_eq_generator
    (R : ClosedRiemannSurface X) {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (d : Edge g) :
    R.geometricPolygonEndpointDeck hg hgenus M d =
      R.geometricPolygonDeckEquiv hg hgenus M (PresentedGroup.of (edgeLabelEquiv g d)) :=
  Classical.choose_spec (R.exists_geometricPolygonDeckEquiv hg hgenus M) d

/-- Matrix representatives exist for all actual side-loop endpoint decks on
the same original uniformization. This asserts no homomorphic SL sign lift. -/
theorem ClosedRiemannSurface.exists_geometricPolygon_matrix_representatives
    (R : ClosedRiemannSurface X) {g : ℕ} (hg : 0 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) :
    ∃ A : Edge g → Matrix.SpecialLinearGroup (Fin 2) ℝ, ∀ (d : Edge g) (z : ℍ),
      A d • z = R.geometricPolygonEndpointDeck hg hgenus M d • z := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, _hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  have hrep (d : Edge g) : ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℍ, A • z = R.geometricPolygonEndpointDeck hg hgenus M d • z := by
    obtain ⟨A, _hA, he⟩ := exists_uniformization_matrix_representative hp
      (R.geometricPolygonEndpointDeck hg hgenus M d)
      (R.geometricPolygonLiftBase hg hgenus M)
    exact ⟨A, he⟩
  choose A hA using hrep
  exact ⟨A, hA⟩

/-- Every actual geometric generator except the final b-side has both
off-diagonal entries nonzero when that actual final generator is diagonal. -/
theorem ClosedRiemannSurface.geometricPolygon_matrices_offDiagonal_ne_zero
    (R : ClosedRiemannSurface X) {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (A : Edge g → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : ∀ (d : Edge g) (z : ℍ), A d • z = R.geometricPolygonEndpointDeck (by omega) hgenus M d • z)
    (hD01 : A (finalHandle hg, (1 : Fin 2)) 0 1 = 0)
    (hD10 : A (finalHandle hg, (1 : Fin 2)) 1 0 = 0)
    (d : Edge g) (hd : edgeLabelEquiv g d ≠ Sum.inr (finalHandle hg)) :
    A d 0 1 ≠ 0 ∧ A d 1 0 ≠ 0 := by
  let := R.compactSpace
  let hpos : 0 < g := by omega
  let B : (Fin g ⊕ Fin g) → Matrix.SpecialLinearGroup (Fin 2) ℝ :=
    fun s => A ((edgeLabelEquiv g).symm s)
  have hB (s : Fin g ⊕ Fin g) (z : ℍ) :
      B s • z = R.geometricPolygonDeckEquiv hpos hgenus M (PresentedGroup.of s) • z := by
    simpa only [B, Equiv.apply_symm_apply] using
      (hA ((edgeLabelEquiv g).symm s) z).trans
        (congrArg (fun k : deck M.halfPlaneCover => k • z)
          (R.geometricPolygonEndpointDeck_eq_generator hpos hgenus M
            ((edgeLabelEquiv g).symm s)))
  have hlabel : (edgeLabelEquiv g).symm (Sum.inr (finalHandle hg)) =
      (finalHandle hg, (1 : Fin 2)) := by
    apply (edgeLabelEquiv g).injective
    simp only [Equiv.apply_symm_apply, edgeLabelEquiv_b]
  have hb := M.markedDeck_matrices_offDiagonal_ne_zero hg
    (R.geometricPolygonDeckEquiv hpos hgenus M) B hB
    (by simpa only [B, hlabel] using hD01)
    (by simpa only [B, hlabel] using hD10) (edgeLabelEquiv g d) hd
  simpa only [B, Equiv.symm_apply_apply] using hb

/-- The full product nonvanishing belongs to the actual original-surface
geometric generator list and retains its sole final-b exception. -/
theorem ClosedRiemannSurface.geometricPolygon_matrices_bc_ne_zero
    (R : ClosedRiemannSurface X) {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (A : Edge g → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : ∀ (d : Edge g) (z : ℍ), A d • z = R.geometricPolygonEndpointDeck (by omega) hgenus M d • z)
    (hD01 : A (finalHandle hg, (1 : Fin 2)) 0 1 = 0)
    (hD10 : A (finalHandle hg, (1 : Fin 2)) 1 0 = 0)
    (d : Edge g) (hd : edgeLabelEquiv g d ≠ Sum.inr (finalHandle hg)) :
    A d 0 1 * A d 1 0 ≠ 0 := by
  obtain ⟨hb, hc⟩ := R.geometricPolygon_matrices_offDiagonal_ne_zero hg hgenus M A hA
    hD01 hD10 d hd
  exact mul_ne_zero hb hc

end LowDimensionalTopology.Geometry.Surfaces
