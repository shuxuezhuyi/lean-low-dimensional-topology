/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleBoundaryWord
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleRelatorAlgebra
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandlePuncturedRetraction
public import LowDimensionalTopology.External.TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped ContinuousMap
namespace LowDimensionalTopology.Geometry.Surfaces.HandlePresentation

private theorem boundaryFundamentalGroup_a (g : ℕ) (hg : 0 < g) (i : Fin g) :
    boundaryFundamentalGroupMulEquiv g hg (pathClass (sideLoop (i, (0 : Fin 4)))) =
      FreeGroup.of (i, (0 : Fin 2)) := by
  simpa [HandleCW.edgeSide] using boundaryFundamentalGroupMulEquiv_sideLoop g hg (i, 0)

private theorem boundaryFundamentalGroup_b (g : ℕ) (hg : 0 < g) (i : Fin g) :
    boundaryFundamentalGroupMulEquiv g hg (pathClass (sideLoop (i, (1 : Fin 4)))) =
      FreeGroup.of (i, (1 : Fin 2)) := by
  simpa [HandleCW.edgeSide] using boundaryFundamentalGroupMulEquiv_sideLoop g hg (i, 1)

/-- The actual once-around boundary loop has precisely the oriented free-group word. -/
theorem boundaryFundamentalGroup_inverse_boundary (g : ℕ) (hg : 0 < g) :
    boundaryFundamentalGroupMulEquiv g hg (pathClass (boundaryLoop g))⁻¹ =
      inverseBoundaryEdgeWord g := by
  rw [inverse_boundaryLoop_eq_commutator_product hg]
  unfold inverseBoundaryEdgeWord
  rw [map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  simp only [Function.comp_apply, map_mul, map_inv,
    boundaryFundamentalGroup_a, boundaryFundamentalGroup_b]

/-- The free word of the actual attaching loop is the inverse chronological commutator word. -/
theorem boundaryFundamentalGroup_boundary (g : ℕ) (hg : 0 < g) :
    boundaryFundamentalGroupMulEquiv g hg (pathClass (boundaryLoop g)) =
      (inverseBoundaryEdgeWord g)⁻¹ := by
  apply inv_injective
  rw [inv_inv, ← map_inv, boundaryFundamentalGroup_inverse_boundary]

/-- The boundary free basis in the exact a,b convention of the surface presentation. -/
def boundaryStandardFundamentalGroupMulEquiv (g : ℕ) (hg : 0 < g) :
    FundamentalGroup (Boundary g) (boundaryBase g) ≃* FreeGroup (StandardLabels g) :=
  (boundaryFundamentalGroupMulEquiv g hg).trans (edgeFreeGroupEquiv g)

/-- In the standard free basis, the actual attaching circle is the inverse standard relator. -/
@[simp] theorem boundaryStandardFundamentalGroup_boundary (g : ℕ) (hg : 0 < g) :
    boundaryStandardFundamentalGroupMulEquiv g hg (pathClass (boundaryLoop g)) =
      (standardRelator g)⁻¹ := by
  rw [boundaryStandardFundamentalGroupMulEquiv, MulEquiv.trans_apply,
    boundaryFundamentalGroup_boundary, edgeFreeGroupEquiv_boundaryEdgeWord]

/-- The quotient of the actual boundary fundamental group by its actual attaching circle
is the existing standard surface group. -/
def boundaryRelationQuotientEquivSurfaceGroup (g : ℕ) (hg : 0 < g) :
    (FundamentalGroup (Boundary g) (boundaryBase g) ⧸
      Subgroup.normalClosure ({pathClass (boundaryLoop g)} : Set _)) ≃*
        LiZhongQC.surfaceGroup g := by
  let E := boundaryFundamentalGroupMulEquiv g hg
  refine (QuotientGroup.congr
    (Subgroup.normalClosure ({pathClass (boundaryLoop g)} : Set _))
    (Subgroup.normalClosure ({(inverseBoundaryEdgeWord g)⁻¹} : Set _)) E ?_).trans
      (boundaryEdgePresentationEquivSurfaceGroup g)
  have hE : E (pathClass (boundaryLoop g)) = (inverseBoundaryEdgeWord g)⁻¹ :=
    boundaryFundamentalGroup_boundary g hg
  rw [Subgroup.map_normalClosure _ _ E.surjective, Set.image_singleton]
  exact congrArg (fun r : FreeGroup (Edge g) =>
    Subgroup.normalClosure ({r} : Set _)) hE

/-- Every bouquet point is joined to the actual wedge point. -/
private theorem bouquet_joined_base (g : ℕ) (w : BoundaryBouquet g) :
    Joined (TauCeti.WedgeSum.base _) w := by
  induction w using TauCeti.WedgeSum.ind with
  | base => exact Joined.refl _
  | incl d z =>
    have h := (PathConnectedSpace.joined (1 : Circle) z).map
      (f := TauCeti.WedgeSum.incl (fun _ : Edge g => (1 : Circle)) d)
      (TauCeti.WedgeSum.incl (fun _ : Edge g => (1 : Circle)) d).continuous
    simpa only [TauCeti.WedgeSum.incl_apply_self] using h

/-- The actual finite bouquet is path connected, including its distinguished wedge point. -/
theorem boundaryBouquetPathConnected (g : ℕ) : PathConnectedSpace (BoundaryBouquet g) where
  nonempty := ⟨TauCeti.WedgeSum.base _⟩
  joined x y := (bouquet_joined_base g x).symm.trans (bouquet_joined_base g y)

/-- Path connectedness of the actual quotient boundary follows from its proved homeomorphism. -/
theorem boundaryPathConnected (g : ℕ) (hg : 0 < g) : PathConnectedSpace (Boundary g) := by
  let := boundaryBouquetPathConnected g
  exact (bouquetHomeomorphBoundary g hg).pathConnectedSpace

/-- The actual punctured quotient is path connected by its actual radial deformation. -/
theorem puncturedPathConnected (g : ℕ) (hg : 0 < g) : PathConnectedSpace (Punctured g) := by
  let := boundaryPathConnected g hg
  exact (HandlePunctured.homotopyEquivBoundary g).symm.pathConnectedSpace

/-- A homotopy equivalence induces a bijection by its actual forward map, also after
transporting the target basepoint along an explicit equality. -/
theorem homotopyEquiv_mapOfEq_bijective {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₕ Y) (x : X) (y : Y) (h : e.toFun x = y) :
    Function.Bijective (FundamentalGroup.mapOfEq e.toFun h) := by
  subst y
  rw [TauCeti.FundamentalGroup.mapOfEq_rfl]
  exact e.fundamentalGroup_map_bijective x

/-- The actual radial retraction identifies fundamental groups at the specified boundary base.
Its forward function is exactly the map induced by the retraction. -/
def puncturedFundamentalGroupMulEquivBoundary (g : ℕ) (x : Punctured g)
    (hx : HandlePunctured.retraction g x = boundaryBase g) :
    FundamentalGroup (Punctured g) x ≃* FundamentalGroup (Boundary g) (boundaryBase g) :=
  MulEquiv.ofBijective (FundamentalGroup.mapOfEq (HandlePunctured.retractionMap g) hx)
    (homotopyEquiv_mapOfEq_bijective (HandlePunctured.homotopyEquivBoundary g) x
      (boundaryBase g) hx)

@[simp] theorem puncturedFundamentalGroupMulEquivBoundary_apply (g : ℕ) (x : Punctured g)
    (hx : HandlePunctured.retraction g x = boundaryBase g)
    (γ : FundamentalGroup (Punctured g) x) :
    puncturedFundamentalGroupMulEquivBoundary g x hx γ =
      FundamentalGroup.mapOfEq (HandlePunctured.retractionMap g) hx γ := rfl

end LowDimensionalTopology.Geometry.Surfaces.HandlePresentation
