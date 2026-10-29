/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleBoundaryRelator
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandlePunctureBoundary
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.VanKampenDisc
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CanonicalHandleBasePoint
public import LowDimensionalTopology.Unproved.Surfaces.HandleGroupPresentation
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
namespace LowDimensionalTopology.Geometry.Surfaces.HandlePresentation

/-- The actual common basepoint, viewed in the original quotient surface. -/
def punctureCoverBase (g : ℕ) : PolygonQuotient g :=
  (HandlePunctureBoundary.overlapBase g).val

/-- The fundamental group of the actual polygon quotient is computed from its actual
puncture cover, actual circle generator, and literal oriented boundary word. -/
def polygonFundamentalGroupMulEquivSurfaceGroup (g : ℕ) (hg : 0 < g) :
    FundamentalGroup (PolygonQuotient g) (punctureCoverBase g) ≃*
      LiZhongQC.surfaceGroup g := by
  let A := punctured g
  let B := HandlePuncture.smallDisc g (1 / 2)
  let xAB := HandlePunctureBoundary.overlapBase g
  let x := xAB.val
  have hxA : x ∈ A := xAB.property.1
  have hxB : x ∈ B := xAB.property.2
  let a : A := ⟨x, hxA⟩
  let c := HandlePunctureBoundary.overlapGenerator g
  let i := FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left)
    (⟨x, mem_inter hxA hxB⟩ : ↥(A ∩ B))
  have hr : HandlePunctured.retraction g a = boundaryBase g :=
    HandlePunctureBoundary.boundaryFromOverlap_base g
  let E := puncturedFundamentalGroupMulEquivBoundary g a hr
  have hEc : E (i c) = pathClass (boundaryLoop g) := by
    change FundamentalGroup.mapOfEq (HandlePunctured.retractionMap g) hr
      (FundamentalGroup.map (HandlePunctureBoundary.overlapToPunctured g) xAB c) = _
    have hmap : FundamentalGroup.mapOfEq
        (HandlePunctureBoundary.overlapToPunctured g) (y := a)
        (rfl : HandlePunctureBoundary.overlapToPunctured g xAB = a) c =
          FundamentalGroup.map (HandlePunctureBoundary.overlapToPunctured g) xAB c :=
      DFunLike.congr_fun (TauCeti.FundamentalGroup.mapOfEq_rfl (x := xAB)
        (HandlePunctureBoundary.overlapToPunctured g)) c
    have hc := TauCeti.FundamentalGroup.mapOfEq_comp
      (x := xAB) (y := a) (z := boundaryBase g)
      (HandlePunctured.retractionMap g) (HandlePunctureBoundary.overlapToPunctured g)
      (rfl : HandlePunctureBoundary.overlapToPunctured g xAB = a) hr c
    exact ((congrArg (FundamentalGroup.mapOfEq
      (HandlePunctured.retractionMap g) hr) hmap).symm.trans hc).trans
        (HandlePunctureBoundary.overlapGenerator_boundary g)
  letI : PathConnectedSpace A := puncturedPathConnected g hg
  letI : ContractibleSpace B := HandlePuncture.contractible_smallDisc g
    (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  letI : PathConnectedSpace ↥(A ∩ B) := HandlePuncture.pathConnected_overlap g
    (r := (1 / 2 : ℝ)) (ρ := (1 / 4 : ℝ)) (by norm_num)
    (by constructor <;> norm_num)
  have hA : IsPathConnected A := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hB : IsPathConnected B := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hAB : IsPathConnected (A ∩ B) := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  have hcover : interior A ∪ interior B = univ := by
    rw [(punctured_open g).interior_eq,
      (HandlePuncture.isOpen_smallDisc g (r := (1 / 2 : ℝ)) (by norm_num)).interior_eq]
    exact HandlePuncture.punctured_union_smallDisc g (by norm_num)
  let Q := discCoverQuotientEquiv hxA hxB hcover hA hB hAB c
    (HandlePunctureBoundary.overlapGenerator_zpowers_eq_top g)
  have hN : (Subgroup.normalClosure ({i c} : Set (FundamentalGroup A a))).map E.toMonoidHom =
      Subgroup.normalClosure ({pathClass (boundaryLoop g)} :
        Set (FundamentalGroup (Boundary g) (boundaryBase g))) := by
    have himage : E.toMonoidHom '' ({i c} : Set (FundamentalGroup A a)) =
        {pathClass (boundaryLoop g)} :=
      (Set.image_singleton (f := E.toMonoidHom) (a := i c)).trans
        (congrArg (fun r : FundamentalGroup (Boundary g) (boundaryBase g) =>
          ({r} : Set _)) hEc)
    exact (Subgroup.map_normalClosure ({i c} : Set (FundamentalGroup A a))
      E.toMonoidHom E.surjective).trans (congrArg Subgroup.normalClosure himage)
  exact Q.symm.trans ((QuotientGroup.congr
    (Subgroup.normalClosure ({i c} : Set (FundamentalGroup A a)))
    (Subgroup.normalClosure ({pathClass (boundaryLoop g)} : Set _)) E hN).trans
      (boundaryRelationQuotientEquivSurfaceGroup g hg))

/-- The quotient presentation at its actual boundary vertex. The basepoint is transported
along a genuine path in the punctured quotient. -/
def polygonBoundaryFundamentalGroupMulEquivSurfaceGroup (g : ℕ) (hg : 0 < g) :
    FundamentalGroup (PolygonQuotient g) (boundaryBase g).val ≃*
      LiZhongQC.surfaceGroup g := by
  letI := puncturedPathConnected g hg
  let a := HandlePunctureBoundary.overlapToPunctured g
    (HandlePunctureBoundary.overlapBase g)
  let b := boundaryInclusion g (boundaryBase g)
  let p : Path (punctureCoverBase g) (boundaryBase g).val :=
    (PathConnectedSpace.somePath a b).map continuous_subtype_val
  exact (FundamentalGroup.fundamentalGroupMulEquivOfPath p).symm.trans
    (polygonFundamentalGroupMulEquivSurfaceGroup g hg)

end LowDimensionalTopology.Geometry.Surfaces.HandlePresentation

namespace LowDimensionalTopology.Geometry.Surfaces

/-- The arbitrary positive-genus canonical handle surface has its standard group presentation.
Both sides are the pre-existing mathematical objects; no substitute surface or group is used. -/
def canonicalHandleGroupMulEquivPositive (g : ℕ) (hg : 0 < g) :
    FundamentalGroup (CanonicalHandleSurface g) (canonicalHandleBasePoint g) ≃*
      LiZhongQC.surfaceGroup g := by
  cases g with
  | zero => omega
  | succ n =>
    change FundamentalGroup (HandlePresentation.PolygonQuotient (n + 1))
      (Quot.mk _ (handleBoundaryPoint ((0 : ℝ) / (4 * ((n + 1 : ℕ) : ℝ))))) ≃* _
    rw [zero_div]
    exact HandlePresentation.polygonBoundaryFundamentalGroupMulEquivSurfaceGroup (n + 1)
      (Nat.succ_pos n)

/-- The previously tracked presentation obligation is discharged for every positive genus. -/
theorem handleGroupPresentation_positive (g : ℕ) (hg : 0 < g) :
    LowDimensionalTopology.Unproved.HandleGroupPresentation g :=
  ⟨canonicalHandleGroupMulEquivPositive g hg⟩

end LowDimensionalTopology.Geometry.Surfaces
