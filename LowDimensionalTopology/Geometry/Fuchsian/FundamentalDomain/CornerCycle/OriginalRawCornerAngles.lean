/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalFiniteCornerCycles
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicAngularArea
/-!
# Angles of finite raw corner classes

The angles at the marked indices of a finite raw corner class sum to
`2 * pi / pointOrder`, by transport to the original polygon orbit cycle.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical

/-- The actual original Haar angles in a literal finite raw corner class add to the original cycle's actual reciprocal stabilizer angle. -/
theorem originalRawFiniteCornerClass_angle_sum
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤)
    (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier)
    (i : ZMod J.n) (x : P.domain.carrier)
    (hi : originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (P.finiteCoordinate x)) :
    ∑j : {j : ZMod J.n // Relation.EqvGen (originalRawCornerStep J e) i j},
      (originalCyclicDiscPolygon hD ha J hv e hs).angle ((originalCyclicFinIndex J).symm j.val)=
        2*Real.pi/(fuchsianPointOrder P x : ℝ) := by
  classical
  let Q:=originalCyclicDiscPolygon hD ha J hv e hs
  let E:=originalRawFiniteCornerClassEquiv hD ha J hc hv e hs i x hi
  let F:=(hD.locallyFinite.cycle_finite x).toFinset
  let ec : ↥(fuchsianPolygonCycle P D x)≃↥(F : Set P.domain.carrier):=
    Set.equivOfEq (hD.locallyFinite.cycle_finite x).coe_toFinset.symm
  let T:=E.trans ec
  have hAngles (j : {j : ZMod J.n // Relation.EqvGen (originalRawCornerStep J e) i j}) :
      Q.angle ((originalCyclicFinIndex J).symm j.val)=fuchsianPolygonAngle P D (T j).val := by
    change Q.angle ((originalCyclicFinIndex J).symm j.val)=fuchsianPolygonAngle P D (E j).val
    apply originalCyclicDiscPolygon_angle_eq_fuchsian hD ha J hv e hs
    change originalCyclicVertex hD J hv
      ((originalCyclicFinIndex J) ((originalCyclicFinIndex J).symm j.val))=_
    rw [Equiv.apply_symm_apply]
    exact originalRawFiniteCornerClassEquiv_spec hD ha J hc hv e hs i x hi j
  calc
    _=∑j,fuchsianPolygonAngle P D (T j).val:=by
      apply Finset.sum_congr rfl
      intro j _
      exact hAngles j
    _=∑y:↥(F : Set P.domain.carrier),fuchsianPolygonAngle P D y.val:=
      Equiv.sum_comp T (fun y:↥(F : Set P.domain.carrier)=>fuchsianPolygonAngle P D y.val)
    _=∑y∈F,fuchsianPolygonAngle P D y:=Finset.sum_coe_sort _ _
    _=2*Real.pi/(fuchsianPointOrder P x : ℝ):=sum_cycle_angles_eq_two_pi_div_pointOrder hD x

end LowDimensionalTopology.Geometry.Fuchsian
