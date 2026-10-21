/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalRawCornerAngles
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicRawVertices
/-!
# Stabilizer weights of raw corner classes

Finite corners carry the reciprocal of their point stabilizer order; ideal
corners carry zero. These weights descend to raw corner classes and partition
the polygon angle sum, giving the area formula by Gauss–Bonnet.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Complex.UnitDisc

/- BEGIN OWN ORIGINAL CORNER AREA PARTITION -/
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical

/-- A marked corner contributes its actual reciprocal finite-point stabilizer order, or zero at infinity. -/
def originalRawCornerWeight {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) (J : PolygonalCircle)
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (i : ZMod J.n) : ℝ :=
  if hi : ‖(originalCyclicVertex hD J hv i : ℂ)‖<1 then
    1/(fuchsianPointOrder P (P.finiteCoordinate.symm
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint (originalCyclicVertex hD J hv i)
        hi)) : ℝ)
  else 0

theorem originalRawCornerWeight_finite {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (J : PolygonalCircle)
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (i : ZMod J.n) (x : P.domain.carrier)
    (hi : originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (P.finiteCoordinate x)) :
    originalRawCornerWeight hD J hv i=1/(fuchsianPointOrder P x : ℝ) := by
  have hn : ‖(originalCyclicVertex hD J hv i : ℂ)‖<1:=by
    rw [hi]
    exact (P.finiteCoordinate x).norm_lt_one
  rw [originalRawCornerWeight,dite_eq_left hn]
  congr 2
  apply congrArg (fuchsianPointOrder P)
  apply P.finiteCoordinate.injective
  rw [P.finiteCoordinate.apply_symm_apply]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ hn).trans hi

theorem originalRawCornerWeight_ideal {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (J : PolygonalCircle)
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (i : ZMod J.n) (hi : ‖(originalCyclicVertex hD J hv i : ℂ)‖=1) :
    originalRawCornerWeight hD J hv i=0 := by
  rw [originalRawCornerWeight,dite_eq_right (by rw [hi];exact lt_irrefl 1)]

theorem originalRawCorner_finite_iff_rawChain {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier)
    {i j : ZMod J.n} (hij : Relation.EqvGen (originalRawCornerStep J e) i j) :
    ‖(originalCyclicVertex hD J hv i : ℂ)‖<1 ↔ ‖(originalCyclicVertex hD J hv j : ℂ)‖<1 := by
  have hf (a b : ZMod J.n) (hab : Relation.EqvGen (originalRawCornerStep J e) a b)
      (ha' : ‖(originalCyclicVertex hD J hv a : ℂ)‖<1) :
      ‖(originalCyclicVertex hD J hv b : ℂ)‖<1:=by
    let x:=P.finiteCoordinate.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint
      (originalCyclicVertex hD J hv a) ha')
    have hx : originalCyclicVertex hD J hv a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x):=by
      rw [P.finiteCoordinate.apply_symm_apply]
      exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ ha').symm
    obtain ⟨y,hy⟩:=originalRawFiniteCornerClass_point_exists hD ha J hc hv e hs a x hx b hab
    rw [hy]
    exact (P.finiteCoordinate y.val).norm_lt_one
  exact ⟨hf i j hij,hf j i (Relation.EqvGen.symm _ _ hij)⟩

/-- Actual stabilizer conjugacy, rather than a choice of angle budget, makes the geometric weight constant on a raw class. -/
theorem originalRawCornerWeight_eq_of_rawChain {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier)
    {i j : ZMod J.n} (hij : Relation.EqvGen (originalRawCornerStep J e) i j) :
    originalRawCornerWeight hD J hv i=originalRawCornerWeight hD J hv j := by
  by_cases hn : ‖(originalCyclicVertex hD J hv i : ℂ)‖<1
  · let x:=P.finiteCoordinate.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint
    (originalCyclicVertex hD J hv i) hn)
    have hx : originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x):=by
      rw [P.finiteCoordinate.apply_symm_apply]
      exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ hn).symm
    obtain ⟨y,hy⟩:=originalRawFiniteCornerClass_point_exists hD ha J hc hv e hs i x hx j hij
    rw [originalRawCornerWeight_finite hD J hv i x hx,originalRawCornerWeight_finite hD J hv j y.val hy,
      fuchsianPointOrder_eq_of_mem_cycle P D x y.val y.property]
  · have hj : ¬‖(originalCyclicVertex hD J hv j : ℂ)‖<1:=fun hj=>
      hn ((originalRawCorner_finite_iff_rawChain hD ha J hc hv e hs hij).mpr hj)
    rw [originalRawCornerWeight,dite_eq_right hn,originalRawCornerWeight,dite_eq_right hj]

def originalRawCornerClassWeight {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier) :
    Quotient (originalRawCornerSetoid J e)→ℝ :=
  Quotient.lift (originalRawCornerWeight hD J hv)
    (fun _ _ h=>originalRawCornerWeight_eq_of_rawChain hD ha J hc hv e hs h)

theorem originalRawCornerClassWeight_mk {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier)
    (i : ZMod J.n) :
    originalRawCornerClassWeight hD ha J hc hv e hs (Quotient.mk _ i)=originalRawCornerWeight hD J hv i := rfl

/-- Every actual finite representative, independently of its index, gives the same genuine reciprocal order. -/
theorem originalRawCornerClassWeight_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier)
    (i : ZMod J.n) (x : P.domain.carrier)
    (hi : originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (P.finiteCoordinate x)) :
    originalRawCornerClassWeight hD ha J hc hv e hs (Quotient.mk _ i)=1/(fuchsianPointOrder P x : ℝ) :=
  originalRawCornerWeight_finite hD J hv i x hi

theorem originalRawCornerClassWeight_ideal {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier)
    (i : ZMod J.n) (hi : ‖(originalCyclicVertex hD J hv i : ℂ)‖=1) :
    originalRawCornerClassWeight hD ha J hc hv e hs (Quotient.mk _ i)=0 :=
  originalRawCornerWeight_ideal hD J hv i hi


/-- Every actual raw class, including ideal classes, has its derived geometric weighted angle sum. -/
theorem originalRawCornerClass_angle_sum {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier)
    (i : ZMod J.n) :
    ∑j : {j : ZMod J.n // Relation.EqvGen (originalRawCornerStep J e) i j},
      (originalCyclicDiscPolygon hD ha J hv e hs).angle ((originalCyclicFinIndex J).symm j.val)=
        2*Real.pi*originalRawCornerWeight hD J hv i := by
  let Q:=originalCyclicDiscPolygon hD ha J hv e hs
  by_cases hn : ‖(originalCyclicVertex hD J hv i : ℂ)‖<1
  · let x:=P.finiteCoordinate.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint
    (originalCyclicVertex hD J hv i) hn)
    have hx : originalCyclicVertex hD J hv i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x):=by
      rw [P.finiteCoordinate.apply_symm_apply]
      exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ hn).symm
    rw [originalRawFiniteCornerClass_angle_sum hD ha J hc hv e hs i x hx,
      originalRawCornerWeight_finite hD J hv i x hx]
    ring
  · have hzero : ∑j : {j : ZMod J.n // Relation.EqvGen (originalRawCornerStep J e) i j},
        Q.angle ((originalCyclicFinIndex J).symm j.val)=0:=by
      apply Finset.sum_eq_zero
      intro j _
      have hj : ¬‖(originalCyclicVertex hD J hv j.val : ℂ)‖<1:=fun h=>
        hn ((originalRawCorner_finite_iff_rawChain hD ha J hc hv e hs j.property).mpr h)
      apply Q.angle_of_ideal
      change ‖(originalCyclicVertex hD J hv
        ((originalCyclicFinIndex J) ((originalCyclicFinIndex J).symm j.val)) : ℂ)‖=1
      rw [Equiv.apply_symm_apply]
      exact le_antisymm (originalCyclicVertex hD J hv j.val).norm_le_one (le_of_not_gt hj)
    rw [hzero,originalRawCornerWeight,dite_eq_right hn,mul_zero]

/-- A literal quotient fiber has exactly the genuine class sum, independent of a representative choice. -/
theorem originalRawCornerClass_quotient_angle_sum {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier)
    (q : Quotient (originalRawCornerSetoid J e)) :
    ∑j : {j : ZMod J.n // Quotient.mk (originalRawCornerSetoid J e) j=q},
      (originalCyclicDiscPolygon hD ha J hv e hs).angle ((originalCyclicFinIndex J).symm j.val)=
        2*Real.pi*originalRawCornerClassWeight hD ha J hc hv e hs q := by
  refine Quotient.inductionOn q ?_
  intro i
  let T:=originalRawCornerSetoid J e
  let E : {j : ZMod J.n // Quotient.mk T j=Quotient.mk T i}≃
      {j : ZMod J.n // Relation.EqvGen (originalRawCornerStep J e) i j}:=
    Equiv.subtypeEquivRight (fun j=>⟨fun h=>Relation.EqvGen.symm _ _ (Quotient.exact h),
      fun h=>Quotient.sound (Relation.EqvGen.symm _ _ h)⟩)
  calc
    _=∑j : {j : ZMod J.n // Relation.EqvGen (originalRawCornerStep J e) i j},
        (originalCyclicDiscPolygon hD ha J hv e hs).angle ((originalCyclicFinIndex J).symm j.val):=
      Equiv.sum_comp E (fun j=>(originalCyclicDiscPolygon hD ha J hv e hs).angle
        ((originalCyclicFinIndex J).symm j.val))
    _=2*Real.pi*originalRawCornerWeight hD J hv i:=originalRawCornerClass_angle_sum hD ha J hc hv e hs i
    _=2*Real.pi*originalRawCornerClassWeight hD ha J hc hv e hs (Quotient.mk _ i):=rfl

/-- The actual full polygon angle sum is partitioned over its literal raw endpoint classes. -/
theorem originalRawCornerClasses_total_angle {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier) :
    ∑i : Fin J.n,(originalCyclicDiscPolygon hD ha J hv e hs).angle i=
      2*Real.pi*∑q : Quotient (originalRawCornerSetoid J e),originalRawCornerClassWeight hD ha J hc hv e hs q := by
  let Q:=originalCyclicDiscPolygon hD ha J hv e hs
  let T:=originalRawCornerSetoid J e
  calc
    _=∑j : ZMod J.n,Q.angle ((originalCyclicFinIndex J).symm j):=
      (Equiv.sum_comp (originalCyclicFinIndex J).symm Q.angle).symm
    _=∑q : Quotient T,∑j : {j : ZMod J.n // Quotient.mk T j=q},
        Q.angle ((originalCyclicFinIndex J).symm j.val):=
      (Fintype.sum_fiberwise (Quotient.mk T) (fun j=>Q.angle ((originalCyclicFinIndex J).symm j))).symm
    _=∑q : Quotient T,2*Real.pi*originalRawCornerClassWeight hD ha J hc hv e hs q:=by
      apply Finset.sum_congr rfl
      intro q _
      exact originalRawCornerClass_quotient_angle_sum hD ha J hc hv e hs q
    _=2*Real.pi*∑q : Quotient T,originalRawCornerClassWeight hD ha J hc hv e hs q:=
      (Finset.mul_sum _ _ _).symm

/-- The genuine original finite hyperbolic area is expressed using the actual raw-class stabilizer weights. -/
theorem originalRawCornerClasses_area {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hc : J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v : OriginalRefinedSide
      hD,v.carrier))
    (hv : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hs : ∀i,J.edgeSegment i=(e i).planeCarrier) :
    (P.area D).toReal=((J.n : ℝ)-2)*Real.pi-
      2*Real.pi*∑q : Quotient (originalRawCornerSetoid J e),originalRawCornerClassWeight hD ha J hc hv e hs q := by
  rw [originalCyclicDiscPolygon_gaussBonnet hD ha J hv e hs,
    originalRawCornerClasses_total_angle hD ha J hc hv e hs]

end LowDimensionalTopology.Geometry.Fuchsian
