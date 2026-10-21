/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.IdealVertexDistance
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletFanAngleBudget
@[expose] public section
noncomputable section
open Set Filter Topology MeasureTheory
open scoped Complex.UnitDisc OnePoint ENNReal BigOperators
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- Genuine hyperbolic convexity extends to the actual compactification,
 including ideal limit points, through the proved closed Klein coordinate. -/
theorem discClosedModelClosure_hConvex (S : Set Complex.UnitDisc) (hS :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscHConvex (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S) := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvex_iff_klein_convex _).mpr
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.closure_image_eq,Set.image_image]
  change Convex ℝ (closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' S))
  exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex S).mp hS).closure

/-- A genuine triangle with all three actual vertices in the compactified
 closure of a convex set has its entire finite carrier in the finite closure. -/
theorem closedTriangle_finiteCarrier_subset_closure (T :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle)
    (S : Set Complex.UnitDisc) (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex S)
    (ha : T.a∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S) (hb :
      T.b∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S)
    (hc : T.c∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S) : T.finiteCarrier⊆closure S := by
  have hT : T.closedCarrier⊆_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S:=by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscHConvexHull_min (discClosedModelClosure_hConvex S
      hS)
    intro p hp
    rcases hp with rfl|rfl|rfl
    · exact ha
    · exact hb
    · exact hc
  intro z hz
  have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S:=hT hz
  change z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure S at hm
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRelativeClosure_eq_preimage] at hm
  exact hm

/-- Every actual original polygon corner angle is bounded by the genuine
 full angle of its original cycle and hence by its point-stabilizer order. -/
theorem original_polygon_angle_le_order {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (v : P.domain.carrier) (hv : v∈closure D) :
    fuchsianPolygonAngle P D v≤2*Real.pi/(fuchsianPointOrder P v:ℝ) := by
  rw [←sum_cycle_angles_eq_two_pi_div_pointOrder hD v]
  apply Finset.single_le_sum
  · intro y _hy
    dsimp only [fuchsianPolygonAngle]
    positivity
  · exact (hD.locallyFinite.cycle_finite v).mem_toFinset.mpr ⟨hv,⟨1,one_smul _ _⟩⟩

/-- The actual two-ideal-vertex triangle angle bound follows from its
 original convex fundamental polygon and the true point stabilizer. -/
theorem original_ideal_triangle_angle_le_order {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (v : P.domain.carrier) (hv : v∈closure D)
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (ha :
      T.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate v))
    (hb : T.b∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))
    (hc : T.c∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D)) :
    T.alpha≤2*Real.pi/(fuchsianPointOrder P v:ℝ) := by
  have hfinite : P.finiteCoordinate v∈closure (P.finiteCoordinate '' D):=by
    rw [←P.finiteCoordinate.image_closure]
    exact Set.mem_image_of_mem _ hv
  have hva : T.a∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D):=by
    rw [ha]
    change P.finiteCoordinate v∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D)
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRelativeClosure_eq_preimage]
    exact hfinite
  have hS:=closedTriangle_finiteCarrier_subset_closure T (P.finiteCoordinate '' D) hD.convex hva hb hc
  rw [←P.finiteCoordinate.image_closure] at hS
  have hangle:=cycle_triangle_angle_le T (P.finiteCoordinate '' closure D) (P.finiteCoordinate v) ha hS
  exact hangle.trans (original_polygon_angle_le_order hD v hv)

/-- The first distance estimate from the original convex polygon and its
 actual elliptic stabilizer, with no angle budget supplied as a premise. -/
theorem original_ideal_triangle_cosh_pointDist_ge_csc_order {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (v : P.domain.carrier) (hv : v∈closure D)
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (ha :
      T.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate v))
    (hb : T.b∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))
    (hc : T.c∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))
    (hbIdeal : ‖(T.b:ℂ)‖=1) (hcIdeal : ‖(T.c:ℂ)‖=1)
    (hn : 2≤fuchsianPointOrder P v) :
    1/Real.sin (Real.pi/(fuchsianPointOrder P v:ℝ))≤
      Real.cosh (T.sideLineA.pointDist (P.finiteCoordinate v)) :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedTriangle_cosh_pointDist_ge_csc_order T (P.finiteCoordinate
    v) ha hbIdeal hcIdeal _ hn
    (original_ideal_triangle_angle_le_order hD v hv T ha hb hc)

/-- The corrected universal numerical estimate at an actual elliptic
 polygon corner requires true stabilizer order at least three. -/
theorem original_ideal_triangle_cosh_pointDist_ge_two_div_sqrt_three {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (v : P.domain.carrier) (hv : v∈closure D)
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) (ha :
      T.a=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate v))
    (hb : T.b∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))
    (hc : T.c∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))
    (hbIdeal : ‖(T.b:ℂ)‖=1) (hcIdeal : ‖(T.c:ℂ)‖=1)
    (hn : 3≤fuchsianPointOrder P v) :
    2/Real.sqrt 3≤Real.cosh (T.sideLineA.pointDist (P.finiteCoordinate v)) :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.csc_pi_div_nat_ge_two_div_sqrt_three _ hn).trans
    (original_ideal_triangle_cosh_pointDist_ge_csc_order hD v hv T ha hb hc hbIdeal hcIdeal (by omega))

end LowDimensionalTopology.Geometry.Fuchsian
