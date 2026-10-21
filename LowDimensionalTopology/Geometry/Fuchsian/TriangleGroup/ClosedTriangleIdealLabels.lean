/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleIdealBoundary
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  Set
open scoped UpperHalfPlane Complex.UnitDisc

/-- The actual original vertex in the actual compact physical region. -/
def closedTrianglePhysicalVertex
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i:Fin 3) : closedTrianglePhysicalCompactRegion T :=
  ⟨(![T.toDiscTriangle.a,T.toDiscTriangle.b,T.toDiscTriangle.c] i:ℂ),by
    apply mem_image_of_mem
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.subset_closedDiscHConvexHull
    fin_cases i <;> simp⟩

theorem closedTrianglePhysicalVertex_injective (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    Function.Injective (closedTrianglePhysicalVertex T) := by
  intro i j h
  have hv: (closedTrianglePhysicalVertex T i).val=(closedTrianglePhysicalVertex T j).val:=
    congrArg (fun p:closedTrianglePhysicalCompactRegion T=>p.val) h
  have hD:![T.toDiscTriangle.a,T.toDiscTriangle.b,T.toDiscTriangle.c] i=
      ![T.toDiscTriangle.a,T.toDiscTriangle.b,T.toDiscTriangle.c] j:=
    Complex.UnitClosedDisc.coe_injective hv
  fin_cases i <;> fin_cases j <;> dsimp at hD
  all_goals first | rfl | exact (T.toDiscTriangle.a_ne_b hD).elim |
    exact (T.toDiscTriangle.a_ne_b hD.symm).elim | exact (T.toDiscTriangle.b_ne_c hD).elim |
    exact (T.toDiscTriangle.b_ne_c hD.symm).elim | exact (T.toDiscTriangle.c_ne_a hD).elim |
    exact (T.toDiscTriangle.c_ne_a hD.symm).elim

theorem closedTrianglePhysicalVertex_ideal_iff
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (i:Fin 3) :
    ‖(closedTrianglePhysicalVertex T i).val‖=1 ↔closedTriangleCornerAngle T i=0 := by
  fin_cases i
  · exact T.toDiscTriangle.alpha_eq_zero_iff_ideal.symm
  · exact T.toDiscTriangle.cycle.alpha_eq_zero_iff_ideal.symm
  · exact T.toDiscTriangle.cycle.cycle.alpha_eq_zero_iff_ideal.symm

theorem closedTrianglePhysicalIdeal_exists_vertex (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (p:{p:closedTrianglePhysicalCompactRegion T|‖p.val‖=1}) :
    ∃i:Fin 3,closedTrianglePhysicalVertex T i=p.val := by
  obtain ⟨q,hq,hqe⟩:=p.val.property
  have hN:‖(q:ℂ)‖=1:=by rw [hqe];exact p.property
  rcases closedDiscTriangle_ideal_point_is_vertex T.toDiscTriangle q hq hN with rfl|rfl|rfl
  · exact ⟨0,Subtype.ext hqe⟩
  · exact ⟨1,Subtype.ext hqe⟩
  · exact ⟨2,Subtype.ext hqe⟩

/-- Zero original angles label the genuine omitted geometric points bijectively, without a cusp-class assumption. -/
def closedTrianglePhysicalIdealLabelEquiv (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    {i:Fin 3|closedTriangleCornerAngle T i=0}≃{p:closedTrianglePhysicalCompactRegion T|‖p.val‖=1} :=
  Equiv.ofBijective (fun i=>⟨closedTrianglePhysicalVertex T i.val,
    (closedTrianglePhysicalVertex_ideal_iff T i.val).mpr i.property⟩) ⟨by
      intro i j he
      exact Subtype.ext (closedTrianglePhysicalVertex_injective T (congrArg Subtype.val he)),by
      intro p
      obtain ⟨i,hi⟩:=closedTrianglePhysicalIdeal_exists_vertex T p
      refine ⟨⟨i,(closedTrianglePhysicalVertex_ideal_iff T i).mp ?_⟩,Subtype.ext hi⟩
      rw [hi]
      exact p.property⟩

theorem closedTrianglePhysicalIdeal_card (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    Nat.card {p:closedTrianglePhysicalCompactRegion T|‖p.val‖=1}=
      Nat.card {i:Fin 3|closedTriangleCornerAngle T i=0} :=
  Nat.card_congr (closedTrianglePhysicalIdealLabelEquiv T).symm

end LowDimensionalTopology.Geometry.Fuchsian
