module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeFundamentalDomains
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleEllipticClasses
public import LowDimensionalTopology.Geometry.Polygon.Area.PolygonMeshArea
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.IdealVertexDistance
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology MeasureTheory
open scoped UpperHalfPlane OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian.FiniteJordanOrderTwoHeckeCounterexample
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual ideal triangle with original upper-half-plane endpoints -1,1,infinity. -/
def sourceTriangle : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle :=
  _root_.LowDimensionalTopology.Geometry.Fuchsian.prescribedIdealHTriangle 0 0 (by norm_num) (by norm_num) (by simpa using Real.pi_pos)

/-- Its actual finite Jordan geodesic polygon in the genuine Cayley disc. -/
def sourcePolygon : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon 3 := sourceTriangle.toDiscTriangle.toDiscPolygon

theorem sourceTriangle_endpoints :
    sourceTriangle.a.val = ((-1 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧
    sourceTriangle.b.val = ((1 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧
    sourceTriangle.c.val = (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  constructor
  · change ((⟨-Real.cos 0,Real.sin 0⟩ : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = _
    norm_num
    apply Complex.ext <;> norm_num
  constructor
  · change ((⟨Real.cos 0,Real.sin 0⟩ : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = _
    norm_num
    rfl
  · rfl

/-- The literal lambda=2 Hecke fundamental domain is this finite geodesic triangle. -/
theorem sourceTriangle_interior :
    sourceTriangle.interior = _root_.LowDimensionalTopology.Geometry.Fuchsian.standardHeckeDomain ⊤ (by simp) := by
  ext z
  rw [sourceTriangle,_root_.LowDimensionalTopology.Geometry.Fuchsian.prescribedIdealHTriangle_mem_interior_iff]
  change (z.re ∈ Ioo (-Real.cos 0) (Real.cos 0) ∧ 1 < ‖(z:ℂ)‖^2) ↔
    (|z.re| < Real.cos (_root_.LowDimensionalTopology.Geometry.Fuchsian.triangleOrderAngle ⊤) ∧ 1 < ‖(z:ℂ)‖)
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.triangleOrderAngle_top,Real.cos_zero]
  rw [abs_lt]
  constructor
  · rintro ⟨hx,hn⟩
    exact ⟨hx,by nlinarith [norm_nonneg (z:ℂ)]⟩
  · rintro ⟨hx,hn⟩
    exact ⟨hx,by nlinarith⟩

theorem sourcePolygon_interior :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' sourceTriangle.interior = sourcePolygon.interior := by
  rw [sourcePolygon,_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle.toDiscPolygon_interior]
  exact sourceTriangle.cayley_interior

theorem sourceTriangle_fundamentalDomain :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (_root_.LowDimensionalTopology.Geometry.Fuchsian.standardHeckeGroup ⊤ (by simp)) ℍ volume sourceTriangle.interior := by
  rw [sourceTriangle_interior]
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.standardHeckeDomain_fundamentalDomain ⊤ (by simp)

theorem source_fixed_point_frontier : UpperHalfPlane.I ∈ frontier sourceTriangle.interior := by
  rw [frontier,sourceTriangle.interior_isOpen.interior_eq]
  constructor
  · rw [sourceTriangle,_root_.LowDimensionalTopology.Geometry.Fuchsian.prescribedIdealHTriangle_interior_closure]
    norm_num
  · rw [sourceTriangle,_root_.LowDimensionalTopology.Geometry.Fuchsian.prescribedIdealHTriangle_mem_interior_iff]
    norm_num

theorem source_joining_line : sourceTriangle.sideLineC = .circle 0 1 (by norm_num) :=
  _root_.LowDimensionalTopology.Geometry.Fuchsian.prescribedIdealHTriangle_circle _ _ _ _ _

theorem source_fixed_point_on_joining_line : UpperHalfPlane.I ∈ sourceTriangle.sideLineC.carrier := by
  rw [source_joining_line]
  norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier]

theorem source_distance_cosh_one : Real.cosh (sourceTriangle.sideLineC.pointDist UpperHalfPlane.I) = 1 := by
  have hdist : sourceTriangle.sideLineC.pointDist UpperHalfPlane.I = 0 :=
    Metric.infDist_zero_of_mem source_fixed_point_on_joining_line
  rw [hdist,Real.cosh_zero]

theorem source_uniform_bound_failure :
    Real.cosh (sourceTriangle.sideLineC.pointDist UpperHalfPlane.I) < 2 / Real.sqrt 3 := by
  rw [source_distance_cosh_one]
  simpa only [Nat.cast_ofNat,Real.sin_pi_div_two,div_one] using _root_.LowDimensionalTopology.Geometry.Hyperbolic.csc_pi_div_two_lt_two_div_sqrt_three

/-- The actual inversion lies in the original lambda=2 group, fixes i, and has exact order two. -/
theorem source_inversion :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry _root_.LowDimensionalTopology.Geometry.Fuchsian.modularInversionSL ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.standardHeckeGroup ⊤ (by simp) ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry _root_.LowDimensionalTopology.Geometry.Fuchsian.modularInversionSL UpperHalfPlane.I = UpperHalfPlane.I ∧
    orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry _root_.LowDimensionalTopology.Geometry.Fuchsian.modularInversionSL) = 2 := by
  refine ⟨?_,?_,_root_.LowDimensionalTopology.Geometry.Fuchsian.modularInversionSL_order_two⟩
  · rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.standardHeckeGroup_generators]
    exact Subgroup.subset_closure (by simp)
  · simpa only [_root_.LowDimensionalTopology.Geometry.Fuchsian.modularNativeHom_S_eq] using _root_.LowDimensionalTopology.Geometry.Fuchsian.modular_I_fixed_order_two.1

/-- The full original stabilizer has order two, not merely a selected element. -/
theorem source_full_stabilizer_order_two :
    Nat.card (MulAction.stabilizer (_root_.LowDimensionalTopology.Geometry.Fuchsian.standardHeckeGroup ⊤ (by simp)) UpperHalfPlane.I) = 2 := by
  let T := _root_.LowDimensionalTopology.Geometry.Fuchsian.standardHeckeTriangle ⊤ (by simp)
  have hα : T.alpha = Real.pi / 2 := (_root_.LowDimensionalTopology.Geometry.Fuchsian.standardHeckeTriangle_angles ⊤ (by simp)).1
  have hβ : T.beta = 0 :=
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.standardHeckeTriangle_angles ⊤ (by simp)).2.1.trans _root_.LowDimensionalTopology.Geometry.Fuchsian.triangleOrderAngle_top
  have hγ : T.gamma = 0 := (_root_.LowDimensionalTopology.Geometry.Fuchsian.standardHeckeTriangle_angles ⊤ (by simp)).2.2
  let i : {i : Fin 3 | 0 < _root_.LowDimensionalTopology.Geometry.Fuchsian.closedTriangleCornerAngle T i} :=
    ⟨0,by change 0 < T.alpha;rw [hα];positivity⟩
  let x := _root_.LowDimensionalTopology.Geometry.Fuchsian.closedTriangleFiniteVertexPoint T i
  have hxi : x.val = UpperHalfPlane.I := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_halfPlaneToClosedModel.injective
    rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.closedTriangleFiniteVertexPoint_vertex T i]
    apply Subtype.ext
    change ((⟨-Real.cos (Real.pi/2),Real.sin (Real.pi/2)⟩ : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = _
    change ((⟨-Real.cos (Real.pi/2),Real.sin (Real.pi/2)⟩ : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
      ((UpperHalfPlane.I : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    apply congrArg (fun z : ℂ => (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    apply Complex.ext <;> norm_num
  have hcard : Nat.card ↥(_root_.LowDimensionalTopology.Geometry.Fuchsian.triangleConformalGroup T ⊓
      MulAction.stabilizer (ℍ ≃ᵢ ℍ) UpperHalfPlane.I) = 2 := by
    rw [←hxi]
    apply _root_.LowDimensionalTopology.Geometry.Fuchsian.closedTriangle_vertex_conformal_stabilizer_card T
      (Or.inr ⟨2,by norm_num,hα⟩) (Or.inl hβ) (Or.inl hγ) x 0
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.closedTriangleFiniteVertexPoint_vertex T i) 2 (by norm_num)
    exact hα
  let E : MulAction.stabilizer (_root_.LowDimensionalTopology.Geometry.Fuchsian.standardHeckeGroup ⊤ (by simp)) UpperHalfPlane.I ≃
      ↥(_root_.LowDimensionalTopology.Geometry.Fuchsian.triangleConformalGroup T ⊓ MulAction.stabilizer (ℍ ≃ᵢ ℍ)
        UpperHalfPlane.I) := {
    toFun g := ⟨g.val.val,⟨g.val.property,MulAction.mem_stabilizer_iff.mp g.property⟩⟩
    invFun g := ⟨⟨g.val,g.property.1⟩,MulAction.mem_stabilizer_iff.mpr g.property.2⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  exact (Nat.card_congr E).trans hcard

/-- A counterexample in the actual finite Jordan geodesic class to the printed
unrestricted uniform constant, retaining the full original stabilizer order. -/
theorem actual_finite_jordan_order_two_counterexample :
    DiscreteTopology (_root_.LowDimensionalTopology.Geometry.Fuchsian.standardHeckeGroup ⊤ (by simp)) ∧
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (_root_.LowDimensionalTopology.Geometry.Fuchsian.standardHeckeGroup ⊤ (by simp)) ℍ volume sourceTriangle.interior ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' sourceTriangle.interior = sourcePolygon.interior ∧
    UpperHalfPlane.I ∈ frontier sourceTriangle.interior ∧
    Nat.card (MulAction.stabilizer (_root_.LowDimensionalTopology.Geometry.Fuchsian.standardHeckeGroup ⊤ (by simp)) UpperHalfPlane.I) = 2 ∧
    UpperHalfPlane.I ∈ sourceTriangle.sideLineC.carrier ∧
    Real.cosh (sourceTriangle.sideLineC.pointDist UpperHalfPlane.I) < 2 / Real.sqrt 3 :=
  ⟨_root_.LowDimensionalTopology.Geometry.Fuchsian.standardHeckeGroup_infinite_discrete,sourceTriangle_fundamentalDomain,sourcePolygon_interior,
    source_fixed_point_frontier,source_full_stabilizer_order_two,source_fixed_point_on_joining_line,
    source_uniform_bound_failure⟩

end LowDimensionalTopology.Geometry.Fuchsian.FiniteJordanOrderTwoHeckeCounterexample
