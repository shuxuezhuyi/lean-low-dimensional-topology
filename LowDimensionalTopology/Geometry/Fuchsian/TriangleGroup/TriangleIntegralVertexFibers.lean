module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleVertexReflectionGroups
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleVertexClasses
public import Mathlib.Tactic
@[expose] public section
noncomputable section
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius
  Set
open scoped UpperHalfPlane

def finiteTriangleVertexAngle (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) : Fin 3 → ℝ :=
  ![_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure T.rayAB T.rayAC,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure T.rayBA T.rayBC,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure T.rayCA T.rayCB]

/-- Integral-submultiple genuine geometric vertex angles prove finiteness
of every entire original triangle vertex gluing class. -/
theorem finiteTriangle_integral_vertex_fiber_finite
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (n : Fin 3 → ℕ)
    (hn : ∀ i,2 ≤ n i) (hangle : ∀ i,finiteTriangleVertexAngle T i=Real.pi/(n i : ℝ))
    (i : Fin 3) :
    ((finiteTrianglePoincarePairing T).project ⁻¹'
      {(finiteTrianglePoincarePairing T).project (1,finiteTrianglePoincareVertex T i)}).Finite := by
  fin_cases i
  · let J := Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.rayAB.supportLine,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.rayAC.supportLine}
    have hJ : (J : Set (ℍ≃ᵢℍ)).Finite :=
      native_reflections_finite_of_angle T.rayAB T.rayAC (n 0) (hn 0) (hangle 0)
    let : Finite J := hJ.to_subtype
    apply finiteTriangle_vertex_fiber_finite T 0 J
    intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.rayAC.supportLine ∈ J :=
        Subgroup.subset_closure (by simp)
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineB ∈ J
      rw [←T.support_AC_eq]
      exact he
    · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.rayAB.supportLine ∈ J
      exact Subgroup.subset_closure (by simp)
  · let J := Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.rayBA.supportLine,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.rayBC.supportLine}
    have hJ : (J : Set (ℍ≃ᵢℍ)).Finite :=
      native_reflections_finite_of_angle T.rayBA T.rayBC (n 1) (hn 1) (hangle 1)
    let : Finite J := hJ.to_subtype
    apply finiteTriangle_vertex_fiber_finite T 1 J
    intro j hj
    fin_cases j
    · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.rayBC.supportLine ∈ J
      exact Subgroup.subset_closure (by simp)
    · exact (hj rfl).elim
    · have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.rayBA.supportLine ∈ J :=
        Subgroup.subset_closure (by simp)
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineC ∈ J
      rw [←T.support_BA_eq]
      exact he
  · let J := Subgroup.closure {_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.rayCA.supportLine,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.rayCB.supportLine}
    have hJ : (J : Set (ℍ≃ᵢℍ)).Finite :=
      native_reflections_finite_of_angle T.rayCA T.rayCB (n 2) (hn 2) (hangle 2)
    let : Finite J := hJ.to_subtype
    apply finiteTriangle_vertex_fiber_finite T 2 J
    intro j hj
    fin_cases j
    · have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.rayCB.supportLine ∈ J :=
        Subgroup.subset_closure (by simp)
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.sideLineA ∈ J
      rw [←T.support_CB_eq]
      exact he
    · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry T.rayCA.supportLine ∈ J
      exact Subgroup.subset_closure (by simp)
    · exact (hj rfl).elim

/-- The genuine integral-angle triangle has finite whole original gluing fibers
at every original polygon point, including all three actual vertices. -/
theorem finiteTriangle_integral_all_fibers_finite
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (n : Fin 3 → ℕ)
    (hn : ∀ i,2 ≤ n i) (hangle : ∀ i,finiteTriangleVertexAngle T i=Real.pi/(n i : ℝ)) :
    ∀ x : (finiteTrianglePoincarePolygon T).Point,
    ((finiteTrianglePoincarePairing T).project ⁻¹'
      {(finiteTrianglePoincarePairing T).project (1,x)}).Finite := by
  classical
  intro x
  by_cases hv : ∀ i : Fin 3,x.val ≠ triangleOppositeVertex T i
  · exact (finiteTriangle_nonvertex_local_condition T x hv).1
  · push Not at hv
    obtain ⟨i,hi⟩ := hv
    have hx : x=finiteTrianglePoincareVertex T i := Subtype.ext hi
    subst x
    exact finiteTriangle_integral_vertex_fiber_finite T n hn hangle i

end LowDimensionalTopology.Geometry.Fuchsian
