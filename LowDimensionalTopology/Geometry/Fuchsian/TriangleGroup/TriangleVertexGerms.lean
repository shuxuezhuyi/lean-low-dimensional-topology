/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Germs
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleVertexClasses
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.FiniteAngleNormalization
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane
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

def triangleVertexFirstSide (i : Fin 3) : Fin 3:=![2,2,1] i

def triangleVertexSecondSide (i : Fin 3) : Fin 3:=![1,0,0] i

theorem triangleVertex_incident_sides (i j : Fin 3) :
    j≠i ↔ j=triangleVertexFirstSide i ∨ j=triangleVertexSecondSide i := by
  fin_cases i <;> fin_cases j <;> decide

def triangleVertexFirstRay
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (i : Fin 3) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt (triangleOppositeVertex T i) := by
  refine Fin.cases (motive:=fun i : Fin 3=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt (triangleOppositeVertex T i)) T.rayAB (fun j=>?_) i
  refine Fin.cases (motive:=fun j : Fin 2=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt (triangleOppositeVertex T j.succ)) T.rayBA (fun k=>?_) j
  exact Fin.cases T.rayCA (fun j => j.elim0) k

def triangleVertexSecondRay
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (i : Fin 3) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt (triangleOppositeVertex T i) := by
  refine Fin.cases (motive:=fun i : Fin 3=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt (triangleOppositeVertex T i)) T.rayAC (fun j=>?_) i
  refine Fin.cases (motive:=fun j : Fin 2=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt (triangleOppositeVertex T j.succ)) T.rayBC (fun k=>?_) j
  exact Fin.cases T.rayCB (fun j => j.elim0) k

theorem triangleVertexFirstRay_support (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (i : Fin 3) :
    (triangleVertexFirstRay T i).supportLine=finiteTrianglePoincareLine T (triangleVertexFirstSide i) := by
  fin_cases i
  · rfl
  · exact T.support_BA_eq
  · rfl

theorem triangleVertexSecondRay_support (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (i : Fin 3) :
    (triangleVertexSecondRay T i).supportLine=finiteTrianglePoincareLine T (triangleVertexSecondSide i) := by
  fin_cases i
  · exact T.support_AC_eq
  · rfl
  · exact T.support_CB_eq

def triangleVertexAngle
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (i : Fin 3) : ℝ:=![T.alpha,T.beta,T.gamma] i

theorem triangleVertex_rays_angle (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (i : Fin 3) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure (triangleVertexFirstRay T i) (triangleVertexSecondRay T i)=triangleVertexAngle T i := by
  fin_cases i <;> rfl

/-- Near each genuine finite vertex the original triangle has its actual two-ray angle interior. -/
theorem triangleVertex_local_open_germ (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (i : Fin 3) :
    ∃r : ℝ,0<r ∧ Metric.ball (triangleOppositeVertex T i) r∩T.interior=
      Metric.ball (triangleOppositeVertex T i) r∩
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior (triangleVertexFirstRay T i) (triangleVertexSecondRay T i) := by
  fin_cases i
  · exact T.locally_angleA
  · exact T.locally_angleB
  · exact T.locally_angleC

/-- Closing the actual local angle identifies the full original polygon carrier on a genuine ball. -/
theorem triangleVertex_local_closed_germ (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle) (i : Fin 3) :
    ∃r : ℝ,0<r ∧ ∀z∈Metric.ball (triangleOppositeVertex T i) r,
      z∈(finiteTrianglePoincarePolygon T).carrier ↔
        z∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior (triangleVertexFirstRay T i) (triangleVertexSecondRay T i)) := by
  obtain ⟨r,hr,he⟩:=triangleVertex_local_open_germ T i
  have hG : ∀ᶠz in 𝓝 (triangleOppositeVertex T i),z∈T.interior ↔
      z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior (triangleVertexFirstRay T i) (triangleVertexSecondRay T i):=by
    filter_upwards [Metric.ball_mem_nhds (triangleOppositeVertex T i) hr] with z hz
    constructor
    · intro h
      have hh : z∈Metric.ball (triangleOppositeVertex T i) r∩T.interior:=⟨hz,h⟩
      rw [he] at hh
      exact hh.2
    · intro h
      have hh : z∈Metric.ball (triangleOppositeVertex T i) r∩
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.properHAngleInterior (triangleVertexFirstRay T i) (triangleVertexSecondRay T i):=⟨hz,h⟩
      rw [←he] at hh
      exact hh.2
  obtain ⟨s,hs,hc⟩:=Metric.eventually_nhds_iff_ball.mp (_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_closure_germ hG)
  refine ⟨s,hs,?_⟩
  intro z hz
  rw [finiteTrianglePoincarePolygon_carrier]
  exact hc z hz

/-- A true neighbourhood of each vertex misses its actual opposite side. -/
theorem triangleVertex_misses_opposite_side
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HTriangle)
    (i : Fin 3) :
    ∃r : ℝ,0<r ∧ ∀z∈Metric.ball (triangleOppositeVertex T i) r,z∉finiteTrianglePoincareSide T i := by
  have ho : IsOpen {z : ℍ | 0<triangleBarycentric T z i}:=
    isOpen_lt continuous_const (triangleBarycentric_continuous T i)
  have hv : triangleOppositeVertex T i∈{z : ℍ | 0<triangleBarycentric T z i}:=by
    simp only [mem_ofPred_eq,triangleBarycentric_opposite,ite_true,zero_lt_one]
  obtain ⟨r,hr,hsub⟩:=Metric.isOpen_iff.mp ho _ hv
  refine ⟨r,hr,?_⟩
  intro z hz hside
  have hpos:=hsub hz
  have he:=(triangleBarycentric_side T i z).mp hside
  change 0<triangleBarycentric T z i at hpos
  rw [he.2] at hpos
  exact lt_irrefl _ hpos

end LowDimensionalTopology.Geometry.Fuchsian
