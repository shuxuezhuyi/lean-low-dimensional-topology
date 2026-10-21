module
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Quotient.FiniteSideCompatibility
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- The outgoing vertex-side flag retains the side label at the given vertex. -/
def finitePolygonOutgoingFlag {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin m) : FinitePolygonVertexFlag Q hf :=
  ⟨(i,finitePolygonSideEquiv Q hf i),finitePolygonSide_left_mem Q hf i⟩

/-- Canonical flag cycles close, cover a vertex ball and have pairwise disjoint interior pieces. -/
def FinitePolygonCanonicalCycleConditions {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf)) : Prop :=
  ∀i : Fin m,∃n : ℕ,∃r : ℝ,0<r ∧
    ((finitePolygonCanonicalVertexStep Q hf S)^[n+1]) (1,finitePolygonOutgoingFlag Q hf i)=
      (1,finitePolygonOutgoingFlag Q hf i) ∧
    (⋃j : Fin (n+1),S.vertexCyclePiece
      (finitePolygonFlagStateCopy Q hf S (((finitePolygonCanonicalVertexStep Q hf S)^[j.val])
        (1,finitePolygonOutgoingFlag Q hf i))) r)=Metric.ball (finitePolygonVertex Q hf i) r ∧
    Pairwise (fun (j k : Fin (n+1))=>Disjoint
      (S.vertexCycleInteriorPiece (finitePolygonFlagStateCopy Q hf S
        (((finitePolygonCanonicalVertexStep Q hf S)^[j.val]) (1,finitePolygonOutgoingFlag Q hf i))) r)
      (S.vertexCycleInteriorPiece (finitePolygonFlagStateCopy Q hf S
        (((finitePolygonCanonicalVertexStep Q hf S)^[k.val]) (1,finitePolygonOutgoingFlag Q hf i))) r))

/--
Complete canonical cycles and relative-neighborhood side compatibility imply
finite fibers and local tessellation throughout the polygon.
-/
theorem finitePolygon_canonical_cycles_local_tessellation {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hOpp : ∀i : Fin m,∀x∈finitePolygonSide Q i,x∉range (finitePolygonVertex Q hf) →
      S.OppositeSideNeighborhoods (finitePolygonSideEquiv Q hf i) x)
    (hCycle : FinitePolygonCanonicalCycleConditions Q hf S) : S.FiniteFiberLocalTessellationCondition := by
  let P:=finiteDiscPoincarePolygon Q hf
  let : IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  have hReg:=finitePolygon_oppositeSideNeighborhoods_regularity Q hf S hOpp
  have hVertices (i : Fin m) :
      (S.project ⁻¹' {S.project (1,finitePolygonPoincareVertex Q hf i)}).Finite ∧
      ∃r₀ : ℝ,0<r₀ ∧ ∀r : ℝ,0<r → r ≤ r₀ →
        S.LocalTessellation (1,finitePolygonPoincareVertex Q hf i) r := by
    obtain ⟨n,r,hr,hclose,hcover,hdisj⟩:=hCycle i
    exact finitePolygonCanonicalVertexCycle_local_radius Q hf S (finitePolygonOutgoingFlag Q hf i)
      n r hr hclose hcover hdisj hReg
  have hx (x : P.Point) : (S.project ⁻¹' {S.project (1,x)}).Finite ∧
      ∃r₀ : ℝ,0<r₀ ∧ ∀r : ℝ,0<r → r ≤ r₀ → S.LocalTessellation (1,x) r := by
    by_cases hv : x.val∈range (finitePolygonVertex Q hf)
    · obtain ⟨i,hi⟩:=hv
      have he : x=finitePolygonPoincareVertex Q hf i:=Subtype.ext hi.symm
      rw [he]
      exact hVertices i
    · rcases hReg x hv with hxI | ⟨s,r,hs⟩
      · constructor
        · rw [S.project_fiber_eq_singleton_of_interior (1,x) hxI]
          exact finite_singleton _
        · exact S.interior_local_radius (finiteDiscPoincarePolygon_interior_isOpen Q hf) x hxI
      · exact ⟨hs.finite_class S,hs.local_radius S⟩
  exact ⟨fun x=>(hx x).1,fun x=>(hx x).2⟩

/-- Side compatibility and canonical vertex cycles imply discreteness and a fundamental domain.
Compactness supplies the uniform recentered chart condition. -/
theorem finitePolygon_canonical_cycles_poincare {m : ℕ} (Q : DiscPolygon m)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) (finiteDiscPoincarePolygon Q hf))
    (hOpp : ∀i : Fin m,∀x∈finitePolygonSide Q i,x∉range (finitePolygonVertex Q hf) →
      S.OppositeSideNeighborhoods (finitePolygonSideEquiv Q hf i) x)
    (hCycle : FinitePolygonCanonicalCycleConditions Q hf S) :
    DiscreteTopology (↥(Subgroup.closure (range S.element))) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' Q.interior) := by
  exact S.native_poincare_of_compact (finitePolygon_canonical_cycles_local_tessellation Q hf S hOpp hCycle)
    (finiteDiscPoincarePolygon_interior_isOpen Q hf) (finiteDiscPoincarePolygon_interior_isConnected Q hf)
    (finiteDiscPoincarePolygon_carrier Q hf) (finiteDiscPoincarePolygon_isCompact Q hf)
    (finiteDiscPoincarePolygon_countableSides Q hf) (finiteDiscPoincarePolygon_geodesicSides Q hf)

end LowDimensionalTopology.Geometry.Polygon
