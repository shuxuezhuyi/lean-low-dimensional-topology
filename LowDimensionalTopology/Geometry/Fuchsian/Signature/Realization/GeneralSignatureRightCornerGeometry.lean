/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.CofinitePolygonLowerSharpness
public import LowDimensionalTopology.Geometry.Polygon.Support.ConvexDiscPolygonSupports
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped Complex.UnitDisc UpperHalfPlane

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

/-- The two prescribed right corners of an actual tangential boundary triple
are distinct finite points on the cut line. Their adjacent native supports
are perpendicular, and the canonical genuine mirror exchanges the points.
Other vertices of the original polygon may be ideal. -/
theorem generalSignature_right_corner_geometry {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (i : Fin n)
    (hk : θ (finRotate n i) = Real.pi / 2)
    (hj : θ (finRotate n (finRotate n i)) = Real.pi / 2) :
    let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
    let k := finRotate n i
    let j := finRotate n k
    let M := triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j)
    ∃ u v : ℍ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc u) = Q.vertices k ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc v) = Q.vertices j ∧ u ≠ v ∧
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q k) u ∧
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q k).OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q j) v ∧
      M u = v ∧ M v = u ∧
      ∃ L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine, _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L = M ∧
        UpperHalfPlane.I ∈ L.carrier := by
  let Q := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
  let k := finRotate n i
  let j := finRotate n k
  let M := triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j)
  have hak : Q.angle k = Real.pi / 2 := by
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle]
    exact hk
  have haj : Q.angle j = Real.pi / 2 := by
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_angle]
    exact hj
  have hfk : ‖(Q.vertices k : ℂ)‖ < 1 :=
    Q.vertex_finite_of_angle_pos k (by rw [hak]; positivity)
  have hfj : ‖(Q.vertices j : ℂ)‖ < 1 :=
    Q.vertex_finite_of_angle_pos j (by rw [haj]; positivity)
  let a : 𝔻 := Complex.UnitDisc.mk (Q.vertices k : ℂ) hfk
  let b : 𝔻 := Complex.UnitDisc.mk (Q.vertices j : ℂ) hfj
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane a
  let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane b
  have ha : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel a = Q.vertices k := Subtype.ext rfl
  have hbb : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel b = Q.vertices j := Subtype.ext rfl
  have hu : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc u) = Q.vertices k := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
    exact ha
  have hv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc v) = Q.vertices j := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
    exact hbb
  have hC : Function.Injective (fun x : ℍ => _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective
  have huv : u ≠ v := by
    intro he
    have hV : Q.vertices k = Q.vertices j := hu.symm.trans ((congrArg
      (fun x : ℍ => _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)) he).trans hv)
    exact Q.next_ne_self k ((Q.vertices_injective hV).symm)
  have horthu : (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q k) u := by
    have h := Q.adjacent_sides_orthogonal_of_angle_right k a ha.symm hak
    have hH := ((Q.geodesicSide ((finRotate n).symm k)).orthogonalAt_iff_halfPlane
      (Q.geodesicSide k) a).mp h
    simpa only [_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine, u, k, Equiv.symm_apply_apply] using hH
  have horthv : (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q k).OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q j) v := by
    have h := Q.adjacent_sides_orthogonal_of_angle_right j b hbb.symm haj
    have hH := ((Q.geodesicSide ((finRotate n).symm j)).orthogonalAt_iff_halfPlane
      (Q.geodesicSide j) b).mp h
    simpa only [_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine, v, j, Equiv.symm_apply_apply] using hH
  have hswap : cofiniteClosedOrthogonal (cofiniteTangentMirror θ d i j)
      (Q.vertices k) = Q.vertices j :=
    cofiniteTangentMirror_vertex_right θ d hθ hd hb i j (hk.trans hj.symm)
  have hMu : M u = v := by
    apply hC
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
      (triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j) u)) =
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc v)
    rw [cofiniteTangentMirror_native_commutes, hu, hswap, hv]
  obtain ⟨L, hL, hLI, _⟩ := cofiniteTangentMirror_genuine_line θ d i j
  have hMv : M v = u := by
    rw [← hMu]
    change (triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j))
      ((triangleVertexOrthogonalIsometry (cofiniteTangentMirror θ d i j)) u) = u
    rw [← hL]
    exact L.reflection_involutive u
  exact ⟨u, v, hu, hv, huv, horthu, horthv, hMu, hMv, L, hL, hLI⟩

end LowDimensionalTopology.Geometry.Fuchsian
