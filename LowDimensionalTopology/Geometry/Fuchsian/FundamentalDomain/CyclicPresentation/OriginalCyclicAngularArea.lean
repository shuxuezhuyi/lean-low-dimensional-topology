/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Germs
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicArea
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonConvexAngles
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonAngles
/-!
# Original polygon angles and the Euler area identity

Finite cyclic-polygon angles equal the original subtended angles; ideal angles
vanish. Substituting these angles into Gauss–Bonnet gives the Euler area
identity for the associated boundary-word realization.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem convexPolygon_angle_eq_subtended {n : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n) (hQ
  : Q.IsConvex)
    (i : Fin n) (z : 𝔻) (hz : Q.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z) :
    Q.angle i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle Q.finiteCarrier z := by
  have hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex Q.finiteCarrier := by
    rw [Q.finiteCarrier_eq_closure]
    exact hQ.closure
  have hzC : z∈Q.finiteCarrier := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z∈Q.closedCarrier
    rw [←hz]
    exact Q.boundary_subset_closedCarrier (mem_iUnion.mpr
      ⟨i,_root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_left_mem _ _⟩)
  by_cases hL : (Q.cornerRayPrev i z hz).supportLine=(Q.cornerRayNext i z hz).supportLine
  · rw [Q.angle_eq_pi_of_same_support i z hz hL]
    let R:=Q.cornerRayPrev i z hz
    let S:=Q.cornerRayNext i z hz
    let L:=R.supportLine
    have hp : Q.vertices ((finRotate n).symm i)∈L.closedCarrier := by
      have h:=_root_.LowDimensionalTopology.Geometry.Polygon.discRayTowardClosed_endpoint_mem z (Q.vertices ((finRotate
        n).symm i))
        (show _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z≠Q.vertices ((finRotate n).symm i) from by
          rw [←hz];exact fun he=>Q.prev_ne_self i (Q.vertices_injective he).symm)
      exact closure_mono (image_mono R.subset_support) h
    have hq : Q.vertices (finRotate n i)∈L.closedCarrier := by
      have h:=_root_.LowDimensionalTopology.Geometry.Polygon.discRayTowardClosed_endpoint_mem z (Q.vertices (finRotate n
        i))
        (show _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z≠Q.vertices (finRotate n i) from by
          rw [←hz];exact fun he=>Q.next_ne_self i (Q.vertices_injective he).symm)
      have hh : Q.vertices (finRotate n i)∈S.supportLine.closedCarrier:=
        closure_mono (image_mono S.subset_support) h
      change Q.vertices (finRotate n i)∈R.supportLine.closedCarrier
      rwa [hL]
    have hpq : Q.vertices ((finRotate n).symm i)≠Q.vertices (finRotate n i):=
      Q.vertices_injective.ne (_root_.LowDimensionalTopology.Geometry.Polygon.polygonSupport_prev_ne_next Q.three_le i)
    have hzB : z∈Q.finiteBoundary := (Q.finiteBoundary_mem_iff z).mpr (by
      rw [←hz]
      exact mem_iUnion.mpr ⟨i,_root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_left_mem _ _⟩)
    have hK:=Q.klein_boundary_straight_germ i z hz hL
    rw [hz,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion] at hK
    have hNative:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_kleinCoordinate.tendsto z).eventually hK
    have hB : ∀ᶠ w in 𝓝 z,w∈Q.finiteBoundary↔w∈L.carrier := by
      filter_upwards [hNative] with w hw
      exact (Q.klein_mem_boundary_iff w).symm.trans
        (hw.trans (L.mem_carrier_iff_complexLineEquation _ _ hpq hp hq w).symm)
    let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer z
    have hFz : F z=0:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_apply_self z
    obtain ⟨m,hm,hG⟩:=Q.normalized_interior_halfPlane_germ z hzB L
      (R.subset_support R.start_mem) hB
    have hClosed:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_closure_germ hG
    have hEq : F '' Q.finiteCarrier=closure (F '' Q.interior) := by
      rw [Q.finiteCarrier_eq_closure,F.image_closure]
    rw [←hEq] at hClosed
    let A : Set 𝔻:={w | 0 ≤ inner ℝ (w : ℂ) m}
    have hA : ∀ᶠ w in 𝓝 (0 : 𝔻),w∈F '' Q.finiteCarrier↔w∈A := by
      filter_upwards [hClosed] with w hw
      exact hw.trans (Set.ext_iff.mp (_root_.LowDimensionalTopology.Geometry.Polygon.closure_disc_open_halfPlane m hm)
        w)
    have h0Q : (0 : 𝔻)∈F '' Q.finiteCarrier:=⟨z,hzC,hFz⟩
    have h0A : (0 : 𝔻)∈A:=by simp [A]
    have hAngles:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle_eq_of_convex_germ
      (hC.isometry_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry z))
      (_root_.LowDimensionalTopology.Geometry.Polygon.discHConvex_closed_halfPlane m) h0Q h0A hA
    have hTransport:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle_isometry F (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry z) Q.finiteCarrier z
    rw [hFz] at hTransport
    exact ((hTransport.symm.trans hAngles).trans
      (_root_.LowDimensionalTopology.Geometry.Polygon.discSubtendedAngle_closed_halfPlane m hm)).symm
  · have hMinor:=Q.hasMinorInterior_of_isConvex_proper hQ i z hz hL
    have hTrue:=Q.meshTriangle_subtendedAngle_sum_of_convex_germ z hC hzC
      (Filter.Eventually.of_forall (fun _=>Iff.rfl))
    exact (Q.meshTriangle_subtendedAngle_sum_at_minor i z hz hL hMinor).symm.trans hTrue

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LeanEval.Topology.ClassificationOfSurfaces.Moise

theorem originalCyclicDiscPolygon_angle_eq_fuchsian {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hvertices : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hspec : ∀i,J.edgeSegment i=(e i).planeCarrier)
    (i : Fin J.n) (x : P.domain.carrier)
    (hx : (originalCyclicDiscPolygon hD ha J hvertices e hspec).vertices i=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x)) :
    (originalCyclicDiscPolygon hD ha J hvertices e hspec).angle i=fuchsianPolygonAngle P D x := by
  let Q:=originalCyclicDiscPolygon hD ha J hvertices e hspec
  have hQI : Q.interior=P.finiteCoordinate '' D:=originalCyclicDiscPolygon_interior hD ha J hvertices e hspec
  have hQ : Q.IsConvex := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex Q.interior
    rw [hQI]
    exact hD.convex
  have hCF : Q.finiteCarrier=P.finiteCoordinate '' closure D := by
    rw [Q.finiteCarrier_eq_closure,hQI,←P.finiteCoordinate.image_closure]
  calc
    Q.angle i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSubtendedAngle Q.finiteCarrier (P.finiteCoordinate
      x):=
      convexPolygon_angle_eq_subtended Q hQ i (P.finiteCoordinate x) hx
    _=fuchsianPolygonAngle P D x:=by rw [hCF];rfl

/-- Each literal angle is the original Haar-defined polygon angle at its actual finite point, or zero at an actual ideal vertex. -/
theorem originalCyclicDiscPolygon_angle_original {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) (J : PolygonalCircle)
    (hvertices : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e : ZMod J.n≃OriginalRefinedSide hD) (hspec : ∀i,J.edgeSegment i=(e i).planeCarrier)
    (i : Fin J.n) :
    (originalCyclicDiscPolygon hD ha J hvertices e hspec).angle i=
      if hi : ‖((originalCyclicDiscPolygon hD ha J hvertices e hspec).vertices i : ℂ)‖<1 then
        fuchsianPolygonAngle P D (P.finiteCoordinate.symm
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint ((originalCyclicDiscPolygon hD ha J
            hvertices e hspec).vertices i) hi))
      else 0 := by
  classical
  let Q:=originalCyclicDiscPolygon hD ha J hvertices e hspec
  by_cases hi : ‖(Q.vertices i : ℂ)‖<1
  · rw [dite_eq_left hi]
    apply originalCyclicDiscPolygon_angle_eq_fuchsian hD ha J hvertices e hspec i
    rw [P.finiteCoordinate.apply_symm_apply]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec _ hi).symm
  · rw [dite_eq_right hi]
    exact Q.angle_of_ideal i (le_antisymm (Q.vertices i).norm_le_one (le_of_not_gt hi))

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- Original finite-area data produce the genuine geometric Euler/area identity with the original Haar-defined angles; actual ideal vertices contribute zero. The genus here belongs to the proved faithful boundary-word realization. -/
theorem finite_area_original_angular_area_euler {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (ha : P.area D≠⊤) :
    ∃J : PolygonalCircle,∃e : ZMod J.n≃OriginalRefinedSide hD,
    ∃hvertices : ∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' originalRefinedEndpointSet hD,
    ∃hspec : ∀i,J.edgeSegment i=(e i).planeCarrier,
    ∃g : ℕ,_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus
      ((originalCyclicPresentation J e).presentation.PolygonalRealization
        (originalCyclicPresentation J e).valid) g ∧
      (P.area D).toReal=2*Real.pi*((Nat.card
        (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.Vertex (originalCyclicPresentation J
          e).presentation) : ℝ)-2+2*(g : ℝ))-
        ∑i : Fin J.n,
          if hi : ‖((originalCyclicDiscPolygon hD ha J hvertices e hspec).vertices i : ℂ)‖<1 then
            fuchsianPolygonAngle P D (P.finiteCoordinate.symm
              (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint ((originalCyclicDiscPolygon hD ha
                J hvertices e hspec).vertices i) hi))
          else 0 := by
  classical
  obtain ⟨J,e,hvertices,hspec,_hI,_hA,_hE,g,hg,hArea⟩:=
    finite_area_original_refined_area_euler hD ha
  refine ⟨J,e,hvertices,hspec,g,hg,?_⟩
  rw [hArea]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  exact originalCyclicDiscPolygon_angle_original hD ha J hvertices e hspec i

end LowDimensionalTopology.Geometry.Fuchsian
