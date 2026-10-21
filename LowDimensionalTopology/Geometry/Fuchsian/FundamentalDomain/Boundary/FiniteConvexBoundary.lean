/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.FiniteHull
public import LowDimensionalTopology.Geometry.Polygon.Convexity.FiniteHullSupports
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaKleinHull
public import LowDimensionalTopology.Geometry.Polygon.Support.CyclicDiscPolygonSupports
public import Mathlib.Analysis.Convex.Between
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Dynamics.PeriodicPts.Lemmas
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Complex.UnitDisc Topology UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance finiteConvexSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance finiteConvexSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩















/-- The literal compact Klein closure of the original true polygon has nonempty actual interior. -/
theorem compactKlein_interior_nonempty {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) :
    (interior (fuchsianPolygonCompactKlein P D)).Nonempty := by
  have ho:=P.kleinCoordinate_isOpenEmbedding.isOpenMap D hD.locallyFinite.fundamental.isOpen
  have hn:=((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  obtain ⟨x,hx⟩:=hn
  refine ⟨P.kleinCoordinate x,interior_mono subset_closure ?_⟩
  rw [ho.interior_eq]
  exact mem_image_of_mem _ hx

/-- Every original genuine finite-area convex fundamental polygon has an actual finite convex Jordan geodesic polygon with exactly the same literal native interior and compact Klein closure. Cyclic support data and Jordan geometry are constructed from its true extreme points. -/
theorem finite_area_polygon_actual_cyclic_model {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (harea : P.area D≠⊤) :
    ∃n : ℕ,∃S : _root_.LowDimensionalTopology.Geometry.Polygon.CyclicDiscPolygonSupportData n,
      S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P D ∧
      S.toDiscPolygon.interior=P.finiteCoordinate '' D := by
  classical
  let K:=fuchsianPolygonCompactKlein P D
  let hfinite:=finite_area_compactKlein_extreme_finite hD harea
  let V:=hfinite.toFinset
  have hV : (V:Set ℂ)=K.extremePoints ℝ:=hfinite.coe_toFinset
  have hKconv : Convex ℝ K:=hD.klein_convex.closure
  have hK : K=convexHull ℝ (V:Set ℂ):=by
    have he:=closure_convexHull_extremePoints (fuchsianPolygonCompactKlein_compact P D) hKconv
    rw [←hV,(V.finite_toSet.isClosed_convexHull ℝ).closure_eq] at he
    exact he.symm
  have hcard : 3≤V.card:=_root_.LowDimensionalTopology.Geometry.Euclidean.finite_planar_hull_card_ge_three V (hK ▸
    compactKlein_interior_nonempty hD)
  have hext (u : ℂ) (hu : u∈V) : u∈(convexHull ℝ (V:Set ℂ)).extremePoints ℝ:=by
    rw [←hK]
    exact (Set.Finite.mem_toFinset hfinite).mp hu
  have hdisc (u : ℂ) (hu : u∈V) : ‖u‖≤1:=by
    have huK : u∈K:=extremePoints_subset ((Set.Finite.mem_toFinset hfinite).mp hu)
    have hsub : K⊆Metric.closedBall (0:ℂ) 1:=by
      apply closure_minimal _ Metric.isClosed_closedBall
      rintro z ⟨x,hx,rfl⟩
      apply Metric.ball_subset_closedBall
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (P.finiteCoordinate
        x)∈Metric.ball (0:ℂ) 1
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.range_kleinCoordinate]
      exact mem_range_self _
    simpa only [Metric.mem_closedBall,dist_zero_right] using hsub huK
  obtain ⟨n,S,hvertices,hsupport⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.finite_extreme_cyclic_support_data V hcard hext hdisc
  have hregion : S.toCenteredData.kleinRegion=K:=by
    apply subset_antisymm
    · rw [_root_.LowDimensionalTopology.Geometry.Polygon.cyclic_support_region_eq_convexHull,hK]
      apply convexHull_mono
      rintro z ⟨i,rfl⟩
      exact hvertices i
    · rw [hK]
      apply convexHull_min _ S.toCenteredData.kleinRegion_convex
      intro u hu
      exact hsupport u hu
  have ho:=P.kleinCoordinate_isOpenEmbedding.isOpenMap D hD.locallyFinite.fundamental.isOpen
  have hn:=((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  have hnonempty : (interior (P.kleinCoordinate '' D)).Nonempty:=by
    rw [ho.interior_eq]
    exact hn.image P.kleinCoordinate
  have hKint : interior K=P.kleinCoordinate '' D:=
    (hD.klein_convex.interior_closure_eq_interior_of_nonempty_interior hnonempty).trans ho.interior_eq
  refine ⟨n,S,hregion,?_⟩
  change S.toCenteredData.toDiscPolygon.interior=P.finiteCoordinate '' D
  rw [S.toCenteredData.toDiscPolygon_interior]
  ext z
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate z∈S.toCenteredData.strictKleinRegion↔_
  rw [←S.toCenteredData.interior_kleinRegion,hregion,hKint]
  have he : P.kleinCoordinate '' D=_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' (P.finiteCoordinate '' D):=by
    rw [image_image]
    rfl
  rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate_injective.mem_set_image]

end LowDimensionalTopology.Geometry.Fuchsian
