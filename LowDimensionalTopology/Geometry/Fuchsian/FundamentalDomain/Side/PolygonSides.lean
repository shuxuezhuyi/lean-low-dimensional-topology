module
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.PlaneSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.ConvexFundamentalPolygons
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Tactic
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.HalfPlanes
@[expose] public section
noncomputable section
open Set Topology
open scoped Pointwise OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine geodesic segment, allowing unbounded segments, in the original disc coordinate. -/
def IsFuchsianGeodesicSegment
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (S : Set P.domain.carrier) : Prop :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' S) ∧
    ∃ L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine, P.finiteCoordinate '' S ⊆ L.carrier

/-- A positive-length geodesic segment obtained from two literal closed tiles. -/
def IsFuchsianPolygonSide
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D S : Set P.domain.carrier) : Prop :=
  (∃ g : H, g ≠ 1 ∧ S = closure D ∩ fuchsianDomainTile P D g) ∧
    IsFuchsianGeodesicSegment P S ∧ S.Nontrivial

/-- A single-point triple intersection for three distinct original group elements. -/
def IsFuchsianPolygonVertex
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (x : P.domain.carrier) : Prop :=
  ∃ g h : H, g ≠ 1 ∧ h ≠ 1 ∧ g ≠ h ∧
    closure D ∩ fuchsianDomainTile P D g ∩ fuchsianDomainTile P D h = {x}

/-- An edge is a maximal genuine geodesic segment in the polygon boundary. -/
def IsFuchsianPolygonEdge
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D S : Set P.domain.carrier) : Prop :=
  IsFuchsianGeodesicSegment P S ∧ S.Nontrivial ∧ S ⊆ frontier D ∧
    ∀ T : Set P.domain.carrier, IsFuchsianGeodesicSegment P T → T ⊆ frontier D → S ⊆ T → T ⊆ S

/-- The actual possible singleton point attached to a pair of closed-tile witnesses. -/
def polygonTripleWitnessPoints
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (g h : H) : Set P.domain.carrier :=
  {x | closure D ∩ fuchsianDomainTile P D g ∩ fuchsianDomainTile P D h = {x}}

theorem polygonTripleWitnessPoints_finite
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (g h : H) : (polygonTripleWitnessPoints P D g h).Finite := by
  apply Set.Subsingleton.finite
  intro x hx y hy
  exact Set.singleton_injective (hx.symm.trans hy)

/-- The actual sides form a countable collection; no finite-sidedness assumption is imposed. -/
theorem fuchsianPolygonSides_countable
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) : {S | IsFuchsianPolygonSide P D S}.Countable := by
  let : Countable H := P.countable
  apply (Set.countable_range (fun g : H => closure D ∩ fuchsianDomainTile P D g)).mono
  rintro S ⟨⟨g, _hg, rfl⟩, _hs⟩
  exact mem_range_self g

/-- The actual vertex set is countable. -/
theorem fuchsianPolygonVertices_countable
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) : {x | IsFuchsianPolygonVertex P D x}.Countable := by
  let : Countable H := P.countable
  apply (Set.countable_iUnion (fun g : H => Set.countable_iUnion
    (fun h : H => (polygonTripleWitnessPoints_finite P D g h).countable))).mono
  rintro x ⟨g, h, _hg, _hh, _hgh, he⟩
  exact mem_iUnion₂.mpr ⟨g, h, he⟩

/-- Only finitely many distinct actual sides can meet a compact set. -/
theorem IsLocallyFiniteFuchsianDomain.compact_sides_finite
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (K : Set P.domain.carrier) (hK : IsCompact K) :
    {S | IsFuchsianPolygonSide P D S ∧ (S ∩ K).Nonempty}.Finite := by
  apply ((hD.compact_hits_finite K hK).image
    (fun g : H => closure D ∩ fuchsianDomainTile P D g)).subset
  rintro S ⟨⟨⟨g, _hg, rfl⟩, _hs⟩, x, hx, hxK⟩
  exact ⟨g, ⟨x, hx.2, hxK⟩, rfl⟩

/-- Only finitely many actual vertices can lie in a compact set. -/
theorem IsLocallyFiniteFuchsianDomain.compact_vertices_finite
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsLocallyFiniteFuchsianDomain P D) (K : Set P.domain.carrier) (hK : IsCompact K) :
    ({x | IsFuchsianPolygonVertex P D x} ∩ K).Finite := by
  let T : Set H := {g : H | (fuchsianDomainTile P D g ∩ K).Nonempty}
  have hT : T.Finite := hD.compact_hits_finite K hK
  have hf : (⋃ g ∈ T, ⋃ h ∈ T, polygonTripleWitnessPoints P D g h).Finite :=
    hT.biUnion (fun g _hg => hT.biUnion (fun h _hh => polygonTripleWitnessPoints_finite P D g h))
  apply hf.subset
  rintro x ⟨⟨g, h, _hg, _hh, _hgh, he⟩, hxK⟩
  have hx : x ∈ closure D ∩ fuchsianDomainTile P D g ∩ fuchsianDomainTile P D h := by
    rw [he]
    exact mem_singleton x
  exact mem_iUnion₂.mpr ⟨g, ⟨x, hx.1.2, hxK⟩, mem_iUnion₂.mpr ⟨h, ⟨x, hx.2, hxK⟩, he⟩⟩

/-- Every intersection of distinct actual closed tiles lies in the original domain frontier. -/
theorem IsFuchsianFundamentalDomain.closed_tile_intersection_subset_frontier
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) {g : H} (hg : g ≠ 1) :
    closure D ∩ fuchsianDomainTile P D g ⊆ frontier D := by
  have ho := ((isFuchsianFundamentalDomain_iff P D).mp hD).1
  rintro x ⟨hx, y, hy, hgy⟩
  change g • y = x at hgy
  have hn : x ∉ D := by
    intro hxD
    have he : g⁻¹ • x = y := by rw [← hgy, inv_smul_smul]
    exact Set.disjoint_left.mp (hD.disjoint_image_closure (inv_ne_one.mpr hg)) ⟨x, hxD, he⟩ hy
  simpa only [frontier, ho.interior_eq, mem_sdiff] using And.intro hx hn

/-- All genuine polygon sides lie in the genuine boundary. -/
theorem IsFuchsianPolygonSide.subset_frontier
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D S : Set P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) (hS : IsFuchsianPolygonSide P D S) : S ⊆ frontier D := by
  obtain ⟨⟨g, hg, rfl⟩, _hs⟩ := hS
  exact hD.closed_tile_intersection_subset_frontier hg

/-- All genuine polygon vertices lie in the genuine boundary. -/
theorem IsFuchsianPolygonVertex.mem_frontier
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} {x : P.domain.carrier}
    (hD : IsFuchsianFundamentalDomain P D) (hx : IsFuchsianPolygonVertex P D x) : x ∈ frontier D := by
  obtain ⟨g, h, hg, _hh, _hgh, he⟩ := hx
  have hx' : x ∈ closure D ∩ fuchsianDomainTile P D g ∩ fuchsianDomainTile P D h := by
    rw [he]
    exact mem_singleton x
  exact hD.closed_tile_intersection_subset_frontier hg hx'.1

/-- The genuine original action, transported to the native finite disc. -/
def UnitDiscFuchsianGroup.discAction {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) : Complex.UnitDisc ≃ₜ Complex.UnitDisc :=
  (P.finiteCoordinate.symm.trans (Homeomorph.smul g)).trans P.finiteCoordinate

/-- Every actual group element is a true isometry of the existing hyperbolic disc metric. -/
theorem UnitDiscFuchsianGroup.discAction_isometry
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) :
    let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric; Isometry (P.discAction g) := by
  let := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  obtain ⟨a, c, hdet, hform⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.complexMobius_disc_normal_form g.val (P.image_eq g)
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_isometry_iff_coefficient_formula _).mpr
  refine ⟨a, c, by simpa only [Complex.normSq_eq_norm_sq] using hdet, Or.inl ?_⟩
  intro z
  change (P.finiteCoordinate (g • P.finiteCoordinate.symm z) : ℂ) = _
  rw [P.finite_smul g a c hdet hform, P.finiteCoordinate.apply_symm_apply]
  rfl

/-- The coordinate action preserves exactly the original set image. -/
theorem UnitDiscFuchsianGroup.discAction_image
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (S : Set P.domain.carrier) :
    P.finiteCoordinate '' (g • S) = P.discAction g '' (P.finiteCoordinate '' S) := by
  change P.finiteCoordinate '' ((fun x => g • x) '' S) = _
  simp only [image_image]
  congr 1
  funext x
  simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.discAction, Homeomorph.trans_apply,
    P.finiteCoordinate.symm_apply_apply]
  rfl

/-- Every actual polygon translate is geodesically convex in the native disc coordinate. -/
theorem IsConvexFuchsianPolygon.smul_convex
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (g : H) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' (g • D)) := by
  rw [P.discAction_image]
  exact hD.convex.isometry_image (P.discAction_isometry g)

/-- Compatibility alias for the shared genuine planar separation theorem. -/
abbrev convex_open_disjoint_closures_hyperplane := @_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.convex_open_disjoint_closures_hyperplane

/-- The intersection of two actual closed polygon copies is geodesically convex. -/
theorem IsConvexFuchsianPolygon.closed_tile_intersection_convex
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (g : H) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' (closure D ∩ fuchsianDomainTile P D g)) := by
  have hg : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' (g • closure D)) := by
    rw [P.discAction_image]
    exact hD.closure_convex.isometry_image (P.discAction_isometry g)
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.finiteCoordinate '' (closure D ∩ g • closure D))
  rw [image_inter P.finiteCoordinate.injective]
  intro z hz w hw u hu
  exact ⟨hD.closure_convex z hz.1 w hw.1 hu, hg z hz.2 w hw.2 hu⟩

/-- A nondegenerate common closed-tile boundary is an actual native geodesic segment. -/
theorem IsConvexFuchsianPolygon.closed_tile_intersection_segment
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) {g : H} (hg : g ≠ 1)
    (hn : (closure D ∩ fuchsianDomainTile P D g).Nontrivial) :
    IsFuchsianGeodesicSegment P (closure D ∩ fuchsianDomainTile P D g) := by
  let U : Set ℂ := P.kleinCoordinate '' D
  let V : Set ℂ := P.kleinCoordinate '' (g • D)
  have hDo := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).1
  have hDn := ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
  have hVc : Convex ℝ V := by
    change Convex ℝ ((fun x => _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (P.finiteCoordinate x)) '' (g • D))
    rw [← image_image]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp (hD.smul_convex g)
  have hd : Disjoint U V := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
    have hxy := P.kleinCoordinate_isOpenEmbedding.injective (hxz.trans hyz.symm)
    exact Set.disjoint_left.mp (hD.locallyFinite.fundamental.disjoint_image hg) hy (hxy ▸ hx)
  obtain ⟨n, t, hnn, hline⟩ := convex_open_disjoint_closures_hyperplane hD.klein_convex
    (P.kleinCoordinate_isOpenEmbedding.isOpenMap D hDo) (hDn.image P.kleinCoordinate) hVc
    (P.kleinCoordinate_isOpenEmbedding.isOpenMap (g • D) ((Homeomorph.smul g).isOpenMap D hDo))
    ((hDn.image (fun x => g • x)).image P.kleinCoordinate) hd
  have hUl : P.kleinCoordinate '' closure D ⊆ closure U :=
    image_closure_subset_closure_image P.kleinCoordinate_isOpenEmbedding.continuous
  have hVl : P.kleinCoordinate '' (g • closure D) ⊆ closure V := by
    have he : g • closure D = closure (g • D) := (Homeomorph.smul g).image_closure D
    rw [he]
    exact image_closure_subset_closure_image P.kleinCoordinate_isOpenEmbedding.continuous
  have hA (x : P.domain.carrier) (hx : x ∈ closure D ∩ fuchsianDomainTile P D g) :
      inner ℝ n (P.kleinCoordinate x) = t :=
    hline _ ⟨hUl ⟨x, hx.1, rfl⟩, hVl ⟨x, hx.2, rfl⟩⟩
  obtain ⟨x, hx, y, hy, hxy⟩ := hn
  obtain ⟨L, ⟨hxL, hyL⟩, _huniq⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_discLine_through
    (P.finiteCoordinate x) (P.finiteCoordinate y) (P.finiteCoordinate.injective.ne hxy)
  obtain ⟨m, u, hm, hL⟩ := L.exists_klein_linear_equation
  refine ⟨hD.closed_tile_intersection_convex g, L, ?_⟩
  rintro z ⟨w, hw, rfl⟩
  apply (hL (P.finiteCoordinate w)).mpr
  exact (_root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_equations_iff_of_two_points (x := P.kleinCoordinate w) hnn hm
    (P.kleinCoordinate_isOpenEmbedding.injective.ne hxy) (hA x hx) (hA y hy)
    ((hL _).mp hxL) ((hL _).mp hyL)).mp (hA w hw)

/-- Every positive-length actual closed-tile intersection really is a side in the literal source sense. -/
theorem IsConvexFuchsianPolygon.side_of_nontrivial_intersection
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) {g : H} (hg : g ≠ 1)
    (hn : (closure D ∩ fuchsianDomainTile P D g).Nontrivial) :
    IsFuchsianPolygonSide P D (closure D ∩ fuchsianDomainTile P D g) :=
  ⟨⟨g, hg, rfl⟩, hD.closed_tile_intersection_segment hg hn, hn⟩

/-- Each actual finite-disc point lies on a genuine native geodesic line. -/
theorem exists_discLine_through_point
    (z : Complex.UnitDisc) : ∃ L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine, z ∈ L.carrier := by
  let L := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z).re
  exact ⟨L.toDiscLine, (L.mem_discCarrier z).mpr rfl⟩

/-- Every intersection of distinct closed polygon copies is a genuine geodesic segment,
including the possible empty and singleton cases. -/
theorem IsConvexFuchsianPolygon.closed_tile_intersection_geodesic
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) {g : H} (hg : g ≠ 1) :
    IsFuchsianGeodesicSegment P (closure D ∩ fuchsianDomainTile P D g) := by
  by_cases hn : (closure D ∩ fuchsianDomainTile P D g).Nontrivial
  · exact hD.closed_tile_intersection_segment hg hn
  have hs : (closure D ∩ fuchsianDomainTile P D g).Subsingleton := by
    intro x hx y hy
    by_contra hxy
    exact hn ⟨x, hx, y, hy, hxy⟩
  refine ⟨hD.closed_tile_intersection_convex g, ?_⟩
  rcases (closure D ∩ fuchsianDomainTile P D g).eq_empty_or_nonempty with he | ⟨x, hx⟩
  · refine ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).toDiscLine, ?_⟩
    simp only [he, image_empty, empty_subset]
  · obtain ⟨L, hL⟩ := exists_discLine_through_point (P.finiteCoordinate x)
    refine ⟨L, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    exact hs hy hx ▸ hL

/-- On a genuine convex fundamental polygon, the segment condition is a theorem, not an extra side hypothesis. -/
theorem IsConvexFuchsianPolygon.side_iff {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D S : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    IsFuchsianPolygonSide P D S ↔
      ∃ g : H, g ≠ 1 ∧ S = closure D ∩ fuchsianDomainTile P D g ∧ S.Nontrivial := by
  constructor
  · rintro ⟨⟨g, hg, he⟩, _hseg, hn⟩
    exact ⟨g, hg, he, hn⟩
  · rintro ⟨g, hg, rfl, hn⟩
    exact hD.side_of_nontrivial_intersection hg hn

end LowDimensionalTopology.Geometry.Fuchsian
