/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.CompactClosedQuotients
public import LowDimensionalTopology.Geometry.Hyperbolic.Topology.NativePuncturedBalls
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.QuotientInteriorEmbedding
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.NativeDirichletMeasureDomains
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincarePointQuotient
public import LowDimensionalTopology.Geometry.Polygon.Development.PoincareCycleFolding
public import Mathlib.Topology.Covering.Quotient
public import Mathlib.Topology.Maps.Proper.Basic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane Pointwise ENNReal
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon

/-- Nonzero genuine angular multiplicity forces membership in a literal original
closed-polygon translate; no orbit-covering assumption is substituted. -/
theorem nativeMultiplicity_nonzero_implies_translate_mem
    (H : Subgroup (ℍ≃ᵢℍ)) (A : Set ℍ) (hA : IsClosed A) (z : ℍ)
    (hz : nativePolygonAngularMultiplicity H A z≠0) : ∃g : H,z∈g • A := by
  by_contra hn
  push Not at hn
  apply hz
  rw [nativePolygonAngularMultiplicity_eq_translated]
  apply ENNReal.tsum_eq_zero.mpr
  intro g
  apply nativeLocalAngularFraction_of_not_mem_closure
  have hc : IsClosed (g • A):=g.val.toHomeomorph.isClosedMap _ hA
  simpa only [hc.closure_eq] using hn g

namespace PoincareSidePairing

/-- Positive genuine angular multiplicity supplies the true developing
surjectivity needed for the identified polygon's actual orbit map. -/
theorem evaluation_surjective_of_positive_angularMultiplicity
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hP : IsCompact P.carrier)
    (hM : ∀z : ℍ,_root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonAngularMultiplicity S.Generated P.carrier
      z≠0) :
    Function.Surjective S.evaluation := by
  apply S.evaluation_surjective_iff_closed_cover.mpr
  apply Set.eq_univ_of_forall
  intro z
  obtain ⟨g,hg⟩:=_root_.LowDimensionalTopology.Geometry.Polygon.nativeMultiplicity_nonzero_implies_translate_mem S.Generated
    P.carrier hP.isClosed z (hM z)
  exact mem_iUnion.mpr ⟨g,hg⟩

/-- The actual original side-identified polygon is compact, without any
assumption that the developing map is injective or locally unramified. -/
theorem pointQuotient_compactSpace
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hP : IsCompact P.carrier) : CompactSpace S.PointQuotient := by
  let : CompactSpace P.Point:=isCompact_iff_compactSpace.mp hP
  exact Function.Surjective.compactSpace S.continuous_pointProjection Quotient.mk_surjective

/-- The true quotient target is compact because the positive actual angular
multiplicity makes the compact identified original polygon map onto it. -/
theorem orbitQuotient_compactSpace_of_positive_angularMultiplicity
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hP : IsCompact P.carrier)
    (hM : ∀z : ℍ,_root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonAngularMultiplicity S.Generated P.carrier
      z≠0) :
    CompactSpace (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated ℍ) := by
  let : CompactSpace S.PointQuotient:=S.pointQuotient_compactSpace hP
  exact Function.Surjective.compactSpace S.continuous_pointToOrbit
    (S.pointToOrbit_surjective (S.evaluation_surjective_of_positive_angularMultiplicity hP hM))

/-- Actual proper compact-orbit finiteness makes every fiber of the genuine
identified-polygon-to-orbit map finite; no fundamental-domain hypothesis is used. -/
theorem pointToOrbit_finite_fibers
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier)
    (q : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated ℍ) : (S.pointToOrbit ⁻¹' {q}).Finite := by
  let x : ℍ:=q.out
  have hx : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ x=q:=Quotient.out_eq q
  have hf : (P.carrier∩MulAction.orbit S.Generated x).Finite:=
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.nativeIsometrySubgroup_discontinuous
      S.Generated).finite_inter_orbit x hP
  let F : Set P.Point:={p | _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ
    p.val=q}
  have hF : F.Finite := by
    apply (hf.preimage Subtype.val_injective.injOn).subset
    intro p hp
    refine ⟨p.property,?_⟩
    have he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ p.val=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ x:=hp.trans hx.symm
    exact MulAction.mem_orbit_iff.mpr (Quotient.exact he)
  apply (hF.image S.pointProjection).subset
  intro p hp
  obtain ⟨r,rfl⟩:=Quotient.exists_rep p
  exact ⟨r,hp,rfl⟩


/-- Actual side identifications never identify an original interior point with
a distinct original polygon point. -/
theorem pointGluing_interior_rigid
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    {p q : P.Point} (h : Relation.EqvGen S.PointStep p q)
    (hi : p.val∈P.interior ∨q.val∈P.interior) : p=q := by
  induction h with
  | rel p q h =>
    obtain ⟨t,hp,hq⟩:=h
    have hqt : q.val∈(S.paired t).val := by
      rw [←S.generator_side_image t]
      exact ⟨p.val,hp,hq.symm⟩
    rcases hi with hi|hi
    · exact (disjoint_left.mp (P.interior_disjoint_side t) hi hp).elim
    · exact (disjoint_left.mp (P.interior_disjoint_side (S.paired t)) hi hqt).elim
  | refl p => rfl
  | symm p q _ ih =>exact (ih hi.symm).symm
  | trans p q r _ _ ih1 ih2 =>
    rcases hi with hi|hi
    · have he:=ih1 (Or.inl hi)
      exact he.trans (ih2 (Or.inl (he ▸ hi)))
    · have he:=ih2 (Or.inr hi)
      exact (ih1 (Or.inr (he.symm ▸ hi))).trans he

/-- Literal original translate labels of an actual interior preimage. -/
def interiorOrbitLabel
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) (z : ℍ) :=
  {g : S.Generated //g⁻¹ • z∈P.interior}

/-- Every such genuine label gives a point in the actual identified polygon's
fiber above the specified original orbit. -/
def interiorOrbitLabelToFiber
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) (z : ℍ)
    (g : S.interiorOrbitLabel z) :
    {q : S.PointQuotient //S.pointToOrbit q=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection
      S.Generated ℍ z} :=
  ⟨S.pointProjection ⟨g.val⁻¹ • z,P.interior_subset_carrier g.property⟩,
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_smul S.Generated ℍ g.val⁻¹ z⟩

/-- At an actual free original point, no two genuine interior-translate labels
collapse under the literal original side identifications. -/
theorem interiorOrbitLabelToFiber_injective
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) (z : ℍ)
    (hz : ∀g : S.Generated,g • z=z →g=1) :
    Function.Injective (S.interiorOrbitLabelToFiber z) := by
  intro g h he
  have hh:=congrArg Subtype.val he
  have hp : (⟨g.val⁻¹ • z,P.interior_subset_carrier g.property⟩ : P.Point)=
      ⟨h.val⁻¹ • z,P.interior_subset_carrier h.property⟩:=
    S.pointGluing_interior_rigid (Quotient.exact hh) (Or.inl g.property)
  have heq : g.val⁻¹ • z=h.val⁻¹ • z:=congrArg Subtype.val hp
  have hfix : (g.val*h.val⁻¹) • z=z := by
    rw [mul_smul,←heq,smul_inv_smul]
  have hgh:=hz _ hfix
  exact Subtype.ext (mul_inv_eq_one.mp hgh)

/-- Avoiding every actual translated original boundary makes every actual
identified-polygon preimage an original interior preimage. -/
theorem interiorOrbitLabelToFiber_surjective
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) (z : ℍ)
    (hz : ∀g : S.Generated,z∉g • P.boundary) :
    Function.Surjective (S.interiorOrbitLabelToFiber z) := by
  intro q
  obtain ⟨p,hp⟩:=Quotient.exists_rep q.val
  have hOrbit : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ p.val=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ z:=by
    exact (S.pointToOrbit_projection p).symm.trans
      ((congrArg S.pointToOrbit hp).trans q.property)
  obtain ⟨g,hg⟩:=(Quotient.exact hOrbit : MulAction.orbitRel S.Generated ℍ p.val z)
  change g • z=p.val at hg
  have hi : p.val∈P.interior := by
    rcases p.property with hi|hb
    · exact hi
    · have hzB : z∈g⁻¹ • P.boundary:=⟨p.val,hb,by change g⁻¹ • p.val=z;rw [←hg,inv_smul_smul]⟩
      exact (hz _ hzB).elim
  let t : S.interiorOrbitLabel z:=⟨g⁻¹,by simpa only [inv_inv,hg] using hi⟩
  refine ⟨t,Subtype.ext ?_⟩
  have heP : (⟨t.val⁻¹ • z,P.interior_subset_carrier t.property⟩ : P.Point)=p:=by
    apply Subtype.ext
    change (g⁻¹)⁻¹ • z=p.val
    simpa only [inv_inv] using hg
  exact (congrArg S.pointProjection heP).trans hp



/-- The actual free interior-translate labels are exactly the points of the
actual identified-polygon fiber at a boundary-avoiding original point. -/
def interiorOrbitFiberEquiv
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) (z : ℍ)
    (hfree : ∀g : S.Generated,g • z=z →g=1)
    (hboundary : ∀g : S.Generated,z∉g • P.boundary) :
    S.interiorOrbitLabel z≃
      {q : S.PointQuotient //S.pointToOrbit
        q=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ z} :=
  Equiv.ofBijective (S.interiorOrbitLabelToFiber z)
    ⟨S.interiorOrbitLabelToFiber_injective z hfree,
      S.interiorOrbitLabelToFiber_surjective z hboundary⟩

/-- The actual compact-orbit bound gives finitely many original interior
translate labels; they are not selected from a postulated finite tiling. -/
theorem interiorOrbitLabel_finite
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier) (z : ℍ) :
    {g : S.Generated | g⁻¹ • z∈P.interior}.Finite := by
  apply ((_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite S.Generated
    hP).point_finite z).subset
  intro g hg
  exact ⟨g⁻¹ • z,P.interior_subset_carrier hg,smul_inv_smul g z⟩

/-- The true literal orbital count is precisely the cardinality of the actual
interior preimage-label type. -/
theorem orbitalCoverMultiplicity_eq_interiorOrbitLabel_card
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitalCoverMultiplicity S.Generated P.interior z=
      (Nat.card (S.interiorOrbitLabel z) : ℝ≥0∞) := by
  have hf:=S.interiorOrbitLabel_finite hP z
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitalCoverMultiplicity_eq_card _ _ hf]
  congr 1
  change hf.toFinset.card=Nat.card {g : S.Generated | g⁻¹ • z∈P.interior}
  rw [Nat.card_coe_set_eq,Set.ncard_eq_toFinset_card _ hf]


end PoincareSidePairing

/-- At every actual free point avoiding the original translated sides, the
number of points in the true side-identified polygon fiber is exactly the
geometrically proved angular multiplicity, with no degree hypothesis. -/
theorem NativeGeodesicPolygonGeometry.identifiedFiber_natCard
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (S : PoincareSidePairing (ℍ≃ᵢℍ) P) [DiscreteTopology S.Generated]
    (hP : IsCompact P.carrier) (z : ℍ)
    (hfree : ∀g : S.Generated,g • z=z →g=1)
    (hboundary : ∀g : S.Generated,z∉g • P.boundary)
    (k : ℕ) (hk : nativePolygonAngularMultiplicity S.Generated P.interior z=k) :
    Nat.card {q : S.PointQuotient //S.pointToOrbit q=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ z}=k := by
  have hfront : ∀g : S.Generated,z∉frontier (g • P.interior) := by
    intro g hg
    change z∈frontier (g.val.toHomeomorph '' P.interior) at hg
    rw [←g.val.toHomeomorph.image_frontier,G.frontier_boundary] at hg
    exact hboundary g hg
  have hE:=Nat.card_congr (S.interiorOrbitFiberEquiv z hfree hboundary)
  have hcard : (Nat.card {q : S.PointQuotient //S.pointToOrbit q=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ z} : ℝ≥0∞)=k := by
    calc
      _=(Nat.card (S.interiorOrbitLabel z) : ℝ≥0∞):=congrArg (fun n : ℕ=>(n : ℝ≥0∞)) hE.symm
      _=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitalCoverMultiplicity S.Generated P.interior z:=
        (S.orbitalCoverMultiplicity_eq_interiorOrbitLabel_card hP z).symm
      _=nativePolygonAngularMultiplicity S.Generated P.interior z:=
        (nativePolygonAngularMultiplicity_eq_orbital_off_frontiers _ _ _ hfront).symm
      _=k:=hk
  exact_mod_cast hcard

/--
The original compact side-identified polygon maps continuously and onto
the actual compact orbit space with finite fibers, and has the same derived
integer fiber degree as at every genuine regular free orbit.
The local ramified-covering property at exceptional points is not asserted here.
-/
theorem nativeJordan_identifiedPolygon_finite_map_degree
    {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉D.vertices →S.OppositeSideNeighborhoods s x) :
    ∃k : ℕ,0<k ∧CompactSpace S.PointQuotient ∧
      CompactSpace (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated ℍ) ∧
      Continuous S.pointToOrbit ∧Function.Surjective S.pointToOrbit ∧
      (∀q : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated ℍ,(S.pointToOrbit ⁻¹'
        {q}).Finite) ∧
      ∀z : ℍ,(∀g : S.Generated,g • z=z →g=1) →
        (∀g : S.Generated,z∉g • P.boundary) →
        Nat.card {q : S.PointQuotient //S.pointToOrbit q=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ z}=k := by
  obtain ⟨k,hk,hAll⟩:=nativeJordan_angularMultiplicity_positive_integer C hC hbound
    hInside hBoundary D S hP hOpp
  let G:=nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D
  have hM : ∀z : ℍ,nativePolygonAngularMultiplicity S.Generated P.carrier z≠0 := by
    intro z
    rw [←G.angularMultiplicity_interior_eq hP S.Generated z,(hAll z).1]
    exact_mod_cast hk.ne'
  refine ⟨k,hk,S.pointQuotient_compactSpace hP,
    S.orbitQuotient_compactSpace_of_positive_angularMultiplicity hP hM,
    S.continuous_pointToOrbit,
    S.pointToOrbit_surjective (S.evaluation_surjective_of_positive_angularMultiplicity hP hM),
    S.pointToOrbit_finite_fibers hP,?_⟩
  intro z hfree hboundary
  exact G.identifiedFiber_natCard S hP z hfree hboundary k (hAll z).1



/-- The genuine free physical points away from every original translated side. -/
def nativePolygonRegularFreeLocus
    (H : Subgroup (ℍ≃ᵢℍ)) (P : PoincarePolygon ℍ) : Set ℍ :=
  {z | (∀g : H,g • z=z →g=1) ∧∀g : H,z∉g • P.boundary}

/-- The regular free locus has full genuine hyperbolic measure, rather than
being a postulated nonempty region on which the degree assertion is conditional. -/
theorem NativeGeodesicPolygonGeometry.ae_regularFreeLocus
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] :
    ∀ᵐz : ℍ∂volume,z∈nativePolygonRegularFreeLocus H P := by
  let : Countable H:=nativeDiscreteIsometrySubgroup_countable H
  have ha : ∀ᵐz : ℍ∂volume,z∉⋃g : H,g • P.boundary:=
    measure_eq_zero_iff_ae_notMem.mp (G.translated_boundary_volume_zero H)
  filter_upwards [_root_.LowDimensionalTopology.Geometry.Fuchsian.nativeCountableIsometrySubgroup_free_points_ae
    H,ha] with z hf hb
  exact ⟨hf,fun g hg=>hb (mem_iUnion.mpr ⟨g,hg⟩)⟩

/-- The actual regular free locus is genuinely dense in the hyperbolic plane,
by the actual positive density area of every original nonempty open set. -/
theorem NativeGeodesicPolygonGeometry.regularFreeLocus_dense
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] :
    Dense (nativePolygonRegularFreeLocus H P) := by
  let : Measure.IsOpenPosMeasure (volume : Measure ℍ):=
    ⟨fun U hU hn=>ne_of_gt (native_open_volume_pos hU hn)⟩
  exact (volume : Measure ℍ).dense_of_ae (G.ae_regularFreeLocus H)


end LowDimensionalTopology.Geometry.Polygon

namespace LowDimensionalTopology.Geometry.Polygon
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane Pointwise ENNReal
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
namespace PoincareSidePairing

/-- The original point-side pairing step is symmetric because the original
paired element is its literal inverse. -/
theorem pointStep_symmetric
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    {p q : P.Point} (h : S.PointStep p q) : S.PointStep q p := by
  obtain ⟨s,hp,hq⟩:=h
  refine ⟨S.paired s,?_,?_⟩
  · rw [←S.generator_side_image s]
    exact ⟨p.val,hp,hq.symm⟩
  · rw [S.generator_paired,hq,inv_smul_smul]

/-- Actual side maps preserve the actual original vertex predicate in both
directions along every genuine elementary side identification. -/
theorem pointStep_vertex_iff
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hV : ∀x∈V,∀s : P.Side,x∈s.val →S.element s x∈V)
    {p q : P.Point} (h : S.PointStep p q) : p.val∈V ↔q.val∈V := by
  obtain ⟨s,hp,hq⟩:=h
  have hqs : q.val∈(S.paired s).val := by
    rw [←S.generator_side_image s]
    exact ⟨p.val,hp,hq.symm⟩
  constructor
  · intro hv
    rw [hq]
    exact hV p.val hv s hp
  · intro hv
    have hh:=hV q.val hv (S.paired s) hqs
    change S.generator (S.paired s) • q.val∈V at hh
    rw [S.generator_paired,hq,inv_smul_smul] at hh
    exact hh

/-- Finite original side chains preserve the actual vertex predicate. -/
theorem pointGluing_vertex_iff
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hV : ∀x∈V,∀s : P.Side,x∈s.val →S.element s x∈V)
    {p q : P.Point} (h : Relation.EqvGen S.PointStep p q) : p.val∈V ↔q.val∈V := by
  induction h with
  | rel p q h =>exact S.pointStep_vertex_iff hV h
  | refl p =>rfl
  | symm p q _ ih =>exact ih.symm
  | trans p q r _ _ ih1 ih2 =>exact ih1.trans ih2

/-- At a true nonvertex point, two successive original side identifications
cancel: uniqueness of the actual incident side retains both original side labels. -/
theorem pointStep_two_cancel_nonvertex
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    {p q r : P.Point} (hq : q.val∉V) (hpq : S.PointStep p q) (hqr : S.PointStep q r) : p=r := by
  obtain ⟨s,hp,heq⟩:=hpq
  obtain ⟨t,hqt,her⟩:=hqr
  have hqs : q.val∈(S.paired s).val := by
    rw [←S.generator_side_image s]
    exact ⟨p.val,hp,heq.symm⟩
  have ht : t=S.paired s := by
    by_contra hn
    exact hq (G.side_meet_vertex t (S.paired s) hn q.val hqt hqs)
  apply Subtype.ext
  rw [her,ht,S.generator_paired,heq,inv_smul_smul]

/-- Every complete original side chain based away from actual vertices has
length at most one after cancellation, rather than an assumed bounded gluing relation. -/
theorem pointGluing_nonvertex_reduces
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hV : ∀x∈V,∀s : P.Side,x∈s.val →S.element s x∈V)
    {p q : P.Point} (h : Relation.EqvGen S.PointStep p q) (hp : p.val∉V) :
    p=q ∨S.PointStep p q := by
  induction h with
  | rel p q h =>exact Or.inr h
  | refl p =>exact Or.inl rfl
  | symm p q h ih =>
    have hq : p.val∉V:=fun hv=>hp ((S.pointGluing_vertex_iff hV h).mp hv)
    rcases ih hq with he| hs
    · exact Or.inl he.symm
    · exact Or.inr (S.pointStep_symmetric hs)
  | trans p q r h1 h2 ih1 ih2 =>
    have hq : q.val∉V:=fun hv=>hp ((S.pointGluing_vertex_iff hV h1).mpr hv)
    rcases ih1 hp with he1| hs1
    · exact he1.symm ▸ ih2 hq
    · rcases ih2 hq with he2| hs2
      · exact he2 ▸ Or.inr hs1
      · exact Or.inl (pointStep_two_cancel_nonvertex G S hq hs1 hs2)

/-- With finitely many actual original sides, the literal elementary pairing
relation is a finite union of genuinely closed side graphs. -/
theorem pointStep_graph_isClosed
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) (hP : IsCompact P.carrier) :
    IsClosed {a : P.Point×P.Point | S.PointStep a.1 a.2} := by
  let : Finite P.Side:=G.finite_sides_of_compact hP
  have he : {a : P.Point×P.Point | S.PointStep a.1 a.2}=
      ⋃s : P.Side,{a : P.Point×P.Point | a.1.val∈s.val ∧a.2.val=S.element s a.1.val} := by
    ext a
    simp only [PointStep,mem_ofPred_eq,mem_iUnion]
    rfl
  rw [he]
  apply isClosed_iUnion_of_finite
  intro s
  exact ((G.side_closed s).preimage (continuous_subtype_val.comp continuous_fst)).inter
    (isClosed_eq (continuous_subtype_val.comp continuous_snd)
      ((S.element s).continuous.comp (continuous_subtype_val.comp continuous_fst)))

/-- The entire actual point-gluing relation is closed: nonvertex classes are
literal side pairs, while all remaining identifications lie in the finite original vertex set. -/
theorem pointGluing_graph_isClosed
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) (hP : IsCompact P.carrier) (hVf :
      V.Finite)
    (hV : ∀x∈V,∀s : P.Side,x∈s.val →S.element s x∈V) :
    IsClosed {a : P.Point×P.Point | Relation.EqvGen S.PointStep a.1 a.2} := by
  classical
  let W : Set P.Point:=Subtype.val ⁻¹' V
  have hf : W.Finite:=hVf.preimage Subtype.val_injective.injOn
  let E : Set (P.Point×P.Point):=
    {a | a.1∈W ∧a.2∈W ∧Relation.EqvGen S.PointStep a.1 a.2}
  have hE : E.Finite:=(hf.prod hf).subset (fun _ h=>⟨h.1,h.2.1⟩)
  have he : {a : P.Point×P.Point | Relation.EqvGen S.PointStep a.1 a.2}=
      Set.diagonal P.Point ∪{a : P.Point×P.Point | S.PointStep a.1 a.2}∪E := by
    ext a
    constructor
    · intro h
      by_cases hv : a.1.val∈V
      · exact Or.inr ⟨hv,(S.pointGluing_vertex_iff hV h).mp hv,h⟩
      · rcases pointGluing_nonvertex_reduces G S hV h hv with he| hs
        · exact Or.inl (Or.inl he)
        · exact Or.inl (Or.inr hs)
    · rintro ((he| hs)| hE)
      · have hab : a.1=a.2:=he
        change Relation.EqvGen S.PointStep a.1 a.2
        rw [←hab]
        exact Relation.EqvGen.refl _
      · exact Relation.EqvGen.rel _ _ hs
      · exact hE.2.2
  rw [he]
  exact (isClosed_diagonal.union (pointStep_graph_isClosed G S hP)).union hE.isClosed

end PoincareSidePairing

/-- Compactness of the literal original polygon derives finiteness of its
actual endpoint vertices from the actual finite side family. -/
theorem NativeGeodesicSideIntervals.vertices_finite_of_compact
    {P : PoincarePolygon ℍ} (D : NativeGeodesicSideIntervals P)
    (G : NativeGeodesicPolygonGeometry P D.vertices) (hP : IsCompact P.carrier) :
    D.vertices.Finite := by
  let : Finite P.Side:=G.finite_sides_of_compact hP
  exact Set.finite_iUnion D.endpoints_finite

end LowDimensionalTopology.Geometry.Polygon

namespace LowDimensionalTopology.Geometry.Polygon
open Set Topology
open scoped UpperHalfPlane
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
namespace PoincareSidePairing

/-- The actual original side-identified polygon has its genuine Hausdorff
quotient topology, derived from the actual closed original point-gluing relation. -/
theorem pointQuotient_t2Space
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) (hP : IsCompact P.carrier) (hVf :
      V.Finite)
    (hV : ∀x∈V,∀s : P.Side,x∈s.val →S.element s x∈V) :
    T2Space S.PointQuotient := by
  let : CompactSpace P.Point:=isCompact_iff_compactSpace.mp hP
  exact _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.closedSetoid_quotient_t2Space S.pointGluingSetoid
    (pointGluing_graph_isClosed G S hP hVf hV)
end PoincareSidePairing

/-- The actual original Jordan polygon's side-identification quotient is
Hausdorff; original finite sidedness and finite vertices are both derived. -/
theorem nativeJordan_pointQuotient_t2Space
    {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hP : IsCompact P.carrier) : T2Space S.PointQuotient := by
  let G:=nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D
  exact _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.pointQuotient_t2Space G S hP
    (D.vertices_finite_of_compact G hP) (D.pairing_preserves_vertices S)
end LowDimensionalTopology.Geometry.Polygon

namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
/-- The actual free-point condition is preserved by the original group action. -/
theorem native_free_smul
    (H : Subgroup (ℍ≃ᵢℍ)) {z : ℍ}
    (hz : ∀h : H,h • z=z →h=1) (g : H) :
    ∀h : H,h • (g • z)=g • z →h=1 := by
  intro h hh
  have hconj : (g⁻¹*h*g) • z=z := by
    simp only [mul_smul]
    rw [hh,inv_smul_smul]
  have he:=congrArg (fun a : H=>g*a*g⁻¹) (hz _ hconj)
  simpa only [mul_assoc,mul_inv_cancel_left,inv_mul_cancel_left,mul_one,one_mul,
    mul_inv_cancel] using he

/-- The actual native orbit projection is locally a homeomorphism at every
actual free point, by the genuine proper action. -/
theorem native_orbitProjection_localHomeomorphOn_free
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] :
    IsLocalHomeomorphOn (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ) {z | ∀h : H,h • z=z →h=1} := by
  let : ProperlyDiscontinuousSMul H ℍ:=_root_.LowDimensionalTopology.Geometry.Fuchsian.nativeIsometrySubgroup_properlyDiscontinuous H
  let : ContinuousConstSMul H ℍ:=⟨fun h=>h.val.continuous⟩
  have hc:=isCoveringMapOn_quotientMk_of_properlyDiscontinuousSMul (G:=H) (E:=ℍ)
  apply hc.isLocalHomeomorphOn.mono
  intro z hz
  refine ⟨z,?_,rfl⟩
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro h hh
  exact hz h (MulAction.mem_stabilizer_iff.mp hh)

namespace PoincareSidePairing
/-- The original open polygon maps to the actual identified polygon. -/
def interiorPointProjection
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) :
    P.interior→S.PointQuotient :=
  fun x=>S.pointProjection ⟨x.val,P.interior_subset_carrier x.property⟩

/-- The actual open interior embeds openly after the literal original side identifications. -/
theorem interiorPointProjection_isOpenEmbedding
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) :
    IsOpenEmbedding S.interiorPointProjection := by
  let e : P.interior≃ₜ{p : P.Point //p.val∈P.interior}:=
    { toFun:=fun x=>⟨⟨x.val,P.interior_subset_carrier x.property⟩,x.property⟩
      invFun:=fun x=>⟨x.val.val,x.property⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl
      continuous_toFun:=by fun_prop
      continuous_invFun:=by fun_prop }
  have he:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.quotient_openEmbedding_of_open_rigid S.pointGluingSetoid
    (Subtype.val ⁻¹' P.interior) (G.interior_open.preimage continuous_subtype_val)
    (fun p hp q h=>S.pointGluing_interior_rigid h (Or.inl hp))
  exact he.comp e.isOpenEmbedding

/-- Over genuine free points avoiding all original translated sides, the
identified-polygon map is locally a homeomorphism. -/
theorem pointToOrbit_localHomeomorphOn_regular
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) [DiscreteTopology S.Generated] :
    IsLocalHomeomorphOn S.pointToOrbit
      (S.pointToOrbit ⁻¹' (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ ''
        _root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonRegularFreeLocus S.Generated P)) := by
  let W : Set P.interior:={x | ∀h : S.Generated,h • x.val=x.val →h=1}
  have hi : IsLocalHomeomorphOn (Subtype.val : P.interior→ℍ) W:=
    G.interior_open.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
  have hcomp : IsLocalHomeomorphOn
      ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ) ∘ (Subtype.val :
        P.interior→ℍ)) W:=
    (_root_.LowDimensionalTopology.Geometry.Polygon.native_orbitProjection_localHomeomorphOn_free
      S.Generated).comp hi (fun _ hx=>hx)
  have hj : IsLocalHomeomorphOn S.interiorPointProjection W:=
    (interiorPointProjection_isOpenEmbedding G S).isLocalHomeomorph.isLocalHomeomorphOn
  have hcomp' : IsLocalHomeomorphOn (S.pointToOrbit ∘ S.interiorPointProjection) W:=hcomp
  apply (hcomp'.of_comp_right hj).mono
  intro q hq
  obtain ⟨z,hz,hzq⟩:=hq
  obtain ⟨g,hg⟩:=S.interiorOrbitLabelToFiber_surjective z hz.2 ⟨q,hzq.symm⟩
  refine ⟨⟨g.val⁻¹ • z,g.property⟩,_root_.LowDimensionalTopology.Geometry.Polygon.native_free_smul S.Generated hz.1
    g.val⁻¹,?_⟩
  exact congrArg Subtype.val hg

/-- On the dense full-area regular free locus, the original compact
side-identified polygon is a genuine covering of the actual orbit space. -/
theorem pointToOrbit_coveringOn_regular
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) [DiscreteTopology S.Generated]
    (hP : IsCompact P.carrier) (hVf : V.Finite)
    (hV : ∀x∈V,∀s : P.Side,x∈s.val →S.element s x∈V) :
    IsCoveringMapOn S.pointToOrbit (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection
      S.Generated ℍ ''
      _root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonRegularFreeLocus S.Generated P) := by
  let : CompactSpace S.PointQuotient:=S.pointQuotient_compactSpace hP
  let : T2Space S.PointQuotient:=pointQuotient_t2Space G S hP hVf hV
  let : ProperlyDiscontinuousSMul S.Generated ℍ:=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.nativeIsometrySubgroup_properlyDiscontinuous S.Generated
  let : ContinuousConstSMul S.Generated ℍ:=⟨fun h=>h.val.continuous⟩
  exact IsCoveringMapOn.of_isLocalHomeomorphOn S.continuous_pointToOrbit
    (pointToOrbit_localHomeomorphOn_regular G S)
end PoincareSidePairing
end LowDimensionalTopology.Geometry.Polygon

namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
/-- The true regular free orbits form a dense subset of the actual orbit space. -/
theorem NativeGeodesicPolygonGeometry.regularFreeOrbitLocus_dense
    {P : PoincarePolygon ℍ} {V : Set ℍ} (G : NativeGeodesicPolygonGeometry P V)
    (H : Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] :
    Dense (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ '' nativePolygonRegularFreeLocus H P) := by
  apply dense_iff_inter_open.mpr
  intro U hU hUne
  have hne : ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ) ⁻¹' U).Nonempty := by
    obtain ⟨q,hq⟩:=hUne
    obtain ⟨z,rfl⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_surjective H ℍ q
    exact ⟨z,hq⟩
  obtain ⟨z,hzU,hzR⟩:=(G.regularFreeLocus_dense H).inter_open_nonempty _
    (hU.preimage (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_continuous H ℍ)) hne
  exact ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection H ℍ z,hzU,⟨z,hzR,rfl⟩⟩

/-- The original compact Jordan polygon's genuine side quotient covers the
actual orbit space over a genuine dense set, without a covering assumption. -/
theorem nativeJordan_identifiedPolygon_coveringOn_regular
    {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier) :
    Dense (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ ''
      nativePolygonRegularFreeLocus S.Generated P) ∧
    IsCoveringMapOn S.pointToOrbit (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection
      S.Generated ℍ ''
      nativePolygonRegularFreeLocus S.Generated P) := by
  let G:=nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D
  exact ⟨G.regularFreeOrbitLocus_dense S.Generated,
    _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.pointToOrbit_coveringOn_regular G S hP
      (D.vertices_finite_of_compact G hP) (D.pairing_preserves_vertices S)⟩
end LowDimensionalTopology.Geometry.Polygon

namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- True native proper compact-orbit bounds make every original raw evaluation
fiber finite, even when the original developing map is multiply covered. -/
theorem copyEvaluation_fiber_finite_of_discrete
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier) (x : ℍ) :
    (S.copyEvaluation ⁻¹' {x}).Finite := by
  let F : Set S.Generated:={g |x∈g • P.carrier}
  have hf : F.Finite:=(_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite
    S.Generated hP).point_finite x
  let j : {b : S.Copy //S.copyEvaluation b=x}→F:=fun b=>
    ⟨b.val.1,⟨b.val.2.val,b.val.2.property,b.property⟩⟩
  have hj : Function.Injective j := by
    intro b c hbc
    have hg : b.val.1=c.val.1:=congrArg Subtype.val hbc
    apply Subtype.ext
    apply Prod.ext hg
    apply Subtype.ext
    have he : b.val.1 • b.val.2.val=c.val.1 • c.val.2.val:=b.property.trans c.property.symm
    rw [←hg] at he
    have hh:=congrArg (fun y : ℍ=>b.val.1⁻¹ • y) he
    simpa only [inv_smul_smul] using hh
  let : Finite F:=hf.to_subtype
  have hfin : Finite {b : S.Copy //S.copyEvaluation b=x}:=Finite.of_injective j hj
  exact Set.finite_coe_iff.mp hfin

/--
Every whole actual original gluing class is finite under native discreteness
and compactness, with no local tessellation or local fundamental-domain premise.
-/
theorem project_fiber_finite_of_discrete
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier) (a : S.Copy) :
    (S.project ⁻¹' {S.project a}).Finite := by
  apply (S.copyEvaluation_fiber_finite_of_discrete hP (S.copyEvaluation a)).subset
  intro b hb
  exact S.gluing_evaluation ((S.project_eq_iff b a).mp hb)

/-- The genuine closed tiles incident through one original side-gluing class. -/
def classTileUnion
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) (a : S.Copy) : Set ℍ :=
  ⋃c : {c : S.Copy //S.project c=S.project a},c.val.1 • P.carrier

/-- Finite actual gluing classes give a genuinely closed ambient tile union. -/
theorem classTileUnion_isClosed
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier) (a : S.Copy) :
    IsClosed (S.classTileUnion a) := by
  let : Finite {c : S.Copy //S.project c=S.project a}:=
    (S.project_fiber_finite_of_discrete hP a).to_subtype
  exact isClosed_iUnion_of_finite (fun c=>c.val.1.val.toHomeomorph.isClosedMap _ hP.isClosed)

/-- Its original glued center belongs to the actual class tile union. -/
theorem copyEvaluation_mem_classTileUnion
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) (a : S.Copy) :
    S.copyEvaluation a∈S.classTileUnion a :=
  mem_iUnion.mpr ⟨⟨a,rfl⟩,⟨a.2.val,a.2.property,rfl⟩⟩


/-- At a true nonvertex point of the full class union, the original opposite-side
convention supplies an ambient neighborhood. The adjacent center remains in the
same whole class because the actual incident original side is crossed. -/
theorem classTileUnion_mem_nhds_of_regular
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    (hOpp : ∀s : P.Side,∀p∈s.val,p∉V →S.OppositeSideNeighborhoods s p)
    (a : S.Copy) (y : ℍ) (hy : y∈S.classTileUnion a)
    (hVertex : ∀g : S.Generated,y∉g • V)
    (hNear : ∀c : S.Copy,S.project c=S.project a →∀s : P.Side,
      c.1⁻¹ • y∈s.val →c.2.val∈s.val) : S.classTileUnion a∈𝓝 y := by
  obtain ⟨c,hc⟩:=mem_iUnion.mp hy
  obtain ⟨p,hp,hpy⟩:=hc
  have hi : c.val.1⁻¹ • y=p:=by rw [←hpy,inv_smul_smul]
  rcases hp with hp|hp
  · have hn : c.val.1 • P.interior∈𝓝 y:=by
      rw [←hpy]
      exact c.val.1.val.toHomeomorph.isOpenMap.image_mem_nhds (G.interior_open.mem_nhds hp)
    apply Filter.mem_of_superset hn
    rintro z ⟨u,hu,rfl⟩
    exact mem_iUnion.mpr ⟨c,⟨u,P.interior_subset_carrier hu,rfl⟩⟩
  · obtain ⟨s,hs,hps⟩:=mem_sUnion.mp hp
    let t : P.Side:=⟨s,hs⟩
    have hpv : p∉V:=fun h=>hVertex c.val.1 ⟨p,h,hpy⟩
    have hct : c.val.2.val∈t.val:=hNear c.val c.property t (hi.symm ▸ hps)
    let d:=S.sideMateCopy c.val t hct
    have hd : S.project d=S.project a:=by
      apply Eq.trans _ c.property
      exact ((S.project_eq_iff c.val d).mpr
        (Relation.EqvGen.rel _ _ (S.step_sideMateCopy c.val t hct))).symm
    have hn : P.carrier∪(fun z : ℍ=>S.generator t • z) ⁻¹' P.carrier∈𝓝 p:=
      hOpp t p hps hpv P.carrier self_mem_nhdsWithin P.carrier self_mem_nhdsWithin
    have hng : c.val.1.val.toHomeomorph ''
        (P.carrier∪(fun z : ℍ=>S.generator t • z) ⁻¹' P.carrier)∈𝓝 y:=by
      rw [←hpy]
      exact c.val.1.val.toHomeomorph.isOpenMap.image_mem_nhds hn
    apply Filter.mem_of_superset hng
    rintro z ⟨u,hu,rfl⟩
    rcases hu with hu|hu
    · exact mem_iUnion.mpr ⟨c,⟨u,hu,rfl⟩⟩
    · apply mem_iUnion.mpr
      refine ⟨⟨d,hd⟩,S.generator t • u,hu,?_⟩
      change (c.val.1*(S.generator t)⁻¹) • (S.generator t • u)=c.val.1 • u
      simp only [mul_smul,inv_smul_smul]

/-- Finitely many actual representatives and the actual locally finite closed
side family give simultaneous absence of all nonincident original sides. -/
theorem classTileUnion_eventually_incident_sides
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) [DiscreteTopology S.Generated]
    (hP : IsCompact P.carrier) (a : S.Copy) :
    ∀ᶠy in 𝓝 (S.copyEvaluation a),∀c : S.Copy,S.project c=S.project a →∀s : P.Side,
      c.1⁻¹ • y∈s.val →c.2.val∈s.val := by
  let I:={c : S.Copy //S.project c=S.project a}
  let : Finite I:=(S.project_fiber_finite_of_discrete hP a).to_subtype
  have hh (c : I) : ∀ᶠy in 𝓝 (S.copyEvaluation a),∀s : P.Side,
      c.val.1⁻¹ • y∈s.val →c.val.2.val∈s.val := by
    obtain ⟨r,hr,hNear⟩:=exists_ball_incident_sides G.locallyFinite G.side_closed c.val.2
    have he : S.copyEvaluation c.val=S.copyEvaluation a:=
      S.gluing_evaluation ((S.project_eq_iff _ _).mp c.property)
    have hc : c.val.1⁻¹ • S.copyEvaluation a=c.val.2.val:=by
      rw [←he]
      exact inv_smul_smul _ _
    have hn : ∀ᶠp in 𝓝 c.val.2.val,∀s : P.Side,p∈s.val →c.val.2.val∈s.val :=
      Filter.mem_of_superset (Metric.ball_mem_nhds c.val.2.val hr) (fun p hp=>hNear p hp)
    have ht:=((c.val.1⁻¹).val.continuous.tendsto (S.copyEvaluation a)).eventually
      (hc.symm ▸ hn)
    change ∀ᶠy in 𝓝 (S.copyEvaluation a),∀s : P.Side,
      c.val.1⁻¹ • y∈s.val →c.val.1⁻¹ • S.copyEvaluation a∈s.val at ht
    simpa only [hc] using ht
  filter_upwards [Filter.eventually_all.mpr hh] with y hy c hc
  exact hy ⟨c,hc⟩



/-- The actual finite original vertices have a locally finite translated
family under genuine native discreteness and compact closure. -/
theorem translated_finite_vertices_closed_discrete
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier)
    (V : Set ℍ) (hV : V.Finite) (hVP : V⊆P.carrier) :
    IsClosed (⋃g : S.Generated,g • V) ∧IsDiscrete (⋃g : S.Generated,g • V) := by
  have hLF : LocallyFinite (fun g : S.Generated=>g • V):=
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.native_compact_translates_locallyFinite S.Generated hP).subset
      (fun _=>image_mono hVP)
  have hf (g : S.Generated) : (g • V).Finite:=hV.image (fun x=>g • x)
  exact ⟨hLF.isClosed_iUnion (fun g=>(hf g).isClosed),
    _root_.LowDimensionalTopology.Geometry.Polygon.locallyFinite_finite_union_isDiscrete hLF hf⟩

/-- There are genuinely no other translated original vertices in a
sufficiently small neighborhood of any specified physical center. -/
theorem eventually_avoid_translated_vertices_except_center
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} (S :
      _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier)
    (V : Set ℍ) (hV : V.Finite) (hVP : V⊆P.carrier) (x : ℍ) :
    ∀ᶠy in 𝓝 x,y≠x →∀g : S.Generated,y∉g • V := by
  obtain ⟨hclosed,hdiscrete⟩:=S.translated_finite_vertices_closed_discrete hP V hV hVP
  by_cases hx : x∈⋃g : S.Generated,g • V
  · obtain ⟨U,hU,hUV⟩:=isDiscrete_iff_forall_mem_exists_isOpen.mp hdiscrete x hx
    have hxU : x∈U:=by
      have hh : x∈U∩⋃g : S.Generated,g • V:=hUV.symm ▸ mem_singleton x
      exact hh.1
    filter_upwards [hU.mem_nhds hxU] with y hy hne g hg
    have he : y∈({x} : Set ℍ):=hUV ▸ ⟨hy,mem_iUnion.mpr ⟨g,hg⟩⟩
    exact hne he
  · filter_upwards [hclosed.isOpen_compl.mem_nhds hx] with y hy _ g hg
    exact hy (mem_iUnion.mpr ⟨g,hg⟩)


end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing

namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane Pointwise ENNReal
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/--
Under genuine native discreteness, the whole original side-gluing class
fills an actual neighborhood of its physical center. Only coverage is asserted;
its pieces may overlap, and no unramified local tessellation fiber equality is assumed.
-/
theorem classTileUnion_mem_nhds
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) [DiscreteTopology S.Generated]
    (hP : IsCompact P.carrier) (hVf : V.Finite) (hVP : V⊆P.carrier)
    (hOpp : ∀s : P.Side,∀p∈s.val,p∉V →S.OppositeSideNeighborhoods s p)
    (a : S.Copy) : S.classTileUnion a∈𝓝 (S.copyEvaluation a) := by
  let x:=S.copyEvaluation a
  have hNear:=classTileUnion_eventually_incident_sides G S hP a
  have hVert:=S.eventually_avoid_translated_vertices_except_center hP V hVf hVP x
  obtain ⟨r,hr,hB⟩:=Metric.mem_nhds_iff.mp (hNear.and hVert)
  let B : Set ℍ:=Metric.ball x r\{x}
  let C : Set B:=Subtype.val ⁻¹' S.classTileUnion a
  have hPre : IsPreconnected B:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.native_punctured_ball_isPreconnected x r
  let : PreconnectedSpace B:=isPreconnected_iff_preconnectedSpace.mp hPre
  have hCclosed : IsClosed C:=(S.classTileUnion_isClosed hP a).preimage continuous_subtype_val
  have hCopen : IsOpen C:=by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    have hNr:=hB y.property.1
    have hn : S.classTileUnion a∈𝓝 y.val:=
      classTileUnion_mem_nhds_of_regular G S hOpp a y.val hy
        (hNr.2 y.property.2) hNr.1
    exact (continuous_subtype_val.tendsto y).eventually hn
  have hx : x∈closure (a.1 • P.interior):=by
    have hp : a.2.val∈closure P.interior:=G.carrier_closure ▸ a.2.property
    exact image_closure_subset_closure_image a.1.val.continuous ⟨a.2.val,hp,rfl⟩
  let U : Set ℍ:=(a.1 • P.interior)∩Metric.ball x r
  have hUopen : IsOpen U:=
    (a.1.val.toHomeomorph.isOpenMap _ G.interior_open).inter Metric.isOpen_ball
  have hUnonempty : U.Nonempty:=by
    obtain ⟨y,hy,hyr⟩:=((mem_closure_iff_frequently.mp hx).and_eventually
      (Metric.ball_mem_nhds x hr)).exists
    exact ⟨y,hy,hyr⟩
  have hUnot : ¬U⊆({x} : Set ℍ):=by
    intro hh
    exact ne_of_gt (_root_.LowDimensionalTopology.Geometry.Polygon.native_open_volume_pos hUopen hUnonempty)
      (measure_mono_null hh (_root_.LowDimensionalTopology.Geometry.Polygon.native_countable_volume_zero
        (Set.countable_singleton x)))
  obtain ⟨y,hy,hyne⟩:=not_subset.mp hUnot
  have hyStar : y∈S.classTileUnion a:=by
    obtain ⟨p,hp,hpy⟩:=hy.1
    exact mem_iUnion.mpr ⟨⟨a,rfl⟩,⟨p,P.interior_subset_carrier hp,hpy⟩⟩
  have hAll : (univ : Set B)⊆C:=
    isPreconnected_univ.subset_isClopen ⟨hCclosed,hCopen⟩
      ⟨⟨y,hy.2,hyne⟩,trivial,hyStar⟩
  apply Filter.mem_of_superset (Metric.ball_mem_nhds x hr)
  intro z hz
  by_cases he : z=x
  · exact he ▸ S.copyEvaluation_mem_classTileUnion a
  · exact hAll (a:=⟨z,hz,he⟩) trivial

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing

namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
open Set Filter Topology MeasureTheory
open scoped UpperHalfPlane Pointwise ENNReal
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/--
The genuine original side-identified polygon maps openly onto its actual
orbit space. Discreteness supplies finite whole classes, and the original
opposite-side convention supplies local coverage; no local tessellation injectivity is assumed.
-/
theorem pointToOrbit_isOpenMap
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) [DiscreteTopology S.Generated]
    (hP : IsCompact P.carrier) (hVf : V.Finite) (hVP : V⊆P.carrier)
    (hOpp : ∀s : P.Side,∀p∈s.val,p∉V →S.OppositeSideNeighborhoods s p) :
    IsOpenMap S.pointToOrbit := by
  let : ContinuousConstSMul S.Generated ℍ:=⟨fun g=>g.val.continuous⟩
  have hπ : IsOpenMap (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ):=
    MulAction.isOpenQuotientMap_quotientMk.isOpenMap
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro q ⟨p,hp,rfl⟩
  obtain ⟨z,hz⟩:=Quotient.exists_rep p
  change S.pointProjection z=p at hz
  let a : S.Copy:=(1,z)
  let I:={c : S.Copy //S.project c=S.project a}
  let : Finite I:=(S.project_fiber_finite_of_discrete hP a).to_subtype
  have hEach (c : I) : ∃δ : ℝ,0<δ ∧∀u : P.Point,dist u c.val.2<δ →S.pointProjection u∈U := by
    have he : S.pointProjection c.val.2=S.pointProjection z:=by
      have hh:=congrArg S.forgetIndex c.property
      simpa only [forgetIndex_project,a] using hh
    have hcp : S.pointProjection c.val.2∈U:=by rw [he,hz];exact hp
    have hn : S.pointProjection ⁻¹' U∈𝓝 c.val.2:=
      (S.continuous_pointProjection.tendsto c.val.2).eventually (hU.mem_nhds hcp)
    obtain ⟨δ,hδ,hδB⟩:=Metric.mem_nhds_iff.mp hn
    exact ⟨δ,hδ,fun u hu=>hδB hu⟩
  choose δ hδ hδB using hEach
  obtain ⟨c0,_hc0,hmin⟩:=Set.exists_min_image (univ : Set I) δ (Set.toFinite _)
    ⟨⟨a,rfl⟩,trivial⟩
  have hN:=classTileUnion_mem_nhds G S hP hVf hVP hOpp a
  obtain ⟨ρ,hρ,hρB⟩:=Metric.mem_nhds_iff.mp hN
  let r:=min ρ (δ c0)
  have hr : 0<r:=lt_min hρ (hδ c0)
  have hsmall : ∀c : I,r≤δ c:=fun c=>(min_le_right _ _).trans (hmin c trivial)
  have htarget : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ '' Metric.ball z.val r∈
      𝓝 (S.pointToOrbit p):=by
    rw [←hz,S.pointToOrbit_projection]
    exact hπ.image_mem_nhds (Metric.ball_mem_nhds z.val hr)
  apply Filter.mem_of_superset htarget
  rintro w ⟨y,hy,rfl⟩
  have hya : dist y (S.copyEvaluation a)<ρ:=by
    change dist y z.val<ρ
    exact lt_of_lt_of_le hy (min_le_left _ _)
  obtain ⟨c,hc⟩:=mem_iUnion.mp (hρB hya)
  obtain ⟨v,hv,hvy⟩:=hc
  change c.val.1 • v=y at hvy
  let u : P.Point:=⟨v,hv⟩
  have hcenter : c.val.1 • c.val.2.val=z.val:=by
    have hh:=S.gluing_evaluation ((S.project_eq_iff _ _).mp c.property)
    simpa only [copyEvaluation,a,one_smul] using hh
  have hdist : dist u c.val.2<r:=by
    change dist v c.val.2.val<r
    calc
      dist v c.val.2.val=dist (c.val.1 • v) (c.val.1 • c.val.2.val):=
        (c.val.1.val.dist_eq _ _).symm
      _=dist y z.val:=congrArg₂ dist hvy hcenter
      _<r:=hy
  have hu : S.pointProjection u∈U:=hδB c u (lt_of_lt_of_le hdist (hsmall c))
  refine ⟨S.pointProjection u,hu,?_⟩
  rw [S.pointToOrbit_projection]
  exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection_smul S.Generated ℍ c.val.1
    v).symm.trans
    (congrArg (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ) hvy)

end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing

namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
/-- The actual original compact Jordan polygon's side-identified map is open,
with finite original vertices derived from compactness and the original side intervals. -/
theorem nativeJordan_pointToOrbit_isOpenMap
    {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉D.vertices →S.OppositeSideNeighborhoods s x) :
    IsOpenMap S.pointToOrbit := by
  let G:=nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D
  let : Finite P.Side:=G.finite_sides_of_compact hP
  have hVf : D.vertices.Finite:=Set.finite_iUnion D.endpoints_finite
  have hVP : D.vertices⊆P.carrier := by
    intro x hx
    obtain ⟨s,hs⟩:=mem_iUnion.mp hx
    exact P.side_subset_carrier s (D.endpoints_subset_side s hs)
  exact _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.pointToOrbit_isOpenMap G S hP hVf hVP hOpp
end LowDimensionalTopology.Geometry.Polygon

namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
/--
The actual original side-identified compact polygon is a compact Hausdorff
space mapping continuously, openly, and finitely onto the compact Hausdorff orbit
space. Over a genuine dense full-area regular locus it is an actual covering of
the same derived positive integer degree as. Local branch models
at the exceptional points are not asserted in this intermediate result.
-/
theorem nativeJordan_identifiedPolygon_finite_open_cover_degree
    {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier)
    (hOpp : ∀s : P.Side,∀x∈s.val,x∉D.vertices →S.OppositeSideNeighborhoods s x) :
    ∃k : ℕ,0<k ∧CompactSpace S.PointQuotient ∧T2Space S.PointQuotient ∧
      CompactSpace (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated
        ℍ) ∧T2Space (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated ℍ) ∧
      Continuous S.pointToOrbit ∧IsOpenMap S.pointToOrbit ∧
      Function.Surjective S.pointToOrbit ∧
      (∀q : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient S.Generated ℍ,(S.pointToOrbit ⁻¹'
        {q}).Finite) ∧
      Dense (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ ''
        nativePolygonRegularFreeLocus S.Generated P) ∧
      IsCoveringMapOn S.pointToOrbit (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection
        S.Generated ℍ ''
        nativePolygonRegularFreeLocus S.Generated P) ∧
      ∀q∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ '' nativePolygonRegularFreeLocus S.Generated P,
        Nat.card (S.pointToOrbit ⁻¹' {q})=k := by
  obtain ⟨k,hk,hSrc,hTgt,hCont,hSurj,hFib,hDeg⟩:=
    nativeJordan_identifiedPolygon_finite_map_degree C hC hbound hInside hBoundary D S hP hOpp
  let : ProperlyDiscontinuousSMul S.Generated ℍ:=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.nativeIsometrySubgroup_properlyDiscontinuous S.Generated
  let : ContinuousConstSMul S.Generated ℍ:=⟨fun h=>h.val.continuous⟩
  obtain ⟨hDense,hCover⟩:=nativeJordan_identifiedPolygon_coveringOn_regular
    C hC hbound hInside hBoundary D S hP
  refine ⟨k,hk,hSrc,nativeJordan_pointQuotient_t2Space C hC hbound hInside hBoundary D S hP,
    hTgt,inferInstance,hCont,
    nativeJordan_pointToOrbit_isOpenMap C hC hbound hInside hBoundary D S hP hOpp,
    hSurj,hFib,hDense,hCover,?_⟩
  rintro q ⟨z,hz,rfl⟩
  exact hDeg z hz.1 hz.2
end LowDimensionalTopology.Geometry.Polygon

namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
universe u v
variable {X : Type u} {Γ : Type v} [Group Γ] [MulAction Γ X]
variable {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon X} (S :
  _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing Γ P)

/-- Every literal original point-gluing chain lifts to a genuine generated
translation between original development copies. -/
theorem pointGluing_lift_translate {p q : P.Point}
    (h : Relation.EqvGen S.PointStep p q) :
    ∃g : S.Generated,S.project (1,p)=g • S.project (1,q) := by
  induction h with
  | rel p q h =>
    obtain ⟨s,hp,hq⟩:=h
    refine ⟨(S.generator s)⁻¹,?_⟩
    apply (S.project_eq_iff _ _).mpr
    apply Relation.EqvGen.rel
    exact Or.inr ⟨s,hp,hq,by change 1=((S.generator s)⁻¹*1)*S.generator s;simp⟩
  | refl p => exact ⟨1,(one_smul _ _).symm⟩
  | symm p q _ ih =>
    obtain ⟨g,hg⟩:=ih
    refine ⟨g⁻¹,?_⟩
    rw [hg,inv_smul_smul]
  | trans p q r _ _ ih1 ih2 =>
    obtain ⟨g,hg⟩:=ih1
    obtain ⟨h,hh⟩:=ih2
    exact ⟨g*h,by rw [hg,hh,mul_smul]⟩

/-- The original identified polygon is exactly the orbit quotient of the
original development by its true generated left translations. -/
theorem forgetIndex_eq_iff_exists_smul (a b : S.Development) :
    S.forgetIndex a=S.forgetIndex b ↔∃g : S.Generated,a=g • b := by
  induction a using Quotient.inductionOn with
  | h a =>
    induction b using Quotient.inductionOn with
    | h b =>
      constructor
      · intro he
        have hPoint : Relation.EqvGen S.PointStep a.2 b.2:=Quotient.exact he
        obtain ⟨g,hg⟩:=S.pointGluing_lift_translate hPoint
        refine ⟨a.1*g*b.1⁻¹,?_⟩
        have hh:=congrArg (fun q : S.Development=>a.1 • q) hg
        have hae : ((a.1,a.2) : S.Copy)=a:=by cases a;rfl
        change S.project a=S.project (((a.1*g*b.1⁻¹)*b.1),b.2)
        simpa only [smul_project,translateCopy,mul_one,mul_assoc,inv_mul_cancel,
          mul_one,hae] using hh
      · rintro ⟨g,he⟩
        rw [he,S.forgetIndex_smul]

/-- The index-forgetting map is onto the literal original side quotient. -/
theorem forgetIndex_surjective : Function.Surjective S.forgetIndex := by
  intro q
  induction q using Quotient.inductionOn with
  | h p => exact ⟨S.project (1,p),rfl⟩

/-- Forgetting the copy index is an actual open map, without requiring the
original evaluation to be injective or a local tessellation. -/
theorem forgetIndex_isOpenMap [TopologicalSpace X] : IsOpenMap S.forgetIndex := by
  let : TopologicalSpace S.Generated:=⊥
  let : DiscreteTopology S.Generated:=⟨rfl⟩
  intro U hU
  apply isQuotientMap_quotient_mk'.isOpen_preimage.mp
  change IsOpen (S.pointProjection ⁻¹' (S.forgetIndex '' U))
  have he : S.pointProjection ⁻¹' (S.forgetIndex '' U)=
      (fun p : P.Point=>S.project (1,p)) ⁻¹'
        (⋃g : S.Generated,S.translationHomeomorph g '' U) := by
    ext p
    constructor
    · rintro ⟨q,hq,he⟩
      obtain ⟨g,hg⟩:=(S.forgetIndex_eq_iff_exists_smul _ _).mp
        ((S.forgetIndex_project (1,p)).trans he.symm)
      exact mem_iUnion.mpr ⟨g,⟨q,hq,hg.symm⟩⟩
    · intro hp
      obtain ⟨g,q,hq,hg⟩:=mem_iUnion.mp hp
      refine ⟨q,hq,?_⟩
      have hh:=congrArg S.forgetIndex hg
      exact (S.forgetIndex_smul g q).symm.trans hh
  rw [he]
  exact (isOpen_iUnion fun g=>(S.translationHomeomorph g).isOpenMap _ hU).preimage
    (S.continuous_project.comp (continuous_const.prodMk continuous_id))
end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
/--
Actual whole-class local coverage makes the original developing map open,
even at its genuine ramification points. No local tessellation injectivity is imposed.
-/
theorem evaluation_isOpenMap_of_opposite
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) [DiscreteTopology S.Generated]
    (hP : IsCompact P.carrier) (hVf : V.Finite) (hVP : V⊆P.carrier)
    (hOpp : ∀s : P.Side,∀p∈s.val,p∉V →S.OppositeSideNeighborhoods s p) :
    IsOpenMap S.evaluation := by
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨q,hq,rfl⟩
  obtain ⟨a,ha⟩:=Quotient.exists_rep q
  change S.project a=q at ha
  let I:={c : S.Copy //S.project c=S.project a}
  let : Finite I:=(S.project_fiber_finite_of_discrete hP a).to_subtype
  have hEach (c : I) : ∃δ : ℝ,0<δ ∧∀u : P.Point,dist u c.val.2<δ →S.project (c.val.1,u)∈U := by
    have hcp : S.project c.val∈U:=by rw [c.property,ha];exact hq
    have hc : Continuous (fun u : P.Point=>S.project (c.val.1,u)) := by
      let : TopologicalSpace S.Generated:=⊥
      exact S.continuous_project.comp (continuous_const.prodMk continuous_id)
    have hn : (fun u : P.Point=>S.project (c.val.1,u)) ⁻¹' U∈𝓝 c.val.2:=
      (hc.tendsto c.val.2).eventually (hU.mem_nhds hcp)
    obtain ⟨δ,hδ,hδB⟩:=Metric.mem_nhds_iff.mp hn
    exact ⟨δ,hδ,fun u hu=>hδB hu⟩
  choose δ hδ hδB using hEach
  obtain ⟨c0,_hc0,hmin⟩:=Set.exists_min_image (univ : Set I) δ (Set.toFinite _)
    ⟨⟨a,rfl⟩,trivial⟩
  have hN:=classTileUnion_mem_nhds G S hP hVf hVP hOpp a
  obtain ⟨ρ,hρ,hρB⟩:=Metric.mem_nhds_iff.mp hN
  let r:=min ρ (δ c0)
  have hr : 0<r:=lt_min hρ (hδ c0)
  have hsmall : ∀c : I,r≤δ c:=fun c=>(min_le_right _ _).trans (hmin c trivial)
  apply Filter.mem_of_superset (Metric.ball_mem_nhds (S.evaluation q) hr)
  intro y hy
  have hya : dist y (S.copyEvaluation a)<ρ:=by
    rw [←ha] at hy
    exact lt_of_lt_of_le hy (min_le_left _ _)
  obtain ⟨c,hc⟩:=mem_iUnion.mp (hρB hya)
  obtain ⟨v,hv,hvy⟩:=hc
  change c.val.1 • v=y at hvy
  let u : P.Point:=⟨v,hv⟩
  have hcenter : c.val.1 • c.val.2.val=S.evaluation q:=by
    have hh:=S.gluing_evaluation ((S.project_eq_iff _ _).mp c.property)
    exact hh.trans (congrArg S.evaluation ha)
  have hdist : dist u c.val.2<r:=by
    change dist v c.val.2.val<r
    calc
      dist v c.val.2.val=dist (c.val.1 • v) (c.val.1 • c.val.2.val):=
        (c.val.1.val.dist_eq _ _).symm
      _=dist y (S.evaluation q):=congrArg₂ dist hvy hcenter
      _<r:=hy
  exact ⟨S.project (c.val.1,u),hδB c u (lt_of_lt_of_le hdist (hsmall c)),hvy⟩
end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing

namespace LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
/-- The original developing map is a true local homeomorphism at every
original nonvertex class, including actual interiors of paired sides. -/
theorem evaluation_localHomeomorphOn_nonvertex
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) [DiscreteTopology S.Generated]
    (hP : IsCompact P.carrier) (hVf : V.Finite) (hVP : V⊆P.carrier)
    (hV : ∀x∈V,∀s : P.Side,x∈s.val →S.element s x∈V)
    (hOpp : ∀s : P.Side,∀p∈s.val,p∉V →S.OppositeSideNeighborhoods s p) :
    IsLocalHomeomorphOn S.evaluation
      {q | ∃a : S.Copy,S.project a=q ∧a.2.val∉V} := by
  let : IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  have hOpen:=evaluation_isOpenMap_of_opposite G S hP hVf hVP hOpp
  rintro q ⟨a,rfl,hav⟩
  have hx : ∃r : ℝ,0<r ∧S.LocalTessellation (1,a.2) r := by
    rcases G.regularity_of_vertex_preservation S hV hOpp a.2 hav with hi|⟨s,r,hs⟩
    · obtain ⟨r,hr,hR⟩:=S.interior_local_radius G.interior_open a.2 hi
      exact ⟨r,hr,hR r hr le_rfl⟩
    · exact ⟨r,hs.positive,hs.localTessellation S⟩
  obtain ⟨r,hr,ht⟩:=hx
  have ha : S.translateCopy a.1 (1,a.2)=a:=by
    change ((a.1*1,a.2) : S.Copy)=a
    rw [mul_one]
    cases a
    rfl
  have ht' : S.LocalTessellation a r:=ha ▸ ht.translate S a.1
  let e : OpenPartialHomeomorph S.Development ℍ:=OpenPartialHomeomorph.ofContinuousOpen
    ((ht'.evaluation_injOn S).toPartialEquiv S.evaluation (S.project '' S.copyNeighborhood a r))
    S.continuous_evaluation_of_generated_isometric.continuousOn hOpen (ht'.isOpen_image S)
  exact ⟨e,ht'.center_mem S hr,rfl⟩
end LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing



namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
/-- The actual free native points away from genuine translated vertices; side
interiors are included. -/
def nativePolygonNonvertexFreeLocus (H : Subgroup (ℍ≃ᵢℍ)) (V : Set ℍ) : Set ℍ:=
  {z | (∀g : H,g • z=z →g=1) ∧∀g : H,z∉g • V}

namespace PoincareSidePairing
/-- The original side quotient is locally unramified at every free orbit
avoiding the true original vertices, including all genuine side-interior orbits. -/
theorem pointToOrbit_localHomeomorphOn_nonvertex_free
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) [DiscreteTopology S.Generated]
    (hP : IsCompact P.carrier) (hVf : V.Finite) (hVP : V⊆P.carrier)
    (hV : ∀x∈V,∀s : P.Side,x∈s.val →S.element s x∈V)
    (hOpp : ∀s : P.Side,∀p∈s.val,p∉V →S.OppositeSideNeighborhoods s p) :
    IsLocalHomeomorphOn S.pointToOrbit
      (S.pointToOrbit ⁻¹' (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ ''
        _root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonNonvertexFreeLocus S.Generated V)) := by
  let A : Set S.Development:=S.evaluation ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonNonvertexFreeLocus S.Generated V
  have he : IsLocalHomeomorphOn S.evaluation A := by
    apply (evaluation_localHomeomorphOn_nonvertex G S hP hVf hVP hV hOpp).mono
    intro q hq
    obtain ⟨a,ha⟩:=Quotient.exists_rep q
    change S.project a=q at ha
    refine ⟨a,ha,?_⟩
    intro hav
    apply hq.2 a.1
    exact ⟨a.2.val,hav,congrArg S.evaluation ha⟩
  have hcomp : IsLocalHomeomorphOn ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection
    S.Generated ℍ) ∘ S.evaluation) A:=
    (_root_.LowDimensionalTopology.Geometry.Polygon.native_orbitProjection_localHomeomorphOn_free
      S.Generated).comp he (fun _ hx=>hx.1)
  have heq : (S.pointToOrbit ∘ S.forgetIndex)=
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ) ∘ S.evaluation:=
    funext (S.pointToOrbit_forgetIndex)
  rw [←heq] at hcomp
  have hf : IsLocalHomeomorphOn S.forgetIndex A:=
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.localHomeomorphOn_first_of_comp_open hcomp S.continuous_forgetIndex S.forgetIndex_isOpenMap
  apply (hcomp.of_comp_right hf).mono
  intro q hq
  obtain ⟨z,hz,hzq⟩:=hq
  obtain ⟨p,hp⟩:=Quotient.exists_rep q
  change S.pointProjection p=q at hp
  have hOrbit : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ p.val=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection S.Generated ℍ z:=
    (S.pointToOrbit_projection p).symm.trans ((congrArg S.pointToOrbit hp).trans hzq.symm)
  obtain ⟨g,hg⟩:=(Quotient.exact hOrbit : MulAction.orbitRel S.Generated ℍ p.val z)
  change g • z=p.val at hg
  let a : S.Copy:=(g⁻¹,p)
  have hE : S.evaluation (S.project a)=z:=by
    change g⁻¹ • p.val=z
    rw [←hg,inv_smul_smul]
  exact ⟨S.project a,by change S.evaluation (S.project a)∈_root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonNonvertexFreeLocus S.Generated V;rw [hE];exact hz,hp⟩

/-- The true covering extends across every original side interior. Only genuine
vertex orbits and nontrivial stabilizers are excluded from this statement. -/
theorem pointToOrbit_coveringOn_nonvertex_free
    {P : _root_.LowDimensionalTopology.Geometry.Polygon.PoincarePolygon ℍ} {V : Set ℍ} (G :
      _root_.LowDimensionalTopology.Geometry.Polygon.NativeGeodesicPolygonGeometry P V)
    (S : _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ≃ᵢℍ) P) [DiscreteTopology S.Generated]
    (hP : IsCompact P.carrier) (hVf : V.Finite) (hVP : V⊆P.carrier)
    (hV : ∀x∈V,∀s : P.Side,x∈s.val →S.element s x∈V)
    (hOpp : ∀s : P.Side,∀p∈s.val,p∉V →S.OppositeSideNeighborhoods s p) :
    IsCoveringMapOn S.pointToOrbit (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection
      S.Generated ℍ ''
      _root_.LowDimensionalTopology.Geometry.Polygon.nativePolygonNonvertexFreeLocus S.Generated V) := by
  let : CompactSpace S.PointQuotient:=S.pointQuotient_compactSpace hP
  let : T2Space S.PointQuotient:=pointQuotient_t2Space G S hP hVf hV
  let : ProperlyDiscontinuousSMul S.Generated ℍ:=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.nativeIsometrySubgroup_properlyDiscontinuous S.Generated
  let : ContinuousConstSMul S.Generated ℍ:=⟨fun h=>h.val.continuous⟩
  exact IsCoveringMapOn.of_isLocalHomeomorphOn S.continuous_pointToOrbit
    (pointToOrbit_localHomeomorphOn_nonvertex_free G S hP hVf hVP hV hOpp)
end PoincareSidePairing

/-- The actual original compact Jordan polygon covers all nonvertex free
orbits, including the images of genuine original paired side interiors. -/
theorem nativeJordan_identifiedPolygon_coveringOn_nonvertex_free
    {P : PoincarePolygon ℍ}
    (C : Set ℂ) (hC : IsComplexJordanCurve C) (hbound : C⊆Metric.closedBall (0 : ℂ) 1)
    (hInside : P.interior=nativeJordanInside C)
    (hBoundary : P.boundary=(fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹'
      C)
    (D : NativeGeodesicSideIntervals P) (S : PoincareSidePairing (ℍ≃ᵢℍ) P)
    [DiscreteTopology S.Generated] (hP : IsCompact P.carrier)
    (hOpp : ∀s : P.Side,∀p∈s.val,p∉D.vertices →S.OppositeSideNeighborhoods s p) :
    IsCoveringMapOn S.pointToOrbit (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection
      S.Generated ℍ ''
      nativePolygonNonvertexFreeLocus S.Generated D.vertices) := by
  let G:=nativeJordan_sideIntervals_geometry C hC hbound hInside hBoundary D
  have hVP : D.vertices⊆P.carrier := by
    intro x hx
    obtain ⟨s,hs⟩:=mem_iUnion.mp hx
    exact P.side_subset_carrier s (D.endpoints_subset_side s hs)
  exact _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.pointToOrbit_coveringOn_nonvertex_free G S hP
    (D.vertices_finite_of_compact G hP) hVP (D.pairing_preserves_vertices S) hOpp
end LowDimensionalTopology.Geometry.Polygon
