module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.HyperbolicSidePairing
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSelfPairedSides
/-!
# Compact connectors along hyperbolic side pairings

Coordinate chords join boundary points through the polygon interior. For a
hyperbolic side pairing, the polygon supplies a free compact connector whose
periodic trace is disjoint from the traces of different cyclic cosets.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric
open scoped Topology Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A literal straight chord in a genuine coordinate, regarded as a subset of the original space. -/
def coordinateChord {X : Type*} (f : X → ℂ) (a b : X) : Set X := f ⁻¹' segment ℝ (f a) (f b)

/-- The coordinate image is the whole chord, rather than a clipped surrogate. -/
theorem coordinateChord_image {X : Type*} (f : X → ℂ) (hr : Convex ℝ (range f)) (a b : X) :
    f '' coordinateChord f a b = segment ℝ (f a) (f b) := by
  exact image_preimage_eq_of_subset (hr.segment_subset (mem_range_self a) (mem_range_self b))

theorem coordinateChord_compact {X : Type*} [TopologicalSpace X] (f : X → ℂ)
    (hf : Topology.IsEmbedding f) (hr : Convex ℝ (range f)) (a b : X) :
    IsCompact (coordinateChord f a b) := by
  apply hf.isCompact_iff.mpr
  rw [coordinateChord_image f hr]
  rw [segment_eq_image' ℝ (f a) (f b)]
  exact isCompact_Icc.image (by fun_prop)

theorem coordinateChord_preconnected {X : Type*} [TopologicalSpace X] (f : X → ℂ)
    (hf : Topology.IsEmbedding f) (hr : Convex ℝ (range f)) (a b : X) :
    IsPreconnected (coordinateChord f a b) := by
  apply hf.isInducing.isPreconnected_image.mp
  rw [coordinateChord_image f hr]
  exact (convex_segment (f a) (f b)).isPreconnected

/-- Except for its boundary endpoint, a chord from a genuine interior point lies in the original open convex domain. -/
theorem coordinateChord_except_boundary_subset {X : Type*} [TopologicalSpace X] (f : X → ℂ)
    (hf : Topology.IsOpenEmbedding f) {D : Set X} (ho : IsOpen D)
    (hc : Convex ℝ (f '' D)) {a w : X} (ha : a ∈ D) (hw : w ∈ closure D) :
    coordinateChord f a w \ {w} ⊆ D := by
  rintro z ⟨hz,hzw⟩
  by_cases hza : z = a
  · exact hza ▸ ha
  have hfz : f z ∈ openSegment ℝ (f a) (f w) :=
    mem_openSegment_of_ne_left_right (hf.injective.ne (Ne.symm hza))
      (hf.injective.ne (by simpa only [mem_singleton_iff] using hzw) |>.symm) hz
  have hfo : IsOpen (f '' D) := hf.isOpenMap D ho
  have hfa : f a ∈ interior (f '' D) := by rw [hfo.interior_eq];exact mem_image_of_mem _ ha
  have hfw : f w ∈ closure (f '' D) := by
    rwa [hf.isEmbedding.closure_eq_preimage_closure_image D] at hw
  have hzi := hc.openSegment_interior_closure_subset_interior hfa hfw hfz
  rw [hfo.interior_eq] at hzi
  obtain ⟨v,hv,hve⟩ := hzi
  exact hf.injective hve ▸ hv

/-- Every two genuine closed-domain points admit an actual compact connected connector whose other points are interior. -/
theorem exists_compact_convex_connector {X : Type*} [TopologicalSpace X] (f : X → ℂ)
    (hf : Topology.IsOpenEmbedding f) (hr : Convex ℝ (range f))
    {D : Set X} (ho : IsOpen D) (hc : Convex ℝ (f '' D)) (hne : D.Nonempty)
    {w v : X} (hw : w ∈ closure D) (hv : v ∈ closure D) :
    ∃ C : Set X, IsCompact C ∧ IsPreconnected C ∧ w ∈ C ∧ v ∈ C ∧ C ⊆ D ∪ {w,v} := by
  obtain ⟨a,ha⟩ := hne
  let C := coordinateChord f a w ∪ coordinateChord f a v
  have haC : a ∈ coordinateChord f a w ∩ coordinateChord f a v :=
    ⟨left_mem_segment ℝ _ _,left_mem_segment ℝ _ _⟩
  refine ⟨C,(coordinateChord_compact f hf.isEmbedding hr a w).union (coordinateChord_compact f hf.isEmbedding hr a v),
    (coordinateChord_preconnected f hf.isEmbedding hr a w).union a haC.1 haC.2
      (coordinateChord_preconnected f hf.isEmbedding hr a v),
    Or.inl (right_mem_segment ℝ _ _),Or.inr (right_mem_segment ℝ _ _),?_⟩
  rintro z (hz | hz)
  · by_cases hzw : z = w
    · exact Or.inr (Or.inl hzw)
    · exact Or.inl (coordinateChord_except_boundary_subset f hf ho hc ha hw ⟨hz,hzw⟩)
  · by_cases hzv : z = v
    · exact Or.inr (Or.inr hzv)
    · exact Or.inl (coordinateChord_except_boundary_subset f hf ho hc ha hv ⟨hz,hzv⟩)

/-- The two genuine paired-side endpoints admit the needed compact connector without extra arc hypotheses. -/
theorem IsConvexFuchsianPolygon.side_connector {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D : Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (s : FuchsianPolygonSides P D)
    {w : P.domain.carrier} (hw : w ∈ s.val) :
    ∃ C : Set P.domain.carrier, IsCompact C ∧ IsPreconnected C ∧
      w ∈ C ∧ (fuchsianSideElement hD s)⁻¹ • w ∈ C ∧
      C ⊆ D ∪ {w,(fuchsianSideElement hD s)⁻¹ • w} := by
  have hws := (fuchsianSideElement_spec hD s).2 ▸ hw
  obtain ⟨v,hv,hvw⟩ := hws.2
  have hwinv : (fuchsianSideElement hD s)⁻¹ • w = v := by
    change (fuchsianSideElement hD s) • v = w at hvw
    rw [←hvw,inv_smul_smul]
  have hc := hD.locallyFinite.fundamental
  exact exists_compact_convex_connector P.kleinCoordinate P.kleinCoordinate_isOpenEmbedding
    (by rw [P.kleinCoordinate_range];exact convex_ball _ _)
    ((isFuchsianFundamentalDomain_iff P D).mp hc).1 hD.klein_convex
    ((isFuchsianFundamentalDomain_iff P D).mp hc).2.1.nonempty hws.1 (hwinv ▸ hv)

/-- Repeated connectors have either a translated interior representative or a translated endpoint. -/
theorem cyclic_connector_point_cases {G X : Type*} [Group G] [MulAction G X]
    (g : G) {D C : Set X} {w z : X} (hC : C ⊆ D ∪ {w,g • w})
    (hz : z ∈ ⋃ n : ℤ, (g^n • ·) '' C) :
    (∃ n : ℤ, ∃ x ∈ D, g^n • x = z) ∨ ∃ n : ℤ, g^n • w = z := by
  obtain ⟨n,x,hx,rfl⟩ := mem_iUnion.mp hz
  rcases hC hx with hx | rfl | rfl
  · exact Or.inl ⟨n,x,hx,rfl⟩
  · exact Or.inr ⟨n,rfl⟩
  · exact Or.inr ⟨n+1,by rw [zpow_add,zpow_one,mul_smul]⟩

/-- Packing and a genuinely free endpoint prevent distinct cosets from crossing the periodic trace. -/
theorem cyclic_connector_intersection_forces_zpower {G X : Type*} [Group G] [MulAction G X]
    (g h : G) {D C : Set X} {w : X}
    (hpacking : ∀ (a b : G) (x y : X), x ∈ D → y ∈ D → a • x = b • y → a = b)
    (hwavoid : ∀ a : G, a • w ∉ D)
    (hwfree : ∀ a : G, a • w = w → a = 1)
    (hC : C ⊆ D ∪ {w,g • w})
    (hne : ((⋃ n : ℤ, (g^n • ·) '' C) ∩ (h • ·) '' (⋃ n : ℤ, (g^n • ·) '' C)).Nonempty) :
    h ∈ Subgroup.zpowers g := by
  obtain ⟨z,hz,y,hy,hyz⟩ := hne
  change h • y = z at hyz
  rcases cyclic_connector_point_cases g hC hz with ⟨n,x,hx,hxz⟩ | ⟨n,hxz⟩ <;>
    rcases cyclic_connector_point_cases g hC hy with ⟨m,v,hv,hvy⟩ | ⟨m,hvy⟩
  · have he : g^n = h*g^m := hpacking _ _ x v hx hv (by rw [mul_smul,hvy,hyz,hxz])
    have hh : h = g^(n-m) := by rw [zpow_sub,he];group
    rw [hh]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  · have he : ((g^n)⁻¹*h*g^m) • w = x := by
      rw [mul_smul,mul_smul,hvy,hyz,←hxz,inv_smul_smul]
    exact (hwavoid _ (he ▸ hx)).elim
  · have he : ((h*g^m)⁻¹*g^n) • w = v := by
      calc
        _ = (h*g^m)⁻¹ • (g^n • w) := mul_smul _ _ _
        _ = (h*g^m)⁻¹ • ((h*g^m) • v) := by rw [mul_smul,hvy,hyz,hxz]
        _ = v := inv_smul_smul _ _
    exact (hwavoid _ (he ▸ hv)).elim
  · have he : ((g^n)⁻¹*h*g^m) • w = w := by
      rw [mul_smul,mul_smul,hvy,hyz,←hxz,inv_smul_smul]
    have hid := hwfree _ he
    have hh : h = g^(n-m) := by rw [zpow_sub];calc h = g^n*((g^n)⁻¹*h*g^m)*(g^m)⁻¹ := by group
                                                _ = g^n*(g^m)⁻¹ := by rw [hid];group
    rw [hh]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _


/-- Actual open fundamental tiles have unique group labels when interior points are identified. -/
theorem IsFuchsianFundamentalDomain.interior_tile_labels_unique
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsFuchsianFundamentalDomain P D)
    (a b : H) {x y : P.domain.carrier} (hx : x ∈ D) (hy : y ∈ D)
    (he : a • x = b • y) : a = b := by
  by_contra hne
  have hn : b⁻¹*a ≠ 1 := by intro h;apply hne;exact (inv_mul_eq_one.mp h).symm
  have hxy : (b⁻¹*a) • x = y := by rw [mul_smul,he,inv_smul_smul]
  exact Set.disjoint_left.mp (hD.disjoint_image hn) ⟨x,hx,hxy⟩ hy

/-- The orbit of a genuine fundamental-domain boundary point never enters its open interior. -/
theorem IsFuchsianFundamentalDomain.boundary_orbit_avoids_interior
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsFuchsianFundamentalDomain P D)
    {w : P.domain.carrier} (hw : w ∈ frontier D) (a : H) : a • w ∉ D := by
  have ho := ((isFuchsianFundamentalDomain_iff P D).mp hD).1
  have hwc := frontier_subset_closure hw
  have hwn : w ∉ D := by simpa only [frontier,ho.interior_eq,mem_sdiff] using hw |>.2
  intro haw
  by_cases ha : a = 1
  · exact hwn (by simpa only [ha,one_smul] using haw)
  · exact Set.disjoint_left.mp (hD.disjoint_image_closure (inv_ne_one.mpr ha))
      ⟨a • w,haw,inv_smul_smul a w⟩ hwc

/-- A hyperbolic side-pairing element forces all stabilizers along its side interior to be trivial. -/
theorem IsConvexFuchsianPolygon.hyperbolic_side_interior_free
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (s : FuchsianPolygonSides P D)
    (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (fuchsianSideElement hD s).val)
    {w : P.domain.carrier} (hw : w ∈ s.val) (hi : IsFuchsianPolygonSideInterior P D w)
    (a : H) (ha : a • w = w) : a = 1 := by
  by_contra hn
  have he := hD.side_interior_fixing_eq_pairing s hw hi a hn ha
  have hfix : (fuchsianSideElement hD s).val.val w.val = w.val := by
    have h := congrArg Subtype.val ha
    rw [he] at h
    exact h
  have hfront := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_fixed_mem_disc_frontier _ hg _root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc
    (P.image_eq _) hfix
  have hn : w.val ∉ interior _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := hfront.2
  exact hn (by rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc.isOpen.interior_eq];exact w.property)

/-- The genuine fundamental polygon supplies every packing hypothesis in the periodic-connector lemma. -/
theorem IsConvexFuchsianPolygon.hyperbolic_side_connector_coset_packing
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (s : FuchsianPolygonSides P D)
    (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (fuchsianSideElement hD s).val)
    {w : P.domain.carrier} (hw : w ∈ s.val) (hi : IsFuchsianPolygonSideInterior P D w)
    {C : Set P.domain.carrier} (hC : C ⊆ D ∪ {w,(fuchsianSideElement hD s)⁻¹ • w})
    (h : H)
    (hne : ((⋃ n : ℤ, ((fuchsianSideElement hD s)⁻¹^n • ·) '' C) ∩
      (h • ·) '' (⋃ n : ℤ, ((fuchsianSideElement hD s)⁻¹^n • ·) '' C)).Nonempty) :
    h ∈ Subgroup.zpowers (fuchsianSideElement hD s) := by
  have hwf := (hD.side_interior_iff_boundary_nonvertex w).mp hi |>.1
  simpa only [Subgroup.zpowers_inv] using cyclic_connector_intersection_forces_zpower (fuchsianSideElement hD s)⁻¹ h
    (fun a b x y hx hy he => hD.locallyFinite.fundamental.interior_tile_labels_unique a b hx hy he)
    (hD.locallyFinite.fundamental.boundary_orbit_avoids_interior hwf)
    (hD.hyperbolic_side_interior_free s hg hw hi) hC hne


/-- Every actual positive-length side has a genuine relative-interior point. -/
theorem IsFuchsianPolygonSide.exists_relative_interior
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D S : Set P.domain.carrier} (hS : IsFuchsianPolygonSide P D S) :
    ∃ w ∈ S, IsFuchsianPolygonSideInterior P D w := by
  obtain ⟨a,ha,b,hb,hab⟩ := hS.2.2
  have habf := P.finiteCoordinate.injective.ne hab
  obtain ⟨w,hw,_huniq⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_discMidpoint habf
  obtain ⟨x,hx,hxw⟩ := hS.2.1.1 _ (mem_image_of_mem P.finiteCoordinate ha)
    _ (mem_image_of_mem P.finiteCoordinate hb) hw.1
  refine ⟨x,hx,S,hS,a,ha,b,hb,hab,?_⟩
  have hwn := discMidpoint_image_isometry (discOriginNormalizer_isometry (P.finiteCoordinate x)) habf hw
  have habn := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate
    x)).injective.ne habf
  have ho := discMidpoint_klein_openSegment habn hwn
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate x) (P.finiteCoordinate x)) ∈
    openSegment ℝ
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate x)
        (P.finiteCoordinate a)))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate x)
        (P.finiteCoordinate b)))
  simpa only [hxw] using ho

/-- The original convex polygon itself supplies a free compact connector whose full periodic trace has no intersections with different cyclic cosets. -/
theorem IsConvexFuchsianPolygon.hyperbolic_side_compact_connector
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (s : FuchsianPolygonSides P D)
    (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (fuchsianSideElement hD s).val) :
    ∃ w ∈ s.val, ∃ C : Set P.domain.carrier,
      IsCompact C ∧ IsPreconnected C ∧ w ∈ C ∧ (fuchsianSideElement hD s)⁻¹ • w ∈ C ∧
      C ⊆ D ∪ {w,(fuchsianSideElement hD s)⁻¹ • w} ∧
      (∀ a : H, a • w = w → a = 1) ∧
      ∀ h : H, h ∉ Subgroup.zpowers (fuchsianSideElement hD s) →
        Disjoint (⋃ n : ℤ, ((fuchsianSideElement hD s)⁻¹^n • ·) '' C)
          ((h • ·) '' (⋃ n : ℤ, ((fuchsianSideElement hD s)⁻¹^n • ·) '' C)) := by
  obtain ⟨w,hw,hi⟩ := s.property.exists_relative_interior
  obtain ⟨C,hCc,hCp,hwC,hgwC,hCsub⟩ := hD.side_connector s hw
  refine ⟨w,hw,C,hCc,hCp,hwC,hgwC,hCsub,hD.hyperbolic_side_interior_free s hg hw hi,?_⟩
  intro h hh
  rw [Set.disjoint_iff_inter_eq_empty,←Set.not_nonempty_iff_eq_empty]
  exact fun hne => hh (hD.hyperbolic_side_connector_coset_packing s hg hw hi hCsub h hne)

end LowDimensionalTopology.Geometry.Fuchsian
