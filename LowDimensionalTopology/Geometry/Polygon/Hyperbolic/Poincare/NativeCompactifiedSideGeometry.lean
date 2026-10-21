module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Polygon.Development.IdealPolygonPoincareData
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.NativeGeodesicPolygonGeometry
public import LowDimensionalTopology.Geometry.Polygon.Hyperbolic.Poincare.JordanNativePolygonGeometry
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Polygon
open LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- Every true native portion of a compactified side lies on its actual supporting line. -/
theorem nativeCompactifiedSide_subset_discLine (p q : 𝕔𝔻) (hpq : p≠q)
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (hp : p∈L.closedCarrier) (hq : q∈L.closedCarrier) :
    nativeCompactifiedSide p q⊆L.toHalfPlane.carrier := by
  intro z hz
  have hzArc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)∈L.closedArcHull p q := by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment_eq_arcHull L p q hpq hp hq]
    exact hz
  have hzL : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)∈L.closedCarrier :=
    hzArc L.closedCarrier L.closedCarrier_isPreconnected (Subset.refl _) hp hq
  have hc := (L.closedCarrier_mem_interior_iff (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
    z)).mp hzL
  have hh := (L.mem_carrier (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)).mp hc
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using hh

/-- Away from its actual original endpoints, a genuine compactified side has exactly
its full native supporting-line germ, including sides with two ideal endpoints. -/
theorem nativeCompactifiedSide_line_germ (p q : 𝕔𝔻) (hpq : p≠q)
    (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine) (hp : p∈L.closedCarrier) (hq : q∈L.closedCarrier)
    (x : ℍ) (hx : x∈nativeCompactifiedSide p q)
    (hxp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)≠p)
    (hxq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)≠q) :
    ∀ᶠy in 𝓝 x,y∈nativeCompactifiedSide p q ↔y∈L.toHalfPlane.carrier := by
  have hseg : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x∈segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q) := by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x),hx,rfl⟩
  have hnep : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x := by
    intro he
    exact hxp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective he.symm)
  have hneq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x := by
    intro he
    exact hxq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective he.symm)
  have hOpen := mem_openSegment_of_ne_left_right hnep hneq hseg
  have hG := polygonComplex_segment_line_germ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hpq) hOpen
  have hNear := _root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.continuous.continuousAt.eventually hG
  let N := L.toHalfPlane
  have hm : N.incenterNormal≠0 := N.incenterNormal_ne_zero
  have hleft : inner ℝ N.incenterNormal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    p)=N.incenterOffset :=
    (L.incenter_closed_affine_eq_zero_iff p).mpr hp
  have hright : inner ℝ N.incenterNormal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    q)=N.incenterOffset :=
    (L.incenter_closed_affine_eq_zero_iff q).mpr hq
  filter_upwards [hNear] with y hy
  have hs : y∈nativeCompactifiedSide p q ↔
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate y∈segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q) := by
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image).symm
  rw [hs,hy,_root_.LowDimensionalTopology.Geometry.Fuchsian.polygonLineEquation_iff_support
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hpq) hm hleft hright]
  rw [←N.incenter_affine_eq_zero_iff,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hKleinAffine,sub_eq_zero]



/-- A genuinely locally finite union of finite endpoint sets is discrete; no finiteness
of the side index set is required. -/
theorem locallyFinite_finite_union_isDiscrete {X : Type*} [TopologicalSpace X] [T1Space X]
    {ι : Type*} {F : ι→Set X} (hLF : LocallyFinite F) (hf : ∀i,(F i).Finite) :
    IsDiscrete (⋃i,F i) := by
  apply isDiscrete_iff_nhdsWithin.mpr
  intro x hx
  apply le_antisymm
  · rw [hLF.nhdsWithin_iUnion]
    apply iSup_le
    intro i
    by_cases hi : x∈F i
    · rw [(hf i).isDiscrete.nhdsWithin x hi]
    · have hbot : 𝓝[F i] x=⊥ := by
        apply notMem_closure_iff_nhdsWithin_eq_bot.mp
        rwa [(hf i).isClosed.closure_eq]
      rw [hbot]
      exact bot_le
  · exact pure_le_nhdsWithin hx

/-- Literal original geodesic side intervals and their genuine finite-or-ideal endpoints.
These data contain no local charts, tessellation, group or regular-open assumptions. -/
structure NativeGeodesicSideIntervals (P : PoincarePolygon ℍ) where
  startPoint : P.Side→𝕔𝔻
  endPoint : P.Side→𝕔𝔻
  endpoint_ne : ∀s,startPoint s≠endPoint s
  side_eq : ∀s,s.val=nativeCompactifiedSide (startPoint s) (endPoint s)
  locallyFinite : LocallyFinite (fun s : P.Side=>s.val)
  side_intersection : ∀s t : P.Side,s≠t →∀x∈s.val,x∈t.val →
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)∈({startPoint s,endPoint s} : Set 𝕔𝔻)

def NativeGeodesicSideIntervals.endpoints {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) (s : P.Side) : Set ℍ :=
  (fun x : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)) ⁻¹' {D.startPoint s,D.endPoint s}

def NativeGeodesicSideIntervals.vertices {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) : Set ℍ := ⋃s,D.endpoints s

theorem NativeGeodesicSideIntervals.endpoints_finite {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) (s : P.Side) : (D.endpoints s).Finite :=
  ((Set.finite_singleton (D.endPoint s)).insert (D.startPoint s)).preimage
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective.comp
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective).injOn

theorem NativeGeodesicSideIntervals.endpoints_subset_side {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) (s : P.Side) : D.endpoints s⊆s.val := by
  intro x hx
  rw [D.side_eq s]
  simp only [NativeGeodesicSideIntervals.endpoints,mem_preimage,mem_insert_iff,mem_singleton_iff] at hx
  rcases hx with hx | hx
  · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment _ _
    rw [hx]
    exact closedModelDiscHSegment_left_mem _ _
  · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment _ _
    rw [hx]
    exact closedModelDiscHSegment_right_mem _ _

theorem NativeGeodesicSideIntervals.vertices_discrete {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) : IsDiscrete D.vertices :=
  locallyFinite_finite_union_isDiscrete (D.locallyFinite.subset D.endpoints_subset_side)
    D.endpoints_finite

/-- The true support of a literal original geodesic side is determined by its endpoints. -/
def NativeGeodesicSideIntervals.support {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) (s : P.Side) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_discLine_closedCarrier (D.startPoint s) (D.endPoint s)
    (D.endpoint_ne s)).choose

theorem NativeGeodesicSideIntervals.support_endpoints {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) (s : P.Side) :
    D.startPoint s∈(D.support s).closedCarrier ∧D.endPoint s∈(D.support s).closedCarrier :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.existsUnique_discLine_closedCarrier (D.startPoint s) (D.endPoint s)
    (D.endpoint_ne s)).choose_spec.1

/-- The full native side geometry is proved from literal original intervals and endpoints,
including infinitely many locally finite sides and arbitrary ideal endpoint status. -/
def NativeGeodesicSideIntervals.side_geometry {P : PoincarePolygon ℍ}
    (D : NativeGeodesicSideIntervals P) : NativeGeodesicSideData P D.vertices where
  locallyFinite := D.locallyFinite
  side_closed := by
    intro s
    rw [D.side_eq s]
    exact nativeCompactifiedSide_isClosed _ _
  vertex_discrete := D.vertices_discrete
  line s := (D.support s).toHalfPlane
  side_subset_line := by
    intro s
    rw [D.side_eq s]
    exact nativeCompactifiedSide_subset_discLine _ _ (D.endpoint_ne s) _
      (D.support_endpoints s).1 (D.support_endpoints s).2
  side_two_points := by
    intro s
    rw [D.side_eq s]
    exact nativeCompactifiedSide_nontrivial _ _ (D.endpoint_ne s)
  side_meet_vertex := by
    intro s t hst x hx ht
    exact mem_iUnion.mpr ⟨s,D.side_intersection s t hst x hx ht⟩
  side_interval := by
    intro s x hx hv
    have hs : x∈nativeCompactifiedSide (D.startPoint s) (D.endPoint s) := D.side_eq s ▸ hx
    have hxp : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)≠D.startPoint s := by
      intro he
      exact hv (mem_iUnion.mpr ⟨s,Or.inl he⟩)
    have hxq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)≠D.endPoint s := by
      intro he
      exact hv (mem_iUnion.mpr ⟨s,Or.inr he⟩)
    rw [D.side_eq s]
    exact nativeCompactifiedSide_line_germ _ _ (D.endpoint_ne s) _
      (D.support_endpoints s).1 (D.support_endpoints s).2 x hs hxp hxq

end LowDimensionalTopology.Geometry.Polygon
