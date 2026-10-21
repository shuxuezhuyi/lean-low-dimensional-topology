module
public import LowDimensionalTopology.Geometry.Polygon.Development.FinitePolygonPoincareData
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.ClosedSegmentTransport
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Tactic
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

/-- Actual closed Klein coordinates preserve precisely finite versus ideal status. -/
theorem closedKleinCoordinate_finite_iff (p : 𝕔𝔻) :
    ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p‖<1 ↔‖(p : ℂ)‖<1 := by
  rcases _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDisc_interior_or_ideal p with ⟨z,rfl⟩ | hp
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion]
    exact iff_of_true (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinFormula_mem_disc z) z.norm_lt_one
  · have hk : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p=(p : ℂ) := by
      change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein p : ℂ)=(p : ℂ)
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein_ideal_fixed p hp]
    rw [hk,hp]

/-- The literal native side with arbitrary finite or ideal endpoints in the actual compactified disc. -/
def nativeCompactifiedSide (p q : 𝕔𝔻) : Set ℍ :=
  (fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
    z)) ⁻¹' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q

/-- Every strict interior point of the actual Klein segment is a genuine finite native side point. -/
theorem nativeCompactifiedSide_realizes_openSegment {p q : 𝕔𝔻} (hpq : p≠q) {w : ℂ}
    (hw : w∈openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q)) :
    ∃z∈nativeCompactifiedSide p q,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate z=w := by
  have hwp : ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p‖≤1:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein p).norm_le_one
  have hwq : ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q‖≤1:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedPoincareToKlein q).norm_le_one
  have hwlt : ‖w‖<1:=mem_ball_zero_iff.mp (openSegment_subset_ball_of_ne
    (mem_closedBall_zero_iff.mpr hwp) (mem_closedBall_zero_iff.mpr hwq)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hpq) hw)
  have hwSeg : w∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
    exact openSegment_subset_segment ℝ _ _ hw
  obtain ⟨r,hr,hrw⟩:=hwSeg
  have hrf : ‖(r : ℂ)‖<1:=(closedKleinCoordinate_finite_iff r).mp (hrw.symm ▸ hwlt)
  let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint r hrf
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z,?_,?_⟩
  · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z))∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec]
    exact hr
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscFinitePoint_spec]
    exact hrw

/-- Every actual nondegenerate compactified side has two genuinely distinct native points,
even when one or both original endpoints are ideal. -/
theorem nativeCompactifiedSide_nontrivial (p q : 𝕔𝔻) (hpq : p≠q) :
    (nativeCompactifiedSide p q).Nontrivial := by
  let F : ℝ→ᵃ[ℝ]ℂ:=AffineMap.lineMap (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q)
  have h0 : F (1/3)∈openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q):=
    lineMap_mem_openSegment ℝ _ _ (by norm_num)
  have h1 : F (2/3)∈openSegment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
    p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q):=
    lineMap_mem_openSegment ℝ _ _ (by norm_num)
  obtain ⟨z,hz,hzF⟩:=nativeCompactifiedSide_realizes_openSegment hpq h0
  obtain ⟨w,hw,hwF⟩:=nativeCompactifiedSide_realizes_openSegment hpq h1
  refine ⟨z,hz,w,hw,?_⟩
  intro hzw
  have he : F (1/3)=F (2/3):=hzF.symm.trans ((congrArg
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate hzw).trans hwF)
  have ht:=(AffineMap.lineMap_injective ℝ
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne hpq)) he
  norm_num at ht

/-- The arbitrary finite/ideal side is genuinely closed in the native hyperbolic plane. -/
theorem nativeCompactifiedSide_isClosed (p q : 𝕔𝔻) : IsClosed (nativeCompactifiedSide p q) := by
  let : T2Space 𝕔𝔻:=Complex.UnitClosedDisc.isEmbedding_coe.t2Space
  exact (closedModelDiscHSegment_isCompact p q).isClosed.preimage
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.continuous.comp
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.continuous)

/-- The actual original Jordan polygon with arbitrary finite or ideal vertices as native
Poincare data. Nonempty sides are proved from genuine finite side points, not assumed. -/
def jordanDiscPoincarePolygon {n : ℕ} (Q : DiscPolygon n) : PoincarePolygon ℍ where
  interior:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' Q.interior
  interior_nonempty:=by
    obtain ⟨z,hz⟩:=Q.interior_isConnected.nonempty
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z,by simpa only [mem_preimage,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane] using hz⟩
  sides:=range (finitePolygonSide Q)
  sides_nonempty:=by
    have hn : 0<n:=by have:=Q.three_le;omega
    exact ⟨finitePolygonSide Q ⟨0,hn⟩,mem_range_self _⟩
  side_nonempty:=by
    rintro s ⟨i,rfl⟩
    exact (nativeCompactifiedSide_nontrivial (Q.vertices i) (Q.vertices (finRotate n i))
      (Q.vertices_injective.ne (Q.next_ne_self i).symm)).nonempty
  disjoint:=by
    apply Set.disjoint_left.mpr
    intro z hzI hzB
    obtain ⟨s,⟨i,rfl⟩,hs⟩:=mem_sUnion.mp hzB
    have hb : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)∈Q.complexBoundary:=
      ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z),mem_iUnion.mpr ⟨i,hs⟩,rfl⟩
    exact hzI.1 hb


/-- The actual finite native portion of a nondegenerate compactified geodesic side is
dense in precisely the original finite-or-ideal closed side, including both ideal endpoints. -/
theorem nativeCompactifiedSide_closedModelClosure (p q : 𝕔𝔻) (hpq : p≠q) :
    closure ((fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) '' nativeCompactifiedSide p q)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment p q := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.image_injective
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.isClosedEmbedding_closedKleinCoordinate.closure_image_eq,image_image,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
  change closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate '' nativeCompactifiedSide p
    q)=
    segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate
      p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate q)
  apply subset_antisymm
  · apply closure_minimal
    · rintro w ⟨z,hz,rfl⟩
      rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment]
      exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z),hz,rfl⟩
    · rw [←closure_openSegment]
      exact isClosed_closure
  · rw [←closure_openSegment]
    apply closure_mono
    intro w hw
    obtain ⟨z,hz,hzw⟩:=nativeCompactifiedSide_realizes_openSegment hpq hw
    exact ⟨z,hz,hzw⟩

/-- Literal original finite or ideal polygon sides remain distinct native sets.
Their genuine closed-model closures recover the original endpoint incidences. -/
theorem jordanPolygonSide_injective {n : ℕ} (Q : DiscPolygon n) :
    Function.Injective (finitePolygonSide Q) := by
  intro i j hij
  by_contra hne
  have hcl:=congrArg (fun S : Set ℍ=>closure ((fun z :
    ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) '' S)) hij
  change closure ((fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) ''
      nativeCompactifiedSide (Q.vertices i) (Q.vertices (finRotate n i)))=
    closure ((fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) ''
      nativeCompactifiedSide (Q.vertices j) (Q.vertices (finRotate n j))) at hcl
  rw [nativeCompactifiedSide_closedModelClosure _ _ (Q.vertices_injective.ne (Q.next_ne_self i).symm),
    nativeCompactifiedSide_closedModelClosure _ _ (Q.vertices_injective.ne (Q.next_ne_self j).symm)] at hcl
  have hl : Q.vertices i∈discPolygonEdge Q.vertices j := by
    change Q.vertices i∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (Q.vertices
      j) (Q.vertices (finRotate n j))
    rw [←hcl]
    exact closedModelDiscHSegment_left_mem _ _
  have hr : Q.vertices (finRotate n i)∈discPolygonEdge Q.vertices j := by
    change Q.vertices (finRotate n
      i)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (Q.vertices j) (Q.vertices (finRotate
      n j))
    rw [←hcl]
    exact closedModelDiscHSegment_right_mem _ _
  have hle := (Q.simple_edges i j hne ⟨closedModelDiscHSegment_left_mem _ _,hl⟩).2
  have hre := (Q.simple_edges i j hne ⟨closedModelDiscHSegment_right_mem _ _,hr⟩).2
  simp only [mem_insert_iff,mem_singleton_iff] at hle hre
  have hleI : i=j ∨i=finRotate n j := hle.imp (fun h=>Q.vertices_injective h) (fun h=>Q.vertices_injective h)
  have hreI : finRotate n i=j ∨finRotate n i=finRotate n j := hre.imp (fun h=>Q.vertices_injective h) (fun
    h=>Q.vertices_injective h)
  rcases hleI with he | he
  · exact hne he
  · rcases hreI with he' | he'
    · exact polygonSupport_next_next_ne_self Q.three_le j ((congrArg (finRotate n) he.symm).trans he')
    · exact hne ((finRotate n).injective he')

/-- The original side labels are in genuine bijection with the native original sides,
without excluding ideal vertices. -/
def jordanPolygonSideEquiv {n : ℕ} (Q : DiscPolygon n) : Fin n≃(jordanDiscPoincarePolygon Q).Side :=
  Equiv.ofInjective (finitePolygonSide Q) (jordanPolygonSide_injective Q)

theorem jordanDiscPoincarePolygon_boundary {n : ℕ} (Q : DiscPolygon n)
    :
    (jordanDiscPoincarePolygon Q).boundary=
      (fun z : ℍ=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)) ⁻¹' Q.complexBoundary := by
  ext z
  constructor
  · rintro ⟨s,⟨i,rfl⟩,hz⟩
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z),mem_iUnion.mpr ⟨i,hz⟩,rfl⟩
  · rintro ⟨p,hp,he⟩
    have he' : p=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z) := Subtype.ext he
    subst p
    obtain ⟨i,hi⟩ := mem_iUnion.mp hp
    exact ⟨finitePolygonSide Q i,mem_range_self i,hi⟩

theorem jordanDiscPoincarePolygon_carrier {n : ℕ} (Q : DiscPolygon n)
    :
    (jordanDiscPoincarePolygon Q).carrier=closure (jordanDiscPoincarePolygon Q).interior := by
  let f : ℍ→ℂ:=fun z=>(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z : ℂ)
  have hfc : Continuous f := Complex.UnitDisc.continuous_coe.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.continuous
  have hCo : IsOpenMap ((↑) : 𝔻→ℂ) := by
    change IsOpenMap (Subtype.val : Metric.ball (0 : ℂ) 1→ℂ)
    exact Metric.isOpen_ball.isOpenMap_subtype_val
  have hfo : IsOpenMap f := hCo.comp _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isOpenMap
  calc
    _=(f ⁻¹' Q.complexInterior)∪(f ⁻¹' Q.complexBoundary) := by
      rw [PoincarePolygon.carrier,jordanDiscPoincarePolygon_boundary]
      rfl
    _=f ⁻¹' closure Q.complexInterior := by rw [Q.closure_complexInterior,preimage_union]
    _=closure (f ⁻¹' Q.complexInterior) := hfo.preimage_closure_eq_closure_preimage hfc _
    _=_ := rfl

theorem jordanDiscPoincarePolygon_interior_isOpen {n : ℕ} (Q : DiscPolygon n)
    : IsOpen (jordanDiscPoincarePolygon Q).interior :=
  Q.interior_isOpen.preimage _root_.LowDimensionalTopology.Geometry.Hyperbolic.continuous_halfPlaneToDisc

theorem jordanDiscPoincarePolygon_interior_isConnected {n : ℕ} (Q : DiscPolygon n)
    : IsConnected (jordanDiscPoincarePolygon Q).interior := by
  change IsConnected (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph ⁻¹' Q.interior)
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.isConnected_preimage.mpr Q.interior_isConnected

theorem jordanDiscPoincarePolygon_countableSides {n : ℕ} (Q : DiscPolygon n)
    : (jordanDiscPoincarePolygon Q).sides.Countable :=
  (Set.finite_range _).countable

theorem jordanDiscPoincarePolygon_geodesicSides {n : ℕ} (Q : DiscPolygon n)
    :
    ∀s∈(jordanDiscPoincarePolygon Q).sides,∃L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine,s⊆L.carrier := by
  rintro s ⟨i,rfl⟩
  exact ⟨finitePolygonLine Q i,finitePolygonSide_subset_line Q i⟩


/-- The all-finite specialization is definitionally the previously fixed original data. -/
theorem jordanDiscPoincarePolygon_eq_finite {n : ℕ} (Q : DiscPolygon n)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) : jordanDiscPoincarePolygon Q=finiteDiscPoincarePolygon Q hf := rfl

/-- All original finite-or-ideal sides remain genuinely locally finite and closed in H. -/
theorem jordanDiscPoincarePolygon_locallyFiniteSides {n : ℕ} (Q : DiscPolygon n) :
    LocallyFinite (fun s : (jordanDiscPoincarePolygon Q).Side=>s.val) := by
  let : Finite (jordanDiscPoincarePolygon Q).Side:=Finite.of_equiv (Fin n) (jordanPolygonSideEquiv Q)
  exact locallyFinite_of_finite _

theorem jordanDiscPoincarePolygon_closedSides {n : ℕ} (Q : DiscPolygon n) :
    ∀s : (jordanDiscPoincarePolygon Q).Side,IsClosed s.val := by
  intro s
  obtain ⟨i,rfl⟩:=(jordanPolygonSideEquiv Q).surjective s
  exact finitePolygonSide_isClosed Q i

/-- Only the actual finite original vertices belong to the native geometric vertex set;
no condition is checked at ideal endpoints outside the native hyperbolic plane. -/
def jordanPolygonNativeVertices {n : ℕ} (Q : DiscPolygon n) : Set ℍ :=
  (fun z : ℍ=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)) ⁻¹' range Q.vertices

theorem jordanPolygonNativeVertices_finite {n : ℕ} (Q : DiscPolygon n) :
    (jordanPolygonNativeVertices Q).Finite := by
  exact (Set.finite_range Q.vertices).preimage
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective.comp
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective).injOn

theorem jordanPolygonNativeVertices_isDiscrete {n : ℕ} (Q : DiscPolygon n) :
    IsDiscrete (jordanPolygonNativeVertices Q) := (jordanPolygonNativeVertices_finite Q).isDiscrete

end LowDimensionalTopology.Geometry.Polygon
