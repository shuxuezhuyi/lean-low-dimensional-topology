module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.Germs
public import LowDimensionalTopology.Geometry.Polygon.Development.FinitePolygonPoincareData
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSidePairing
public import LowDimensionalTopology.Geometry.Polygon.Angle.PolygonBoundaryConvexity
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter InnerProductGeometry
open scoped Complex.UnitDisc UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces

/-- The actual straight-line boundary equation equals any nonzero supporting affine zero equation
through its two original distinct endpoints. -/
theorem polygonLineEquation_iff_support {a b m : ℂ} {t : ℝ}
    (hab : a≠b) (hm : m≠0) (ha : inner ℝ m a=t) (hb : inner ℝ m b=t) (y : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Polygon.polygonComplexLineEquation a b y=0 ↔ inner ℝ m y=t := by
  let f:=_root_.LowDimensionalTopology.Geometry.Polygon.polygonComplexLineEquation a b
  let k:=_root_.LowDimensionalTopology.Geometry.Polygon.complexLinearFunctionalNormal f.linear
  have hrepr (x : ℂ) : f x=inner ℝ k x+f 0 := by
    dsimp only [k]
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.complexLinearFunctionalNormal_inner]
    exact congrFun f.decomp x
  have hfa : f a=0 := by simp [f,_root_.LowDimensionalTopology.Geometry.Polygon.polygonComplexLineEquation_apply]
  have hfb : f b=0 := by
    simp only [f, _root_.LowDimensionalTopology.Geometry.Polygon.polygonComplexLineEquation_apply,
      div_self (sub_ne_zero.mpr hab.symm)]
    rfl
  have hfu : f (a+Complex.I*(b-a))=1 := by
    rw [show f=_root_.LowDimensionalTopology.Geometry.Polygon.polygonComplexLineEquation a b from rfl,
      _root_.LowDimensionalTopology.Geometry.Polygon.polygonComplexLineEquation_apply]
    have he : (a+Complex.I*(b-a)-a)/(b-a)=Complex.I := by
      field_simp [sub_ne_zero.mpr hab.symm]
      ring
    rw [he]
    rfl
  have hk : k≠0 := by
    intro he
    have h1:=hrepr a
    have h2:=hrepr (a+Complex.I*(b-a))
    rw [he,inner_zero_left,zero_add,hfa] at h1
    rw [he,inner_zero_left,zero_add,hfu] at h2
    linarith
  have hka : inner ℝ k a= -f 0 := by linarith only [hrepr a,hfa]
  have hkb : inner ℝ k b= -f 0 := by linarith only [hrepr b,hfb]
  have he : f y=0 ↔ inner ℝ k y= -f 0 := by rw [hrepr];constructor <;> intro h <;> linarith
  exact he.trans (_root_.LowDimensionalTopology.Geometry.Euclidean.complex_affine_equations_iff_of_two_points hk hm hab hka hkb ha hb)

/-- A nonzero original real inner-product functional is open and its strict supporting cut
has exactly the corresponding weak closed half-plane as its true closure. -/
theorem complex_support_cut_closure {m : ℂ} (hm : m≠0) (t : ℝ) :
    closure {y : ℂ|inner ℝ m y<t}={y : ℂ|inner ℝ m y≤t} := by
  let f : ℂ→L[ℝ]ℝ:=innerSL ℝ m
  have hs : Function.Surjective f := by
    intro r
    refine ⟨(r/‖m‖^2) • m,?_⟩
    change inner ℝ m ((r/‖m‖^2) • m)=r
    rw [inner_smul_right,real_inner_self_eq_norm_sq]
    exact div_mul_cancel₀ r (pow_ne_zero 2 (norm_ne_zero_iff.mpr hm))
  have he:=f.isOpenMap hs |>.preimage_closure_eq_closure_preimage f.continuous (Iio t)
  rw [closure_Iio] at he
  exact he.symm

/-- An open set bounded by a nonzero supporting functional lies strictly on its open side. -/
theorem complex_open_support_strict {I : Set ℂ} {m : ℂ} {t : ℝ}
    (hm : m≠0) (hI : IsOpen I) (hbound : ∀y∈I,inner ℝ m y≤t) :
    ∀y∈I,inner ℝ m y<t := by
  let f : ℂ→L[ℝ]ℝ:=innerSL ℝ m
  have hs : Function.Surjective f := by
    intro r
    refine ⟨(r/‖m‖^2) • m,?_⟩
    change inner ℝ m ((r/‖m‖^2) • m)=r
    rw [inner_smul_right,real_inner_self_eq_norm_sq]
    exact div_mul_cancel₀ r (pow_ne_zero 2 (norm_ne_zero_iff.mpr hm))
  intro y hy
  have hsub : f '' I⊆Iic t := by rintro _ ⟨z,hz,rfl⟩;exact hbound z hz
  have hh:=interior_maximal hsub ((f.isOpenMap hs) I hI) (mem_image_of_mem f hy)
  have hh' : f y<t := by simpa only [interior_Iic,mem_Iio] using hh
  exact hh'

/-- For two genuine Jordan regions, an actual supporting line boundary germ determines the
original inside as its true open half-plane locally. No local inside choice is assumed. -/
theorem complex_jordan_supported_line_germ {I O B : Set ℂ} {x m : ℂ} {t : ℝ}
    (hm : m≠0) (hI : IsOpen I) (hO : IsOpen O) (hd : Disjoint I O) (hu : I∪O=Bᶜ)
    (hxI : x∈frontier I) (hbound : ∀y∈I,inner ℝ m y≤t)
    (he : ∀ᶠy in 𝓝 x,y∈B ↔ inner ℝ m y=t) :
    ∀ᶠy in 𝓝 x,y∈I ↔ inner ℝ m y<t := by
  have hstrict:=complex_open_support_strict hm hI hbound
  obtain ⟨r,hr,hBall⟩:=Metric.mem_nhds_iff.mp he
  let C : Set ℂ:=Metric.ball x r∩{y : ℂ|inner ℝ m y<t}
  have hC : IsPreconnected C :=
    ((convex_ball x r).inter ((convex_Iio t).linear_preimage (innerSL ℝ m).toLinearMap)).isPreconnected
  have hsub : C⊆I∪O := by
    intro y hy
    have hh : y∈B ↔ inner ℝ m y=t:=hBall hy.1
    rw [hu,mem_compl_iff,hh]
    exact ne_of_lt hy.2
  have hCI : C⊆I := by
    apply (hC.subset_or_subset hI hO hd hsub).resolve_right
    intro hCO
    obtain ⟨y,hy,hyI⟩:=mem_closure_iff.mp (frontier_subset_closure hxI)
      (Metric.ball x r) Metric.isOpen_ball (Metric.mem_ball_self hr)
    exact Set.disjoint_left.mp hd hyI (hCO ⟨hy,hstrict y hyI⟩)
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  exact ⟨fun hyI=>hstrict y hyI,fun hyF=>hCI ⟨hy,hyF⟩⟩

/-- Original native closed-carrier membership is literal membership in the original Klein body. -/
theorem finitePolygon_carrier_kleinBody_iff {n : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (w : ℍ) :
    w∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ↔ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w∈Q.kleinBody := by
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon_carrier_iff]
  change _↔_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' Q.closedCarrier
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate,
    ←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.mem_set_image.symm

/-- A genuine supported affine-line boundary germ in the original Jordan polygon gives
its actual native closed-half-plane germ, also at collinear marked corners. -/
theorem finitePolygon_native_supported_line_germ
    {n : ℕ}
    (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (x : ℍ)
    (hx : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)∈Q.boundary) {m : ℂ} {t : ℝ}
    (hm : m≠0) (hbound : ∀y∈Q.kleinBody,inner ℝ m y≤t)
    (he : ∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x),
      y∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' Q.boundary ↔ inner ℝ m y=t) :
    ∃r : ℝ,0<r ∧ ∀w : ℍ,dist w x<r →
      (w∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ↔ inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)≤t) := by
  obtain ⟨hI,hO,hd,hu,hFI,_hFO⟩:=Q.klein_jordan_regions
  have hxI : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x∈frontier (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' Q.interior) := by
    rw [hFI, _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate,
      ←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion]
    exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate hx
  have hboundI : ∀y∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' Q.interior,inner ℝ m y≤t := by
    rintro _ ⟨z,hz,rfl⟩
    apply hbound
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion]
    exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (subset_closure (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel hz))
  have hOpen:=complex_jordan_supported_line_germ hm hI hO hd hu hxI hboundI he
  have hClosed:=_root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.angular_closure_germ hOpen
  change ∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x),
    y∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' Q.interior) ↔ y∈closure {y : ℂ|inner ℝ m y<t} at hClosed
  rw [complex_support_cut_closure hm t] at hClosed
  have hbody : closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' Q.interior)=Q.kleinBody :=
    Q.closedKlein_image_closedCarrier.symm
  rw [hbody] at hClosed
  have hNative:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.continuous.continuousAt.eventually hClosed
  have hNative' : ∀ᶠw in 𝓝 x,
      w∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ↔ inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)≤t := by
    filter_upwards [hNative] with w hw
    exact (finitePolygon_carrier_kleinBody_iff Q hf w).trans hw
  exact Metric.eventually_nhds_iff_ball.mp hNative'

/-- A literal original finite vertex has its original actual closed Klein coordinate. -/
theorem finitePolygonVertex_klein_coordinate {n : ℕ} (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices i) := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate,
    ←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_coordinate]

/-- Any original affine equation through both true side endpoints is precisely the actual native h-line. -/
theorem finitePolygon_line_equation_of_two
    {n : ℕ}
    (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (i : Fin n)
    {m : ℂ} {t : ℝ} (hm : ‖m‖=1)
    (hleft : inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices i))=t)
    (hright : inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices (finRotate n i)))=t) (x : ℍ) :
    x∈(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).carrier ↔ inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x)=t := by
  have he:=(Q.geodesicSide i).closedCarrier_iff_equation_of_two _ _
    (Q.vertices_injective.ne (Q.next_ne_self i).symm)
    (Q.geodesicSide_endpoints i).1 (Q.geodesicSide_endpoints i).2 m t hm hleft hright
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x))
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_mem_interior_iff,_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.mem_carrier,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion] at he
  exact he

/-- Relative-interior points of any original convex side have their true supporting half-plane
germ, even when other original corners are straight and supporting lines repeat. -/
theorem finitePolygon_weak_nonvertex_halfPlane_germ
    {n : ℕ}
    (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (hQ : Q.IsConvex)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) {i : Fin n} {x : ℍ}
    (hx : x∈_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q i)
    (hv : x∉range (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf)) :
    ∃(m : ℂ)(t : ℝ),‖m‖=1 ∧
      (∀w : ℍ,w∈(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).carrier ↔ inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)=t) ∧
      ∃r : ℝ,0<r ∧ ∀w : ℍ,dist w x<r →
        (w∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ↔ inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)≤t) := by
  obtain ⟨m,t,hm,hbound,hleft,hright⟩:=Q.exists_support_equation hQ i
  have hm0 : m≠0 := by intro h;rw [h,norm_zero] at hm;norm_num at hm
  have hseg : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x∈segment ℝ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices i))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices (finRotate n i))) := by
    have hx' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x)∈
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (Q.vertices i) (Q.vertices (finRotate n i)):=hx
    have h : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x))∈
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment (Q.vertices i) (Q.vertices (finRotate n i)) :=
      ⟨_,hx',rfl⟩
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKlein_image_closedModelDiscHSegment] at h
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate] using h
  have hne (j : Fin n) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices j)≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x := by
    intro he
    apply hv
    refine ⟨j,?_⟩
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate_injective
    exact (finitePolygonVertex_klein_coordinate Q hf j).trans he
  have hopen:=mem_openSegment_of_ne_left_right (hne i) (hne (finRotate n i)) hseg
  have hB : ∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate x),
      y∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' Q.boundary ↔ inner ℝ m y=t := by
    filter_upwards [Q.klein_boundary_line_germ_edge i hopen] with y hy
    exact hy.trans (polygonLineEquation_iff_support
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (Q.vertices_injective.ne (Q.next_ne_self i).symm))
      hm0 hleft hright y)
  refine ⟨m,t,hm,finitePolygon_line_equation_of_two Q i hm hleft hright,?_⟩
  exact finitePolygon_native_supported_line_germ Q hf x (mem_iUnion.mpr ⟨i,hx⟩) hm0 hbound hB

/-- In a genuine convex polygon, an actual angle-pi corner has one actual supporting mirror. -/
theorem finitePolygon_straight_corner_support
    {n : ℕ}
    (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (hQ : Q.IsConvex)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) (hangle : Q.angle i=Real.pi) :
    (Q.cornerRayPrev i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i))
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_coordinate Q hf i).symm).supportLine=
    (Q.cornerRayNext i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i))
      (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_coordinate Q hf i).symm).supportLine := by
  let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)
  have hz : Q.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_coordinate Q hf i).symm
  by_contra hne
  have hminor:=Q.hasMinorInterior_of_isConvex_proper hQ i z hz hne
  have hθ:=Q.angle_of_minor i z hz hminor
  have hlt:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_lt_pi (Q.cornerRayPrev i z hz).toHalfPlane
    (Q.cornerRayNext i z hz).toHalfPlane ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt.different_supports_iff _ _).mp hne)
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.discInteriorAngleMeasure_eq_halfPlane,←hθ,hangle] at hlt
  exact lt_irrefl _ hlt

/-- A marked straight corner has its genuine original closed supporting half-plane germ;
no deletion or reindexing of the original polygon is needed. -/
theorem finitePolygon_straight_halfPlane_germ
    {n : ℕ}
    (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (hQ : Q.IsConvex)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) (hangle : Q.angle i=Real.pi) :
    _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q ((finRotate n).symm i)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i ∧
    ∃(m : ℂ)(t : ℝ),‖m‖=1 ∧
      (∀w : ℍ,w∈(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).carrier ↔ inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)=t) ∧
      ∃r : ℝ,0<r ∧ ∀w : ℍ,dist w (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)<r →
        (w∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier ↔ inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w)≤t) := by
  let z:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)
  have hz : Q.vertices i=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel z:=(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_coordinate Q hf i).symm
  have hRS:=finitePolygon_straight_corner_support Q hQ hf i hangle
  have hD : Q.geodesicSide ((finRotate n).symm i)=Q.geodesicSide i := by
    rw [←Q.cornerRayPrev_support_geodesicSide i z hz,←Q.cornerRayNext_support_geodesicSide i z hz]
    exact hRS
  have hN : _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q ((finRotate n).symm i)=_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i :=
    congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.toHalfPlane hD
  refine ⟨hN,?_⟩
  obtain ⟨m,t,hm,hbound,hleft,hright⟩:=Q.exists_support_equation hQ i
  have hm0 : m≠0 := by intro h;rw [h,norm_zero] at hm;norm_num at hm
  have hprev : inner ℝ m (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (Q.vertices ((finRotate n).symm i)))=t := by
    rw [←finitePolygonVertex_klein_coordinate Q hf]
    apply (finitePolygon_line_equation_of_two Q i hm hleft hright _).mp
    rw [←hN]
    exact _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_subset_line Q _ (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide_left_mem Q hf _)
  have hB : ∀ᶠy in 𝓝 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i)),
      y∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate '' Q.boundary ↔ inner ℝ m y=t := by
    rw [finitePolygonVertex_klein_coordinate]
    filter_upwards [Q.klein_boundary_straight_germ i z hz hRS] with y hy
    exact hy.trans (polygonLineEquation_iff_support
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_injective.ne (Q.vertices_injective.ne (_root_.LowDimensionalTopology.Geometry.Polygon.centeredPolygonSupport_prev_ne_next Q.three_le i)))
      hm0 hprev hright y)
  refine ⟨m,t,hm,finitePolygon_line_equation_of_two Q i hm hleft hright,?_⟩
  apply finitePolygon_native_supported_line_germ Q hf (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex Q hf i) _ hm0 hbound hB
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonVertex_coordinate]
  exact Q.vertex_mem_boundary i

/-- Points on an actual supporting h-line cannot be in the genuine open convex polygon;
thus all closed-carrier points on that line lie on actual original sides. -/
theorem finitePolygon_support_line_boundary
    {n : ℕ}
    (Q : _root_.LowDimensionalTopology.Geometry.Polygon.DiscPolygon n)
    (hQ : Q.IsConvex)
    (hf : ∀i,‖(Q.vertices i : ℂ)‖<1) (i : Fin n) {w : ℍ}
    (hw : w∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).carrier)
    (hL : w∈(_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Q i).carrier) :
    w∈(_root_.LowDimensionalTopology.Geometry.Polygon.finiteDiscPoincarePolygon Q hf).boundary := by
  apply hw.resolve_left
  intro hI
  obtain ⟨m,t,hm,hbound,hl,hr⟩:=Q.exists_support_equation hQ i
  have hm0 : m≠0 := by intro h;rw [h,norm_zero] at hm;norm_num at hm
  have hboundI : ∀y∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate '' Q.interior,inner ℝ m y≤t := by
    rintro _ ⟨z,hz,rfl⟩
    apply hbound
    rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion]
    exact mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (subset_closure (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel hz))
  have hstrict:=complex_open_support_strict hm0 Q.klein_inside_isOpen hboundI
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneKleinCoordinate w) (mem_image_of_mem _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate hI)
  have he:=(finitePolygon_line_equation_of_two Q i hm hl hr w).mp hL
  exact hstrict.ne he

end LowDimensionalTopology.Geometry.Fuchsian
