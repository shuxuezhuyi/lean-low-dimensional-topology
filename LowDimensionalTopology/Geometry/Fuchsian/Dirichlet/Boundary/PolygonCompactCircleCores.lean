module
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.ConvexRadial
public import LowDimensionalTopology.Geometry.Fuchsian.GeometricFiniteness.FinitelyGeneratedCore
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.GenericDirichletCenters
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import Mathlib.Geometry.Euclidean.Sphere.SecondInter
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Data.Set.Finite.Powerset
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped Pointwise UpperHalfPlane OnePoint RealInnerProductSpace Affine
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
local instance compactCoreSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance compactCoreSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- The literal compact core cut from the genuine closed polygon by an actual hyperbolic ball. -/
def fuchsianClosedPolygonCore {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (D : Set P.domain.carrier) (w : P.domain.carrier) (R : ℝ) : Set P.domain.carrier :=
  closure D ∩ {z | P.hyperbolicDist w z ≤ R}

/-- Every genuine closed-ball polygon core based in the polygon is compact and connected. -/
theorem fuchsian_closed_polygon_core_compact_connected
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w : P.domain.carrier) (hw : w ∈ D)
    (R : ℝ) (hR : 0 ≤ R) :
    IsCompact (fuchsianClosedPolygonCore P D w R) ∧
      IsConnected (fuchsianClosedPolygonCore P D w R) := by
  let φ := P.halfPlaneCoordinate
  let A : Set ℍ := (φ '' closure D) ∩ Metric.closedBall (φ w) R
  have he : fuchsianClosedPolygonCore P D w R = φ.symm '' A := by
    ext z
    constructor
    · rintro ⟨hz,hzR⟩
      change dist (φ w) (φ z) ≤ R at hzR
      exact ⟨φ z,⟨⟨z,hz,rfl⟩,by simpa only [Metric.mem_closedBall,dist_comm] using hzR⟩,φ.symm_apply_apply z⟩
    · rintro ⟨u,⟨⟨z,hz,hzu⟩,huR⟩,rfl⟩
      rw [←hzu,φ.symm_apply_apply]
      refine ⟨hz,?_⟩
      change dist (φ w) (φ z) ≤ R
      simpa only [Metric.mem_closedBall,hzu,dist_comm] using huR
  have hAc : IsCompact A := (isCompact_closedBall (φ w) R).inter_left
    (φ.isClosedMap _ isClosed_closure)
  have hcD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (φ '' D) := by
    have hh := hD.normalized_hConvex (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    rw [map_one] at hh
    simpa using hh
  have hcCl : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (φ '' closure D) := by rw [φ.image_closure]; exact hcD.closure
  have hcA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex A := fun z hz u hu v hv =>
    ⟨hcCl z hz.1 u hu.1 hv,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_metric_closedBall (φ w) R) z hz.2
      u hu.2 hv⟩
  rw [he]
  refine ⟨hAc.image φ.symm.continuous,?_,hcA.isPreconnected.image φ.symm φ.symm.continuous.continuousOn⟩
  exact ⟨w,φ w,⟨⟨w,subset_closure hw,rfl⟩,by simpa only [Metric.mem_closedBall,dist_self] using hR⟩,
    φ.symm_apply_apply w⟩

/-- For any specified genuine interior center, every sufficiently large actual ball core
has connected whole-group saturation and overlaps a fixed finite actual generating family. -/
theorem finitelyGenerated_cofinal_polygon_ball_cores
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (hFG : H.FG) (w : P.domain.carrier) (hw : w ∈ D) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∃ T : Set H, T.Finite ∧ T ⊆ fuchsianSidePairingElements P D ∧
      Subgroup.closure T = ⊤ ∧ ∀ R : ℝ, R₀ ≤ R →
      IsCompact (fuchsianClosedPolygonCore P D w R) ∧
      IsConnected (fuchsianClosedPolygonCore P D w R) ∧
      IsConnected (⋃ g : H, g • fuchsianClosedPolygonCore P D w R) ∧
      ∀ g ∈ T, (fuchsianClosedPolygonCore P D w R ∩ g • fuchsianClosedPolygonCore P D w R).Nonempty := by
  let : ContinuousConstSMul H P.domain.carrier := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainContinuousConstSMul P.domain
  obtain ⟨K,hKc,_hKconn,hKD,_hwK,_hUK,T,hTf,hTS,hTgen,hover⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.IsConvexFuchsianPolygon.finitelyGenerated_compact_connected_core hD hFG
  have hdist : Continuous (fun z : P.domain.carrier => P.hyperbolicDist w z) := by
    change Continuous (fun z => dist (P.halfPlaneCoordinate w) (P.halfPlaneCoordinate z))
    fun_prop
  obtain ⟨M,hM⟩ := (hKc.image hdist).bddAbove
  let R₀ := max 1 M
  have hR₀ : 0 < R₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨R₀,hR₀,T,hTf,hTS,hTgen,?_⟩
  intro R hR
  have hRpos : 0 < R := hR₀.trans_le hR
  have hsub : K ⊆ fuchsianClosedPolygonCore P D w R := by
    intro z hz
    refine ⟨hKD hz,(hM ⟨z,hz,rfl⟩).trans ?_⟩
    exact (le_max_right _ _).trans hR
  have hcover (g : H) (hg : g ∈ T) :
      (fuchsianClosedPolygonCore P D w R ∩ g • fuchsianClosedPolygonCore P D w R).Nonempty :=
    (hover g hg).mono (inter_subset_inter hsub (Set.image_mono hsub))
  have hc := fuchsian_closed_polygon_core_compact_connected hD w hw R hRpos.le
  exact ⟨hc.1,hc.2,connected_orbit_union_of_generators _ hc.2 T hTgen hcover,hcover⟩

/-- Genuine radii avoiding every actual polygon vertex occur beyond every prescribed bound. -/
theorem exists_polygon_radius_avoiding_vertices {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (D : Set P.domain.carrier) (w : P.domain.carrier) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ < R ∧ ∀ v : P.domain.carrier, IsFuchsianPolygonVertex P D v →
      P.hyperbolicDist w v ≠ R := by
  let B : Set ℝ := (fun v : P.domain.carrier => P.hyperbolicDist w v) ''
    {v | IsFuchsianPolygonVertex P D v}
  have hB : B.Countable := (fuchsianPolygonVertices_countable P D).image _
  obtain ⟨R,hR,hRB⟩ := (hB.dense_compl ℝ).inter_open_nonempty (Ioi R₀) isOpen_Ioi nonempty_Ioi
  refine ⟨R,hR,?_⟩
  intro v hv he
  exact hRB ⟨v,hv,he⟩



/-- A genuine complex circle meets a genuine real affine line in finitely many points. -/
theorem complex_circle_affine_line_inter_finite (c : ℂ) (R : ℝ) (n : ℂ) (t : ℝ) (hn : n ≠ 0) :
    {z : ℂ | ‖z-c‖ = R ∧ inner ℝ n z = t}.Finite := by
  let F : Set ℂ := {z | ‖z-c‖ = R ∧ inner ℝ n z = t}
  rcases F.eq_empty_or_nonempty with he | ⟨p,hp⟩
  · change F.Finite
    rw [he]
    exact finite_empty
  let s : EuclideanGeometry.Sphere ℂ := ⟨c,R⟩
  have hpS : p ∈ s := by
    rw [EuclideanGeometry.mem_sphere]
    change dist p c = R
    simpa only [dist_eq_norm] using hp.1
  apply ((finite_singleton (s.secondInter p (Complex.I*n))).insert p).subset
  intro z hz
  have horth : inner ℝ n (z-p) = 0 := by rw [inner_sub_right,hz.2,hp.2]; ring
  obtain ⟨a,ha⟩ := _root_.LowDimensionalTopology.Geometry.Euclidean.complex_orthogonal_eq_real_smul n (z-p) hn horth
  have hline : z ∈ AffineSubspace.mk' p (ℝ ∙ (Complex.I*n)) := by
    rw [AffineSubspace.mem_mk',Submodule.mem_span_singleton]
    exact ⟨a,ha.symm⟩
  have hzS : z ∈ s := by
    rw [EuclideanGeometry.mem_sphere]
    change dist z c = R
    simpa only [dist_eq_norm] using hz.1
  have hchoice := (EuclideanGeometry.Sphere.eq_or_eq_secondInter_of_mem_mk'_span_singleton_iff_mem hpS hline).mpr hzS
  simpa only [mem_insert_iff,mem_singleton_iff] using hchoice

/-- Two genuine finite circles with distinct actual centers have finite intersection. -/
theorem complex_circles_distinct_centers_inter_finite (c d : ℂ) (R S : ℝ) (hcd : c ≠ d) :
    {z : ℂ | ‖z-c‖ = R ∧ ‖z-d‖ = S}.Finite := by
  apply (complex_circle_affine_line_inter_finite c R (d-c)
    ((R^2-S^2-‖c‖^2+‖d‖^2)/2) (sub_ne_zero.mpr hcd.symm)).subset
  intro z hz
  refine ⟨hz.1,?_⟩
  have h1 := norm_sub_sq_real z c
  have h2 := norm_sub_sq_real z d
  rw [hz.1] at h1
  rw [hz.2] at h2
  rw [inner_sub_left,real_inner_comm z d,real_inner_comm z c]
  nlinarith

/-- Every genuine native hyperbolic circle has finite intersection with every actual native geodesic. -/
theorem halfPlaneLine_sphere_inter_finite (L : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (w :
  ℍ) (R : ℝ) :
    (L.carrier ∩ Metric.sphere w R).Finite := by
  cases L with
  | vertical c =>
    apply ((complex_circle_affine_line_inter_finite (w.center R) (w.im*Real.sinh R) 1 c one_ne_zero).preimage
      UpperHalfPlane.coe_injective.injOn).subset
    intro z hz
    refine ⟨?_,?_⟩
    · have hh := UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.mp (Metric.mem_sphere.mp hz.2)
      simpa only [dist_eq_norm] using hh
    · have hzL : z.re = c := hz.1
      simpa only [Complex.inner,map_one,mul_one,UpperHalfPlane.coe_re] using hzL
  | circle c r hr =>
    have hcenter : w.center R ≠ (c : ℂ) := by
      intro he
      have hh := congrArg Complex.im he
      rw [UpperHalfPlane.coe_im,UpperHalfPlane.center_im,Complex.ofReal_im] at hh
      exact (mul_pos w.im_pos (Real.cosh_pos R)).ne' hh
    apply ((complex_circles_distinct_centers_inter_finite (w.center R) c (w.im*Real.sinh R) r hcenter).preimage
      UpperHalfPlane.coe_injective.injOn).subset
    intro z hz
    refine ⟨?_,hz.1⟩
    have hh := UpperHalfPlane.dist_eq_iff_dist_coe_center_eq.mp (Metric.mem_sphere.mp hz.2)
    simpa only [dist_eq_norm] using hh


/-- Each genuine original polygon side meets each genuine hyperbolic circle in finitely many actual points. -/
theorem fuchsian_side_hyperbolic_circle_inter_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} {D S : Set P.domain.carrier}
    (hS : IsFuchsianPolygonSide P D S) (w : P.domain.carrier) (R : ℝ) :
    (S ∩ {x | P.hyperbolicDist w x = R}).Finite := by
  obtain ⟨L,hL⟩ := hS.2.1.2
  apply ((halfPlaneLine_sphere_inter_finite L.toHalfPlane (P.halfPlaneCoordinate w) R).preimage
    P.halfPlaneCoordinate.injective.injOn).subset
  intro x hx
  refine ⟨(L.mem_carrier _).mp (hL ⟨x,hx.1,rfl⟩),?_⟩
  rw [Metric.mem_sphere]
  have hh := hx.2
  change dist (P.halfPlaneCoordinate w) (P.halfPlaneCoordinate x) = R at hh
  rwa [dist_comm]

/-- The original convex locally finite polygon boundary meets every genuine hyperbolic
circle in finitely many actual points, without a finite-sidedness assumption. -/
theorem fuchsian_polygon_frontier_hyperbolic_circle_inter_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w : P.domain.carrier) (R : ℝ) :
    (frontier D ∩ {x | P.hyperbolicDist w x = R}).Finite := by
  let C : Set P.domain.carrier := {x | P.hyperbolicDist w x = R}
  have hCeq : C = P.halfPlaneCoordinate.symm '' Metric.sphere (P.halfPlaneCoordinate w) R := by
    ext x
    constructor
    · intro hx
      refine ⟨P.halfPlaneCoordinate x,?_,P.halfPlaneCoordinate.symm_apply_apply x⟩
      rw [Metric.mem_sphere]
      change dist (P.halfPlaneCoordinate w) (P.halfPlaneCoordinate x) = R at hx
      rwa [dist_comm]
    · rintro ⟨u,hu,rfl⟩
      change dist (P.halfPlaneCoordinate w) (P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm u)) = R
      rw [P.halfPlaneCoordinate.apply_symm_apply]
      simpa only [Metric.mem_sphere,dist_comm] using hu
  have hC : IsCompact C := hCeq.symm ▸
    (isCompact_sphere (P.halfPlaneCoordinate w) R).image P.halfPlaneCoordinate.symm.continuous
  have hF := hD.locallyFinite.compact_sides_finite C hC
  have hU := hF.biUnion (fun S hS => fuchsian_side_hyperbolic_circle_inter_finite hS.1 w R)
  apply hU.subset
  rintro x ⟨hxfront,hxC⟩
  obtain ⟨S,hS,hxS⟩ := hD.boundary_mem_side hxfront
  exact mem_iUnion.mpr ⟨S,mem_iUnion.mpr ⟨⟨hS,x,hxS,hxC⟩,hxS,hxC⟩⟩



/-- A real interval with finitely many removed points has a finite cover by actual convex subsets. -/
theorem real_interval_sdiff_finite_convex_cover (a b : ℝ) (B : Set ℝ) (hB : B.Finite) :
    ∃ F : Set (Set ℝ), F.Finite ∧ Icc a b \ B = ⋃ U ∈ F, U ∧
      ∀ U ∈ F, Convex ℝ U := by
  classical
  let C : Set ℝ → Set ℝ := fun A => Icc a b ∩ ⋂ p ∈ B, if p ∈ A then Ioi p else Iio p
  let F := C '' 𝒫 B
  have hC (A : Set ℝ) : Convex ℝ (C A) := by
    apply (convex_Icc a b).inter
    apply convex_iInter₂
    intro p _
    split_ifs
    · exact convex_Ioi p
    · exact convex_Iio p
  refine ⟨F,hB.powerset.image C,?_,?_⟩
  · ext x
    constructor
    · intro hx
      let A := {p ∈ B | p < x}
      have hAB : A ⊆ B := fun _ hp => hp.1
      refine mem_iUnion₂.mpr ⟨C A,⟨A,hAB,rfl⟩,hx.1,?_⟩
      apply mem_iInter₂.mpr
      intro p hp
      split_ifs with hpA
      · exact hpA.2
      · exact lt_of_le_of_ne (le_of_not_gt (fun hpx => hpA ⟨hp,hpx⟩))
          (fun he => hx.2 (he ▸ hp))
    · intro hx
      obtain ⟨U,⟨A,_hAB,rfl⟩,hx⟩ := mem_iUnion₂.mp hx
      refine ⟨hx.1,?_⟩
      intro hxB
      have hh := mem_iInter₂.mp hx.2 x hxB
      split_ifs at hh <;> exact (lt_irrefl _ hh)
  · rintro U ⟨A,_hA,rfl⟩
    exact hC A

/-- Removing finitely many genuine circle points admits a finite cover by actual
continuous images of convex real angle intervals. -/
theorem circle_sdiff_finite_preconnected_cover (B : Set Circle) (hB : B.Finite) :
    ∃ F : Set (Set Circle), F.Finite ∧ Bᶜ = ⋃ U ∈ F, U ∧
      ∀ U ∈ F, IsPreconnected U := by
  classical
  let I : Set ℝ := Ioc (-Real.pi) Real.pi
  have hinj : InjOn Circle.exp I := Circle.exp_injOn_Ioc (by linarith)
  let A : Set ℝ := I ∩ Circle.exp ⁻¹' B
  have hA : A.Finite := hB.of_injOn (f := Circle.exp) (fun _ hx => hx.2) (hinj.mono inter_subset_left)
  let A' := insert (-Real.pi) A
  obtain ⟨E,hEf,hE,hEc⟩ := real_interval_sdiff_finite_convex_cover (-Real.pi) Real.pi A' (hA.insert _)
  let F := (fun U : Set ℝ => Circle.exp '' U) '' E
  refine ⟨F,hEf.image _,?_,?_⟩
  · ext z
    constructor
    · intro hz
      have hzI : Complex.arg (z : ℂ) ∈ I := ⟨Complex.neg_pi_lt_arg _,Complex.arg_le_pi _⟩
      have hzA : Complex.arg (z : ℂ) ∉ A' := by
        rintro (he | ha)
        · exact hzI.1.ne' he
        · exact hz (by simpa only [A,mem_inter_iff,mem_preimage,Circle.exp_arg] using ha.2)
      have hangle : Complex.arg (z : ℂ) ∈ Icc (-Real.pi) Real.pi \ A' :=
        ⟨⟨hzI.1.le,hzI.2⟩,hzA⟩
      rw [hE] at hangle
      obtain ⟨U,hUE,hu⟩ := mem_iUnion₂.mp hangle
      exact mem_iUnion₂.mpr ⟨Circle.exp '' U,⟨U,hUE,rfl⟩,Complex.arg (z : ℂ),hu,Circle.exp_arg z⟩
    · intro hz
      obtain ⟨_,⟨U,hUE,rfl⟩,t,ht,rfl⟩ := mem_iUnion₂.mp hz
      have ht' : t ∈ Icc (-Real.pi) Real.pi \ A' := by rw [hE]; exact mem_iUnion₂.mpr ⟨U,hUE,ht⟩
      intro htB
      have htne : t ≠ -Real.pi := by intro he; exact ht'.2 (Or.inl he)
      exact ht'.2 (Or.inr ⟨⟨lt_of_le_of_ne ht'.1.1 htne.symm,ht'.1.2⟩,htB⟩)
  · rintro _ ⟨U,hUE,rfl⟩
    exact (hEc U hUE).isPreconnected.image Circle.exp Circle.exp.continuous.continuousOn

/-- A genuine circle minus finitely many actual cut points has finitely many actual connected components. -/
theorem circle_finite_connectedComponentIn_compl (B : Set Circle) (hB : B.Finite) :
    ((fun x => connectedComponentIn Bᶜ x) '' Bᶜ).Finite := by
  obtain ⟨F,hF,hcover,hconn⟩ := circle_sdiff_finite_preconnected_cover B hB
  exact _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.finite_connectedComponentIn_image_of_finite_preconnected_cover Bᶜ F hF
    (by rw [hcover])
    (fun U hU x hx => by rw [hcover]; exact mem_iUnion₂.mpr ⟨U,hU,hx⟩) hconn


/-- The affine parametrization of an actual positive complex circle is a genuine homeomorphism. -/
def complexCircleAffineHomeomorph (c : ℂ) (R : ℝ) (hR : 0 < R) :
    Circle ≃ₜ Metric.sphere c R := by
  let e : ℂ ≃ₜ ℂ := (Homeomorph.smulOfNeZero R hR.ne').trans (Homeomorph.addLeft c)
  refine e.subtype (fun z => ?_)
  change z ∈ Metric.sphere (0 : ℂ) 1 ↔ e z ∈ Metric.sphere c R
  simp only [Metric.mem_sphere,dist_eq_norm,sub_zero,e,Homeomorph.trans_apply,
    Homeomorph.smulOfNeZero_apply,Homeomorph.coe_addLeft,add_sub_cancel_left,
    norm_smul,Real.norm_eq_abs,abs_of_pos hR]
  constructor
  · intro hz
    rw [hz,mul_one]
  · intro hz
    apply mul_left_cancel₀ hR.ne'
    simpa only [mul_one] using hz

/-- A genuine positive native hyperbolic metric circle is homeomorphic to the actual circle. -/
def halfPlaneMetricCircleHomeomorph (w : ℍ) (R : ℝ) (hR : 0 < R) :
    Circle ≃ₜ Metric.sphere w R :=
  (complexCircleAffineHomeomorph (w.center R) (w.im*Real.sinh R)
    (mul_pos w.im_pos (Real.sinh_pos_iff.mpr hR))).trans
    ((UpperHalfPlane.isEmbedding_coe.homeomorphImage (Metric.sphere w R)).trans
      (Homeomorph.setCongr (UpperHalfPlane.image_coe_sphere w R))).symm

/-- The actual circle in the original Fuchsian domain carrier has a genuine circle parametrization. -/
def fuchsianMetricCircleHomeomorph {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R : ℝ) (hR : 0 < R) :
    Circle ≃ₜ {x : P.domain.carrier | P.hyperbolicDist w x = R} :=
  (halfPlaneMetricCircleHomeomorph (P.halfPlaneCoordinate w) R hR).trans
    (P.halfPlaneCoordinate.symm.subtype (fun z => by
      change dist z (P.halfPlaneCoordinate w) = R ↔
        dist (P.halfPlaneCoordinate w) (P.halfPlaneCoordinate (P.halfPlaneCoordinate.symm z)) = R
      rw [P.halfPlaneCoordinate.apply_symm_apply,dist_comm]))


/-- A genuinely preconnected set avoiding a frontier stays on the same side as any one of its points. -/
theorem isPreconnected_subset_open_of_avoids_frontier {X : Type*} [TopologicalSpace X]
    {U D : Set X} (hU : IsPreconnected U) (hD : IsOpen D)
    (hfront : Disjoint U (frontier D)) (hUD : (U ∩ D).Nonempty) : U ⊆ D := by
  have hsep : U ⊆ D ∪ (closure D)ᶜ := by
    intro x hx
    by_cases hxD : x ∈ D
    · exact Or.inl hxD
    · apply Or.inr
      intro hxc
      exact disjoint_left.mp hfront hx (by rw [hD.frontier_eq]; exact ⟨hxc,hxD⟩)
  rcases IsPreconnected.subset_or_subset hD isClosed_closure.isOpen_compl
    (disjoint_left.mpr (fun _ hxD hxNot => hxNot (subset_closure hxD))) hsep hU with hsub | hsub
  · exact hsub
  · obtain ⟨x,hxU,hxD⟩ := hUD
    exact (hsub hxU (subset_closure hxD)).elim

/-- The genuine hyperbolic circle away from the original polygon boundary has a finite
cover by actual preconnected subsets of the original carrier. -/
theorem fuchsian_polygon_circle_sdiff_frontier_finite_cover
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w : P.domain.carrier) (R : ℝ) (hR : 0 < R) :
    ∃ F : Set (Set P.domain.carrier), F.Finite ∧
      {x | P.hyperbolicDist w x = R} \ frontier D = ⋃ U ∈ F, U ∧
      ∀ U ∈ F, IsPreconnected U := by
  let e := fuchsianMetricCircleHomeomorph P w R hR
  let f : Circle → P.domain.carrier := fun u => (e u).val
  have hfinj : Function.Injective f := Subtype.val_injective.comp e.injective
  have hcont : Continuous f := continuous_subtype_val.comp e.continuous
  let B := f ⁻¹' frontier D
  have hB : B.Finite := by
    apply (fuchsian_polygon_frontier_hyperbolic_circle_inter_finite hD w R).of_injOn
      (f := f) ?_ hfinj.injOn
    intro u hu
    exact ⟨hu,(e u).property⟩
  obtain ⟨E,hE,hEc,hEp⟩ := circle_sdiff_finite_preconnected_cover B hB
  let F := (fun U => f '' U) '' E
  refine ⟨F,hE.image _,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨hxR,hxf⟩
      let u := e.symm ⟨x,hxR⟩
      have he : f u = x := congrArg Subtype.val (e.apply_symm_apply ⟨x,hxR⟩)
      have hu : u ∈ Bᶜ := by change f u ∉ frontier D; rwa [he]
      rw [hEc] at hu
      obtain ⟨U,hUE,huU⟩ := mem_iUnion₂.mp hu
      exact mem_iUnion₂.mpr ⟨f '' U,⟨U,hUE,rfl⟩,u,huU,he⟩
    · intro hx
      obtain ⟨_,⟨U,hUE,rfl⟩,u,hu,rfl⟩ := mem_iUnion₂.mp hx
      refine ⟨(e u).property,?_⟩
      have huB : u ∈ Bᶜ := by rw [hEc]; exact mem_iUnion₂.mpr ⟨U,hUE,hu⟩
      exact huB
  · rintro _ ⟨U,hUE,rfl⟩
    exact (hEp U hUE).image f hcont.continuousOn

/-- Intersecting a genuine hyperbolic circle with the actual open convex locally finite
polygon gives finitely many genuine connected components, without assuming finitely many sides. -/
theorem fuchsian_polygon_circle_inter_finite_components
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w : P.domain.carrier) (R : ℝ) (hR : 0 < R) :
    ((fun x => connectedComponentIn (D ∩ {x | P.hyperbolicDist w x = R}) x) ''
      (D ∩ {x | P.hyperbolicDist w x = R})).Finite := by
  let C : Set P.domain.carrier := {x | P.hyperbolicDist w x = R}
  obtain ⟨F,hF,hcover,hpre⟩ := fuchsian_polygon_circle_sdiff_frontier_finite_cover hD w R hR
  let E : Set (Set P.domain.carrier) := {U ∈ F | U ⊆ D}
  have hEc : D ∩ C = ⋃ U ∈ E, U := by
    ext x
    constructor
    · rintro ⟨hxD,hxC⟩
      have hxf : x ∉ frontier D := fun hxF =>
        (disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hD.locallyFinite.fundamental.isOpen)) hxF hxD
      have hx : x ∈ C \ frontier D := ⟨hxC,hxf⟩
      rw [hcover] at hx
      obtain ⟨U,hUF,hxU⟩ := mem_iUnion₂.mp hx
      have hUsub : U ⊆ D := isPreconnected_subset_open_of_avoids_frontier (hpre U hUF)
        hD.locallyFinite.fundamental.isOpen
        (disjoint_left.mpr (fun y hy hyf => by
          have hy' : y ∈ C \ frontier D := by rw [hcover]; exact mem_iUnion₂.mpr ⟨U,hUF,hy⟩
          exact hy'.2 hyf)) ⟨x,hxU,hxD⟩
      exact mem_iUnion₂.mpr ⟨U,⟨hUF,hUsub⟩,hxU⟩
    · intro hx
      obtain ⟨U,⟨hUF,hUD⟩,hxU⟩ := mem_iUnion₂.mp hx
      have hx' : x ∈ C \ frontier D := by rw [hcover]; exact mem_iUnion₂.mpr ⟨U,hUF,hxU⟩
      exact ⟨hUD hxU,hx'.1⟩
  exact _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.finite_connectedComponentIn_image_of_finite_preconnected_cover (D ∩ C) E
    (hF.subset (fun _ hU => hU.1)) (by rw [hEc])
    (fun U hU x hx => by rw [hEc]; exact mem_iUnion₂.mpr ⟨U,hU,hx⟩)
    (fun U hU => hpre U hU.1)

end LowDimensionalTopology.Geometry.Fuchsian
