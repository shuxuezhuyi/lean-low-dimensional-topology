module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.DirichletKleinCircle
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
local instance embeddedArcSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance embeddedArcSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- Each original open-region component is relatively closed in that region. -/
theorem closure_connectedComponentIn_inter_subset {X : Type*} [TopologicalSpace X]
    {U : Set X} {x : X} (hx : x ∈ U) :
    closure (connectedComponentIn U x) ∩ U ⊆ connectedComponentIn U x := by
  let V := connectedComponentIn U x
  have hs : V ⊆ closure V ∩ U := fun z hz => ⟨subset_closure hz,connectedComponentIn_subset U x hz⟩
  have hp : IsPreconnected (closure V ∩ U) :=
    isPreconnected_connectedComponentIn.subset_closure hs inter_subset_left
  exact hp.subset_connectedComponentIn (hs (mem_connectedComponentIn hx)) inter_subset_right

/-- The actual frontier of an open-region component lies on the original region frontier. -/
theorem frontier_connectedComponentIn_subset_frontier {X : Type*} [TopologicalSpace X]
    [LocallyConnectedSpace X] {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U) :
    frontier (connectedComponentIn U x) ⊆ frontier U := by
  intro z hz
  refine ⟨closure_mono (connectedComponentIn_subset U x) hz.1,?_⟩
  rw [hU.interior_eq]
  intro hzU
  have hzV := closure_connectedComponentIn_inter_subset hx ⟨hz.1,hzU⟩
  exact hz.2 (by rw [(hU.connectedComponentIn).interior_eq]; exact hzV)

/-- Both full-interval endpoint parameters represent the actual omitted circle point. -/
theorem circleArcParam_endpoints (a : Circle) :
    circleArcParam a (-Real.pi) = a ∧ circleArcParam a Real.pi = a := by
  have he : Circle.exp (-Real.pi) = Circle.exp Real.pi :=
    Circle.exp_eq_exp.mpr ⟨-1,by push_cast; ring⟩
  constructor
  · simp only [circleArcParam,he,div_mul_cancel]
  · simp only [circleArcParam,div_mul_cancel]

/-- The actual angular parametrization is injective on the genuine slit interval. -/
theorem circleArcParam_injOn_slit (a : Circle) :
    Set.InjOn (circleArcParam a) (Ioo (-Real.pi) Real.pi) := by
  intro l hl r hr he
  have hh : Circle.exp l = Circle.exp r := mul_left_cancel he
  exact Circle.exp_injOn_Ioc (show Real.pi-(-Real.pi) ≤ 2*Real.pi by ring_nf; exact le_rfl)
    ⟨hl.1,hl.2.le⟩ ⟨hr.1,hr.2.le⟩ hh

/-- A component avoiding an actual exterior neighborhood is a genuine embedded closed
arc, with two distinct actual endpoints on the original region frontier. -/
theorem circle_component_embedded_arc {U : Set Circle} (hU : IsOpen U)
    (a x : Circle) (ha : a ∉ closure U) (hx : x ∈ U) :
    ∃ l r : ℝ, -Real.pi < l ∧ l < r ∧ r < Real.pi ∧
      connectedComponentIn U x = circleArcParam a '' Ioo l r ∧
      closure (connectedComponentIn U x) = circleArcParam a '' Icc l r ∧
      Set.InjOn (circleArcParam a) (Icc l r) ∧
      circleArcParam a l ≠ circleArcParam a r ∧
      circleArcParam a l ∈ frontier U ∧ circleArcParam a r ∈ frontier U := by
  let : LocallyConnectedSpace Circle := circle_locallyConnectedSpace
  let V := connectedComponentIn U x
  have hV : IsConnected V := isConnected_connectedComponentIn_iff.mpr hx
  have hVo : IsOpen V := hU.connectedComponentIn
  have hVa : a ∉ closure V := fun hh => ha (closure_mono (connectedComponentIn_subset U x) hh)
  obtain ⟨l,r,hl,hlr,hr,hparam⟩ := circle_connected_open_eq_actual_arc a hV hVo
    (fun hh => hVa (subset_closure hh))
  have hclosed : closure V = circleArcParam a '' Icc l r := by
    rw [hparam,circleArcParam_closure_image a l r hlr]
  have hl' : -Real.pi < l := lt_of_le_of_ne hl (by
    intro he
    apply hVa
    rw [hclosed]
    exact ⟨l,⟨le_rfl,hlr.le⟩,by rw [←he,(circleArcParam_endpoints a).1]⟩)
  have hr' : r < Real.pi := lt_of_le_of_ne hr (by
    intro he
    apply hVa
    rw [hclosed]
    exact ⟨r,⟨hlr.le,le_rfl⟩,by rw [he,(circleArcParam_endpoints a).2]⟩)
  have hinj : Set.InjOn (circleArcParam a) (Icc l r) := by
    intro u hu v hv he
    exact circleArcParam_injOn_slit a ⟨hl'.trans_le hu.1,hu.2.trans_lt hr'⟩
      ⟨hl'.trans_le hv.1,hv.2.trans_lt hr'⟩ he
  have hfront (t : ℝ) (ht : t = l ∨ t = r) : circleArcParam a t ∈ frontier V := by
    have htI : t ∈ Icc l r := by rcases ht with rfl | rfl <;> exact ⟨by linarith,by linarith⟩
    refine ⟨by rw [hclosed]; exact ⟨t,htI,rfl⟩,?_⟩
    rw [hVo.interior_eq]
    intro hmem
    rw [hparam] at hmem
    obtain ⟨s,hs,hst⟩ := hmem
    have he : s = t := hinj ⟨hs.1.le,hs.2.le⟩ htI hst
    rcases ht with ht | ht <;> linarith [hs.1,hs.2]
  exact ⟨l,r,hl',hlr,hr',hparam,hclosed,hinj,
    fun he => hlr.ne (hinj ⟨le_rfl,hlr.le⟩ ⟨hlr.le,le_rfl⟩ he),
    frontier_connectedComponentIn_subset_frontier hU hx (hfront l (Or.inl rfl)),
    frontier_connectedComponentIn_subset_frontier hU hx (hfront r (Or.inr rfl))⟩


/-- Every genuine open circle region with finite frontier and an exterior neighborhood
has finitely many genuine embedded closed component arcs with distinct frontier endpoints. -/
theorem circle_finite_embedded_component_arcs {U : Set Circle} (hU : IsOpen U)
    (hfin : (frontier U).Finite) (a : Circle) (ha : a ∉ closure U) :
    ∃ C : Set (Set Circle), C.Finite ∧ U = ⋃ V ∈ C, V ∧
      closure U = ⋃ V ∈ C, closure V ∧
      (∀ V ∈ C, ∀ W ∈ C, V ≠ W → Disjoint V W) ∧
      ∀ V ∈ C, ∃ l r : ℝ, -Real.pi < l ∧ l < r ∧ r < Real.pi ∧
        V = circleArcParam a '' Ioo l r ∧ closure V = circleArcParam a '' Icc l r ∧
        Set.InjOn (circleArcParam a) (Icc l r) ∧
        circleArcParam a l ≠ circleArcParam a r ∧
        circleArcParam a l ∈ frontier U ∧ circleArcParam a r ∈ frontier U := by
  let C : Set (Set Circle) := (fun x => connectedComponentIn U x) '' U
  have hC : C.Finite := circle_open_finite_frontier_components_finite hU hfin
  have hcov : U = ⋃ V ∈ C, V := by
    ext x
    constructor
    · intro hx
      exact mem_iUnion₂.mpr ⟨connectedComponentIn U x,⟨x,hx,rfl⟩,mem_connectedComponentIn hx⟩
    · intro hx
      obtain ⟨V,⟨y,hy,rfl⟩,hxV⟩ := mem_iUnion₂.mp hx
      exact connectedComponentIn_subset U y hxV
  refine ⟨C,hC,hcov,?_,?_,?_⟩
  · rw [←hC.closure_biUnion (fun V => V),←hcov]
  · rintro V ⟨x,hx,rfl⟩ W ⟨y,hy,rfl⟩ hne
    apply disjoint_left.mpr
    intro z hzV hzW
    exact hne ((connectedComponentIn_eq hzV).trans (connectedComponentIn_eq hzW).symm)
  · rintro V ⟨x,hx,rfl⟩
    exact circle_component_embedded_arc hU a x ha hx

/-- A genuine exterior point of a center-containing convex polygon extends radially
to genuine exterior points of every larger actual metric circle. -/
theorem fuchsian_polygon_large_circle_exterior
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w z : P.domain.carrier) (hw : w ∈ D)
    (hz : z ∉ closure D) (R : ℝ) (hR : P.hyperbolicDist w z < R) :
    ∃ x : P.domain.carrier, P.hyperbolicDist w x = R ∧ x ∉ closure D := by
  let F := normalizedPolygonKleinCoordinate P w
  let u := F z
  have hF := normalizedPolygonKleinCoordinate_isOpenEmbedding P w
  have hu0 : u ≠ 0 := by
    intro he
    have hzw : z = w := hF.injective (he.trans (normalizedPolygonKleinCoordinate_self P w).symm)
    exact hz (hzw ▸ subset_closure hw)
  have hq : ‖u‖ < Real.tanh R := by
    have h := (Real.artanh_lt_artanh_iff
      (show Real.tanh (P.hyperbolicDist w z) ∈ Ioo (-1:ℝ) 1 from
        ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩)
      (show Real.tanh R ∈ Ioo (-1:ℝ) 1 from ⟨Real.neg_one_lt_tanh _,Real.tanh_lt_one _⟩)).mp
        (by simpa only [Real.artanh_tanh] using hR)
    rwa [←normalizedPolygonKleinCoordinate_norm_eq_tanh_hyperbolicDist] at h
  have hqpos : 0 < Real.tanh R := (norm_pos_iff.mpr hu0).trans hq
  let v := (Real.tanh R/‖u‖) • u
  have hvnorm : ‖v‖ = Real.tanh R := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos hqpos (norm_pos_iff.mpr hu0))]
    exact div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hu0)
  obtain ⟨x,hxR,hxF⟩ := (normalizedPolygonKleinCoordinate_image_metric_circle P w R).symm ▸
    (show v ∈ Metric.sphere (0:ℂ) (Real.tanh R) by rw [Metric.mem_sphere,dist_zero_right,hvnorm])
  refine ⟨x,hxR,?_⟩
  intro hxD
  have hc : Convex ℝ (F '' closure D) := by
    have he : F '' closure D = _root_.LowDimensionalTopology.Geometry.Hyperbolic.kleinCoordinate ''
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer (P.finiteCoordinate w) '' (P.finiteCoordinate '' closure D)) := by
      rw [image_image,image_image]
      rfl
    rw [he]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHConvex_iff_klein_convex _).mp
      (hD.closure_convex.isometry_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discOriginNormalizer_isometry
        _))
  have h0 : (0:ℂ) ∈ F '' closure D := ⟨w,subset_closure hw,normalizedPolygonKleinCoordinate_self P w⟩
  have hv : v ∈ F '' closure D := ⟨x,hxD,hxF⟩
  let t := ‖u‖/Real.tanh R
  have ht : 0 < t := div_pos (norm_pos_iff.mpr hu0) hqpos
  have ht1 : t < 1 := (div_lt_one hqpos).mpr hq
  have hu : u ∈ F '' closure D := by
    have hmem := hc h0 hv (sub_nonneg.mpr ht1.le) ht.le (by ring : (1-t)+t=1)
    have heq : (1-t) • (0:ℂ)+t • v = u := by
      rw [smul_zero,zero_add,smul_smul]
      have hs : t*(Real.tanh R/‖u‖) = 1 := by
        dsimp [t]; field_simp
      rw [hs,one_smul]
    exact heq ▸ hmem
  obtain ⟨y,hy,hyz⟩ := hu
  exact hz (hF.injective hyz ▸ hy)


/-- Removing the open part of a truly embedded compact interval leaves exactly its two actual endpoints. -/
theorem interval_injOn_closed_sdiff_open {X : Type*} (f : ℝ → X) {l r : ℝ}
    (hlr : l < r) (hinj : Set.InjOn f (Icc l r)) :
    (f '' Icc l r) \ (f '' Ioo l r) = {f l,f r} := by
  rw [←hinj.image_sdiff_subset Ioo_subset_Icc_self,Icc_sdiff_Ioo_same hlr.le,image_pair]

/-- A genuine polygon metric circle with an exterior neighborhood and no isolated cuts
has a finite decomposition into genuine embedded compact arcs. Their open parts are
pairwise disjoint and the two distinct actual endpoints lie on the original frontier. -/
theorem fuchsian_polygon_circle_embedded_component_arcs
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w : P.domain.carrier) (R : ℝ) (hR : 0 < R)
    (x : P.domain.carrier) (hxR : P.hyperbolicDist w x = R) (hx : x ∉ closure D)
    (hclosed : closure (D ∩ {x | P.hyperbolicDist w x = R}) =
      closure D ∩ {x | P.hyperbolicDist w x = R}) :
    ∃ a : Circle, ∃ C : Set (Set P.domain.carrier), C.Finite ∧
      D ∩ {x | P.hyperbolicDist w x = R} = ⋃ V ∈ C, V ∧
      closure D ∩ {x | P.hyperbolicDist w x = R} = ⋃ V ∈ C, closure V ∧
      (∀ V ∈ C, ∀ W ∈ C, V ≠ W → Disjoint V W) ∧
      ∀ V ∈ C, ∃ l r : ℝ, -Real.pi < l ∧ l < r ∧ r < Real.pi ∧
        V = fuchsianCircleArcParam P w R hR a '' Ioo l r ∧
        closure V = fuchsianCircleArcParam P w R hR a '' Icc l r ∧
        Set.InjOn (fuchsianCircleArcParam P w R hR a) (Icc l r) ∧
        fuchsianCircleArcParam P w R hR a l ≠ fuchsianCircleArcParam P w R hR a r ∧
        fuchsianCircleArcParam P w R hR a l ∈ frontier D ∧
        fuchsianCircleArcParam P w R hR a r ∈ frontier D ∧
        closure V \ V = {fuchsianCircleArcParam P w R hR a l,fuchsianCircleArcParam P w R hR a r} := by
  let e := fuchsianMetricCircleHomeomorph P w R hR
  let f : Circle → P.domain.carrier := fun u => (e u).val
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hinj : Function.Injective f := Subtype.val_injective.comp e.injective
  let U := f ⁻¹' D
  have hU : IsOpen U := hD.locallyFinite.fundamental.isOpen.preimage hf
  have hfin : (frontier U).Finite := by
    have hB : (f ⁻¹' frontier D).Finite := by
      apply (fuchsian_polygon_frontier_hyperbolic_circle_inter_finite hD w R).of_injOn
        (f := f) ?_ hinj.injOn
      intro u hu
      exact ⟨hu,(e u).property⟩
    exact hB.subset (hf.frontier_preimage_subset D)
  let a := e.symm ⟨x,hxR⟩
  have hfa : f a = x := congrArg Subtype.val (e.apply_symm_apply ⟨x,hxR⟩)
  have ha : a ∉ closure U := by
    intro ha
    have hh := hf.closure_preimage_subset D ha
    exact hx (hfa ▸ hh)
  obtain ⟨E,hE,hcov,hcl,hdisj,hprop⟩ := circle_finite_embedded_component_arcs hU hfin a ha
  have hVsub (V : Set Circle) (hV : V ∈ E) : V ⊆ U := by
    intro u hu
    rw [hcov]
    exact mem_iUnion₂.mpr ⟨V,hV,hu⟩
  have heU : f '' U = D ∩ {x | P.hyperbolicDist w x = R} := by
    ext y
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨hu,(e u).property⟩
    · rintro ⟨hyD,hyR⟩
      let u := e.symm ⟨y,hyR⟩
      have he : f u = y := congrArg Subtype.val (e.apply_symm_apply ⟨y,hyR⟩)
      exact ⟨u,by change f u ∈ D; rwa [he],he⟩
  have hfcl (V : Set Circle) : closure (f '' V) = f '' closure V :=
    hf.isClosedMap.closure_image_eq_of_continuous hf V
  let C := (fun V => f '' V) '' E
  have hc : D ∩ {x | P.hyperbolicDist w x = R} = ⋃ V ∈ C, V := by
    rw [←heU,hcov]
    change f '' (⋃ V ∈ E, V) = ⋃ V ∈ (fun W => f '' W) '' E, V
    rw [biUnion_image]
    simp only [image_iUnion]
  refine ⟨a,C,hE.image _,hc,?_,?_,?_⟩
  · rw [←hclosed,←heU,hfcl,hcl]
    change f '' (⋃ V ∈ E, closure V) = ⋃ W ∈ (fun V => f '' V) '' E, closure W
    rw [biUnion_image]
    simp only [image_iUnion,←hfcl]
  · rintro V ⟨A,hA,rfl⟩ W ⟨B,hB,rfl⟩ hne
    apply disjoint_left.mpr
    rintro y ⟨u,hu,rfl⟩ ⟨v,hv,he⟩
    have hne' : A ≠ B := fun he => hne (congrArg (fun Z => f '' Z) he)
    exact disjoint_left.mp (hdisj A hA B hB hne') hu (hinj he ▸ hv)
  · rintro V ⟨A,hA,rfl⟩
    obtain ⟨l,r,hl,hlr,hr,hAeq,hAcl,hAinj,hne,hlfront,hrfront⟩ := hprop A hA
    have hOpen : f '' A = fuchsianCircleArcParam P w R hR a '' Ioo l r := by
      rw [hAeq,image_image]
      rfl
    have hClose : closure (f '' A) = fuchsianCircleArcParam P w R hR a '' Icc l r := by
      rw [hfcl,hAcl,image_image]
      rfl
    have hParamInj : Set.InjOn (fuchsianCircleArcParam P w R hR a) (Icc l r) := by
      intro t ht s hs he
      exact hAinj ht hs (hinj he)
    refine ⟨l,r,hl,hlr,hr,hOpen,hClose,hParamInj,?_,?_,?_,?_⟩
    · intro he
      exact hne (hinj he)
    · exact hf.frontier_preimage_subset D hlfront
    · exact hf.frontier_preimage_subset D hrfront
    · change closure (f '' A) \ (f '' A) = _
      rw [hClose,hOpen]
      exact interval_injOn_closed_sdiff_open _ hlr hParamInj

/-- For any original nontrivial group and any actual interior center, sufficiently
large suitable circles have finite genuinely embedded arc boundaries in the original carrier. -/
theorem exists_polygon_circle_embedded_arc_boundary
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w : P.domain.carrier) (hw : w ∈ D)
    (g : H) (hg : g ≠ 1) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ < R ∧ ∃ hR : 0 < R,
      (∀ x : P.domain.carrier, P.hyperbolicDist w x = R →
        ¬IsFuchsianPolygonVertex P D x ∧ IsDirichletCenter P x) ∧
      ∃ a : Circle, ∃ C : Set (Set P.domain.carrier), C.Finite ∧
        D ∩ {x | P.hyperbolicDist w x = R} = ⋃ V ∈ C, V ∧
        closure D ∩ {x | P.hyperbolicDist w x = R} = ⋃ V ∈ C, closure V ∧
        (∀ V ∈ C, ∀ W ∈ C, V ≠ W → Disjoint V W) ∧
        ∀ V ∈ C, ∃ l r : ℝ, -Real.pi < l ∧ l < r ∧ r < Real.pi ∧
          V = fuchsianCircleArcParam P w R hR a '' Ioo l r ∧
          closure V = fuchsianCircleArcParam P w R hR a '' Icc l r ∧
          Set.InjOn (fuchsianCircleArcParam P w R hR a) (Icc l r) ∧
          fuchsianCircleArcParam P w R hR a l ≠ fuchsianCircleArcParam P w R hR a r ∧
          fuchsianCircleArcParam P w R hR a l ∈ frontier D ∧
          fuchsianCircleArcParam P w R hR a r ∈ frontier D ∧
          closure V \ V = {fuchsianCircleArcParam P w R hR a l,fuchsianCircleArcParam P w R hR a r} := by
  have hz : g • w ∉ closure D := fun hh =>
    disjoint_left.mp (hD.locallyFinite.fundamental.disjoint_image_closure hg) (smul_mem_smul_set hw) hh
  obtain ⟨R,hbig,hR,havoid,_hside,hcl,_harcs⟩ :=
    exists_polygon_circle_finite_transverse_arc_boundary hD w (max R₀ (P.hyperbolicDist w (g • w)))
  have hR₀ : R₀ < R := (le_max_left _ _).trans_lt hbig
  have hRz : P.hyperbolicDist w (g • w) < R := (le_max_right _ _).trans_lt hbig
  obtain ⟨x,hxR,hxD⟩ := fuchsian_polygon_large_circle_exterior hD w (g • w) hw hz R hRz
  exact ⟨R,hR₀,hR,havoid,fuchsian_polygon_circle_embedded_component_arcs hD w R hR x hxR hxD hcl⟩


local instance incidenceSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance incidenceSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- A genuine connected one-sided neighborhood at a boundary point selects exactly
one actual open-region component whose closure contains that point. -/
theorem unique_component_closure_of_connected_nhds {X : Type*} [TopologicalSpace X]
    {U N : Set X} {y : X} (hN : IsOpen N) (hyN : y ∈ N)
    (hp : IsPreconnected (U ∩ N)) (hy : y ∈ closure (U ∩ N)) :
    ∃! V : Set X, V ∈ ((fun x => connectedComponentIn U x) '' U) ∧ y ∈ closure V := by
  obtain ⟨z,hzU,hzN⟩ := (show (U ∩ N).Nonempty from Set.Nonempty.of_closure ⟨y,hy⟩)
  have hsub : U ∩ N ⊆ connectedComponentIn U z := hp.subset_connectedComponentIn ⟨hzU,hzN⟩ inter_subset_left
  refine ⟨connectedComponentIn U z,⟨⟨z,hzU,rfl⟩,closure_mono hsub hy⟩,?_⟩
  rintro V ⟨⟨w,hw,rfl⟩,hyV⟩
  obtain ⟨v,hvN,hvV⟩ := mem_closure_iff.mp hyV N hN hyN
  have hvU : v ∈ U := connectedComponentIn_subset U w hvV
  have hs : U ∩ N ⊆ connectedComponentIn U w := by
    rw [connectedComponentIn_eq hvV]
    exact hp.subset_connectedComponentIn ⟨hvU,hvN⟩ inter_subset_left
  exact connectedComponentIn_eq (hs ⟨hzU,hzN⟩)

/-- The genuine original metric circle is homeomorphic to the actual unit circle
through the actual center-normalized Klein chart. -/
def fuchsianKleinCircleHomeomorph {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R : ℝ) (hR : 0 < R) :
    Circle ≃ₜ {x | P.hyperbolicDist w x = R} :=
  (complexCircleAffineHomeomorph 0 (Real.tanh R)
    (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangential_tanh_pos hR)).trans
    (((normalizedPolygonKleinCoordinate_isOpenEmbedding P w).isEmbedding.homeomorphImage
      {x | P.hyperbolicDist w x = R}).trans
      (Homeomorph.setCongr (normalizedPolygonKleinCoordinate_image_metric_circle P w R))).symm

/-- Its actual Klein coordinate is the literal positive-radius multiple of the genuine circle point. -/
theorem fuchsianKleinCircleHomeomorph_coordinate {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R : ℝ) (hR : 0 < R) (u : Circle) :
    normalizedPolygonKleinCoordinate P w (fuchsianKleinCircleHomeomorph P w R hR u).val =
      Real.tanh R • (u : ℂ) := by
  let k := ((normalizedPolygonKleinCoordinate_isOpenEmbedding P w).isEmbedding.homeomorphImage
    {x | P.hyperbolicDist w x = R}).trans
    (Homeomorph.setCongr (normalizedPolygonKleinCoordinate_image_metric_circle P w R))
  have he := congrArg Subtype.val (k.apply_symm_apply
    (complexCircleAffineHomeomorph 0 (Real.tanh R)
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangential_tanh_pos hR) u))
  change normalizedPolygonKleinCoordinate P w (k.symm
    (complexCircleAffineHomeomorph 0 (Real.tanh R)
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangential_tanh_pos hR) u)).val = _
  change normalizedPolygonKleinCoordinate P w (k.symm
    (complexCircleAffineHomeomorph 0 (Real.tanh R)
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangential_tanh_pos hR) u)).val =
    (complexCircleAffineHomeomorph 0 (Real.tanh R)
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangential_tanh_pos hR) u).val at he
  exact he.trans (by change (0:ℂ)+Real.tanh R • (u:ℂ) = _; exact zero_add _)

/-- The actual circle homeomorphism and the actual real angular curve agree exactly. -/
theorem fuchsianKleinCircleHomeomorph_exp {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R : ℝ) (hR : 0 < R) (θ : ℝ) :
    (fuchsianKleinCircleHomeomorph P w R hR (Circle.exp θ)).val = fuchsianKleinCircleParam P w R θ := by
  apply (normalizedPolygonKleinCoordinate_isOpenEmbedding P w).injective
  rw [fuchsianKleinCircleHomeomorph_coordinate,fuchsianKleinCircleParam_coordinate]
  simp only [circleMap,zero_add,Circle.coe_exp,Complex.real_smul]


/-- A true local homeomorphism whose actual region germ is one strict real side
provides a genuine connected punctured neighborhood, not just a sign label. -/
theorem one_sided_local_homeomorph_connected_nhds {X : Type*} [TopologicalSpace X]
    {f : ℝ → X} (hf : IsLocalHomeomorph f) {U : Set X} (x d : ℝ) (hd : d ≠ 0)
    (hside : ∀ᶠ t in 𝓝 x, (f t ∈ U ↔ d*(t-x) < 0)) :
    ∃ N : Set X, IsOpen N ∧ f x ∈ N ∧ IsPreconnected (U ∩ N) ∧ f x ∈ closure (U ∩ N) := by
  obtain ⟨e,hx,he⟩ := hf x
  have hev : ∀ᶠ t in 𝓝 x, t ∈ e.source ∧ (e t ∈ U ↔ d*(t-x) < 0) := by
    rw [he] at hside
    have hs : ∀ᶠ t in 𝓝 x, t ∈ e.source := e.open_source.mem_nhds hx
    exact hs.and hside
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp hev
  let I := Ioo (x-ε) (x+ε)
  have hdist (t : ℝ) (ht : t ∈ I) : dist t x < ε := by
    rw [Real.dist_eq,abs_lt]
    exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
  have hIsub : I ⊆ e.source := fun t ht => (hball (hdist t ht)).1
  let J := if 0 < d then Ioo (x-ε) x else Ioo x (x+ε)
  have hJsub : J ⊆ I := by
    intro t ht
    by_cases hp : 0 < d
    · simp only [J,ite_eq_left hp,mem_Ioo] at ht
      exact ⟨ht.1,by linarith [ht.2]⟩
    · simp only [J,ite_eq_right hp,mem_Ioo] at ht
      exact ⟨by linarith [ht.1],ht.2⟩
  have hJpre : IsPreconnected J := by
    by_cases hp : 0 < d
    · simpa only [J,ite_eq_left hp] using (isPreconnected_Ioo : IsPreconnected (Ioo (x-ε) x))
    · simpa only [J,ite_eq_right hp] using (isPreconnected_Ioo : IsPreconnected (Ioo x (x+ε)))
  have hJcl : x ∈ closure J := by
    by_cases hp : 0 < d
    · simp only [J,ite_eq_left hp,closure_Ioo (by linarith : x-ε < x).ne,mem_Icc]
      exact ⟨by linarith,le_rfl⟩
    · simp only [J,ite_eq_right hp,closure_Ioo (by linarith : x < x+ε).ne,mem_Icc]
      exact ⟨le_rfl,by linarith⟩
  have hchar (t : ℝ) (ht : t ∈ I) : e t ∈ U ↔ t ∈ J := by
    rw [(hball (hdist t ht)).2]
    by_cases hp : 0 < d
    · simp only [J,ite_eq_left hp,mem_Ioo]
      constructor
      · intro hh
        refine ⟨ht.1,?_⟩
        by_contra hn
        have hn' : 0 ≤ t-x := sub_nonneg.mpr (le_of_not_gt hn)
        exact (not_lt_of_ge (mul_nonneg hp.le hn')) hh
      · intro hh
        exact mul_neg_of_pos_of_neg hp (sub_neg.mpr hh.2)
    · have hn : d < 0 := lt_of_le_of_ne (le_of_not_gt hp) hd
      simp only [J,ite_eq_right hp,mem_Ioo]
      constructor
      · intro hh
        refine ⟨?_,ht.2⟩
        by_contra hp'
        have hn' : t-x ≤ 0 := sub_nonpos.mpr (le_of_not_gt hp')
        exact (not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos hn.le hn')) hh
      · intro hh
        exact mul_neg_of_neg_of_pos hn (sub_pos.mpr hh.1)
  let N := e '' I
  have hNeq : U ∩ N = e '' J := by
    ext y
    constructor
    · rintro ⟨hyU,t,htI,rfl⟩
      exact ⟨t,(hchar t htI).mp hyU,rfl⟩
    · rintro ⟨t,htJ,rfl⟩
      exact ⟨(hchar t (hJsub htJ)).mpr htJ,⟨t,hJsub htJ,rfl⟩⟩
  refine ⟨N,e.isOpen_image_of_subset_source isOpen_Ioo hIsub,?_,?_,?_⟩
  · rw [he]
    exact ⟨x,⟨by linarith,by linarith⟩,rfl⟩
  · rw [hNeq]
    exact hJpre.image e (e.continuousOn.mono (hJsub.trans hIsub))
  · rw [he,hNeq]
    exact mem_closure_image (e.continuousAt hx) hJcl

/-- The genuine nonzero one-sided local chart gives unique actual component incidence at the cut. -/
theorem one_sided_local_homeomorph_unique_component {X : Type*} [TopologicalSpace X]
    {f : ℝ → X} (hf : IsLocalHomeomorph f) {U : Set X} (x d : ℝ) (hd : d ≠ 0)
    (hside : ∀ᶠ t in 𝓝 x, (f t ∈ U ↔ d*(t-x) < 0)) :
    ∃! V : Set X, V ∈ ((fun z => connectedComponentIn U z) '' U) ∧ f x ∈ closure V := by
  obtain ⟨N,hN,hxN,hpre,hcl⟩ := one_sided_local_homeomorph_connected_nhds hf x d hd hside
  exact unique_component_closure_of_connected_nhds hN hxN hpre hcl


/-- Genuine one-sidedness of the actual original circle curve gives exactly one
actual circle-region component incident to the original cut point. -/
theorem fuchsian_circle_one_sided_unique_component
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    {D : Set P.domain.carrier} (w x : P.domain.carrier) (R : ℝ) (hR : 0 < R)
    (hxR : P.hyperbolicDist w x = R)
    (hside : ∃ θ d : ℝ, d ≠ 0 ∧ fuchsianKleinCircleParam P w R θ = x ∧
      ∀ᶠ t in 𝓝 θ, (fuchsianKleinCircleParam P w R t ∈ D ↔ d*(t-θ) < 0)) :
    ∃! V : Set {z | P.hyperbolicDist w z = R},
      V ∈ ((fun z => connectedComponentIn (Subtype.val ⁻¹' D) z) '' (Subtype.val ⁻¹' D)) ∧
        (⟨x,hxR⟩ : {z | P.hyperbolicDist w z = R}) ∈ closure V := by
  obtain ⟨θ,d,hd,hθ,he⟩ := hside
  let f : ℝ → {z | P.hyperbolicDist w z = R} :=
    fun t => fuchsianKleinCircleHomeomorph P w R hR (Circle.exp t)
  have hlocal : IsLocalHomeomorph f :=
    (fuchsianKleinCircleHomeomorph P w R hR).isLocalHomeomorph.comp Circle.isCoveringMap_exp.isLocalHomeomorph
  have hpoint : f θ = (⟨x,hxR⟩ : {z | P.hyperbolicDist w z = R}) :=
    Subtype.ext ((fuchsianKleinCircleHomeomorph_exp P w R hR θ).trans hθ)
  have hside' : ∀ᶠ t in 𝓝 θ, (f t ∈ Subtype.val ⁻¹' D ↔ d*(t-θ) < 0) := by
    filter_upwards [he] with t ht
    change ((fuchsianKleinCircleHomeomorph P w R hR (Circle.exp t)).val ∈ D ↔ _)
    rwa [fuchsianKleinCircleHomeomorph_exp]
  have hu := one_sided_local_homeomorph_unique_component hlocal θ d hd hside'
  rw [hpoint] at hu
  exact hu

/-- Arbitrarily large suitable actual circles have unique actual interior-component
incidence at every original polygon frontier cut. -/
theorem exists_polygon_circle_unique_component_incidence
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w : P.domain.carrier) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ < R ∧ 0 < R ∧
      (∀ x : P.domain.carrier, P.hyperbolicDist w x = R →
        ¬IsFuchsianPolygonVertex P D x ∧ IsDirichletCenter P x) ∧
      ∀ (x : P.domain.carrier) (hxR : P.hyperbolicDist w x = R), x ∈ frontier D →
        ∃! V : Set {z | P.hyperbolicDist w z = R},
          V ∈ ((fun z => connectedComponentIn (Subtype.val ⁻¹' D) z) '' (Subtype.val ⁻¹' D)) ∧
            (⟨x,hxR⟩ : {z | P.hyperbolicDist w z = R}) ∈ closure V := by
  obtain ⟨R,hR₀,hR,havoid,hside,_⟩ := exists_polygon_circle_finite_transverse_arc_boundary hD w R₀
  refine ⟨R,hR₀,hR,havoid,?_⟩
  intro x hxR hx
  exact fuchsian_circle_one_sided_unique_component P w x R hR hxR (hside x hx hxR)


/-- Two actual frontier points are neighbors exactly when they are the two endpoints
of the closure of one genuine component of the actual open circle region. -/
def circleArcEndpointNeighbor (U : Set Circle) (p q : Circle) : Prop :=
  p ≠ q ∧ ∃ V : Set Circle,
    V ∈ ((fun x => connectedComponentIn U x) '' U) ∧ closure V \ V = {p,q}

theorem circleArcEndpointNeighbor_symm {U : Set Circle} {p q : Circle}
    (h : circleArcEndpointNeighbor U p q) : circleArcEndpointNeighbor U q p := by
  obtain ⟨hne,V,hV,he⟩ := h
  exact ⟨hne.symm,V,hV,he.trans (pair_comm p q)⟩

/-- Every genuine circle-region component has exactly its two distinct actual frontier endpoints. -/
theorem circle_component_boundary_pair {U : Set Circle} (hU : IsOpen U)
    (a : Circle) (ha : a ∉ closure U) {V : Set Circle}
    (hV : V ∈ ((fun x => connectedComponentIn U x) '' U)) :
    ∃ p q : Circle, p ≠ q ∧ p ∈ frontier U ∧ q ∈ frontier U ∧ closure V \ V = {p,q} := by
  obtain ⟨x,hx,rfl⟩ := hV
  obtain ⟨l,r,_hl,hlr,_hr,hOpen,hClose,hinj,hne,hpl,hpr⟩ := circle_component_embedded_arc hU a x ha hx
  refine ⟨circleArcParam a l,circleArcParam a r,hne,hpl,hpr,?_⟩
  change closure (connectedComponentIn U x) \ connectedComponentIn U x = _
  rw [hClose,hOpen]
  exact interval_injOn_closed_sdiff_open _ hlr hinj

/-- Unique actual component incidence makes the actual endpoint neighbor uniquely determined. -/
theorem circle_frontier_arc_neighbor_existsUnique {U : Set Circle} (hU : IsOpen U)
    (a : Circle) (ha : a ∉ closure U)
    (hinc : ∀ p ∈ frontier U, ∃! V : Set Circle,
      V ∈ ((fun x => connectedComponentIn U x) '' U) ∧ p ∈ closure V)
    (p : {u | u ∈ frontier U}) :
    ∃! q : {u | u ∈ frontier U}, circleArcEndpointNeighbor U p.val q.val := by
  obtain ⟨V,⟨hV,hpV⟩,hunique⟩ := hinc p.val p.property
  obtain ⟨b,c,hbc,hb,hc,hpair⟩ := circle_component_boundary_pair hU a ha hV
  have hVsub : V ⊆ U := by
    obtain ⟨x,hx,rfl⟩ := hV
    exact connectedComponentIn_subset U x
  have hpnot : p.val ∉ U := by
    simpa only [hU.interior_eq] using p.property.2
  have hpends : p.val ∈ {b,c} := hpair ▸ (show p.val ∈ closure V \ V from ⟨hpV,fun hh => hpnot (hVsub hh)⟩)
  have hex : ∃ q : {u | u ∈ frontier U}, circleArcEndpointNeighbor U p.val q.val := by
    rcases mem_insert_iff.mp hpends with hp | hp
    · refine ⟨⟨c,hc⟩,?_,V,hV,?_⟩
      · simpa only [hp] using hbc
      · simpa only [hp] using hpair
    · have hp' : p.val = c := hp
      refine ⟨⟨b,hb⟩,?_,V,hV,?_⟩
      · simpa only [hp'] using hbc.symm
      · simpa only [hp',pair_comm] using hpair
  obtain ⟨q,hq⟩ := hex
  refine ⟨q,hq,?_⟩
  intro r hr
  obtain ⟨hpq,W,hW,hpairW⟩ := hq
  obtain ⟨hpr,Z,hZ,hpairZ⟩ := hr
  have hpW : p.val ∈ closure W := by
    have hh : p.val ∈ closure W \ W := by rw [hpairW]; exact mem_insert _ _
    exact hh.1
  have hpZ : p.val ∈ closure Z := by
    have hh : p.val ∈ closure Z \ Z := by rw [hpairZ]; exact mem_insert _ _
    exact hh.1
  have hWV : W = V := hunique W ⟨hW,hpW⟩
  have hZV : Z = V := hunique Z ⟨hZ,hpZ⟩
  have hrq : r.val ∈ ({p.val,q.val} : Set Circle) := by
    rw [←hpairW,hWV,←hZV,hpairZ]
    exact mem_insert_of_mem _ (mem_singleton _)
  rcases mem_insert_iff.mp hrq with hrp | hrq
  · exact (hpr hrp.symm).elim
  · exact Subtype.ext (show r.val = q.val from hrq)

/-- The actual other endpoint of the uniquely incident genuine circle-region arc. -/
def circleFrontierArcMate {U : Set Circle} (hU : IsOpen U) (a : Circle) (ha : a ∉ closure U)
    (hinc : ∀ p ∈ frontier U, ∃! V : Set Circle,
      V ∈ ((fun x => connectedComponentIn U x) '' U) ∧ p ∈ closure V) :
    {u | u ∈ frontier U} → {u | u ∈ frontier U} :=
  fun p => (circle_frontier_arc_neighbor_existsUnique hU a ha hinc p).choose

theorem circleFrontierArcMate_spec {U : Set Circle} (hU : IsOpen U) (a : Circle) (ha : a ∉ closure U)
    (hinc : ∀ p ∈ frontier U, ∃! V : Set Circle,
      V ∈ ((fun x => connectedComponentIn U x) '' U) ∧ p ∈ closure V)
    (p : {u | u ∈ frontier U}) :
    circleArcEndpointNeighbor U p.val (circleFrontierArcMate hU a ha hinc p).val :=
  (circle_frontier_arc_neighbor_existsUnique hU a ha hinc p).choose_spec.1

theorem circleFrontierArcMate_involutive {U : Set Circle} (hU : IsOpen U) (a : Circle) (ha : a ∉ closure U)
    (hinc : ∀ p ∈ frontier U, ∃! V : Set Circle,
      V ∈ ((fun x => connectedComponentIn U x) '' U) ∧ p ∈ closure V) :
    Function.Involutive (circleFrontierArcMate hU a ha hinc) := by
  intro p
  exact (circle_frontier_arc_neighbor_existsUnique hU a ha hinc (circleFrontierArcMate hU a ha hinc p)).unique
    (circleFrontierArcMate_spec hU a ha hinc (circleFrontierArcMate hU a ha hinc p))
    (circleArcEndpointNeighbor_symm (circleFrontierArcMate_spec hU a ha hinc p))

theorem circleFrontierArcMate_ne_self {U : Set Circle} (hU : IsOpen U) (a : Circle) (ha : a ∉ closure U)
    (hinc : ∀ p ∈ frontier U, ∃! V : Set Circle,
      V ∈ ((fun x => connectedComponentIn U x) '' U) ∧ p ∈ closure V)
    (p : {u | u ∈ frontier U}) : circleFrontierArcMate hU a ha hinc p ≠ p := by
  intro he
  exact (circleFrontierArcMate_spec hU a ha hinc p).1 (congrArg Subtype.val he).symm

/-- The true reversal permutation of actual arc endpoints; it reverses actual component arcs. -/
def circleFrontierArcReversal {U : Set Circle} (hU : IsOpen U) (a : Circle) (ha : a ∉ closure U)
    (hinc : ∀ p ∈ frontier U, ∃! V : Set Circle,
      V ∈ ((fun x => connectedComponentIn U x) '' U) ∧ p ∈ closure V) :
    Equiv.Perm {u | u ∈ frontier U} :=
  (circleFrontierArcMate_involutive hU a ha hinc).toPerm


/-- Actual one-sided circle curves give unique component incidence in every genuine
circle homeomorphism, including the original metric-circle chart. -/
theorem fuchsian_circle_one_sided_unique_chart_component
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    {D : Set P.domain.carrier} (w : P.domain.carrier) (R : ℝ) (hR : 0 < R)
    (e : Circle ≃ₜ {z | P.hyperbolicDist w z = R}) (p : Circle)
    (hside : ∃ θ d : ℝ, d ≠ 0 ∧ fuchsianKleinCircleParam P w R θ = (e p).val ∧
      ∀ᶠ t in 𝓝 θ, (fuchsianKleinCircleParam P w R t ∈ D ↔ d*(t-θ) < 0)) :
    ∃! V : Set Circle,
      V ∈ ((fun z => connectedComponentIn ((fun u => (e u).val) ⁻¹' D) z) ''
        ((fun u => (e u).val) ⁻¹' D)) ∧ p ∈ closure V := by
  obtain ⟨θ,d,hd,hθ,he⟩ := hside
  let f : ℝ → Circle := fun t => e.symm (fuchsianKleinCircleHomeomorph P w R hR (Circle.exp t))
  have hlocal : IsLocalHomeomorph f := e.symm.isLocalHomeomorph.comp
    ((fuchsianKleinCircleHomeomorph P w R hR).isLocalHomeomorph.comp Circle.isCoveringMap_exp.isLocalHomeomorph)
  have hpoint : f θ = p := by
    apply e.injective
    rw [e.apply_symm_apply]
    exact Subtype.ext ((fuchsianKleinCircleHomeomorph_exp P w R hR θ).trans hθ)
  have hside' : ∀ᶠ t in 𝓝 θ,
      (f t ∈ (fun u => (e u).val) ⁻¹' D ↔ d*(t-θ) < 0) := by
    filter_upwards [he] with t ht
    change ((e (e.symm (fuchsianKleinCircleHomeomorph P w R hR (Circle.exp t)))).val ∈ D ↔ _)
    rw [e.apply_symm_apply,fuchsianKleinCircleHomeomorph_exp]
    exact ht
  have hu := one_sided_local_homeomorph_unique_component hlocal θ d hd hside'
  rwa [hpoint] at hu

/-- Absence of isolated actual cuts identifies the genuine circle-chart frontier
exactly with the preimage of the original polygon frontier. -/
theorem fuchsian_circle_frontier_preimage_eq
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w : P.domain.carrier) (R : ℝ)
    (e : Circle ≃ₜ {z | P.hyperbolicDist w z = R})
    (hclosed : closure (D ∩ {x | P.hyperbolicDist w x = R}) =
      closure D ∩ {x | P.hyperbolicDist w x = R}) :
    frontier ((fun u => (e u).val) ⁻¹' D) = (fun u => (e u).val) ⁻¹' frontier D := by
  let f : Circle → P.domain.carrier := fun u => (e u).val
  let U := f ⁻¹' D
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hinj : Function.Injective f := Subtype.val_injective.comp e.injective
  have hU : IsOpen U := hD.locallyFinite.fundamental.isOpen.preimage hf
  have heU : f '' U = D ∩ {x | P.hyperbolicDist w x = R} := by
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact ⟨hu,(e u).property⟩
    · rintro ⟨hxD,hxR⟩
      let u := e.symm ⟨x,hxR⟩
      have he : f u = x := congrArg Subtype.val (e.apply_symm_apply ⟨x,hxR⟩)
      exact ⟨u,by change f u ∈ D; rwa [he],he⟩
  have hcl : f '' closure U = closure D ∩ {x | P.hyperbolicDist w x = R} := by
    rw [←hf.isClosedMap.closure_image_eq_of_continuous hf,heU,hclosed]
  refine subset_antisymm (hf.frontier_preimage_subset D) ?_
  intro u hu
  have hfu : f u ∈ frontier D := hu
  have hfucl : f u ∈ f '' closure U := by rw [hcl]; exact ⟨hfu.1,(e u).property⟩
  obtain ⟨v,hv,he⟩ := hfucl
  have hucl : u ∈ closure U := hinj he ▸ hv
  refine ⟨hucl,?_⟩
  rw [hU.interior_eq]
  change f u ∉ D
  simpa only [hD.locallyFinite.fundamental.isOpen.interior_eq] using hfu.2

/-- The actual frontier of the true metric-circle chart is in bijection with the
literal original polygon-circle cut set. -/
def fuchsianCircleFrontierCutEquiv
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w : P.domain.carrier) (R : ℝ)
    (e : Circle ≃ₜ {z | P.hyperbolicDist w z = R})
    (hclosed : closure (D ∩ {x | P.hyperbolicDist w x = R}) =
      closure D ∩ {x | P.hyperbolicDist w x = R}) :
    {p | p ∈ frontier ((fun u => (e u).val) ⁻¹' D)} ≃
      ↥(frontier D ∩ {z | P.hyperbolicDist w z = R}) := by
  have hfront := fuchsian_circle_frontier_preimage_eq hD w R e hclosed
  refine
    { toFun := fun p => ⟨(e p.val).val,?_,(e p.val).property⟩
      invFun := fun x => ⟨e.symm ⟨x.val,x.property.2⟩,?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hp : p.val ∈ frontier ((fun u => (e u).val) ⁻¹' D) := p.property
    exact (Set.ext_iff.mp hfront p.val).mp hp
  · rw [hfront]
    change (e (e.symm ⟨x.val,x.property.2⟩)).val ∈ frontier D
    rw [e.apply_symm_apply]
    exact x.property.1
  · intro p
    apply Subtype.ext
    change e.symm (e p.val) = p.val
    exact e.symm_apply_apply _
  · intro x
    apply Subtype.ext
    change (e (e.symm ⟨x.val,x.property.2⟩)).val = x.val
    exact congrArg Subtype.val (e.apply_symm_apply ⟨x.val,x.property.2⟩)


/-- For actual suitable large circles, the true circle-region frontier is finite and
its actual component endpoints admit a genuine fixed-point-free reversal involution.
Every reversed pair is the exact endpoint pair of a genuine original circle-region component. -/
theorem exists_fuchsian_circle_frontier_arc_reversal
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H} {D :
      Set P.domain.carrier}
    (hD : IsConvexFuchsianPolygon P D) (w : P.domain.carrier) (hw : w ∈ D)
    (g : H) (hg : g ≠ 1) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ < R ∧ ∃ hR : 0 < R,
      (∀ x : P.domain.carrier, P.hyperbolicDist w x = R →
        ¬IsFuchsianPolygonVertex P D x ∧ IsDirichletCenter P x) ∧
      closure (D ∩ {x | P.hyperbolicDist w x = R}) = closure D ∩ {x | P.hyperbolicDist w x = R} ∧
      let e := fuchsianMetricCircleHomeomorph P w R hR
      let U := (fun u => (e u).val) ⁻¹' D
      (frontier U).Finite ∧ ∃ b : Equiv.Perm (frontier U),
        Function.Involutive b ∧ (∀ p, b p ≠ p) ∧
        ∀ p, circleArcEndpointNeighbor U p.val (b p).val := by
  have hz : g • w ∉ closure D := fun hh =>
    disjoint_left.mp (hD.locallyFinite.fundamental.disjoint_image_closure hg) (smul_mem_smul_set hw) hh
  obtain ⟨R,hbig,hR,havoid,hside,hcl,_⟩ :=
    exists_polygon_circle_finite_transverse_arc_boundary hD w (max R₀ (P.hyperbolicDist w (g • w)))
  obtain ⟨x,hxR,hxD⟩ := fuchsian_polygon_large_circle_exterior hD w (g • w) hw hz R
    ((le_max_right _ _).trans_lt hbig)
  let e := fuchsianMetricCircleHomeomorph P w R hR
  let f : Circle → P.domain.carrier := fun u => (e u).val
  let U := f ⁻¹' D
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hinj : Function.Injective f := Subtype.val_injective.comp e.injective
  have hU : IsOpen U := hD.locallyFinite.fundamental.isOpen.preimage hf
  have hfin : (frontier U).Finite := by
    have hB : (f ⁻¹' frontier D).Finite := by
      apply (fuchsian_polygon_frontier_hyperbolic_circle_inter_finite hD w R).of_injOn
        (f := f) ?_ hinj.injOn
      intro u hu
      exact ⟨hu,(e u).property⟩
    exact hB.subset (hf.frontier_preimage_subset D)
  let a := e.symm ⟨x,hxR⟩
  have hfa : f a = x := congrArg Subtype.val (e.apply_symm_apply ⟨x,hxR⟩)
  have ha : a ∉ closure U := by
    intro hh
    have hv := hf.closure_preimage_subset D hh
    exact hxD (hfa ▸ hv)
  have hinc (p : Circle) (hp : p ∈ frontier U) :
      ∃! V : Set Circle, V ∈ ((fun x => connectedComponentIn U x) '' U) ∧ p ∈ closure V := by
    apply fuchsian_circle_one_sided_unique_chart_component P w R hR e p
    exact hside (f p) (hf.frontier_preimage_subset D hp) (e p).property
  let b := circleFrontierArcReversal hU a ha hinc
  exact ⟨R,(le_max_left _ _).trans_lt hbig,hR,havoid,hcl,hfin,b,
    circleFrontierArcMate_involutive hU a ha hinc,
    circleFrontierArcMate_ne_self hU a ha hinc,
    circleFrontierArcMate_spec hU a ha hinc⟩


/-- The already constructed actual Dirichlet pairing is effected by exactly one
actual nonidentity original group element at each genuine nonvertex cut. -/
theorem dirichletCircleCutPairing_element_existsUnique
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R : ℝ)
    (hReg : ∀ x ∈ dirichletCircleCuts P w R,
      ¬IsFuchsianPolygonVertex P (dirichletDomain P w) x)
    (x : dirichletCircleCuts P w R) :
    ∃! g : H, g ≠ 1 ∧ g • x.val = (dirichletCircleCutPairing P w hw R hReg x).val := by
  let g := dirichletCircleMateElement P w hw R hReg x
  refine ⟨g,⟨(dirichletCircleMateElement_spec P w hw R hReg x).1,rfl⟩,?_⟩
  intro h hh
  have hmem : h • x.val ∈ dirichletCircleCuts P w R := hh.2.symm ▸
    (dirichletCircleCutPairing P w hw R hReg x).property
  exact (dirichletCircleCut_mate_existsUnique P w hw R x.property
    (hReg x.val x.property)).choose_spec.2 h ⟨hh.1,hmem⟩

/-- Arbitrarily large true Dirichlet circles carry both actual fixed-point-free
involutions on the same literal finite cut set: unique original-group pairing and
reversal of actual genuine component-arc endpoints. -/
theorem exists_dirichlet_circle_two_pairings
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) (g : H) (hg : g ≠ 1) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ < R ∧ ∃ hR : 0 < R, (dirichletCircleCuts P w R).Finite ∧
      let e := fuchsianMetricCircleHomeomorph P w R hR
      let U := (fun u => (e u).val) ⁻¹' dirichletDomain P w
      (frontier U).Finite ∧ ∃ E : ↥(frontier U) ≃ dirichletCircleCuts P w R,
        (∀ p, (E p).val = (e p.val).val) ∧
        ∃ a b : Equiv.Perm (dirichletCircleCuts P w R),
          Function.Involutive a ∧ (∀ x, a x ≠ x) ∧
          (∀ x, ∃! k : H, k ≠ 1 ∧ k • x.val = (a x).val) ∧
          Function.Involutive b ∧ (∀ x, b x ≠ x) ∧
          (∀ x, circleArcEndpointNeighbor U (E.symm x).val (E.symm (b x)).val) ∧
          ∃ N : ℕ, 0 < N ∧ (a*b)^N = 1 := by
  let D := dirichletDomain P w
  have hD := dirichletDomain_isConvexFuchsianPolygon P w hw
  obtain ⟨R,hR₀,hR,havoid,hcl,hfin,B,hBi,hBne,hBspec⟩ :=
    exists_fuchsian_circle_frontier_arc_reversal hD w (dirichletDomain_center_mem P w hw) g hg R₀
  let e := fuchsianMetricCircleHomeomorph P w R hR
  let U := (fun u => (e u).val) ⁻¹' D
  let E : ↥(frontier U) ≃ dirichletCircleCuts P w R := fuchsianCircleFrontierCutEquiv hD w R e hcl
  have hReg : ∀ x ∈ dirichletCircleCuts P w R,
      ¬IsFuchsianPolygonVertex P D x := fun x hx => (havoid x hx.2).1
  have hFree : ∀ x ∈ dirichletCircleCuts P w R, IsDirichletCenter P x :=
    fun x hx => (havoid x hx.2).2
  let A := dirichletCircleCutPairing P w hw R hReg
  let C := E.permCongr B
  have hCi : Function.Involutive C := by
    intro x
    change E (B (E.symm (E (B (E.symm x)))) ) = x
    rw [E.symm_apply_apply,hBi,E.apply_symm_apply]
  have hCne (x : dirichletCircleCuts P w R) : C x ≠ x := by
    intro he
    apply hBne (E.symm x)
    have h := congrArg E.symm he
    change E.symm (E (B (E.symm x))) = E.symm x at h
    rwa [E.symm_apply_apply] at h
  have hCspec (x : dirichletCircleCuts P w R) :
      circleArcEndpointNeighbor U (E.symm x).val (E.symm (C x)).val := by
    change circleArcEndpointNeighbor U (E.symm x).val (E.symm (E (B (E.symm x)))).val
    rw [E.symm_apply_apply]
    exact hBspec (E.symm x)
  let : Finite (dirichletCircleCuts P w R) := (dirichletCircleCuts_finite P w hw R).to_subtype
  have hperiod : ∃ N : ℕ, 0 < N ∧ (A*C)^N = 1 := (isOfFinOrder_of_finite (A*C)).exists_pow_eq_one
  exact ⟨R,hR₀,hR,dirichletCircleCuts_finite P w hw R,hfin,E,(by intro p; rfl),A,C,
    dirichletCircleMate_involutive P w hw R hReg,
    dirichletCircleMate_ne_self P w hw R hReg hFree,
    dirichletCircleCutPairing_element_existsUnique P w hw R hReg,hCi,hCne,hCspec,hperiod⟩


/-- Actual finite generation simultaneously provides a connected full original orbit-ball
neighborhood and the genuine finite alternating endpoint gluing data on its Dirichlet circle.
This is pre-development data; no embedded developed curves or finite ends are asserted. -/
theorem finitelyGenerated_dirichlet_circle_gluing_data
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hFG : H.FG) (w : P.domain.carrier) (hw : IsDirichletCenter P w) (g : H) (hg : g ≠ 1) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ < R ∧ ∃ hR : 0 < R,
      IsOpen (fuchsianOrbitBallUnion P w R) ∧ IsConnected (fuchsianOrbitBallUnion P w R) ∧
      (dirichletCircleCuts P w R).Finite ∧
      let e := fuchsianMetricCircleHomeomorph P w R hR
      let U := (fun u => (e u).val) ⁻¹' dirichletDomain P w
      (frontier U).Finite ∧ ∃ E : ↥(frontier U) ≃ dirichletCircleCuts P w R,
        (∀ p, (E p).val = (e p.val).val) ∧
        ∃ a b : Equiv.Perm (dirichletCircleCuts P w R),
          Function.Involutive a ∧ (∀ x, a x ≠ x) ∧
          (∀ x, ∃! k : H, k ≠ 1 ∧ k • x.val = (a x).val) ∧
          Function.Involutive b ∧ (∀ x, b x ≠ x) ∧
          (∀ x, circleArcEndpointNeighbor U (E.symm x).val (E.symm (b x)).val) ∧
          ∃ N : ℕ, 0 < N ∧ (a*b)^N = 1 := by
  obtain ⟨R₁,_hR₁,hconn⟩ := finitelyGenerated_cofinal_orbitBallUnions_connected P hFG w hw
  obtain ⟨R,hbig,hR,hdata⟩ := exists_dirichlet_circle_two_pairings P w hw g hg (max R₀ R₁)
  have hc := hconn R ((le_max_right _ _).trans_lt hbig)
  exact ⟨R,(le_max_left _ _).trans_lt hbig,hR,hc.1,hc.2,hdata⟩

end LowDimensionalTopology.Geometry.Fuchsian
