module
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.CircleArcIncidence
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.DistanceLevelFrontiers
public import Mathlib.Analysis.Convex.PathConnected
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped Pointwise unitInterval
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
local instance orbitBoundarySphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance orbitBoundarySphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- Distance from an actual original point to the actual whole center orbit, computed
in the genuine native hyperbolic metric through the true half-plane coordinate. -/
def fuchsianNearestOrbitDistance {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w x : P.domain.carrier) : ℝ :=
  Metric.infDist (P.halfPlaneCoordinate x) (range (fun g : H => P.halfPlaneCoordinate (g • w)))

theorem continuous_fuchsianNearestOrbitDistance {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) :
    Continuous (fuchsianNearestOrbitDistance P w) :=
  (Metric.continuous_infDist_pt _).comp P.halfPlaneCoordinate.continuous

/-- The true full orbit-ball union is exactly the strict sublevel of actual orbit distance. -/
theorem fuchsianOrbitBallUnion_eq_nearest_lt {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R : ℝ) :
    fuchsianOrbitBallUnion P w R = {x | fuchsianNearestOrbitDistance P w x < R} := by
  ext x
  simp only [fuchsianOrbitBallUnion,mem_iUnion,mem_ofPred_eq]
  change (∃ g : H, P.hyperbolicDist (g • w) x < R) ↔ _
  rw [fuchsianNearestOrbitDistance,Metric.infDist_lt_iff (range_nonempty _)]
  constructor
  · rintro ⟨g,hg⟩
    refine ⟨P.halfPlaneCoordinate (g • w),⟨g,rfl⟩,?_⟩
    change dist (P.halfPlaneCoordinate (g • w)) (P.halfPlaneCoordinate x) < R at hg
    simpa only [dist_comm] using hg
  · rintro ⟨y,⟨g,rfl⟩,hg⟩
    refine ⟨g,?_⟩
    change dist (P.halfPlaneCoordinate (g • w)) (P.halfPlaneCoordinate x) < R
    simpa only [dist_comm] using hg

/-- The actual center is a genuine nearest whole-orbit point in its closed Dirichlet polygon. -/
theorem fuchsianNearestOrbitDistance_closed_dirichlet {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) {x : P.domain.carrier}
    (hx : x ∈ closure (dirichletDomain P w)) :
    fuchsianNearestOrbitDistance P w x = P.hyperbolicDist w x := by
  apply le_antisymm
  · have h := Metric.infDist_le_dist_of_mem (x := P.halfPlaneCoordinate x)
      (show P.halfPlaneCoordinate w ∈ range (fun g : H => P.halfPlaneCoordinate (g • w)) from
        ⟨1,by change P.halfPlaneCoordinate ((1:H) • w) = P.halfPlaneCoordinate w; rw [one_smul]⟩)
    exact h.trans_eq (dist_comm _ _)
  · apply (Metric.le_infDist (range_nonempty _)).mpr
    rintro y ⟨g,rfl⟩
    have hh := closure_dirichletDomain_le P w hx g
    rwa [P.hyperbolicDist_comm x w] at hh

/-- Genuine whole-orbit distance is invariant under every actual original group element. -/
theorem fuchsianNearestOrbitDistance_smul {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w x : P.domain.carrier) (g : H) :
    fuchsianNearestOrbitDistance P w (g • x) = fuchsianNearestOrbitDistance P w x := by
  apply eq_of_forall_gt_iff
  intro R
  have hg : g • x ∈ fuchsianOrbitBallUnion P w R ↔ x ∈ fuchsianOrbitBallUnion P w R := by
    constructor
    · intro hh
      have hv : g⁻¹ • (g • x) ∈ g⁻¹ • fuchsianOrbitBallUnion P w R := smul_mem_smul_set hh
      rw [fuchsianOrbitBallUnion_invariant,inv_smul_smul] at hv
      exact hv
    · intro hh
      have hv : g • x ∈ g • fuchsianOrbitBallUnion P w R := smul_mem_smul_set hh
      rwa [fuchsianOrbitBallUnion_invariant] at hv
  exact (Set.ext_iff.mp (fuchsianOrbitBallUnion_eq_nearest_lt P w R) (g • x)).symm.trans
    (hg.trans (Set.ext_iff.mp (fuchsianOrbitBallUnion_eq_nearest_lt P w R) x))

/-- Every actual full-orbit neighborhood frontier point has the exact genuine nearest-orbit distance. -/
theorem fuchsianOrbitBallUnion_frontier_subset_level {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R : ℝ) :
    frontier (fuchsianOrbitBallUnion P w R) ⊆ {x | fuchsianNearestOrbitDistance P w x = R} := by
  rw [fuchsianOrbitBallUnion_eq_nearest_lt]
  exact frontier_lt_subset_eq (continuous_fuchsianNearestOrbitDistance P w) continuous_const

/-- Every actual closed Dirichlet circle point lies on the true whole-orbit neighborhood frontier. -/
theorem closed_dirichlet_circle_subset_orbit_frontier {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R : ℝ) (hR : 0 < R) :
    closure (dirichletDomain P w) ∩ {x | P.hyperbolicDist w x = R} ⊆
      frontier (fuchsianOrbitBallUnion P w R) := by
  intro x hx
  have hnear : fuchsianNearestOrbitDistance P w x = R :=
    (fuchsianNearestOrbitDistance_closed_dirichlet P w hx.1).trans hx.2
  have hxnot : x ∉ fuchsianOrbitBallUnion P w R := by
    rw [fuchsianOrbitBallUnion_eq_nearest_lt]
    change ¬fuchsianNearestOrbitDistance P w x < R
    rw [hnear]
    exact lt_irrefl _
  have hxball : P.halfPlaneCoordinate x ∈ frontier (Metric.ball (P.halfPlaneCoordinate w) R) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hMetric_ball_frontier _ _ hR]
    change dist (P.halfPlaneCoordinate x) (P.halfPlaneCoordinate w) = R
    have hh : P.hyperbolicDist w x = R := hx.2
    change dist (P.halfPlaneCoordinate w) (P.halfPlaneCoordinate x) = R at hh
    simpa only [dist_comm] using hh
  have he := P.halfPlaneCoordinate.isOpenMap.preimage_closure_eq_closure_preimage
    P.halfPlaneCoordinate.continuous (Metric.ball (P.halfPlaneCoordinate w) R)
  have hxb : x ∈ closure (P.halfPlaneCoordinate ⁻¹' Metric.ball (P.halfPlaneCoordinate w) R) :=
    (Set.ext_iff.mp he x).mp hxball.1
  have hsub : P.halfPlaneCoordinate ⁻¹' Metric.ball (P.halfPlaneCoordinate w) R ⊆
      fuchsianOrbitBallUnion P w R := by
    intro y hy
    have hh : dist (P.halfPlaneCoordinate y) (P.halfPlaneCoordinate w) < R := hy
    exact mem_iUnion.mpr ⟨1,by
      change dist (P.halfPlaneCoordinate ((1:H) • w)) (P.halfPlaneCoordinate y) < R
      simpa only [one_smul,dist_comm] using hh⟩
  refine ⟨closure_mono hsub hxb,?_⟩
  rwa [(fuchsianOrbitBallUnion_isOpen P w R).interior_eq]

/-- The actual neighborhood frontier is preserved by every original group element. -/
theorem fuchsianOrbitBallUnion_frontier_invariant {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (R : ℝ) (g : H) :
    g • frontier (fuchsianOrbitBallUnion P w R) = frontier (fuchsianOrbitBallUnion P w R) := by
  let : ContinuousConstSMul H P.domain.carrier := _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainContinuousConstSMul P.domain
  change (Homeomorph.smul g) '' frontier (fuchsianOrbitBallUnion P w R) = _
  rw [(Homeomorph.smul g).image_frontier]
  change frontier (g • fuchsianOrbitBallUnion P w R) = _
  rw [fuchsianOrbitBallUnion_invariant]

/-- The literal full original neighborhood frontier is exactly the union of all
actual original group translates of the closed Dirichlet-circle intersection. -/
theorem fuchsianOrbitBallUnion_frontier_eq_dirichlet_circle_translates
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) (R : ℝ) (hR : 0 < R) :
    frontier (fuchsianOrbitBallUnion P w R) = ⋃ g : H,
      g • (closure (dirichletDomain P w) ∩ {x | P.hyperbolicDist w x = R}) := by
  have hD := dirichletDomain_isConvexFuchsianPolygon P w hw
  ext x
  constructor
  · intro hx
    have hcov : x ∈ ⋃ g : H, (fun y : P.domain.carrier => g • y) '' closure (dirichletDomain P w) := by
      rw [hD.locallyFinite.fundamental.closure_cover]
      trivial
    obtain ⟨g,y,hy,hgy⟩ := mem_iUnion.mp hcov
    change g • y = x at hgy
    have hnearest : fuchsianNearestOrbitDistance P w x = R := fuchsianOrbitBallUnion_frontier_subset_level P w R hx
    have hyr : P.hyperbolicDist w y = R := by
      rw [←fuchsianNearestOrbitDistance_closed_dirichlet P w hy,
        ←fuchsianNearestOrbitDistance_smul P w y g,hgy]
      exact hnearest
    exact mem_iUnion.mpr ⟨g,y,⟨hy,hyr⟩,hgy⟩
  · intro hx
    obtain ⟨g,y,hy,hgy⟩ := mem_iUnion.mp hx
    change g • y = x at hgy
    have hyf := closed_dirichlet_circle_subset_orbit_frontier P w R hR hy
    have hmem : g • y ∈ g • frontier (fuchsianOrbitBallUnion P w R) := smul_mem_smul_set hyf
    rw [fuchsianOrbitBallUnion_frontier_invariant,hgy] at hmem
    exact hmem


/-- Actual finite generation gives arbitrarily large connected whole-orbit neighborhoods
whose literal global frontiers are exactly the actual original group translates of
finitely many genuinely embedded compact Dirichlet circle arcs. -/
theorem finitelyGenerated_fullOrbitBoundary_arc_decomposition
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) (hFG :
      H.FG)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) (g : H) (hg : g ≠ 1) (R₀ : ℝ) :
    ∃ R : ℝ, R₀ < R ∧ ∃ hR : 0 < R,
      IsOpen (fuchsianOrbitBallUnion P w R) ∧ IsConnected (fuchsianOrbitBallUnion P w R) ∧
      (∀ x : P.domain.carrier, P.hyperbolicDist w x = R →
        ¬IsFuchsianPolygonVertex P (dirichletDomain P w) x ∧ IsDirichletCenter P x) ∧
      ∃ a : Circle, ∃ C : Set (Set P.domain.carrier), C.Finite ∧
        (dirichletDomain P w) ∩ {x | P.hyperbolicDist w x = R} = ⋃ V ∈ C, V ∧
        closure (dirichletDomain P w) ∩ {x | P.hyperbolicDist w x = R} = ⋃ V ∈ C, closure V ∧
        frontier (fuchsianOrbitBallUnion P w R) = ⋃ k : H, ⋃ V ∈ C, k • closure V ∧
        (∀ V ∈ C, ∀ W ∈ C, V ≠ W → Disjoint V W) ∧
        ∀ V ∈ C, ∃ l r : ℝ, -Real.pi < l ∧ l < r ∧ r < Real.pi ∧
          V = fuchsianCircleArcParam P w R hR a '' Ioo l r ∧
          closure V = fuchsianCircleArcParam P w R hR a '' Icc l r ∧
          Set.InjOn (fuchsianCircleArcParam P w R hR a) (Icc l r) ∧
          fuchsianCircleArcParam P w R hR a l ≠ fuchsianCircleArcParam P w R hR a r ∧
          fuchsianCircleArcParam P w R hR a l ∈ frontier (dirichletDomain P w) ∧
          fuchsianCircleArcParam P w R hR a r ∈ frontier (dirichletDomain P w) ∧
          closure V \ V = {fuchsianCircleArcParam P w R hR a l,fuchsianCircleArcParam P w R hR a r} := by
  have hD := dirichletDomain_isConvexFuchsianPolygon P w hw
  obtain ⟨R₁,_hR₁,hconn⟩ := finitelyGenerated_cofinal_orbitBallUnions_connected P hFG w hw
  obtain ⟨R,hbig,hR,havoid,a,C,hfinite,hOpen,hClose,hdisj,hprop⟩ :=
    exists_polygon_circle_embedded_arc_boundary hD w (dirichletDomain_center_mem P w hw) g hg (max R₀ R₁)
  have hc := hconn R ((le_max_right _ _).trans_lt hbig)
  have hBd := fuchsianOrbitBallUnion_frontier_eq_dirichlet_circle_translates P w hw R hR
  rw [hClose] at hBd
  have hBd' : frontier (fuchsianOrbitBallUnion P w R) = ⋃ k : H, ⋃ V ∈ C, k • closure V := by
    simpa only [smul_set_iUnion₂] using hBd
  exact ⟨R,(le_max_left _ _).trans_lt hbig,hR,hc.1,hc.2,havoid,a,C,hfinite,hOpen,hClose,hBd',hdisj,hprop⟩



/-- The actual circle-arc path traversing the genuine angular interval once. -/
def circleArcPath (a : Circle) (l r : ℝ) : Path (circleArcParam a l) (circleArcParam a r) :=
  (Path.segment l r).map (continuous_circleArcParam a)

/-- Its image is the full actual compact angular arc. -/
theorem circleArcPath_range (a : Circle) (l r : ℝ) (hlr : l < r) :
    range (circleArcPath a l r) = circleArcParam a '' Icc l r := by
  change range (circleArcParam a ∘ (Path.segment l r)) = _
  rw [range_comp,Path.range_segment,segment_eq_Icc hlr.le]

/-- A genuine slit-contained positive circle arc is a genuinely injective path. -/
theorem circleArcPath_injective (a : Circle) {l r : ℝ}
    (hl : -Real.pi < l) (hlr : l < r) (hr : r < Real.pi) :
    Function.Injective (circleArcPath a l r) := by
  have hinj : Set.InjOn (circleArcParam a) (Icc l r) := by
    intro u hu v hv he
    exact circleArcParam_injOn_slit a ⟨hl.trans_le hu.1,hu.2.trans_lt hr⟩
      ⟨hl.trans_le hv.1,hv.2.trans_lt hr⟩ he
  have ht (t : I) : (Path.segment l r) t ∈ Icc l r := by
    rw [←segment_eq_Icc hlr.le,←Path.range_segment]
    exact mem_range_self t
  intro t s he
  exact Path.segment_injective_of_ne hlr.ne (hinj (ht t) (ht s) he)

/-- Removing the two actual endpoints of this embedded path leaves exactly the actual open arc. -/
theorem circleArcPath_sdiff_endpoints (a : Circle) {l r : ℝ}
    (hl : -Real.pi < l) (hlr : l < r) (hr : r < Real.pi) :
    range (circleArcPath a l r) \ {circleArcParam a l,circleArcParam a r} =
      circleArcParam a '' Ioo l r := by
  have hinj : Set.InjOn (circleArcParam a) (Icc l r) := by
    intro u hu v hv he
    exact circleArcParam_injOn_slit a ⟨hl.trans_le hu.1,hu.2.trans_lt hr⟩
      ⟨hl.trans_le hv.1,hv.2.trans_lt hr⟩ he
  have hsub : ({l,r}:Set ℝ) ⊆ Icc l r := by
    rw [pair_subset_iff]
    exact ⟨⟨le_rfl,hlr.le⟩,⟨hlr.le,le_rfl⟩⟩
  rw [circleArcPath_range a l r hlr,←image_pair,←hinj.image_sdiff_subset hsub,Icc_sdiff_both]

/-- Each actual neighboring endpoint pair is joined by a genuine injective path
whose full image is its actual component closure and whose endpoint-deleted image is that component. -/
theorem circleArcEndpointNeighbor_path {U : Set Circle} (hU : IsOpen U)
    (a : Circle) (ha : a ∉ closure U) {p q : Circle} (hpq : circleArcEndpointNeighbor U p q) :
    ∃ γ : Path p q, Function.Injective γ ∧ ∃ V : Set Circle,
      V ∈ ((fun x => connectedComponentIn U x) '' U) ∧ range γ = closure V ∧
        range γ \ {p,q} = V := by
  obtain ⟨_hpq,V,hV,hpair⟩ := hpq
  obtain ⟨x,hx,hxV⟩ := hV
  have hxV' : connectedComponentIn U x = V := hxV
  obtain ⟨l,r,hl,hlr,hr,hOpen,hClose,hinj,_hne,_hpl,_hpr⟩ := circle_component_embedded_arc hU a x ha hx
  rw [hxV'] at hOpen hClose
  have hpairs : ({p,q}:Set Circle) = {circleArcParam a l,circleArcParam a r} := by
    rw [←hpair,hClose,hOpen]
    exact interval_injOn_closed_sdiff_open _ hlr hinj
  rcases pair_eq_pair_iff.mp hpairs with ⟨hp,hq⟩ | ⟨hp,hq⟩
  · let γ : Path p q := (circleArcPath a l r).cast hp hq
    have hγ : range γ = closure V := by
      change range (circleArcPath a l r) = _
      rw [circleArcPath_range a l r hlr,hClose]
    refine ⟨γ,circleArcPath_injective a hl hlr hr,V,⟨x,hx,hxV⟩,hγ,?_⟩
    change range (circleArcPath a l r) \ {p,q} = V
    rw [hp,hq,circleArcPath_sdiff_endpoints a hl hlr hr,←hOpen]
  · let γ : Path p q := (circleArcPath a l r).symm.cast hp hq
    have hγ : range γ = closure V := by
      change range (circleArcPath a l r).symm = _
      rw [Path.symm_range,circleArcPath_range a l r hlr,hClose]
    have hγinj : Function.Injective γ :=
      (circleArcPath_injective a hl hlr hr).comp unitInterval.symm_involutive.injective
    refine ⟨γ,hγinj,V,⟨x,hx,hxV⟩,hγ,?_⟩
    change range (circleArcPath a l r).symm \ {p,q} = V
    rw [Path.symm_range,hp,hq,pair_comm,circleArcPath_sdiff_endpoints a hl hlr hr,←hOpen]


/-- Each genuine Dirichlet circle-component endpoint pair is joined in the original
carrier by a genuinely injective compact path lying on the actual global orbit-neighborhood
frontier; all its points except the endpoints lie inside the original Dirichlet polygon. -/
theorem dirichlet_circle_arc_neighbor_frontier_path
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (w : P.domain.carrier) (R : ℝ) (hR : 0 < R)
    (a : Circle)
    (ha : a ∉ closure ((fun u => (fuchsianMetricCircleHomeomorph P w R hR u).val) ⁻¹' dirichletDomain P w))
    (p q : Circle)
    (hpq : circleArcEndpointNeighbor
      ((fun u => (fuchsianMetricCircleHomeomorph P w R hR u).val) ⁻¹' dirichletDomain P w) p q) :
    ∃ γ : Path (fuchsianMetricCircleHomeomorph P w R hR p).val
        (fuchsianMetricCircleHomeomorph P w R hR q).val,
      Function.Injective γ ∧ range γ ⊆ frontier (fuchsianOrbitBallUnion P w R) ∧
      range γ \ {(fuchsianMetricCircleHomeomorph P w R hR p).val,
        (fuchsianMetricCircleHomeomorph P w R hR q).val} ⊆ dirichletDomain P w := by
  let e := fuchsianMetricCircleHomeomorph P w R hR
  let f : Circle → P.domain.carrier := fun u => (e u).val
  let D := dirichletDomain P w
  let U := f ⁻¹' D
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hfi : Function.Injective f := Subtype.val_injective.comp e.injective
  have hU : IsOpen U := (dirichletDomain_isOpen P w).preimage hf
  obtain ⟨δ,hδi,V,hV,hδrange,hδopen⟩ := circleArcEndpointNeighbor_path hU a ha hpq
  have hVsub : V ⊆ U := by
    obtain ⟨x,hx,rfl⟩ := hV
    exact connectedComponentIn_subset U x
  let γ : Path (f p) (f q) := δ.map hf
  have hγrange : range γ = f '' range δ := by
    change range (f ∘ δ) = _
    rw [range_comp]
  have hγi : Function.Injective γ := hfi.comp hδi
  refine ⟨γ,hγi,?_,?_⟩
  · intro x hx
    rw [hγrange,hδrange] at hx
    obtain ⟨u,hu,rfl⟩ := hx
    have huD : f u ∈ closure D := hf.closure_preimage_subset D (closure_mono hVsub hu)
    exact closed_dirichlet_circle_subset_orbit_frontier P w R hR ⟨huD,(e u).property⟩
  · have heq : range γ \ {f p,f q} = f '' V := by
      rw [hγrange,←image_pair,←image_sdiff hfi,hδopen]
    rw [heq]
    rintro x ⟨u,hu,rfl⟩
    exact hVsub hu

end LowDimensionalTopology.Geometry.Fuchsian
