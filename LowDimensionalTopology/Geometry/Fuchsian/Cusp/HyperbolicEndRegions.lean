module
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.ConvexRadial
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.DirichletParabolicEnds
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.Boundary.DirichletOrdinarySides
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.ParabolicSideFiniteness
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.CircleNoTriod
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.NormNum
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter Topology
open scoped OnePoint Complex.UnitDisc unitInterval
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A true bounded Jordan side missing even one genuine limit point on its
boundary contact cannot contain an entire original non-elementary orbit. -/
theorem unitDisc_orbit_not_inside_jordan_missing_limit
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (w : P.domain.carrier)
    {C : Set ℂ} (hCJ : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C)
    (hCB : C ⊆ Metric.closedBall (0:ℂ) 1)
    (ζ : Circle) (hζ : ((ζ:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ fuchsianLimitSet H)
    (hζC : (ζ:ℂ) ∉ C) :
    ¬∀ g : H, (P.finiteCoordinate (g • w):ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C := by
  intro horbit
  let K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := (fun z : ℂ =>
    (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ''
    closure (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C)
  have hK : IsClosed K :=
    ((complexJordanInside_closure_compact_of_subset_closedUnitBall hCB).image
      OnePoint.continuous_coe).isClosed
  have horbK : MulAction.orbit H w.val ⊆ K := by
    rintro z ⟨g,rfl⟩
    exact ⟨P.finiteCoordinate (g • w),subset_closure (horbit
      g),_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteChart_coe (g • w)⟩
  have hL : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H ⊆ K :=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet_subset_closure_orbit H hNE
      w.val).trans (closure_minimal horbK hK)
  rw [fuchsianLimitSet_eq_nonElementary H hNE] at hζ
  obtain ⟨v,hv,hvζ⟩ := hL hζ
  have hvEq : v = (ζ:ℂ) := OnePoint.coe_injective hvζ
  have hζcl : (ζ:ℂ) ∈ closure (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C) := hvEq ▸ hv
  have hζsphere : (ζ:ℂ) ∈ Metric.sphere (0:ℂ) 1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using Circle.norm_coe ζ
  have hh := complexJordanInside_closure_sphere_eq hCJ hCB
  have hContact : (ζ:ℂ) ∈ C ∩ Metric.sphere (0:ℂ) 1 := hh ▸ ⟨hζcl,hζsphere⟩
  exact hζC hContact.1

/-- At a genuine Jordan boundary point where the curve is locally entirely on
the unit circle, its actual bounded side fills a true inner half-neighbourhood.
If the whole original orbit lies outside that side, this point is ordinary. -/
theorem unitDisc_jordan_local_circle_contact_not_limit
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (w : P.domain.carrier)
    {C : Set ℂ} (hCJ : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C)
    (hCB : C ⊆ Metric.closedBall (0:ℂ) 1)
    (hOutside : ∀ g : H, (P.finiteCoordinate (g • w):ℂ) ∈
      _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanOutside C)
    (ξ : ℂ) (hξ : ξ ∈ C) (U : Set ℂ) (hUo : IsOpen U) (hξU : ξ ∈ U)
    (hCU : U ∩ C ⊆ Metric.sphere (0:ℂ) 1) :
    (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∉ fuchsianLimitSet H := by
  obtain ⟨r,hr,hBU⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds hξU)
  let V := Metric.ball ξ r ∩ Metric.ball (0:ℂ) 1
  have hVpre : IsPreconnected V := ((convex_ball ξ r).inter (convex_ball (0:ℂ) 1)).isPreconnected
  have hVC : Disjoint V C := by
    apply Set.disjoint_left.mpr
    rintro z ⟨hzB,hzD⟩ hzC
    have hh := hCU ⟨hBU hzB,hzC⟩
    have hn : ‖z‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hh
    have hlt : ‖z‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hzD
    exact (ne_of_lt hlt) hn
  have hξcl : ξ ∈ closure (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C) :=
    frontier_subset_closure ((_root_.LowDimensionalTopology.Geometry.Polygon.complexJordan_regions
      hCJ).2.2.2.2.2.2.1.symm ▸ hξ)
  obtain ⟨v,hvB,hvI⟩ := mem_closure_iff_nhds.mp hξcl _ (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  have hvD := complexJordanInside_subset_ball_of_subset_closedBall zero_lt_one hCB hvI
  have hVI : V ⊆ _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C := by
    rcases complexJordan_preconnected_subset_side hCJ hVpre hVC with hi | ho
    · exact hi
    · exact False.elim (Set.disjoint_left.mp (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordan_regions
      hCJ).2.2.1
        hvI (ho ⟨hvB,hvD⟩))
  let K : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := (fun z : ℂ =>
    (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) ''
    (Metric.closedBall (0:ℂ) 1 \ Metric.ball ξ r)
  have hK : IsClosed K :=
    (((isCompact_closedBall (0:ℂ) 1).inter_right Metric.isOpen_ball.isClosed_compl).image
      OnePoint.continuous_coe).isClosed
  have horbK : MulAction.orbit H w.val ⊆ K := by
    rintro z ⟨g,rfl⟩
    refine ⟨P.finiteCoordinate (g • w),⟨?_,?_⟩,_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteChart_coe (g •
      w)⟩
    · simpa only [Metric.mem_closedBall,dist_zero_right] using
        (P.finiteCoordinate (g • w)).norm_lt_one.le
    · intro hzB
      have hzD : (P.finiteCoordinate (g • w):ℂ) ∈ Metric.ball (0:ℂ) 1 := by
        simpa only [Metric.mem_ball,dist_zero_right] using (P.finiteCoordinate (g • w)).norm_lt_one
      exact Set.disjoint_left.mp (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordan_regions hCJ).2.2.1
        (hVI ⟨hzB,hzD⟩) (hOutside g)
  have hL : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H ⊆ K :=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet_subset_closure_orbit H hNE
      w.val).trans (closure_minimal horbK hK)
  intro hξL
  rw [fuchsianLimitSet_eq_nonElementary H hNE] at hξL
  obtain ⟨v,hv,hvξ⟩ := hL hξL
  have he : v = ξ := OnePoint.coe_injective hvξ
  exact hv.2 (he.symm ▸ Metric.mem_ball_self hr)

/-- Two actual unit-circle points admit a genuine injective circle arc missing
any third prescribed circle point. This retains the named avoided point. -/
theorem circle_exists_injective_path_avoiding (p q ζ : Circle)
    (hpq : p ≠ q) (hpζ : p ≠ ζ) (hqζ : q ≠ ζ) :
    ∃ γ : Path p q, Function.Injective γ ∧ ∀ t, γ t ≠ ζ := by
  let e := _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.circleNoTriod_punctureHomeomorph ζ
  let u := e ⟨p,hpζ⟩
  let v := e ⟨q,hqζ⟩
  let arcSegment := Path.segment u.val v.val
  have hSegmentMem (t : I) : arcSegment t ∈ Ioo (-Real.pi) Real.pi :=
    (convex_Ioo (-Real.pi) Real.pi).segment_subset u.property v.property
      (by rw [←Path.range_segment]; exact mem_range_self t)
  let δ : Path u v :=
    { toFun := fun t => ⟨arcSegment t,hSegmentMem t⟩
      continuous_toFun := arcSegment.continuous.subtype_mk _
      source' := Subtype.ext arcSegment.source
      target' := Subtype.ext arcSegment.target }
  have huv : u.val ≠ v.val := by
    intro he
    exact hpq (congrArg Subtype.val (e.injective (Subtype.ext he)))
  have hδi : Function.Injective δ := fun s t he =>
    Path.segment_injective_of_ne huv (congrArg Subtype.val he)
  have hu : p = (e.symm u).val := (congrArg Subtype.val (e.symm_apply_apply ⟨p,hpζ⟩)).symm
  have hv : q = (e.symm v).val := (congrArg Subtype.val (e.symm_apply_apply ⟨q,hqζ⟩)).symm
  let γ := ((δ.map e.symm.continuous).map continuous_subtype_val).cast hu hv
  refine ⟨γ,?_,?_⟩
  · change Function.Injective (fun t : I => (e.symm (δ t)).val)
    exact Subtype.val_injective.comp (e.symm.injective.comp hδi)
  · intro t
    exact (e.symm (δ t)).property

/-- A true disc crosscut closes along a real unit-circle arc avoiding a named
third circle point. The resulting genuine Jordan curve also avoids that point. -/
theorem unitDisc_crosscut_jordan_completion_avoiding
    (a b ζ : Circle) (hζa : ζ ≠ a) (hζb : ζ ≠ b)
    (γ : Path (b:ℂ) (a:ℂ)) (hγ : Function.Injective γ)
    (hInterior : range γ \ {(a:ℂ),(b:ℂ)} ⊆ Metric.ball (0:ℂ) 1) :
    ∃ δ : Path (a:ℂ) (b:ℂ), Function.Injective δ ∧
      (∀ z ∈ range δ, ‖z‖ = 1) ∧ (ζ:ℂ) ∉ range δ ∧
      ∃ J : Circle → ℂ, Continuous J ∧ Function.Injective J ∧
        range J = range γ ∪ range δ ∧ range J ⊆ Metric.closedBall (0:ℂ) 1 ∧
        (ζ:ℂ) ∉ range J := by
  have hab : a ≠ b := by
    intro h
    have hval : γ 0 = γ 1 := γ.source.trans
      ((congrArg (fun z : Circle => (z:ℂ)) h).symm.trans γ.target.symm)
    have he := congrArg (fun t : I => (t:ℝ)) (hγ hval)
    norm_num at he
  obtain ⟨ν,hν,hνζ⟩ := circle_exists_injective_path_avoiding a b ζ hab (Ne.symm hζa) (Ne.symm hζb)
  let δ := ν.map continuous_subtype_val
  have hδ : Function.Injective δ := Circle.coe_injective.comp hν
  have hδnorm : ∀ z ∈ range δ, ‖z‖ = 1 := by
    rintro z ⟨t,rfl⟩
    exact Circle.norm_coe (ν t)
  have hδζ : (ζ:ℂ) ∉ range δ := by
    rintro ⟨t,ht⟩
    exact hνζ t (Circle.coe_injective ht)
  have hγζ : (ζ:ℂ) ∉ range γ := by
    intro hz
    have hza : (ζ:ℂ) ≠ (a:ℂ) := fun he => hζa (Circle.coe_injective he)
    have hzb : (ζ:ℂ) ≠ (b:ℂ) := fun he => hζb (Circle.coe_injective he)
    have hm : (ζ:ℂ) ∈ range γ \ {(a:ℂ),(b:ℂ)} :=
      ⟨hz,by simp only [mem_insert_iff,mem_singleton_iff]; tauto⟩
    have hn : ‖(ζ:ℂ)‖ < 1 := by
      simpa only [Metric.mem_ball,dist_zero_right] using hInterior hm
    rw [Circle.norm_coe] at hn
    exact (lt_irrefl 1) hn
  have hinter : range γ ∩ range δ = {(b:ℂ),(a:ℂ)} := by
    apply subset_antisymm
    · intro z hz
      by_cases hza : z = (a:ℂ)
      · exact mem_insert_of_mem _ (mem_singleton_iff.mpr hza)
      by_cases hzb : z = (b:ℂ)
      · exact mem_insert_iff.mpr (Or.inl hzb)
      have hm : z ∈ range γ \ {(a:ℂ),(b:ℂ)} :=
        ⟨hz.1,by simp only [mem_insert_iff,mem_singleton_iff]; tauto⟩
      have hl : ‖z‖ < 1 := by
        simpa only [Metric.mem_ball,dist_zero_right] using hInterior hm
      exact False.elim ((ne_of_lt hl) (hδnorm z hz.2))
    · intro z hz
      rcases mem_insert_iff.mp hz with hz | hz
      · subst z
        exact ⟨⟨0,γ.source⟩,⟨1,δ.target⟩⟩
      · have he : z = (a:ℂ) := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨1,γ.target⟩,⟨0,δ.source⟩⟩
  let loop := γ.trans δ
  have hloop : Set.InjOn loop (Iio (1:I)) :=
    path_trans_injOn_Iio_of_two_endpoints γ δ hγ hδ hinter
  let J := closedPathUnitCircleMap loop
  have hJ := closedPathUnitCircleMap_spec loop hloop
  have hJrange : range J = range γ ∪ range δ := hJ.2.2.trans (Path.trans_range γ δ)
  refine ⟨δ,hδ,hδnorm,hδζ,J,hJ.1,hJ.2.1,hJrange,?_,?_⟩
  · rw [hJrange]
    intro z hz
    have hn : ‖z‖ ≤ 1 := by
      rcases hz with hz | hz
      · by_cases hza : z = (a:ℂ)
        · exact hza ▸ (Circle.norm_coe a).le
        by_cases hzb : z = (b:ℂ)
        · exact hzb ▸ (Circle.norm_coe b).le
        have hm : z ∈ range γ \ {(a:ℂ),(b:ℂ)} :=
          ⟨hz,by simp only [mem_insert_iff,mem_singleton_iff]; tauto⟩
        exact (by simpa only [Metric.mem_ball,dist_zero_right] using hInterior hm : ‖z‖ < 1).le
      · exact (hδnorm z hz).le
    simpa only [Metric.mem_closedBall,dist_zero_right] using hn
  · rw [hJrange]
    exact fun h => h.elim hγζ hδζ

/-- An actual developed crosscut in the frontier of an open orbit-containing
region has a genuine Jordan completion whose bounded side is outside that
whole original region. A third genuine limit point chooses the circle arc. -/
theorem unitDisc_crosscut_frontier_neighborhood_outside
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (w : P.domain.carrier)
    {N : Set P.domain.carrier} (hNo : IsOpen N) (hNp : IsPreconnected N)
    (hOrbit : ∀ g : H, g • w ∈ N)
    (a b ζ : Circle) (hζa : ζ ≠ a) (hζb : ζ ≠ b)
    (hζL : ((ζ:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ fuchsianLimitSet H)
    (γ : Path (b:ℂ) (a:ℂ)) (hγ : Function.Injective γ)
    (hInterior : range γ \ {(a:ℂ),(b:ℂ)} ⊆ Metric.ball (0:ℂ) 1)
    (hγFront : range γ \ {(a:ℂ),(b:ℂ)} ⊆
      (fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)) '' frontier N) :
    ∃ δ : Path (a:ℂ) (b:ℂ), Function.Injective δ ∧
      (∀ z ∈ range δ, ‖z‖ = 1) ∧
      ∃ J : Circle → ℂ, Continuous J ∧ Function.Injective J ∧
        range J = range γ ∪ range δ ∧ range J ⊆ Metric.closedBall (0:ℂ) 1 ∧
        _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve (range J) ∧
        (fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)) '' N ⊆
          _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanOutside (range J) := by
  obtain ⟨δ,hδ,hδnorm,_hδζ,J,hJ,hJi,hJrange,hJB,hJζ⟩ :=
    unitDisc_crosscut_jordan_completion_avoiding a b ζ hζa hζb γ hγ hInterior
  have hCJ : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve (range
    J) := _root_.LowDimensionalTopology.Geometry.Polygon.isComplexJordanCurve_of_continuous_injective hJ hJi
  let f := fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)
  have hf := unitDisc_finite_plane_isOpenEmbedding P
  have hdis : Disjoint (f '' N) (range J) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ hzJ
    have hxnorm : ‖f x‖ < 1 := (P.finiteCoordinate x).norm_lt_one
    rw [hJrange] at hzJ
    rcases hzJ with hzγ | hzδ
    · have hxa : f x ≠ (a:ℂ) := by intro he; rw [he,Circle.norm_coe] at hxnorm; exact (lt_irrefl 1) hxnorm
      have hxb : f x ≠ (b:ℂ) := by intro he; rw [he,Circle.norm_coe] at hxnorm; exact (lt_irrefl 1) hxnorm
      have hxγ : f x ∈ range γ \ {(a:ℂ),(b:ℂ)} :=
        ⟨hzγ,by simp only [mem_insert_iff,mem_singleton_iff]; tauto⟩
      obtain ⟨y,hy,hyx⟩ := hγFront hxγ
      have he : y = x := hf.injective hyx
      exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr hNo) hy (he.symm ▸ hx)
    · exact (ne_of_lt hxnorm) (hδnorm _ hzδ)
  have hside := complexJordan_preconnected_subset_side hCJ
    (hNp.image f hf.continuous.continuousOn) hdis
  have hout : f '' N ⊆ _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanOutside (range J) :=
    hside.resolve_left (fun hi => unitDisc_orbit_not_inside_jordan_missing_limit
      P hNE w hCJ hJB ζ hζL hJζ (fun g => hi ⟨g • w,hOrbit g,rfl⟩))
  exact ⟨δ,hδ,hδnorm,J,hJ,hJi,hJrange,hJB,hCJ,hout⟩

/-- The true closed Jordan side of a disc crosscut can meet the actual limit
set on the unit circle only at the two genuine crosscut endpoints, provided
the full original orbit lies on its outside. -/
theorem unitDisc_crosscut_inside_limit_contact_endpoints
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (w : P.domain.carrier)
    (a b : Circle) (γ : Path (b:ℂ) (a:ℂ))
    (hInterior : range γ \ {(a:ℂ),(b:ℂ)} ⊆ Metric.ball (0:ℂ) 1)
    (δ : Path (a:ℂ) (b:ℂ)) (hδnorm : ∀ z ∈ range δ, ‖z‖ = 1)
    {C : Set ℂ} (hC : C = range γ ∪ range δ)
    (hCJ : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C) (hCB : C ⊆ Metric.closedBall (0:ℂ) 1)
    (hOutside : ∀ g : H, (P.finiteCoordinate (g • w):ℂ) ∈
      _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanOutside C) :
    {ξ : ℂ | ξ ∈ closure (_root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C) ∧ ξ ∈ Metric.sphere
      (0:ℂ) 1 ∧
      (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ fuchsianLimitSet H} ⊆ {(a:ℂ),(b:ℂ)} := by
  intro ξ hξ
  have hContact : ξ ∈ C ∩ Metric.sphere (0:ℂ) 1 :=
    (complexJordanInside_closure_sphere_eq hCJ hCB) ▸ ⟨hξ.1,hξ.2.1⟩
  have hξC : ξ ∈ C := hContact.1
  by_cases hξa : ξ = (a:ℂ)
  · exact Or.inl hξa
  by_cases hξb : ξ = (b:ℂ)
  · exact Or.inr (mem_singleton_iff.mpr hξb)
  have hξγ : ξ ∉ range γ := by
    intro hh
    have hm : ξ ∈ range γ \ {(a:ℂ),(b:ℂ)} :=
      ⟨hh,by simp only [mem_insert_iff,mem_singleton_iff]; tauto⟩
    have hlt : ‖ξ‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hInterior hm
    have heq : ‖ξ‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hξ.2.1
    exact (ne_of_lt hlt) heq
  let U := (range γ)ᶜ
  have hUo : IsOpen U := (isCompact_range γ.continuous).isClosed.isOpen_compl
  have hCU : U ∩ C ⊆ Metric.sphere (0:ℂ) 1 := by
    rintro z ⟨hzU,hzC⟩
    rw [hC] at hzC
    have hzδ : z ∈ range δ := hzC.resolve_left hzU
    simpa only [Metric.mem_sphere,dist_zero_right] using hδnorm z hzδ
  exact False.elim ((unitDisc_jordan_local_circle_contact_not_limit
    P hNE w hCJ hCB hOutside ξ hξC U hUo hξγ hCU) hξ.2.2)

/-- The genuine two-ended sphere compactification becomes an actual injective
complex disc crosscut through the existing finite chart, retaining its exact
original real-curve interior. -/
theorem unitDisc_two_endpoint_path_finite_data
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (F : ℝ → P.domain.carrier) (A B : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (ha : A ∈ frontier P.domain.carrier) (hb : B ∈ frontier P.domain.carrier)
    (ψ : Path B A) (hψ : Function.Injective ψ)
    (hRange : range ψ = insert A (insert B (range (fun t => (F t).val)))) :
    ∃ a b : Circle, ((a:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = A ∧ ((b:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = B ∧
      ∃ γ : Path (b:ℂ) (a:ℂ), Function.Injective γ ∧
        range γ = insert (a:ℂ) (insert (b:ℂ) (range (fun t => (P.finiteCoordinate (F t):ℂ)))) ∧
        range γ \ {(a:ℂ),(b:ℂ)} ⊆ Metric.ball (0:ℂ) 1 := by
  have hAc : ((_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart
    A:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = A :=
    sphereFiniteChart_coe_of_mem_unitDisc_closure (frontier_subset_closure ha)
  have hBc : ((_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart
    B:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = B :=
    sphereFiniteChart_coe_of_mem_unitDisc_closure (frontier_subset_closure hb)
  have hAn : ‖_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart A‖ = 1 := by
    change A ∈ frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc at ha
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle,←hAc,_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe,sub_zero] at ha
    exact ha
  have hBn : ‖_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart B‖ = 1 := by
    change B ∈ frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc at hb
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle,←hBc,_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe,sub_zero] at hb
    exact hb
  let a : Circle := ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart A,by simpa [Submonoid.unitSphere,Metric.mem_sphere,dist_zero_right] using hAn⟩
  let b : Circle := ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart B,by simpa [Submonoid.unitSphere,Metric.mem_sphere,dist_zero_right] using hBn⟩
  have hψcl (t : I) : ψ t ∈ closure _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
    have hh : ψ t ∈ insert A (insert B (range (fun s => (F s).val))) := hRange ▸ mem_range_self t
    rcases hh with hA | hh
    · rw [hA]
      exact frontier_subset_closure ha
    · rcases hh with hB | hh
      · rw [hB]
        exact frontier_subset_closure hb
      · obtain ⟨s,hs⟩ := hh
        exact hs ▸ subset_closure (F s).property
  have hsource (t : I) : ψ t ∈ _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart.source := by
    rw [_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart_source]
    exact fun he => infty_not_mem_unitDisc_closure (he ▸ hψcl t)
  let γ : Path (b:ℂ) (a:ℂ) :=
    { toFun := fun t => _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart (ψ t)
      continuous_toFun := _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart.continuousOn.comp_continuous ψ.continuous hsource
      source' := congrArg _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart ψ.source
      target' := congrArg _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart ψ.target }
  have hγ : Function.Injective γ := fun s t he =>
    hψ (_root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart.injOn (hsource s) (hsource t) he)
  have hγRange : range γ = insert (a:ℂ) (insert (b:ℂ)
      (range (fun t => (P.finiteCoordinate (F t):ℂ)))) := by
    have he : range γ = _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart '' range ψ := by
      ext z
      simp only [mem_range,mem_image]
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨ψ t,⟨t,rfl⟩,rfl⟩
      · rintro ⟨v,⟨t,rfl⟩,rfl⟩
        exact ⟨t,rfl⟩
    rw [he,hRange,Set.image_insert_eq,Set.image_insert_eq]
    have hFI : _root_.LowDimensionalTopology.Geometry.Surfaces.sphereFiniteChart '' range (fun t => (F t).val) =
        range (fun t => (P.finiteCoordinate (F t):ℂ)) := by
      ext z
      constructor
      · rintro ⟨v,⟨t,rfl⟩,rfl⟩
        exact ⟨t,(sphereFiniteChart_unitDisc_coordinate P (F t)).symm⟩
      · rintro ⟨t,rfl⟩
        exact ⟨(F t).val,⟨t,rfl⟩,sphereFiniteChart_unitDisc_coordinate P (F t)⟩
    rw [hFI]
  refine ⟨a,b,hAc,hBc,γ,hγ,hγRange,?_⟩
  intro z hz
  have hh := hγRange ▸ hz.1
  rcases hh with hza | hh
  · exact False.elim (hz.2 (Or.inl hza))
  · rcases hh with hzb | hh
    · exact False.elim (hz.2 (Or.inr (mem_singleton_iff.mpr hzb)))
    · obtain ⟨t,rfl⟩ := hh
      simpa only [Metric.mem_ball,dist_zero_right] using (P.finiteCoordinate (F t)).norm_lt_one

/-- The true bounded side of the crosscut completion pulls back to an open
original-disc region whose frontier is exactly the whole original real curve;
the added unit-circle arc contributes no original interior points. -/
theorem unitDisc_crosscut_inside_preimage_properties
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (F : ℝ → P.domain.carrier) (a b : Circle)
    (γ : Path (b:ℂ) (a:ℂ))
    (hγRange : range γ = insert (a:ℂ) (insert (b:ℂ)
      (range (fun t => (P.finiteCoordinate (F t):ℂ)))))
    (δ : Path (a:ℂ) (b:ℂ)) (hδnorm : ∀ z ∈ range δ, ‖z‖ = 1)
    {C : Set ℂ} (hC : C = range γ ∪ range δ) (hCJ : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve
      C) :
    let region := (fun z : P.domain.carrier => (P.finiteCoordinate
      z:ℂ)) ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C
    IsOpen region ∧ frontier region = range F := by
  let f := fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)
  have hf := unitDisc_finite_plane_isOpenEmbedding P
  have hpre : f ⁻¹' C = range F := by
    ext x
    constructor
    · intro hx
      change f x ∈ C at hx
      rw [hC] at hx
      have hn : ‖f x‖ < 1 := (P.finiteCoordinate x).norm_lt_one
      rcases hx with hxγ | hxδ
      · rw [hγRange] at hxγ
        rcases hxγ with he | hxγ
        · rw [he,Circle.norm_coe] at hn
          exact False.elim ((lt_irrefl 1) hn)
        · rcases hxγ with he | hxF
          · rw [he,Circle.norm_coe] at hn
            exact False.elim ((lt_irrefl 1) hn)
          · obtain ⟨t,ht⟩ := hxF
            exact ⟨t,hf.injective ht⟩
      · exact False.elim ((ne_of_lt hn) (hδnorm _ hxδ))
    · rintro ⟨t,rfl⟩
      change f (F t) ∈ C
      rw [hC]
      apply Or.inl
      rw [hγRange]
      exact mem_insert_of_mem _ (mem_insert_of_mem _ (mem_range_self t))
  refine ⟨(_root_.LowDimensionalTopology.Geometry.Polygon.complexJordan_regions hCJ).1.preimage hf.continuous,?_⟩
  rw [unitDisc_inside_preimage_frontier_eq P hCJ]
  exact hpre

/-- A genuine non-elementary disc limit set contains a third actual unit-circle
point different from any prescribed pair. -/
theorem exists_disc_limit_circle_point_ne_pair
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (a b : Circle) :
    ∃ ζ : Circle, ((ζ:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ fuchsianLimitSet H ∧ ζ ≠ a ∧ ζ ≠ b := by
  have hnot : ¬ fuchsianLimitSet H ⊆ {((a:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),((b:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)} := by
    intro hs
    have hc := (Set.toFinite {((a:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),((b:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)}).countable.mono hs
    rw [fuchsianLimitSet_eq_nonElementary H hNE] at hc
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet_not_countable H hNE hc
  obtain ⟨z,hz,hzne⟩ := Set.not_subset.mp hnot
  have hzc := P.asFuchsianDisc.limitSet_subset_frontier hz
  change z ∈ frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc at hzc
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.frontier_extendedUnitDisc_eq_circle] at hzc
  have hzn : z ≠ ∞ := fun he => _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_infty 0 1 (he ▸ hzc)
  obtain ⟨v,rfl⟩ := OnePoint.ne_infty_iff_exists.mp hzn
  have hvn : ‖v‖ = 1 := by simpa only [_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_coe,sub_zero] using hzc
  let ζ : Circle := ⟨v,by simpa [Submonoid.unitSphere,Metric.mem_sphere,dist_zero_right] using hvn⟩
  refine ⟨ζ,hz,?_,?_⟩
  · intro he
    exact hzne (Or.inl (congrArg (fun u : Circle =>
      ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) he))
  · intro he
    exact hzne (Or.inr (mem_singleton_iff.mpr
      (congrArg (fun u : Circle => ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) he)))

/--
A genuine hyperbolic crosscut side can meet only finitely many original
Dirichlet sides. Its two possible limit-set contacts are excluded from the
actual polygon closure by; all remaining ideal contacts are proved
ordinary through the true Jordan regions.
-/
theorem unitDisc_hyperbolic_crosscut_region_sides_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (w : P.domain.carrier) (hw :
      IsDirichletCenter P w)
    (k : H) (hk : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic k.val)
    (a b : Circle)
    (hka : k.val.val ((a:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
      ((a:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (hkb : k.val.val ((b:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
      ((b:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (γ : Path (b:ℂ) (a:ℂ))
    (hInterior : range γ \ {(a:ℂ),(b:ℂ)} ⊆ Metric.ball (0:ℂ) 1)
    (δ : Path (a:ℂ) (b:ℂ)) (hδnorm : ∀ z ∈ range δ, ‖z‖ = 1)
    {C : Set ℂ} (hC : C = range γ ∪ range δ)
    (hCJ : _root_.LowDimensionalTopology.Geometry.Polygon.IsComplexJordanCurve C) (hCB : C ⊆ Metric.closedBall (0:ℂ) 1)
    (hOutside : ∀ g : H, (P.finiteCoordinate (g • w):ℂ) ∈
      _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanOutside C) :
    let region := (fun z : P.domain.carrier => (P.finiteCoordinate
      z:ℂ)) ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C
    {S : Set P.domain.carrier | IsFuchsianPolygonSide P (dirichletDomain P w) S ∧
      (S ∩ closure region).Nonempty}.Finite := by
  let region := (fun z : P.domain.carrier => (P.finiteCoordinate
    z:ℂ)) ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C
  let D := dirichletDomain P w
  let K := closure ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ''
    region) ∩
    closure ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D)
  have hD := dirichletDomain_isConvexFuchsianPolygon P w hw
  have haNot : ((a:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∉
      closure ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D) := by
    intro hh
    exact hD.hyperbolic_fixed_not_idealBoundary k hk (a:ℂ) hka
      ((mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D (a:ℂ)).mpr ⟨Circle.norm_coe a,hh⟩)
  have hbNot : ((b:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∉
      closure ((Subtype.val : P.domain.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' D) := by
    intro hh
    exact hD.hyperbolic_fixed_not_idealBoundary k hk (b:ℂ) hkb
      ((mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D (b:ℂ)).mpr ⟨Circle.norm_coe b,hh⟩)
  have hregImage : (Subtype.val : P.domain.carrier →
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' region ⊆
      (fun z : ℂ => (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) '' _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C := by
    rintro z ⟨x,hx,rfl⟩
    exact ⟨P.finiteCoordinate x,hx,_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteChart_coe x⟩
  have hKL : Disjoint K (fuchsianLimitSet H) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨hzReg,hzD⟩ hzL
    have hzFront := P.asFuchsianDisc.limitSet_subset_frontier hzL
    have hzNot : z ∉ P.domain.carrier := fun hh =>
      Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr P.domain.isOpen) hzFront hh
    obtain ⟨ξ,⟨hξcl,hξsphere⟩,hξz⟩ := unitDisc_inside_ambient_closure_contact hCB
      ⟨closure_mono hregImage hzReg,hzNot⟩
    change (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = z at hξz
    have hξL : (ξ:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ fuchsianLimitSet H := by
      rw [hξz]
      exact hzL
    have hPair := unitDisc_crosscut_inside_limit_contact_endpoints
      P hNE w a b γ hInterior δ hδnorm hC hCJ hCB hOutside ⟨hξcl,hξsphere,hξL⟩
    rcases hPair with he | he
    · apply haNot
      rw [←hξz,he] at hzD
      exact hzD
    · apply hbNot
      have he' : ξ = (b:ℂ) := mem_singleton_iff.mp he
      rw [←hξz,he'] at hzD
      exact hzD
  apply (dirichletSides_closed_sphere_off_limit_finite P hNE w K
    (isClosed_closure.inter isClosed_closure) hKL).subset
  rintro S ⟨hS,z,hzS,hzReg⟩
  have hzD : z ∈ closure D :=
    frontier_subset_closure (hS.subset_frontier hD.locallyFinite.fundamental hzS)
  exact ⟨hS,z,hzS,
    image_closure_subset_closure_image continuous_subtype_val ⟨z,hzReg,rfl⟩,
    image_closure_subset_closure_image continuous_subtype_val ⟨z,hzD,rfl⟩⟩

namespace RegularDirichletCircleData
variable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P :
  _root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : _root_.LowDimensionalTopology.Geometry.Fuchsian.RegularDirichletCircleData P w)

/-- Every genuine hyperbolic developed-curve end has a finite family of true
original sides on its entire closed radial end. All crosscut separation,
ordinary-contact and whole-end assignment facts are proved from the actual
constructed compactification. -/
theorem compactification_hyperbolic_radial_end_sides_finite
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hw :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius)
    {k : H} {F : ℝ → P.domain.carrier}
    (hArc : d.originalArc hw x ⊆ range F)
    (hF : range F ⊆ frontier (_root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius))
    (hShape : _root_.LowDimensionalTopology.Geometry.Fuchsian.DiscFrontierCurveCompactification P k F) (hhyp :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic k.val) :
    {S : Set P.domain.carrier | _root_.LowDimensionalTopology.Geometry.Fuchsian.IsFuchsianPolygonSide P
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w) S ∧
      (S ∩ closure {z | z ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w ∧ d.radius <
        P.hyperbolicDist w z ∧
        _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection (Real.tanh
          d.radius) (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w z) ∈
          _root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x}).Nonempty}.Finite := by
  rcases hShape with hp | hh
  · exact False.elim (hhyp.1.not_parabolic hp.1)
  · obtain ⟨A,B,_hAB,hAf,hBf,ha,hb,ψ,hψ,_hψcl,hψrange,_hψdisc⟩ := hh.2
    obtain ⟨a,b,haA,hbB,γ,hγ,hγRange,hInterior⟩ :=
      _root_.LowDimensionalTopology.Geometry.Fuchsian.unitDisc_two_endpoint_path_finite_data P F A B ha hb ψ hψ hψrange
    obtain ⟨ζ,hζL,hζa,hζb⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.exists_disc_limit_circle_point_ne_pair P hNE a b
    let N := _root_.LowDimensionalTopology.Geometry.Fuchsian.fuchsianOrbitBallUnion P w d.radius
    have hOrbit (g : H) : g • w ∈ N := by
      apply mem_iUnion.mpr
      refine ⟨g,?_⟩
      change dist (P.halfPlaneCoordinate (g • w)) (P.halfPlaneCoordinate (g • w)) < d.radius
      simpa only [dist_self] using d.radius_pos
    have hγFront : range γ \ {(a:ℂ),(b:ℂ)} ⊆
        (fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)) '' frontier N := by
      intro z hz
      have hh := hγRange ▸ hz.1
      rcases hh with hza | hh
      · exact False.elim (hz.2 (Or.inl hza))
      · rcases hh with hzb | hh
        · exact False.elim (hz.2 (Or.inr (mem_singleton_iff.mpr hzb)))
        · obtain ⟨t,rfl⟩ := hh
          exact ⟨F t,hF (mem_range_self t),rfl⟩
    obtain ⟨δ,_hδ,hδnorm,J,_hJ,_hJi,hJRange,hJB,hCJ,hNout⟩ :=
      _root_.LowDimensionalTopology.Geometry.Fuchsian.unitDisc_crosscut_frontier_neighborhood_outside P hNE w
        d.orbit_neighborhood_open d.orbit_neighborhood_connected.isPreconnected hOrbit
        a b ζ hζa hζb hζL γ hγ hInterior hγFront
    let C := range J
    let region := (fun z : P.domain.carrier => (P.finiteCoordinate
      z:ℂ)) ⁻¹' _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanInside C
    obtain ⟨hRo,hRfr⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.unitDisc_crosscut_inside_preimage_properties P F a b γ hγRange δ hδnorm hJRange hCJ
    have hOutside (g : H) : (P.finiteCoordinate (g •
      w):ℂ) ∈ _root_.LowDimensionalTopology.Geometry.Polygon.complexJordanOutside C :=
      hNout ⟨g • w,hOrbit g,rfl⟩
    have hka : k.val.val ((a:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((a:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
      rw [haA]
      exact hAf
    have hkb : k.val.val ((b:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((b:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
      rw [hbB]
      exact hBf
    have hFinite := _root_.LowDimensionalTopology.Geometry.Fuchsian.unitDisc_hyperbolic_crosscut_region_sides_finite
      P hNE w hw k hhyp a b hka hkb γ hInterior δ hδnorm hJRange hCJ hJB hOutside
    have hRN : Disjoint region N := _root_.LowDimensionalTopology.Geometry.Fuchsian.unitDisc_inside_preimage_disjoint_of_outside P hCJ hNout
    have hRfront : frontier region ⊆ frontier N := by rw [hRfr]; exact hF
    have hcontact :
        ((_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x) ∩
          closure (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' region)).Nonempty := by
      obtain ⟨z,hz⟩ := d.originalArc_nonempty hw x
      refine ⟨_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w z,⟨z,hz,rfl⟩,?_⟩
      have hzR : z ∈ closure region := frontier_subset_closure (hRfr.symm ▸ hArc hz)
      exact mem_closure_image (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate_isOpenEmbedding P w).continuous.continuousAt hzR
    have hQR := _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichlet_Klein_strict_end_subset_region P w hw d.radius d.radius_pos
      (d.klein_originalArc_isPreconnected hw x) (d.klein_originalArc_subset_spherical_slice hw x)
      (d.klein_originalArc_isOpen_sphere hw x) hRo hRN hRfront hcontact
    apply hFinite.subset
    rintro S ⟨hS,z,hzS,hzQ⟩
    exact ⟨hS,z,hzS,closure_mono hQR hzQ⟩

/-- Every original component of the genuine regular circle has a finite family
of true polygon sides meeting its full closed radial end. Finite-return,
parabolic and hyperbolic developed components are all derived and covered. -/
theorem radial_end_sides_finite
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hw :
      _root_.LowDimensionalTopology.Geometry.Fuchsian.IsDirichletCenter P w)
    (x : _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletCircleCuts P w d.radius) :
    {S : Set P.domain.carrier | _root_.LowDimensionalTopology.Geometry.Fuchsian.IsFuchsianPolygonSide P
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w) S ∧
      (S ∩ closure {z | z ∈ _root_.LowDimensionalTopology.Geometry.Fuchsian.dirichletDomain P w ∧ d.radius <
        P.hyperbolicDist w z ∧
        _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.radialSphereProjection (Real.tanh
          d.radius) (_root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w z) ∈
          _root_.LowDimensionalTopology.Geometry.Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x}).Nonempty}.Finite := by
  rcases d.radial_end_sides_finite_or_hyperbolic_crosscut hNE hw x with hfin |
      ⟨k,F,hhyp,_hk,_hproper,_hembed,hArc,hF,hShape⟩
  · exact hfin
  · exact d.compactification_hyperbolic_radial_end_sides_finite hNE hw x hArc hF hShape hhyp

end RegularDirichletCircleData
end LowDimensionalTopology.Geometry.Fuchsian
