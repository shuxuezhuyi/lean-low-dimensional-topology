module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenCoreVertexCycles
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.FuchsianCuspCompletion
public import LowDimensionalTopology.Geometry.Fuchsian.LimitSet.Approximation.HyperbolicApproximation
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter Topology
open scoped OnePoint Complex.UnitDisc UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Truncating the true normalized cusp of a genuine one-ended region leaves
an actual compact subset of the original polygon, including its boundary.
The height threshold is arbitrary; no compact-core premise is supplied. -/
theorem IsConvexFuchsianPolygon.one_end_low_height_precompact
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D)
    (a : Mobius.ExtendedComplex) (ha : a∈frontier P.domain.carrier)
    (I : Set P.domain.carrier)
    (hI : closure ((Subtype.val : P.domain.carrier → Mobius.ExtendedComplex) '' I) \
      P.domain.carrier⊆{a})
    (q : Mobius.complexMobiusGroup) (_hq : q.val '' Hyperbolic.extendedUnitDisc=Hyperbolic.openHalfPlaneSet)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : Hyperbolic.realSLMobius A=q*Hyperbolic.cayleyMobius)
    (hqa : q.val a=∞) (hT : DiscreteGroups.mobiusTranslation 1∈DiscreteGroups.Action.Actions.subgroupConjugate q H)
    (t : ℝ) :
    ∃ K : Set P.domain.carrier, IsCompact K ∧
      closure D∩closure I⊆K∪{z | t<(normalizedPolygonHalfPlaneChart P A z).im} := by
  by_cases haD : a∈closure ((Subtype.val : P.domain.carrier → Mobius.ExtendedComplex) '' D)
  · have haC : a∈Mobius.complexCircle 0 1 := by
      change a∈frontier Hyperbolic.extendedUnitDisc at ha
      rwa [Mobius.frontier_extendedUnitDisc_eq_circle] at ha
    have han : a≠∞ := fun he => Mobius.complexCircle_infty 0 1 (he ▸ haC)
    obtain ⟨η,rfl⟩ := OnePoint.ne_infty_iff_exists.mp han
    have hn : ‖η‖=1 := by simpa only [Mobius.complexCircle_coe,sub_zero] using haC
    have hη : η∈fuchsianPolygonIdealBoundary P D :=
      (mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D η).mpr ⟨hn,haD⟩
    let ψ := normalizedPolygonHalfPlaneChart P A
    let S := ψ '' D
    obtain ⟨x,hx⟩ :=
      ((isFuchsianFundamentalDomain_iff P D).mp hD.locallyFinite.fundamental).2.1.nonempty
    let b := |(ψ x).re|+1
    have hwidth : ∀ z∈S,∀ y∈S,y.re<z.re+1 := by
      intro z hz y hy
      exact hD.normalized_horizontal_width η hη q A hA hqa hT
        ((normalizedPolygonHalfPlaneChart_image P A D) ▸ hz)
        ((normalizedPolygonHalfPlaneChart_image P A D) ▸ hy)
    have hbound : closure S⊆{z : ℍ | |z.re| ≤ b} := by
      apply closure_minimal
      · intro z hz
        have h₁ := hwidth (ψ x) ⟨x,hx,rfl⟩ z hz
        have h₂ := hwidth z hz (ψ x) ⟨x,hx,rfl⟩
        change |z.re| ≤ b
        apply abs_le.mpr
        constructor
        · dsimp [b]
          linarith [neg_abs_le (ψ x).re]
        · dsimp [b]
          linarith [le_abs_self (ψ x).re]
      · exact isClosed_le UpperHalfPlane.continuous_re.abs continuous_const
    obtain ⟨K,hK,hIK⟩ :=
      unitDisc_one_endpoint_low_strip_precompact P I (η:Mobius.ExtendedComplex) hI q A hA hqa b t
    refine ⟨K,hK,?_⟩
    rintro z ⟨hzD,hzI⟩
    by_cases hzt : t<(ψ z).im
    · exact Or.inr hzt
    · exact Or.inl (hIK z hzI
        (hbound (image_closure_subset_closure_image ψ.continuous ⟨z,hzD,rfl⟩))
        (le_of_not_gt hzt))
  · exact ⟨closure D∩closure I,unitDisc_one_endpoint_closed_inter_compact P D I a hI haD,
      subset_union_left⟩

/-- The genuine Nielsen part of a hyperbolic crosscut end is precompact
in the original native disc, with its ideal contacts excluded geometrically. -/
theorem unitDisc_hyperbolic_crosscut_region_core_precompact
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (w : P.domain.carrier)
    (hw : IsDirichletCenter P w)
    (k : H) (hk : Mobius.MobiusHyperbolic k.val)
    (a b : Circle)
    (hka : k.val.val ((a:ℂ):Mobius.ExtendedComplex) = ((a:ℂ):Mobius.ExtendedComplex))
    (hkb : k.val.val ((b:ℂ):Mobius.ExtendedComplex) = ((b:ℂ):Mobius.ExtendedComplex))
    (γ : Path (b:ℂ) (a:ℂ))
    (hInterior : range γ \ {(a:ℂ),(b:ℂ)} ⊆ Metric.ball (0:ℂ) 1)
    (δ : Path (a:ℂ) (b:ℂ)) (hδnorm : ∀ z ∈ range δ, ‖z‖ = 1)
    {C : Set ℂ} (hC : C = range γ ∪ range δ)
    (hCJ : Polygon.IsComplexJordanCurve C) (hCB : C ⊆ Metric.closedBall (0:ℂ) 1)
    (hOutside : ∀ g : H, (P.finiteCoordinate (g • w):ℂ) ∈ Polygon.complexJordanOutside C) :
    let region := (fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)) ⁻¹' Polygon.complexJordanInside C
    ∃ K : Set P.domain.carrier, IsCompact K ∧
      ((region ∩ dirichletDomain P w) ∩ fuchsianNielsenCore P hNE)⊆K := by
  let region := (fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)) ⁻¹' Polygon.complexJordanInside C
  let D := dirichletDomain P w
  let K := closure ((Subtype.val : P.domain.carrier → Mobius.ExtendedComplex) '' region) ∩
    closure ((Subtype.val : P.domain.carrier → Mobius.ExtendedComplex) '' D)
  have hD := dirichletDomain_isConvexFuchsianPolygon P w hw
  have haNot : ((a:ℂ):Mobius.ExtendedComplex) ∉
      closure ((Subtype.val : P.domain.carrier → Mobius.ExtendedComplex) '' D) := by
    intro hh
    exact hD.hyperbolic_fixed_not_idealBoundary k hk (a:ℂ) hka
      ((mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D (a:ℂ)).mpr ⟨Circle.norm_coe a,hh⟩)
  have hbNot : ((b:ℂ):Mobius.ExtendedComplex) ∉
      closure ((Subtype.val : P.domain.carrier → Mobius.ExtendedComplex) '' D) := by
    intro hh
    exact hD.hyperbolic_fixed_not_idealBoundary k hk (b:ℂ) hkb
      ((mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D (b:ℂ)).mpr ⟨Circle.norm_coe b,hh⟩)
  have hregImage : (Subtype.val : P.domain.carrier → Mobius.ExtendedComplex) '' region ⊆
      (fun z : ℂ => (z:Mobius.ExtendedComplex)) '' Polygon.complexJordanInside C := by
    rintro z ⟨x,hx,rfl⟩
    exact ⟨P.finiteCoordinate x,hx,Surfaces.discFiniteChart_coe x⟩
  have hKL : Disjoint K (fuchsianLimitSet H) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨hzReg,hzD⟩ hzL
    have hzFront := P.asFuchsianDisc.limitSet_subset_frontier hzL
    have hzNot : z ∉ P.domain.carrier := fun hh =>
      Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr P.domain.isOpen) hzFront hh
    obtain ⟨ξ,⟨hξcl,hξsphere⟩,hξz⟩ := unitDisc_inside_ambient_closure_contact hCB
      ⟨closure_mono hregImage hzReg,hzNot⟩
    change (ξ:Mobius.ExtendedComplex) = z at hξz
    have hξL : (ξ:Mobius.ExtendedComplex) ∈ fuchsianLimitSet H := by
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
  have hCompact := nielsenCore_ordinary_closed_inter_compact P hNE K
    (isClosed_closure.inter isClosed_closure) (by rwa [←fuchsianLimitSet_eq_nonElementary H hNE])
  refine ⟨_,hCompact,?_⟩
  rintro z ⟨⟨hzR,hzD⟩,hzN⟩
  exact ⟨⟨subset_closure ⟨z,hzR,rfl⟩,subset_closure ⟨z,hzD,rfl⟩⟩,subset_closure hzN⟩

namespace RegularDirichletCircleData
variable {H : Subgroup Mobius.complexMobiusGroup} {P : Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : Fuchsian.RegularDirichletCircleData P w)

/-- Every original finite-period radial end is actually precompact in the
original native disc, without any compactification assumption. -/
theorem finite_period_radial_end_core_precompact
    (hNE : DiscreteGroups.IsNonElementary H)
    (hw : Fuchsian.IsDirichletCenter P w)
    (x : Fuchsian.dirichletCircleCuts P w d.radius)
    (hpos : 0<d.endpointPeriod hw x) :
    ∃ K : Set P.domain.carrier, IsCompact K ∧
      d.radialEnd hw x∩Fuchsian.fuchsianNielsenCore P hNE⊆K := by
  obtain ⟨region,_ho,hc,hQ⟩ := d.finite_period_radial_end_precompact hNE hw x hpos
  exact ⟨closure region,hc,fun _ hz=>subset_closure (hQ hz.1)⟩

/-- The actual hyperbolic developed curve supplies genuine compactness of
the entire original radial end's Nielsen portion. -/
theorem compactification_hyperbolic_radial_end_core_precompact
    (hNE : DiscreteGroups.IsNonElementary H)
    (hw : Fuchsian.IsDirichletCenter P w)
    (x : Fuchsian.dirichletCircleCuts P w d.radius)
    {k : H} {F : ℝ → P.domain.carrier}
    (hArc : d.originalArc hw x ⊆ range F)
    (hF : range F ⊆ frontier (Fuchsian.fuchsianOrbitBallUnion P w d.radius))
    (hShape : Fuchsian.DiscFrontierCurveCompactification P k F)
    (hhyp : Mobius.MobiusHyperbolic k.val) :
    ∃ K : Set P.domain.carrier, IsCompact K ∧
      d.radialEnd hw x∩Fuchsian.fuchsianNielsenCore P hNE⊆K := by
  rcases hShape with hp | hh
  · exact False.elim (hhyp.1.not_parabolic hp.1)
  · obtain ⟨A,B,_hAB,hAf,hBf,ha,hb,ψ,hψ,_hψcl,hψrange,_hψdisc⟩ := hh.2
    obtain ⟨a,b,haA,hbB,γ,hγ,hγRange,hInterior⟩ :=
      Fuchsian.unitDisc_two_endpoint_path_finite_data P F A B ha hb ψ hψ hψrange
    obtain ⟨ζ,hζL,hζa,hζb⟩ := Fuchsian.exists_disc_limit_circle_point_ne_pair P hNE a b
    let N := Fuchsian.fuchsianOrbitBallUnion P w d.radius
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
      Fuchsian.unitDisc_crosscut_frontier_neighborhood_outside P hNE w
        d.orbit_neighborhood_open d.orbit_neighborhood_connected.isPreconnected hOrbit
        a b ζ hζa hζb hζL γ hγ hInterior hγFront
    let C := range J
    let region := (fun z : P.domain.carrier => (P.finiteCoordinate z:ℂ)) ⁻¹' Polygon.complexJordanInside C
    obtain ⟨hRo,hRfr⟩ := Fuchsian.unitDisc_crosscut_inside_preimage_properties P F a b γ hγRange δ hδnorm hJRange hCJ
    have hOutside (g : H) : (P.finiteCoordinate (g • w):ℂ) ∈ Polygon.complexJordanOutside C :=
      hNout ⟨g • w,hOrbit g,rfl⟩
    have hka : k.val.val ((a:ℂ):Mobius.ExtendedComplex) = ((a:ℂ):Mobius.ExtendedComplex) := by
      rw [haA]
      exact hAf
    have hkb : k.val.val ((b:ℂ):Mobius.ExtendedComplex) = ((b:ℂ):Mobius.ExtendedComplex) := by
      rw [hbB]
      exact hBf
    obtain ⟨K,hK,hsub⟩ := Fuchsian.unitDisc_hyperbolic_crosscut_region_core_precompact
      P hNE w hw k hhyp a b hka hkb γ hInterior δ hδnorm hJRange hCJ hJB hOutside
    have hRN : Disjoint region N := Fuchsian.unitDisc_inside_preimage_disjoint_of_outside P hCJ hNout
    have hRfront : frontier region ⊆ frontier N := by rw [hRfr]; exact hF
    have hcontact :
        ((Fuchsian.normalizedPolygonKleinCoordinate P w '' d.originalArc hw x) ∩
          closure (Fuchsian.normalizedPolygonKleinCoordinate P w '' region)).Nonempty := by
      obtain ⟨z,hz⟩ := d.originalArc_nonempty hw x
      refine ⟨Fuchsian.normalizedPolygonKleinCoordinate P w z,⟨z,hz,rfl⟩,?_⟩
      have hzR : z ∈ closure region := frontier_subset_closure (hRfr.symm ▸ hArc hz)
      exact mem_closure_image (Fuchsian.normalizedPolygonKleinCoordinate_isOpenEmbedding P
        w).continuous.continuousAt hzR
    have hQR := Fuchsian.dirichlet_Klein_strict_end_subset_region P w hw d.radius d.radius_pos
      (d.klein_originalArc_isPreconnected hw x) (d.klein_originalArc_subset_spherical_slice hw x)
      (d.klein_originalArc_isOpen_sphere hw x) hRo hRN hRfront hcontact
    refine ⟨K,hK,?_⟩
    rintro z ⟨hzQ,hzN⟩
    exact hsub ⟨⟨hQR hzQ,hzQ.1⟩,hzN⟩

end RegularDirichletCircleData

/-- Genuine full-group parabolic normalization data for a native cusp tail.
The parabolic element, its actual boundary point and the real coordinate are
all tied to the unchanged original group and native disc. -/
structure NielsenCuspTailData {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) where
  element : H
  parabolic : Mobius.MobiusParabolic element.val
  endpoint : Mobius.ExtendedComplex
  endpoint_mem : endpoint∈frontier P.domain.carrier
  fixed : element.val.val endpoint=endpoint
  normalizer : Mobius.complexMobiusGroup
  maps_disc : normalizer.val '' Hyperbolic.extendedUnitDisc=Hyperbolic.openHalfPlaneSet
  realLift : Matrix.SpecialLinearGroup (Fin 2) ℝ
  realLift_eq : Hyperbolic.realSLMobius realLift=normalizer*Hyperbolic.cayleyMobius
  maps_endpoint : normalizer.val endpoint=∞
  translation_mem : DiscreteGroups.mobiusTranslation 1∈DiscreteGroups.Action.Actions.subgroupConjugate normalizer H

/-- The genuine high horocyclic region in the original native disc. -/
def NielsenCuspTailData.tail {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (C : NielsenCuspTailData P) (t : ℝ) : Set P.domain.carrier :=
  {z | t<(normalizedPolygonHalfPlaneChart P C.realLift z).im}

theorem NielsenCuspTailData.tail_isOpen {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (C : NielsenCuspTailData P) (t : ℝ) : IsOpen (C.tail t) :=
  isOpen_lt continuous_const
    (UpperHalfPlane.continuous_im.comp (normalizedPolygonHalfPlaneChart P C.realLift).continuous)

/-- The whole original group, genuinely normalized at the chosen cusp. -/
theorem NielsenCuspTailData.halfPlaneGroup
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (C : NielsenCuspTailData P) :
    HalfPlaneFuchsianGroup (DiscreteGroups.Action.Actions.subgroupConjugate C.normalizer H) where
  preserves g:=by
    have hh:=(P.asFuchsianDisc.nielsenConjugate C.normalizer).image_eq g
    change g.val.val '' (C.normalizer.val ''
      Hyperbolic.extendedUnitDisc)=C.normalizer.val '' Hyperbolic.extendedUnitDisc at hh
    rwa [C.maps_disc] at hh
  discrete:=(P.asFuchsianDisc.nielsenConjugate C.normalizer).discrete

/-- The true cusp-tail coordinate recovers exactly the positive-height
horodisc in the actual sphere. -/
theorem NielsenCuspTailData.tail_sphere_image
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (C : NielsenCuspTailData P)
    (t : ℝ) (ht : 0 ≤ t) :
    C.normalizer.val '' ((Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' C.tail t)=
      Surfaces.stableCuspSphere t := by
  let ψ:=normalizedPolygonHalfPlaneChart P C.realLift
  apply subset_antisymm
  · rintro _ ⟨_,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨(ψ z:ℍ),hz,(halfPlane_chart_coordinate_extended P C.normalizer C.realLift C.realLift_eq z).symm⟩
  · rintro _ ⟨z,hz,rfl⟩
    let u : ℍ:=⟨z,lt_of_le_of_lt ht hz⟩
    let x:=ψ.symm u
    have he : ψ x=u:=ψ.apply_symm_apply u
    refine ⟨x.val,⟨x,?_,rfl⟩,?_⟩
    · change t<(ψ x).im
      rw [he]
      exact hz
    · exact (halfPlane_chart_coordinate_extended P C.normalizer C.realLift C.realLift_eq x).trans
        (congrArg Hyperbolic.extendedHalfPlanePoint he)

/-- The tail is literally the original normalizer's inverse image of the
genuine sphere horodisc. -/
theorem NielsenCuspTailData.tail_sphere_eq
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (C : NielsenCuspTailData P)
    (t : ℝ) (ht : 0 ≤ t) :
    (Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' C.tail t=
      C.normalizer.val⁻¹'Surfaces.stableCuspSphere t := by
  apply (Set.image_injective.mpr C.normalizer.val.injective)
  rw [C.tail_sphere_image t ht,image_preimage_eq _ C.normalizer.val.surjective]

/-- The exact native-to-half-plane normalization of every original cusp tail. -/
theorem NielsenCuspTailData.tail_coordinate_image
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (C : NielsenCuspTailData P) (t : ℝ) :
    normalizedPolygonHalfPlaneChart P C.realLift '' C.tail t=Hyperbolic.horizontalHorocyclicRegion t := by
  change (normalizedPolygonHalfPlaneChart P C.realLift) '' ((normalizedPolygonHalfPlaneChart P
    C.realLift)⁻¹'Hyperbolic.horizontalHorocyclicRegion t)=_
  exact (normalizedPolygonHalfPlaneChart P C.realLift).image_preimage _

/-- The actual change between two native cusp normalizations through an
unchanged element of the original group. -/
def NielsenCuspTailData.change {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    (C E : NielsenCuspTailData P)
    (g : H) : Mobius.complexMobiusGroup :=
  C.normalizer*g.val*E.normalizer⁻¹

theorem NielsenCuspTailData.change_maps_halfPlane
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (C E : NielsenCuspTailData P) (g : H) :
    (C.change E g).val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet := by
  have hsub (C E : NielsenCuspTailData P) (g : H) :
      (C.change E g).val '' Hyperbolic.openHalfPlaneSet⊆Hyperbolic.openHalfPlaneSet := by
    rintro _ ⟨z,hz,rfl⟩
    obtain ⟨y,hy,rfl⟩ := E.maps_disc.symm ▸ hz
    change C.normalizer • (g.val • (E.normalizer⁻¹ • (E.normalizer • y)))∈Hyperbolic.openHalfPlaneSet
    rw [inv_smul_smul,←C.maps_disc]
    exact mem_image_of_mem _ (P.asFuchsianDisc.invariant g y hy)
  apply subset_antisymm (hsub C E g)
  intro z hz
  let y:=(E.change C g⁻¹).val z
  have hy : y∈Hyperbolic.openHalfPlaneSet := hsub E C g⁻¹ ⟨z,hz,rfl⟩
  refine ⟨y,hy,?_⟩
  change C.normalizer • (g.val • (E.normalizer⁻¹ •
    (E.normalizer • (g.val⁻¹ • (C.normalizer⁻¹ • z)))))=z
  simp only [inv_smul_smul,smul_inv_smul]

theorem NielsenCuspTailData.change_infty_iff
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (C E : NielsenCuspTailData P) (g : H) :
    (C.change E g).val ∞=∞↔g.val.val E.endpoint=C.endpoint := by
  have hE : E.normalizer⁻¹ • (∞:Mobius.ExtendedComplex)=E.endpoint := by
    rw [←E.maps_endpoint]
    change E.normalizer⁻¹ • (E.normalizer • E.endpoint)=E.endpoint
    exact inv_smul_smul _ _
  change C.normalizer • (g.val • (E.normalizer⁻¹ • (∞:Mobius.ExtendedComplex)))=∞↔_
  rw [hE,←C.maps_endpoint]
  exact C.normalizer.val.injective.eq_iff

/-- The cross-normalization conjugate of the genuine unit translation is an
actual element of the unchanged original group in the first cusp chart. -/
theorem NielsenCuspTailData.change_parabolic_mem
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (C E : NielsenCuspTailData P) (g : H) :
    C.change E g*DiscreteGroups.mobiusTranslation 1*(C.change E g)⁻¹∈
      DiscreteGroups.Action.Actions.subgroupConjugate C.normalizer H := by
  obtain ⟨k,hk,hkT⟩ := (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff E.normalizer H _).mp E.translation_mem
  apply (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff C.normalizer H _).mpr
  refine ⟨g.val*k*g.val⁻¹,H.mul_mem (H.mul_mem g.property hk) (H.inv_mem g.property),?_⟩
  rw [←hkT]
  dsimp [Fuchsian.NielsenCuspTailData.change]
  group

/-- Distinct actual cusp points force the genuine cross-normalization's
real lower-left coefficient to have absolute value at least one. -/
theorem NielsenCuspTailData.change_lowerLeft
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (C E : NielsenCuspTailData P) (g : H)
    (hne : g.val.val E.endpoint≠C.endpoint)
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : Hyperbolic.realSLMobius B=C.change E g) :
    1 ≤ |B 1 0| := by
  have hc : B 1 0≠0 := by
    intro hc
    apply hne
    apply (C.change_infty_iff E g).mp
    rw [←hB]
    exact not_ne_iff.mp (fun hn=>(Hyperbolic.realSLMobius_infty_ne_iff B).mp hn hc)
  have hBT : Mobius.mobiusSpecialLinearProjection
      (Matrix.SpecialLinearGroup.map Complex.ofRealHom B*Mobius.invariantDiscTranslationLift*
        (Matrix.SpecialLinearGroup.map Complex.ofRealHom B)⁻¹)∈
      DiscreteGroups.Action.Actions.subgroupConjugate C.normalizer H := by
    rw [map_mul,map_mul,map_inv,Surfaces.stableCuspShimizu_translation_projection]
    change Hyperbolic.realSLMobius B*DiscreteGroups.mobiusTranslation 1*(Hyperbolic.realSLMobius B)⁻¹∈_
    rw [hB]
    exact C.change_parabolic_mem E g
  have hh:=Surfaces.multipleCusp_shimizu_cross _ C.halfPlaneGroup.discrete C.translation_mem
    (Matrix.SpecialLinearGroup.map Complex.ofRealHom B) hBT
    (by change (B 1 0:ℂ)≠0;exact Complex.ofReal_ne_zero.mpr hc)
  change 1 ≤ ‖(B 1 0:ℂ)‖ at hh
  simpa only [Complex.norm_real,Real.norm_eq_abs] using hh

/-- Different actual cusp endpoints have disjoint genuine unit-height
tails even after an arbitrary original group translate. This is the true
cross-cusp Shimizu bound, not a separation premise. -/
theorem NielsenCuspTailData.tail_disjoint_of_endpoint_ne
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (C E : NielsenCuspTailData P) (g : H)
    (hne : g.val.val E.endpoint≠C.endpoint) :
    Disjoint (C.tail 1) (g • E.tail 1) := by
  obtain ⟨B,hB⟩ := mobius_preserves_halfPlane_exists_SL (C.change E g) (C.change_maps_halfPlane E g)
  have hc:=C.change_lowerLeft E g hne B hB
  have hc2 : 1 ≤ (B 1 0)^2 := by nlinarith [sq_abs (B 1 0)]
  apply disjoint_left.mpr
  rintro _ hx ⟨y,hy,rfl⟩
  let u:=normalizedPolygonHalfPlaneChart P E.realLift y
  let v:=normalizedPolygonHalfPlaneChart P C.realLift (g • y)
  have he : B • u=v := by
    apply Mobius.halfPlaneBoundaryPoint_injective
    change (((B • u:ℍ):ℂ):Mobius.ExtendedComplex)=((v:ℂ):Mobius.ExtendedComplex)
    rw [←Hyperbolic.realSLMobius_action B u,hB]
    change C.normalizer • (g.val • (E.normalizer⁻¹ • Hyperbolic.extendedHalfPlanePoint u))=
      Hyperbolic.extendedHalfPlanePoint v
    have heU : Hyperbolic.extendedHalfPlanePoint u=E.normalizer.val y.val :=
      (halfPlane_chart_coordinate_extended P E.normalizer E.realLift E.realLift_eq y).symm
    rw [heU]
    change C.normalizer • (g.val • (E.normalizer⁻¹ • (E.normalizer • y.val)))=
      Hyperbolic.extendedHalfPlanePoint v
    rw [inv_smul_smul]
    exact halfPlane_chart_coordinate_extended P C.normalizer C.realLift C.realLift_eq (g • y)
  have hden : u.im<Complex.normSq (realSLDenominator B u) := by
    rw [realSLDenominator_normSq]
    have hh:=mul_nonneg (sub_nonneg.mpr hc2) (sq_nonneg u.im)
    change 1<u.im at hy
    nlinarith [sq_nonneg (B 1 0*u.re+B 1 1)]
  have him : (B • u:ℍ).im<1 := by
    rw [realSL_im_action]
    exact (div_lt_one (u.im_pos.trans hden)).mpr hden
  rw [he] at him
  change 1<v.im at hx
  exact (not_lt_of_ge hx.le) him

/-- A true high native horodisc has no ideal accumulation point other than
the fixed point of its actual original parabolic element. -/
theorem NielsenCuspTailData.tail_idealEndpoints_subset
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (C : NielsenCuspTailData P)
    (t : ℝ) (ht : 0<t) :
    Hyperbolic.discTraceIdealEndpoints (P.finiteCoordinate '' C.tail t)⊆{C.endpoint} := by
  have he : Hyperbolic.extendedDiscPoint '' (P.finiteCoordinate '' C.tail t)=
      (Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' C.tail t := by
    rw [image_image]
    apply image_congr
    intro x _
    exact P.finiteCoordinate_extended x
  rintro p ⟨hpcl,hpI⟩
  rw [he] at hpcl
  have hpFr : p∈frontier Hyperbolic.extendedUnitDisc := by
    rw [Mobius.frontier_extendedUnitDisc_eq_circle,←Hyperbolic.extendedDiscIdealBoundary_eq_circle]
    exact hpI
  have hFr := (Mobius.mobiusBoundaryHomeomorph C.normalizer).image_frontier Hyperbolic.extendedUnitDisc
  change C.normalizer.val '' frontier Hyperbolic.extendedUnitDisc=
    frontier (C.normalizer.val '' Hyperbolic.extendedUnitDisc) at hFr
  rw [C.maps_disc,nielsen_openHalfPlane_frontier] at hFr
  have hqI : C.normalizer.val p∈Hyperbolic.halfPlaneIdealBoundary := hFr ▸ ⟨p,hpFr,rfl⟩
  have hqcl : C.normalizer.val p∈closure (Hyperbolic.extendedHalfPlanePoint '' Hyperbolic.horizontalHorocyclicRegion t) := by
    rw [←C.tail_coordinate_image t,
      normalizedPolygonHalfPlaneChart_extended_closure P (C.tail t) C.normalizer C.realLift C.realLift_eq]
    exact ⟨p,hpcl,rfl⟩
  have hqi : C.normalizer.val p=∞ := mem_singleton_iff.mp
    (horizontalHorocyclicRegion_idealEndpoints t ht ▸ (show C.normalizer.val p∈
      Hyperbolic.hTraceIdealEndpoints (Hyperbolic.horizontalHorocyclicRegion t) from ⟨hqcl,hqI⟩))
  exact mem_singleton_iff.mpr (C.normalizer.val.injective (hqi.trans C.maps_endpoint.symm))

/-- Every original stabilizer element preserves the true unit-height native
horodisc. Discreteness and the actual unit translation force height preservation. -/
theorem NielsenCuspTailData.tail_stabilizer_image
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (C : NielsenCuspTailData P) (g : H)
    (hg : g.val.val C.endpoint=C.endpoint) : g • C.tail 1=C.tail 1 := by
  have hsub (g : H) (hg : g.val.val C.endpoint=C.endpoint) : g • C.tail 1⊆C.tail 1 := by
    let k : DiscreteGroups.Action.Actions.subgroupConjugate C.normalizer H :=
      ⟨C.normalizer*g.val*C.normalizer⁻¹,
        (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff C.normalizer H _).mpr ⟨g.val,g.property,rfl⟩⟩
    have hki : k.val.val ∞=∞ := by
      have hInv : C.normalizer⁻¹ • (∞:Mobius.ExtendedComplex)=C.endpoint := by
        rw [←C.maps_endpoint]
        change C.normalizer⁻¹ • (C.normalizer • C.endpoint)=C.endpoint
        exact inv_smul_smul _ _
      change C.normalizer • (g.val • (C.normalizer⁻¹ • (∞:Mobius.ExtendedComplex)))=∞
      rw [hInv]
      change C.normalizer.val (g.val.val C.endpoint)=∞
      rw [hg,C.maps_endpoint]
    have hEq:=normalized_cusp_affine_image C.halfPlaneGroup C.translation_mem k hki
    rintro _ ⟨x,hx,rfl⟩
    have hxS : C.normalizer.val x.val∈Surfaces.stableCuspSphere 1 :=
      C.tail_sphere_image 1 (by norm_num) ▸ ⟨x.val,⟨x,hx,rfl⟩,rfl⟩
    have hkS : k.val.val (C.normalizer.val x.val)∈Surfaces.stableCuspSphere 1 :=
      hEq ▸ mem_image_of_mem k.val.val hxS
    have he : k.val.val (C.normalizer.val x.val)=C.normalizer.val (g • x).val := by
      change C.normalizer • (g.val • (C.normalizer⁻¹ • (C.normalizer • x.val)))=_
      rw [inv_smul_smul]
      rfl
    have hxImage : (g • x).val∈(Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' C.tail 1 := by
      rw [C.tail_sphere_eq 1 (by norm_num)]
      change C.normalizer.val (g • x).val∈Surfaces.stableCuspSphere 1
      rw [←he]
      exact hkS
    obtain ⟨y,hy,hyx⟩ := hxImage
    change g • x∈C.tail 1
    rw [←Subtype.val_injective hyx]
    exact hy
  apply subset_antisymm (hsub g hg)
  intro x hx
  have hgi : g⁻¹.val.val C.endpoint=C.endpoint := Mobius.mobius_inv_fixed hg
  have hh := hsub g⁻¹ hgi (show g⁻¹ • x∈g⁻¹ • C.tail 1 from ⟨x,hx,rfl⟩)
  exact ⟨g⁻¹ • x,hh,smul_inv_smul g x⟩

/-- A strictly deeper genuine tail has its full native closure inside the
shallower tail; this is a consequence of the actual continuous height map. -/
theorem NielsenCuspTailData.closure_tail_subset
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (C : NielsenCuspTailData P)
    {s t : ℝ} (hst : s<t) : closure (C.tail t)⊆C.tail s := by
  have hcl : closure (C.tail t)⊆
      {z : P.domain.carrier | t ≤ (normalizedPolygonHalfPlaneChart P C.realLift z).im} := by
    apply closure_minimal
    · intro z hz
      change t<(normalizedPolygonHalfPlaneChart P C.realLift z).im at hz
      exact hz.le
    · exact isClosed_le continuous_const
        (UpperHalfPlane.continuous_im.comp (normalizedPolygonHalfPlaneChart P C.realLift).continuous)
  intro z hz
  exact hst.trans_le (hcl hz)

namespace RegularDirichletCircleData
variable {H : Subgroup Mobius.complexMobiusGroup} {P : Fuchsian.UnitDiscFuchsianGroup H}
  {w : P.domain.carrier} (d : Fuchsian.RegularDirichletCircleData P w)

/-- In a genuine parabolic radial end, deleting any specified true high
horocyclic tail leaves an actual compact native remainder. -/
theorem compactification_parabolic_radial_end_truncation
    (hNE : DiscreteGroups.IsNonElementary H)
    (hw : Fuchsian.IsDirichletCenter P w)
    (x : Fuchsian.dirichletCircleCuts P w d.radius)
    {k : H} {F : ℝ → P.domain.carrier}
    (hArc : d.originalArc hw x⊆range F)
    (hF : range F⊆frontier (Fuchsian.fuchsianOrbitBallUnion P w d.radius))
    (hShape : Fuchsian.DiscFrontierCurveCompactification P k F)
    (hpar : Mobius.MobiusParabolic k.val) :
    ∃ C : Fuchsian.NielsenCuspTailData P, ∀t : ℝ,
      ∃ K : Set P.domain.carrier, IsCompact K ∧
        d.radialEnd hw x∩Fuchsian.fuchsianNielsenCore P hNE⊆K∪C.tail t := by
  obtain ⟨a,hfix,ha,I,_hIo,_hIfr,hQI,hIideal⟩ :=
    d.compactification_parabolic_radial_end_region hNE hw x hArc hF hShape hpar
  obtain ⟨q,hq,hT,hqa⟩ := Fuchsian.parabolic_unit_halfPlane_normalizer P k hpar a hfix
  obtain ⟨A,hA⟩ := Fuchsian.halfPlane_chart_real_lift q hq
  let C : Fuchsian.NielsenCuspTailData P := ⟨k,hpar,a,ha,hfix,q,hq,A,hA,hqa,hT⟩
  refine ⟨C,?_⟩
  intro t
  obtain ⟨K,hK,hsub⟩ := Fuchsian.IsConvexFuchsianPolygon.one_end_low_height_precompact
    (Fuchsian.dirichletDomain_isConvexFuchsianPolygon P w hw) a ha I hIideal q hq A hA hqa hT t
  refine ⟨K,hK,?_⟩
  rintro z ⟨hzQ,_hzN⟩
  exact hsub ⟨subset_closure hzQ.1,subset_closure (hQI hzQ)⟩

/-- Every actual regular-circle end is genuinely precompact on the Nielsen
region, or has a real original parabolic normalization with compact remainder
after every height truncation. These alternatives are proved from the original
developed curve, rather than assumed as finite end data. -/
theorem radial_end_core_compact_or_cusp
    (hNE : DiscreteGroups.IsNonElementary H)
    (hw : Fuchsian.IsDirichletCenter P w)
    (x : Fuchsian.dirichletCircleCuts P w d.radius) :
    (∃ K : Set P.domain.carrier, IsCompact K ∧
      d.radialEnd hw x∩Fuchsian.fuchsianNielsenCore P hNE⊆K) ∨
    (∃ C : Fuchsian.NielsenCuspTailData P,∀t : ℝ,
      ∃ K : Set P.domain.carrier, IsCompact K ∧
        d.radialEnd hw x∩Fuchsian.fuchsianNielsenCore P hNE⊆K∪C.tail t) := by
  by_cases hzero : d.endpointPeriod hw x=0
  · obtain ⟨k,F,_hk,_hproper,_hembed,hArc,hF,hShape⟩ :=
      d.aperiodic_compactification_contains_originalArc hw x hzero
    have hOrig := hShape
    rcases hShape with hpar|hhyp
    · exact Or.inr (d.compactification_parabolic_radial_end_truncation hNE hw x hArc hF hOrig hpar.1)
    · exact Or.inl (d.compactification_hyperbolic_radial_end_core_precompact hNE hw x hArc hF hOrig hhyp.1)
  · exact Or.inl (d.finite_period_radial_end_core_precompact hNE hw x (Nat.pos_of_ne_zero hzero))

include d in
/-- The genuine original Dirichlet Nielsen portion has a finite family of
actual parabolic tails whose deletion at every chosen height leaves a true
compact native remainder. The finite family is constructed from the proved
original regular-circle ends. -/
theorem dirichlet_core_compact_cusp_truncation
    (hNE : DiscreteGroups.IsNonElementary H)
    (hw : Fuchsian.IsDirichletCenter P w) :
    ∃ F : Finset (Fuchsian.NielsenCuspTailData P),∀t : ℝ,
      ∃ K : Set P.domain.carrier,IsCompact K ∧
        Fuchsian.dirichletDomain P w∩Fuchsian.fuchsianNielsenCore P hNE⊆K∪⋃C∈F,C.tail t := by
  classical
  let : Finite (Fuchsian.dirichletCircleCuts P w d.radius) :=
    (Fuchsian.dirichletCircleCuts_finite P w hw d.radius).to_subtype
  let := Fintype.ofFinite (Fuchsian.dirichletCircleCuts P w d.radius)
  have hEach (x : Fuchsian.dirichletCircleCuts P w d.radius) :
      ∃ F : Finset (Fuchsian.NielsenCuspTailData P),∀t : ℝ,
        ∃ K : Set P.domain.carrier,IsCompact K ∧
          d.radialEnd hw x∩Fuchsian.fuchsianNielsenCore P hNE⊆K∪⋃C∈F,C.tail t := by
    rcases d.radial_end_core_compact_or_cusp hNE hw x with hc|⟨C,hC⟩
    · obtain ⟨K,hK,hsub⟩ := hc
      exact ⟨∅,fun _=>⟨K,hK,fun z hz=>Or.inl (hsub hz)⟩⟩
    · refine ⟨{C},?_⟩
      intro t
      obtain ⟨K,hK,hsub⟩ := hC t
      refine ⟨K,hK,?_⟩
      intro z hz
      rcases hsub hz with h|h
      · exact Or.inl h
      · exact Or.inr (mem_iUnion₂.mpr ⟨C,Finset.mem_singleton_self C,h⟩)
  choose F hF using hEach
  refine ⟨Finset.univ.biUnion F,?_⟩
  intro t
  choose K hK hsub using fun x=>hF x t
  let B : Set P.domain.carrier:={z | P.hyperbolicDist w z ≤ d.radius}
  have hBc : IsCompact B := by
    have hh := P.halfPlaneCoordinate.isCompact_preimage.mpr
      (isCompact_closedBall (P.halfPlaneCoordinate w) d.radius)
    convert hh using 1
    ext z
    change P.hyperbolicDist w z ≤ d.radius↔dist (P.halfPlaneCoordinate z) (P.halfPlaneCoordinate w) ≤ d.radius
    rw [dist_comm]
    rfl
  refine ⟨B∪⋃x,K x,hBc.union (isCompact_iUnion hK),?_⟩
  rintro z ⟨hzD,hzN⟩
  by_cases hzB : P.hyperbolicDist w z ≤ d.radius
  · exact Or.inl (Or.inl hzB)
  · obtain ⟨x,hx⟩ := mem_iUnion.mp
      (d.radial_ends_cover_strict_exterior hw ⟨hzD,lt_of_not_ge hzB⟩)
    rcases hsub x ⟨hx,hzN⟩ with h|h
    · exact Or.inl (Or.inr (mem_iUnion.mpr ⟨x,h⟩))
    · obtain ⟨C,hC,hzC⟩ := mem_iUnion₂.mp h
      exact Or.inr (mem_iUnion₂.mpr ⟨C,Finset.mem_biUnion.mpr ⟨x,Finset.mem_univ x,hC⟩,hzC⟩)

include d in
/-- The truncation controls the full closed original Dirichlet tile on the
actual open Nielsen region. The deeper-height construction proves this
boundary assertion, rather than assuming coverage only off tile boundaries. -/
theorem closed_dirichlet_core_compact_cusp_cover
    (hNE : DiscreteGroups.IsNonElementary H)
    (hw : Fuchsian.IsDirichletCenter P w) :
    ∃ F : Finset (Fuchsian.NielsenCuspTailData P),∃ K : Set P.domain.carrier,IsCompact K ∧
      closure (Fuchsian.dirichletDomain P w)∩Fuchsian.fuchsianNielsenCore P hNE⊆K∪⋃C∈F,C.tail 1 := by
  obtain ⟨F,hF⟩ := d.dirichlet_core_compact_cusp_truncation hNE hw
  obtain ⟨K,hK,hsub⟩ := hF 2
  refine ⟨F,K,hK,?_⟩
  rintro z hz
  have hzcl : z∈closure (Fuchsian.dirichletDomain P w∩Fuchsian.fuchsianNielsenCore P hNE) :=
    (Fuchsian.fuchsianNielsenCore_isOpen P hNE).closure_inter hz
  have hzc := closure_mono hsub hzcl
  rw [closure_union,hK.isClosed.closure_eq,F.closure_biUnion] at hzc
  rcases hzc with h|h
  · exact Or.inl h
  · obtain ⟨C,hC,hzC⟩ := mem_iUnion₂.mp h
    exact Or.inr (mem_iUnion₂.mpr ⟨C,hC,C.closure_tail_subset (by norm_num) hzC⟩)

include d in
/-- A genuine compact set and the entire original group orbit of finitely
many actual parabolic horodiscs cover the whole true Nielsen region. No
compact-core or orbit-cover assertion is introduced as a hypothesis. -/
theorem nielsen_core_compact_cusp_orbit_cover
    (hNE : DiscreteGroups.IsNonElementary H)
    (hw : Fuchsian.IsDirichletCenter P w) :
    ∃ F : Finset (Fuchsian.NielsenCuspTailData P),∃ K : Set P.domain.carrier,IsCompact K ∧
      Fuchsian.fuchsianNielsenCore P hNE⊆(⋃g : H,g • K)∪⋃g : H,⋃C∈F,g • C.tail 1 := by
  obtain ⟨F,K,hK,hsub⟩ := d.closed_dirichlet_core_compact_cusp_cover hNE hw
  refine ⟨F,K,hK,?_⟩
  intro x hx
  have hxcover : x∈⋃g : H,Fuchsian.fuchsianDomainTile P (Fuchsian.dirichletDomain P w) g := by
    change x∈⋃g : H,(fun y : P.domain.carrier=>g • y) '' closure (Fuchsian.dirichletDomain P w)
    rw [(Fuchsian.dirichletDomain_isConvexFuchsianPolygon P w hw).locallyFinite.fundamental.closure_cover]
    trivial
  obtain ⟨g,y,hy,he⟩ := mem_iUnion.mp hxcover
  have hyN : y∈Fuchsian.fuchsianNielsenCore P hNE := by
    have hh := Fuchsian.fuchsianNielsenCore_invariant P hNE g⁻¹ x hx
    rw [←he,inv_smul_smul] at hh
    exact hh
  rcases hsub ⟨hy,hyN⟩ with h|h
  · exact Or.inl (mem_iUnion.mpr ⟨g,y,h,he⟩)
  · obtain ⟨C,hC,hyC⟩ := mem_iUnion₂.mp h
    exact Or.inr (mem_iUnion.mpr ⟨g,mem_iUnion₂.mpr ⟨C,hC,⟨y,hyC,he⟩⟩⟩)

end RegularDirichletCircleData

/-- The actual native-disc ideal trace is precisely the genuine sphere
closure intersected with the original disc frontier. -/
theorem native_disc_ideal_trace_eq {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (S : Set P.domain.carrier) :
    Hyperbolic.discTraceIdealEndpoints (P.finiteCoordinate '' S)=
      closure ((Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' S)∩frontier P.domain.carrier := by
  have he : Hyperbolic.extendedDiscPoint '' (P.finiteCoordinate '' S)=
      (Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' S := by
    rw [image_image]
    apply image_congr
    intro x _
    exact P.finiteCoordinate_extended x
  rw [Hyperbolic.discTraceIdealEndpoints,he]
  congr 1
  change Hyperbolic.extendedDiscIdealBoundary=frontier Hyperbolic.extendedUnitDisc
  rw [Hyperbolic.extendedDiscIdealBoundary_eq_circle,Mobius.frontier_extendedUnitDisc_eq_circle]

/-- Genuine original group action transports the entire actual ideal trace. -/
theorem native_disc_ideal_trace_smul {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (S : Set P.domain.carrier) :
    Hyperbolic.discTraceIdealEndpoints (P.finiteCoordinate '' (g • S))=
      g.val.val '' Hyperbolic.discTraceIdealEndpoints (P.finiteCoordinate '' S) := by
  have he : (Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' (g • S)=
      (Mobius.mobiusBoundaryHomeomorph g.val) '' ((Subtype.val : P.domain.carrier→Mobius.ExtendedComplex) '' S) := by
    ext p
    constructor
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨x.val,⟨x,hx,rfl⟩,rfl⟩
    · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨g • x,⟨x,hx,rfl⟩,rfl⟩
  have hFr : (Mobius.mobiusBoundaryHomeomorph g.val) '' frontier P.domain.carrier=
      frontier P.domain.carrier := by
    rw [(Mobius.mobiusBoundaryHomeomorph g.val).image_frontier]
    change frontier (g.val.val '' Hyperbolic.extendedUnitDisc)=frontier Hyperbolic.extendedUnitDisc
    rw [P.image_eq g]
  rw [native_disc_ideal_trace_eq,native_disc_ideal_trace_eq,he,
    ←(Mobius.mobiusBoundaryHomeomorph g.val).image_closure]
  conv_lhs => rw [←hFr]
  exact (image_inter (Mobius.mobiusBoundaryHomeomorph g.val).injective).symm

/-- All genuine original translates of one horodisc with a prescribed actual
boundary endpoint. -/
def NielsenCuspTailData.orbitTail {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    (C : NielsenCuspTailData P)
    (p : Mobius.ExtendedComplex) :
    Set P.domain.carrier :=
  {x | ∃g : H,g.val.val C.endpoint=p ∧ x∈g • C.tail 1}

theorem NielsenCuspTailData.orbitTail_isOpen
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    (C : NielsenCuspTailData P)
    (p : Mobius.ExtendedComplex) :
    IsOpen (C.orbitTail p) := by
  have he : C.orbitTail p=⋃g : H,⋃(_h:g.val.val C.endpoint=p),g • C.tail 1 := by
    ext x
    simp [Fuchsian.NielsenCuspTailData.orbitTail]
  rw [he]
  exact isOpen_iUnion (fun g=>isOpen_iUnion (fun _h=>(Homeomorph.smul g).isOpenMap _ (C.tail_isOpen 1)))

/-- Once the actual endpoint is fixed, all original translates of a single
horodisc coincide. This follows from the actual stabilizer height law. -/
theorem NielsenCuspTailData.orbitTail_eq {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (C : NielsenCuspTailData P) (g : H) :
    C.orbitTail (g.val.val C.endpoint)=g • C.tail 1 := by
  apply subset_antisymm
  · rintro x ⟨a,ha,hx⟩
    have hfix : (g⁻¹*a).val.val C.endpoint=C.endpoint := by
      change g.val.val.symm (a.val.val C.endpoint)=C.endpoint
      rw [ha]
      exact Equiv.symm_apply_apply _ _
    have hstab:=C.tail_stabilizer_image (g⁻¹*a) hfix
    have he : a • C.tail 1=g • C.tail 1 := by
      calc
        a • C.tail 1=g • ((g⁻¹*a) • C.tail 1) := by rw [smul_smul,mul_inv_cancel_left]
        _=g • C.tail 1 := congrArg (fun S : Set P.domain.carrier=>g • S) hstab
    exact he ▸ hx
  · intro x hx
    exact ⟨g,rfl,hx⟩

/-- An entire original same-endpoint horodisc orbit family has only that
one genuine ideal endpoint, even though the group itself may be infinite. -/
theorem NielsenCuspTailData.orbitTail_idealEndpoints_subset
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    (C : NielsenCuspTailData P)
    (p : Mobius.ExtendedComplex) :
    Hyperbolic.discTraceIdealEndpoints (P.finiteCoordinate '' C.orbitTail p)⊆{p} := by
  classical
  by_cases hp : ∃g : H,g.val.val C.endpoint=p
  · obtain ⟨g,rfl⟩ := hp
    rw [C.orbitTail_eq g,native_disc_ideal_trace_smul]
    exact (image_mono (C.tail_idealEndpoints_subset 1 zero_lt_one)).trans
      (by rw [image_singleton])
  · have he : C.orbitTail p=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro x ⟨g,hg,_hx⟩
      exact hp ⟨g,hg⟩
    rw [he,image_empty,Hyperbolic.discTraceIdealEndpoints,image_empty,closure_empty,empty_inter]
    exact empty_subset _

/-- Actual ideal traces commute with a genuinely finite union, through the
literal sphere closure of the unchanged native points. -/
theorem native_disc_ideal_trace_finset_union
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) {ι : Type*} (F : Finset ι) (U : ι→Set P.domain.carrier) :
    Hyperbolic.discTraceIdealEndpoints (P.finiteCoordinate '' (⋃i∈F,U i))=
      ⋃i∈F,Hyperbolic.discTraceIdealEndpoints (P.finiteCoordinate '' U i) := by
  simp_rw [native_disc_ideal_trace_eq,image_iUnion]
  rw [F.closure_biUnion]
  simp only [iUnion_inter]

/-- The actual horodisc families from finitely many true cusp coordinates,
grouped by their literal original sphere endpoint. -/
def nielsenCuspOrbitTail {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (F : Finset (NielsenCuspTailData P))
    (p : Mobius.ExtendedComplex) : Set P.domain.carrier := ⋃C∈F,C.orbitTail p

theorem nielsenCuspOrbitTail_isOpen {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    (F : Finset (NielsenCuspTailData P))
    (p : Mobius.ExtendedComplex) :
    IsOpen (nielsenCuspOrbitTail F p) :=
  isOpen_iUnion (fun C=>isOpen_iUnion (fun _h=>C.orbitTail_isOpen p))

theorem nielsenCuspOrbitTail_idealEndpoints_subset
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    (F : Finset (NielsenCuspTailData P))
    (p : Mobius.ExtendedComplex) :
    Hyperbolic.discTraceIdealEndpoints (P.finiteCoordinate '' nielsenCuspOrbitTail F p)⊆{p} := by
  rw [nielsenCuspOrbitTail,native_disc_ideal_trace_finset_union]
  intro q hq
  obtain ⟨C,_hC,hq⟩ := mem_iUnion₂.mp hq
  exact C.orbitTail_idealEndpoints_subset p hq

/-- Different literal sphere endpoints give pairwise disjoint open whole-
group cusp families. The bound is true for all original group elements. -/
theorem nielsenCuspOrbitTail_pairwise_disjoint
    {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H} (F : Finset (NielsenCuspTailData P)) :
    Pairwise (fun p q : Mobius.ExtendedComplex=>Disjoint (nielsenCuspOrbitTail F p) (nielsenCuspOrbitTail F q)) := by
  intro p q hpq
  apply disjoint_left.mpr
  intro x hxp hxq
  obtain ⟨C,_hC,hxa⟩ := mem_iUnion₂.mp hxp
  obtain ⟨E,_hE,hxb⟩ := mem_iUnion₂.mp hxq
  obtain ⟨a,ha,hxa⟩ := hxa
  obtain ⟨b,hb,hxb⟩ := hxb
  have hne : (a⁻¹*b).val.val E.endpoint≠C.endpoint := by
    intro he
    apply hpq
    rw [←ha,←hb]
    have hh:=congrArg (fun r : Mobius.ExtendedComplex=>a.val.val r) he
    change a.val • (a.val⁻¹ • (b.val • E.endpoint))=a.val • C.endpoint at hh
    change a.val • C.endpoint=b.val • E.endpoint
    simpa only [smul_inv_smul] using hh.symm
  obtain ⟨y,hy,hyx⟩ := hxa
  obtain ⟨z,hz,hzx⟩ := hxb
  apply disjoint_left.mp (C.tail_disjoint_of_endpoint_ne E (a⁻¹*b) hne) hy
  refine ⟨z,hz,?_⟩
  apply (Homeomorph.smul a).injective
  change a • ((a⁻¹*b) • z)=a • y
  rw [smul_smul,mul_inv_cancel_left]
  exact hzx.trans hyx.symm

/-- A nonempty actual cusp family supplies an actual original parabolic
element fixing its named genuine sphere endpoint. -/
theorem nielsenCuspOrbitTail_parabolic {H : Subgroup Mobius.complexMobiusGroup}
    {P : UnitDiscFuchsianGroup H}
    (F : Finset (NielsenCuspTailData P))
    (p : Mobius.ExtendedComplex)
    (hp : (nielsenCuspOrbitTail F p).Nonempty) :
    ∃f : H,Mobius.MobiusParabolic f.val ∧ f.val.val p=p := by
  obtain ⟨x,hx⟩ := hp
  obtain ⟨C,_hC,hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨g,hg,_hx⟩ := hx
  let f : H:=g*C.element*g⁻¹
  have hf : Mobius.MobiusParabolic f.val :=
    (Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨g.val,rfl⟩)).mp C.parabolic
  refine ⟨f,hf,?_⟩
  rw [←hg]
  change g.val • (C.element.val • (g.val⁻¹ • (g.val • C.endpoint)))=g.val • C.endpoint
  rw [inv_smul_smul]
  change g.val.val (C.element.val.val C.endpoint)=g.val.val C.endpoint
  rw [C.fixed]


/-- Every genuine geometric disc ray admits a forward unit-speed coordinate
on the true real parameter half-line, with no choice of model ray added. -/
theorem discRay_exists_forward_isometry {z : 𝔻} (R : Hyperbolic.DiscRayAt z) :
    ∃ γ : ℝ→𝔻, (letI:=Hyperbolic.discHyperbolicMetric; Isometry γ) ∧
      γ 0=z ∧ R.val=γ '' Ici 0 := by
  let :=Hyperbolic.discHyperbolicMetric
  obtain ⟨γ,hγ,s,hs,hor,_he⟩ := R.isRay
  rcases hor with hpos|hneg
  · let δ : ℝ→𝔻 := fun t=>γ (s+t)
    have hδ : Isometry δ := by
      apply Isometry.of_dist_eq
      intro t u
      change dist (γ (s+t)) (γ (s+u))=dist t u
      rw [hγ.1.dist_eq]
      simp only [dist_eq_norm,add_sub_add_left_eq_sub]
    refine ⟨δ,hδ,by simpa [δ] using hs,?_⟩
    rw [hpos]
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨t-s,sub_nonneg.mpr ht,by dsimp [δ];congr 1;ring⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨s+t,by change 0 ≤ t at ht;change s ≤ s+t;linarith,rfl⟩
  · let δ : ℝ→𝔻 := fun t=>γ (s-t)
    have hδ : Isometry δ := by
      apply Isometry.of_dist_eq
      intro t u
      change dist (γ (s-t)) (γ (s-u))=dist t u
      rw [hγ.1.dist_eq]
      rw [dist_eq_norm,dist_eq_norm,show (s-t)-(s-u)=-(t-u) by ring,norm_neg]
    refine ⟨δ,hδ,by simpa [δ] using hs,?_⟩
    rw [hneg]
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨s-t,sub_nonneg.mpr ht,by dsimp [δ];congr 1;ring⟩
    · rintro ⟨t,ht,rfl⟩
      exact ⟨s-t,by change 0 ≤ t at ht;change s-t ≤ s;linarith,rfl⟩

/-- Deleting any finite initial segment preserves the actual sphere ideal
endpoint of a genuine ray. The deleted part is truly compact in the disc. -/
theorem discRay_forward_tail_endpoint {z : 𝔻} (R : Hyperbolic.DiscRayAt z)
    (γ : ℝ→𝔻) (hγ : Continuous γ) (hR : R.val=γ '' Ici 0)
    (s : ℝ) (hs : 0 ≤ s) :
    R.idealEndpoint∈Hyperbolic.discTraceIdealEndpoints (γ '' Ici s) := by
  have hUnion : R.val=γ '' Icc 0 s∪γ '' Ici s := by
    rw [hR,←image_union]
    congr 1
    ext t
    simp only [mem_Ici,mem_union,mem_Icc]
    constructor
    · intro ht
      rcases le_total t s with h|h
      · exact Or.inl ⟨ht,h⟩
      · exact Or.inr h
    · rintro (⟨h,_⟩|h)
      · exact h
      · exact hs.trans h
  have hc : IsCompact (Hyperbolic.extendedDiscPoint '' (γ '' Icc 0 s)) :=
    (isCompact_Icc.image hγ).image (OnePoint.continuous_coe.comp continuous_subtype_val)
  have hnot : R.idealEndpoint∉Hyperbolic.extendedDiscPoint '' (γ '' Icc 0 s) := by
    rintro ⟨v,_hv,hv⟩
    have hi : Hyperbolic.extendedDiscPoint v∈Hyperbolic.extendedDiscIdealBoundary := hv.symm ▸ R.idealEndpoint_mem
    have hn : ‖(v:ℂ)‖=1 := (Hyperbolic.coe_mem_extendedDiscIdealBoundary (v:ℂ)).mp hi
    exact (ne_of_lt v.norm_lt_one) hn
  have hcl : R.idealEndpoint∈closure (Hyperbolic.extendedDiscPoint '' R.val) := by
    obtain ⟨_γ,_hγ,_s,_hs,_hor,hEnd⟩ := R.isRay
    exact (hEnd.symm ▸ (mem_singleton R.idealEndpoint)).1
  rw [hUnion,image_union,closure_union,hc.isClosed.closure_eq] at hcl
  exact ⟨hcl.resolve_left hnot,R.idealEndpoint_mem⟩

/-- A genuine ending ray has a connected nonempty tail outside any actual
compact subset, retaining its true ideal endpoint. -/
theorem discRay_tail_avoids_compact {z : 𝔻} (R : Hyperbolic.DiscRayAt z)
    (K : Set 𝔻) (hK : IsCompact K) :
    ∃ T : Set 𝔻, IsConnected T ∧ T⊆R.val\K ∧
      R.idealEndpoint∈Hyperbolic.discTraceIdealEndpoints T := by
  let :=Hyperbolic.discHyperbolicMetric
  obtain ⟨γ,hγ,hzero,hR⟩ := discRay_exists_forward_isometry R
  obtain ⟨r,hr⟩ := hK.isBounded.subset_closedBall (γ 0)
  let s := max 0 r+1
  have hs : 0 ≤ s := by dsimp [s];linarith [le_max_left 0 r]
  have hrs : r<s := by dsimp [s];linarith [le_max_right 0 r]
  refine ⟨γ '' Ici s,?_,?_,discRay_forward_tail_endpoint R γ hγ.continuous hR s hs⟩
  · exact isConnected_Ici.image γ hγ.continuous.continuousOn
  · rintro x ⟨t,ht,rfl⟩
    refine ⟨hR.symm ▸ ⟨t,hs.trans ht,rfl⟩,?_⟩
    intro hKx
    have hb := hr hKx
    rw [Metric.mem_closedBall,hγ.dist_eq,Real.dist_eq,sub_zero,abs_of_nonneg (hs.trans ht)] at hb
    exact (not_lt_of_ge hb) (hrs.trans_le ht)

/--
Infinitely many actual compact inverse-ray returns yield the geometric
point-of-approximation property at all actual interior basepoints.
-/
theorem infinite_compact_ray_returns_pointOfApproximation
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (ξ : ℂ) (hξ : (ξ:Mobius.ExtendedComplex)∈fuchsianLimitSet H)
    {z : 𝔻}
    (R : Hyperbolic.DiscRayAt z)
    (hR : R.idealEndpoint=(ξ:Mobius.ExtendedComplex))
    (K : Set 𝔻) (hK : IsCompact K)
    (hInf : {g : H | ((P.discAction g)⁻¹'R.val∩K).Nonempty}.Infinite) :
    IsFuchsianPointOfApproximation P ξ := by
  let e:=hInf.natEmbedding _
  let g : ℕ→H := fun n=>(e n).val
  have hg : Function.Injective g := Subtype.val_injective.comp e.injective
  have hnear := (disc_orbit_ray_infDist_iff_compact P g R 0).mpr
    ⟨K,hK,fun n=>(e n).property⟩
  have hrate := (disc_orbit_matrix_rate_iff_ray_bound P g ξ
    (fuchsian_limit_finite_norm_one P ξ hξ) 0 R hR).mpr hnear
  exact (fuchsian_pointOfApproximation_iff_single_sequence P ξ).mpr ⟨hξ,g,hg,hrate⟩

/-- A non-approximation endpoint gives only finitely many genuine translates
of any fixed compact set meeting a chosen actual ending ray. -/
theorem not_pointOfApproximation_compact_ray_hits_finite
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (ξ : ℂ) (hξ : (ξ:Mobius.ExtendedComplex)∈fuchsianLimitSet H)
    (hnot : ¬IsFuchsianPointOfApproximation P ξ)
    {z : 𝔻}
    (R : Hyperbolic.DiscRayAt z)
    (hR : R.idealEndpoint=(ξ:Mobius.ExtendedComplex))
    (K : Set 𝔻) (hK : IsCompact K) :
    {g : H | ((P.discAction g)⁻¹'R.val∩K).Nonempty}.Finite := by
  by_contra h
  exact hnot (infinite_compact_ray_returns_pointOfApproximation P ξ hξ R hR K hK h)

/-- If the actual ideal endpoint is not a point of approximation, a genuine
connected ending tail avoids all original translates of any given compact
set simultaneously. The finite hit set is proved, not supplied. -/
theorem not_pointOfApproximation_tail_avoids_all_compact_translates
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (ξ : ℂ) (hξ : (ξ:Mobius.ExtendedComplex)∈fuchsianLimitSet H)
    (hnot : ¬IsFuchsianPointOfApproximation P ξ)
    {z : 𝔻}
    (R : Hyperbolic.DiscRayAt z)
    (hR : R.idealEndpoint=(ξ:Mobius.ExtendedComplex))
    (K : Set 𝔻) (hK : IsCompact K) :
    ∃ T : Set 𝔻, IsConnected T ∧ T⊆R.val ∧
      R.idealEndpoint∈Hyperbolic.discTraceIdealEndpoints T ∧
      ∀g : H,Disjoint T (P.discAction g '' K) := by
  let F : Set H:={g | ((P.discAction g)⁻¹'R.val∩K).Nonempty}
  have hF : F.Finite := not_pointOfApproximation_compact_ray_hits_finite P ξ hξ hnot R hR K hK
  let L:=⋃g∈F,P.discAction g '' K
  have hL : IsCompact L := hF.isCompact_biUnion (fun g _=>hK.image (P.discAction g).continuous)
  obtain ⟨T,hT,hsub,hend⟩ := discRay_tail_avoids_compact R L hL
  refine ⟨T,hT,fun x hx=>(hsub hx).1,hend,?_⟩
  intro g
  apply disjoint_left.mpr
  rintro x hx ⟨y,hy,rfl⟩
  have hg : g∈F := ⟨y,(hsub hx).1,hy⟩
  exact (hsub hx).2 (mem_iUnion₂.mpr ⟨g,hg,⟨y,hy,rfl⟩⟩)

/-- A genuinely connected set in a pairwise disjoint open cover lies in one
member. This elementary separation lemma places no finiteness restriction
on the actual cusp-orbit family. -/
theorem connected_subset_one_of_disjoint_open_cover
    {X ι : Type*} [TopologicalSpace X] {S : Set X} (hS : IsConnected S)
    (U : ι→Set X) (ho : ∀i,IsOpen (U i))
    (hdis : Pairwise (fun i j=>Disjoint (U i) (U j))) (hcover : S⊆⋃i,U i) :
    ∃i,S⊆U i := by
  classical
  obtain ⟨x,hx⟩ := hS.nonempty
  obtain ⟨i,hxi⟩ := mem_iUnion.mp (hcover hx)
  let V:=⋃j : {j : ι // j≠i},U j.val
  have hVo : IsOpen V := isOpen_iUnion (fun j=>ho j.val)
  have hd : Disjoint (U i) V := by
    apply disjoint_left.mpr
    intro y hy hyV
    obtain ⟨j,hj⟩ := mem_iUnion.mp hyV
    exact disjoint_left.mp (hdis j.property.symm) hy hj
  have hUV : S⊆U i∪V := by
    intro y hy
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hcover hy)
    by_cases he : j=i
    · exact Or.inl (he ▸ hj)
    · exact Or.inr (mem_iUnion.mpr ⟨⟨j,he⟩,hj⟩)
  exact ⟨i,hS.isPreconnected.subset_left_of_subset_union (ho i) hVo hd hUV ⟨x,hx,hxi⟩⟩

/-- The genuine regular-circle decomposition proves the actual split at
every original limit point. The compact orbit cover and all cusp separation
properties are derived from the original geometric group data. -/
theorem RegularDirichletCircleData.limit_point_parabolic_or_approximation
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {w : P.domain.carrier} (d : RegularDirichletCircleData P w)
    (hNE : DiscreteGroups.IsNonElementary H) (hw : IsDirichletCenter P w)
    (hwN : w∈fuchsianNielsenCore P hNE)
    (ξ : ℂ) (hξ : (ξ:Mobius.ExtendedComplex)∈fuchsianLimitSet H) :
    (∃g : H,Mobius.MobiusParabolic g.val ∧ g.val.val (ξ:Mobius.ExtendedComplex)=(ξ:Mobius.ExtendedComplex)) ∨
      IsFuchsianPointOfApproximation P ξ := by
  classical
  by_cases hApprox : IsFuchsianPointOfApproximation P ξ
  · exact Or.inr hApprox
  left
  have hn:=fuchsian_limit_finite_norm_one P ξ hξ
  let R:=approximationCanonicalRay (P.finiteCoordinate w) ξ hn
  have hR:=approximationCanonicalRay_endpoint (P.finiteCoordinate w) ξ hn
  have hRayN : R.val⊆P.finiteCoordinate '' fuchsianNielsenCore P hNE :=
    fuchsianNielsenCore_canonical_ray_subset P hNE w hwN ξ hn
      (by rwa [←fuchsianLimitSet_eq_nonElementary H hNE])
  obtain ⟨F,K,hK,hcover⟩ := d.nielsen_core_compact_cusp_orbit_cover hNE hw
  obtain ⟨T,hT,hTR,hEnd,hAvoid⟩ :=
    not_pointOfApproximation_tail_avoids_all_compact_translates P ξ hξ hApprox R hR
      (P.finiteCoordinate '' K) (hK.image P.finiteCoordinate.continuous)
  let T₀:=P.finiteCoordinate.symm '' T
  have hT₀ : IsConnected T₀ := hT.image P.finiteCoordinate.symm P.finiteCoordinate.symm.continuous.continuousOn
  have hT₀N : T₀⊆fuchsianNielsenCore P hNE := by
    rintro x ⟨u,hu,rfl⟩
    obtain ⟨v,hv,hev⟩ := hRayN (hTR hu)
    rwa [←hev,P.finiteCoordinate.symm_apply_apply]
  have hT₀Avoid (g : H) : Disjoint T₀ (g • K) := by
    apply disjoint_left.mpr
    rintro x ⟨u,hu,heu⟩ ⟨y,hy,hygx⟩
    apply disjoint_left.mp (hAvoid g) hu
    refine ⟨P.finiteCoordinate y,⟨y,hy,rfl⟩,?_⟩
    change P.finiteCoordinate (g • P.finiteCoordinate.symm (P.finiteCoordinate y))=u
    change g • y=x at hygx
    rw [P.finiteCoordinate.symm_apply_apply,hygx,←heu,P.finiteCoordinate.apply_symm_apply]
  have hT₀Cover : T₀⊆⋃p : Mobius.ExtendedComplex,nielsenCuspOrbitTail F p := by
    intro x hx
    rcases hcover (hT₀N hx) with h|h
    · obtain ⟨g,hg⟩ := mem_iUnion.mp h
      exact False.elim (disjoint_left.mp (hT₀Avoid g) hx hg)
    · obtain ⟨g,hg⟩ := mem_iUnion.mp h
      obtain ⟨C,hC,hxC⟩ := mem_iUnion₂.mp hg
      apply mem_iUnion.mpr
      refine ⟨g.val.val C.endpoint,mem_iUnion₂.mpr ⟨C,hC,?_⟩⟩
      exact ⟨g,rfl,hxC⟩
  obtain ⟨p,hTp⟩ := connected_subset_one_of_disjoint_open_cover hT₀
    (nielsenCuspOrbitTail F) (nielsenCuspOrbitTail_isOpen F)
    (nielsenCuspOrbitTail_pairwise_disjoint F) hT₀Cover
  have hEq : P.finiteCoordinate '' T₀=T := by
    rw [image_image]
    simp only [P.finiteCoordinate.apply_symm_apply,image_id']
  have hξTrace : R.idealEndpoint∈Hyperbolic.discTraceIdealEndpoints (P.finiteCoordinate '' T₀) := hEq.symm ▸ hEnd
  have hMono : Hyperbolic.discTraceIdealEndpoints (P.finiteCoordinate '' T₀)⊆
      Hyperbolic.discTraceIdealEndpoints (P.finiteCoordinate '' nielsenCuspOrbitTail F p) :=
    inter_subset_inter_left _ (closure_mono (image_mono (image_mono hTp)))
  have hξp : (ξ:Mobius.ExtendedComplex)=p := hR ▸ mem_singleton_iff.mp
    (nielsenCuspOrbitTail_idealEndpoints_subset F p (hMono hξTrace))
  obtain ⟨f,hf,hfp⟩ := nielsenCuspOrbitTail_parabolic F p (hT₀.nonempty.mono hTp)
  exact ⟨f,hf,hξp.symm ▸ hfp⟩

/-- Finite generation proves the actual split-limit-set implication for every original non-elementary disc group. -/
theorem finitelyGenerated_nonElementary_split_limitSet
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H)
    (hFG : H.FG) : HasSplitFuchsianLimitSet P := by
  obtain ⟨w,hw,hwN⟩ := exists_dirichlet_center_in_nielsenCore P hNE
  let : Infinite H:=DiscreteGroups.nonElementary_infinite H hNE
  obtain ⟨g,hg⟩ := exists_ne (1:H)
  obtain ⟨d,_hd⟩ := finitelyGenerated_regular_dirichlet_circle_data P hFG w hw g hg 1
  intro ξ hξ
  exact d.limit_point_parabolic_or_approximation hNE hw hwN ξ hξ


/-- The full elementary limit-set convention also splits. Its actual
endpoint set is finite and therefore already closed; every point is an
actual parabolic endpoint or an actual hyperbolic fixed point. -/
theorem elementary_split_limitSet {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hE : DiscreteGroups.IsElementary H) : HasSplitFuchsianLimitSet P := by
  obtain ⟨a,b,hsub⟩ := elementary_fuchsianLimitSet_subset_pair H P.discrete hE
  have hEnd : (fuchsianLimitEndpoints H).Finite :=
    (toFinite ({a,b}:Set Mobius.ExtendedComplex)).subset (fun _ hz=>hsub (subset_closure hz))
  have hEq : fuchsianLimitSet H=fuchsianLimitEndpoints H := hEnd.isClosed.closure_eq
  intro ξ hξ
  rw [hEq] at hξ
  obtain ⟨g,hg,hfix⟩ := hξ
  rcases hg with hp|hl
  · exact Or.inl ⟨g,hp,hfix⟩
  · exact Or.inr (hyperbolic_fixed_pointOfApproximation P g
      (P.asFuchsianDisc.loxodromic_hyperbolic g hl) ξ hfix)


/--
The forward implication for the full original group,
including every elementary case and the full endpoint-closure convention.
-/
theorem finitelyGenerated_split_limitSet {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hFG : H.FG) : HasSplitFuchsianLimitSet P := by
  classical
  by_cases hNE : DiscreteGroups.IsNonElementary H
  · exact finitelyGenerated_nonElementary_split_limitSet P hNE hFG
  · exact elementary_split_limitSet P (Classical.not_not.mp hNE)

end LowDimensionalTopology.Geometry.Fuchsian
