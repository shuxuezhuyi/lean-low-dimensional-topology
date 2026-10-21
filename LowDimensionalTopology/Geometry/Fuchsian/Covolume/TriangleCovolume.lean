/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.FiniteAreaFirstKind
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.NativeTriangleTransport
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.MobiusTriangleGroups
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PerpendicularBisectors
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory Function
open scoped UpperHalfPlane OnePoint MatrixGroups Pointwise ENNReal
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance triangleCovolumeSphereMeasurable:MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance triangleCovolumeSphereBorel:BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

/-- Every nonidentity actual native isometry has area-null fixed locus,
since it is contained in an actual hyperbolic perpendicular bisector. -/
theorem native_isometry_fixed_volume_zero (f:ℍ≃ᵢℍ) (hf:f≠1) :
    volume {z:ℍ|f z=z}=0 := by
  have hex:∃p:ℍ,f p≠p:=by
    by_contra hn
    push Not at hn
    exact hf (IsometryEquiv.ext hn)
  obtain ⟨p,hp⟩:=hex
  obtain ⟨L,hL⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_hEquidistantLine hp.symm
  apply measure_mono_null (t:=L.carrier) _ L.volume_zero
  intro z hz
  rw [hL]
  change dist z p=dist z (f p)
  calc
    dist z p = dist (f z) (f p) := (f.isometry.dist_eq z p).symm
    _ = dist z (f p) := by rw [show f z=z from hz]

/-- The original three-mirror group is countable through its actual
finite words in the finite set of original sides. -/
theorem triangleReflectionGroup_countable (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) : Countable (triangleReflectionGroup T) := by
  classical
  have hfinite:(triangleReflectionSides T).Finite:=by
    simp only [triangleReflectionSides]
    exact (finite_singleton _).insert _ |>.insert _
  let triangleCovolumeSideFinite:Finite (triangleReflectionSides T):=hfinite.to_subtype
  let W:=List (triangleReflectionSides T)
  let f:W→triangleReflectionGroup T:=fun l=>
    ⟨(l.map (fun L=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L.val)).prod,by
      apply (triangleReflectionGroup T).list_prod_mem
      intro g hg
      obtain ⟨L,_,rfl⟩:=List.mem_map.mp hg
      exact Subgroup.subset_closure ⟨L.val,L.property,rfl⟩⟩
  apply Surjective.countable (f:=f)
  intro g
  obtain ⟨l,hl,he⟩:=(triangleReflectionGroup_mem_iff_word T g.val).mp g.property
  let w:W:=l.attach.map (fun L=>⟨L.val,hl L.val L.property⟩)
  refine ⟨w,Subtype.ext ?_⟩
  change (w.map (fun L=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry
    L.val)).prod=g.val
  dsimp only [w]
  have hw:w.map (fun L=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry L.val)=
      l.map _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry:=by
    dsimp only [w]
    rw [List.map_map]
    change l.attach.map (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry ∘
      Subtype.val)=_
    rw [←List.map_map,List.attach_map_subtype_val]
  rw [hw]
  exact he

theorem native_aeFundamental_packing_volume_le {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) {D T:Set ℍ} :
    letI:=P.nativeAction
    MeasureTheory.IsFundamentalDomain H D volume →
      NullMeasurableSet T volume → Pairwise (Disjoint on fun g:H=>g•T) → volume T≤volume D := by
  let triangleCovolumeNativeAction:=P.nativeAction
  let triangleCovolumeNativeCountable:Countable H:=_root_.LowDimensionalTopology.Geometry.Mobius.discreteMobius_countable H P.discrete
  let triangleCovolumeNativeContinuous:ContinuousConstSMul H ℍ:=⟨by
      intro g
      obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL g.val (P.preserves g)
      have he:(fun z:ℍ=>g•z)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
        A:ℍ→ℍ):=funext (P.nativeAction_realSL g A hA)
      rw [he]
      exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A).continuous⟩
  let triangleCovolumeNativeInvariant:SMulInvariantMeasure H ℍ volume:=⟨by
      intro g S hS
      obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL g.val (P.preserves g)
      have he:(fun z:ℍ=>g•z)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
        A:ℍ→ℍ):=funext (P.nativeAction_realSL g A hA)
      rw [he]
      exact (show MeasurePreserving (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) volume volume from
        ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
          A).continuous.measurable,parabolic_realSL_map_volume A⟩).measure_preimage hS.nullMeasurableSet⟩
  intro hD hT hpack
  have hpair:Pairwise (AEDisjoint volume on fun g:H=>g•T∩D):=by
    intro g k hne
    exact ((hpack hne).mono inter_subset_left inter_subset_left).aedisjoint
  exact hD.measure_le_of_pairwise_disjoint hT hpair

theorem native_finite_aeArea_no_boundary_wandering {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) {D:Set ℍ} :
    letI:=P.nativeAction
    MeasureTheory.IsFundamentalDomain H D volume → volume D≠⊤ →
      ∀U:Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,IsOpen U →
      (∀g:H,g≠1→Disjoint (g.val.val '' U) U) →
      ∀p:ℝ,((p:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∉U := by
  let triangleCovolumeBoundaryNativeAction:=P.nativeAction
  intro hD harea U hU hwander p hp
  let T:=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' U
  have ho:IsOpen T:=hU.preimage _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_isOpenEmbedding.continuous
  have hpack:Pairwise (Disjoint on fun g:H=>g•T):=by
    intro g k hne
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,hgx⟩ ⟨y,hy,hky⟩
    have hkg:k⁻¹*g≠1:=by
      intro he
      apply hne
      exact (inv_mul_eq_one.mp he).symm
    have hxy:(k⁻¹*g)•x=y:=by
      have he:=congrArg (fun z:ℍ=>k⁻¹•z) (hgx.trans hky.symm)
      simpa only [mul_smul,inv_smul_smul] using he
    apply Set.disjoint_left.mp (hwander (k⁻¹*g) hkg) _ hy
    exact ⟨_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint x,hx,by rw [P.nativeAction_boundary,hxy]⟩
  have hle:=native_aeFundamental_packing_volume_le P hD ho.measurableSet.nullMeasurableSet hpack
  rw [real_boundary_open_volume_top U hU p hp] at hle
  exact harea (top_unique hle)

/-- Every actual finite real boundary point of a finite-area original
native Fuchsian surface lies in its genuine limit set. -/
theorem native_finite_aeArea_real_boundary_limit {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hH:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) {D:Set
      ℍ} :
    letI:=P.nativeAction
    MeasureTheory.IsFundamentalDomain H D volume → volume D≠⊤ →
      ∀p:ℝ,((p:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H := by
  let triangleCovolumeLimitNativeAction:=P.nativeAction
  intro hD harea p
  by_contra hpL
  have hpO:((p:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet H:=hpL
  obtain ⟨N,hN,hpN,_hcl,hsep⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.exists_invariant_disc_neighbourhood_disjoint_other_translates H hH P.discrete ((p:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hpO
  have hpF:((p:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈frontier P.asFuchsianDisc.carrier:=by
    change ((p:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    rw [nielsen_openHalfPlane_frontier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_halfPlaneIdealBoundary]
    simp
  have hfree:=ordinary_fuchsian_frontier_free P.asFuchsianDisc hH ((p:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hpF hpO
  have hwander:∀g:H,g≠1→Disjoint (g.val.val '' N) N:=by
    intro g hg
    exact (hsep g).2 (fun he=>hg (hfree g he))
  exact native_finite_aeArea_no_boundary_wandering P hD harea N hN.isOpen hwander p hpN

/-- Finite genuine area forces the full original native limit set to
fill the actual invariant-circle frontier, including infinity. -/
theorem native_finite_aeArea_firstKind {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hH:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) {D:Set
      ℍ} :
    letI:=P.nativeAction
    MeasureTheory.IsFundamentalDomain H D volume → volume D≠⊤ → P.asFuchsianDisc.IsFirstKind := by
  let triangleCovolumeFirstKindNativeAction:=P.nativeAction
  intro hD harea
  have hreal:=native_finite_aeArea_real_boundary_limit P hH hD harea
  have hInfinity:(∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H:=by
    obtain ⟨g,hg⟩:=hH.exists_move_boundary ∞
    have hi:(∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
      rw [nielsen_openHalfPlane_frontier]
      exact Or.inl rfl
    have he:g.val.val '' frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
      change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
        g.val) '' frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_
      rw [Homeomorph.image_frontier]
      exact congrArg frontier (P.preserves g)
    have hf:g.val.val ∞∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary:=by
      rw [←nielsen_openHalfPlane_frontier,←he]
      exact mem_image_of_mem _ hi
    rcases hf with hInf|⟨z,hz,hzEq⟩
    · exact False.elim (hg hInf)
    · have hzR:z=(z.re:ℂ):=by
        have hz0:z.im=0:=hz
        apply Complex.ext <;> simp [hz0]
      have hgz:g.val.val ∞=((z.re:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=hzEq.symm.trans (congrArg ((↑):ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) hzR)
      have hlim:g•(∞:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H:=by
        change g.val.val ∞∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H
        rw [hgz]
        exact hreal z.re
      have hback:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet_invariant H g⁻¹ hlim
      simpa only [inv_smul_smul] using hback
  apply Set.Subset.antisymm P.asFuchsianDisc.limitSet_subset_frontier
  rw [fuchsianLimitSet_eq_nonElementary H hH]
  intro x hx
  change x∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet at hx
  rw [nielsen_openHalfPlane_frontier] at hx
  rcases hx with rfl|⟨z,hz,rfl⟩
  · exact hInfinity
  · have hzR:z=(z.re:ℂ):=by
      have hz0:z.im=0:=hz
      apply Complex.ext <;> simp [hz0]
    rw [hzR]
    exact hreal z.re


/-- The actual even subgroup has a finite genuine area measurable
fundamental domain, obtained from the original reflection triangle
and the actual two cosets, including every ideal-vertex case. -/
theorem triangleConformalKernel_finite_measureDomain (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) :
    ∃S:Set ℍ,MeasureTheory.IsFundamentalDomain (triangleConformalKernel T) S volume ∧ volume S≠⊤ := by
  let triangleCovolumeReflectionCountable:Countable (triangleReflectionGroup T):=
    triangleReflectionGroup_countable T
  let triangleCovolumeReflectionContinuous:ContinuousConstSMul (triangleReflectionGroup T) ℍ:=
    ⟨fun g=>g.val.continuous⟩
  let triangleCovolumeReflectionInvariant:SMulInvariantMeasure (triangleReflectionGroup T) ℍ volume:=⟨by
    intro g S hS
    exact (show MeasurePreserving g.val volume volume from
      ⟨g.val.continuous.measurable,native_isometry_volume_map g.val⟩).measure_preimage hS.nullMeasurableSet⟩
  let triangleCovolumeKernelFiniteIndex:(triangleConformalKernel T).FiniteIndex:=⟨by
    rw [triangleConformalKernel_index_two]
    norm_num⟩
  have hD:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.fundamentalDomain_of_integral_angles T ha hb hc
  obtain ⟨F,hF,hTF,hFC⟩:=hD.exists_fundamentalSet
  have hm:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.nullMeasurableSet_of_between _ _ hD hTF hFC
  have hnull:∀g:triangleReflectionGroup T,g≠1→volume {x:ℍ|g•x=x}=0:=by
    intro g hg
    exact native_isometry_fixed_volume_zero g.val (fun he=>hg (Subtype.ext he))
  refine ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.subgroupTransversalSet (triangleConformalKernel
    T) F,
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.subgroupTransversalSet_measureDomain _ hF hm hnull,?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.subgroupTransversalSet_measure _ hF hm hnull]
  have hv:volume F≠⊤:=by
    rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.measure_eq_of_between _ _ hD
      hTF hFC,T.area_eq_angle_defect]
    exact ENNReal.ofReal_ne_top
  apply ENNReal.mul_ne_top
  · simp only [ENat.card_eq_coe_natCard,ENat.toENNReal_coe,ne_eq,ENNReal.natCast_ne_top,not_false_eq_true]
  · exact hv

/-- The genuine whole conformal image inherits the physical native
finite-area domain through its faithful actual group homomorphism. -/
theorem triangleConformalMobius_finite_measureDomain (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma)
    (P:HalfPlaneFuchsianGroup
      (nativeConformalSubgroupMobiusHom (triangleConformalGroup T) inf_le_right).range) :
    letI:=P.nativeAction
    ∃S:Set ℍ,MeasureTheory.IsFundamentalDomain
      (nativeConformalSubgroupMobiusHom (triangleConformalGroup T) inf_le_right).range S volume ∧ volume S≠⊤ := by
  let triangleCovolumeImageAction:=P.nativeAction
  let F:=nativeConformalSubgroupMobiusHom (triangleConformalGroup T) inf_le_right
  let e:triangleConformalKernel T≃*F.range:=(triangleConformalKernelEquiv T).trans
    (MonoidHom.ofInjective (nativeConformalSubgroupMobiusHom_isometry _ _).injective)
  obtain ⟨S,hS,harea⟩:=triangleConformalKernel_finite_measureDomain T ha hb hc
  refine ⟨S,?_,harea⟩
  have he (g:triangleConformalKernel T) (z:ℍ): e g•z=g•z:=by
    apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
    rw [←P.nativeAction_boundary]
    exact nativeConformalSubgroupMobiusHom_action _ _ (triangleConformalKernelEquiv T g) z
  have h:=hS.preimage_of_equiv (f:=id) (MeasurePreserving.id volume).quasiMeasurePreserving
    e.bijective (by intro g z;exact he g z)
  simpa only [preimage_id] using h

/-- Every actual native triangle conformal image has the first-kind
limit set, through the genuine finite-area original triangle domain. -/
theorem triangleMobiusImage_firstKind (K:Subgroup (ℍ≃ᵢℍ))
    (hK:K≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) (ht:IsTriangleGroup K)
    (P:HalfPlaneFuchsianGroup (nativeConformalSubgroupMobiusHom K hK).range)
    (hNE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (nativeConformalSubgroupMobiusHom K
      hK).range) :
    P.asFuchsianDisc.IsFirstKind := by
  obtain ⟨p,q,r,hp,hq,hr,T,ha,hb,hc,hEq⟩:=ht
  subst K
  let triangleCovolumeTriangleAction:=P.nativeAction
  obtain ⟨S,hS,harea⟩:=triangleConformalMobius_finite_measureDomain T
    (ha ▸ triangleOrderAngle_isIntegral p hp)
    (hb ▸ triangleOrderAngle_isIntegral q hq)
    (hc ▸ triangleOrderAngle_isIntegral r hr) P
  exact native_finite_aeArea_firstKind P hNE hS harea

/-- An actual geometric triangle group is of the first kind on every
original geometric invariant disc, with all coordinates and finite
or ideal triangle models derived from its whole-group definition. -/
theorem mobiusTriangleGroup_firstKind {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hNE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary
      H) (ht:IsMobiusTriangleGroup H) :
    D.IsFirstKind := by
  obtain ⟨K,hK,hTri,q,hq⟩:=ht
  let triangleCovolumeTriangleDiscrete:DiscreteTopology K:=by
    obtain ⟨p,r,s,hT⟩:=hTri
    exact hT.discrete
  let P:=nativeConformalSubgroup_halfPlaneData K hK
  let H':=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  have hNE':_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (nativeConformalSubgroupMobiusHom K
    hK).range:=hq ▸ hNE.conjugation q
  have hfirst:=triangleMobiusImage_firstKind K hK hTri P hNE'
  let Dq:=D.nielsenConjugate q
  have hbound:frontier Dq.carrier=frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    apply _root_.LowDimensionalTopology.Geometry.Mobius.invariantComplexDiscs_frontier_eq H' (hNE.conjugation
      q) Dq.isDisc P.asFuchsianDisc.isDisc
    · exact Dq.image_eq
    · intro g
      let hg:(nativeConformalSubgroupMobiusHom K hK).range:=⟨g.val,hq ▸ g.property⟩
      change g.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
      exact P.preserves hg
  change fuchsianLimitSet (nativeConformalSubgroupMobiusHom K
    hK).range=frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet at hfirst
  change fuchsianLimitSet H=frontier D.carrier
  apply q.val.injective.image_injective
  rw [finiteArea_full_limitSet_conjugation,hq,hfirst]
  change frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q) '' frontier D.carrier
  rw [Homeomorph.image_frontier]
  exact hbound.symm

/-- The original second-kind condition rigorously excludes every
actual whole geometric triangle group. -/
theorem secondKind_not_mobiusTriangleGroup {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hNE:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary
      H) (hs:D.IsSecondKind) :
    ¬IsMobiusTriangleGroup H := by
  intro ht
  have he:=mobiusTriangleGroup_firstKind D hNE ht
  exact hs.ne he

end LowDimensionalTopology.Geometry.Fuchsian
