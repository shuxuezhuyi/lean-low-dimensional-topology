/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.ParabolicAreaInfinity
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.ParabolicFiniteArea
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.OrdinaryLocalDomains
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
local instance finiteAreaFirstKindSphereMeasurable:MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance finiteAreaFirstKindSphereBorel:BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

/-- Every genuine Euclidean rectangle reaching a nonempty real ideal
interval has infinite actual half-plane hyperbolic density area. -/
theorem boundary_rectangle_volume_top (a b c:ℝ) (hab:a<b) (hc:0<c) :
    volume {z:ℍ | a<z.re ∧ z.re<b ∧ z.im<c}=⊤ := by
  let R:Set ℍ:={z | a<z.re ∧ z.re<b ∧ z.im<c}
  let A:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph (fun _=>c/2) (Ioo a b)
  have hcover:{z:ℍ | a<z.re ∧ z.re<b}⊆R∪A:=by
    intro z hz
    by_cases hy:z.im<c
    · exact Or.inl ⟨hz.1,hz.2,hy⟩
    · exact Or.inr ⟨hz,by dsimp only;linarith only [not_lt.mp hy,hc]⟩
  have hle:volume {z:ℍ | a<z.re ∧ z.re<b}≤volume R+volume A:=
    (measure_mono hcover).trans (measure_union_le _ _)
  rw [parabolic_vertical_strip_volume_top a b hab,
    parabolic_vertical_strip_above_volume a b (c/2) (by positivity)] at hle
  by_contra hn
  have hfinite:volume R+ENNReal.ofReal ((b-a)/(c/2))≠⊤:=ENNReal.add_ne_top.mpr ⟨hn,ENNReal.ofReal_ne_top⟩
  exact hfinite (top_unique hle)

/-- Every open sphere neighborhood of a finite real boundary point
has infinite actual half-plane hyperbolic area on its native side. -/
theorem real_boundary_open_volume_top (U:Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hU:IsOpen
  U)
    (p:ℝ) (hp:((p:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈U) :
    volume (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' U)=⊤ := by
  have ho:IsOpen (((↑):ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ⁻¹'
    U):=hU.preimage OnePoint.continuous_coe
  obtain ⟨ε,hε,hball⟩:=Metric.isOpen_iff.mp ho (p:ℂ) hp
  let a:=p-ε/3
  let b:=p+ε/3
  let c:=ε/3
  have hab:a<b:=by dsimp only [a,b];linarith only [hε]
  have hc:0<c:=by dsimp only [c];positivity
  have hsub:{z:ℍ | a<z.re ∧ z.re<b ∧ z.im<c}⊆_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' U:=by
    intro z hz
    apply hball
    rw [Metric.mem_ball,dist_eq_norm]
    have hre:|z.re-p|<ε/3:=by
      apply abs_lt.mpr
      dsimp only [a,b] at hz
      constructor <;> linarith only [hz.1,hz.2.1]
    have hn:‖(z:ℂ)-(p:ℂ)‖≤|z.re-p|+z.im:=by
      simpa only [Complex.sub_re,Complex.ofReal_re,UpperHalfPlane.coe_re,
        Complex.sub_im,Complex.ofReal_im,sub_zero,UpperHalfPlane.coe_im,
        abs_of_pos z.im_pos] using Complex.norm_le_abs_re_add_abs_im ((z:ℂ)-(p:ℂ))
    dsimp only [c] at hz
    linarith only [hn,hre,hz.2.2,hε]
  exact top_unique ((boundary_rectangle_volume_top a b c hab hc) ▸ measure_mono hsub)

section PackingArea
variable {G X:Type*} [Group G] [MulAction G X] [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [Countable G] [MeasurableConstSMul G X]
    {μ:Measure X} [SMulInvariantMeasure G X μ]

/-- A genuine measurable packing has area at most the actual full
fundamental domain, including finite elliptic stabilizers on null sets. -/
theorem finiteArea_packing_measure_le {D T:Set X}
    (hD:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain G X μ D)
    (hnull:∀g:G,g≠1→μ {x:X|g•x=x}=0)
    (hT:NullMeasurableSet T μ)
    (hpack:Pairwise (Disjoint on fun g:G=>g•T)) : μ T≤μ D := by
  obtain ⟨F,hF,hDF,hFC⟩:=hD.exists_fundamentalSet
  have hm:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.nullMeasurableSet_of_between G X hD hDF hFC
  have hMF:=hF.measureDomain_of_fixed_null hm hnull
  have hpair:Pairwise (AEDisjoint μ on fun g:G=>g•T∩F):=by
    intro g k hne
    exact ((hpack hne).mono inter_subset_left inter_subset_left).aedisjoint
  have hle:=hMF.measure_le_of_pairwise_disjoint hT hpair
  rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.measure_eq_of_between G X hD hDF
    hFC] at hle
  exact hle
end PackingArea

/-- A genuine native packing has density area at most an actual
fundamental domain for the same entire original Fuchsian group. -/
theorem native_fundamental_packing_volume_le {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) {D T:Set ℍ} :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume D →
      NullMeasurableSet T volume → Pairwise (Disjoint on fun g:H=>g•T) → volume T≤volume D := by
  let finiteAreaNativeAction:=P.nativeAction
  let finiteAreaNativeCountable:Countable H:=_root_.LowDimensionalTopology.Geometry.Mobius.discreteMobius_countable H P.discrete
  let finiteAreaNativeContinuous:ContinuousConstSMul H ℍ:=⟨by
      intro g
      obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL g.val (P.preserves g)
      have he:(fun z:ℍ=>g•z)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
        A:ℍ→ℍ):=funext (P.nativeAction_realSL g A hA)
      rw [he]
      exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A).continuous⟩
  let finiteAreaNativeInvariant:SMulInvariantMeasure H ℍ volume:=⟨by
      intro g S hS
      obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL g.val (P.preserves g)
      have he:(fun z:ℍ=>g•z)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
        A:ℍ→ℍ):=funext (P.nativeAction_realSL g A hA)
      rw [he]
      exact (show MeasurePreserving (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) volume volume from
        ⟨(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
          A).continuous.measurable,parabolic_realSL_map_volume A⟩).measure_preimage hS.nullMeasurableSet⟩
  let finiteAreaNativeNoAtoms:NullSingletonClass (volume:Measure ℍ):=⟨by
    intro z
    rw [UpperHalfPlane.volume_eq_lintegral]
    simp⟩
  intro hD hT hpack
  have hnull:∀g:H,g≠1→volume {x:ℍ|g•x=x}=0:=by
    intro g hg
    have hgn:g.val≠1:=fun he=>hg (Subtype.ext he)
    have hf:((_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint:ℍ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ⁻¹'
        {z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex|g.val.val z=z}).Finite:=
      (mobius_boundary_fixed_finite g.val
        hgn).preimage _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective.injOn
    have hsub:{x:ℍ|g•x=x}⊆_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹'
        {z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex|g.val.val z=z}:=by
      intro z hz
      change g.val.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint
        z)=_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z
      rw [P.nativeAction_boundary,hz]
    exact (hf.subset hsub).countable.measure_zero volume
  exact finiteArea_packing_measure_le hD hnull hT hpack

/-- A finite-area original native fundamental domain excludes a true
open wandering neighborhood at any actual finite real boundary point. -/
theorem native_finite_area_no_boundary_wandering {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) {D:Set ℍ} :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume D → volume D≠⊤ →
      ∀U:Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,IsOpen U →
      (∀g:H,g≠1→Disjoint (g.val.val '' U) U) →
      ∀p:ℝ,((p:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∉U := by
  let finiteAreaBoundaryNativeAction:=P.nativeAction
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
  have hle:=native_fundamental_packing_volume_le P hD ho.measurableSet.nullMeasurableSet hpack
  rw [real_boundary_open_volume_top U hU p hp] at hle
  exact harea (top_unique hle)

/-- A genuine ordinary point on an original invariant-circle frontier
has trivial stabilizer: its finite stabilizer would otherwise give an
elliptic with an impossible fixed point on that actual frontier. -/
theorem ordinary_fuchsian_frontier_free {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hH:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary
      H) (p:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hp:p∈frontier D.carrier) (hOrd:p∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet H) :
    ∀g:H,g•p=p→g=1 := by
  intro g hfix
  by_contra hg
  have hdis:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_ordinary_discontinuous H hH D.discrete
  have hfin:IsOfFinOrder g:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isOfFinOrder_of_finite_stabilizer g p (hdis.finite_stabilizer p hOrd) hfix
  have hfinC:IsOfFinOrder g.val:=H.subtype.isOfFinOrder hfin
  have hgn:g.val≠1:=fun he=>hg (Subtype.ext he)
  have hEll:=_root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic g.val hgn hfinC
  exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_fixed_not_mem_disc_frontier g.val hEll D.isDisc (D.image_eq g) hfix hp

/-- Every actual finite real boundary point of a finite-area original
native Fuchsian surface lies in its genuine limit set. -/
theorem native_finite_area_real_boundary_limit {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hH:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) {D:Set
      ℍ} :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume D → volume D≠⊤ →
      ∀p:ℝ,((p:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H := by
  let finiteAreaLimitNativeAction:=P.nativeAction
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
  exact native_finite_area_no_boundary_wandering P hD harea N hN.isOpen hwander p hpN

/-- Finite genuine area forces the full original native limit set to
fill the actual invariant-circle frontier, including infinity. -/
theorem native_finite_area_firstKind {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) (hH:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) {D:Set
      ℍ} :
    letI:=P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume D → volume D≠⊤ → P.asFuchsianDisc.IsFirstKind := by
  let finiteAreaFirstKindNativeAction:=P.nativeAction
  intro hD harea
  have hreal:=native_finite_area_real_boundary_limit P hH hD harea
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

/-- Genuine parabolic and loxodromic ideal endpoints transform under
actual simultaneous conjugation of the entire original group. -/
theorem finiteArea_limitEndpoints_conjugation (H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    q.val '' fuchsianLimitEndpoints H=fuchsianLimitEndpoints (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z,⟨g,hg,hfix⟩,rfl⟩
    refine ⟨⟨q*g.val*q⁻¹,⟨g.val,g.property,rfl⟩⟩,?_,?_⟩
    · have hc:IsConj g.val (q*g.val*q⁻¹):=isConj_iff.mpr ⟨q,rfl⟩
      rcases hg with hp|hl
      · exact Or.inl ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj hc).mp hp)
      · exact Or.inr ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusLoxodromic_isConj hc).mp hl)
    · exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_conjugate_fixedpoint g.val q z hfix
  · rintro z ⟨g,hg,hfix⟩
    obtain ⟨u,hu,he⟩:=g.property
    change q*u*q⁻¹=g.val at he
    have hc:IsConj u g.val:=isConj_iff.mpr ⟨q,he⟩
    refine ⟨q⁻¹.val z,⟨⟨u,hu⟩,?_,?_⟩,?_⟩
    · rcases hg with hp|hl
      · exact Or.inl ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj hc).mpr hp)
      · exact Or.inr ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusLoxodromic_isConj hc).mpr hl)
    · apply q.val.injective
      change q•(u•(q⁻¹•z))=q•(q⁻¹•z)
      have hh:(q*u*q⁻¹)•z=z:=by
        change (q*u*q⁻¹).val z=z
        rw [he]
        exact hfix
      simpa only [mul_smul,smul_inv_smul] using hh
    · change q•(q⁻¹•z)=z
      exact smul_inv_smul q z

/-- The full genuine limit set transforms by the same actual sphere
homeomorphism, with no non-elementarity assumption needed. -/
theorem finiteArea_full_limitSet_conjugation (H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (q:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    q.val '' fuchsianLimitSet H=fuchsianLimitSet (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) := by
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q) '' closure (fuchsianLimitEndpoints
    H)=_
  rw [Homeomorph.image_closure]
  change closure (q.val '' fuchsianLimitEndpoints H)=_
  rw [finiteArea_limitEndpoints_conjugation]
  rfl

/-- Every original non-elementary Fuchsian group with a genuine
finite-density-area fundamental domain is of the first kind on its
original geometric invariant disc. Every coordinate and area/orbit
transport is constructed from the original whole-domain data. -/
theorem fuchsian_finite_area_firstKind {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (hH:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H)
    {S:Set (fuchsianGeometricDomain D).carrier}
    (hS:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D) S)
    (harea:geometricModelArea D S≠⊤) : D.IsFirstKind := by
  let q:=D.halfPlaneNormalizer
  let Q:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.normalizedHalfPlaneData D
  let E:=geometricHalfPlaneChart D q D.halfPlaneNormalizer_image
  let finiteAreaOriginalNormalizedAction:MulAction (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) ℍ:=Q.nativeAction
  have hES:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) ℍ volume (E '' S):=
    parabolic_disc_chart_fundamental_image D q D.halfPlaneNormalizer_image Q S hS
  have hvol:volume (E '' S)≠⊤:=by
    rw [←geometricModelArea_eq_halfPlaneChart D q D.halfPlaneNormalizer_image S hS.isOpen.measurableSet]
    exact harea
  have hFirst:=native_finite_area_firstKind Q (hH.conjugation q) hES hvol
  change fuchsianLimitSet (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
    H)=frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet at hFirst
  change fuchsianLimitSet H=frontier D.carrier
  apply q.val.injective.image_injective
  have hboundary:q.val '' frontier D.carrier=frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q) '' frontier D.carrier=_
    rw [Homeomorph.image_frontier]
    exact congrArg frontier D.halfPlaneNormalizer_image
  rw [finiteArea_full_limitSet_conjugation,hboundary]
  exact hFirst

end LowDimensionalTopology.Geometry.Fuchsian
