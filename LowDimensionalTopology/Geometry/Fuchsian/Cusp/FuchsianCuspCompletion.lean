/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.IsometricCircle.BoundaryIsometricCircles
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.ParabolicDirichletBoundary
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.CyclicClassRepresentatives
public import LowDimensionalTopology.Geometry.Surfaces.Cusp.MultipleCusps
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveCanonicalTransport
public import LowDimensionalTopology.Geometry.Fuchsian.Geodesic.SimpleClosedCurves
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped OnePoint UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine non-affine group member sends the actual height-one cusp strictly below height one. Elliptic elements are allowed. -/
theorem normalized_cusp_nonaffine_height {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈H)
    (hc : A 1 0≠0) (z : ℍ) (hz : 1<z.im) : (A•z).im<1 := by
  have hbound:=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspShimizu_lowerLeft H P.discrete hT
    (Matrix.SpecialLinearGroup.map Complex.ofRealHom A) hA
    (by change (A 1 0:ℂ)≠0;exact Complex.ofReal_ne_zero.mpr hc)
  change 1≤‖(A 1 0:ℂ)‖ at hbound
  rw [Complex.norm_real,Real.norm_eq_abs] at hbound
  have hc2 : 1≤(A 1 0)^2:=by nlinarith [sq_abs (A 1 0)]
  have hden : z.im<Complex.normSq (realSLDenominator A z):=by
    rw [realSLDenominator_normSq]
    have hh:=mul_nonneg (sub_nonneg.mpr hc2) (sq_nonneg z.im)
    nlinarith [sq_nonneg (A 1 0*z.re+A 1 1)]
  rw [realSL_im_action]
  exact (div_lt_one (z.im_pos.trans hden)).mpr hden

/-- Every actual affine group member preserves the whole height-one horodisc under the genuine discrete unit-translation normalization. -/
theorem normalized_cusp_affine_image {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (g : H) (hg : g.val.val ∞=∞) :
    g.val.val '' _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere 1=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere 1 := by
  have him (g : H) (hg : g.val.val ∞=∞) (z : ℍ) :
      letI:=P.nativeAction
      (g•z).im=z.im := by
    let cuspNativeAction:=P.nativeAction
    obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL g.val (P.preserves g)
    have hc : A 1 0=0:=by
      by_contra hc
      exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_infty_ne_iff A).mpr hc) (hA.symm ▸ hg)
    have hd:=discrete_unitTranslation_affine_denominator H P.discrete hT A
      (hA.symm ▸ g.property) hc
    have hd2 : (A 1 1)^2=1:=by nlinarith [sq_abs (A 1 1)]
    have he : g•z=A•z:=P.nativeAction_realSL g A hA z
    rw [he,realSL_im_action,realSLDenominator_normSq,hc]
    simp only [zero_mul,zero_add,zero_pow (by norm_num : 2≠0),add_zero,hd2,div_one]
  have hsub (g : H) (hg : g.val.val ∞=∞) :
      g.val.val '' _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere 1⊆_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere 1:=by
    rintro _ ⟨_,⟨z,hz,rfl⟩,rfl⟩
    let w : ℍ:=⟨z,by change 1<z.im at hz;linarith⟩
    let cuspNativeAction:=P.nativeAction
    refine ⟨(g•w:ℍ),?_,?_⟩
    · change 1<(g•w:ℍ).im
      rw [him g hg w]
      exact hz
    · exact (P.nativeAction_boundary g w).symm
  apply subset_antisymm (hsub g hg)
  intro z hz
  have hgi : g⁻¹.val.val ∞=∞:=_root_.LowDimensionalTopology.Geometry.Mobius.mobius_inv_fixed hg
  have hpre:=hsub g⁻¹ hgi (mem_image_of_mem g⁻¹.val.val hz)
  exact ⟨g⁻¹.val.val z,hpre,Equiv.apply_symm_apply _ _⟩

/-- Distinct actual cusp ends give separated genuine height-one horodiscs. -/
theorem normalized_cusp_nonaffine_disjoint {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H)
    (g : H) (hg : g.val.val ∞≠∞) :
    Disjoint (g.val.val '' _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere 1) (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere 1) := by
  apply disjoint_left.mpr
  rintro _ ⟨_,⟨z,hz,rfl⟩,rfl⟩ ⟨w,hw,he⟩
  let u : ℍ:=⟨z,by change 1<z.im at hz;linarith⟩
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL g.val (P.preserves g)
  have hc : A 1 0≠0:=by
    intro hc
    apply hg
    rw [←hA]
    exact not_ne_iff.mp (fun hn => ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_infty_ne_iff A).mp
      hn) hc)
  have hlow:=normalized_cusp_nonaffine_height P hT A (hA.symm ▸ g.property) hc u hz
  have heq : (A•u:ℍ)=⟨w,by change 1<w.im at hw;linarith⟩:=by
    apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A u).symm.trans ((congrArg (fun f :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup=>f.val
      (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) hA).trans he.symm)
  rw [heq] at hlow
  change 1<w.im at hw
  exact (not_lt_of_ge hw.le) hlow

/-- The actual height-one cusp is a genuine stable subset for the full original normalized group. -/
def normalizedStableCusp {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset P.asFuchsianDisc.domain where
  carrier:=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere 1
  subset_domain:=by
    rintro _ ⟨z,hz,rfl⟩
    exact ⟨z,by change 1<z.im at hz;change 0<z.im;linarith,rfl⟩
  stable:=by
    intro g hg
    by_cases hfix : g.val ∞=∞
    · exact Or.inl (normalized_cusp_affine_image P hT ⟨g,hg⟩ hfix)
    · exact Or.inr (normalized_cusp_nonaffine_disjoint P hT ⟨g,hg⟩ hfix)

/-- The actual stabilizer of every genuine parabolic fixed point has a genuine parabolic generator, not a supplied primitive period. -/
theorem parabolic_point_exists_stabilizer_generator {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (p : fuchsianCyclicFixedPoints D .parabolic) :
    ∃f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, f∈H ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f ∧
      Subgroup.zpowers f=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val := by
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val
  have : IsCyclic K:=D.stabilizer_isCyclic p.val
  obtain ⟨a,ha⟩:=exists_zpow_surjective K
  have hK : Subgroup.zpowers a.val=K:=by
    apply le_antisymm (Subgroup.zpowers_le.mpr a.property)
    intro g hg
    obtain ⟨n,hn⟩:=ha ⟨g,hg⟩
    exact Subgroup.mem_zpowers_iff.mpr ⟨n,congrArg Subtype.val hn⟩
  obtain ⟨g,hgH,hg,hgp⟩:=p.property.2
  have hgK : g∈K:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val
    g).mpr ⟨hgH,hgp⟩
  have han : a.val≠1:=by
    intro he
    obtain ⟨n,hn⟩:=Subgroup.mem_zpowers_iff.mp (hK.symm ▸ hgK)
    exact hg.1 (hn.symm.trans (by rw [he,one_zpow]))
  have hsame:=cyclic_nonidentity_same_fixedPoints K inferInstance g a.val hgK a.property hg.1 han
  have haf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic a.val:=by
    obtain ⟨u,hu⟩:=hg.2
    refine ⟨han,u,fun z=>?_⟩
    exact (hsame z).symm.trans (hu z)
  exact ⟨a.val,((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val a.val).mp
    a.property).1,haf,hK⟩

/-- The actual stable height-one cusp has precisely the full original stabilizer of its ideal point. -/
theorem normalizedStableCusp_stabilizer {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈H) :
    (normalizedStableCusp P hT).stabilizer=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ∞ := by
  apply le_antisymm
  · intro g hg
    refine (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ∞ g).mpr ⟨hg.1,?_⟩
    by_contra hn
    have hd:=normalized_cusp_nonaffine_disjoint P hT ⟨g,hg.1⟩ hn
    have he : g.val '' _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere 1=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere 1:=hg.2
    rw [he] at hd
    exact (_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere_isConnected
      1).nonempty.ne_empty (disjoint_self.mp hd)
  · intro g hg
    obtain ⟨hgH,hfix⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ∞ g).mp hg
    exact ⟨hgH,normalized_cusp_affine_image P hT ⟨g,hgH⟩ hfix⟩

/-- A genuine generator of an actual parabolic point stabilizer normalizes the whole original disc and its whole point stabilizer simultaneously. -/
theorem parabolic_generator_halfPlane_normalizer {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfp : f.val p=p)
    (hK : Subgroup.zpowers f=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p) :
    ∃q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧ q.val p=∞ ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) ∞=_root_.LowDimensionalTopology.Geometry.Surfaces.stableTranslationGroup := by
  have hfH : f∈H:=((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p f).mp
    (hK ▸ Subgroup.mem_zpowers f)).1
  obtain ⟨q₀,h,hdisc,hfq⟩:=_root_.LowDimensionalTopology.Geometry.Surfaces.parabolic_disc_signed_normalization f hf D.isDisc (D.image_eq ⟨f,hfH⟩)
  let r:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(h:ℂ)*Complex.I)
  let q:=r*q₀
  have hq : q.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    change ((fun z=>r.val (q₀.val z)) '' D.carrier)=_
    rw [←image_image,hdisc]
    exact vertical_cusp_shift_image h
  have hfq' : q*f*q⁻¹=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∨q*f*q⁻¹=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)⁻¹:=by
    have he : q*f*q⁻¹=r*(q₀*f*q₀⁻¹)*r⁻¹:=by dsimp only [q];group
    rw [he]
    rcases hfq with hp|hn
    · exact Or.inl (by rw [hp];exact translation_conjugation_commutes _ _)
    · right
      rw [hn]
      have he : r*(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)⁻¹*r⁻¹=(r*_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1*r⁻¹)⁻¹:=by group
      rw [he,translation_conjugation_commutes]
  have hfix : (q*f*q⁻¹).val ∞=∞:=by
    rcases hfq' with he|he
    · rw [he];exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty _
    · rw [he,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_neg];exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty _
  have hfix₀:=(_root_.LowDimensionalTopology.Geometry.Mobius.mobius_conjugate_boundary_fixed_iff f q ∞).mp hfix
  obtain ⟨a,ha⟩:=hf.2
  have hpq : p=q.val.symm ∞:=((ha p).mp hfp).trans ((ha (q.val.symm ∞)).mp hfix₀).symm
  have hqp : q.val p=∞:=by rw [hpq,Equiv.apply_symm_apply]
  refine ⟨q,hq,hqp,?_⟩
  rw [←hqp,primitive_boundaryStabilizer_conjugation,←hK]
  change (Subgroup.zpowers f).map (MulAut.conj
    q).toMonoidHom=_root_.LowDimensionalTopology.Geometry.Surfaces.stableTranslationGroup
  rw [MonoidHom.map_zpowers]
  change Subgroup.zpowers (q*f*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Surfaces.stableTranslationGroup
  rcases hfq' with he|he
  · rw [he];rfl
  · rw [he,Subgroup.zpowers_inv];rfl

/-- Every actual parabolic fixed point of an arbitrary original Fuchsian disc has a genuine full-group stable cusp and genuine normalization. No ellipse-free or primitive-period condition is supplied. -/
theorem fuchsian_parabolic_cusp_normalization_exists {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (p : fuchsianCyclicFixedPoints D .parabolic) :
    ∃S : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset D.domain,S.stabilizer=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val ∧
      Nonempty (_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization S p.val) := by
  obtain ⟨f,_hfH,hf,hK⟩:=parabolic_point_exists_stabilizer_generator D p
  have hfp : f.val p.val=p.val:=((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H
    p.val f).mp
    (hK ▸ Subgroup.mem_zpowers f)).2
  obtain ⟨q,hq,hqp,hstab⟩:=parabolic_generator_halfPlane_normalizer D f hf p.val hfp hK
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  let Q : HalfPlaneFuchsianGroup K:={
    preserves:=by
      intro g
      have hh:=(D.nielsenConjugate q).image_eq g
      change g.val.val '' (q.val '' D.carrier)=q.val '' D.carrier at hh
      rwa [hq] at hh
    discrete:=(D.nielsenConjugate q).discrete
  }
  have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈K:=by
    have hh : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer K ∞:=by
      rw [hstab]
      exact Subgroup.mem_zpowers _
    exact ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer K ∞ _).mp hh).1
  let T:=normalizedStableCusp Q hT
  let S : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset D.domain:={
    carrier:=q.val ⁻¹' T.carrier
    subset_domain:=by
      intro z hz
      have hqm : q.val z∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=T.subset_domain hz
      rw [←hq] at hqm
      obtain ⟨w,hw,he⟩:=hqm
      exact q.val.injective he ▸ hw
    stable:=by
      apply (mobiusStableSet_conjugation H (q.val ⁻¹' T.carrier) q).mp
      rw [image_preimage_eq _ q.val.surjective]
      exact T.stable
  }
  have him : q.val '' S.carrier=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere 1:=image_preimage_eq _ q.val.surjective
  have hST : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q S.stabilizer=_root_.LowDimensionalTopology.Geometry.Surfaces.stableTranslationGroup:=by
    rw [←S.conjugate_stabilizer q]
    change _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusSetStabilizer K (q.val '' S.carrier)=_
    rw [him]
    exact (normalizedStableCusp_stabilizer Q hT).trans hstab
  have hSfull : S.stabilizer=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val:=by
    apply Subgroup.map_injective (f := (MulAut.conj q).toMonoidHom) (MulAut.conj q).injective
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q S.stabilizer=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val)
    rw [hST,←primitive_boundaryStabilizer_conjugation,hqp,hstab]
  exact ⟨S,hSfull,⟨⟨q,1,him,hST,hqp⟩⟩⟩

/-- A representative is an actual parabolic fixed point of an actual maximal cyclic subgroup class. -/
def fuchsianParabolicPointRepresentative {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (c : FuchsianCyclicConjugacyClasses D .parabolic) :
    fuchsianCyclicFixedPoints D .parabolic :=
  (fuchsianCyclicPointStabilizerEquiv D .parabolic).symm (Quotient.out c)

/-- The chosen true point represents precisely its original actual cusp class. -/
theorem fuchsianParabolicPointRepresentative_class {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (c : FuchsianCyclicConjugacyClasses D .parabolic) :
    (Quotient.mk _ (fuchsianCyclicPointStabilizer D .parabolic (fuchsianParabolicPointRepresentative D c)) :
      FuchsianCyclicConjugacyClasses D .parabolic)=c := by
  change Quotient.mk _ ((fuchsianCyclicPointStabilizerEquiv D .parabolic)
    ((fuchsianCyclicPointStabilizerEquiv D .parabolic).symm (Quotient.out c)))=c
  rw [Equiv.apply_symm_apply,Quotient.out_eq]

/-- Different literal maximal parabolic subgroup classes label different actual whole-group cusp orbits. -/
theorem fuchsianParabolicPointRepresentative_orbits_distinct {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : Pairwise (fun c d=>¬MulAction.orbitRel H
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
      (fuchsianParabolicPointRepresentative D c).val (fuchsianParabolicPointRepresentative D d).val) := by
  intro c d hcd hrel
  obtain ⟨g,hg⟩:=hrel
  have htyped : MulAction.orbitRel H (fuchsianCyclicFixedPoints D .parabolic)
      (fuchsianParabolicPointRepresentative D c) (fuchsianParabolicPointRepresentative D d):=
    ⟨g,Subtype.ext hg⟩
  have he : (Quotient.mk _ (fuchsianCyclicPointStabilizer D .parabolic (fuchsianParabolicPointRepresentative D c)) :
      FuchsianCyclicConjugacyClasses D .parabolic)=
      Quotient.mk _ (fuchsianCyclicPointStabilizer D .parabolic (fuchsianParabolicPointRepresentative D d)):=by
    apply Quotient.sound
    change MulAction.orbitRel H (fuchsianCyclicFixedPoints D .parabolic)
      ((fuchsianCyclicPointStabilizerEquiv D .parabolic).symm
        ((fuchsianCyclicPointStabilizerEquiv D .parabolic) (fuchsianParabolicPointRepresentative D c)))
      ((fuchsianCyclicPointStabilizerEquiv D .parabolic).symm
        ((fuchsianCyclicPointStabilizerEquiv D .parabolic) (fuchsianParabolicPointRepresentative D d)))
    simpa only [Equiv.symm_apply_apply] using htyped
  rw [fuchsianParabolicPointRepresentative_class,fuchsianParabolicPointRepresentative_class] at he
  exact hcd he

/-- The actual stable horodisc constructed for one actual original cusp class. -/
def fuchsianCuspChartSubset {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (c : FuchsianCyclicConjugacyClasses D .parabolic) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset D.domain :=
  Classical.choose (fuchsian_parabolic_cusp_normalization_exists D (fuchsianParabolicPointRepresentative D c))

/-- Its stabilizer is the whole original point stabilizer, including every original group member fixing that cusp. -/
theorem fuchsianCuspChartSubset_stabilizer {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (c : FuchsianCyclicConjugacyClasses D .parabolic) :
    (fuchsianCuspChartSubset D c).stabilizer=
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H (fuchsianParabolicPointRepresentative D c).val :=
  (Classical.choose_spec (fuchsian_parabolic_cusp_normalization_exists D (fuchsianParabolicPointRepresentative D c))).1

/-- Genuine full-group normalization data for every actual cusp class of the original disc. -/
def fuchsianCuspChartNormalization {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (c : FuchsianCyclicConjugacyClasses D .parabolic) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization (fuchsianCuspChartSubset D
      c) (fuchsianParabolicPointRepresentative D c).val :=
  Classical.choice (Classical.choose_spec
    (fuchsian_parabolic_cusp_normalization_exists D (fuchsianParabolicPointRepresentative D c))).2

/-- The full original cusp stabilizer condition follows from the construction, rather than being an extra field. -/
theorem fuchsianCuspChart_full_stabilizer {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : ∀c,∀f∈H,
      f.val (fuchsianParabolicPointRepresentative D c).val=(fuchsianParabolicPointRepresentative D c).val→
      f∈(fuchsianCuspChartSubset D c).stabilizer := by
  intro c f hf hfix
  rw [fuchsianCuspChartSubset_stabilizer]
  exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H _ f).mpr ⟨hf,hfix⟩

/-- The actual original orbit quotient with all actual parabolic cusp orbits adjoined and the genuine cusp topology. Compactness in the cofinite case is a separate theorem. -/
abbrev FuchsianCuspCompletion {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.MultipleCuspAugmentedQuotient (fuchsianCuspChartNormalization D)

/-- The unchanged original whole-group quotient included in the actual simultaneous cusp completion. -/
def fuchsianCuspCompletionOld {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusDomainQuotient D.domain→FuchsianCuspCompletion D :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspQuotientOld (fuchsianCuspChartNormalization D)

/-- The old quotient retains exactly its original topology as an actual open subspace. -/
theorem fuchsianCuspCompletionOld_isOpenEmbedding {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : Topology.IsOpenEmbedding (fuchsianCuspCompletionOld D) :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspQuotientOld_isOpenEmbedding (fuchsianCuspChartNormalization D) D.discontinuous

/-- The new actual quotient point labelled by a genuine maximal parabolic subgroup conjugacy class. -/
def fuchsianCuspCompletionPoint {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) :
    FuchsianCyclicConjugacyClasses D .parabolic→FuchsianCuspCompletion D :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspNewPoint (fuchsianCuspChartNormalization D)

/-- Distinct actual cusp classes give distinct new completion points. -/
theorem fuchsianCuspCompletionPoint_injective {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : Function.Injective (fuchsianCuspCompletionPoint D) := by
  intro c d he
  by_contra hcd
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspNewPoint_ne (fuchsianCuspChartNormalization D)
    (fuchsianParabolicPointRepresentative_orbits_distinct D) hcd he

/-- Every genuine cusp point is outside the original quotient. -/
theorem fuchsianCuspCompletionPoint_not_mem_old {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (c : FuchsianCyclicConjugacyClasses D .parabolic) :
    fuchsianCuspCompletionPoint D c∉range (fuchsianCuspCompletionOld D) :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspNewPoint_not_mem_old (fuchsianCuspChartNormalization
    D) D.discontinuous c

/-- There are no additional completion points beyond the original quotient and the actual cusp classes. -/
theorem fuchsianCuspCompletion_old_or_cusp {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (x : FuchsianCuspCompletion D) :
    x∈range (fuchsianCuspCompletionOld D)∨∃c,x=fuchsianCuspCompletionPoint D c :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspQuotient_old_or_new (fuchsianCuspChartNormalization D) x

/-- The complement of the original quotient is in literal bijection with the actual maximal parabolic subgroup conjugacy classes. -/
def fuchsianCuspCompletionComplementEquiv {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) :
    FuchsianCyclicConjugacyClasses D .parabolic≃
      {x : FuchsianCuspCompletion D // x∉range (fuchsianCuspCompletionOld D)} :=
  Equiv.ofBijective (fun c=>⟨fuchsianCuspCompletionPoint D c,fuchsianCuspCompletionPoint_not_mem_old D c⟩) (by
    constructor
    · intro c d he
      exact fuchsianCuspCompletionPoint_injective D (congrArg Subtype.val he)
    · rintro ⟨x,hx⟩
      obtain h|⟨c,hc⟩:=fuchsianCuspCompletion_old_or_cusp D x
      · exact (hx h).elim
      · exact ⟨c,Subtype.ext hc.symm⟩)

/-- The all-cusp completion is a genuine Riemann surface, using actual normalized cusp charts and actual original quotient charts. -/
def fuchsianCuspCompletionRiemannSurface {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannSurface (FuchsianCuspCompletion D) :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspRiemannSurface (fuchsianCuspChartNormalization
    D) D.discontinuous
    (fuchsianParabolicPointRepresentative_orbits_distinct D) (fuchsianCuspChart_full_stabilizer D)

/-- The completion includes unchanged literal original representatives through the genuine original orbit projection. -/
theorem fuchsianCuspCompletionOld_projection {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (z : D.domain.carrier) :
    fuchsianCuspCompletionOld D (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainProjection D.domain z)=
      Quotient.mk _ (_root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspAugmentedOld
        (fuchsianCuspChartNormalization D) z) := rfl

/-- Every actual parabolic fixed point is in the genuine whole-group orbit of the representative of its actual maximal subgroup class. -/
theorem fuchsianParabolicPointRepresentative_orbit_cover {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (p : fuchsianCyclicFixedPoints D .parabolic) :
    ∃c : FuchsianCyclicConjugacyClasses D .parabolic,∃g : H,
      g.val.val (fuchsianParabolicPointRepresentative D c).val=p.val := by
  let c : FuchsianCyclicConjugacyClasses D .parabolic:=Quotient.mk _ (fuchsianCyclicPointStabilizer D .parabolic p)
  have he:=fuchsianParabolicPointRepresentative_class D c
  have hrel:=Quotient.exact he
  change MulAction.orbitRel H (fuchsianCyclicFixedPoints D .parabolic)
    ((fuchsianCyclicPointStabilizerEquiv D .parabolic).symm
      ((fuchsianCyclicPointStabilizerEquiv D .parabolic) (fuchsianParabolicPointRepresentative D c)))
    ((fuchsianCyclicPointStabilizerEquiv D .parabolic).symm
      ((fuchsianCyclicPointStabilizerEquiv D .parabolic) p)) at hrel
  simp only [Equiv.symm_apply_apply] at hrel
  obtain ⟨g,hg⟩:=hrel
  refine ⟨c,g⁻¹,?_⟩
  have hh : g • p=fuchsianParabolicPointRepresentative D c:=hg
  have hh' : g⁻¹ • fuchsianParabolicPointRepresentative D c=p:=by rw [←hh,inv_smul_smul]
  exact congrArg Subtype.val hh'

/-- The genuine cusp completion is Hausdorff through the proved original and cusp charts. -/
theorem fuchsianCuspCompletion_t2Space {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : T2Space (FuchsianCuspCompletion D) :=
  (fuchsianCuspCompletionRiemannSurface D).t2Space

/-- The genuine all-cusp completion is connected, with the unchanged original quotient as common connected chart domain. -/
theorem fuchsianCuspCompletion_connectedSpace {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : ConnectedSpace (FuchsianCuspCompletion D) :=
  (fuchsianCuspCompletionRiemannSurface D).connectedSpace

end LowDimensionalTopology.Geometry.Fuchsian
