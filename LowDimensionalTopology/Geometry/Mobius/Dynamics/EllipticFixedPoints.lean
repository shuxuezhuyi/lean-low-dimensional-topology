/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.FiniteOrbit
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.FiniteIndexCriteria
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ParabolicEllipticNormalForms
@[expose] public section
open Set Filter
open scoped Topology OnePoint UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- A finite actual boundary orbit of an infinite-order elliptic consists only of its true fixed points. -/
theorem elliptic_finite_cyclic_orbit_fixed (g : complexMobiusGroup) (he : MobiusElliptic g)
    (hinf : ¬IsOfFinOrder g) (z : ExtendedComplex)
    (hz : (MulAction.orbit (Subgroup.zpowers g) z).Finite) : g.val z=z := by
  by_contra hgz
  obtain hp | hp:=mobius_nonidentity_fixedPoint_dichotomy g he.1
  · exact he.not_parabolic ⟨he.1,hp⟩
  · obtain ⟨a,b,hab,hfix⟩:=hp
    have ha : g.val a=a:=(hfix a).mpr (Or.inl rfl)
    have hb : g.val b=b:=(hfix b).mpr (Or.inr rfl)
    have hza : a≠z:=fun h=>hgz (h ▸ ha)
    have hzb : b≠z:=fun h=>hgz (h ▸ hb)
    obtain ⟨n,hn,hnfix⟩:=DiscreteGroups.Action.exists_positive_power_fixing_finite_orbit z hz
      (⟨g,Subgroup.mem_zpowers g⟩ : Subgroup.zpowers g)
    have hnz : (g^n).val z=z:=hnfix z (MulAction.mem_orbit_self z)
    have hpow : g^n=1:=mobius_eq_one_of_three_fixed (g^n) a b z hab hza hzb
      (mobius_pow_fixed ha n) (mobius_pow_fixed hb n) hnz
    exact hinf (isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,hpow⟩)

/-- Genuine half-plane points include continuously and injectively in the compactified complex model. -/
def halfPlaneBoundaryPoint (z : ℍ) : ExtendedComplex:=((z : ℂ) : ExtendedComplex)

theorem halfPlaneBoundaryPoint_injective : Function.Injective halfPlaneBoundaryPoint :=
  OnePoint.coe_injective.comp UpperHalfPlane.coe_injective

theorem halfPlaneBoundaryPoint_continuous : Continuous halfPlaneBoundaryPoint :=
  OnePoint.continuous_coe.comp UpperHalfPlane.continuous_coe

theorem halfPlaneBoundaryPoint_mem (z : ℍ) : halfPlaneBoundaryPoint z∈Hyperbolic.openHalfPlaneSet :=
  (Hyperbolic.coe_mem_openHalfPlaneSet _).mpr z.im_pos

/-- The native real-SL cyclic orbit is the actual original Mobius cyclic orbit. -/
theorem halfPlaneBoundaryPoint_cyclic_orbit (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    halfPlaneBoundaryPoint '' MulAction.orbit (Subgroup.zpowers A) z=
      MulAction.orbit (Subgroup.zpowers (Hyperbolic.realSLMobius A)) (halfPlaneBoundaryPoint z) := by
  ext w
  constructor
  · rintro ⟨v,⟨C,rfl⟩,rfl⟩
    obtain ⟨n,hn⟩:=C.property
    have hmem : Hyperbolic.realSLMobius C.val∈Subgroup.zpowers (Hyperbolic.realSLMobius A):=by
      rw [←hn,map_zpow]
      exact Subgroup.zpow_mem_zpowers _ _
    exact ⟨⟨Hyperbolic.realSLMobius C.val,hmem⟩,Hyperbolic.realSLMobius_action C.val z⟩
  · rintro ⟨f,rfl⟩
    obtain ⟨n,hn⟩:=f.property
    refine ⟨(A^n) • z,⟨⟨A^n,Subgroup.zpow_mem_zpowers _ _⟩,rfl⟩,?_⟩
    change halfPlaneBoundaryPoint ((A^n) • z)=f.val.val (halfPlaneBoundaryPoint z)
    rw [←hn]
    change halfPlaneBoundaryPoint ((A^n) • z)=(Hyperbolic.realSLMobius A^n).val (halfPlaneBoundaryPoint z)
    rw [←map_zpow]
    exact (Hyperbolic.realSLMobius_action (A^n) z).symm

/-- A genuine elliptic cyclic orbit lies in an actual compact hyperbolic closed ball. -/
theorem elliptic_halfPlane_cyclic_orbit_compact (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (p z : ℍ) (hp : A • p=p) :
    ∃K : Set ExtendedComplex,IsCompact K ∧ K⊆Hyperbolic.openHalfPlaneSet ∧
      MulAction.orbit (Subgroup.zpowers (Hyperbolic.realSLMobius A)) (halfPlaneBoundaryPoint z)⊆K := by
  let B:=Metric.closedBall p (dist z p)
  refine ⟨halfPlaneBoundaryPoint '' B,(isCompact_closedBall p _).image halfPlaneBoundaryPoint_continuous,?_,?_⟩
  · rintro x ⟨v,hv,rfl⟩
    exact halfPlaneBoundaryPoint_mem v
  · rw [←halfPlaneBoundaryPoint_cyclic_orbit]
    apply image_mono
    rintro v ⟨C,rfl⟩
    have hCp : C.val • p=p:=(Subgroup.zpowers_le.mpr
      (show A∈MulAction.stabilizer (Matrix.SpecialLinearGroup (Fin 2) ℝ) p from hp)) C.property
    change dist (C.val • z) p≤dist z p
    have he:=(Hyperbolic.realGL_isometry (Matrix.SpecialLinearGroup.mapGL ℝ C.val)).dist_eq z p
    change dist (C.val • z) (C.val • p)=dist z p at he
    rw [hCp] at he
    exact he.le

/-- Conjugating a genuine elliptic by any actual group element gives the transported genuine fixed point. -/
theorem ellipticFixedPointSet_conjugate_mem (H : Subgroup complexMobiusGroup)
    (g u : H) (he : MobiusElliptic g.val) (z : ExtendedComplex) (hz : g.val.val z=z) :
    u.val.val z∈DiscreteGroups.ellipticFixedPointSet H := by
  refine ⟨u*g*u⁻¹,(mobiusElliptic_conjugation g.val u.val).mpr he,?_⟩
  change u.val.val (g.val.val (u.val.val.symm (u.val.val z)))=u.val.val z
  rw [u.val.val.symm_apply_apply,hz]

/-- The actual orbit of a moved elliptic center supplies actual elliptic fixed points in the model. -/
theorem elliptic_moved_center_cyclic_orbit (H : Subgroup complexMobiusGroup)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : Hyperbolic.realSLMobius A∈H)
    (he : MobiusElliptic (Hyperbolic.realSLMobius A)) (p : ℍ) (hp : A • p=p)
    (f : H) (w : ℍ) (hw : f.val.val (halfPlaneBoundaryPoint p)=halfPlaneBoundaryPoint w) :
    MulAction.orbit (Subgroup.zpowers (Hyperbolic.realSLMobius A)) (halfPlaneBoundaryPoint
      w)⊆DiscreteGroups.ellipticFixedPointSet H := by
  rintro z ⟨C,rfl⟩
  have hCH : C.val∈H:=(Subgroup.zpowers_le.mpr hA) C.property
  have hfix : (Hyperbolic.realSLMobius A).val (halfPlaneBoundaryPoint p)=halfPlaneBoundaryPoint p:=by
    change (Hyperbolic.realSLMobius A).val ((p : ℂ) : ExtendedComplex)=((p : ℂ) : ExtendedComplex)
    rw [Hyperbolic.realSLMobius_action,hp]
  have hh:=ellipticFixedPointSet_conjugate_mem H ⟨Hyperbolic.realSLMobius A,hA⟩ (⟨C.val,hCH⟩*f) he
    (halfPlaneBoundaryPoint p) hfix
  change C.val.val (f.val.val (halfPlaneBoundaryPoint p))∈DiscreteGroups.ellipticFixedPointSet H at hh
  rwa [hw] at hh

/-- Condition (3) implies (5) on the actual half-plane, with actual compact orbits and conjugate centers. -/
theorem ellipticFixedPointsNonaccumulating_halfPlane_finiteOrder (H : Subgroup complexMobiusGroup)
    (hH : DiscreteGroups.IsNonElementary H) (hinv : ∀f : H,f.val.val ''
      Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet)
    (hnacc : DiscreteGroups.EllipticFixedPointsNonaccumulating H Hyperbolic.openHalfPlaneSet) :
      DiscreteGroups.EllipticsFiniteOrder H := by
  intro g hg he
  by_contra hinf
  obtain ⟨A,hAg⟩:=Fuchsian.mobius_preserves_halfPlane_exists_SL g (hinv ⟨g,hg⟩)
  have heA : MobiusElliptic (Hyperbolic.realSLMobius A):=hAg.symm ▸ he
  let p:=Hyperbolic.hEllipticCenter A ((Hyperbolic.realSLMobius_elliptic_iff A heA.1).mp heA)
  have hp : A • p=p:=(Hyperbolic.hSL_elliptic_fixed_iff A _ p).mpr rfl
  obtain ⟨f,hfm⟩:=hH.exists_move_boundary (halfPlaneBoundaryPoint p)
  obtain ⟨B,hB⟩:=Fuchsian.mobius_preserves_halfPlane_exists_SL f.val (hinv f)
  let w:=B • p
  have hw : f.val.val (halfPlaneBoundaryPoint p)=halfPlaneBoundaryPoint w:=by
    rw [←hB]
    exact Hyperbolic.realSLMobius_action B p
  have hwp : w≠p:=by
    intro h
    exact hfm (hw.trans (congrArg halfPlaneBoundaryPoint h))
  obtain ⟨K,hK,hKH,hOrb⟩:=elliptic_halfPlane_cyclic_orbit_compact A p w hp
  have hcenter : MulAction.orbit (Subgroup.zpowers (Hyperbolic.realSLMobius A)) (halfPlaneBoundaryPoint
    w)⊆DiscreteGroups.ellipticFixedPointSet H:=
    elliptic_moved_center_cyclic_orbit H A (hAg.symm ▸ hg) heA p hp f w hw
  have hfiniteK : (K∩DiscreteGroups.ellipticFixedPointSet H).Finite:=
    (DiscreteGroups.ellipticFixedPointsNonaccumulating_iff_compact H Hyperbolic.openHalfPlaneSet
      (OnePoint.isOpenMap_coe _ (isOpen_lt continuous_const Complex.continuous_im))).mp hnacc K hK hKH
  have hfinite : (MulAction.orbit (Subgroup.zpowers (Hyperbolic.realSLMobius A)) (halfPlaneBoundaryPoint w)).Finite:=
    hfiniteK.subset (fun z hz=>⟨hOrb hz,hcenter hz⟩)
  have hfixed : (Hyperbolic.realSLMobius A).val (halfPlaneBoundaryPoint w)=halfPlaneBoundaryPoint w:=
    elliptic_finite_cyclic_orbit_fixed (Hyperbolic.realSLMobius A) heA (by rwa [hAg]) _ hfinite
  have hAw : A • w=w:=by
    apply halfPlaneBoundaryPoint_injective
    exact (Hyperbolic.realSLMobius_action A w).symm.trans hfixed
  exact hwp ((Hyperbolic.hSL_elliptic_fixed_iff A _ w).mp hAw)

/-- The actual entire elliptic fixed-point set transforms under the genuine global conjugacy. -/
theorem ellipticFixedPointSet_subgroupConjugate (H : Subgroup complexMobiusGroup) (q : complexMobiusGroup) :
    DiscreteGroups.ellipticFixedPointSet (DiscreteGroups.Action.Actions.subgroupConjugate q H)=q.val ''
      DiscreteGroups.ellipticFixedPointSet H := by
  ext z
  constructor
  · rintro ⟨f,hfe,hfz⟩
    obtain ⟨g,hg,heq⟩:=(DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H f.val).mp f.property
    have hge : MobiusElliptic g:=(mobiusElliptic_conjugation g q).mp (by rw [heq];exact hfe)
    have hgz : g.val (q.val.symm z)=q.val.symm z:=by
      apply q.val.injective
      rw [q.val.apply_symm_apply]
      change (q*g*q⁻¹).val z=z
      rw [heq]
      exact hfz
    exact ⟨q.val.symm z,⟨⟨g,hg⟩,hge,hgz⟩,q.val.apply_symm_apply z⟩
  · rintro ⟨w,⟨g,hge,hgw⟩,rfl⟩
    refine ⟨⟨q*g.val*q⁻¹,(DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨g.val,g.property,rfl⟩⟩,
      (mobiusElliptic_conjugation g.val q).mpr hge,?_⟩
    change q.val (g.val.val (q.val.symm (q.val w)))=q.val w
    rw [q.val.symm_apply_apply,hgw]

/-- Literal fixed-point nonaccumulation transports across genuine model conjugation. -/
theorem _root_.LowDimensionalTopology.Geometry.DiscreteGroups.EllipticFixedPointsNonaccumulating.conjugate {H :
    Subgroup complexMobiusGroup}
    {D : Set ExtendedComplex} (h : DiscreteGroups.EllipticFixedPointsNonaccumulating H D) (hD : IsOpen D)
    (q : complexMobiusGroup) :
    DiscreteGroups.EllipticFixedPointsNonaccumulating (DiscreteGroups.Action.Actions.subgroupConjugate q H) (q.val
      '' D) := by
  apply (DiscreteGroups.ellipticFixedPointsNonaccumulating_iff_compact _ _
    ((mobiusBoundaryHomeomorph q).isOpenMap D hD)).mpr
  intro K hK hKD
  let K':=q.val.symm '' K
  have hK' : IsCompact K':=hK.image (mobiusBoundaryHomeomorph q).symm.continuous
  have hK'D : K'⊆D:=by
    rintro z ⟨w,hw,rfl⟩
    obtain ⟨v,hv,he⟩:=hKD hw
    change q.val v=w at he
    rw [←he,q.val.symm_apply_apply]
    exact hv
  have hf : (K'∩DiscreteGroups.ellipticFixedPointSet H).Finite:=
    (DiscreteGroups.ellipticFixedPointsNonaccumulating_iff_compact H D hD).mp h K' hK' hK'D
  apply (hf.image q.val).subset
  rintro z ⟨hzK,hzE⟩
  rw [ellipticFixedPointSet_subgroupConjugate] at hzE
  obtain ⟨w,hw,he⟩:=hzE
  refine ⟨w,⟨?_,hw⟩,he⟩
  exact ⟨z,hzK,by rw [←he,q.val.symm_apply_apply]⟩

set_option maxHeartbeats 800000 in
/-- Nonaccumulating elliptic fixed points force finite elliptic order in an invariant disc. -/
theorem _root_.LowDimensionalTopology.Geometry.DiscreteGroups.EllipticFixedPointsNonaccumulating.ellipticsFiniteOrder
    {H : Subgroup complexMobiusGroup}
    (hH : DiscreteGroups.IsNonElementary H) {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D)
    (hinv : ∀g : H,g.val.val '' D=D) (h : DiscreteGroups.EllipticFixedPointsNonaccumulating H D) :
      DiscreteGroups.EllipticsFiniteOrder H := by
  obtain ⟨q,hq⟩:=Fuchsian.IsComplexOpenDisc.halfPlane_normalizer hD
  let K:=DiscreteGroups.Action.Actions.subgroupConjugate q H
  have hK : DiscreteGroups.IsNonElementary K:=hH.conjugation q
  have hKH : ∀f : K,f.val.val '' Hyperbolic.openHalfPlaneSet=Hyperbolic.openHalfPlaneSet:=by
    intro f
    obtain ⟨g,hg,heq⟩:=(DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H f.val).mp f.property
    rw [←heq,←hq,stableAxis_conjugate_image,hinv ⟨g,hg⟩]
  have hacc : DiscreteGroups.EllipticFixedPointsNonaccumulating K Hyperbolic.openHalfPlaneSet:=by
    have hh:=h.conjugate hD.isOpen q
    rwa [hq] at hh
  have hKE:=ellipticFixedPointsNonaccumulating_halfPlane_finiteOrder K hK hKH hacc
  intro g hg he
  have hgK : q*g*q⁻¹∈K:=(DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨g,hg,rfl⟩
  have hfin : IsOfFinOrder ((MulAut.conj q) g):=
    hKE _ hgK ((mobiusElliptic_conjugation g q).mpr he)
  apply orderOf_pos_iff.mp
  simpa only [(MulAut.conj q).orderOf_eq g] using hfin.orderOf_pos

/-- All six original conditions are equivalent for genuine conformal subgroups preserving an actual disc.
The full orientation-reversing isometry-group adapter is a separate obligation. -/
theorem conformal_discreteness_elliptic_and_cyclic_criteria_tfae (H : Subgroup complexMobiusGroup) (hH :
    DiscreteGroups.IsNonElementary H)
    (D : Set ExtendedComplex) (hD : IsComplexOpenDisc D) (hinv : ∀g : H,g.val.val '' D=D) :
    List.TFAE [IsDiscreteMobiusSubgroup H,DiscreteGroups.IsMobiusDiscontinuousOn H D,
      DiscreteGroups.EllipticFixedPointsNonaccumulating H D,DiscreteGroups.EllipticsNonaccumulatingAtIdentity H,
      DiscreteGroups.EllipticsFiniteOrder H,DiscreteGroups.AllCyclicSubgroupsDiscrete H] := by
  have hHD : HasInvariantComplexDisc H:=⟨D,hD,hinv⟩
  tfae_have 1 ↔ 2:=DiscreteGroups.discrete_iff_discDiscontinuous H hH D hD hinv
  tfae_have 1 ↔ 4:=DiscreteGroups.discrete_iff_ellipticsNonaccumulatingAtIdentity H hH hHD
  tfae_have 1 ↔ 5:=DiscreteGroups.discrete_iff_ellipticsFiniteOrder H hH hHD
  tfae_have 1 ↔ 6:=DiscreteGroups.discrete_iff_allCyclicSubgroupsDiscrete H hH hHD
  tfae_have 2 → 3:=fun h=>DiscreteGroups.IsMobiusDiscontinuousOn.ellipticFixedPointsNonaccumulating h hD.isOpen
  tfae_have 3 → 5:=fun h=>DiscreteGroups.EllipticFixedPointsNonaccumulating.ellipticsFiniteOrder hH hD hinv h
  tfae_finish

/-- All six discreteness criteria hold in an elliptic-free non-elementary disc group. -/
theorem ellipticFree_all_six_criteria (H : Subgroup complexMobiusGroup) (hH : DiscreteGroups.IsNonElementary H)
    (D : Set ExtendedComplex) (hD : IsComplexOpenDisc D) (hinv : ∀g : H,g.val.val '' D=D)
    (hE : DiscreteGroups.IsEllipticFree H) :
    IsDiscreteMobiusSubgroup H ∧ DiscreteGroups.IsMobiusDiscontinuousOn H D ∧
      DiscreteGroups.EllipticFixedPointsNonaccumulating H D ∧ DiscreteGroups.EllipticsNonaccumulatingAtIdentity H ∧
      DiscreteGroups.EllipticsFiniteOrder H ∧ DiscreteGroups.AllCyclicSubgroupsDiscrete H := by
  have hd:=DiscreteGroups.discrete_of_ellipticFree_nonElementary_invariant_disc H ⟨D,hD,hinv⟩ hE hH
  have hdis:=(DiscreteGroups.discrete_iff_discDiscontinuous H hH D hD hinv).mp hd
  exact ⟨hd,hdis,DiscreteGroups.IsMobiusDiscontinuousOn.ellipticFixedPointsNonaccumulating hdis hD.isOpen,
    DiscreteGroups.discrete_ellipticsNonaccumulatingAtIdentity H hd,DiscreteGroups.discrete_elliptic_finiteOrder H hd,
    DiscreteGroups.discrete_allCyclicSubgroupsDiscrete H hd⟩

end
end LowDimensionalTopology.Geometry.Mobius
