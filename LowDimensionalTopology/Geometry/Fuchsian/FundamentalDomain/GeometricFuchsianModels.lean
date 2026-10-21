/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.GeneralizedModelSides
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletEquivariance
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
@[expose] public section
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Topology OnePoint Pointwise UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- Equivariant original group and point equivalences identify the actual orbit relation. -/
theorem orbitProjection_eq_iff_equivariant
    {G K X Y : Type*} [Group G] [Group K] [MulAction G X] [MulAction K Y]
    (e : G≃*K) (f : X≃Y) (he : ∀g x,f (g • x)=e g • f x) (x y : X) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection G X x=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection G X y ↔ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection K Y (f x)=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection K Y (f y):=by
  constructor
  · intro hxy
    obtain ⟨g,hg⟩:=(Quotient.exact hxy : MulAction.orbitRel G X x y)
    apply Quotient.sound
    refine ⟨e g,?_⟩
    exact (he g y).symm.trans (congrArg f hg)
  · intro hxy
    obtain ⟨k,hk⟩:=(Quotient.exact hxy : MulAction.orbitRel K Y (f x) (f y))
    apply Quotient.sound
    refine ⟨e.symm k,?_⟩
    apply f.injective
    rw [he,e.apply_symm_apply]
    exact hk

/-- The geometric genuine point selector transports under actual equivariant equivalences. -/
theorem _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalSet.equivariant_preimage
    {G K X Y : Type*} [Group G] [Group K] [MulAction G X] [MulAction K Y]
    (e : G≃*K) (f : X≃Y) (he : ∀g x,f (g • x)=e g • f x)
    {F : Set Y} (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalSet K Y F) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalSet G X (f ⁻¹' F):=by
  intro x
  obtain ⟨y,⟨hy,hrel⟩,hunique⟩:=hF (f x)
  refine ⟨f.symm y,⟨?_,?_⟩,?_⟩
  · change f (f.symm y)∈F
    rwa [f.apply_symm_apply]
  · apply (orbitProjection_eq_iff_equivariant e f he _ _).mpr
    rwa [f.apply_symm_apply]
  · intro z hz
    apply f.injective
    rw [f.apply_symm_apply]
    exact hunique (f z) ⟨hz.1,(orbitProjection_eq_iff_equivariant e f he _ _).mp hz.2⟩

/-- Full genuine fundamental domains transport with their actual measure, original orbit selector and frontier. -/
theorem _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage
    {G K X Y : Type*} [Group G] [Group K] [MulAction G X] [MulAction K Y]
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y]
    (e : G≃*K) (f : X≃ₜY) (he : ∀g x,f (g • x)=e g • f x)
    {ν : Measure Y} {D : Set Y} (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain K
      Y ν D) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain G X (Measure.map f.symm ν) (f ⁻¹' D):=by
  refine ⟨hD.isOpen.preimage f.continuous,?_,?_,?_⟩
  · have hf : f ⁻¹' D=f.symm '' D:=by
      ext x
      constructor
      · exact fun hx=>⟨f x,hx,f.symm_apply_apply x⟩
      · rintro ⟨y,hy,rfl⟩
        change f (f.symm y)∈D
        rwa [f.apply_symm_apply]
    rw [hf]
    exact hD.isConnected.image _ f.symm.continuous.continuousOn
  · obtain ⟨F,hF,hDF,hFcl⟩:=hD.exists_fundamentalSet
    refine ⟨f ⁻¹' F,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalSet.equivariant_preimage e
      f.toEquiv he hF,
      preimage_mono hDF,?_⟩
    rw [←f.preimage_closure]
    exact preimage_mono hFcl
  · rw [Measure.map_apply f.symm.continuous.measurable isClosed_frontier.measurableSet]
    have hf : f.symm ⁻¹' frontier (f ⁻¹' D)=frontier D:=by
      rw [←f.preimage_frontier,←preimage_comp]
      simp only [Function.comp_def,f.apply_symm_apply,preimage_id']
    rw [hf]
    exact hD.null_frontier

/-- The original geometric domain with its exact original sphere action. -/
def fuchsianGeometricDomain {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) : _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusInvariantDomain H:=
  ⟨D.carrier,D.isDisc.isOpen,D.isDisc.isConnected,D.invariant⟩

/-- A proved actual whole-model normalizer to the standard disc. -/
def geometricDiscNormalizer {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*D.halfPlaneNormalizer

theorem geometricDiscNormalizer_image {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D
  : FuchsianDisc H) :
    (geometricDiscNormalizer D).val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=by
  change (fun z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (D.halfPlaneNormalizer.val z)) '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
  rw [←image_image]
  rw [D.halfPlaneNormalizer_image,cayleyMobius_image_openHalfPlane]

/-- The exact entire original group transported by the actual disc normalizer. -/
abbrev geometricDiscGroup {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup:=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (geometricDiscNormalizer D) H

theorem geometricDiscData {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) : UnitDiscFuchsianGroup (geometricDiscGroup D) where
  invariant g z hz:=by
    have hi:=(D.nielsenConjugate (geometricDiscNormalizer D)).invariant g z
    rw [D.nielsenConjugate_carrier,geometricDiscNormalizer_image] at hi
    exact hi hz
  discontinuous:=by
    have hd:=(D.nielsenConjugate (geometricDiscNormalizer D)).discontinuous
    rw [D.nielsenConjugate_carrier,geometricDiscNormalizer_image] at hd
    exact hd

/-- The actual normalizer homeomorphism between the original geometric points and the actual standard-disc points. -/
def geometricDiscHomeomorph {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H) :
    (fuchsianGeometricDomain D).carrier≃ₜ(geometricDiscData D).domain.carrier:=
  ((fuchsianGeometricDomain D).conjugateHomeomorph (geometricDiscNormalizer D)).trans
    (Homeomorph.setCongr (geometricDiscNormalizer_image D))

theorem geometricDiscHomeomorph_coe {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H)
    (x : (fuchsianGeometricDomain D).carrier) :
    (geometricDiscHomeomorph D x).val=(geometricDiscNormalizer D).val x.val:=rfl

theorem geometricDiscHomeomorph_equivariant {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (g : H) (x : (fuchsianGeometricDomain D).carrier) :
    geometricDiscHomeomorph D (g • x)=
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence (geometricDiscNormalizer D) H g • geometricDiscHomeomorph D x:=by
  apply Subtype.ext
  change (geometricDiscNormalizer D).val (g.val.val x.val)=
    (geometricDiscNormalizer D).val (g.val.val ((geometricDiscNormalizer D).val.symm ((geometricDiscNormalizer D).val
      x.val)))
  rw [(geometricDiscNormalizer D).val.symm_apply_apply]

local instance geometricSphereMeasurableSpace : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance geometricSphereBorelSpace : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

/-- The genuine hyperbolic density area transported from the actual native disc chart of the original model. -/
def geometricModelArea {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc
  H) :
    Measure (fuchsianGeometricDomain D).carrier:=
  Measure.map (geometricDiscHomeomorph D).symm (geometricDiscData D).area

theorem geometricModelArea_apply {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H)
    (S : Set (fuchsianGeometricDomain D).carrier) (hS : MeasurableSet S) :
    geometricModelArea D S=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea
      ((geometricDiscData D).finiteCoordinate '' (geometricDiscHomeomorph D '' S)):=by
  rw [geometricModelArea,Measure.map_apply (geometricDiscHomeomorph D).symm.continuous.measurable hS]
  have he : (geometricDiscHomeomorph D).symm ⁻¹' S=geometricDiscHomeomorph D '' S:=by
    ext y
    constructor
    · exact fun hy=>⟨(geometricDiscHomeomorph D).symm y,hy,(geometricDiscHomeomorph D).apply_symm_apply y⟩
    · rintro ⟨x,hx,rfl⟩
      change (geometricDiscHomeomorph D).symm (geometricDiscHomeomorph D x)∈S
      rwa [(geometricDiscHomeomorph D).symm_apply_apply]
  rw [he]
  exact (geometricDiscData D).area_apply _
    ((geometricDiscHomeomorph D).measurableEmbedding.measurableSet_image.mpr hS)

/-- Actual native disc fundamental domains pull back to genuine original-model domains, with original action and actual density area. -/
theorem geometricModel_fundamentalDomain_of_disc
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    {S : Set (geometricDiscData D).domain.carrier}
    (hS : IsFuchsianFundamentalDomain (geometricDiscData D) S) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D)
      (geometricDiscHomeomorph D ⁻¹' S):=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence
      (geometricDiscNormalizer D) H)
    (geometricDiscHomeomorph D) (geometricDiscHomeomorph_equivariant D) hS


/-- Any proved whole-model disc normalizer gives its genuine finite native disc coordinate. -/
def geometricDiscChart {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc
  H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hq : q.val ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    (fuchsianGeometricDomain D).carrier≃ₜComplex.UnitDisc:=
  (((fuchsianGeometricDomain D).conjugateHomeomorph q).trans
    (Homeomorph.setCongr hq)).trans _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph

theorem geometricDiscChart_extended {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hq : q.val ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (x : (fuchsianGeometricDomain D).carrier) :
    (((geometricDiscChart D q hq x : Complex.UnitDisc) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=q.val x.val:=by
  let y : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=⟨q.val x.val,by rw [←hq];exact mem_image_of_mem _ x.property⟩
  change (((_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph y : Complex.UnitDisc) : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=y.val
  exact (_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe
    (_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph y)).symm.trans
    (congrArg Subtype.val (_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph.symm_apply_apply y))

/-- Two genuine whole-model disc coordinates differ by one actual normalized disc isometry. -/
theorem geometricDiscChart_transition {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D
  : FuchsianDisc H)
    (q₁ q₂ : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (h₁ : q₁.val ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (h₂ : q₂.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    ∃a c : ℂ,∃hdet : Complex.normSq a-Complex.normSq c=1,
      ∀x,geometricDiscChart D q₂ h₂ x=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hdet (geometricDiscChart D q₁ h₁ x):=by
  let T : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup:=q₂*q₁⁻¹
  have hT : T.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=by
    change (fun z=>q₂.val (q₁.val.symm z)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
    rw [←image_image,←h₁,q₁.val.symm_image_image,h₂]
    exact h₁.symm
  obtain ⟨a,c,hdet,hform⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.complexMobius_disc_normal_form T hT
  refine ⟨a,c,hdet,fun x=>?_⟩
  have he : (((geometricDiscChart D q₂ h₂ x : Complex.UnitDisc) : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
      (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hdet (geometricDiscChart D q₁ h₁ x) : Complex.UnitDisc) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
    calc
      _=q₂.val x.val:=geometricDiscChart_extended D q₂ h₂ x
      _=T.val (q₁.val x.val):=by change q₂.val x.val=q₂.val (q₁.val.symm (q₁.val x.val));rw [q₁.val.symm_apply_apply]
      _=T.val (((geometricDiscChart D q₁ h₁ x : Complex.UnitDisc) : ℂ) :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=
        congrArg T.val (geometricDiscChart_extended D q₁ h₁ x).symm
      _=_:=_root_.LowDimensionalTopology.Geometry.Surfaces.discFractionalHomeomorph_actual T a c hdet hform _
  exact Subtype.val_injective (OnePoint.coe_injective he)

/-- The actual density area computed in any two genuine disc coordinates is identical. -/
theorem geometricDiscChart_area_independent {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (q₁ q₂ : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (h₁ : q₁.val ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (h₂ : q₂.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (S : Set (fuchsianGeometricDomain D).carrier) (hS : MeasurableSet S) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (geometricDiscChart D q₂ h₂ '' S)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (geometricDiscChart D q₁ h₁ '' S):=by
  obtain ⟨a,c,hdet,htrans⟩:=geometricDiscChart_transition D q₁ q₂ h₁ h₂
  have him : geometricDiscChart D q₂ h₂ '' S=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hdet '' (geometricDiscChart D q₁ h₁ '' S):=by
    rw [image_image]
    exact image_congr (fun x _=>htrans x)
  rw [him]
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.normalizedDisc_hyperbolicArea a c hdet _
    ((geometricDiscChart D q₁ h₁).measurableEmbedding.measurableSet_image.mpr hS)

/-- The original density area is independent of the chosen actual whole-model Mobius normalization. -/
theorem geometricModelArea_eq_discChart {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hq : q.val ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (S : Set (fuchsianGeometricDomain D).carrier) (hS : MeasurableSet S) :
    geometricModelArea D S=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (geometricDiscChart D q hq '' S):=by
  rw [geometricModelArea_apply D S hS,image_image]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (geometricDiscChart D
    (geometricDiscNormalizer D)
    (geometricDiscNormalizer_image D) '' S)=_
  exact (geometricDiscChart_area_independent D (geometricDiscNormalizer D) q
    (geometricDiscNormalizer_image D) hq S hS).symm

end
end LowDimensionalTopology.Geometry.Fuchsian
