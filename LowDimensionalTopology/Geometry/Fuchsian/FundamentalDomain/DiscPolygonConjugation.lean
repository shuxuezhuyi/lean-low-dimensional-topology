/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.ZeroStabilizerRotations
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.PolygonSidePairing
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveCanonicalTransport
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianFiniteGroups
/-!
# Conjugating Fuchsian polygons

A disc-preserving Mobius conjugation transports the group action, density
area and hyperbolic metric. Equivariant area-preserving isometries transport
convex fundamental polygons and their actual side-pairing elements.
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped Topology OnePoint Pointwise Complex.UnitDisc ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance discConjugationSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance discConjugationSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- Whole-group conjugation in the actual invariant unit disc, with its genuine compact-hit condition. -/
theorem UnitDiscFuchsianGroup.conjugateData {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    UnitDiscFuchsianGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
      H) where
  invariant g z hz := by
    have hi := (P.asFuchsianDisc.nielsenConjugate q).invariant g z
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.nielsenConjugate_carrier] at hi
    change z ∈ q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈ q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc at hi
    rw [hq] at hi
    exact hi hz
  discontinuous := by
    have hd := (P.asFuchsianDisc.nielsenConjugate q).discontinuous
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.nielsenConjugate_carrier] at hd
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn _ (q.val ''
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) at hd
    rwa [hq] at hd

/-- The actual point homeomorphism belonging to whole-group disc conjugation. -/
def UnitDiscFuchsianGroup.conjugateCoordinate {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    P.domain.carrier ≃ₜ (P.conjugateData q hq).domain.carrier :=
  (P.domain.conjugateHomeomorph q).trans (Homeomorph.setCongr hq)

theorem UnitDiscFuchsianGroup.conjugateCoordinate_equivariant {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (g : H) (x : P.domain.carrier) :
    P.conjugateCoordinate q hq (g • x) = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H g • P.conjugateCoordinate q hq x := by
  apply Subtype.ext
  change q.val (g.val.val x.val) = q.val (g.val.val (q.val.symm (q.val x.val)))
  rw [q.val.symm_apply_apply]

/-- The finite coordinate of a genuine conjugation is one actual normalized disc automorphism. -/
theorem UnitDiscFuchsianGroup.conjugateCoordinate_normal_form {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    ∃ a c : ℂ, ∃ hd : Complex.normSq a - Complex.normSq c = 1,
      ∀ x : P.domain.carrier,
        (P.conjugateData q hq).finiteCoordinate (P.conjugateCoordinate q hq x) =
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hd (P.finiteCoordinate x) := by
  obtain ⟨a,c,hd,hform⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.complexMobius_disc_normal_form q hq
  refine ⟨a,c,hd,fun x => ?_⟩
  have hc {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (Q : UnitDiscFuchsianGroup
    G) (y : Q.domain.carrier) :
      ((((Q.finiteCoordinate y : Complex.UnitDisc) : ℂ) :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) = y.val :=
    (_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe (Q.finiteCoordinate y)).symm.trans
      (congrArg Subtype.val (Q.finiteCoordinate.symm_apply_apply y))
  apply Complex.UnitDisc.coe_injective
  apply OnePoint.coe_injective
  rw [hc]
  change q.val x.val = _
  rw [←hc P x]
  exact _root_.LowDimensionalTopology.Geometry.Surfaces.discFractionalHomeomorph_actual q a c hd hform (P.finiteCoordinate x)

/-- Conjugation preserves the actual density-area measures, rather than just their null sets. -/
theorem UnitDiscFuchsianGroup.conjugateCoordinate_area_map {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    Measure.map (P.conjugateCoordinate q hq) P.area = (P.conjugateData q hq).area := by
  let Q := P.conjugateData q hq
  let f := P.conjugateCoordinate q hq
  obtain ⟨a,c,hd,hform⟩ := P.conjugateCoordinate_normal_form q hq
  apply Measure.ext
  intro S hS
  have hpre : MeasurableSet (f ⁻¹' S) := hS.preimage f.continuous.measurable
  have hM := P.finiteCoordinate.measurableEmbedding.measurableSet_image.mpr hpre
  have him : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hd '' (P.finiteCoordinate '' (f ⁻¹' S)) = Q.finiteCoordinate '' S := by
    ext z
    constructor
    · rintro ⟨w,⟨x,hx,rfl⟩,rfl⟩
      exact ⟨f x,hx,hform x⟩
    · rintro ⟨y,hy,rfl⟩
      refine ⟨P.finiteCoordinate (f.symm y),⟨f.symm y,?_,rfl⟩,?_⟩
      · change f (f.symm y) ∈ S
        rwa [f.apply_symm_apply]
      · rw [←hform,f.apply_symm_apply]
  rw [Measure.map_apply f.continuous.measurable hS,P.area_apply _ hpre,Q.area_apply _ hS,←him]
  exact (_root_.LowDimensionalTopology.Geometry.Surfaces.normalizedDisc_hyperbolicArea a c hd _ hM).symm

/-- The original finite-coordinate conjugation is a genuine native hyperbolic isometry. -/
theorem UnitDiscFuchsianGroup.conjugateCoordinate_isometry {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    letI := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
    Isometry (fun z : Complex.UnitDisc => (P.conjugateData q hq).finiteCoordinate
      (P.conjugateCoordinate q hq (P.finiteCoordinate.symm z))) := by
  let discConjugationNativeMetric := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  obtain ⟨a,c,hd,hform⟩ := P.conjugateCoordinate_normal_form q hq
  have hnorm : ‖a‖ ^ 2 - ‖c‖ ^ 2 = 1 := by
    simpa only [Complex.normSq_eq_norm_sq] using hd
  have he : (fun z : Complex.UnitDisc => (P.conjugateData q hq).finiteCoordinate
      (P.conjugateCoordinate q hq (P.finiteCoordinate.symm z))) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discCoefficientAction a c hnorm := by
    funext z
    rw [hform,P.finiteCoordinate.apply_symm_apply]
    apply Complex.UnitDisc.coe_injective
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discCoefficientAction_coe]
    rfl
  rw [he]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.discCoefficientAction_isometry a c hnorm

/-- Genuine equivariant coordinates transport the full polygon predicate, including compact-finite tiles. -/
theorem equivariant_fuchsian_polygon_image
    {H K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) (Q :
      UnitDiscFuchsianGroup K)
    (e : H ≃* K) (f : P.domain.carrier ≃ₜ Q.domain.carrier)
    (he : ∀ g x, f (g • x) = e g • f x)
    (harea : Measure.map f P.area = Q.area)
    (hiso : letI := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
      Isometry (fun z : Complex.UnitDisc => Q.finiteCoordinate (f (P.finiteCoordinate.symm z))))
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    IsConvexFuchsianPolygon Q (f '' D) := by
  have hback (g : K) (x : Q.domain.carrier) : f.symm (g • x) = e.symm g • f.symm x := by
    apply f.injective
    rw [f.apply_symm_apply,he,e.apply_symm_apply,f.apply_symm_apply]
  have hF := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage e.symm f.symm hback hD.locallyFinite.fundamental
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain K Q.domain.carrier (Measure.map f P.area) (f.symm ⁻¹' D) at hF
  have hset : f.symm ⁻¹' D = f '' D := (f.toEquiv.image_eq_preimage_symm D).symm
  rw [harea,hset] at hF
  refine ⟨⟨hF,?_⟩,?_⟩
  · intro L hL
    have hfin := (hD.locallyFinite.compact_hits_finite (f.symm '' L) (hL.image f.symm.continuous)).image e
    apply hfin.subset
    rintro g ⟨x,hx,hxL⟩
    obtain ⟨y,hy,hgy⟩ := hx
    have hyD : f.symm y ∈ closure D := by
      rw [←f.image_closure] at hy
      obtain ⟨w,hw,hew⟩ := hy
      rwa [←hew,f.symm_apply_apply]
    have hxy : e.symm g • f.symm y = f.symm x := by
      apply f.injective
      rw [he,e.apply_symm_apply,f.apply_symm_apply,f.apply_symm_apply]
      exact hgy
    refine ⟨e.symm g,⟨f.symm x,⟨f.symm y,hyD,hxy⟩,⟨x,hxL,rfl⟩⟩,e.apply_symm_apply g⟩
  · let discConjugationTransferMetric := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
    have hc := hD.convex.isometry_image hiso
    have him : (fun z : Complex.UnitDisc => Q.finiteCoordinate (f (P.finiteCoordinate.symm z))) ''
        (P.finiteCoordinate '' D) = Q.finiteCoordinate '' (f '' D) := by
      rw [image_image,image_image]
      exact image_congr (fun x _ => by rw [P.finiteCoordinate.symm_apply_apply])
    rwa [him] at hc

/-- The inverse finite coordinate is also a genuine isometry. -/
theorem inverse_finiteCoordinate_isometry
    {H K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) (Q :
      UnitDiscFuchsianGroup K)
    (f : P.domain.carrier ≃ₜ Q.domain.carrier)
    (hf : letI := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
      Isometry (fun z : Complex.UnitDisc => Q.finiteCoordinate (f (P.finiteCoordinate.symm z)))) :
    letI := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
    Isometry (fun z : Complex.UnitDisc => P.finiteCoordinate (f.symm (Q.finiteCoordinate.symm z))) := by
  let discConjugationInverseMetric := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  let n := P.finiteCoordinate.symm.trans (f.trans Q.finiteCoordinate)
  let u : Complex.UnitDisc ≃ᵢ Complex.UnitDisc := ⟨n.toEquiv,hf⟩
  exact u.symm.isometry

/-- The whole actual polygon predicate pulls back through a genuine area-preserving equivariant disc coordinate. -/
theorem equivariant_fuchsian_polygon_preimage
    {H K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) (Q :
      UnitDiscFuchsianGroup K)
    (e : H ≃* K) (f : P.domain.carrier ≃ₜ Q.domain.carrier)
    (he : ∀ g x, f (g • x) = e g • f x)
    (harea : Measure.map f P.area = Q.area)
    (hiso : letI := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
      Isometry (fun z : Complex.UnitDisc => Q.finiteCoordinate (f (P.finiteCoordinate.symm z))))
    {D : Set Q.domain.carrier} (hD : IsConvexFuchsianPolygon Q D) :
    IsConvexFuchsianPolygon P (f ⁻¹' D) := by
  have hback (g : K) (x : Q.domain.carrier) : f.symm (g • x) = e.symm g • f.symm x := by
    apply f.injective
    rw [f.apply_symm_apply,he,e.apply_symm_apply,f.apply_symm_apply]
  have hareaBack : Measure.map f.symm Q.area = P.area := by
    rw [←harea,Measure.map_map f.symm.continuous.measurable f.continuous.measurable]
    have heq : f.symm ∘ f = id := funext f.symm_apply_apply
    rw [heq,Measure.map_id]
  have h := equivariant_fuchsian_polygon_image Q P e.symm f.symm hback hareaBack
    (inverse_finiteCoordinate_isometry P Q f hiso) hD
  have hset : f.symm '' D = f ⁻¹' D := f.symm.toEquiv.image_eq_preimage_symm D
  rwa [hset] at h

/-- Whole-group conjugation preserves every genuine convex fundamental polygon. -/
theorem UnitDiscFuchsianGroup.conjugate_polygon_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) :
    IsConvexFuchsianPolygon (P.conjugateData q hq) (P.conjugateCoordinate q hq '' D) :=
  equivariant_fuchsian_polygon_image P (P.conjugateData q hq)
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
      H) (P.conjugateCoordinate q hq)
    (P.conjugateCoordinate_equivariant q hq) (P.conjugateCoordinate_area_map q hq)
    (P.conjugateCoordinate_isometry q hq) hD

/-- The same exact predicate pulls back to the original group and its original disc. -/
theorem UnitDiscFuchsianGroup.conjugate_polygon_preimage {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    {D : Set (P.conjugateData q hq).domain.carrier}
    (hD : IsConvexFuchsianPolygon (P.conjugateData q hq) D) :
    IsConvexFuchsianPolygon P (P.conjugateCoordinate q hq ⁻¹' D) :=
  equivariant_fuchsian_polygon_preimage P (P.conjugateData q hq)
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
      H) (P.conjugateCoordinate q hq)
    (P.conjugateCoordinate_equivariant q hq) (P.conjugateCoordinate_area_map q hq)
    (P.conjugateCoordinate_isometry q hq) hD

/-- A genuine original side element transports to the same actual equivariant group element. -/
theorem equivariant_fuchsian_side_element_image
    {H K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) (Q :
      UnitDiscFuchsianGroup K)
    (e : H ≃* K) (f : P.domain.carrier ≃ₜ Q.domain.carrier)
    (he : ∀ g x, f (g • x) = e g • f x)
    (harea : Measure.map f P.area = Q.area)
    (hiso : letI := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
      Isometry (fun z : Complex.UnitDisc => Q.finiteCoordinate (f (P.finiteCoordinate.symm z))))
    {D : Set P.domain.carrier} (hD : IsConvexFuchsianPolygon P D) (s : FuchsianPolygonSides P D) :
    ∃ hQ : IsConvexFuchsianPolygon Q (f '' D), ∃ t : FuchsianPolygonSides Q (f '' D),
      fuchsianSideElement hQ t = e (fuchsianSideElement hD s) := by
  let g := fuchsianSideElement hD s
  have hg := (fuchsianSideElement_spec hD s).1
  have heg : e g ≠ 1 := by intro hh;exact hg (e.injective (hh.trans (map_one e).symm))
  have hQ := equivariant_fuchsian_polygon_image P Q e f he harea hiso hD
  have hNon : (closure D ∩ fuchsianDomainTile P D g).Nontrivial := by
    rw [←(fuchsianSideElement_spec hD s).2]
    exact s.property.2.2
  have hm {x : P.domain.carrier} (hx : x ∈ closure D ∩ fuchsianDomainTile P D g) :
      f x ∈ closure (f '' D) ∩ fuchsianDomainTile Q (f '' D) (e g) := by
    refine ⟨?_,?_⟩
    · rw [←f.image_closure]
      exact mem_image_of_mem _ hx.1
    · obtain ⟨y,hy,hgy⟩ := hx.2
      refine ⟨f y,?_,?_⟩
      · rw [←f.image_closure]
        exact mem_image_of_mem _ hy
      · exact (he g y).symm.trans (congrArg f hgy)
  obtain ⟨x,hx,y,hy,hxy⟩ := hNon
  have hNew : (closure (f '' D) ∩ fuchsianDomainTile Q (f '' D) (e g)).Nontrivial :=
    ⟨f x,hm hx,f y,hm hy,f.injective.ne hxy⟩
  let t : FuchsianPolygonSides Q (f '' D) := ⟨_,hQ.side_of_nontrivial_intersection heg hNew⟩
  refine ⟨hQ,t,?_⟩
  exact ((hQ.existsUnique_side_element t.property).choose_spec.2 (e g) ⟨heg,rfl⟩).symm

/-- Side pairing existence pulls back to the original group; no artificial signed orientation is introduced. -/
theorem equivariant_fuchsian_side_element_preimage
    {H K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H) (Q :
      UnitDiscFuchsianGroup K)
    (e : H ≃* K) (f : P.domain.carrier ≃ₜ Q.domain.carrier)
    (he : ∀ g x, f (g • x) = e g • f x)
    (harea : Measure.map f P.area = Q.area)
    (hiso : letI := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
      Isometry (fun z : Complex.UnitDisc => Q.finiteCoordinate (f (P.finiteCoordinate.symm z))))
    {D : Set Q.domain.carrier} (hD : IsConvexFuchsianPolygon Q D) (s : FuchsianPolygonSides Q D) :
    ∃ hP : IsConvexFuchsianPolygon P (f ⁻¹' D), ∃ t : FuchsianPolygonSides P (f ⁻¹' D),
      fuchsianSideElement hP t = e.symm (fuchsianSideElement hD s) := by
  have hback (g : K) (x : Q.domain.carrier) : f.symm (g • x) = e.symm g • f.symm x := by
    apply f.injective
    rw [f.apply_symm_apply,he,e.apply_symm_apply,f.apply_symm_apply]
  have hareaBack : Measure.map f.symm Q.area = P.area := by
    rw [←harea,Measure.map_map f.symm.continuous.measurable f.continuous.measurable]
    have heq : f.symm ∘ f = id := funext f.symm_apply_apply
    rw [heq,Measure.map_id]
  have h := equivariant_fuchsian_side_element_image Q P e.symm f.symm hback hareaBack
    (inverse_finiteCoordinate_isometry P Q f hiso) hD s
  have hset : f.symm '' D = f ⁻¹' D := f.symm.toEquiv.image_eq_preimage_symm D
  rwa [hset] at h

/-- Every actual point has a genuine whole-disc Mobius normalizer to zero. -/
theorem discPoint_normalizer_exists (z : Complex.UnitDisc) :
    ∃ q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ∧
      q.val (((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) = ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  let a := (_root_.LowDimensionalTopology.Geometry.Surfaces.discCenterScale (z:ℂ) : ℂ)
  let c := -conj (z:ℂ) * a
  have hd : Complex.normSq a - Complex.normSq c = 1 := _root_.LowDimensionalTopology.Geometry.Surfaces.discCenter_determinant z.norm_lt_one
  refine ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.normalizedDiscMobius a c
    hd,_root_.LowDimensionalTopology.Geometry.Surfaces.normalizedDiscMobius_preserves_disc a c hd,?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.normalizedDiscMobius_val,_root_.LowDimensionalTopology.Geometry.Hyperbolic.normalizedDiscTransformation_of_closedDisc a c z hd z.norm_lt_one.le]
  exact congrArg (fun w : ℂ => (w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) (_root_.LowDimensionalTopology.Geometry.Surfaces.discCenter_maps_center_zero z.norm_lt_one)

/-- The actual conjugation can be chosen at any original interior point. -/
theorem UnitDiscFuchsianGroup.point_normalizer_exists {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) :
    ∃ q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, ∃ hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc,
      (P.conjugateCoordinate q hq w).val = ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  obtain ⟨q,hq,hzero⟩ := discPoint_normalizer_exists (P.finiteCoordinate w)
  refine ⟨q,hq,?_⟩
  have hc : ((((P.finiteCoordinate w : Complex.UnitDisc) : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) = w.val :=
    (_root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe (P.finiteCoordinate w)).symm.trans
      (congrArg Subtype.val (P.finiteCoordinate.symm_apply_apply w))
  change q.val w.val = _
  rwa [hc] at hzero

end LowDimensionalTopology.Geometry.Fuchsian
