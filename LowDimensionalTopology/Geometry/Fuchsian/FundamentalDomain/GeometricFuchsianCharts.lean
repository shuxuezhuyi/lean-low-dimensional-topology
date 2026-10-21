/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeometricFuchsianModels
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeneralizedBoundaryReflection
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
local instance geometricChartSphereMeasurableSpace : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance geometricChartSphereBorelSpace : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩
/-- Any actual half-plane normalization gives the original model's genuine H coordinate. -/
def geometricHalfPlaneChart {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hq : q.val ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) :
    (fuchsianGeometricDomain D).carrier≃ₜℍ:=
  (((fuchsianGeometricDomain D).conjugateHomeomorph q).trans
    (Homeomorph.setCongr hq)).trans _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneOpenModelHomeomorph.symm

theorem geometricHalfPlaneChart_extended {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hq : q.val ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (x : (fuchsianGeometricDomain D).carrier) :
    (((geometricHalfPlaneChart D q hq x : ℍ) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=q.val x.val:=by
  let y : _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=⟨q.val x.val,by rw [←hq];exact mem_image_of_mem _ x.property⟩
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneOpenModelHomeomorph
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneOpenModelHomeomorph.symm y)).val=y.val
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneOpenModelHomeomorph.apply_symm_apply]

/-- The original actual density measure is also the genuine H volume in every true half-plane chart. -/
theorem geometricModelArea_eq_halfPlaneChart {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hq : q.val ''
      D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (S : Set (fuchsianGeometricDomain D).carrier) (hS : MeasurableSet S) :
    geometricModelArea D S=volume (geometricHalfPlaneChart D q hq '' S):=by
  have hqd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*q).val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=by
    change (fun z=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val
      z)) '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
    rw [←image_image,hq,cayleyMobius_image_openHalfPlane]
  rw [geometricModelArea_eq_discChart D (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*q) hqd S hS,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea_eq_halfPlane_volume _
      ((geometricDiscChart D (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*q)
        hqd).measurableEmbedding.measurableSet_image.mpr hS),image_image]
  congr 1
  apply image_congr
  intro x _
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyEquiv.injective
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (geometricDiscChart D (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*q) hqd x))=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (geometricHalfPlaneChart D q hq x)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  have he : (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (geometricHalfPlaneChart D q hq x) :
    Complex.UnitDisc) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
      (((geometricDiscChart D (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*q) hqd x : Complex.UnitDisc) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
    calc
      _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley (((geometricHalfPlaneChart D q hq x : ℍ) : ℂ) :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_halfPlane _).symm
      _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (q.val x.val):=by rw [geometricHalfPlaneChart_extended];rfl
      _=_:=(geometricDiscChart_extended D (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius*q) hqd x).symm
  exact (Subtype.val_injective (OnePoint.coe_injective he)).symm


/-- Actual whole-sphere conjugation restricted to the original genuine geometric model. -/
def geometricConjugateHomeomorph {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D :
  FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    (fuchsianGeometricDomain D).carrier≃ₜ(fuchsianGeometricDomain (D.nielsenConjugate q)).carrier:=
  (fuchsianGeometricDomain D).conjugateHomeomorph q

theorem geometricConjugateHomeomorph_coe {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (x : (fuchsianGeometricDomain D).carrier) :
    (geometricConjugateHomeomorph D q x).val=q.val x.val:=rfl

theorem geometricConjugateHomeomorph_equivariant {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (g : H) (x : (fuchsianGeometricDomain
      D).carrier) :
    geometricConjugateHomeomorph D q (g • x)=
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H g • geometricConjugateHomeomorph D q x:=
  (fuchsianGeometricDomain D).conjugateHomeomorph_equivariant q g x

/-- The actual hyperbolic density area on original models is invariant under every genuine Mobius coordinate change. -/
theorem geometricModelArea_conjugate_image {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (S : Set (fuchsianGeometricDomain
      D).carrier) (hS : MeasurableSet S) :
    geometricModelArea (D.nielsenConjugate q) (geometricConjugateHomeomorph D q '' S)=geometricModelArea D S:=by
  let E:=D.nielsenConjugate q
  let u:=geometricDiscNormalizer E
  have hu : (u*q).val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc:=by
    change (fun z=>u.val (q.val z)) '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
    rw [←image_image]
    exact geometricDiscNormalizer_image E
  rw [geometricModelArea_eq_discChart E u (geometricDiscNormalizer_image E) _
    ((geometricConjugateHomeomorph D q).measurableEmbedding.measurableSet_image.mpr hS),
    geometricModelArea_eq_discChart D (u*q) hu S hS,image_image]
  congr 1

/-- Measure-level invariance, proved from the genuine density change of variables. -/
theorem geometricModelArea_map_conjugate {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
    Measure.map (geometricConjugateHomeomorph D q).symm (geometricModelArea (D.nielsenConjugate q))=
      geometricModelArea D:=by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (geometricConjugateHomeomorph D q).symm.continuous.measurable hS]
  have he : (geometricConjugateHomeomorph D q).symm ⁻¹' S=geometricConjugateHomeomorph D q '' S:=
    ((geometricConjugateHomeomorph D q).toEquiv.image_eq_preimage_symm S).symm
  rw [he]
  exact geometricModelArea_conjugate_image D q S hS

/-- Full genuine fundamental domains transport to the original geometric model, including actual area-zero frontier. -/
theorem geometric_fundamentalDomain_conjugate_preimage
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (q :
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    {S : Set (fuchsianGeometricDomain (D.nielsenConjugate q)).carrier}
    (hS : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H)
      (fuchsianGeometricDomain (D.nielsenConjugate q)).carrier (geometricModelArea (D.nielsenConjugate q)) S) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D).carrier (geometricModelArea D)
      (geometricConjugateHomeomorph D q ⁻¹' S):=by
  rw [←geometricModelArea_map_conjugate D q]
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q
      H) (geometricConjugateHomeomorph D q)
    (geometricConjugateHomeomorph_equivariant D q) hS

end
end LowDimensionalTopology.Geometry.Fuchsian
