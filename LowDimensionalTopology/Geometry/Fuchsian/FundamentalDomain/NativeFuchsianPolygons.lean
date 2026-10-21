/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.ParabolicFordFundamentalDomains
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.GeneralizedFundamentalDomains
public import LowDimensionalTopology.Geometry.DiscreteGroups.Packing.ElementaryPacking
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology OnePoint Pointwise UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance nativePolygonSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance nativePolygonSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- Discreteness on H3 gives the actual compact-hit condition on the invariant H2. -/
theorem HalfPlaneFuchsianGroup.discontinuous {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  rw [←_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_range]
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusDiscontinuousOn_of_H3_lift H P.discrete _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_isOpenEmbedding.isEmbedding _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_continuous
  intro g x y he
  obtain ⟨A,hA⟩ := mobius_preserves_halfPlane_exists_SL g.val (P.preserves g)
  have hxy : A • x = y := _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A x).symm.trans
    ((congrArg (fun f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup => f.val
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint x)) hA).trans he))
  rw [←hA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed_realSL,hxy]

/-- The native model carries all original geometric Fuchsian-disc data, including elementary groups. -/
def HalfPlaneFuchsianGroup.asFuchsianDisc {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) : FuchsianDisc H where
  carrier := _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
  isDisc := _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet_isComplexOpenDisc
  invariant g z hz := by
    change g.val.val z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    rw [←P.preserves g]
    exact mem_image_of_mem _ hz
  discontinuous := P.discontinuous

/-- The same full group in its genuine Cayley disc coordinate. -/
theorem HalfPlaneFuchsianGroup.cayleyData {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup
      H) : UnitDiscFuchsianGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H) where
  invariant g z hz := by
    have hi := (P.asFuchsianDisc.nielsenConjugate
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius).invariant g z
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.nielsenConjugate_carrier] at hi
    change z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet →
      g • z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet at hi
    rw [cayleyMobius_image_openHalfPlane] at hi
    exact hi hz
  discontinuous := by
    have hd := (P.asFuchsianDisc.nielsenConjugate
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius).discontinuous
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.nielsenConjugate_carrier] at hd
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn _ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) at hd
    rw [cayleyMobius_image_openHalfPlane] at hd
    exact hd

/-- Native and original finite disc points are identified by the actual Cayley map. -/
def HalfPlaneFuchsianGroup.cayleyCoordinate {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) : ℍ ≃ₜ P.cayleyData.domain.carrier :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.trans P.cayleyData.finiteCoordinate.symm

theorem HalfPlaneFuchsianGroup.cayleyCoordinate_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (z : ℍ) :
    P.cayleyData.finiteCoordinate (P.cayleyCoordinate z) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z := by
  exact P.cayleyData.finiteCoordinate.apply_symm_apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z)

theorem HalfPlaneFuchsianGroup.cayleyCoordinate_equivariant {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (g : H) (z : ℍ) :
    letI := P.nativeAction
    P.cayleyCoordinate (g • z) =
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H g • P.cayleyCoordinate z := by
  let nativePolygonHalfPlaneAction := P.nativeAction
  apply Subtype.ext
  have hc (w : ℍ) : (P.cayleyCoordinate w).val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint w) := by
    have he := _root_.LowDimensionalTopology.Geometry.Surfaces.discFiniteHomeomorph_symm_coe (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w)
    change _ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (((w : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius_apply,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_halfPlane]
    exact he
  rw [hc]
  change _ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (g.val.val
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm (P.cayleyCoordinate z).val))
  rw [hc,_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm_apply_apply,←P.nativeAction_boundary]

/-- Native hyperbolic area equals the original density area after the genuine Cayley coordinate. -/
theorem HalfPlaneFuchsianGroup.cayleyCoordinate_area_map {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) :
    Measure.map P.cayleyCoordinate volume = P.cayleyData.area := by
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply P.cayleyCoordinate.continuous.measurable hS,P.cayleyData.area_apply S hS,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea_eq_halfPlane_volume _
      (P.cayleyData.finiteCoordinate.measurableEmbedding.measurableSet_image.mpr hS)]
  congr 1
  ext z
  constructor
  · intro hz
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z,⟨P.cayleyCoordinate
      z,hz,P.cayleyCoordinate_finite z⟩,?_⟩
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc z
  · rintro ⟨w,⟨x,hx,hxw⟩,hwz⟩
    change P.cayleyCoordinate z ∈ S
    have hzx : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc z = P.cayleyData.finiteCoordinate x := by
      rw [←hwz,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane,hxw]
    have he : P.cayleyCoordinate z = x :=
      P.cayleyData.finiteCoordinate.injective ((P.cayleyCoordinate_finite z).trans hzx)
    rwa [he]

/-- A native fundamental domain is a genuine fundamental domain for the original conjugate group. -/
theorem HalfPlaneFuchsianGroup.cayley_fundamental {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) {S : Set ℍ} :
    letI := P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume S →
      IsFuchsianFundamentalDomain P.cayleyData (P.cayleyCoordinate '' S) := by
  let nativePolygonHalfPlaneAction := P.nativeAction
  intro hS
  let e := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H
  let f := P.cayleyCoordinate
  have he (g : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H) (x : P.cayleyData.domain.carrier) :
      f.symm (g • x) = e.symm g • f.symm x := by
    apply f.injective
    rw [f.apply_symm_apply,P.cayleyCoordinate_equivariant,e.apply_symm_apply,f.apply_symm_apply]
  have h := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage e.symm f.symm he hS
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain _ _ (Measure.map
    P.cayleyCoordinate volume) (f.symm ⁻¹' S) at h
  rw [P.cayleyCoordinate_area_map] at h
  have hset : f.symm ⁻¹' S = f '' S := (f.toEquiv.image_eq_preimage_symm S).symm
  rwa [hset] at h

/-- Native geodesic convexity transfers to the same original disc polygon. -/
theorem HalfPlaneFuchsianGroup.cayley_convex {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) {S : Set ℍ} (hS : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscHConvex (P.cayleyData.finiteCoordinate '' (P.cayleyCoordinate '' S)) := by
  have he : P.cayleyData.finiteCoordinate '' (P.cayleyCoordinate '' S) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' S := by
    rw [image_image]
    exact image_congr (fun z _ => P.cayleyCoordinate_finite z)
  rw [he]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hConvex_iff_cayley_discHConvex S).mp hS

/-- The compact closed-tile condition transfers with the original group equivalence. -/
theorem HalfPlaneFuchsianGroup.cayley_compact_tiles {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) {S : Set ℍ} :
    letI := P.nativeAction
    (∀ K : Set ℍ, IsCompact K → {g : H | (g • closure S ∩ K).Nonempty}.Finite) →
      ∀ K : Set P.cayleyData.domain.carrier, IsCompact K →
        {g : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H |
          (g • closure (P.cayleyCoordinate '' S) ∩ K).Nonempty}.Finite := by
  let nativePolygonHalfPlaneAction := P.nativeAction
  intro hS K hK
  let e := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius H
  let f := P.cayleyCoordinate
  have hfin := (hS (f.symm '' K) (hK.image f.symm.continuous)).image e
  apply hfin.subset
  intro g hg
  obtain ⟨x,hx,hxK⟩ := hg
  obtain ⟨y,hy,hgy⟩ := hx
  have hyS : f.symm y ∈ closure S := by
    rw [←f.image_closure] at hy
    obtain ⟨w,hw,hew⟩ := hy
    rwa [←hew,f.symm_apply_apply]
  have hz : e.symm g • f.symm y = f.symm x := by
    apply f.injective
    rw [P.cayleyCoordinate_equivariant,e.apply_symm_apply,f.apply_symm_apply,f.apply_symm_apply]
    exact hgy
  refine ⟨e.symm g,⟨f.symm x,?_,⟨x,hxK,rfl⟩⟩,e.apply_symm_apply g⟩
  exact ⟨f.symm y,hyS,hz⟩

/-- Native fundamental, convex and locally finite data give a genuine original-group polygon. -/
theorem HalfPlaneFuchsianGroup.cayley_polygon {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) {S : Set ℍ} :
    letI := P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume S → _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex S →
    (∀ K : Set ℍ, IsCompact K → {g : H | (g • closure S ∩ K).Nonempty}.Finite) →
      IsConvexFuchsianPolygon P.cayleyData (P.cayleyCoordinate '' S) := by
  let nativePolygonHalfPlaneAction := P.nativeAction
  intro hf hc hl
  exact ⟨⟨P.cayley_fundamental hf,P.cayley_compact_tiles hl⟩,P.cayley_convex hc⟩

/-- The same native fundamental domain also has the original half-plane geometric area. -/
theorem HalfPlaneFuchsianGroup.geometric_fundamental {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) {S : Set ℍ} :
    letI := P.nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H ℍ volume S →
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
        P.asFuchsianDisc).carrier
        (geometricModelArea P.asFuchsianDisc)
        (geometricHalfPlaneIdentity P.asFuchsianDisc rfl ⁻¹' S) := by
  let nativePolygonHalfPlaneAction := P.nativeAction
  intro hS
  have he (g : H) (x : (fuchsianGeometricDomain P.asFuchsianDisc).carrier) :
      geometricHalfPlaneIdentity P.asFuchsianDisc rfl (g • x) =
        g • geometricHalfPlaneIdentity P.asFuchsianDisc rfl x := by
    apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
    rw [geometricHalfPlaneIdentity_extended,←P.nativeAction_boundary,
      geometricHalfPlaneIdentity_extended]
    rfl
  have h := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.equivariant_preimage (MulEquiv.refl H)
    (geometricHalfPlaneIdentity P.asFuchsianDisc rfl) he hS
  rw [geometricHalfPlaneIdentity_volume_map] at h
  exact h

/-- The corrected primitive parabolic construction is a genuine convex fundamental polygon. -/
theorem primitive_unitTranslation_Ford_polygon {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hprim : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) :
    IsConvexFuchsianPolygon P.cayleyData (P.cayleyCoordinate '' parabolicFordDomain H) := by
  exact P.cayley_polygon (primitive_unitTranslation_Ford_fundamental P hprim)
    (parabolicFordDomain_hConvex H P.discrete hprim.mem)
    (fun K hK => parabolicFordDomain_compact_hits_finite P hprim.mem K hK)

/-- The exact strict circle exterior intersected with the primitive strip is the same polygon. -/
theorem primitive_unitTranslation_strictFord_polygon {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (hprim : IsPrimitive H
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)) :
    IsConvexFuchsianPolygon P.cayleyData (P.cayleyCoordinate '' parabolicFordStrictStrip H) := by
  rw [←parabolicFordDomain_eq_strictStrip P hprim.mem
    (hprim.generates ∞ (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1)).symm]
  exact primitive_unitTranslation_Ford_polygon P hprim

end LowDimensionalTopology.Geometry.Fuchsian
