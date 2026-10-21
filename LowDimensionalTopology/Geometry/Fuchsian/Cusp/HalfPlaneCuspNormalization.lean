/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.FuchsianCuspCompletion
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeFuchsianPolygons
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis Set
open scoped OnePoint UpperHalfPlane

/-- A genuine normalized cusp also makes its original invariant half-plane horizontal. -/
theorem halfPlane_cusp_normalizer_parent_image {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) {S:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset
      P.asFuchsianDisc.domain} {w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization S w) :
    ∃d:ℝ,C.normalizer.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere d := by
  let D:=P.asFuchsianDisc.domain.conjugate C.normalizer
  have hmem:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate C.normalizer H:=C.normalized_translation_mem
  have hpres:(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1).val '' D.carrier=D.carrier:=by
    apply subset_antisymm
    · rintro z ⟨x,hx,rfl⟩
      exact D.invariant ⟨_,hmem⟩ x hx
    · intro z hz
      refine ⟨(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)⁻¹.val z,D.invariant
        ⟨_,(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate C.normalizer
        H).inv_mem hmem⟩ z hz,?_⟩
      exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1).val.apply_symm_apply z
  obtain ⟨d,hu|hl⟩:=_root_.LowDimensionalTopology.Geometry.Surfaces.parabolicTranslationDisc_eq_halfPlane (P.asFuchsianDisc.isDisc.image C.normalizer) hpres
  · exact ⟨d,hu⟩
  · have hsub:_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere C.height⊆D.carrier:=by
      rw [←C.disc_eq]
      exact image_mono S.subset_domain
    let z:ℂ:=⟨0,max C.height d+1⟩
    have hz:(z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere C.height:=⟨z,by
      change C.height<max C.height d+1
      linarith [le_max_left C.height d],rfl⟩
    have hlow:=hsub hz
    change (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈C.normalizer.val '' P.asFuchsianDisc.carrier at hlow
    rw [hl] at hlow
    obtain ⟨u,hu,huz⟩:=hlow
    have hue:u=z:=OnePoint.coe_injective huz
    rw [hue] at hu
    change max C.height d+1<d at hu
    linarith [le_max_right C.height d]

/-- Literal vertical translation carries the true horizontal cusp half-plane to its shifted height. -/
theorem cusp_vertical_translation_image (s h:ℝ) :
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,s⟩:ℂ)).val '' _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere h=_root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere (h+s) := by
  ext p
  constructor
  · rintro ⟨q,⟨z,hz,rfl⟩,rfl⟩
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
    refine ⟨z+⟨0,s⟩,?_,rfl⟩
    change h+s<z.im+s
    change h<z.im at hz
    linarith
  · rintro ⟨z,hz,rfl⟩
    refine ⟨((z-⟨0,s⟩:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),⟨z-⟨0,s⟩,?_,rfl⟩,?_⟩
    · change h<z.im-s
      change h+s<z.im at hz
      linarith
    · rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe,sub_add_cancel]

/-- Correcting only the vertical origin makes the actual cusp normalization an actual native real-SL isometry. -/
theorem halfPlane_cusp_normalizer_native {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) {S:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset
      P.asFuchsianDisc.domain} {w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization S w) :
    ∃d:ℝ,∃A:Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,-d⟩:ℂ)*C.normalizer ∧
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val w=∞ := by
  obtain ⟨d,hd⟩:=halfPlane_cusp_normalizer_parent_image P C
  let q:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,-d⟩:ℂ)*C.normalizer
  have hq:q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    change (fun z=> (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,-d⟩:ℂ)).val
      (C.normalizer.val z)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_
    rw [←image_image,hd,cusp_vertical_translation_image,add_neg_cancel]
    rfl
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL q hq
  refine ⟨d,A,hA,?_⟩
  rw [hA]
  change (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,-d⟩:ℂ)).val (C.normalizer.val w)=∞
  rw [C.cusp_eq,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty]


/-- The chosen native coordinate differs from the actual cusp coordinate only by its proved vertical origin. -/
theorem halfPlane_cusp_normalizer_coordinates {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P:HalfPlaneFuchsianGroup H) {S:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSubset
      P.asFuchsianDisc.domain} {w:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex}
    (C:_root_.LowDimensionalTopology.Geometry.Surfaces.MobiusCuspNormalization S w) (d:ℝ) (A:Matrix.SpecialLinearGroup
      (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,-d⟩:ℂ)*C.normalizer) (z:ℍ) :
    C.normalizer.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)=(((A•z:ℍ):ℂ)+⟨0,d⟩:ℂ) := by
  have he:_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (A•z)=
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,-d⟩:ℂ)).val (C.normalizer.val
        (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)):=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A z).symm.trans
      (congrArg (fun f:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup=>f.val
        (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)) hA)
  have he':=congrArg (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
    (⟨0,-d⟩:ℂ)).val.symm he.symm
  rw [Equiv.symm_apply_apply] at he'
  have hInv:(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,-d⟩:ℂ))⁻¹=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (⟨0,d⟩:ℂ):=by
    rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_neg]
    congr 1
    apply Complex.ext <;> simp
  change C.normalizer.val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint z)=
    ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation
      (⟨0,-d⟩:ℂ))⁻¹).val (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (A•z)) at he'
  rw [hInv] at he'
  exact he'.trans (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe _ ((A•z:ℍ):ℂ))

end LowDimensionalTopology.Geometry.Fuchsian
