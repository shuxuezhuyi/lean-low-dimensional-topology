module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Packing.PackingExample
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordFundamentalDomains

/-! Actual counterexamples to omitted stabilizer-maximality conditions in the coset examples. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped Pointwise OnePoint UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
noncomputable section

/-- The actual discrete group of translations by half-integers. -/
def parabolicHalfTranslationGroup : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (((1/2 : ℝ)) : ℂ))

theorem parabolicHalfTranslationGroup_discrete : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup parabolicHalfTranslationGroup := by
  have ht : (0 : ℝ) < 1/2 := by norm_num
  let D := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingVerticalStrip (1/2)
  have hp : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusPacking parabolicHalfTranslationGroup D := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingVerticalStrip_translation_packing ht
  have ho : IsOpen D := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingVerticalStrip_isOpen _
  have hn : D.Nonempty := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingVerticalStrip_nonempty ht
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_open_discrete _ _ (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSaturation_isOpen _ ho)
    (hn.mono (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.subset_mobiusSaturation _
      _)) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_openPacking_saturation_discontinuous _ _ ho hp)

theorem coset_realTranslation_image_halfPlane (t : ℝ) :
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (t : ℂ)).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  apply Subset.antisymm
  · rintro _ ⟨_,⟨z,hz,rfl⟩,rfl⟩
    change 0 < z.im at hz
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_openHalfPlaneSet]
    simpa only [Complex.add_im,Complex.ofReal_im,add_zero] using hz
  · rintro _ ⟨z,hz,rfl⟩
    change 0 < z.im at hz
    refine ⟨((z - t : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),⟨z-t,?_,rfl⟩,?_⟩
    · change 0 < (z - (t : ℂ)).im
      simpa only [Complex.sub_im,Complex.ofReal_im,sub_zero] using hz
    · rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe,sub_add_cancel]

theorem parabolicHalfTranslationGroup_fixes_infty (g : parabolicHalfTranslationGroup) :
    g.val.val ∞ = ∞ := by
  obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
  rw [←hn,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingTranslation_zpow,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty]

/-- This is a genuine Fuchsian group in the same original half-plane model as. -/
theorem parabolicHalfTranslationFuchsian : HalfPlaneFuchsianGroup parabolicHalfTranslationGroup where
  preserves g := by
    obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp g.property
    rw [←hn,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingTranslation_zpow]
    have he : (n : ℂ) * (((1/2 : ℝ)) : ℂ) = (((n : ℝ) / 2 : ℝ) : ℂ) := by push_cast;ring
    rw [he]
    exact coset_realTranslation_image_halfPlane _
  discrete := parabolicHalfTranslationGroup_discrete

/-- All actual group elements are affine, so the common exterior has no circle constraints at all. -/
theorem parabolicHalfTranslationGroup_Ford_univ : strictFordRegion parabolicHalfTranslationGroup = univ := by
  apply Set.eq_univ_of_forall
  intro z A hA hc
  exact False.elim (hc ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff A).mp
    (parabolicHalfTranslationGroup_fixes_infty ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hA⟩)))

/-- The original unit translation belongs to the larger actual half-translation group. -/
theorem parabolicHalfTranslationGroup_contains_unit : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ parabolicHalfTranslationGroup := by
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨2,?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingTranslation_zpow]
  norm_num

/-- The translation omitted by the nonmaximal unit subgroup still fixes the parabolic endpoint. -/
theorem parabolicHalfTranslation_not_unitSubgroup : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (1/2) ∉
    Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1) := by
  rintro ⟨n,hn⟩
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ^ n = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (1/2) at hn
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.packingTranslation_zpow] at hn
  have he := congrArg (fun f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup => f.val ((0 : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) hn
  simp only [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe,zero_add,mul_one] at he
  have hr := congrArg Complex.re (OnePoint.coe_injective he)
  norm_num at hr
  have hcast : (2 : ℝ) * (n : ℝ) = 1 := by linarith
  have hi : (2 : ℤ) * n = 1 := by exact_mod_cast hcast
  omega

/-- The true native real matrix translation is the original sphere translation. -/
theorem coset_realSLTranslation (t : ℝ) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (t : ℂ) := by
  apply mobius_ext_on_halfPlane
  intro z
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]

/-- The literal width-one strip in this formulation fails the orbit-selector condition for this genuine group. -/
theorem parabolicHalfTranslation_widthOne_not_fundamental :
    letI := parabolicHalfTranslationFuchsian.nativeAction
    ¬ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain parabolicHalfTranslationGroup ℍ volume
      (strictFordRegion parabolicHalfTranslationGroup ∩ {z : ℍ | 0 < z.re ∧ z.re < 1}) := by
  let parabolicCounterexampleAction := parabolicHalfTranslationFuchsian.nativeAction
  intro hD
  let z : ℍ := ⟨(1/4 : ℂ) + Complex.I,by norm_num⟩
  let w : ℍ := ⟨(3/4 : ℂ) + Complex.I,by norm_num⟩
  have hz : z ∈ strictFordRegion parabolicHalfTranslationGroup ∩ {z : ℍ | 0 < z.re ∧ z.re < 1} := by
    rw [parabolicHalfTranslationGroup_Ford_univ]
    norm_num [z]
  have hw : w ∈ strictFordRegion parabolicHalfTranslationGroup ∩ {z : ℍ | 0 < z.re ∧ z.re < 1} := by
    rw [parabolicHalfTranslationGroup_Ford_univ]
    norm_num [w]
  let g : parabolicHalfTranslationGroup :=
    ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (((1/2 : ℝ)) : ℂ),Subgroup.mem_zpowers _⟩
  have hgw : g • z = w := by
    rw [parabolicHalfTranslationFuchsian.nativeAction_realSL g
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (1/2))
      (coset_realSLTranslation (1/2))]
    apply UpperHalfPlane.coe_injective
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
    dsimp [z,w]
    push_cast
    ring
  have he : w = z := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.eq_of_mem parabolicHalfTranslationGroup ℍ hD hw hz
    (Quotient.sound ⟨g,hgw⟩)
  have hr := congrArg UpperHalfPlane.re he
  norm_num [z,w] at hr

end
end LowDimensionalTopology.Geometry.Fuchsian
