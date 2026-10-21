/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.DiscreteGroups.Counting.MobiusCounting
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.ParabolicAffineIsometries
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteDilationGroups
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance elementaryPackingChordalMetric : MetricSpace Mobius.ExtendedComplex := Mobius.complexChordalMetricSpace
local instance elementaryPackingSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex := borel
    Mobius.ExtendedComplex
local instance elementaryPackingSphereBorel : BorelSpace Mobius.ExtendedComplex := ⟨rfl⟩

/-- A continuous equivariant lift to actual H3 pulls its compact-hit condition back to the boundary. -/
theorem mobiusDiscontinuousOn_of_H3_lift (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) {X : Type*} [TopologicalSpace X]
    (e : X → Mobius.ExtendedComplex) (he : Topology.IsEmbedding e)
    (F : X → Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) (hF : Continuous F)
    (hEquiv : ∀ (g : H) (x y : X), g.val.val (e x) = e y → g.val • F x = F y) :
    IsMobiusDiscontinuousOn H (Set.range e) := by
  intro K hK hKe
  let L := e ⁻¹' K
  have hL : IsCompact L := he.isInducing.isCompact_preimage' hK hKe
  apply ((discreteMobius_isDiscontinuous_H3 H hd) (F '' L) (hL.image hF)).subset
  rintro g ⟨_, ⟨z, hz, rfl⟩, hgz⟩
  obtain ⟨x, rfl⟩ := hKe hz
  obtain ⟨y, hy⟩ := hKe hgz
  refine ⟨g.val • F x, ⟨F x, ⟨x, hz, rfl⟩, rfl⟩, y, ?_, (hEquiv g x y hy.symm).symm⟩
  change e y ∈ K
  rwa [hy]

/-- Unit-multiplier affine groups act discontinuously on the finite complex chart. -/
theorem discrete_affine_unit_discontinuous (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hu : ∀ f : H, ‖(Mobius.mobiusMultiplier ⟨f.val, hi f.property⟩ : ℂ)‖ = 1) :
    IsMobiusDiscontinuousOn H (Set.range (fun z : ℂ => (z : Mobius.ExtendedComplex))) := by
  apply mobiusDiscontinuousOn_of_H3_lift H hd _ OnePoint.isOpenEmbedding_coe.isEmbedding
    (fun z : ℂ => Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint z 1 zero_lt_one)
    (continuous_upperHalfSpacePoint_horizontal 1 zero_lt_one)
  intro g x y hxy
  have hxy' : (Mobius.mobiusMultiplier ⟨g.val, hi g.property⟩ : ℂ) * x +
      Mobius.mobiusAffineConstant ⟨g.val, hi g.property⟩ = y := by
    rw [Mobius.mobius_affine_formula ⟨g.val, hi g.property⟩ x] at hxy
    exact OnePoint.coe_injective hxy
  apply Subtype.ext
  rw [Mobius.mobius_affine_representation ⟨g.val, hi g.property⟩]
  change (Mobius.affineMobius _ _ (Units.ne_zero _) • Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint x 1
    zero_lt_one).val = _
  rw [Mobius.affineMobius_smul]
  simp only [Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint_horizontal,
    Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint_height, hu g, one_mul, hxy']
  rfl

/-- Projection from a nonzero finite boundary point to its height on the vertical geodesic. -/
def elementaryAxisLift (z : PuncturedPlane) : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
  Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint 0 ‖z.val‖ (norm_pos_iff.mpr z.property)

theorem elementaryAxisLift_continuous : Continuous elementaryAxisLift := by
  apply Continuous.subtype_mk
  change Continuous (fun z : PuncturedPlane => Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 ‖z.val‖)
  have h := (continuous_subtype_val.norm.smul
    (continuous_const : Continuous (fun _ : PuncturedPlane => Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 1)))
  convert h using 1
  funext z
  change Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 ‖z.val‖ = ‖z.val‖ •
    Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 1
  rw [Mobius.quaternionThreePoint_smul]
  simp only [mul_zero, mul_one]

theorem mobiusScaling_axis_smul (a : ℂˣ) (t : ℝ) (ht : 0 < t) :
    Mobius.mobiusScaling a • Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint 0 t ht =
      Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint 0 (‖(a : ℂ)‖ * t) (mul_pos (norm_pos_iff.mpr a.ne_zero)
        ht) := by
  apply Subtype.ext
  rw [mobiusScaling_eq_affine, Mobius.affineMobius_smul]
  simp only [Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint_horizontal,
    Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint_height, mul_zero, zero_add]
  rfl

theorem mobiusReciprocal_axis_smul (t : ℝ) (ht : 0 < t) :
    mobiusReciprocal • Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint 0 t ht =
      Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint 0 t⁻¹ (inv_pos.mpr ht) := by
  apply Subtype.ext
  change (Mobius.reciprocalMobius • Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint 0 t ht).val = _
  rw [Mobius.reciprocalMobius_smul]
  simp only [Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint,
    Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint,
    Hyperbolic.QuaternionHalfSpace.quaternionHeight_threePoint,
    Mobius.quaternionThreePoint_norm_sq, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_add, map_zero, zero_div]
  congr 1
  field_simp


/-- Both endpoint-fixing and endpoint-exchanging maps preserve the actual vertical lift. -/
theorem elementaryAxisLift_equivariant (f : Mobius.complexMobiusGroup)
    (hf : f ∈ mobiusZeroInftyPairStabilizer) (x y : PuncturedPlane)
    (hxy : f.val (x.val : Mobius.ExtendedComplex) = (y.val : Mobius.ExtendedComplex)) :
    f • elementaryAxisLift x = elementaryAxisLift y := by
  obtain ⟨a, ha | ha⟩ := mobius_zeroInftyPair_normal_form ⟨f, hf⟩
  · change f = Mobius.mobiusScaling a at ha
    subst f
    rw [Mobius.mobiusScaling_coe] at hxy
    have hz : (a : ℂ) * x.val = y.val := OnePoint.coe_injective hxy
    unfold elementaryAxisLift
    rw [mobiusScaling_axis_smul]
    apply Subtype.ext
    change Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 (‖(a : ℂ)‖ * ‖x.val‖) =
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 ‖y.val‖
    congr 1
    rw [← hz, norm_mul]
  · change f = Mobius.mobiusScaling a * mobiusReciprocal at ha
    subst f
    rw [mobiusScaling_mul_reciprocal_coe a x.val x.property] at hxy
    have hz : (a : ℂ) / x.val = y.val := OnePoint.coe_injective hxy
    unfold elementaryAxisLift
    rw [mul_smul, mobiusReciprocal_axis_smul, mobiusScaling_axis_smul]
    apply Subtype.ext
    change Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 (‖(a : ℂ)‖ * ‖x.val‖⁻¹) =
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 ‖y.val‖
    congr 1
    rw [← hz, norm_div, div_eq_mul_inv]

/-- Every discrete actual endpoint-pair group is discontinuous off that pair. -/
theorem discrete_pair_discontinuous (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (hp : H ≤ mobiusZeroInftyPairStabilizer) :
    IsMobiusDiscontinuousOn H (Set.range (fun z : PuncturedPlane => (z.val : Mobius.ExtendedComplex))) := by
  apply mobiusDiscontinuousOn_of_H3_lift H hd _
    (OnePoint.isOpenEmbedding_coe.isEmbedding.comp Topology.IsEmbedding.subtypeVal)
    elementaryAxisLift elementaryAxisLift_continuous
  exact fun g x y hxy => elementaryAxisLift_equivariant g.val (hp g.property) x y hxy

local instance elementaryPackingAreaNullSingleton : MeasureTheory.NullSingletonClass mobiusChordalArea :=
  MeasureTheory.Measure.nullSingletonClass_hausdorff Mobius.ExtendedComplex (by norm_num : (0 : ℝ) < 2)

/-- A nonempty open boundary domain has a point fixed by no nonidentity group element. -/
theorem discreteMobius_open_free_point (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (S : Set Mobius.ExtendedComplex) (hS : IsOpen S) (hne : S.Nonempty) :
    ∃ z ∈ S, ∀ g : H, g.val.val z = z → g = 1 := by
  let : Countable H := Mobius.discreteMobius_countable H hd
  let E : Set Mobius.ExtendedComplex := ⋃ g : {g : H // g ≠ 1}, Function.fixedPoints g.val.val.val
  have hE : mobiusChordalArea E = 0 := by
    apply MeasureTheory.measure_iUnion_null
    intro g
    exact (mobiusCounting_fixedPoints_finite g.val.val
      (fun he => g.property (Subtype.ext he))).countable.measure_zero mobiusChordalArea
  have hnot : ¬S ⊆ E := by
    intro h
    have hle := MeasureTheory.measure_mono (μ := mobiusChordalArea) h
    rw [hE] at hle
    exact (not_le_of_gt (mobiusChordalArea_open_positive _ hS hne)) hle
  obtain ⟨z, hz, hzE⟩ := Set.not_subset.mp hnot
  refine ⟨z, hz, fun g hg => ?_⟩
  by_contra hn
  exact hzE (Set.mem_iUnion.mpr ⟨⟨g, hn⟩, hg⟩)

/-- Discontinuity on a genuine open invariant sphere domain supplies an actual open packing. -/
theorem discreteMobius_openPacking_of_domain (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (S : Set Mobius.ExtendedComplex) (hS : IsOpen S) (hne : S.Nonempty)
    (hInv : ∀ (g : H) z, z ∈ S → g • z ∈ S) (hD : IsMobiusDiscontinuousOn H S) :
    ∃ D : Set Mobius.ExtendedComplex, IsOpen D ∧ D.Nonempty ∧ IsMobiusPacking H D := by
  obtain ⟨z, hz, hfree⟩ := discreteMobius_open_free_point H hd S hS hne
  obtain ⟨q, r, _, _, hdisc, hzD, _, _, hsep⟩ :=
    mobius_discontinuous_roundDisc H S hS hInv hD z hz
  exact ⟨mobiusNormalizedDisc q r, hdisc.isOpen, ⟨z, hzD⟩,
    fun g hg => (hsep g).2 (fun he => hg (hfree g he))⟩

/-- Open packings transport through the actual boundary conjugacy homeomorphism. -/
theorem mobius_openPacking_of_conjugate (H : Subgroup Mobius.complexMobiusGroup) (q : Mobius.complexMobiusGroup)
    (h : ∃ E : Set Mobius.ExtendedComplex, IsOpen E ∧ E.Nonempty ∧
      IsMobiusPacking (DiscreteGroups.Action.Actions.subgroupConjugate q H) E) :
    ∃ D : Set Mobius.ExtendedComplex, IsOpen D ∧ D.Nonempty ∧ IsMobiusPacking H D := by
  obtain ⟨E, hE, ⟨w, hw⟩, hp⟩ := h
  refine ⟨q.val ⁻¹' E, hE.preimage (Mobius.continuous_mobiusBoundary q),
    ⟨q.val.symm w, by simpa only [mem_preimage, Equiv.apply_symm_apply]⟩, ?_⟩
  intro g hg
  let k := DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H g
  have hk : k ≠ 1 := by
    intro he
    exact hg ((DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q H).injective (he.trans (map_one _).symm))
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, rfl⟩ hz
  apply Set.disjoint_left.mp (hp k hk) _ hz
  refine ⟨q.val x, hx, ?_⟩
  change q.val (g.val.val (q.val.symm (q.val x))) = q.val (g.val.val x)
  rw [Equiv.symm_apply_apply]

/-- The finite chart is a nonempty invariant open discontinuity domain for a discrete Euclidean affine group. -/
theorem discrete_affine_unit_openPacking (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (hi : H ≤ Mobius.mobiusInftyStabilizer)
    (hu : ∀ f : H, ‖(Mobius.mobiusMultiplier ⟨f.val, hi f.property⟩ : ℂ)‖ = 1) :
    ∃ D : Set Mobius.ExtendedComplex, IsOpen D ∧ D.Nonempty ∧ IsMobiusPacking H D := by
  apply discreteMobius_openPacking_of_domain H hd (Set.range (fun z : ℂ => (z : Mobius.ExtendedComplex)))
    (OnePoint.isOpenEmbedding_coe.isOpen_range) ⟨(0 : ℂ), 0, rfl⟩ _
    (discrete_affine_unit_discontinuous H hd hi hu)
  rintro g _ ⟨z, rfl⟩
  exact ⟨_, (Mobius.mobius_affine_formula ⟨g.val, hi g.property⟩ z).symm⟩

/-- The punctured finite chart supplies a packing for every discrete endpoint-pair subgroup. -/
theorem discrete_pair_openPacking (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (hp : H ≤ mobiusZeroInftyPairStabilizer) :
    ∃ D : Set Mobius.ExtendedComplex, IsOpen D ∧ D.Nonempty ∧ IsMobiusPacking H D := by
  have he : Topology.IsOpenEmbedding (fun z : PuncturedPlane => (z.val : Mobius.ExtendedComplex)) :=
    OnePoint.isOpenEmbedding_coe.comp puncturedPlaneDomain.isOpen.isOpenEmbedding_subtypeVal
  apply discreteMobius_openPacking_of_domain H hd _ he.isOpen_range
    ⟨(1 : ℂ), ⟨1, one_ne_zero⟩, rfl⟩ _ (discrete_pair_discontinuous H hd hp)
  rintro g _ ⟨z, rfl⟩
  obtain ⟨a, ha | ha⟩ := mobius_zeroInftyPair_normal_form ⟨g.val, hp g.property⟩
  · change g.val = Mobius.mobiusScaling a at ha
    change g.val.val (z.val : Mobius.ExtendedComplex) ∈ _
    rw [ha, Mobius.mobiusScaling_coe]
    exact ⟨⟨(a : ℂ) * z.val, mul_ne_zero a.ne_zero z.property⟩, rfl⟩
  · change g.val = Mobius.mobiusScaling a * mobiusReciprocal at ha
    change g.val.val (z.val : Mobius.ExtendedComplex) ∈ _
    rw [ha, mobiusScaling_mul_reciprocal_coe a z.val z.property]
    exact ⟨⟨(a : ℂ) / z.val, div_ne_zero a.ne_zero z.property⟩, rfl⟩

/-- Every discrete elementary actual Mobius subgroup has a nonempty open sphere packing. -/
theorem discrete_elementary_openPacking (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (hE : IsElementary H) :
    ∃ D : Set Mobius.ExtendedComplex, IsOpen D ∧ D.Nonempty ∧ IsMobiusPacking H D := by
  let : DiscreteTopology H := hd
  by_cases hP : ∃ p ∈ H, Mobius.MobiusParabolic p
  · obtain ⟨p, hpH, hp⟩ := hP
    obtain ⟨q, hi, hu⟩ := discrete_elementary_parabolic_euclidean_coordinates H hd hE p hpH hp
    apply mobius_openPacking_of_conjugate H q
    have hK : Mobius.IsDiscreteMobiusSubgroup (DiscreteGroups.Action.Actions.subgroupConjugate q H) :=
      DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q H
    exact discrete_affine_unit_openPacking _ hK hi (fun f => (hu f).1)
  by_cases hL : ∃ f ∈ H, Mobius.MobiusLoxodromic f
  · obtain ⟨f, hfH, hf⟩ := hL
    obtain ⟨a, b, hab, _, _, hpair⟩ := discrete_elementary_loxodromic_fixed_pair H hd hE f hfH hf
    obtain ⟨q, hq⟩ := mobius_invariant_pair_conjugate_zeroInftyPairStabilizer H a b hab hpair
    apply mobius_openPacking_of_conjugate H q
    exact discrete_pair_openPacking _ (DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q H) hq
  have hall : ∀ f ∈ H, f ≠ 1 → Mobius.MobiusElliptic f := by
    intro f hf hn
    rcases Mobius.mobius_nonidentity_type_trichotomy f hn with hp | hl | he
    · exact False.elim (hP ⟨f, hf, hp⟩)
    · exact False.elim (hL ⟨f, hf, hl⟩)
    · exact he
  obtain ⟨q, hq⟩ := (Mobius.all_nonidentity_elliptic_iff_common_halfSpace_fixedPoint H).mp hall
  let : Finite H := discreteMobius_finite_of_common_H3_fixed H hd q hq
  exact discreteMobius_openPacking_of_domain H hd Set.univ isOpen_univ Set.univ_nonempty
    (fun _ _ _ => trivial) (fun _ _ _ => Set.toFinite _)

/-- Critical normalized-norm convergence in the elementary branch needs no ordinary-set hypothesis. -/
theorem summable_normalizedNorm_inv_four_of_elementary (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (hE : IsElementary H) :
    Summable (fun g : H => (Mobius.mobiusNormalizedNorm g.val ^ 4)⁻¹) := by
  obtain ⟨D, hD, hne, hp⟩ := discrete_elementary_openPacking H hd hE
  exact mobiusCounting_critical_summable_of_openPacking H D hD hne hp

/-- Summability of inverse fourth powers of normalized norms, including elementary and non-elementary groups. -/
theorem summable_normalizedNorm_inv_four_of_ordinarySet_nonempty (H : Subgroup Mobius.complexMobiusGroup)
    (hd : Mobius.IsDiscreteMobiusSubgroup H) (hne : (mobiusOrdinarySet H).Nonempty) :
    Summable (fun g : H => (Mobius.mobiusNormalizedNorm g.val ^ 4)⁻¹) := by
  by_cases hE : IsElementary H
  · exact summable_normalizedNorm_inv_four_of_elementary H hd hE
  · exact summable_normalizedNorm_inv_four_of_nonElementary_ordinarySet H hE hd hne

end LowDimensionalTopology.Geometry.DiscreteGroups
