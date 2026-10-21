/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.FiniteOrbit

public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.Mobius
public import LowDimensionalTopology.Geometry.Mobius.Classification.MobiusTypes
public import LowDimensionalTopology.Geometry.Mobius.Rotation.RotationalGroups

@[expose] public section

open Set
open scoped OnePoint

namespace LowDimensionalTopology.Geometry.DiscreteGroups

open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

noncomputable section

theorem standardElement_pow_height (k : ℂˣ) (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) (m : ℕ) :
    Hyperbolic.QuaternionHalfSpace.quaternionHeight (((Mobius.mobiusStandardElement k) ^ m • q).val) =
      ‖(k : ℂ)‖ ^ m * Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_smul, Mobius.mobiusStandardElement_smul_val,
      Hyperbolic.QuaternionHalfSpace.quaternionHeight_threePoint, ih]
    rw [pow_succ']
    ring

theorem standardTranslation_pow_horizontal_re (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) (m : ℕ) :
    (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal (((Mobius.mobiusStandardElement 1) ^ m • q).val)).re =
      (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val).re + (m : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_smul, Mobius.mobiusStandardElement_smul_val,
      Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint]
    simp only [Units.val_one, ite_true, one_mul, Complex.add_re, Complex.one_re, ih,
      Nat.cast_add, Nat.cast_one]
    ring

theorem standardElement_periodic_H3_elliptic (k : ℂˣ) (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace)
    (m : ℕ) (hm : 0 < m) (hfix : (Mobius.mobiusStandardElement k) ^ m • q = q) :
    Mobius.MobiusElliptic (Mobius.mobiusStandardElement k) := by
  have hk1 : (k : ℂ) ≠ 1 := by
    intro hk
    have hku : k = 1 := Units.ext hk
    subst k
    have ht := congrArg (fun p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
      (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal p.val).re) hfix
    rw [standardTranslation_pow_horizontal_re] at ht
    have hmr : (m : ℝ) = 0 := by linarith
    exact hm.ne' (Nat.cast_eq_zero.mp hmr)
  have hh := congrArg (fun p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
    Hyperbolic.QuaternionHalfSpace.quaternionHeight p.val) hfix
  rw [standardElement_pow_height] at hh
  have hp : Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val ≠ 0 := q.property.ne'
  have hpow : ‖(k : ℂ)‖ ^ m = 1 := (mul_eq_right₀ hp).mp hh
  have hnorm := (pow_eq_one_iff_of_nonneg (norm_nonneg (k : ℂ)) hm.ne').mp hpow
  exact Mobius.mobiusStandardElement_isElliptic k hk1 hnorm

theorem conjugate_pow_smul {G X : Type*} [Group G] [MulAction G X]
    (g f : G) (m : ℕ) (x : X) :
    (g * f * g⁻¹) ^ m • (g • x) = g • (f ^ m • x) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_smul, ih]
    simp only [mul_smul, inv_smul_smul, pow_succ']

/-- A nonidentity map with a positive-periodic actual H3 point is elliptic. -/
theorem mobius_periodic_H3_elliptic (f : Mobius.complexMobiusGroup) (hf : f ≠ 1)
    (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) (m : ℕ) (hm : 0 < m) (hfix : f ^ m • q = q) :
      Mobius.MobiusElliptic f := by
  obtain ⟨k, hc⟩ := Mobius.mobius_nonidentity_conjugate_standard f hf
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  have hs : (Mobius.mobiusStandardElement k) ^ m • (g • q) = g • q := by
    rw [← hg, conjugate_pow_smul, hfix]
  exact (Mobius.mobiusElliptic_isConj hc).mpr (standardElement_periodic_H3_elliptic k (g • q) m hm hs)

/-- Every nonidentity element of a group with a finite actual H3 orbit is elliptic. -/
theorem finite_H3_orbit_all_elliptic (H : Subgroup Mobius.complexMobiusGroup) (q :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace)
    (hq : (MulAction.orbit H q).Finite) : ∀ f ∈ H, f ≠ 1 → Mobius.MobiusElliptic f := by
  intro f hf hn
  obtain ⟨m, hm, hfix⟩ := DiscreteGroups.Action.exists_positive_power_fixing_finite_orbit q hq (⟨f, hf⟩ : H)
  apply mobius_periodic_H3_elliptic f hn q m hm
  have hh := hfix q (MulAction.mem_orbit_self q)
  change (((⟨f, hf⟩ : H) ^ m : H) : Mobius.complexMobiusGroup) • q = q at hh
  simpa only [Subgroup.coe_pow] using hh

/-- The actual common fixed point follows from the complete elliptic-group theorem. -/
theorem finite_H3_orbit_common_fixed (H : Subgroup Mobius.complexMobiusGroup) (q :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace)
    (hq : (MulAction.orbit H q).Finite) :
    ∃ p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, ∀ f ∈ H, f • p = p :=
  (Mobius.all_nonidentity_elliptic_iff_common_halfSpace_fixedPoint H).mp (finite_H3_orbit_all_elliptic H q hq)

/-- The two finite-orbit witnesses in the Type 1 discussion: an interior orbit,
or a boundary orbit with at least three points. -/
def HasTypeOneOrbit (H : Subgroup Mobius.complexMobiusGroup) : Prop :=
  DiscreteGroups.Action.HasFiniteOrbit H Hyperbolic.QuaternionHalfSpace.UpperHalfSpace ∨
    ∃ z : Mobius.ExtendedComplex, (MulAction.orbit H z).Finite ∧ 2 < (MulAction.orbit H z).ncard

theorem hasTypeOneOrbit_iff_common_H3_fixed (H : Subgroup Mobius.complexMobiusGroup) :
    HasTypeOneOrbit H ↔ ∃ p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, ∀ f ∈ H, f • p = p := by
  constructor
  · rintro (⟨q, hq⟩ | ⟨z, hz, hcard⟩)
    · exact finite_H3_orbit_common_fixed H q hq
    · let : Finite H := mobius_finite_of_finite_boundary_orbit H z hz hcard
      exact Mobius.mobius_finite_subgroup_common_H3_fixed H
  · rintro ⟨q, hq⟩
    exact Or.inl (DiscreteGroups.Action.hasFiniteOrbit_of_fixed q (fun f : H => hq f.val f.property))

theorem hasTypeOneOrbit_iff_all_elliptic (H : Subgroup Mobius.complexMobiusGroup) :
    HasTypeOneOrbit H ↔ ∀ f ∈ H, f ≠ 1 → Mobius.MobiusElliptic f :=
  (hasTypeOneOrbit_iff_common_H3_fixed H).trans (Mobius.all_nonidentity_elliptic_iff_common_halfSpace_fixedPoint H).symm

theorem hasTypeOneOrbit_isElementary (H : Subgroup Mobius.complexMobiusGroup)
    (h : HasTypeOneOrbit H) : IsElementary H := by
  obtain ⟨q, hq⟩ := (hasTypeOneOrbit_iff_common_H3_fixed H).mp h
  exact isElementary_of_interior_fixed H q (fun f => hq f.val f.property)

/-- The actual interior inclusion into the full compactified three-space. -/
def typeOneUpperEmbedding (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) : Inversive.ExtendedEuclidean 3 :=
  ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val : Inversive.Euclidean 3) :
    Inversive.ExtendedEuclidean 3)

theorem typeOneUpperEmbedding_injective : Function.Injective typeOneUpperEmbedding := by
  intro q r h
  apply Subtype.ext
  exact Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm.injective (OnePoint.coe_injective h)

theorem typeOneUpperEmbedding_equivariant (f : Mobius.complexMobiusGroup) (q :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    typeOneUpperEmbedding (f • q) = f • typeOneUpperEmbedding q :=
  (Mobius.mobiusGeometricPoincare_apply f q).symm

theorem typeOneUpperEmbedding_mem (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    typeOneUpperEmbedding q ∈ Hyperbolic.poincareHalfSpaceSet 2 1 := by
  rw [typeOneUpperEmbedding, Hyperbolic.poincareHalfSpaceSet_coe]
  have hh := Mobius.euclideanThreeQuaternion_symm_height q.val
  simpa only [one_mul, hh] using (show 0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val from q.property)

theorem exists_typeOneUpperEmbedding_of_mem (x : Inversive.ExtendedEuclidean 3)
    (hx : x ∈ Hyperbolic.poincareHalfSpaceSet 2 1) : ∃ q, typeOneUpperEmbedding q = x := by
  induction x using OnePoint.rec with
  | infty => simp [Hyperbolic.poincareHalfSpaceSet_infty] at hx
  | coe x =>
    have hp : 0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight
      (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x) := by
      rw [Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion_height]
      simpa only [Hyperbolic.poincareHalfSpaceSet_coe, one_mul, show (Fin.last 2 : Fin 3) = 2 from rfl] using hx
    refine ⟨⟨Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x, hp⟩, ?_⟩
    simp [typeOneUpperEmbedding]

theorem elementaryBoundaryReflection_lower_mem_upper {x : Inversive.ExtendedEuclidean 3}
    (hx : x ∈ Hyperbolic.poincareHalfSpaceSet 2 (-1)) :
    elementaryBoundaryReflection x ∈ Hyperbolic.poincareHalfSpaceSet 2 1 := by
  induction x using OnePoint.rec with
  | infty => simp [Hyperbolic.poincareHalfSpaceSet_infty] at hx
  | coe x =>
    rw [elementaryBoundaryReflection, Inversive.planeReflectionHomeomorph_apply, Inversive.planeReflection_coe,
      Hyperbolic.poincareHalfSpaceSet_coe]
    have hh : x 2 < 0 := by
      simpa only [Hyperbolic.poincareHalfSpaceSet_coe, show (Fin.last 2 : Fin 3) = 2 from rfl,
        neg_mul, one_mul, neg_pos] using hx
    simpa only [one_mul, show (Fin.last 2 : Fin 3) = 2 from rfl,
      elementaryBoundaryReflection_height, neg_pos] using hh

theorem elementaryHalfSpaceFold_mem_upper_of_not_boundary {x : Inversive.ExtendedEuclidean 3}
    (hx : x ∉ Inversive.plane elementaryBoundaryNormal 0) :
    elementaryHalfSpaceFold x ∈ Hyperbolic.poincareHalfSpaceSet 2 1 := by
  classical
  have hu : x ∈ Hyperbolic.poincareHalfSpaceSet 2 1 ∪ Hyperbolic.poincareHalfSpaceSet 2 (-1) := by
    simpa only [elementaryBoundaryPlane_eq, mem_compl_iff, not_not] using hx
  rw [elementaryHalfSpaceFold]
  split_ifs with hn
  · exact elementaryBoundaryReflection_lower_mem_upper hn
  · exact hu.resolve_right hn

/-- The actual boundary chart into the same full compactified three-space. -/
def typeOneBoundaryEmbedding (z : Mobius.ExtendedComplex) : Inversive.ExtendedEuclidean 3 :=
  Inversive.extendedEquatorialEmbedding 2 (Mobius.extendedComplexEuclideanHomeomorph z)

theorem typeOneBoundaryEmbedding_injective : Function.Injective typeOneBoundaryEmbedding :=
  (Inversive.extendedEquatorialEmbedding_injective 2).comp Mobius.extendedComplexEuclideanHomeomorph.injective

theorem typeOneBoundaryEmbedding_range : range typeOneBoundaryEmbedding =
    Inversive.plane elementaryBoundaryNormal 0 := by
  change range (Inversive.extendedEquatorialEmbedding 2 ∘ Mobius.extendedComplexEuclideanHomeomorph) = _
  rw [range_comp, Mobius.extendedComplexEuclideanHomeomorph.surjective.range_eq, image_univ,
    Inversive.extendedEquatorialEmbedding_range]
  rfl

theorem typeOneBoundaryEmbedding_equivariant (f : Mobius.complexMobiusGroup) (z : Mobius.ExtendedComplex) :
    typeOneBoundaryEmbedding ((f : Equiv.Perm Mobius.ExtendedComplex) z) =
      f • typeOneBoundaryEmbedding z := by
  have h := congrArg (fun k : Equiv.Perm Mobius.ExtendedComplex => k z)
    (Mobius.mobiusRealRepresentative_coordinates f)
  have he : (Mobius.mobiusRealRepresentative f : Inversive.ExtendedHomeomorph 2)
      (Mobius.extendedComplexEuclideanHomeomorph z) =
      Mobius.extendedComplexEuclideanHomeomorph ((f : Equiv.Perm Mobius.ExtendedComplex) z) := by
    apply Mobius.extendedComplexEuclideanHomeomorph.symm.injective
    simpa only [Mobius.euclideanToComplexHom_apply, Homeomorph.symm_apply_apply] using h
  have hb := Hyperbolic.poincareExtension_extendsBoundary (Mobius.mobiusRealRepresentative f)
    (Mobius.extendedComplexEuclideanHomeomorph z)
  change (Mobius.mobiusGeometricPoincare f : Inversive.ExtendedHomeomorph 3) (typeOneBoundaryEmbedding z) =
    Inversive.extendedEquatorialEmbedding 2 ((Mobius.mobiusRealRepresentative f : Inversive.ExtendedHomeomorph 2)
      (Mobius.extendedComplexEuclideanHomeomorph z)) at hb
  rw [he] at hb
  exact hb.symm

/-- Type 1 expressed on the geometric actual full compactified three-space. -/
def HasFullTypeOneOrbit (H : Subgroup Mobius.complexMobiusGroup) : Prop :=
  ∃ x : Inversive.ExtendedEuclidean 3, (MulAction.orbit H x).Finite ∧
    (2 < (MulAction.orbit H x).ncard ∨ x ∉ Inversive.plane elementaryBoundaryNormal 0)

theorem hasFullTypeOneOrbit_iff (H : Subgroup Mobius.complexMobiusGroup) :
    HasFullTypeOneOrbit H ↔ HasTypeOneOrbit H := by
  constructor
  · rintro ⟨x, hx, hcase⟩
    by_cases hb : x ∈ Inversive.plane elementaryBoundaryNormal 0
    · have hc : 2 < (MulAction.orbit H x).ncard := hcase.resolve_right (not_not.mpr hb)
      have hr : x ∈ range typeOneBoundaryEmbedding := by
        rw [typeOneBoundaryEmbedding_range]
        exact hb
      obtain ⟨z, rfl⟩ := hr
      have heq := DiscreteGroups.Action.orbit_image_of_equivariant_map typeOneBoundaryEmbedding
        (fun (g : H) z => typeOneBoundaryEmbedding_equivariant g.val z) z
      rw [← heq] at hx hc
      refine Or.inr ⟨z, (finite_image_iff typeOneBoundaryEmbedding_injective.injOn).mp hx, ?_⟩
      rwa [ncard_image_of_injective _ typeOneBoundaryEmbedding_injective] at hc
    · have hp := elementaryHalfSpaceFold_mem_upper_of_not_boundary hb
      obtain ⟨q, hq⟩ := exists_typeOneUpperEmbedding_of_mem (elementaryHalfSpaceFold x) hp
      have heq := DiscreteGroups.Action.orbit_image_of_equivariant_map elementaryHalfSpaceFold
        (fun (g : H) z => elementaryHalfSpaceFold_equivariant
          (Mobius.mobiusGeometricPoincare g.val) (Mobius.mobiusGeometricPoincare g.val).property
          (Mobius.mobiusGeometricPoincare_preservesHalfSpaces g.val) z) x
      have hfin : (MulAction.orbit H (elementaryHalfSpaceFold x)).Finite := by
        rw [← heq]
        exact hx.image elementaryHalfSpaceFold
      rw [← hq, ← DiscreteGroups.Action.orbit_image_of_equivariant_map typeOneUpperEmbedding
        (fun (g : H) q => typeOneUpperEmbedding_equivariant g.val q)] at hfin
      exact Or.inl ⟨q, (finite_image_iff typeOneUpperEmbedding_injective.injOn).mp hfin⟩
  · rintro (⟨q, hq⟩ | ⟨z, hz, hcard⟩)
    · refine ⟨typeOneUpperEmbedding q, ?_, Or.inr ?_⟩
      · rw [← DiscreteGroups.Action.orbit_image_of_equivariant_map typeOneUpperEmbedding
          (fun (g : H) q => typeOneUpperEmbedding_equivariant g.val q)]
        exact hq.image typeOneUpperEmbedding
      · rw [elementaryBoundaryPlane_eq]
        exact fun h => h (Or.inl (typeOneUpperEmbedding_mem q))
    · have heq := DiscreteGroups.Action.orbit_image_of_equivariant_map typeOneBoundaryEmbedding
        (fun (g : H) z => typeOneBoundaryEmbedding_equivariant g.val z) z
      refine ⟨typeOneBoundaryEmbedding z, ?_, Or.inl ?_⟩
      · rw [← heq]
        exact hz.image typeOneBoundaryEmbedding
      · rw [← heq, ncard_image_of_injective _ typeOneBoundaryEmbedding_injective]
        exact hcard

theorem hasFullTypeOneOrbit_iff_common_H3_fixed (H : Subgroup Mobius.complexMobiusGroup) :
    HasFullTypeOneOrbit H ↔ ∃ p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, ∀ f ∈ H, f • p = p :=
  (hasFullTypeOneOrbit_iff H).trans (hasTypeOneOrbit_iff_common_H3_fixed H)


theorem typeOne_orbit_subset_boundary_iff (H : Subgroup Mobius.complexMobiusGroup)
    (x : Inversive.ExtendedEuclidean 3) :
    MulAction.orbit H x ⊆ Inversive.plane elementaryBoundaryNormal 0 ↔
      x ∈ Inversive.plane elementaryBoundaryNormal 0 := by
  constructor
  · intro h
    exact h (MulAction.mem_orbit_self x)
  · intro hx
    rintro _ ⟨g, rfl⟩
    have hi : (Mobius.mobiusGeometricPoincare g.val : Inversive.ExtendedHomeomorph 3) ''
        Inversive.plane elementaryBoundaryNormal 0 = Inversive.plane elementaryBoundaryNormal 0 := by
      rw [elementaryBoundaryPlane_eq,
        (Mobius.mobiusGeometricPoincare g.val : Inversive.ExtendedHomeomorph 3).image_compl,
        image_union, Mobius.mobiusGeometricPoincare_preservesHalfSpaces g.val 1,
        Mobius.mobiusGeometricPoincare_preservesHalfSpaces g.val (-1)]
    change (Mobius.mobiusGeometricPoincare g.val : Inversive.ExtendedHomeomorph 3) x ∈ _
    rw [← hi]
    exact ⟨x, hx, rfl⟩

/-- The full-space witness is exactly the source alternative of a large orbit or an orbit
not contained in the compactified boundary plane. -/
theorem hasFullTypeOneOrbit_iff_orbit_condition (H : Subgroup Mobius.complexMobiusGroup) :
    HasFullTypeOneOrbit H ↔
      ∃ x : Inversive.ExtendedEuclidean 3, (MulAction.orbit H x).Finite ∧
        (2 < (MulAction.orbit H x).ncard ∨
          ¬MulAction.orbit H x ⊆ Inversive.plane elementaryBoundaryNormal 0) := by
  simp only [HasFullTypeOneOrbit, typeOne_orbit_subset_boundary_iff]

theorem mobiusRealRepresentative_preservesOrientation (f : Mobius.complexMobiusGroup) :
    Inversive.PreservesOrientation (Mobius.mobiusRealRepresentative f : Inversive.ExtendedHomeomorph 2) := by
  obtain ⟨g, hg, hgo, hgf⟩ := (Mobius.mem_complexMobiusGroup_iff_real (f : Equiv.Perm Mobius.ExtendedComplex)).mp
    f.property
  have he : (Mobius.mobiusRealRepresentative f : Inversive.ExtendedHomeomorph 2) = g := by
    apply Mobius.euclideanToComplexHom_injective
    rw [Mobius.mobiusRealRepresentative_coordinates, hgf]
  rw [he]
  exact hgo

theorem mobiusBallConjugate_rotation_of_fixJ (f : Mobius.complexMobiusGroup)
    (hf : f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) :
    ∃ L : Mobius.rotationGroupThree, Mobius.mobiusBallConjugate f = Inversive.cartanLinearExtensionHom L.val := by
  obtain ⟨L, hL⟩ := (Mobius.mobiusBallConjugate_orthogonal_iff_fixJ f).mpr hf
  obtain ⟨g, hg, hgo⟩ := Mobius.orthogonal_ball_boundary L
  have hge : (Hyperbolic.poincareExtension g : Inversive.ExtendedHomeomorph 3) =
      (Hyperbolic.poincareExtension (Mobius.mobiusRealRepresentative f) : Inversive.ExtendedHomeomorph 3) := by
    rw [hg, ← hL]
    unfold Mobius.cayleyPullback Mobius.mobiusBallConjugate Mobius.mobiusGeometricPoincare
    group
  have hgr : g = Mobius.mobiusRealRepresentative f :=
    Hyperbolic.poincareExtensionHom_injective (Subtype.ext hge)
  have hpos : Inversive.PreservesOrientation (Inversive.cartanLinearExtensionHom L) :=
    hgo.mp (by rw [hgr]; exact mobiusRealRepresentative_preservesOrientation f)
  have hmem : Inversive.cartanLinearExtensionHom L ∈ Inversive.generalMobiusGroup 3 := by
    rw [← hL]
    exact Mobius.mobiusBallConjugate_mem f
  exact ⟨⟨L, hmem, hpos⟩, hL⟩

theorem mobius_fixJ_iff_mem_rotationMobius_range (f : Mobius.complexMobiusGroup) :
    f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ↔ f ∈
      Mobius.rotationMobiusHom.range := by
  constructor
  · intro hf
    obtain ⟨L, hL⟩ := mobiusBallConjugate_rotation_of_fixJ f hf
    refine ⟨L, ?_⟩
    apply Mobius.mobiusBallConjugateHom_injective
    change Mobius.mobiusBallConjugate (Mobius.rotationMobius L) = Mobius.mobiusBallConjugate f
    rw [Mobius.rotationMobius_ball, hL]
  · rintro ⟨L, rfl⟩
    apply (Mobius.mobiusBallConjugate_orthogonal_iff_fixJ _).mp
    exact ⟨L.val, Mobius.rotationMobius_ball L⟩

theorem mobius_stabilizer_J_eq_rotationMobius_range :
    MulAction.stabilizer Mobius.complexMobiusGroup Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ =
      Mobius.rotationMobiusHom.range := by
  ext f
  exact mobius_fixJ_iff_mem_rotationMobius_range f

/-- An actual affine Möbius transformation carrying a given interior point to j. -/
def upperHalfSpacePointNormalizer (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) : Mobius.complexMobiusGroup :=
  Mobius.affineMobius ((Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val)⁻¹ : ℂ)
    (-((Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val)⁻¹ : ℂ) *
      Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val)
    (by exact_mod_cast inv_ne_zero q.property.ne')

theorem upperHalfSpacePointNormalizer_smul (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    upperHalfSpacePointNormalizer q • q = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
  apply Subtype.ext
  rw [upperHalfSpacePointNormalizer, Mobius.affineMobius_smul]
  have hn : ‖((Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val)⁻¹ : ℂ)‖ =
    (Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos q.property]
  rw [hn, inv_mul_cancel₀ q.property.ne']
  simp [Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ, Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint]

theorem mobius_common_interior_fixed_conjugate_rotation_range
    (H : Subgroup Mobius.complexMobiusGroup) (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace)
    (hq : ∀ f ∈ H, f • q = q) :
    ∃ u : Mobius.complexMobiusGroup, DiscreteGroups.Action.Actions.subgroupConjugate u H ≤
      Mobius.rotationMobiusHom.range := by
  refine ⟨upperHalfSpacePointNormalizer q, ?_⟩
  intro f hf
  apply (mobius_fixJ_iff_mem_rotationMobius_range f).mp
  obtain ⟨g, hg, rfl⟩ := (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ H f).mp hf
  rw [← upperHalfSpacePointNormalizer_smul q, mul_smul, mul_smul, inv_smul_smul, hq g hg]

theorem mobius_common_interior_fixed_rotation_realization
    (H : Subgroup Mobius.complexMobiusGroup) (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace)
    (hq : ∀ f ∈ H, f • q = q) :
    ∃ u : Mobius.complexMobiusGroup, ∃ R : Subgroup Mobius.rotationGroupThree,
      DiscreteGroups.Action.Actions.subgroupConjugate u H = Mobius.rotationMobiusSubgroup R ∧ Nonempty (H ≃* R) := by
  obtain ⟨u, hu⟩ := mobius_common_interior_fixed_conjugate_rotation_range H q hq
  let R : Subgroup Mobius.rotationGroupThree := (DiscreteGroups.Action.Actions.subgroupConjugate u H).comap
    Mobius.rotationMobiusHom
  have hR : Mobius.rotationMobiusSubgroup R = DiscreteGroups.Action.Actions.subgroupConjugate u H :=
    Subgroup.map_comap_eq_self hu
  refine ⟨u, R, hR.symm, ⟨?_⟩⟩
  exact (DiscreteGroups.Action.Actions.subgroupConjugateEquivalence u H).trans
    ((MulEquiv.subgroupCongr hR).symm.trans (Mobius.rotationSubgroupEquiv R).symm)

theorem mobius_common_interior_fixed_iff_conjugate_rotation_range
    (H : Subgroup Mobius.complexMobiusGroup) :
    (∃ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, ∀ f ∈ H, f • q = q) ↔
      ∃ u : Mobius.complexMobiusGroup, DiscreteGroups.Action.Actions.subgroupConjugate u H ≤
        Mobius.rotationMobiusHom.range := by
  constructor
  · rintro ⟨q, hq⟩
    exact mobius_common_interior_fixed_conjugate_rotation_range H q hq
  · rintro ⟨u, hu⟩
    refine ⟨u⁻¹ • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ, fun f hf => ?_⟩
    have hc : u * f * u⁻¹ ∈ DiscreteGroups.Action.Actions.subgroupConjugate u H :=
      (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff u H _).mpr ⟨f, hf, rfl⟩
    have hj := (mobius_fixJ_iff_mem_rotationMobius_range _).mpr (hu hc)
    have he := congrArg (fun q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => u⁻¹ • q) hj
    simpa only [mul_smul, inv_smul_smul] using he



/-- Type 1 gives an actual rotation subgroup and a group isomorphism to it. -/
theorem typeOne_conjugate_rotation_realization (H : Subgroup Mobius.complexMobiusGroup)
    (h : HasFullTypeOneOrbit H) :
    ∃ u : Mobius.complexMobiusGroup, ∃ R : Subgroup Mobius.rotationGroupThree,
      DiscreteGroups.Action.Actions.subgroupConjugate u H = Mobius.rotationMobiusSubgroup R ∧ Nonempty (H ≃* R) := by
  obtain ⟨q, hq⟩ := (hasFullTypeOneOrbit_iff_common_H3_fixed H).mp h
  exact mobius_common_interior_fixed_rotation_realization H q hq

theorem hasFullTypeOneOrbit_iff_conjugate_rotation_range (H : Subgroup Mobius.complexMobiusGroup) :
    HasFullTypeOneOrbit H ↔
      ∃ u : Mobius.complexMobiusGroup, DiscreteGroups.Action.Actions.subgroupConjugate u H ≤
        Mobius.rotationMobiusHom.range :=
  (hasFullTypeOneOrbit_iff_common_H3_fixed H).trans
    (mobius_common_interior_fixed_iff_conjugate_rotation_range H)


end
end LowDimensionalTopology.Geometry.DiscreteGroups
