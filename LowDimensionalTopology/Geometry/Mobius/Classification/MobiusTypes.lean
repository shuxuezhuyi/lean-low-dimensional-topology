module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Mobius.HyperbolicExtension
public import LowDimensionalTopology.Geometry.Mobius.CrossRatio.MobiusTriples
public import LowDimensionalTopology.Geometry.Mobius.Circle.ComplexCircles
public import LowDimensionalTopology.Geometry.Mobius.Trace.DiscTraces
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.Convex.PathConnected
public import LowDimensionalTopology.Geometry.Inversive.NormalForm
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.DiscreteSubset
public import LowDimensionalTopology.Geometry.Mobius.Rotation.RotationalGroups
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfSpace.GeodesicGeometry
public import LowDimensionalTopology.Geometry.Mobius.Circle.ComplexCyclicOrder
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyBoundaryGroup
public import Mathlib.MeasureTheory.Integral.CircleIntegral
/-!
# Geometric Möbius types, dynamics and axes

The Poincaré extension defines parabolic, elliptic and loxodromic types by
their actual fixed sets in compactified three-space. Standard forms relate
these types to squared trace and provide forward and two-sided dynamics.
Further results describe common interior fixed points, inverse boundary
pairs, commutativity configurations and intersections of elliptic axes.
Vertical and semicircular coordinates identify the complete elliptic fixed
circle and its orthogonality to the complex boundary plane.
-/

@[expose] public section
noncomputable section
open scoped Quaternion OnePoint ComplexConjugate Topology RealInnerProductSpace
open Filter
namespace LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Auxiliary.Algebra

/-- The true Poincare extension as a homomorphism on the entire compactified Euclidean three-space. -/
def mobiusExtendedSpaceHom : complexMobiusGroup →*
    (OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace ≃ₜ OnePoint
      Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :=
  quaternionConjugateHom.comp ((Inversive.generalMobiusGroup 3).subtype.comp mobiusGeometricPoincareHom)

/-- Fixed points in actual compactified three-space. -/
def mobiusExtendedFixedPoints (f : complexMobiusGroup) : Set (OnePoint
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :=
  Function.fixedPoints (mobiusExtendedSpaceHom f)

/-- A parabolic map has a unique boundary fixed point. -/
abbrev MobiusParabolic (f : complexMobiusGroup) : Prop := MobiusBoundaryParabolic f

/-- Loxodromic maps have exactly two fixed points in the entire extended three-space. -/
def MobiusLoxodromic (f : complexMobiusGroup) : Prop :=
  f ≠ 1 ∧ ∃ a b : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace, a ≠ b ∧
    ∀ q, q ∈ mobiusExtendedFixedPoints f ↔ q = a ∨ q = b

/-- Elliptic maps have infinitely many fixed points in the entire extended three-space. -/
def MobiusElliptic (f : complexMobiusGroup) : Prop :=
  f ≠ 1 ∧ (mobiusExtendedFixedPoints f).Infinite


/-- The hyperbolic class is defined by a genuine invariant disc. -/
def MobiusHyperbolic (f : complexMobiusGroup) : Prop :=
  MobiusLoxodromic f ∧ ∃ D : Set ExtendedComplex, IsComplexOpenDisc D ∧
    (f : Equiv.Perm ExtendedComplex) '' D = D

/-- Strictly loxodromic means that the loxodromic map has no invariant geometric disc. -/
def MobiusStrictlyLoxodromic (f : complexMobiusGroup) : Prop :=
  MobiusLoxodromic f ∧ ¬MobiusHyperbolic f

/-- The exact global affine geometric extension is used for every signed height. -/
theorem mobiusGeometricPoincare_affine (a b : ℂ) (ha : a ≠ 0) :
    (mobiusGeometricPoincare (affineMobius a b ha) : Inversive.ExtendedHomeomorph 3) =
      affineThreeHomeomorph a b ha := by
  have hF := affineThreeHomeomorph_geometric a b ha
  apply Hyperbolic.poincareExtension_unique (mobiusRealRepresentative (affineMobius a b ha))
    _ _ (mobiusGeometricPoincare _).property hF.1
    (Hyperbolic.poincareExtension_extendsBoundary _) hF.extendsBoundary
    (Hyperbolic.poincareExtension_preservesHalfSpaces _ 1) hF.preservesUpperHalfSpace

/-- The standard representative is exactly the corresponding affine Mobius map. -/
theorem mobiusStandardElement_affine (k : ℂˣ) :
    mobiusStandardElement k = affineMobius k (if (k : ℂ) = 1 then 1 else 0) k.ne_zero := by
  apply Subtype.ext
  rfl

/-- The finite normal form on real three-space, including negative and zero height. -/
theorem mobiusStandardElement_extended_coe (k : ℂˣ) (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    mobiusExtendedSpaceHom (mobiusStandardElement k) (q : OnePoint
      Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
      (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint ((k : ℂ) *
        Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q +
        (if (k : ℂ) = 1 then 1 else 0)) (‖(k : ℂ)‖ * Hyperbolic.QuaternionHalfSpace.quaternionHeight q) :
          OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) := by
  rw [mobiusStandardElement_affine]
  change quaternionConjugateHom (mobiusGeometricPoincare (affineMobius _ _ _))
    (q : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) = _
  rw [mobiusGeometricPoincare_affine]
  change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion (affineThreeHomeomorph (k : ℂ)
    (if (k : ℂ) = 1 then 1 else 0) k.ne_zero
    ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q : Inversive.Euclidean 3) :
      Inversive.ExtendedEuclidean 3)) = _
  rw [affineThreeHomeomorph_coe]
  rfl

@[simp] theorem mobiusStandardElement_extended_infty (k : ℂˣ) :
    mobiusExtendedSpaceHom (mobiusStandardElement k) ∞ = ∞ := by
  rw [mobiusStandardElement_affine]
  change quaternionConjugateHom (mobiusGeometricPoincare (affineMobius (k : ℂ)
    (if (k : ℂ) = 1 then 1 else 0) k.ne_zero)) ∞ = ∞
  rw [mobiusGeometricPoincare_affine]
  change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion (affineThreeHomeomorph (k : ℂ)
    (if (k : ℂ) = 1 then 1 else 0) k.ne_zero ∞) = ∞
  rw [affineThreeHomeomorph_infty]
  rfl


/-- Fixed points of the finite standard form are determined by its actual horizontal and height coordinates. -/
theorem mobiusStandardElement_extended_fixed_coe_iff (k : ℂˣ) (q :
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    (q : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) ∈ mobiusExtendedFixedPoints
      (mobiusStandardElement k) ↔
      ((k : ℂ) * Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q + (if (k : ℂ) = 1 then 1 else 0) =
        Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q) ∧
      (‖(k : ℂ)‖ * Hyperbolic.QuaternionHalfSpace.quaternionHeight q =
        Hyperbolic.QuaternionHalfSpace.quaternionHeight q) := by
  change mobiusExtendedSpaceHom (mobiusStandardElement k) (q : OnePoint
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
    (q : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) ↔ _
  rw [mobiusStandardElement_extended_coe, OnePoint.coe_eq_coe]
  constructor
  · intro h
    exact ⟨by
      simpa only [Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint] using
        congrArg Hyperbolic.QuaternionHalfSpace.quaternionHorizontal h,
      by
        simpa only [Hyperbolic.QuaternionHalfSpace.quaternionHeight_threePoint] using
          congrArg Hyperbolic.QuaternionHalfSpace.quaternionHeight h⟩
  · rintro ⟨hz, ht⟩
    rw [hz, ht, Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates]

/-- Translation has only the point at infinity fixed in the entire real three-space. -/
theorem mobiusStandardElement_translation_fixed_iff (w : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    w ∈ mobiusExtendedFixedPoints (mobiusStandardElement 1) ↔ w = ∞ := by
  induction w using OnePoint.rec with
  | infty => exact ⟨fun _ => rfl, fun _ => mobiusStandardElement_extended_infty 1⟩
  | coe q => simp [mobiusStandardElement_extended_fixed_coe_iff]

/-- A nonunit dilation fixes only zero and infinity in the entire extended three-space. -/
theorem mobiusStandardElement_loxodromic_fixed_iff (k : ℂˣ) (hk : ‖(k : ℂ)‖ ≠ 1)
    (w : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    w ∈ mobiusExtendedFixedPoints (mobiusStandardElement k) ↔
      w = (0 : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) ∨ w = ∞ := by
  have hk1 : (k : ℂ) ≠ 1 := by intro h; simp [h] at hk
  induction w using OnePoint.rec with
  | infty => exact ⟨fun _ => Or.inr rfl, fun _ => mobiusStandardElement_extended_infty k⟩
  | coe q =>
    rw [mobiusStandardElement_extended_fixed_coe_iff]
    simp only [ite_eq_right hk1, add_zero, OnePoint.coe_eq_coe, OnePoint.coe_ne_infty, or_false]
    constructor
    · rintro ⟨hz, ht⟩
      have hz0 : Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q = 0 := by
        have hm : ((k : ℂ) - 1) * Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q = 0 := by linear_combination hz
        exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hk1)
      have ht0 : Hyperbolic.QuaternionHalfSpace.quaternionHeight q = 0 := by
        have hm : (‖(k : ℂ)‖ - 1) * Hyperbolic.QuaternionHalfSpace.quaternionHeight q = 0 := by linear_combination ht
        exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hk)
      rw [← Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates q, hz0, ht0]
      apply Subtype.ext
      apply Quaternion.ext <;> rfl
    · rintro rfl
      change (k : ℂ) * 0 = 0 ∧ ‖(k : ℂ)‖ * 0 = 0
      simp

/-- A nontrivial unit-modulus rotation fixes the entire actual vertical real line and infinity. -/
theorem mobiusStandardElement_elliptic_fixed_iff (k : ℂˣ) (hk : (k : ℂ) ≠ 1)
    (hkn : ‖(k : ℂ)‖ = 1) (w : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    w ∈ mobiusExtendedFixedPoints (mobiusStandardElement k) ↔
      w = ∞ ∨ ∃ t : ℝ, w = (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 t : OnePoint
        Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) := by
  induction w using OnePoint.rec with
  | infty => exact ⟨fun _ => Or.inl rfl, fun _ => mobiusStandardElement_extended_infty k⟩
  | coe q =>
    rw [mobiusStandardElement_extended_fixed_coe_iff]
    simp only [ite_eq_right hk, add_zero, hkn, one_mul, and_true, OnePoint.coe_ne_infty,
      false_or, OnePoint.coe_eq_coe]
    constructor
    · intro hz
      have hm : ((k : ℂ) - 1) * Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q = 0 := by linear_combination hz
      have hz0 := (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hk)
      refine ⟨Hyperbolic.QuaternionHalfSpace.quaternionHeight q, ?_⟩
      rw [← Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates q, hz0]
      simp
    · rintro ⟨t, rfl⟩
      simp


/-- The full-space fixed-point set is transported by the exact global homeomorphism under conjugation. -/
theorem mobiusExtendedFixedPoints_conjugation (f q : complexMobiusGroup) :
    mobiusExtendedFixedPoints (q * f * q⁻¹) =
      mobiusExtendedSpaceHom q '' mobiusExtendedFixedPoints f := by
  ext w
  constructor
  · intro hw
    refine ⟨(mobiusExtendedSpaceHom q).symm w, ?_, (mobiusExtendedSpaceHom q).apply_symm_apply w⟩
    change mobiusExtendedSpaceHom f ((mobiusExtendedSpaceHom q).symm w) =
      (mobiusExtendedSpaceHom q).symm w
    change mobiusExtendedSpaceHom (q * f * q⁻¹) w = w at hw
    have h := congrArg (mobiusExtendedSpaceHom q).symm hw
    simpa only [map_mul, map_inv, Homeomorph.mul_apply, Homeomorph.inv_apply,
      Homeomorph.symm_apply_apply] using h
  · rintro ⟨z, hz, rfl⟩
    change mobiusExtendedSpaceHom (q * f * q⁻¹) (mobiusExtendedSpaceHom q z) =
      mobiusExtendedSpaceHom q z
    change mobiusExtendedSpaceHom f z = z at hz
    simp only [map_mul, map_inv, Homeomorph.mul_apply, Homeomorph.inv_apply,
      Homeomorph.symm_apply_apply, hz]

/-- The actual full-space fixed-set notion of elliptic is invariant under conjugation. -/
theorem mobiusElliptic_conjugation (f q : complexMobiusGroup) :
    MobiusElliptic (q * f * q⁻¹) ↔ MobiusElliptic f := by
  unfold MobiusElliptic
  rw [mobiusExtendedFixedPoints_conjugation,
    Set.infinite_image_iff (mobiusExtendedSpaceHom q).injective.injOn]
  have he : (q * f * q⁻¹ = 1) ↔ f = 1 := by
    constructor
    · intro h
      have hh := congrArg (fun g : complexMobiusGroup => q⁻¹ * g * q) h
      simpa [mul_assoc] using hh
    · rintro rfl
      simp
  exact and_congr (not_congr he) Iff.rfl

/-- The standard rotation has infinitely many true three-space fixed points. -/
theorem mobiusStandardElement_fixed_infinite (k : ℂˣ) (hk : (k : ℂ) ≠ 1)
    (hkn : ‖(k : ℂ)‖ = 1) :
    (mobiusExtendedFixedPoints (mobiusStandardElement k)).Infinite := by
  have hi : Function.Injective (fun t : ℝ =>
      (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 t : OnePoint
        Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)) := by
    intro s t h
    have he := congrArg Hyperbolic.QuaternionHalfSpace.quaternionHeight (OnePoint.coe_injective h)
    simpa only [Hyperbolic.QuaternionHalfSpace.quaternionHeight_threePoint] using he
  apply (Set.infinite_range_of_injective hi).mono
  rintro w ⟨t, rfl⟩
  exact (mobiusStandardElement_elliptic_fixed_iff k hk hkn _).mpr (Or.inr ⟨t, rfl⟩)

/-- All standard forms are nonidentity in the actual geometric group. -/
theorem mobiusStandardElement_ne_one (k : ℂˣ) : mobiusStandardElement k ≠ 1 := by
  intro h
  have he := congrArg complexMobiusEquivFractionalLinear h
  rw [mobiusStandardElement_equiv, map_one] at he
  exact Mobius.Classification.standardElement_ne_one k he

theorem mobiusStandardElement_isElliptic (k : ℂˣ) (hk : (k : ℂ) ≠ 1)
    (hkn : ‖(k : ℂ)‖ = 1) : MobiusElliptic (mobiusStandardElement k) :=
  ⟨mobiusStandardElement_ne_one k, mobiusStandardElement_fixed_infinite k hk hkn⟩


/-- Elliptic standard forms are exactly the nontranslation unit-modulus parameters. -/
theorem mobiusStandardElement_elliptic_iff (k : ℂˣ) :
    MobiusElliptic (mobiusStandardElement k) ↔ (k : ℂ) ≠ 1 ∧ ‖(k : ℂ)‖ = 1 := by
  constructor
  · intro he
    have hk1 : (k : ℂ) ≠ 1 := by
      intro hk
      have hkU : k = 1 := Units.ext hk
      subst k
      apply he.2
      apply (Set.finite_singleton (∞ : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)).subset
      intro w hw
      exact (mobiusStandardElement_translation_fixed_iff w).mp hw
    refine ⟨hk1, ?_⟩
    by_contra hkn
    apply he.2
    apply ((Set.finite_singleton (∞ : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)).insert
      ((0 : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) : OnePoint
        Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)).subset
    intro w hw
    exact (mobiusStandardElement_loxodromic_fixed_iff k hkn w).mp hw
  · rintro ⟨hk, hkn⟩
    exact mobiusStandardElement_isElliptic k hk hkn

/-- Elliptic is preserved by actual-group conjugacy, using the full-space geometric definition. -/
theorem mobiusElliptic_isConj {f g : complexMobiusGroup} (h : IsConj f g) :
    MobiusElliptic f ↔ MobiusElliptic g := by
  obtain ⟨q, rfl⟩ := isConj_iff.mp h
  exact (mobiusElliptic_conjugation f q).symm

/-- The geometric elliptic class has exactly the source's standard-form parameters. -/
theorem mobiusElliptic_iff_conjugate_standard (f : complexMobiusGroup) :
    MobiusElliptic f ↔ ∃ k : ℂˣ, (k : ℂ) ≠ 1 ∧ ‖(k : ℂ)‖ = 1 ∧
      IsConj f (mobiusStandardElement k) := by
  constructor
  · intro hf
    obtain ⟨k, hk⟩ := mobius_nonidentity_conjugate_standard f hf.1
    have he := (mobiusStandardElement_elliptic_iff k).mp ((mobiusElliptic_isConj hk).mp hf)
    exact ⟨k, he.1, he.2, hk⟩
  · rintro ⟨k, hk, hkn, hc⟩
    exact (mobiusElliptic_isConj hc).mpr (mobiusStandardElement_isElliptic k hk hkn)

/-- The finite-height action of a standard form is the same true H3 action already constructed. -/
theorem mobiusStandardElement_smul_val (k : ℂˣ) (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (mobiusStandardElement k • q).val =
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint ((k : ℂ) *
        Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val +
        (if (k : ℂ) = 1 then 1 else 0)) (‖(k : ℂ)‖ * Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val) := by
  rw [mobiusStandardElement_affine, affineMobius_smul]

/-- A standard form with an H3 fixed point must be a nontrivial unit-modulus rotation. -/
theorem mobiusStandardElement_H3_fixed_iff (k : ℂˣ) :
    (∃ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, mobiusStandardElement k • q = q) ↔
      (k : ℂ) ≠ 1 ∧ ‖(k : ℂ)‖ = 1 := by
  constructor
  · rintro ⟨q, hq⟩
    have hz := congrArg (fun p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
      Hyperbolic.QuaternionHalfSpace.quaternionHorizontal p.val) hq
    have ht := congrArg (fun p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
      Hyperbolic.QuaternionHalfSpace.quaternionHeight p.val) hq
    rw [mobiusStandardElement_smul_val, Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint] at hz
    rw [mobiusStandardElement_smul_val, Hyperbolic.QuaternionHalfSpace.quaternionHeight_threePoint] at ht
    have hqt : Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val ≠ 0 := (show 0 <
      Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val from q.property).ne'
    refine ⟨?_, (mul_eq_right₀ hqt).mp ht⟩
    intro hk
    simp [hk] at hz
  · rintro ⟨hk, hkn⟩
    refine ⟨Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ, ?_⟩
    apply Subtype.ext
    rw [mobiusStandardElement_smul_val]
    simp only [Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ_horizontal,
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ_height, mul_zero,
      ite_eq_right hk, add_zero, hkn, one_mul]
    rfl

/-- The full-space geometric elliptic definition is equivalent to an actual interior H3 fixed point. -/
theorem mobiusElliptic_iff_H3_fixed (f : complexMobiusGroup) (hf : f ≠ 1) :
    MobiusElliptic f ↔ ∃ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, f • q = q := by
  obtain ⟨k, hk⟩ := mobius_nonidentity_conjugate_standard f hf
  obtain ⟨g, hg⟩ := isConj_iff.mp hk
  have hfix : (∃ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, f • q = q) ↔
      ∃ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, mobiusStandardElement k • q = q := by
    constructor
    · rintro ⟨q, hq⟩
      refine ⟨g • q, ?_⟩
      rw [← hg]
      simp only [mul_smul, inv_smul_smul, hq]
    · rintro ⟨q, hq⟩
      refine ⟨g⁻¹ • q, ?_⟩
      have h := congrArg (fun p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => g⁻¹ • p) hq
      rw [← hg] at h
      simpa only [mul_smul, inv_smul_smul] using h
  rw [hfix, mobiusStandardElement_H3_fixed_iff, mobiusElliptic_isConj hk,
    mobiusStandardElement_elliptic_iff]

/-- Every nonidentity finite-order map is genuinely elliptic. -/
theorem mobius_finite_order_elliptic (f : complexMobiusGroup) (hf : f ≠ 1)
    (hfin : IsOfFinOrder f) : MobiusElliptic f := by
  obtain ⟨k, hk, hkn, hc⟩ := mobius_finite_order_conjugate_unit_standard f hf hfin
  exact (mobiusElliptic_iff_conjugate_standard f).mpr ⟨k, hk, hkn, hc⟩


/-- A nonunit standard form is genuinely loxodromic in the source's full-space sense. -/
theorem mobiusStandardElement_isLoxodromic (k : ℂˣ) (hk : ‖(k : ℂ)‖ ≠ 1) :
    MobiusLoxodromic (mobiusStandardElement k) :=
  ⟨mobiusStandardElement_ne_one k, ((0 : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) : OnePoint
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace),
    ∞, OnePoint.coe_ne_infty _, mobiusStandardElement_loxodromic_fixed_iff k hk⟩

/-- The exact two-point geometric definition excludes translation and every unit-modulus rotation. -/
theorem mobiusStandardElement_loxodromic_iff (k : ℂˣ) :
    MobiusLoxodromic (mobiusStandardElement k) ↔ ‖(k : ℂ)‖ ≠ 1 := by
  constructor
  · rintro ⟨_, a, b, hab, hfix⟩ hkn
    by_cases hk : (k : ℂ) = 1
    · have hkU : k = 1 := Units.ext hk
      subst k
      have ha := (mobiusStandardElement_translation_fixed_iff a).mp
        ((hfix a).mpr (Or.inl rfl))
      have hb := (mobiusStandardElement_translation_fixed_iff b).mp
        ((hfix b).mpr (Or.inr rfl))
      exact hab (ha.trans hb.symm)
    · apply mobiusStandardElement_fixed_infinite k hk hkn
      apply ((Set.finite_singleton b).insert a).subset
      intro w hw
      exact (hfix w).mp hw
  · exact mobiusStandardElement_isLoxodromic k

/-- The loxodromic fixed-pair condition is preserved by actual geometric conjugation. -/
theorem mobiusLoxodromic_conjugation_forward (f q : complexMobiusGroup)
    (hf : MobiusLoxodromic f) : MobiusLoxodromic (q * f * q⁻¹) := by
  refine ⟨?_, ?_⟩
  · intro h
    apply hf.1
    have hh := congrArg (fun g : complexMobiusGroup => q⁻¹ * g * q) h
    simpa [mul_assoc] using hh
  · obtain ⟨a, b, hab, hfix⟩ := hf.2
    refine ⟨mobiusExtendedSpaceHom q a, mobiusExtendedSpaceHom q b,
      (mobiusExtendedSpaceHom q).injective.ne hab, ?_⟩
    intro w
    rw [mobiusExtendedFixedPoints_conjugation]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rcases (hfix z).mp hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨a, (hfix a).mpr (Or.inl rfl), rfl⟩
      · exact ⟨b, (hfix b).mpr (Or.inr rfl), rfl⟩

theorem mobiusLoxodromic_conjugation (f q : complexMobiusGroup) :
    MobiusLoxodromic (q * f * q⁻¹) ↔ MobiusLoxodromic f := by
  constructor
  · intro hf
    have hh := mobiusLoxodromic_conjugation_forward (q * f * q⁻¹) q⁻¹ hf
    simpa [mul_assoc] using hh
  · exact mobiusLoxodromic_conjugation_forward f q

theorem mobiusLoxodromic_isConj {f g : complexMobiusGroup} (h : IsConj f g) :
    MobiusLoxodromic f ↔ MobiusLoxodromic g := by
  obtain ⟨q, rfl⟩ := isConj_iff.mp h
  exact (mobiusLoxodromic_conjugation f q).symm

/-- The loxodromic geometric class has exactly the nonunit standard-form parameters. -/
theorem mobiusLoxodromic_iff_conjugate_standard (f : complexMobiusGroup) :
    MobiusLoxodromic f ↔ ∃ k : ℂˣ, ‖(k : ℂ)‖ ≠ 1 ∧ IsConj f (mobiusStandardElement k) := by
  constructor
  · intro hf
    obtain ⟨k, hk⟩ := mobius_nonidentity_conjugate_standard f hf.1
    exact ⟨k, (mobiusStandardElement_loxodromic_iff k).mp
      ((mobiusLoxodromic_isConj hk).mp hf), hk⟩
  · rintro ⟨k, hk, hc⟩
    exact (mobiusLoxodromic_isConj hc).mpr (mobiusStandardElement_isLoxodromic k hk)

/-- The squared trace of a unit-modulus standard representative is a real number. -/
theorem mobiusStandardElement_unit_squaredTrace (k : ℂˣ) (hk : ‖(k : ℂ)‖ = 1) :
    mobiusSquaredTrace (mobiusStandardElement k) = ((2 + 2 * (k : ℂ).re : ℝ) : ℂ) := by
  rw [mobiusStandardElement_squaredTrace, RCLike.inv_eq_conj hk]
  apply Complex.ext <;> simp
  ring

/-- The nonidentity unit circle gives exactly the elliptic trace interval. -/
theorem mobiusStandardElement_unit_trace_bounds (k : ℂˣ) (hk : ‖(k : ℂ)‖ = 1)
    (hk1 : (k : ℂ) ≠ 1) : 0 ≤ 2 + 2 * (k : ℂ).re ∧ 2 + 2 * (k : ℂ).re < 4 := by
  have hr := Complex.abs_re_le_norm (k : ℂ)
  rw [hk, abs_le] at hr
  have hlt : (k : ℂ).re < 1 := by
    apply lt_of_le_of_ne hr.2
    intro h
    have hn := Complex.sq_norm_sub_sq_re (k : ℂ)
    rw [hk, h] at hn
    have hi : (k : ℂ).im = 0 := by nlinarith [sq_nonneg (k : ℂ).im]
    apply hk1
    exact Complex.ext (by simpa using h) (by simpa using hi)
  constructor <;> linarith

/-- Every real value in the elliptic interval is realized by a genuine nontrivial rotation. -/
theorem exists_unit_standard_squaredTrace (r : ℝ) (hr0 : 0 ≤ r) (hr4 : r < 4) :
    ∃ k : ℂˣ, (k : ℂ) ≠ 1 ∧ ‖(k : ℂ)‖ = 1 ∧
      mobiusSquaredTrace (mobiusStandardElement k) = (r : ℂ) := by
  let θ := Real.arccos (r / 2 - 1)
  let k : ℂˣ := Units.mk0 (Complex.exp ((θ : ℂ) * Complex.I)) (Complex.exp_ne_zero _)
  have hn : ‖(k : ℂ)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have hc : (k : ℂ).re = r / 2 - 1 := by
    change (Complex.exp ((θ : ℂ) * Complex.I)).re = _
    rw [Complex.exp_ofReal_mul_I_re]
    exact Real.cos_arccos (by linarith) (by linarith)
  refine ⟨k, ?_, hn, ?_⟩
  · intro h
    have he := congrArg Complex.re h
    rw [hc] at he
    simp only [Complex.one_re] at he
    linarith
  · rw [mobiusStandardElement_unit_squaredTrace k hn, hc]
    congr 1
    ring

/-- The geometric elliptic class has the real squared-trace interval [0,4). -/
theorem mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four (f : complexMobiusGroup) (hf : f ≠ 1) :
    MobiusElliptic f ↔ ∃ r : ℝ, 0 ≤ r ∧ r < 4 ∧ mobiusSquaredTrace f = (r : ℂ) := by
  constructor
  · intro he
    obtain ⟨k, hk1, hkn, hc⟩ := (mobiusElliptic_iff_conjugate_standard f).mp he
    obtain ⟨h0, h4⟩ := mobiusStandardElement_unit_trace_bounds k hkn hk1
    refine ⟨2 + 2 * (k : ℂ).re, h0, h4, ?_⟩
    rw [(mobius_isConj_iff_squaredTrace_eq f _ hf (mobiusStandardElement_ne_one k)).mp hc,
      mobiusStandardElement_unit_squaredTrace k hkn]
  · rintro ⟨r, hr0, hr4, hftrace⟩
    obtain ⟨k, hk1, hkn, hk⟩ := exists_unit_standard_squaredTrace r hr0 hr4
    apply (mobiusElliptic_iff_conjugate_standard f).mpr
    refine ⟨k, hk1, hkn, ?_⟩
    exact (mobius_isConj_iff_squaredTrace_eq f _ hf (mobiusStandardElement_ne_one k)).mpr
      (hftrace.trans hk.symm)

/-- The source parabolic class is also invariant under actual-group conjugacy. -/
theorem mobiusParabolic_isConj {f g : complexMobiusGroup} (hc : IsConj f g) :
    MobiusParabolic f ↔ MobiusParabolic g := by
  by_cases hf : f = 1
  · subst f
    have hg : g = 1 := by
      obtain ⟨q, hq⟩ := isConj_iff.mp hc
      simpa using hq.symm
    subst g
    rfl
  · have hg : g ≠ 1 := by
      intro h
      obtain ⟨q, hq⟩ := isConj_iff.mp hc
      apply hf
      have hh := congrArg (fun a : complexMobiusGroup => q⁻¹ * a * q) (hq.trans h)
      simpa [mul_assoc] using hh
    rw [MobiusParabolic, MobiusParabolic, mobius_parabolic_iff_squaredTrace_eq_four f hf,
      mobius_parabolic_iff_squaredTrace_eq_four g hg,
      (mobius_isConj_iff_squaredTrace_eq f g hf hg).mp hc]









/-- Hyperbolicity defined by an invariant genuine disc is invariant under conjugation. -/
theorem mobiusHyperbolic_conjugation_forward (f q : complexMobiusGroup)
    (hf : MobiusHyperbolic f) : MobiusHyperbolic (q * f * q⁻¹) := by
  refine ⟨(mobiusLoxodromic_conjugation f q).mpr hf.1, ?_⟩
  obtain ⟨D, hD, hi⟩ := hf.2
  refine ⟨(q : Equiv.Perm ExtendedComplex) '' D, hD.image q, ?_⟩
  have hcomp : (((q * f * q⁻¹ : complexMobiusGroup) : Equiv.Perm ExtendedComplex) ∘
      (q : Equiv.Perm ExtendedComplex)) =
      (q : Equiv.Perm ExtendedComplex) ∘ (f : Equiv.Perm ExtendedComplex) := by
    funext z
    change (q : Equiv.Perm ExtendedComplex) ((f : Equiv.Perm ExtendedComplex)
      ((q : Equiv.Perm ExtendedComplex).symm ((q : Equiv.Perm ExtendedComplex) z))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [Set.image_image]
  change ((((q * f * q⁻¹ : complexMobiusGroup) : Equiv.Perm ExtendedComplex) ∘
    (q : Equiv.Perm ExtendedComplex)) '' D) = _
  rw [hcomp]
  simpa only [Set.image_image, Function.comp_def] using
    congrArg (fun E : Set ExtendedComplex => (q : Equiv.Perm ExtendedComplex) '' E) hi

theorem mobiusHyperbolic_conjugation (f q : complexMobiusGroup) :
    MobiusHyperbolic (q * f * q⁻¹) ↔ MobiusHyperbolic f := by
  constructor
  · intro hf
    have hh := mobiusHyperbolic_conjugation_forward (q * f * q⁻¹) q⁻¹ hf
    simpa [mul_assoc] using hh
  · exact mobiusHyperbolic_conjugation_forward f q

theorem mobiusHyperbolic_isConj {f g : complexMobiusGroup} (h : IsConj f g) :
    MobiusHyperbolic f ↔ MobiusHyperbolic g := by
  obtain ⟨q, rfl⟩ := isConj_iff.mp h
  exact (mobiusHyperbolic_conjugation f q).symm

/-- Strict loxodromicity is invariant under conjugation with the geometric definitions. -/
theorem mobiusStrictlyLoxodromic_isConj {f g : complexMobiusGroup} (h : IsConj f g) :
    MobiusStrictlyLoxodromic f ↔ MobiusStrictlyLoxodromic g := by
  exact and_congr (mobiusLoxodromic_isConj h) (not_congr (mobiusHyperbolic_isConj h))
/-- Every positive real nonunit standard dilation preserves a genuine open half-plane component. -/
theorem mobiusStandardElement_positive_isHyperbolic (k : ℂˣ)
    (hki : (k : ℂ).im = 0) (hkp : 0 < (k : ℂ).re) (hkn : ‖(k : ℂ)‖ ≠ 1) :
    MobiusHyperbolic (mobiusStandardElement k) := by
  have hk1 : (k : ℂ) ≠ 1 := by intro h; simp [h] at hkn
  have hmem (z : ExtendedComplex) :
      (mobiusStandardElement k : Equiv.Perm ExtendedComplex) z ∈ complexRealAxis ↔
        z ∈ complexRealAxis := by
    induction z using OnePoint.rec with
    | infty => simp [mobiusStandardElement_infty]
    | coe z =>
      rw [mobiusStandardElement_coe]
      simp only [ite_eq_right hk1, add_zero, complexRealAxis_coe, Complex.mul_im, hki,
        zero_mul, add_zero, mul_eq_zero, hkp.ne', false_or]
  have himage : (mobiusStandardElement k : Equiv.Perm ExtendedComplex) '' complexRealAxis =
      complexRealAxis := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hmem w).mpr hw
    · intro hz
      refine ⟨(mobiusStandardElement k : Equiv.Perm ExtendedComplex).symm z, ?_,
        Equiv.apply_symm_apply _ z⟩
      apply (hmem _).mp
      simpa only [Equiv.apply_symm_apply] using hz
  let U : Set ExtendedComplex := OnePoint.some '' {z : ℂ | 0 < z.im}
  have hcv : Convex ℝ {z : ℂ | 0 < z.im} :=
    convex_halfSpace_gt Complex.imLm.isLinear 0
  have hU : IsPreconnected U :=
    hcv.isPreconnected.image OnePoint.some OnePoint.continuous_coe.continuousOn
  have hsub : U ⊆ complexRealAxisᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hreal
    exact (ne_of_gt hz) ((complexRealAxis_coe z).mp hreal)
  have hi : ((Complex.I : ℂ) : ExtendedComplex) ∈ U :=
    ⟨Complex.I, by simp, rfl⟩
  have hfi : (mobiusStandardElement k : Equiv.Perm ExtendedComplex) Complex.I ∈ U := by
    rw [mobiusStandardElement_coe]
    simp only [ite_eq_right hk1]
    refine ⟨(k : ℂ) * Complex.I, ?_, rfl⟩
    simpa using hkp
  have hD : U ⊆ connectedComponentIn complexRealAxisᶜ (Complex.I : ExtendedComplex) :=
    hU.subset_connectedComponentIn hi hsub
  refine ⟨mobiusStandardElement_isLoxodromic k hkn,
    connectedComponentIn complexRealAxisᶜ (Complex.I : ExtendedComplex),
    ⟨complexRealAxis, complexRealAxis_isGeneralized, Complex.I, hsub hi, rfl⟩, ?_⟩
  have hcomp := (mobiusBoundaryHomeomorph (mobiusStandardElement k)).image_connectedComponentIn (hsub hi)
  change (mobiusStandardElement k : Equiv.Perm ExtendedComplex) ''
    connectedComponentIn complexRealAxisᶜ (Complex.I : ExtendedComplex) = _ at hcomp
  change _ = connectedComponentIn
    ((mobiusStandardElement k : Equiv.Perm ExtendedComplex) '' complexRealAxisᶜ)
    ((mobiusStandardElement k : Equiv.Perm ExtendedComplex) Complex.I) at hcomp
  rw [(mobiusStandardElement k : Equiv.Perm ExtendedComplex).image_compl complexRealAxis,
    himage] at hcomp
  exact hcomp.trans (connectedComponentIn_eq (hD hfi)).symm

/-- Every real squared trace strictly above four is realized by a positive real nonunit dilation. -/
theorem exists_positive_standard_squaredTrace (r : ℝ) (hr : 4 < r) :
    ∃ k : ℂˣ, (k : ℂ).im = 0 ∧ 0 < (k : ℂ).re ∧ ‖(k : ℂ)‖ ≠ 1 ∧
      mobiusSquaredTrace (mobiusStandardElement k) = (r : ℂ) := by
  let a := r / 2 - 1
  have ha : 1 < a := by dsimp [a]; linarith
  let s := Real.sqrt (a ^ 2 - 1)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = a ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  let u := a + s
  have hu : 1 < u := by dsimp [u]; linarith
  let k : ℂˣ := Units.mk0 (u : ℂ) (Complex.ofReal_ne_zero.mpr (by linarith))
  refine ⟨k, by simp [k], by simpa [k] using (by linarith : 0 < u), ?_, ?_⟩
  · change ‖(u : ℂ)‖ ≠ 1
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    exact ne_of_gt hu
  · rw [mobiusStandardElement_squaredTrace]
    change (u : ℂ) + (u : ℂ)⁻¹ + 2 = (r : ℂ)
    rw [← Complex.ofReal_inv]
    norm_cast
    have hid : u * (2 * a - u) = 1 := by dsimp [u]; nlinarith
    have hinv : u⁻¹ = 2 * a - u := inv_eq_of_mul_eq_one_right hid
    rw [hinv]
    dsimp [a]
    ring



/-- A map preserving an arbitrary generalized disc has a nonnegative real squared trace. -/
theorem mobius_generalized_disc_preserver_squaredTrace (f : complexMobiusGroup)
    {D : Set ExtendedComplex} (hD : IsComplexOpenDisc D)
    (hpres : (f : Equiv.Perm ExtendedComplex) '' D = D) :
    ∃ r : ℝ, 0 ≤ r ∧ mobiusSquaredTrace f = (r : ℂ) := by
  obtain ⟨q, hq⟩ := hD.normalize
  have hconj : ((q * f * q⁻¹ : complexMobiusGroup) : Equiv.Perm ExtendedComplex) ''
      Hyperbolic.extendedUnitDisc = Hyperbolic.extendedUnitDisc := by
    rw [← hq]
    have he : (fun z => ((q * f * q⁻¹ : complexMobiusGroup) : Equiv.Perm ExtendedComplex)
        ((q : Equiv.Perm ExtendedComplex) z)) =
        (fun z => (q : Equiv.Perm ExtendedComplex) ((f : Equiv.Perm ExtendedComplex) z)) := by
      funext z
      change (q : Equiv.Perm ExtendedComplex) ((f : Equiv.Perm ExtendedComplex)
        ((q : Equiv.Perm ExtendedComplex).symm ((q : Equiv.Perm ExtendedComplex) z))) = _
      rw [Equiv.symm_apply_apply]
    rw [Set.image_image, he, ← Set.image_image, hpres]
  obtain ⟨r, hr, he⟩ := mobius_disc_preserver_squaredTrace (q * f * q⁻¹) hconj
  exact ⟨r, hr, (mobiusSquaredTrace_conjugation f q).symm.trans he⟩

/-- A geometric loxodromic map cannot be parabolic. -/
theorem MobiusLoxodromic.not_parabolic {f : complexMobiusGroup} (hf : MobiusLoxodromic f) :
    ¬MobiusParabolic f := by
  intro hp
  have hc := (mobiusBoundaryParabolic_iff_conjugate_translation f hf.1).mp hp
  have hn := (mobiusStandardElement_loxodromic_iff 1).mp ((mobiusLoxodromic_isConj hc).mp hf)
  exact hn (by simp)

/-- A geometric loxodromic map cannot be elliptic. -/
theorem MobiusLoxodromic.not_elliptic {f : complexMobiusGroup} (hf : MobiusLoxodromic f) :
    ¬MobiusElliptic f := by
  intro he
  obtain ⟨k, hkn, hc⟩ := (mobiusLoxodromic_iff_conjugate_standard f).mp hf
  have hu := (mobiusStandardElement_elliptic_iff k).mp ((mobiusElliptic_isConj hc).mp he)
  exact hkn hu.2

/-- Every actual nonidentity map belongs to one of the three full-space geometric types. -/
theorem mobius_nonidentity_type_trichotomy (f : complexMobiusGroup) (hf : f ≠ 1) :
    MobiusParabolic f ∨ MobiusLoxodromic f ∨ MobiusElliptic f := by
  obtain ⟨k, hc⟩ := mobius_nonidentity_conjugate_standard f hf
  by_cases hk : (k : ℂ) = 1
  · have hkU : k = 1 := Units.ext hk
    subst k
    exact Or.inl ((mobiusBoundaryParabolic_iff_conjugate_translation f hf).mpr hc)
  · by_cases hkn : ‖(k : ℂ)‖ = 1
    · exact Or.inr (Or.inr ((mobiusElliptic_iff_conjugate_standard f).mpr ⟨k, hk, hkn, hc⟩))
    · exact Or.inr (Or.inl ((mobiusLoxodromic_iff_conjugate_standard f).mpr ⟨k, hkn, hc⟩))

/-- With the actual invariant-disc definition of hyperbolic. -/
theorem mobius_hyperbolic_iff_squaredTrace_real_gt_four (f : complexMobiusGroup) (hf : f ≠ 1) :
    MobiusHyperbolic f ↔ ∃ r : ℝ, 4 < r ∧ mobiusSquaredTrace f = (r : ℂ) := by
  constructor
  · rintro ⟨hl, D, hD, hpres⟩
    obtain ⟨r, hr, ht⟩ := mobius_generalized_disc_preserver_squaredTrace f hD hpres
    refine ⟨r, ?_, ht⟩
    by_contra h4
    have hle : r ≤ 4 := le_of_not_gt h4
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hl.not_elliptic ((mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four f hf).mpr ⟨r, hr, hlt, ht⟩)
    · apply hl.not_parabolic
      apply (mobius_parabolic_iff_squaredTrace_eq_four f hf).mpr
      rw [ht, heq]
      norm_num
  · rintro ⟨r, hr, ht⟩
    obtain ⟨k, hki, hkp, hkn, hk⟩ := exists_positive_standard_squaredTrace r hr
    have hc := (mobius_isConj_iff_squaredTrace_eq f _ hf (mobiusStandardElement_ne_one k)).mpr (ht.trans hk.symm)
    exact (mobiusHyperbolic_isConj hc).mpr (mobiusStandardElement_positive_isHyperbolic k hki hkp hkn)

/-- strict loxodromicity is the complement of the nonnegative real ray. -/
theorem mobius_strictlyLoxodromic_iff_squaredTrace_not_nonnegative_real (f : complexMobiusGroup) (hf : f ≠ 1) :
    MobiusStrictlyLoxodromic f ↔ ¬∃ r : ℝ, 0 ≤ r ∧ mobiusSquaredTrace f = (r : ℂ) := by
  constructor
  · rintro ⟨hl, hh⟩ ⟨r, hr, ht⟩
    rcases lt_trichotomy r 4 with hlt | heq | hgt
    · exact hl.not_elliptic ((mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four f hf).mpr ⟨r, hr, hlt, ht⟩)
    · apply hl.not_parabolic
      apply (mobius_parabolic_iff_squaredTrace_eq_four f hf).mpr
      rw [ht, heq]
      norm_num
    · exact hh ((mobius_hyperbolic_iff_squaredTrace_real_gt_four f hf).mpr ⟨r, hgt, ht⟩)
  · intro hn
    refine ⟨?_, ?_⟩
    · rcases mobius_nonidentity_type_trichotomy f hf with hp | hl | he
      · apply False.elim
        apply hn
        exact ⟨4, by norm_num, by simpa using (mobius_parabolic_iff_squaredTrace_eq_four f hf).mp hp⟩
      · exact hl
      · apply False.elim
        apply hn
        obtain ⟨r, hr, _, ht⟩ := (mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four f hf).mp he
        exact ⟨r, hr, ht⟩
    · intro hh
      obtain ⟨r, hr, ht⟩ := (mobius_hyperbolic_iff_squaredTrace_real_gt_four f hf).mp hh
      exact hn ⟨r, by linarith, ht⟩

/-- The Euclidean similarities used are positive scalings of Euclidean isometries, followed by a translation. -/
def IsEuclideanSimilarity {n : ℕ} (f : Inversive.Euclidean n → Inversive.Euclidean n) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ φ : Inversive.Euclidean n ≃ᵢ Inversive.Euclidean n,
    ∃ b : Inversive.Euclidean n, ∀ x, f x = r • φ x + b

/-- The standard positive scale/isometry normal form is a Euclidean similarity. -/
theorem extendedSimilarity_isEuclideanSimilarity {n : ℕ} (r : ℝ) (hr : 0 < r)
    (φ : Inversive.Euclidean n ≃ᵢ Inversive.Euclidean n) :
    IsEuclideanSimilarity (Inversive.finiteEuclideanPart (Inversive.extendedSimilarity r hr φ)) := by
  refine ⟨r, hr, φ, 0, ?_⟩
  intro x
  simp

/-- A common actual H3 fixed point makes every nonidentity subgroup element geometrically elliptic. -/
theorem mobius_common_H3_fixed_all_elliptic (G : Subgroup complexMobiusGroup)
    (hfix : ∃ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, ∀ f ∈ G, f • q = q) :
    ∀ f ∈ G, f ≠ 1 → MobiusElliptic f := by
  obtain ⟨q, hq⟩ := hfix
  intro f hf hne
  exact (mobiusElliptic_iff_H3_fixed f hne).mpr ⟨q, hq f hf⟩

/-- Every determinant-one representative of an elliptic map or the identity has real trace in [-2,2]. -/
theorem specialLinear_elliptic_or_identity_trace (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : mobiusSpecialLinearProjection A = 1 ∨ MobiusElliptic (mobiusSpecialLinearProjection A)) :
    (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).im = 0 ∧
      -2 ≤ (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).re ∧
      (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).re ≤ 2 := by
  rcases hA with hA | hA
  · rcases (mobiusSpecialLinearProjection_eq_one_iff A).mp hA with hA | hA
    · rw [hA]
      norm_num [Matrix.trace_fin_two]
    · rw [hA]
      norm_num [Matrix.trace_fin_two]
  · obtain ⟨r, hr0, hr4, hr⟩ := (mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four _ hA.1).mp hA
    have hsq : Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 = (r : ℂ) := by
      rw [← mobiusSquaredTrace_specialLinearProjection]
      exact hr
    have hre := congrArg Complex.re hsq
    have him := congrArg Complex.im hsq
    simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im] at hre him
    have hm : (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).re *
        (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).im = 0 := by nlinarith
    have hz : (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).im = 0 := by
      rcases mul_eq_zero.mp hm with h | h
      · rw [h] at hre
        nlinarith [sq_nonneg (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).im]
      · exact h
    refine ⟨hz, ?_, ?_⟩ <;> rw [hz] at hre <;> nlinarith

/-- The trace restriction applies uniformly to every SL2 lift of a subgroup of elliptic elements and the identity. -/
theorem elliptic_group_lift_trace (G : Subgroup complexMobiusGroup)
    (hG : ∀ f ∈ G, f ≠ 1 → MobiusElliptic f) (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : mobiusSpecialLinearProjection A ∈ G) :
    (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).im = 0 ∧
      -2 ≤ (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).re ∧
      (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).re ≤ 2 := by
  apply specialLinear_elliptic_or_identity_trace
  by_cases he : mobiusSpecialLinearProjection A = 1
  · exact Or.inl he
  · exact Or.inr (hG _ hA he)
/-- Two real traces determine the conjugate diagonal relation relative to a nontrivial unit rotation. -/
theorem specialLinear_real_traces_conjugate_diagonal (R A : Auxiliary.Algebra.SpecialLinear2)
    (hR01 : R 0 1 = 0) (hR10 : R 1 0 = 0) (hRd : R 1 1 = conj (R 0 0))
    (hRi : (R 0 0).im ≠ 0) (hA : (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).im = 0)
    (hRA : (Matrix.trace ((R * A : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2)).im = 0) :
    A 1 1 = conj (A 0 0) := by
  simp only [Matrix.trace_fin_two, Complex.add_im] at hA
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, hR01, hR10, zero_mul, add_zero, zero_add, hRd,
    Complex.add_im, Complex.mul_im, Complex.conj_re, Complex.conj_im] at hRA
  have hm : (R 0 0).im * ((A 0 0).re - (A 1 1).re) = 0 := by
    linear_combination hRA - (R 0 0).re * hA
  have hre := (mul_eq_zero.mp hm).resolve_left hRi
  apply Complex.ext
  · simp only [Complex.conj_re]
    linarith
  · simp only [Complex.conj_im]
    linarith

/-- Every nontrivial unit standard map has a diagonal unitary SL2 representative with a nonreal diagonal. -/
theorem unit_standard_specialLinear_diagonal (k : ℂˣ) (hk : (k : ℂ) ≠ 1)
    (hkn : ‖(k : ℂ)‖ = 1) :
    ∃ R : Auxiliary.Algebra.SpecialLinear2, mobiusSpecialLinearProjection R = mobiusStandardElement k ∧
      R 0 1 = 0 ∧ R 1 0 = 0 ∧ R 1 1 = conj (R 0 0) ∧ (R 0 0).im ≠ 0 := by
  obtain ⟨R, hR, u, ha, hb, hc, hd⟩ := Mobius.Classification.specialStandard_lift k
  have hproj : mobiusSpecialLinearProjection R = mobiusStandardElement k := by
    apply complexMobiusEquivFractionalLinear.injective
    rw [mobiusSpecialLinearProjection_equiv, mobiusStandardElement_equiv]
    exact hR
  have hRj : mobiusSpecialLinearProjection R • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ =
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
    rw [hproj]
    apply Subtype.ext
    rw [mobiusStandardElement_smul_val]
    simp only [Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ_horizontal,
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ_height, mul_zero,
      ite_eq_right hk, add_zero, hkn, one_mul]
    rfl
  have huR := (mobiusSpecialLinearProjection_fixJ_iff R).mp hRj
  have hqR := Auxiliary.Algebra.quaternion_of_matrixNorm_sq (R : Auxiliary.Algebra.ComplexMatrix2) R.det_coe
    (Auxiliary.Algebra.unitary_matrixNorm_sq _ huR)
  have hdiag : R 1 1 = conj (R 0 0) := (Auxiliary.Algebra.quaternionMatrix_range_iff_entries _).mp hqR |>.1
  refine ⟨R, hproj, ?_, hc, hdiag, ?_⟩
  · simpa only [ite_eq_right hk, mul_zero] using hb
  · intro hi
    have he : R 1 1 = R 0 0 := hdiag.trans (Complex.conj_eq_iff_im.mpr hi)
    apply hk
    apply mul_left_cancel₀ u.ne_zero
    calc
      (u : ℂ) * (k : ℂ) = R 0 0 := ha.symm
      _ = R 1 1 := he.symm
      _ = (u : ℂ) := hd
      _ = (u : ℂ) * 1 := (mul_one _).symm

/-- Every lift of an all-elliptic subgroup has conjugate diagonal entries after one standard normalization. -/
theorem elliptic_group_lift_conjugate_diagonal (G : Subgroup complexMobiusGroup)
    (hG : ∀ f ∈ G, f ≠ 1 → MobiusElliptic f) (R : Auxiliary.Algebra.SpecialLinear2)
    (hR : mobiusSpecialLinearProjection R ∈ G)
    (hR01 : R 0 1 = 0) (hR10 : R 1 0 = 0) (hRd : R 1 1 = conj (R 0 0))
    (hRi : (R 0 0).im ≠ 0) (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : mobiusSpecialLinearProjection A ∈ G) : A 1 1 = conj (A 0 0) := by
  apply specialLinear_real_traces_conjugate_diagonal R A hR01 hR10 hRd hRi
    (elliptic_group_lift_trace G hG A hA).1
  apply (elliptic_group_lift_trace G hG (R * A) _).1
  rw [map_mul]
  exact G.mul_mem hR hA
/-- The diagonal standard commutator formula is an exact identity in real coordinates. -/
theorem specialLinear_diagonal_commutator_trace_re (R A : Auxiliary.Algebra.SpecialLinear2)
    (hR01 : R 0 1 = 0) (hR10 : R 1 0 = 0) (hRd : R 1 1 = conj (R 0 0)) :
    (Matrix.trace (Mobius.Classification.specialCommutator R A : Auxiliary.Algebra.ComplexMatrix2)).re =
      2 + 4 * (R 0 0).im ^ 2 * (A 1 0 * A 0 1).re := by
  rw [Mobius.Classification.specialCommutator_trace_triangular R A hR10, hR01, hRd]
  simp only [zero_pow (by omega : 2 ≠ 0), zero_mul, add_zero,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, pow_two, show (2 : ℂ).re = 2 from rfl]
  ring

/-- A subgroup consisting of elliptics and the identity bounds each normalized upper-left coefficient by one. -/
theorem elliptic_group_lift_normSq_le_one (G : Subgroup complexMobiusGroup)
    (hG : ∀ f ∈ G, f ≠ 1 → MobiusElliptic f) (R : Auxiliary.Algebra.SpecialLinear2)
    (hR : mobiusSpecialLinearProjection R ∈ G)
    (hR01 : R 0 1 = 0) (hR10 : R 1 0 = 0) (hRd : R 1 1 = conj (R 0 0))
    (hRi : (R 0 0).im ≠ 0) (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : mobiusSpecialLinearProjection A ∈ G) : Complex.normSq (A 0 0) ≤ 1 := by
  have hAd := elliptic_group_lift_conjugate_diagonal G hG R hR hR01 hR10 hRd hRi A hA
  have hcomm : mobiusSpecialLinearProjection (Mobius.Classification.specialCommutator R A) ∈ G := by
    simp only [Mobius.Classification.specialCommutator, map_mul, map_inv]
    exact G.mul_mem (G.mul_mem (G.mul_mem hR hA) (G.inv_mem hR)) (G.inv_mem hA)
  have ht := (elliptic_group_lift_trace G hG (Mobius.Classification.specialCommutator R A) hcomm).2.2
  rw [specialLinear_diagonal_commutator_trace_re R A hR01 hR10 hRd] at ht
  have hs : 0 < 4 * (R 0 0).im ^ 2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hRi)
  have hprod : (A 1 0 * A 0 1).re ≤ 0 := by
    by_contra hp
    have hm := mul_pos hs (lt_of_not_ge hp)
    linarith
  have hd := congrArg Complex.re A.det_coe
  rw [Matrix.det_fin_two, hAd, Complex.mul_conj] at hd
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at hd
  have heq : (A 0 1 * A 1 0).re = (A 1 0 * A 0 1).re := by rw [mul_comm]
  rw [heq] at hd
  linarith

/-- The conjugate-diagonal relation on a product enforces the same off-diagonal ratio. -/
theorem specialLinear_product_conjugate_diagonal (A B : Auxiliary.Algebra.SpecialLinear2)
    (hA : A 1 1 = conj (A 0 0)) (hB : B 1 1 = conj (B 0 0))
    (hAB : (A * B : Auxiliary.Algebra.SpecialLinear2) 1 1 = conj ((A * B : Auxiliary.Algebra.SpecialLinear2) 0 0)) :
    A 0 1 * B 1 0 = conj (A 1 0) * conj (B 0 1) := by
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    hA, hB, map_add, map_mul] at hAB
  have hh := congrArg (starRingEnd ℂ) hAB
  simp only [map_add, map_mul, Complex.conj_conj] at hh
  linear_combination -hh
/-- In an all-elliptic subgroup, a squared trace of four forces the identity. -/
theorem elliptic_group_squaredTrace_four_eq_one (G : Subgroup complexMobiusGroup)
    (hG : ∀ f ∈ G, f ≠ 1 → MobiusElliptic f) (f : complexMobiusGroup) (hf : f ∈ G)
    (ht : mobiusSquaredTrace f = 4) : f = 1 := by
  by_contra hn
  obtain ⟨r, _, hr, he⟩ := (mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four f hn).mp (hG f hf hn)
  rw [ht] at he
  have hre := congrArg Complex.re he
  norm_num at hre
  linarith

/-- A matrix commuting with a nonreal diagonal rotation has both off-diagonal entries zero. -/
theorem specialLinear_commuting_diagonal_offDiagonal_zero (R A : Auxiliary.Algebra.SpecialLinear2)
    (hR01 : R 0 1 = 0) (hR10 : R 1 0 = 0) (hRd : R 1 1 = conj (R 0 0))
    (hRi : (R 0 0).im ≠ 0) (hcomm : Commute R A) : A 0 1 = 0 ∧ A 1 0 = 0 := by
  have hn : R 0 0 - R 1 1 ≠ 0 := by
    intro h
    have hi := congrArg Complex.im (sub_eq_zero.mp h)
    rw [hRd, Complex.conj_im] at hi
    apply hRi
    linarith
  have h01 := congrArg (fun B : Auxiliary.Algebra.SpecialLinear2 => B 0 1) hcomm.eq
  have h10 := congrArg (fun B : Auxiliary.Algebra.SpecialLinear2 => B 1 0) hcomm.eq
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    hR01, hR10, mul_zero, zero_mul, add_zero, zero_add] at h01 h10
  constructor
  · apply (mul_eq_zero.mp (show (R 0 0 - R 1 1) * A 0 1 = 0 by linear_combination h01)).resolve_left hn
  · apply (mul_eq_zero.mp (show (R 0 0 - R 1 1) * A 1 0 = 0 by linear_combination -h10)).resolve_left hn

/-- In an all-elliptic group, one vanishing off-diagonal entry forces the other to vanish as well. -/
theorem elliptic_group_lift_offDiagonal_zero (G : Subgroup complexMobiusGroup)
    (hG : ∀ f ∈ G, f ≠ 1 → MobiusElliptic f) (R : Auxiliary.Algebra.SpecialLinear2)
    (hR : mobiusSpecialLinearProjection R ∈ G)
    (hR01 : R 0 1 = 0) (hR10 : R 1 0 = 0) (hRd : R 1 1 = conj (R 0 0))
    (hRi : (R 0 0).im ≠ 0) (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : mobiusSpecialLinearProjection A ∈ G) (hz : A 0 1 = 0 ∨ A 1 0 = 0) :
    A 0 1 = 0 ∧ A 1 0 = 0 := by
  let C := Mobius.Classification.specialCommutator R A
  have ht : Matrix.trace (C : Auxiliary.Algebra.ComplexMatrix2) = 2 := by
    dsimp [C]
    rw [Mobius.Classification.specialCommutator_trace_triangular R A hR10, hR01]
    rcases hz with hb | hc
    · simp [hb]
    · simp [hc]
  have hC : mobiusSpecialLinearProjection C ∈ G := by
    dsimp [C, Mobius.Classification.specialCommutator]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact G.mul_mem (G.mul_mem (G.mul_mem hR hA) (G.inv_mem hR)) (G.inv_mem hA)
  have hproj : mobiusSpecialLinearProjection C = 1 := by
    apply elliptic_group_squaredTrace_four_eq_one G hG _ hC
    rw [mobiusSquaredTrace_specialLinearProjection, ht]
    norm_num
  have hCm : (C : Auxiliary.Algebra.ComplexMatrix2) = 1 := by
    rcases (mobiusSpecialLinearProjection_eq_one_iff C).mp hproj with h | h
    · exact h
    · rw [h, Matrix.trace_fin_two] at ht
      norm_num at ht
  have hCid : C = 1 := Subtype.ext hCm
  have hcomm : Commute R A := by
    change R * A = A * R
    change R * A * R⁻¹ * A⁻¹ = 1 at hCid
    have hh : R * A * R⁻¹ = A := by
      simpa only [one_mul] using (mul_inv_eq_iff_eq_mul.mp hCid)
    exact mul_inv_eq_iff_eq_mul.mp hh
  exact specialLinear_commuting_diagonal_offDiagonal_zero R A hR01 hR10 hRd hRi hcomm
/-- A strict diagonal norm defect determines a positive vertical fixed height. -/
theorem specialLinear_positive_vertical_ratio (A : Auxiliary.Algebra.SpecialLinear2)
    (hAd : A 1 1 = conj (A 0 0)) (ha : Complex.normSq (A 0 0) < 1)
    (hc : A 1 0 ≠ 0) :
    ∃ t : ℝ, 0 < t ∧ A 0 1 = -conj (A 1 0) * (t : ℂ) ^ 2 := by
  let n := (1 - Complex.normSq (A 0 0)) / Complex.normSq (A 1 0)
  have hn : 0 < n := div_pos (by linarith) (Complex.normSq_pos.mpr hc)
  let t := Real.sqrt n
  have ht : 0 < t := Real.sqrt_pos.mpr hn
  have ht2 : t ^ 2 = n := Real.sq_sqrt hn.le
  have hnt : Complex.normSq (A 1 0) * t ^ 2 = 1 - Complex.normSq (A 0 0) := by
    rw [ht2]
    exact mul_div_cancel₀ _ (ne_of_gt (Complex.normSq_pos.mpr hc))
  have hd := A.det_coe
  rw [Matrix.det_fin_two, hAd, Complex.mul_conj] at hd
  have hprod : A 0 1 * A 1 0 = ((Complex.normSq (A 0 0) - 1 : ℝ) : ℂ) := by
    push_cast
    linear_combination -hd
  refine ⟨t, ht, ?_⟩
  apply mul_right_cancel₀ hc
  calc
    A 0 1 * A 1 0 = ((Complex.normSq (A 0 0) - 1 : ℝ) : ℂ) := hprod
    _ = -((Complex.normSq (A 1 0) : ℝ) : ℂ) * (t : ℂ) ^ 2 := by
      exact_mod_cast (by linarith : Complex.normSq (A 0 0) - 1 = -Complex.normSq (A 1 0) * t ^ 2)
    _ = (-conj (A 1 0) * (t : ℂ) ^ 2) * A 1 0 := by
      rw [← Complex.mul_conj]
      ring

/-- The entry ratio is exactly the fixed-point equation for an actual vertical H3 point. -/
theorem specialLinear_vertical_fixed (A : Auxiliary.Algebra.SpecialLinear2) (t : ℝ) (ht : 0 < t)
    (hAd : A 1 1 = conj (A 0 0))
    (hb : A 0 1 = -conj (A 1 0) * (t : ℂ) ^ 2) :
    mobiusSpecialLinearProjection A •
      (⟨Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 t,
        by exact ht⟩ : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) =
      (⟨Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 t,
        by exact ht⟩ : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) := by
  have hd := A.det_coe
  rw [Matrix.det_fin_two] at hd
  have hnorm : Complex.normSq (A 0 0) + Complex.normSq (A 1 0) * t ^ 2 = 1 := by
    have hc : (((Complex.normSq (A 0 0) + Complex.normSq (A 1 0) * t ^ 2 : ℝ)) : ℂ) = 1 := by
      calc
        _ = A 0 0 * conj (A 0 0) + (A 1 0 * conj (A 1 0)) * (t : ℂ) ^ 2 := by
          rw [Complex.mul_conj, Complex.mul_conj]
          push_cast
          rfl
        _ = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by rw [hAd, hb]; ring
        _ = 1 := hd
    exact_mod_cast hc
  have hD : poincareDenominator (A : Auxiliary.Algebra.ComplexMatrix2) 0 t = 1 := by
    simp only [poincareDenominator, mul_zero, zero_add, hAd, RCLike.norm_conj,
      ← Complex.normSq_eq_norm_sq]
    exact hnorm
  have hz : A 0 1 * conj (A 1 1) + A 0 0 * conj (A 1 0) * (t : ℂ) ^ 2 = 0 := by
    rw [hAd, hb, Complex.conj_conj]
    ring
  rw [mobiusUpperHalfSpace_smul, mobiusPoincareHom_specialLinearProjection]
  apply Subtype.ext
  change poincareCoordinate (A : Auxiliary.Algebra.ComplexMatrix2)
    (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 t) = Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 t
  simp only [poincareCoordinate, Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint,
    Hyperbolic.QuaternionHalfSpace.quaternionHeight_threePoint,
    poincareHorizontal, poincareHeight, mul_zero, zero_add, hD, Complex.ofReal_one,
    hz, div_one, A.det_coe, norm_one, one_mul]
/-- An all-elliptic group containing a nontrivial standard rotation has one common actual vertical fixed point. -/
theorem elliptic_group_standard_common_fixed (G : Subgroup complexMobiusGroup)
    (hG : ∀ f ∈ G, f ≠ 1 → MobiusElliptic f) (k : ℂˣ)
    (hk : (k : ℂ) ≠ 1) (hkn : ‖(k : ℂ)‖ = 1) (hkg : mobiusStandardElement k ∈ G) :
    ∃ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, ∀ f ∈ G, f • q = q := by
  obtain ⟨R, hRproj, hR01, hR10, hRd, hRi⟩ := unit_standard_specialLinear_diagonal k hk hkn
  have hR : mobiusSpecialLinearProjection R ∈ G := hRproj ▸ hkg
  have hdiag (A : Auxiliary.Algebra.SpecialLinear2) (hA : mobiusSpecialLinearProjection A ∈ G) :
      A 1 1 = conj (A 0 0) :=
    elliptic_group_lift_conjugate_diagonal G hG R hR hR01 hR10 hRd hRi A hA
  by_cases hex : ∃ A : Auxiliary.Algebra.SpecialLinear2, mobiusSpecialLinearProjection A ∈ G ∧ A 1 0 ≠ 0
  · obtain ⟨B, hB, hBc⟩ := hex
    have hBnorm := elliptic_group_lift_normSq_le_one G hG R hR hR01 hR10 hRd hRi B hB
    have hBstrict : Complex.normSq (B 0 0) < 1 := by
      apply lt_of_le_of_ne hBnorm
      intro he
      have hd := B.det_coe
      rw [Matrix.det_fin_two, hdiag B hB, Complex.mul_conj, he, Complex.ofReal_one] at hd
      have hprod : B 0 1 * B 1 0 = 0 := by linear_combination -hd
      have hb := (mul_eq_zero.mp hprod).resolve_right hBc
      exact hBc (elliptic_group_lift_offDiagonal_zero G hG R hR hR01 hR10 hRd hRi B hB (Or.inl hb)).2
    obtain ⟨t, ht, hBt⟩ := specialLinear_positive_vertical_ratio B (hdiag B hB) hBstrict hBc
    refine ⟨⟨Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 t, ht⟩, ?_⟩
    intro f hf
    obtain ⟨A, rfl⟩ := mobiusSpecialLinearProjection_surjective f
    have hBA : mobiusSpecialLinearProjection (B * A) ∈ G := by
      rw [map_mul]
      exact G.mul_mem hB hf
    have hrel := specialLinear_product_conjugate_diagonal B A (hdiag B hB) (hdiag A hf)
      (hdiag (B * A) hBA)
    rw [hBt] at hrel
    have hsmall : -(t : ℂ) ^ 2 * A 1 0 = conj (A 0 1) := by
      apply mul_left_cancel₀ ((map_ne_zero (starRingEnd ℂ)).mpr hBc)
      linear_combination hrel
    have hh := congrArg (starRingEnd ℂ) hsmall
    simp only [map_mul, map_neg, map_pow, Complex.conj_ofReal, Complex.conj_conj] at hh
    have hb : A 0 1 = -conj (A 1 0) * (t : ℂ) ^ 2 := by
      rw [← hh]
      ring
    exact specialLinear_vertical_fixed A t ht (hdiag A hf) hb
  · refine ⟨⟨Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 1, show (0 : ℝ) < 1 from zero_lt_one⟩, ?_⟩
    intro f hf
    obtain ⟨A, rfl⟩ := mobiusSpecialLinearProjection_surjective f
    have hc : A 1 0 = 0 := by
      by_contra hc
      exact hex ⟨A, hf, hc⟩
    obtain ⟨hb, _⟩ := elliptic_group_lift_offDiagonal_zero G hG R hR hR01 hR10 hRd hRi A hf (Or.inr hc)
    exact specialLinear_vertical_fixed A 1 zero_lt_one (hdiag A hf) (by simp [hb, hc])

/-- The full-space geometric elliptic condition gives a common actual H3 point for the whole group. -/
theorem all_nonidentity_elliptic_iff_common_halfSpace_fixedPoint (G : Subgroup complexMobiusGroup) :
    (∀ f ∈ G, f ≠ 1 → MobiusElliptic f) ↔
      ∃ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, ∀ f ∈ G, f • q = q := by
  constructor
  · intro hG
    by_cases hex : ∃ f ∈ G, f ≠ 1
    · obtain ⟨f, hf, hne⟩ := hex
      obtain ⟨k, hk, hkn, hc⟩ := (mobiusElliptic_iff_conjugate_standard f).mp (hG f hf hne)
      obtain ⟨q, hq⟩ := isConj_iff.mp hc
      let H := G.map (MulAut.conj q).toMonoidHom
      have hH : ∀ g ∈ H, g ≠ 1 → MobiusElliptic g := by
        rintro g ⟨a, ha, rfl⟩ hne
        change MobiusElliptic (q * a * q⁻¹)
        apply (mobiusElliptic_conjugation a q).mpr
        apply hG a ha
        intro he
        apply hne
        change q * a * q⁻¹ = 1
        simp [he]
      have hkH : mobiusStandardElement k ∈ H := ⟨f, hf, hq⟩
      obtain ⟨p, hp⟩ := elliptic_group_standard_common_fixed H hH k hk hkn hkH
      refine ⟨q⁻¹ • p, ?_⟩
      intro g hg
      have hfix := hp (q * g * q⁻¹) (show q * g * q⁻¹ ∈ H from ⟨g, hg, rfl⟩)
      have hh := congrArg (fun r : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => q⁻¹ • r) hfix
      simpa only [mul_smul, inv_smul_smul] using hh
    · refine ⟨Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ, ?_⟩
      intro f hf
      have he : f = 1 := by
        by_contra hn
        exact hex ⟨f, hf, hn⟩
      simp [he]
  · exact mobius_common_H3_fixed_all_elliptic G

/-- Every finite subgroup of the actual Mobius group has a common H3 fixed point. -/
theorem mobius_finite_subgroup_common_H3_fixed (G : Subgroup complexMobiusGroup) [Finite G] :
    ∃ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, ∀ f ∈ G, f • q = q := by
  apply (all_nonidentity_elliptic_iff_common_halfSpace_fixedPoint G).mp
  intro f hf hn
  have hfin : IsOfFinOrder f := by
    obtain ⟨n, hn, he⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite (⟨f, hf⟩ : G))
    apply isOfFinOrder_iff_pow_eq_one.mpr
    exact ⟨n, hn, by simpa using congrArg (fun g : G => (g : complexMobiusGroup)) he⟩
  exact mobius_finite_order_elliptic f hn hfin


/-- Exact finite-point iterates of the actual geometric standard representative. -/
theorem mobiusStandardElement_pow_coe (k : ℂˣ) (n : ℕ) (z : ℂ) :
    ((mobiusStandardElement k ^ n : complexMobiusGroup) : Equiv.Perm ExtendedComplex) z =
      ((if (k : ℂ) = 1 then z + (n : ℂ) else (k : ℂ) ^ n * z : ℂ) : ExtendedComplex) := by
  have h := Mobius.Classification.standardElement_pow_coe k n z
  simpa only [← mobiusStandardElement_equiv, ← map_pow,
    complexMobiusEquivFractionalLinear_apply] using h

/-- Infinity is fixed by every natural iterate of a standard representative. -/
theorem mobiusStandardElement_pow_infty (k : ℂˣ) (n : ℕ) :
    ((mobiusStandardElement k ^ n : complexMobiusGroup) : Equiv.Perm ExtendedComplex) ∞ = ∞ := by
  have h := Mobius.Classification.standardElement_pow_infty k n
  simpa only [← mobiusStandardElement_equiv, ← map_pow,
    complexMobiusEquivFractionalLinear_apply] using h

/-- A complex sequence escaping every norm bound converges to the actual compactification point. -/
theorem tendsto_complex_coe_infty_of_norm {u : ℕ → ℂ}
    (hu : Tendsto (fun n => ‖u n‖) atTop atTop) :
    Tendsto (fun n => (u n : ExtendedComplex)) atTop (𝓝 ∞) := by
  apply OnePoint.tendsto_coe_infty.comp
  rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
  exact tendsto_norm_atTop_iff_cobounded.mp hu

/-- The standard translation converges to infinity at every actual boundary point. -/
theorem mobius_translation_iterates_tendsto (z : ExtendedComplex) :
    Tendsto (fun n : ℕ => ((mobiusStandardElement 1 ^ n : complexMobiusGroup) :
      Equiv.Perm ExtendedComplex) z) atTop (𝓝 ∞) := by
  induction z using OnePoint.rec with
  | infty => simpa only [mobiusStandardElement_pow_infty] using tendsto_const_nhds
  | coe z =>
    simp only [mobiusStandardElement_pow_coe, Units.val_one, ite_true]
    apply OnePoint.tendsto_coe_infty.comp
    rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact (tendsto_const_add_cobounded z).comp tendsto_natCast_atTop_cobounded

/-- Contracting standard dilations converge to zero at every finite boundary point. -/
theorem mobius_contraction_iterates_tendsto (k : ℂˣ) (hk : ‖(k : ℂ)‖ < 1) (z : ℂ) :
    Tendsto (fun n : ℕ => ((mobiusStandardElement k ^ n : complexMobiusGroup) :
      Equiv.Perm ExtendedComplex) z) atTop (𝓝 ((0 : ℂ) : ExtendedComplex)) := by
  have hk1 : (k : ℂ) ≠ 1 := by intro h; simp [h] at hk
  simp only [mobiusStandardElement_pow_coe, ite_eq_right hk1]
  have h := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hk).mul_const z
  simpa only [Function.comp_def, zero_mul] using OnePoint.continuous_coe.continuousAt.tendsto.comp h

/-- Expanding standard dilations converge to infinity at every nonzero finite boundary point. -/
theorem mobius_expansion_iterates_tendsto (k : ℂˣ) (hk : 1 < ‖(k : ℂ)‖)
    (z : ℂ) (hz : z ≠ 0) :
    Tendsto (fun n : ℕ => ((mobiusStandardElement k ^ n : complexMobiusGroup) :
      Equiv.Perm ExtendedComplex) z) atTop (𝓝 ∞) := by
  have hk1 : (k : ℂ) ≠ 1 := by intro h; simp [h] at hk
  simp only [mobiusStandardElement_pow_coe, ite_eq_right hk1]
  apply tendsto_complex_coe_infty_of_norm
  simp only [norm_mul, norm_pow]
  exact (tendsto_pow_atTop_atTop_of_one_lt hk).atTop_mul_const (norm_pos_iff.mpr hz)

/-- Natural iterates commute with actual geometric conjugation. -/
theorem mobius_iterates_conjugation (f q : complexMobiusGroup) (n : ℕ)
    (z : ExtendedComplex) :
    (((q * f * q⁻¹) ^ n : complexMobiusGroup) : Equiv.Perm ExtendedComplex) z =
      (q : Equiv.Perm ExtendedComplex)
        (((f ^ n : complexMobiusGroup) : Equiv.Perm ExtendedComplex)
          (((q⁻¹ : complexMobiusGroup) : Equiv.Perm ExtendedComplex) z)) := by
  rw [conj_pow]
  rfl

/-- Every parabolic map has a fixed point attracting every boundary point under forward iteration. -/
theorem mobius_parabolic_iterates_tendsto (f : complexMobiusGroup) (hf : MobiusParabolic f) :
    ∃ a : ExtendedComplex, (f : Equiv.Perm ExtendedComplex) a = a ∧
      ∀ z : ExtendedComplex, Tendsto
        (fun n : ℕ => ((f ^ n : complexMobiusGroup) : Equiv.Perm ExtendedComplex) z)
        atTop (𝓝 a) := by
  have hc := (mobiusBoundaryParabolic_iff_conjugate_translation f hf.1).mp hf
  obtain ⟨q, rfl⟩ := isConj_iff.mp hc.symm
  refine ⟨(q : Equiv.Perm ExtendedComplex) ∞, ?_, ?_⟩
  · change q.val ((mobiusStandardElement 1).val (q.val.symm (q.val ∞))) = q.val ∞
    rw [Equiv.symm_apply_apply, mobiusStandardElement_infty]
  · intro z
    simp only [mobius_iterates_conjugation]
    exact (continuous_mobiusBoundary q).continuousAt.tendsto.comp
      (mobius_translation_iterates_tendsto _)

/-- Uniform convergence is measured with the actual sphere-induced chordal metric. -/
def MobiusIteratesConvergeUniformlyOn (f : complexMobiusGroup) (a : ExtendedComplex)
    (K : Set ExtendedComplex) : Prop :=
  letI := complexChordalMetricSpace
  TendstoUniformlyOn
    (fun n : ℕ => fun z : ExtendedComplex =>
      ((f ^ n : complexMobiusGroup) : Equiv.Perm ExtendedComplex) z)
    (fun _ => a) atTop K

/-- The constant-limit uniform convergence criterion in the actual compactification topology. -/
theorem mobiusIteratesConvergeUniformlyOn_iff (f : complexMobiusGroup)
    (a : ExtendedComplex) (K : Set ExtendedComplex) :
    MobiusIteratesConvergeUniformlyOn f a K ↔
      ∀ V ∈ 𝓝 a, ∀ᶠ n : ℕ in atTop, ∀ z ∈ K,
        ((f ^ n : complexMobiusGroup) : Equiv.Perm ExtendedComplex) z ∈ V := by
  let := complexChordalMetricSpace
  change TendstoUniformlyOn _ _ _ _ ↔ _
  rw [tendstoUniformlyOn_iff_tendstoUniformlyOnFilter]
  rw [tendstoUniformlyOnFilter_iff_tendsto, ← Uniform.tendsto_nhds_right]
  change (∀ V ∈ 𝓝 a, ∀ᶠ nz : ℕ × ExtendedComplex in atTop ×ˢ Filter.principal K,
    ((f ^ nz.1 : complexMobiusGroup) : Equiv.Perm ExtendedComplex) nz.2 ∈ V) ↔ _
  simp only [Filter.eventually_prod_principal_iff]

/-- A compact subset of the finite chart has a uniform Euclidean norm bound. -/
theorem compact_boundary_norm_bound {K : Set ExtendedComplex} (hK : IsCompact K)
    (hKinf : (∞ : ExtendedComplex) ∉ K) :
    ∃ R : ℝ, ∀ z : ℂ, (z : ExtendedComplex) ∈ K → ‖z‖ ≤ R := by
  have hKr : K ⊆ Set.range ((↑) : ℂ → ExtendedComplex) := by
    intro z hz
    exact OnePoint.ne_infty_iff_exists.mp (fun h => hKinf (h ▸ hz))
  have hc := OnePoint.isOpenEmbedding_coe.isInducing.isCompact_preimage' hK hKr
  exact hc.exists_bound_of_continuousOn continuous_id.continuousOn

/-- Standard translations converge uniformly on every compact subset avoiding infinity. -/
theorem mobius_translation_iterates_uniformlyOn {K : Set ExtendedComplex}
    (hK : IsCompact K) (hKinf : (∞ : ExtendedComplex) ∉ K) :
    MobiusIteratesConvergeUniformlyOn (mobiusStandardElement 1) ∞ K := by
  rw [mobiusIteratesConvergeUniformlyOn_iff]
  intro V hV
  obtain ⟨L, ⟨_, hLc⟩, hLV⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hV
  obtain ⟨R, hR⟩ := compact_boundary_norm_bound hK hKinf
  obtain ⟨B, hB⟩ := hLc.exists_bound_of_continuousOn continuous_id.continuousOn
  filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_gt_atTop (R + B)]
    with n hn
  intro w hw
  obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp (fun h => hKinf (h ▸ hw))
  rw [mobiusStandardElement_pow_coe]
  simp only [Units.val_one, ite_true]
  apply hLV
  apply Set.mem_union_left
  apply Set.mem_image_of_mem
  change z + (n : ℂ) ∉ L
  intro hzL
  have hbound := hB _ hzL
  simp only [id_eq] at hbound
  have hz := hR z hw
  have htri := norm_add_le (z + (n : ℂ)) (-z)
  have hnat : ‖(n : ℂ)‖ = (n : ℝ) := by simp
  have hcancel : z + (n : ℂ) + -z = (n : ℂ) := by ring
  rw [hcancel, hnat, norm_neg] at htri
  linarith

/-- Uniform convergence to a constant is transported by actual Möbius conjugation. -/
theorem mobius_iterates_uniformlyOn_conjugation (f q : complexMobiusGroup)
    (a : ExtendedComplex) (K : Set ExtendedComplex)
    (h : MobiusIteratesConvergeUniformlyOn f a
      (((q⁻¹ : complexMobiusGroup) : Equiv.Perm ExtendedComplex) '' K)) :
    MobiusIteratesConvergeUniformlyOn (q * f * q⁻¹)
      ((q : Equiv.Perm ExtendedComplex) a) K := by
  rw [mobiusIteratesConvergeUniformlyOn_iff] at h ⊢
  intro V hV
  have hpre := (continuous_mobiusBoundary q).continuousAt.preimage_mem_nhds hV
  filter_upwards [h _ hpre] with n hn
  intro z hz
  rw [mobius_iterates_conjugation]
  exact hn _ ⟨z, hz, rfl⟩

/-- The parabolic assertion of includes genuine uniform convergence on compact sets. -/
theorem parabolic_iterates_tendsto_unique_fixedPoint_uniformly_off (f : complexMobiusGroup) (hf : MobiusParabolic f) :
    ∃ a : ExtendedComplex, (f : Equiv.Perm ExtendedComplex) a = a ∧
      (∀ z : ExtendedComplex, Tendsto
        (fun n : ℕ => ((f ^ n : complexMobiusGroup) : Equiv.Perm ExtendedComplex) z)
        atTop (𝓝 a)) ∧
      ∀ K : Set ExtendedComplex, IsCompact K → a ∉ K →
        MobiusIteratesConvergeUniformlyOn f a K := by
  have hc := (mobiusBoundaryParabolic_iff_conjugate_translation f hf.1).mp hf
  obtain ⟨q, rfl⟩ := isConj_iff.mp hc.symm
  refine ⟨(q : Equiv.Perm ExtendedComplex) ∞, ?_, ?_, ?_⟩
  · change q.val ((mobiusStandardElement 1).val (q.val.symm (q.val ∞))) = q.val ∞
    rw [Equiv.symm_apply_apply, mobiusStandardElement_infty]
  · intro z
    simp only [mobius_iterates_conjugation]
    exact (continuous_mobiusBoundary q).continuousAt.tendsto.comp
      (mobius_translation_iterates_tendsto _)
  · intro K hK haK
    apply mobius_iterates_uniformlyOn_conjugation
    apply mobius_translation_iterates_uniformlyOn
    · exact hK.image (continuous_mobiusBoundary q⁻¹)
    · rintro ⟨z, hz, he⟩
      apply haK
      have hq := congrArg q.val he
      change q.val (q.val.symm z) = q.val ∞ at hq
      rw [Equiv.apply_symm_apply] at hq
      exact hq ▸ hz

/-- Contracting standard dilations converge uniformly on compact sets in the finite chart. -/
theorem mobius_contraction_iterates_uniformlyOn (k : ℂˣ) (hk : ‖(k : ℂ)‖ < 1)
    {K : Set ExtendedComplex} (hK : IsCompact K) (hKinf : (∞ : ExtendedComplex) ∉ K) :
    MobiusIteratesConvergeUniformlyOn (mobiusStandardElement k) (0 : ℂ) K := by
  have hk1 : (k : ℂ) ≠ 1 := by intro h; simp [h] at hk
  rw [mobiusIteratesConvergeUniformlyOn_iff]
  intro V hV
  have hp := OnePoint.continuous_coe.continuousAt.preimage_mem_nhds hV
  obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhds_iff.mp hp
  obtain ⟨R, hR⟩ := compact_boundary_norm_bound hK hKinf
  have hpow : Tendsto (fun n : ℕ => ‖(k : ℂ)‖ ^ n * max R 1) atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hk).mul_const (max R 1)
  filter_upwards [hpow.eventually (gt_mem_nhds hε)] with n hn
  intro w hw
  obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.mp (fun h => hKinf (h ▸ hw))
  rw [mobiusStandardElement_pow_coe]
  simp only [ite_eq_right hk1]
  apply hεV
  simp only [Metric.mem_ball, dist_zero_right, norm_mul, norm_pow]
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left ((hR z hw).trans (le_max_left R 1)) (pow_nonneg (norm_nonneg _) n)) hn

/-- Compact boundary sets avoiding zero have a positive Euclidean norm lower bound in the finite chart. -/
theorem compact_boundary_norm_lower_bound {K : Set ExtendedComplex} (hK : IsCompact K)
    (hKzero : ((0 : ℂ) : ExtendedComplex) ∉ K) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z : ℂ, (z : ExtendedComplex) ∈ K → δ ≤ ‖z‖ := by
  have hp := OnePoint.continuous_coe.continuousAt.preimage_mem_nhds
    (hK.isClosed.compl_mem_nhds hKzero)
  obtain ⟨δ, hδ, hδK⟩ := Metric.mem_nhds_iff.mp hp
  refine ⟨δ, hδ, ?_⟩
  intro z hz
  apply le_of_not_gt
  intro hzδ
  exact hδK (by simpa only [Metric.mem_ball, dist_zero_right] using hzδ) hz

/-- Expanding standard dilations converge uniformly on every compact boundary set avoiding zero. -/
theorem mobius_expansion_iterates_uniformlyOn (k : ℂˣ) (hk : 1 < ‖(k : ℂ)‖)
    {K : Set ExtendedComplex} (hK : IsCompact K)
    (hKzero : ((0 : ℂ) : ExtendedComplex) ∉ K) :
    MobiusIteratesConvergeUniformlyOn (mobiusStandardElement k) ∞ K := by
  have hk1 : (k : ℂ) ≠ 1 := by intro h; simp [h] at hk
  rw [mobiusIteratesConvergeUniformlyOn_iff]
  intro V hV
  obtain ⟨L, ⟨_, hLc⟩, hLV⟩ := OnePoint.hasBasis_nhds_infty.mem_iff.mp hV
  obtain ⟨δ, hδ, hδK⟩ := compact_boundary_norm_lower_bound hK hKzero
  obtain ⟨B, hB⟩ := hLc.exists_bound_of_continuousOn continuous_id.continuousOn
  have hpow := (tendsto_pow_atTop_atTop_of_one_lt hk).atTop_mul_const hδ
  filter_upwards [hpow.eventually_gt_atTop B] with n hn
  intro w hw
  induction w using OnePoint.rec with
  | infty =>
    rw [mobiusStandardElement_pow_infty]
    exact hLV (Set.mem_union_right _ (Set.mem_singleton _))
  | coe z =>
    rw [mobiusStandardElement_pow_coe]
    simp only [ite_eq_right hk1]
    apply hLV
    apply Set.mem_union_left
    apply Set.mem_image_of_mem
    change (k : ℂ) ^ n * z ∉ L
    intro hzL
    have hbound := hB _ hzL
    simp only [id_eq, norm_mul, norm_pow] at hbound
    have hz := hδK z hw
    have hmul := mul_le_mul_of_nonneg_left hz (pow_nonneg (norm_nonneg (k : ℂ)) n)
    linarith

/-- Each standard loxodromic map has an attracting and repelling boundary pair with compact-uniform attraction. -/
theorem mobius_standard_loxodromic_forward_dynamics (k : ℂˣ) (hk : ‖(k : ℂ)‖ ≠ 1) :
    ∃ a b : ExtendedComplex, a ≠ b ∧
      (mobiusStandardElement k : Equiv.Perm ExtendedComplex) a = a ∧
      (mobiusStandardElement k : Equiv.Perm ExtendedComplex) b = b ∧
      (∀ z : ExtendedComplex, z ≠ b → Tendsto
        (fun n : ℕ => ((mobiusStandardElement k ^ n : complexMobiusGroup) :
          Equiv.Perm ExtendedComplex) z) atTop (𝓝 a)) ∧
      ∀ K : Set ExtendedComplex, IsCompact K → b ∉ K →
        MobiusIteratesConvergeUniformlyOn (mobiusStandardElement k) a K := by
  have hk1 : (k : ℂ) ≠ 1 := by intro h; simp [h] at hk
  have hzero : (mobiusStandardElement k : Equiv.Perm ExtendedComplex) (0 : ℂ) = (0 : ℂ) := by
    rw [mobiusStandardElement_coe]
    simp only [ite_eq_right hk1, mul_zero]
  rcases lt_or_gt_of_ne hk with hklt | hkgt
  · refine ⟨(0 : ℂ), ∞, OnePoint.coe_ne_infty _, hzero, mobiusStandardElement_infty k,
      ?_, fun _ hK hKinf => mobius_contraction_iterates_uniformlyOn k hklt hK hKinf⟩
    intro z hz
    obtain ⟨w, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hz
    exact mobius_contraction_iterates_tendsto k hklt w
  · refine ⟨∞, (0 : ℂ), (OnePoint.coe_ne_infty (0 : ℂ)).symm,
      mobiusStandardElement_infty k, hzero, ?_,
      fun _ hK hKzero => mobius_expansion_iterates_uniformlyOn k hkgt hK hKzero⟩
    intro z hz
    induction z using OnePoint.rec with
    | infty => simpa only [mobiusStandardElement_pow_infty] using tendsto_const_nhds
    | coe w =>
      exact mobius_expansion_iterates_tendsto k hkgt w
        (fun hw => hz (congrArg ((↑) : ℂ → ExtendedComplex) hw))

/-- Loxodromic iterates converge uniformly on compact sets away from the repelling fixed point. -/
theorem loxodromic_iterates_tendsto_attractor_uniformly_off_repeller (f : complexMobiusGroup) (hf :
    MobiusLoxodromic f) :
    ∃ a b : ExtendedComplex, a ≠ b ∧
      (f : Equiv.Perm ExtendedComplex) a = a ∧
      (f : Equiv.Perm ExtendedComplex) b = b ∧
      (∀ z : ExtendedComplex, z ≠ b → Tendsto
        (fun n : ℕ => ((f ^ n : complexMobiusGroup) : Equiv.Perm ExtendedComplex) z)
        atTop (𝓝 a)) ∧
      ∀ K : Set ExtendedComplex, IsCompact K → b ∉ K →
        MobiusIteratesConvergeUniformlyOn f a K := by
  obtain ⟨k, hk, hc⟩ := (mobiusLoxodromic_iff_conjugate_standard f).mp hf
  obtain ⟨q, rfl⟩ := isConj_iff.mp hc.symm
  obtain ⟨a, b, hab, ha, hb, hpoint, hunif⟩ := mobius_standard_loxodromic_forward_dynamics k hk
  refine ⟨q.val a, q.val b, q.val.injective.ne hab, ?_, ?_, ?_, ?_⟩
  · change q.val ((mobiusStandardElement k).val (q.val.symm (q.val a))) = q.val a
    rw [Equiv.symm_apply_apply, ha]
  · change q.val ((mobiusStandardElement k).val (q.val.symm (q.val b))) = q.val b
    rw [Equiv.symm_apply_apply, hb]
  · intro z hz
    simp only [mobius_iterates_conjugation]
    apply (continuous_mobiusBoundary q).continuousAt.tendsto.comp
    apply hpoint
    intro he
    apply hz
    have he' := congrArg q.val he
    change q.val (q.val.symm z) = q.val b at he'
    simpa only [Equiv.apply_symm_apply] using he'
  · intro K hK hbK
    apply mobius_iterates_uniformlyOn_conjugation
    apply hunif
    · exact hK.image (continuous_mobiusBoundary q⁻¹)
    · rintro ⟨z, hz, he⟩
      apply hbK
      have hq := congrArg q.val he
      change q.val (q.val.symm z) = q.val b at hq
      rw [Equiv.apply_symm_apply] at hq
      exact hq ▸ hz

/-- Inversion in an actual generalized circle, transported through the fixed real isometric chart. -/
def IsComplexInversePair (S : Set ExtendedComplex) (a b : ExtendedComplex) : Prop :=
  Inversive.IsInversePair (extendedComplexEuclideanHomeomorph '' S)
    (extendedComplexEuclideanHomeomorph a) (extendedComplexEuclideanHomeomorph b)

/-- The fixed real representative acts exactly through the complex coordinate chart. -/
theorem mobiusRealRepresentative_chart (f : complexMobiusGroup) (z : ExtendedComplex) :
    (mobiusRealRepresentative f : Inversive.ExtendedHomeomorph 2)
      (extendedComplexEuclideanHomeomorph z) =
      extendedComplexEuclideanHomeomorph ((f : Equiv.Perm ExtendedComplex) z) := by
  have h := congrArg (fun g : Equiv.Perm ExtendedComplex =>
    extendedComplexEuclideanHomeomorph (g z)) (mobiusRealRepresentative_coordinates f)
  simpa only [euclideanToComplexHom_apply, Homeomorph.apply_symm_apply] using h

/-- Actual Möbius transformations transport actual circle-inverse pairs. -/
theorem IsComplexInversePair.image {S : Set ExtendedComplex} {a b : ExtendedComplex}
    (h : IsComplexInversePair S a b) (f : complexMobiusGroup) :
    IsComplexInversePair ((f : Equiv.Perm ExtendedComplex) '' S)
      ((f : Equiv.Perm ExtendedComplex) a) ((f : Equiv.Perm ExtendedComplex) b) := by
  have hi := Inversive.IsInversePair.image h (mobiusRealRepresentative f).property
  have he : (mobiusRealRepresentative f : Inversive.ExtendedHomeomorph 2) ''
      (extendedComplexEuclideanHomeomorph '' S) =
      extendedComplexEuclideanHomeomorph '' ((f : Equiv.Perm ExtendedComplex) '' S) := by
    rw [Set.image_image, Set.image_image]
    congr 1
    funext z
    exact mobiusRealRepresentative_chart f z
  simpa only [IsComplexInversePair, he, mobiusRealRepresentative_chart] using hi

/-- The actual inverse-pair relation is symmetric. -/
theorem IsComplexInversePair.symm {S : Set ExtendedComplex} {a b : ExtendedComplex}
    (h : IsComplexInversePair S a b) : IsComplexInversePair S b a :=
  Inversive.IsInversePair.symm h

/-- The circles for which zero and infinity are inverse are precisely genuine circles centered at zero. -/
theorem complexInversePair_zero_infty_circle {S : Set ExtendedComplex}
    (h : IsComplexInversePair S (0 : ℂ) ∞) :
    ∃ r : ℝ, 0 < r ∧ S = complexCircle 0 r := by
  have hi : Inversive.IsInversePair (extendedComplexEuclideanHomeomorph '' S)
      ∞ ((0 : Inversive.Euclidean 2) : Inversive.ExtendedEuclidean 2) := by
    simpa only [IsComplexInversePair, extendedComplexEuclideanHomeomorph_coe,
      extendedComplexEuclideanHomeomorph_infty, map_zero] using h.symm
  obtain ⟨F, hF, hFS, hFi⟩ := hi
  rcases hF with ⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩
  · rw [Inversive.sphereInversionHomeomorph_apply, Inversive.sphereInversion_infty,
      OnePoint.coe_eq_coe] at hFi
    subst c
    refine ⟨r, hr, ?_⟩
    apply (extendedComplexEuclideanHomeomorph.toEquiv.image_eq_iff_eq _ _).mp
    change extendedComplexEuclideanHomeomorph '' S =
      extendedComplexEuclideanHomeomorph '' complexCircle 0 r
    rw [← hFS, Inversive.fixedPoints_sphereInversion _ _ hr]
    simp only [complexCircle, complexChart_image_preimage, map_zero]
  · rw [Inversive.planeReflectionHomeomorph_apply, Inversive.planeReflection_infty] at hFi
    exact False.elim ((OnePoint.coe_ne_infty (0 : Inversive.Euclidean 2)) hFi.symm)

/-- A unit-modulus standard representative preserves every centered complex circle. -/
theorem mobius_standard_unit_preserves_centered_circle (k : ℂˣ) (hk1 : (k : ℂ) ≠ 1)
    (hk : ‖(k : ℂ)‖ = 1) (r : ℝ) :
    (mobiusStandardElement k : Equiv.Perm ExtendedComplex) '' complexCircle 0 r =
      complexCircle 0 r := by
  apply ((mobiusStandardElement k : Equiv.Perm ExtendedComplex).eq_preimage_iff_image_eq _ _).mp
  ext z
  induction z using OnePoint.rec with
  | infty => simp only [Set.mem_preimage, mobiusStandardElement_infty, complexCircle_infty]
  | coe z =>
    simp only [Set.mem_preimage, mobiusStandardElement_coe, ite_eq_right hk1,
      complexCircle_coe, sub_zero, norm_mul, hk, one_mul]

/-- The exact boundary fixed-point pair of a nontranslation standard form. -/
theorem mobiusStandardElement_boundary_fixed_iff (k : ℂˣ) (hk : (k : ℂ) ≠ 1)
    (z : ExtendedComplex) :
    (mobiusStandardElement k : Equiv.Perm ExtendedComplex) z = z ↔
      z = ((0 : ℂ) : ExtendedComplex) ∨ z = ∞ := by
  rw [mobiusStandardElement_apply, Mobius.Classification.standardForm_fixed_iff k hk]

/-- The elliptic assertion: every genuine circle making the fixed pair inverse is invariant. -/
theorem elliptic_preserves_generalized_circle_inverse_to_fixed_points (f : complexMobiusGroup) (hf : MobiusElliptic f)
    (a b : ExtendedComplex) (hab : a ≠ b)
    (ha : (f : Equiv.Perm ExtendedComplex) a = a)
    (hb : (f : Equiv.Perm ExtendedComplex) b = b)
    (S : Set ExtendedComplex) (hS : IsComplexInversePair S a b) :
    (f : Equiv.Perm ExtendedComplex) '' S = S := by
  obtain ⟨k, hk1, hkn, hc⟩ := (mobiusElliptic_iff_conjugate_standard f).mp hf
  obtain ⟨q, rfl⟩ := isConj_iff.mp hc.symm
  have ha' : (mobiusStandardElement k).val (q.val.symm a) = q.val.symm a := by
    apply q.val.injective
    change q.val ((mobiusStandardElement k).val (q.val.symm a)) = q.val (q.val.symm a)
    change q.val ((mobiusStandardElement k).val (q.val.symm a)) = a at ha
    simpa only [Equiv.apply_symm_apply] using ha
  have hb' : (mobiusStandardElement k).val (q.val.symm b) = q.val.symm b := by
    apply q.val.injective
    change q.val ((mobiusStandardElement k).val (q.val.symm b)) = q.val (q.val.symm b)
    change q.val ((mobiusStandardElement k).val (q.val.symm b)) = b at hb
    simpa only [Equiv.apply_symm_apply] using hb
  have hab' := q.val.symm.injective.ne hab
  have hi := hS.image q⁻¹
  have hzero : IsComplexInversePair (q.val.symm '' S) (0 : ℂ) ∞ := by
    rcases (mobiusStandardElement_boundary_fixed_iff k hk1 _).mp ha' with ha0 | hai
    · rcases (mobiusStandardElement_boundary_fixed_iff k hk1 _).mp hb' with hb0 | hbi
      · exact False.elim (hab' (ha0.trans hb0.symm))
      · simpa only [show (q⁻¹ : complexMobiusGroup).val = q.val.symm from rfl, ha0, hbi] using hi
    · rcases (mobiusStandardElement_boundary_fixed_iff k hk1 _).mp hb' with hb0 | hbi
      · simpa only [show (q⁻¹ : complexMobiusGroup).val = q.val.symm from rfl, hai, hb0] using hi.symm
      · exact False.elim (hab' (hai.trans hbi.symm))
  obtain ⟨r, _, hcircle⟩ := complexInversePair_zero_infty_circle hzero
  have hpres : (mobiusStandardElement k).val '' (q.val.symm '' S) = q.val.symm '' S := by
    rw [hcircle]
    exact mobius_standard_unit_preserves_centered_circle k hk1 hkn r
  apply (q.val.symm.image_eq_iff_eq _ _).mp
  rw [Set.image_image]
  have he : q.val.symm ∘ (q * mobiusStandardElement k * q⁻¹).val =
      (mobiusStandardElement k).val ∘ q.val.symm := by
    funext z
    change q.val.symm (q.val ((mobiusStandardElement k).val (q.val.symm z))) = _
    exact q.val.symm_apply_apply _
  change (q.val.symm ∘ (q * mobiusStandardElement k * q⁻¹).val) '' S = q.val.symm '' S
  rw [he]
  simpa only [Set.image_image, Function.comp_def] using hpres


/-- Inversion of a nontranslation standard representative inverts its genuine dilation parameter. -/
theorem mobiusStandardElement_inv (k : ℂˣ) (hk : (k : ℂ) ≠ 1) :
    (mobiusStandardElement k)⁻¹ = mobiusStandardElement k⁻¹ := by
  apply Eq.symm
  apply eq_inv_iff_mul_eq_one.mpr
  apply Subtype.ext
  apply Equiv.ext
  intro z
  have hki : (k : ℂ)⁻¹ ≠ 1 := inv_ne_one.mpr hk
  change (mobiusStandardElement k⁻¹).val ((mobiusStandardElement k).val z) = z
  induction z using OnePoint.rec with
  | infty => rw [mobiusStandardElement_infty, mobiusStandardElement_infty]
  | coe z =>
    rw [mobiusStandardElement_coe]
    simp only [ite_eq_right hk]
    rw [mobiusStandardElement_coe]
    simp only [Units.val_inv_eq_inv_val, ite_eq_right hki]
    congr 1
    exact inv_mul_cancel_left₀ k.ne_zero z

/-- The attractive and repulsive labels are defined by the actual forward and backward boundary limits. -/
def IsMobiusAttractingRepellingPair (f : complexMobiusGroup) (a b : ExtendedComplex) : Prop :=
  a ≠ b ∧ (f : Equiv.Perm ExtendedComplex) a = a ∧
    (f : Equiv.Perm ExtendedComplex) b = b ∧
    (∀ z : ExtendedComplex, z ≠ b → Tendsto
      (fun n : ℕ => ((f ^ n : complexMobiusGroup) : Equiv.Perm ExtendedComplex) z)
      atTop (𝓝 a)) ∧
    (∀ z : ExtendedComplex, z ≠ a → Tendsto
      (fun n : ℕ => ((f⁻¹ ^ n : complexMobiusGroup) : Equiv.Perm ExtendedComplex) z)
      atTop (𝓝 b))

/-- An attractive fixed point is the forward-limit member of an actual attracting-repelling pair. -/
def MobiusAttractiveFixedPoint (f : complexMobiusGroup) (a : ExtendedComplex) : Prop :=
  ∃ b : ExtendedComplex, IsMobiusAttractingRepellingPair f a b

/-- A repulsive fixed point is the backward-limit member of an actual attracting-repelling pair. -/
def MobiusRepulsiveFixedPoint (f : complexMobiusGroup) (b : ExtendedComplex) : Prop :=
  ∃ a : ExtendedComplex, IsMobiusAttractingRepellingPair f a b

/-- A contracting standard representative has zero attractive and infinity repulsive. -/
theorem mobius_standard_contraction_attracting_repelling (k : ℂˣ)
    (hk : ‖(k : ℂ)‖ < 1) : IsMobiusAttractingRepellingPair (mobiusStandardElement k) (0 : ℂ) ∞ := by
  have hk1 : (k : ℂ) ≠ 1 := by intro h; simp [h] at hk
  have hkpos := norm_pos_iff.mpr k.ne_zero
  have hkinv : 1 < ‖((k⁻¹ : ℂˣ) : ℂ)‖ := by
    simpa only [Units.val_inv_eq_inv_val, norm_inv] using (one_lt_inv₀ hkpos).mpr hk
  refine ⟨OnePoint.coe_ne_infty _, ?_, mobiusStandardElement_infty k, ?_, ?_⟩
  · rw [mobiusStandardElement_coe]
    simp only [ite_eq_right hk1, mul_zero]
  · intro z hz
    obtain ⟨w, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hz
    exact mobius_contraction_iterates_tendsto k hk w
  · intro z hz
    rw [mobiusStandardElement_inv k hk1]
    induction z using OnePoint.rec with
    | infty => simpa only [mobiusStandardElement_pow_infty] using tendsto_const_nhds
    | coe w =>
      exact mobius_expansion_iterates_tendsto k⁻¹ hkinv w
        (fun hw => hz (congrArg ((↑) : ℂ → ExtendedComplex) hw))

/-- An expanding standard representative has infinity attractive and zero repulsive. -/
theorem mobius_standard_expansion_attracting_repelling (k : ℂˣ)
    (hk : 1 < ‖(k : ℂ)‖) : IsMobiusAttractingRepellingPair (mobiusStandardElement k) ∞ (0 : ℂ) := by
  have hk1 : (k : ℂ) ≠ 1 := by intro h; simp [h] at hk
  have hkinv : ‖((k⁻¹ : ℂˣ) : ℂ)‖ < 1 := by
    simpa only [Units.val_inv_eq_inv_val, norm_inv] using (inv_lt_one₀ (by linarith : 0 < ‖(k : ℂ)‖)).mpr hk
  refine ⟨(OnePoint.coe_ne_infty (0 : ℂ)).symm, mobiusStandardElement_infty k, ?_, ?_, ?_⟩
  · rw [mobiusStandardElement_coe]
    simp only [ite_eq_right hk1, mul_zero]
  · intro z hz
    induction z using OnePoint.rec with
    | infty => simpa only [mobiusStandardElement_pow_infty] using tendsto_const_nhds
    | coe w =>
      exact mobius_expansion_iterates_tendsto k hk w
        (fun hw => hz (congrArg ((↑) : ℂ → ExtendedComplex) hw))
  · intro z hz
    rw [mobiusStandardElement_inv k hk1]
    obtain ⟨w, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hz
    exact mobius_contraction_iterates_tendsto k⁻¹ hkinv w

/-- Both boundary limits defining attraction and repulsion are transported by genuine conjugation. -/
theorem IsMobiusAttractingRepellingPair.conjugation {f : complexMobiusGroup}
    {a b : ExtendedComplex} (h : IsMobiusAttractingRepellingPair f a b)
    (q : complexMobiusGroup) :
    IsMobiusAttractingRepellingPair (q * f * q⁻¹) (q.val a) (q.val b) := by
  obtain ⟨hab, ha, hb, hfor, hback⟩ := h
  refine ⟨q.val.injective.ne hab, ?_, ?_, ?_, ?_⟩
  · change q.val (f.val (q.val.symm (q.val a))) = q.val a
    rw [Equiv.symm_apply_apply, ha]
  · change q.val (f.val (q.val.symm (q.val b))) = q.val b
    rw [Equiv.symm_apply_apply, hb]
  · intro z hz
    simp only [mobius_iterates_conjugation]
    apply (continuous_mobiusBoundary q).continuousAt.tendsto.comp
    apply hfor
    intro he
    apply hz
    have he' := congrArg q.val he
    change q.val (q.val.symm z) = q.val b at he'
    simpa only [Equiv.apply_symm_apply] using he'
  · intro z hz
    have hinv : (q * f * q⁻¹)⁻¹ = q * f⁻¹ * q⁻¹ := by simp only [mul_inv_rev, inv_inv, mul_assoc]
    rw [hinv]
    simp only [mobius_iterates_conjugation]
    apply (continuous_mobiusBoundary q).continuousAt.tendsto.comp
    apply hback
    intro he
    apply hz
    have he' := congrArg q.val he
    change q.val (q.val.symm z) = q.val a at he'
    simpa only [Equiv.apply_symm_apply] using he'

/-- Every geometrically loxodromic transformation has the attractive and repulsive labels. -/
theorem mobius_loxodromic_attracting_repelling (f : complexMobiusGroup)
    (hf : MobiusLoxodromic f) :
    ∃ a b : ExtendedComplex, IsMobiusAttractingRepellingPair f a b := by
  obtain ⟨k, hk, hc⟩ := (mobiusLoxodromic_iff_conjugate_standard f).mp hf
  obtain ⟨q, rfl⟩ := isConj_iff.mp hc.symm
  rcases lt_or_gt_of_ne hk with hkl | hkg
  · exact ⟨q.val (0 : ℂ), q.val ∞,
      (mobius_standard_contraction_attracting_repelling k hkl).conjugation q⟩
  · exact ⟨q.val ∞, q.val (0 : ℂ),
      (mobius_standard_expansion_attracting_repelling k hkg).conjugation q⟩

/-- A nontrivial standard dilation has the exact signed-iterate formula on finite points. -/
theorem mobiusStandardElement_zpow_coe (k : ℂˣ) (hk : (k : ℂ) ≠ 1) (n : ℤ) (z : ℂ) :
    ((mobiusStandardElement k ^ n : complexMobiusGroup) : Equiv.Perm ExtendedComplex) z =
      (((k : ℂ) ^ n * z : ℂ) : ExtendedComplex) := by
  cases n with
  | ofNat m =>
    change ((mobiusStandardElement k ^ (m : ℤ) : complexMobiusGroup) :
      Equiv.Perm ExtendedComplex) z = (((k : ℂ) ^ (m : ℤ) * z : ℂ) : ExtendedComplex)
    rw [zpow_natCast, zpow_natCast, mobiusStandardElement_pow_coe]
    simp only [ite_eq_right hk]
  | negSucc m =>
    rw [zpow_negSucc, ← inv_pow, mobiusStandardElement_inv k hk,
      mobiusStandardElement_pow_coe]
    have hki : (k : ℂ)⁻¹ ≠ 1 := inv_ne_one.mpr hk
    simp only [Units.val_inv_eq_inv_val, ite_eq_right hki, zpow_negSucc, inv_pow]

/-- Every term of a standard loxodromic two-sided orbit is distinct when the starting point is nonfixed. -/
theorem mobius_standard_loxodromic_orbit_injective (k : ℂˣ) (hk : ‖(k : ℂ)‖ ≠ 1)
    (z : ℂ) (hz : z ≠ 0) :
    Function.Injective (fun n : ℤ =>
      ((mobiusStandardElement k ^ n : complexMobiusGroup) : Equiv.Perm ExtendedComplex) z) := by
  have hk1 : (k : ℂ) ≠ 1 := by intro h; simp [h] at hk
  intro m n hmn
  simp only [mobiusStandardElement_zpow_coe k hk1, OnePoint.coe_eq_coe] at hmn
  have hp : (k : ℂ) ^ m = (k : ℂ) ^ n := mul_right_cancel₀ hz hmn
  have hn := congrArg norm hp
  simp only [norm_zpow] at hn
  exact zpow_right_injective₀ (norm_pos_iff.mpr k.ne_zero) hk hn

/-- A fixed boundary point remains fixed under every natural iterate. -/
theorem mobius_pow_fixed {f : complexMobiusGroup} {a : ExtendedComplex}
    (ha : f.val a = a) (n : ℕ) : (f ^ n).val a = a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change f.val ((f ^ n).val a) = a
    rw [ih, ha]

/-- A fixed boundary point is fixed by the actual inverse map. -/
theorem mobius_inv_fixed {f : complexMobiusGroup} {a : ExtendedComplex}
    (ha : f.val a = a) : (f⁻¹).val a = a := by
  change f.val.symm a = a
  exact f.val.symm_apply_eq.mpr ha.symm

/-- No iterate of a point distinct from a fixed point can hit that fixed point. -/
theorem mobius_pow_ne_fixed {f : complexMobiusGroup} {a z : ExtendedComplex}
    (ha : f.val a = a) (hz : z ≠ a) (n : ℕ) : (f ^ n).val z ≠ a := by
  intro he
  exact hz ((f ^ n).val.injective (he.trans (mobius_pow_fixed ha n).symm))

/-- The only accumulation point of a convergent sequence range omitting its limit is its limit. -/
theorem boundary_tendsto_accPt_range_iff {u : ℕ → ExtendedComplex} {a : ExtendedComplex}
    (hu : Tendsto u atTop (𝓝 a)) (ha : a ∉ Set.range u) (w : ExtendedComplex) :
    AccPt w (Filter.principal (Set.range u)) ↔ w = a := by
  constructor
  · intro hw
    by_contra hwa
    obtain ⟨U, V, hU, hV, hUV⟩ := t2_separation_nhds hwa
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hu.eventually hV)
    have hfinite : (U ∩ Set.range u).Finite := by
      apply Set.Finite.subset ((Finset.range N).finite_toSet.image u)
      rintro y ⟨hyU, m, rfl⟩
      refine ⟨m, ?_, rfl⟩
      simp only [Finset.mem_coe, Finset.mem_range]
      by_contra hm
      exact Set.disjoint_left.mp hUV hyU (hN m (Nat.le_of_not_gt hm))
    exact hfinite.not_infinite (Set.Infinite.of_accPt (hw.nhds_inter hU))
  · rintro rfl
    apply accPt_iff_nhds.mpr
    intro U hU
    obtain ⟨n, hn⟩ := (hu.eventually hU).exists
    exact ⟨u n, ⟨hn, Set.mem_range_self n⟩, fun he => ha (he ▸ Set.mem_range_self n)⟩

/-- The true two-sided orbit is the union of the forward and inverse natural orbits. -/
theorem mobius_zpow_orbit_eq_union (f : complexMobiusGroup) (z : ExtendedComplex) :
    Set.range (fun n : ℤ => (f ^ n).val z) =
      Set.range (fun n : ℕ => (f ^ n).val z) ∪
      Set.range (fun n : ℕ => (f⁻¹ ^ n).val z) := by
  ext w
  constructor
  · rintro ⟨n, rfl⟩
    cases n with
    | ofNat m =>
      exact Or.inl ⟨m, by
        change (f ^ m).val z = (f ^ (m : ℤ)).val z
        rw [zpow_natCast]⟩
    | negSucc m =>
      exact Or.inr ⟨m + 1, by
        change (f⁻¹ ^ (m + 1)).val z = (f ^ Int.negSucc m).val z
        rw [zpow_negSucc, inv_pow]⟩
  · rintro (⟨n, rfl⟩ | ⟨n, rfl⟩)
    · exact ⟨(n : ℤ), by
        change (f ^ (n : ℤ)).val z = (f ^ n).val z
        rw [zpow_natCast]⟩
    · exact ⟨-(n : ℤ), by
        change (f ^ (-(n : ℤ))).val z = (f⁻¹ ^ n).val z
        rw [zpow_neg, zpow_natCast, inv_pow]⟩

/-- A loxodromic nonfixed two-sided orbit accumulates at precisely the two dynamically labelled fixed points. -/
theorem mobius_loxodromic_orbit_accumulation {f : complexMobiusGroup} {a b : ExtendedComplex}
    (h : IsMobiusAttractingRepellingPair f a b) (z : ExtendedComplex)
    (hza : z ≠ a) (hzb : z ≠ b) (w : ExtendedComplex) :
    AccPt w (Filter.principal (Set.range (fun n : ℤ => (f ^ n).val z))) ↔
      w = a ∨ w = b := by
  obtain ⟨_, ha, hb, hfor, hback⟩ := h
  rw [mobius_zpow_orbit_eq_union, ← Filter.sup_principal, accPt_sup]
  rw [boundary_tendsto_accPt_range_iff (hfor z hzb)
    (by rintro ⟨n, hn⟩; exact mobius_pow_ne_fixed ha hza n hn)]
  rw [boundary_tendsto_accPt_range_iff (hback z hza)
    (by rintro ⟨n, hn⟩; exact mobius_pow_ne_fixed (mobius_inv_fixed hb) hzb n hn)]

/-- Signed iterates of actual Möbius transformations intertwine actual conjugation. -/
theorem mobius_ziterates_conjugation (f q : complexMobiusGroup) (n : ℤ)
    (z : ExtendedComplex) :
    (((q * f * q⁻¹) ^ n : complexMobiusGroup) : Equiv.Perm ExtendedComplex) z =
      q.val ((f ^ n).val (q.val.symm z)) := by
  rw [conj_zpow]
  rfl

/-- Every term of a true loxodromic two-sided orbit of a nonfixed boundary point is distinct. -/
theorem mobius_loxodromic_orbit_injective (f : complexMobiusGroup)
    (hf : MobiusLoxodromic f) (z : ExtendedComplex) (hz : f.val z ≠ z) :
    Function.Injective (fun n : ℤ => (f ^ n).val z) := by
  obtain ⟨k, hk, hc⟩ := (mobiusLoxodromic_iff_conjugate_standard f).mp hf
  obtain ⟨q, rfl⟩ := isConj_iff.mp hc.symm
  have hk1 : (k : ℂ) ≠ 1 := by intro h; simp [h] at hk
  have hfix : (mobiusStandardElement k).val (q.val.symm z) ≠ q.val.symm z := by
    intro h
    apply hz
    change q.val ((mobiusStandardElement k).val (q.val.symm z)) = z
    rw [h, Equiv.apply_symm_apply]
  have hni : q.val.symm z ≠ ∞ := by
    intro h
    apply hfix
    rw [h, mobiusStandardElement_infty]
  obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hni
  have hw0 : w ≠ 0 := by
    intro h
    apply hfix
    rw [← hw, h, mobiusStandardElement_coe]
    simp only [ite_eq_right hk1, mul_zero]
  intro m n hmn
  have hmn' := congrArg q.val.symm hmn
  simp only [mobius_ziterates_conjugation, Equiv.symm_apply_apply] at hmn'
  rw [← hw] at hmn'
  exact mobius_standard_loxodromic_orbit_injective k hk w hw0 hmn'

/-- A nonfixed two-sided loxodromic orbit is injective and accumulates at precisely its two fixed points. -/
theorem mobius_loxodromic_two_sided_orbit (f : complexMobiusGroup)
    (hf : MobiusLoxodromic f) :
    ∃ a b : ExtendedComplex, IsMobiusAttractingRepellingPair f a b ∧
      ∀ z : ExtendedComplex, f.val z ≠ z →
        Function.Injective (fun n : ℤ => (f ^ n).val z) ∧
        ∀ w : ExtendedComplex,
          AccPt w (Filter.principal (Set.range (fun n : ℤ => (f ^ n).val z))) ↔
            w = a ∨ w = b := by
  obtain ⟨a, b, hab⟩ := mobius_loxodromic_attracting_repelling f hf
  refine ⟨a, b, hab, ?_⟩
  intro z hz
  refine ⟨mobius_loxodromic_orbit_injective f hf z hz, ?_⟩
  have hza : z ≠ a := by intro h; apply hz; rw [h, hab.2.1]
  have hzb : z ≠ b := by intro h; apply hz; rw [h, hab.2.2.1]
  exact mobius_loxodromic_orbit_accumulation hab z hza hzb


/-- The axis is the actual interior fixed set of an elliptic Poincare extension. -/
def mobiusAxis (f : complexMobiusGroup) : Set Hyperbolic.QuaternionHalfSpace.UpperHalfSpace := {q | f • q = q}

/-- Boundary and full-space fixed points agree under the genuine boundary inclusion. -/
theorem mobiusExtendedFixedPoints_boundary_iff (f : complexMobiusGroup) (z : ExtendedComplex) :
    Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding z ∈ mobiusExtendedFixedPoints f ↔
      (f : Equiv.Perm ExtendedComplex) z = z := by
  change mobiusExtendedSpaceHom f (Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding z) =
    Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding z ↔ _
  change quaternionConjugateHom (mobiusGeometricPoincare f)
    (Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding z) =
      Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding z ↔ _
  rw [mobiusGeometricPoincare_boundary]
  exact Hyperbolic.QuaternionHalfSpace.injective_extendedBoundaryEmbedding.eq_iff

/-- Interior and full-space fixed sets agree for the true extension. -/
theorem mobiusExtendedFixedPoints_interior_iff (f : complexMobiusGroup) (q :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (q.val : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) ∈ mobiusExtendedFixedPoints f ↔ q ∈
      mobiusAxis f := by
  change mobiusExtendedSpaceHom f (q.val : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
    (q.val : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) ↔ f • q = q
  change quaternionConjugateHom (mobiusGeometricPoincare f)
    (q.val : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) = (q.val : OnePoint
      Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) ↔ _
  rw [(mobiusGeometricPoincare_geometric f).2.2 q, OnePoint.coe_eq_coe, Subtype.val_inj]

/-- Elliptic axes are nonempty actual subsets of H3. -/
theorem MobiusElliptic.axis_nonempty {f : complexMobiusGroup} (hf : MobiusElliptic f) :
    (mobiusAxis f).Nonempty := (mobiusElliptic_iff_H3_fixed f hf.1).mp hf

/-- The axis is transported by the actual H3 action under conjugation. -/
theorem mobiusAxis_conjugation (f q : complexMobiusGroup) :
    mobiusAxis (q * f * q⁻¹) = (fun p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => q • p) '' mobiusAxis f := by
  ext p
  constructor
  · intro hp
    refine ⟨q⁻¹ • p, ?_, smul_inv_smul q p⟩
    have hh := congrArg (fun p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => q⁻¹ • p) hp
    change q⁻¹ • ((q * f * q⁻¹) • p) = q⁻¹ • p at hh
    change f • (q⁻¹ • p) = q⁻¹ • p
    simpa only [mul_smul, inv_smul_smul] using hh
  · rintro ⟨p, hp, rfl⟩
    change (q * f * q⁻¹) • (q • p) = q • p
    simp only [mul_smul, inv_smul_smul, show f • p = p from hp]

/-- A nontrivial unit standard map has precisely the genuine positive vertical ray as axis. -/
theorem mobiusStandardElement_axis (k : ℂˣ) (hk : (k : ℂ) ≠ 1)
    (hkn : ‖(k : ℂ)‖ = 1) :
    mobiusAxis (mobiusStandardElement k) = {q | Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val = 0} := by
  ext q
  constructor
  · intro hq
    have hz := congrArg (fun p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
      Hyperbolic.QuaternionHalfSpace.quaternionHorizontal p.val) hq
    rw [mobiusStandardElement_smul_val, Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint] at hz
    simp only [ite_eq_right hk, add_zero] at hz
    have hm : ((k : ℂ) - 1) * Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val = 0 := by linear_combination hz
    exact (mul_eq_zero.mp hm).resolve_left (sub_ne_zero.mpr hk)
  · intro hz
    apply Subtype.ext
    rw [mobiusStandardElement_smul_val]
    simp only [show Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val = 0 from hz, mul_zero, ite_eq_right hk,
      add_zero, hkn, one_mul]
    simpa only [show Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val = 0 from hz] using
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates q.val

/-- A point on the actual positive vertical ray. -/
def mobiusVerticalPoint (t : ℝ) (ht : 0 < t) : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
  ⟨Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 t, ht⟩

/-- The vertical ray agrees exactly with the native ambient half-space model. -/
theorem mobiusVerticalPoint_hyperbolic (t : ℝ) (ht : 0 < t) :
    upperHalfSpaceHyperbolicHomeomorph (mobiusVerticalPoint t ht) = Hyperbolic.verticalPoint 2 t ht := by
  apply Subtype.ext
  rw [upperHalfSpaceHyperbolicHomeomorph_val]
  apply Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.injective
  rw [Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply]
  apply Subtype.ext
  apply Quaternion.ext <;>
    simp [mobiusVerticalPoint, Hyperbolic.QuaternionHalfSpace.quaternionThreePoint,
      Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion,
      Hyperbolic.verticalPoint, Hyperbolic.verticalUnitVector, EuclideanSpace.single]

/-- Exponential height is an actual unit-speed complete geodesic parameter. -/
def mobiusVerticalLogParam (s : ℝ) : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
  mobiusVerticalPoint (Real.exp s) (Real.exp_pos s)

theorem mobiusVerticalLogParam_pathDist (s t : ℝ) :
    upperHalfSpacePathDist (mobiusVerticalLogParam s) (mobiusVerticalLogParam t) = dist s t := by
  unfold upperHalfSpacePathDist mobiusVerticalLogParam
  rw [mobiusVerticalPoint_hyperbolic, mobiusVerticalPoint_hyperbolic,
    Hyperbolic.verticalPoint_exp_pathDist, Real.dist_eq, abs_sub_comm]

theorem mobiusVerticalLogParam_range :
    Set.range mobiusVerticalLogParam = {q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace |
      Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val = 0} := by
  ext q
  constructor
  · rintro ⟨s, rfl⟩
    exact Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint 0 (Real.exp s)
  · intro hq
    refine ⟨Real.log (Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val), ?_⟩
    apply Subtype.ext
    change Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 (Real.exp (Real.log
      (Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val))) = q.val
    rw [Real.exp_log q.property]
    simpa only [show Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val = 0 from hq] using
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates q.val

/-- Every actual elliptic axis is the range of a complete unit-speed geodesic in the original length metric. -/
theorem MobiusElliptic.axis_metric_param {f : complexMobiusGroup} (hf : MobiusElliptic f) :
    ∃ γ : ℝ → Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, Set.range γ = mobiusAxis f ∧
      ∀ s t, upperHalfSpacePathDist (γ s) (γ t) = dist s t := by
  obtain ⟨k, hk, hkn, hc⟩ := (mobiusElliptic_iff_conjugate_standard f).mp hf
  obtain ⟨q, rfl⟩ := isConj_iff.mp hc.symm
  refine ⟨fun s => q • mobiusVerticalLogParam s, ?_, ?_⟩
  · rw [mobiusAxis_conjugation, mobiusStandardElement_axis k hk hkn,
      ← mobiusVerticalLogParam_range]
    exact Set.range_comp (fun p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => q • p) mobiusVerticalLogParam
  · intro s t
    rw [upperHalfSpacePathDist_smul, mobiusVerticalLogParam_pathDist]


/-- The actual boundary fixed set of a geometric Möbius transformation. -/
def mobiusBoundaryFixedPoints (f : complexMobiusGroup) : Set ExtendedComplex :=
  Function.fixedPoints f.val

/-- Every actual nonidentity Möbius map has a boundary fixed point. -/
theorem mobius_nonidentity_has_boundary_fixed (f : complexMobiusGroup) (hf : f ≠ 1) :
    ∃ a : ExtendedComplex, f.val a = a := by
  rcases mobius_nonidentity_fixedPoint_dichotomy f hf with ⟨a, ha⟩ | ⟨a, b, _, hab⟩
  · exact ⟨a, (ha a).mpr rfl⟩
  · exact ⟨a, (hab a).mpr (Or.inl rfl)⟩

/-- Three distinct actual boundary fixed points force a Möbius transformation to be identity. -/
theorem mobius_eq_one_of_three_fixed (f : complexMobiusGroup) (a b c : ExtendedComplex)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : f.val a = a) (hb : f.val b = b) (hc : f.val c = c) : f = 1 := by
  by_contra hf
  rcases mobius_nonidentity_fixedPoint_dichotomy f hf with ⟨w, hw⟩ | ⟨u, v, _, huv⟩
  · exact hab (((hw a).mp ha).trans ((hw b).mp hb).symm)
  · rcases (huv a).mp ha with ha' | ha'
    · rcases (huv b).mp hb with hb' | hb'
      · exact hab (ha'.trans hb'.symm)
      · rcases (huv c).mp hc with hc' | hc'
        · exact hac (ha'.trans hc'.symm)
        · exact hbc (hb'.trans hc'.symm)
    · rcases (huv b).mp hb with hb' | hb'
      · rcases (huv c).mp hc with hc' | hc'
        · exact hbc (hb'.trans hc'.symm)
        · exact hac (ha'.trans hc'.symm)
      · exact hab (ha'.trans hb'.symm)

/-- A Möbius transformation exchanging two distinct boundary points is an involution. -/
theorem mobius_sq_eq_one_of_swaps (f : complexMobiusGroup) (a b : ExtendedComplex)
    (hab : a ≠ b) (ha : f.val a = b) (hb : f.val b = a) : f ^ 2 = 1 := by
  have hf : f ≠ 1 := by
    intro he
    subst f
    exact hab ha
  obtain ⟨c, hc⟩ := mobius_nonidentity_has_boundary_fixed f hf
  have hac : a ≠ c := by intro h; exact hab (by simpa only [h, hc] using ha)
  have hbc : b ≠ c := by intro h; exact hab (by simpa only [h, hc] using hb.symm)
  apply mobius_eq_one_of_three_fixed (f ^ 2) a b c hab hac hbc
  · change f.val (f.val a) = a
    rw [ha, hb]
  · change f.val (f.val b) = b
    rw [hb, ha]
  · change f.val (f.val c) = c
    rw [hc, hc]

/-- Mutual preservation uses the actual full boundary fixed sets. -/
def MobiusMutuallyPreservesFixedPoints (f g : complexMobiusGroup) : Prop :=
  g.val '' mobiusBoundaryFixedPoints f = mobiusBoundaryFixedPoints f ∧
    f.val '' mobiusBoundaryFixedPoints g = mobiusBoundaryFixedPoints g

/-- Commuting actual Möbius transformations preserve one another's entire boundary fixed sets. -/
theorem mobius_commute_preserves_fixedPoints {f g : complexMobiusGroup} (h : Commute f g) :
    g.val '' mobiusBoundaryFixedPoints f = mobiusBoundaryFixedPoints f := by
  have hc (z : ExtendedComplex) : f.val (g.val z) = g.val (f.val z) := by
    have hh := congrArg (fun k : complexMobiusGroup => k.val z) h.eq
    exact hh
  apply (g.val.eq_preimage_iff_image_eq _ _).mp
  ext z
  change f.val z = z ↔ f.val (g.val z) = g.val z
  constructor
  · intro hz
    rw [hc, hz]
  · intro hz
    apply g.val.injective
    rw [← hc, hz]

/-- The first implication holds for the genuine Möbius group. -/
theorem mobius_commute_mutually_preserves {f g : complexMobiusGroup} (h : Commute f g) :
    MobiusMutuallyPreservesFixedPoints f g :=
  ⟨mobius_commute_preserves_fixedPoints h, mobius_commute_preserves_fixedPoints h.symm⟩

/-- A preserved nonidentity fixed set containing a point moved by its preserver is exactly that point and its image. -/
theorem mobius_preserved_fixed_pair (f g : complexMobiusGroup) (hf : f ≠ 1)
    (hpres : g.val '' mobiusBoundaryFixedPoints f = mobiusBoundaryFixedPoints f)
    (w : ExtendedComplex) (hw : f.val w = w) (hgw : g.val w ≠ w) :
    g.val (g.val w) = w ∧
      ∀ x : ExtendedComplex, f.val x = x ↔ x = w ∨ x = g.val w := by
  have hmap (x : ExtendedComplex) (hx : f.val x = x) : f.val (g.val x) = g.val x := by
    have hm : g.val x ∈ g.val '' mobiusBoundaryFixedPoints f := ⟨x, hx, rfl⟩
    rw [hpres] at hm
    exact hm
  have hwg := hmap w hw
  have hpair : ∀ x : ExtendedComplex, f.val x = x ↔ x = w ∨ x = g.val w := by
    intro x
    constructor
    · intro hx
      by_contra hn
      have hxw : x ≠ w := fun he => hn (Or.inl he)
      have hxg : x ≠ g.val w := fun he => hn (Or.inr he)
      exact hf (mobius_eq_one_of_three_fixed f w (g.val w) x hgw.symm hxw.symm hxg.symm hw hwg hx)
    · rintro (rfl | rfl)
      · exact hw
      · exact hwg
  refine ⟨?_, hpair⟩
  rcases (hpair (g.val (g.val w))).mp (hmap _ hwg) with he | he
  · exact he
  · exact False.elim (hgw (g.val.injective he))

/-- The three involution relations imply actual commutation. -/
theorem mobius_commute_of_involutions (f g : complexMobiusGroup)
    (hf : f ^ 2 = 1) (hg : g ^ 2 = 1) (hfg : (f * g) ^ 2 = 1) : Commute f g := by
  have hfi : f⁻¹ = f := (eq_inv_iff_mul_eq_one.mpr (by simpa only [pow_two] using hf)).symm
  have hgi : g⁻¹ = g := (eq_inv_iff_mul_eq_one.mpr (by simpa only [pow_two] using hg)).symm
  have hfgi : (f * g)⁻¹ = f * g :=
    (eq_inv_iff_mul_eq_one.mpr (by simpa only [pow_two] using hfg)).symm
  change f * g = g * f
  calc
    f * g = (f * g)⁻¹ := hfgi.symm
    _ = g⁻¹ * f⁻¹ := mul_inv_rev f g
    _ = g * f := by rw [hfi, hgi]

/-- Two involutions with involutive product generate an explicit subgroup of at most four elements. -/
def mobiusInvolutionPairSubgroup (f g : complexMobiusGroup)
    (hf : f ^ 2 = 1) (hg : g ^ 2 = 1) (hfg : (f * g) ^ 2 = 1) :
    Subgroup complexMobiusGroup := by
  have hc := (mobius_commute_of_involutions f g hf hg hfg).eq
  have hff : f * f = 1 := by simpa only [pow_two] using hf
  have hgg : g * g = 1 := by simpa only [pow_two] using hg
  have hfgfg : (f * g) * (f * g) = 1 := by simpa only [pow_two] using hfg
  have hffg : f * (f * g) = g := by rw [← mul_assoc, hff, one_mul]
  have hfgg : (f * g) * g = f := by rw [mul_assoc, hgg, mul_one]
  have hgfg : g * (f * g) = f := by rw [← mul_assoc, ← hc, hfgg]
  have hfgf : (f * g) * f = g := by rw [hc, mul_assoc, hff, mul_one]
  have hfi : f⁻¹ = f := (eq_inv_iff_mul_eq_one.mpr hff).symm
  have hgi : g⁻¹ = g := (eq_inv_iff_mul_eq_one.mpr hgg).symm
  have hfgi : (f * g)⁻¹ = f * g := (eq_inv_iff_mul_eq_one.mpr hfgfg).symm
  exact {
    carrier := {x | x = 1 ∨ x = f ∨ x = g ∨ x = f * g}
    one_mem' := Or.inl rfl
    mul_mem' := by
      intro x y hx hy
      change x = 1 ∨ x = f ∨ x = g ∨ x = f * g at hx
      change y = 1 ∨ y = f ∨ y = g ∨ y = f * g at hy
      change x * y = 1 ∨ x * y = f ∨ x * y = g ∨ x * y = f * g
      rcases hx with rfl | rfl | rfl | rfl <;>
        rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [one_mul, mul_one, hff, hgg, hffg, hfgg, hgfg, hfgf, hfgfg, ← hc] <;>
        simp
    inv_mem' := by
      intro x hx
      change x = 1 ∨ x = f ∨ x = g ∨ x = f * g at hx
      change x⁻¹ = 1 ∨ x⁻¹ = f ∨ x⁻¹ = g ∨ x⁻¹ = f * g
      rcases hx with rfl | rfl | rfl | rfl <;> simp only [inv_one, hfi, hgi, hfgi] <;> simp }

/-- The genuine involution-pair subgroup is finite, so the finite-group fixed-point theorem applies. -/
theorem mobius_involutions_common_H3_fixed (f g : complexMobiusGroup)
    (hf : f ^ 2 = 1) (hg : g ^ 2 = 1) (hfg : (f * g) ^ 2 = 1) :
    ∃ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, f • q = q ∧ g • q = q := by
  let G := mobiusInvolutionPairSubgroup f g hf hg hfg
  have hfinite : (G : Set complexMobiusGroup).Finite := by
    apply Set.Finite.subset ((((Set.finite_singleton (f * g)).insert g).insert f).insert 1)
    intro x hx
    change x = 1 ∨ x = f ∨ x = g ∨ x = f * g at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp
  let := hfinite.fintype
  obtain ⟨q, hq⟩ := mobius_finite_subgroup_common_H3_fixed G
  refine ⟨q, hq f ?_, hq g ?_⟩
  · change f = 1 ∨ f = f ∨ f = g ∨ f = f * g
    exact Or.inr (Or.inl rfl)
  · change g = 1 ∨ g = f ∨ g = g ∨ g = f * g
    exact Or.inr (Or.inr (Or.inl rfl))

/-- Mutual preservation with one fixed point moved by the other map forces the full disjoint involution configuration. -/
theorem mobius_mutual_preservation_involution_configuration (f g : complexMobiusGroup)
    (hf : f ≠ 1) (hg : g ≠ 1) (hpres : MobiusMutuallyPreservesFixedPoints f g)
    (w : ExtendedComplex) (hw : f.val w = w) (hgw : g.val w ≠ w) :
    f ^ 2 = 1 ∧ g ^ 2 = 1 ∧ (f * g) ^ 2 = 1 ∧
      Disjoint (mobiusBoundaryFixedPoints f) (mobiusBoundaryFixedPoints g) := by
  obtain ⟨hggw, hpair⟩ := mobius_preserved_fixed_pair f g hf hpres.1 w hw hgw
  have hfgw : f.val (g.val w) = g.val w := (hpair _).mpr (Or.inr rfl)
  have hdis : Disjoint (mobiusBoundaryFixedPoints f) (mobiusBoundaryFixedPoints g) := by
    apply Set.disjoint_left.mpr
    intro x hxf hxg
    rcases (hpair x).mp hxf with he | he
    · subst x
      exact hgw hxg
    · subst x
      exact hgw (hxg.symm.trans hggw)
  have hg2 := mobius_sq_eq_one_of_swaps g w (g.val w) hgw.symm rfl hggw
  have hfg2 : (f * g) ^ 2 = 1 := by
    apply mobius_sq_eq_one_of_swaps (f * g) w (g.val w) hgw.symm
    · exact hfgw
    · change f.val (g.val (g.val w)) = w
      rw [hggw, hw]
  obtain ⟨c, hc⟩ := mobius_nonidentity_has_boundary_fixed g hg
  have hfc : f.val c ≠ c := by
    intro h
    exact Set.disjoint_left.mp hdis h hc
  have hffcc := (mobius_preserved_fixed_pair g f hg hpres.2 c hc hfc).1
  have hwc : w ≠ c := by intro he; exact hfc (he ▸ hw)
  have hgwc : g.val w ≠ c := by intro he; exact hfc (he ▸ hfgw)
  have hf2 : f ^ 2 = 1 := by
    apply mobius_eq_one_of_three_fixed (f ^ 2) w (g.val w) c hgw.symm hwc hgwc
    · change f.val (f.val w) = w
      rw [hw, hw]
    · change f.val (f.val (g.val w)) = g.val w
      rw [hfgw, hfgw]
    · exact hffcc
  exact ⟨hf2, hg2, hfg2, hdis⟩

/-- The actual geometric alternatives. -/
def MobiusCommutativityConfiguration (f g : complexMobiusGroup) : Prop :=
  MobiusSameFixedPoints f g ∨
    (∃ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, f • q = q ∧ g • q = q) ∧
      f ^ 2 = 1 ∧ g ^ 2 = 1 ∧ (f * g) ^ 2 = 1 ∧
        Disjoint (mobiusBoundaryFixedPoints f) (mobiusBoundaryFixedPoints g)

/-- For nonidentity maps, equality of the full boundary fixed sets implies commutation. -/
theorem mobius_commute_of_same_fixedPoints (f g : complexMobiusGroup)
    (hf : f ≠ 1) (hg : g ≠ 1) (hs : MobiusSameFixedPoints f g) : Commute f g := by
  obtain ⟨a, ha⟩ := mobius_nonidentity_has_boundary_fixed f hf
  have hcommon : MobiusCommonFixedPoint f g := ⟨a, ha, (hs a).mp ha⟩
  rcases mobius_commonFixedPoint_commutator_dichotomy f g hf hg hcommon with ⟨_, hc, _⟩ | ⟨_, _, hn⟩
  · exact hc
  · exact False.elim (hn hs)

/-- The actual geometric alternatives of imply commutation. -/
theorem mobius_configuration_commute (f g : complexMobiusGroup)
    (hf : f ≠ 1) (hg : g ≠ 1) (h : MobiusCommutativityConfiguration f g) : Commute f g := by
  rcases h with hs | ⟨_, hf2, hg2, hfg2, _⟩
  · exact mobius_commute_of_same_fixedPoints f g hf hg hs
  · exact mobius_commute_of_involutions f g hf2 hg2 hfg2

/-- Mutual preservation forces exactly the equal-fixed-set or true common-interior-point involution alternatives. -/
theorem mobius_mutual_preservation_configuration (f g : complexMobiusGroup)
    (hf : f ≠ 1) (hg : g ≠ 1) (h : MobiusMutuallyPreservesFixedPoints f g) :
    MobiusCommutativityConfiguration f g := by
  classical
  by_cases hs : MobiusSameFixedPoints f g
  · exact Or.inl hs
  · right
    have hrel : f ^ 2 = 1 ∧ g ^ 2 = 1 ∧ (f * g) ^ 2 = 1 ∧
        Disjoint (mobiusBoundaryFixedPoints f) (mobiusBoundaryFixedPoints g) := by
      by_cases hex : ∃ w : ExtendedComplex, f.val w = w ∧ g.val w ≠ w
      · obtain ⟨w, hw, hgw⟩ := hex
        exact mobius_mutual_preservation_involution_configuration f g hf hg h w hw hgw
      · have hex' : ∃ w : ExtendedComplex, g.val w = w ∧ f.val w ≠ w := by
          by_contra hn
          apply hs
          intro z
          constructor
          · intro hz
            by_contra hgz
            exact hex ⟨z, hz, hgz⟩
          · intro hz
            by_contra hfz
            exact hn ⟨z, hz, hfz⟩
        obtain ⟨w, hw, hfw⟩ := hex'
        obtain ⟨hg2, hf2, hgf2, hdis⟩ :=
          mobius_mutual_preservation_involution_configuration g f hg hf ⟨h.2, h.1⟩ w hw hfw
        have hc := (mobius_commute_of_involutions g f hg2 hf2 hgf2).eq
        refine ⟨hf2, hg2, ?_, hdis.symm⟩
        rw [← hc]
        exact hgf2
    exact ⟨mobius_involutions_common_H3_fixed f g hrel.1 hrel.2.1 hrel.2.2.1, hrel⟩

/-- All three actual commutativity, fixed-set, and geometric criteria are equivalent. -/
theorem mobius_commute_iff_preserves_fixed_points_and_configuration (f g : complexMobiusGroup) (hf : f ≠ 1) (hg :
    g ≠ 1) :
    (Commute f g ↔ MobiusMutuallyPreservesFixedPoints f g) ∧
      (Commute f g ↔ MobiusCommutativityConfiguration f g) := by
  refine ⟨⟨mobius_commute_mutually_preserves, ?_⟩, ⟨?_, mobius_configuration_commute f g hf hg⟩⟩
  · intro h
    exact mobius_configuration_commute f g hf hg (mobius_mutual_preservation_configuration f g hf hg h)
  · intro h
    exact mobius_mutual_preservation_configuration f g hf hg (mobius_commute_mutually_preserves h)


/-- In the conjugate-diagonal normalization, ellipticity bounds the real diagonal strictly. -/
theorem specialLinear_elliptic_real_diagonal_sq_lt (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : MobiusElliptic (mobiusSpecialLinearProjection A))
    (hAd : A 1 1 = conj (A 0 0)) : (A 0 0).re ^ 2 < 1 := by
  obtain ⟨r, _, hr, ht⟩ := (mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four _ hA.1).mp hA
  rw [mobiusSquaredTrace_specialLinearProjection, Matrix.trace_fin_two, hAd] at ht
  have he := congrArg Complex.re ht
  simp only [pow_two, Complex.mul_re, Complex.add_re, Complex.conj_re, Complex.add_im,
    Complex.conj_im, Complex.ofReal_re] at he
  nlinarith

/-- A finite fixed point lies on the normalized real line through the standard pair. -/
theorem specialLinear_elliptic_fixed_line (A : Auxiliary.Algebra.SpecialLinear2)
    (hAd : A 1 1 = conj (A 0 0)) (ha : (A 0 0).re ^ 2 < 1) (z : ℂ)
    (hfix : (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) z = z) :
    inner ℝ z (conj (A 1 0)) = 0 := by
  change fractionalLinear (Matrix.SpecialLinearGroup.toGL A) z = z at hfix
  have hf := (Mobius.Classification.fractionalLinear_fixed_coe_iff _ z).mp hfix
  change A 1 0 * (z * z) + (A 1 1 - A 0 0) * z + (-A 0 1) = 0 at hf
  have hp : (A 1 0 * z) ^ 2 + (A 1 1 - A 0 0) * (A 1 0 * z) - A 0 1 * A 1 0 = 0 := by
    linear_combination A 1 0 * hf
  have hd := A.det_coe
  rw [Matrix.det_fin_two, hAd, Complex.mul_conj] at hd
  have hprod : A 0 1 * A 1 0 = ((Complex.normSq (A 0 0) - 1 : ℝ) : ℂ) := by
    push_cast
    linear_combination -hd
  rw [hAd, hprod] at hp
  let w := A 1 0 * z
  change w ^ 2 + (conj (A 0 0) - A 0 0) * w -
    ((Complex.normSq (A 0 0) - 1 : ℝ) : ℂ) = 0 at hp
  have hre := congrArg Complex.re hp
  have him := congrArg Complex.im hp
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.zero_re, Complex.zero_im, Complex.normSq_apply] at hre him
  have hw : w.re = 0 := by
    by_contra hwr
    have hm : w.re * (w.im - (A 0 0).im) = 0 := by nlinarith
    have hi : w.im = (A 0 0).im := sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hwr)
    rw [hi] at hre
    nlinarith [sq_nonneg w.re]
  simpa only [w, Complex.mul_re, Complex.inner, Complex.conj_re, Complex.conj_im,
    neg_mul, sub_neg_eq_add, mul_neg, neg_neg, mul_comm] using hw
/-- Conjugacy transports the actual boundary fixed-point equation. -/
theorem mobius_conjugate_boundary_fixed_iff (f q : complexMobiusGroup) (z : ExtendedComplex) :
    (q * f * q⁻¹).val z = z ↔ f.val (q.val.symm z) = q.val.symm z := by
  change q.val (f.val (q.val.symm z)) = z ↔ _
  constructor
  · intro h
    have hh := congrArg q.val.symm h
    simpa only [Equiv.symm_apply_apply] using hh
  · intro h
    rw [h, Equiv.apply_symm_apply]

/-- The normalized fixed pair lies on one genuine line through the standard endpoints. -/
theorem specialLinear_elliptic_fixed_circle (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : MobiusElliptic (mobiusSpecialLinearProjection A))
    (hAd : A 1 1 = conj (A 0 0)) :
    ∃ S : Set ExtendedComplex, IsComplexGeneralizedCircle S ∧
      ((0 : ℂ) : ExtendedComplex) ∈ S ∧ ∞ ∈ S ∧
      ∀ z, (mobiusSpecialLinearProjection A).val z = z → z ∈ S := by
  have ha := specialLinear_elliptic_real_diagonal_sq_lt A hA hAd
  by_cases hc : A 1 0 = 0
  · by_cases hb : A 0 1 = 0
    · have hd := A.det_coe
      rw [Matrix.det_fin_two, hAd, hb, hc, mul_zero, sub_zero, Complex.mul_conj] at hd
      have hn : Complex.normSq (A 0 0) = 1 := by exact_mod_cast hd
      have hi : (A 0 0).im ≠ 0 := by
        intro hi
        rw [Complex.normSq_apply, hi, mul_zero, add_zero] at hn
        nlinarith
      have hdiff : A 1 1 - A 0 0 ≠ 0 := by
        intro he
        have hz := congrArg Complex.im (sub_eq_zero.mp he)
        rw [hAd, Complex.conj_im] at hz
        apply hi
        linarith
      refine ⟨complexRealAxis, complexRealAxis_isGeneralized, by simp, complexRealAxis_infty, ?_⟩
      intro z hz
      induction z using OnePoint.rec with
      | infty => exact complexRealAxis_infty
      | coe z =>
        change fractionalLinear (Matrix.SpecialLinearGroup.toGL A) z = z at hz
        have hf := (Mobius.Classification.fractionalLinear_fixed_coe_iff _ z).mp hz
        change A 1 0 * (z * z) + (A 1 1 - A 0 0) * z + (-A 0 1) = 0 at hf
        rw [hc, hb, zero_mul, zero_add, neg_zero, add_zero] at hf
        have hz0 := (mul_eq_zero.mp hf).resolve_left hdiff
        simp [hz0]
    · refine ⟨complexLine (A 0 1) 0, complexLine_isGeneralized _ _ hb,
        by simp, complexLine_infty _ _, ?_⟩
      intro z hz
      induction z using OnePoint.rec with
      | infty => exact complexLine_infty _ _
      | coe z =>
        rw [complexLine_coe]
        change fractionalLinear (Matrix.SpecialLinearGroup.toGL A) z = z at hz
        have hf := (Mobius.Classification.fractionalLinear_fixed_coe_iff _ z).mp hz
        change A 1 0 * (z * z) + (A 1 1 - A 0 0) * z + (-A 0 1) = 0 at hf
        rw [hc, zero_mul, zero_add, hAd] at hf
        have hre := congrArg Complex.re hf
        have him := congrArg Complex.im hf
        simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
          Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
          Complex.neg_re, Complex.neg_im, Complex.zero_re, Complex.zero_im] at hre him
        simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im]
        linear_combination -z.re * hre - z.im * him
  · refine ⟨complexLine (conj (A 1 0)) 0,
      complexLine_isGeneralized _ _ ((map_ne_zero (starRingEnd ℂ)).mpr hc),
      by simp, complexLine_infty _ _, ?_⟩
    intro z hz
    induction z using OnePoint.rec with
    | infty => exact complexLine_infty _ _
    | coe z => exact (complexLine_coe _ z 0).mpr (specialLinear_elliptic_fixed_line A hAd ha z hz)

/-- first assertion: all boundary fixed points of g and h lie on one genuine generalized circle. -/
theorem elliptic_pair_fixed_points_concyclic_of_product_elliptic (f g : complexMobiusGroup)
    (hf : MobiusElliptic f) (hg : MobiusElliptic g) (hfg : MobiusElliptic (f * g)) :
    ∃ S : Set ExtendedComplex, IsComplexGeneralizedCircle S ∧
      ∀ z, f.val z = z ∨ g.val z = z → z ∈ S := by
  obtain ⟨k, hk, hkn, hconj⟩ := (mobiusElliptic_iff_conjugate_standard f).mp hf
  obtain ⟨q, hq⟩ := isConj_iff.mp hconj
  obtain ⟨R, hR, hR01, hR10, hRd, hRi⟩ := unit_standard_specialLinear_diagonal k hk hkn
  obtain ⟨A, hA⟩ := mobiusSpecialLinearProjection_surjective (q * g * q⁻¹)
  have hAE : MobiusElliptic (mobiusSpecialLinearProjection A) := by
    rw [hA]
    exact (mobiusElliptic_conjugation g q).mpr hg
  have hRAE : MobiusElliptic (mobiusSpecialLinearProjection (R * A)) := by
    rw [map_mul, hR, hA, ← hq]
    simpa only [mul_assoc, inv_mul_cancel_left] using (mobiusElliptic_conjugation (f * g) q).mpr hfg
  have hAd := specialLinear_real_traces_conjugate_diagonal R A hR01 hR10 hRd hRi
    (specialLinear_elliptic_or_identity_trace A (Or.inr hAE)).1
    (specialLinear_elliptic_or_identity_trace (R * A) (Or.inr hRAE)).1
  obtain ⟨S, hS, hS0, hSi, hAS⟩ := specialLinear_elliptic_fixed_circle A hAE hAd
  refine ⟨q.val.symm '' S, hS.image (q⁻¹).property.1, ?_⟩
  intro z hz
  refine ⟨q.val z, ?_, q.val.symm_apply_apply z⟩
  rcases hz with hz | hz
  · have hfix : (mobiusStandardElement k).val (q.val z) = q.val z := by
      rw [← hq, mobius_conjugate_boundary_fixed_iff]
      simpa only [Equiv.symm_apply_apply] using hz
    rcases (mobiusStandardElement_boundary_fixed_iff k hk _).mp hfix with he | he
    · exact he ▸ hS0
    · exact he ▸ hSi
  · apply hAS
    rw [hA, mobius_conjugate_boundary_fixed_iff]
    simpa only [Equiv.symm_apply_apply] using hz
/-- The commutator trace bound in forces a nonpositive determinant defect. -/
theorem specialLinear_elliptic_commutator_diagonal_bound (R A : Auxiliary.Algebra.SpecialLinear2)
    (hR01 : R 0 1 = 0) (hR10 : R 1 0 = 0) (hRd : R 1 1 = conj (R 0 0))
    (hRi : (R 0 0).im ≠ 0) (hAd : A 1 1 = conj (A 0 0))
    (hC : mobiusSpecialLinearProjection (Mobius.Classification.specialCommutator R A) = 1 ∨
      MobiusElliptic (mobiusSpecialLinearProjection (Mobius.Classification.specialCommutator R A))) :
    Complex.normSq (A 0 0) ≤ 1 := by
  have ht := (specialLinear_elliptic_or_identity_trace (Mobius.Classification.specialCommutator R A) hC).2.2
  rw [specialLinear_diagonal_commutator_trace_re R A hR01 hR10 hRd] at ht
  have hs : 0 < 4 * (R 0 0).im ^ 2 := mul_pos (by norm_num) (sq_pos_of_ne_zero hRi)
  have hprod : (A 1 0 * A 0 1).re ≤ 0 := by
    by_contra hp
    have hm := mul_pos hs (lt_of_not_ge hp)
    linarith
  have hd := congrArg Complex.re A.det_coe
  rw [Matrix.det_fin_two, hAd, Complex.mul_conj] at hd
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re] at hd
  rw [mul_comm (A 0 1) (A 1 0)] at hd
  linarith

/-- The parabolic commutator case is excluded by the elliptic-or-identity hypothesis. -/
theorem specialLinear_elliptic_commutator_trace_two (R A : Auxiliary.Algebra.SpecialLinear2)
    (hC : mobiusSpecialLinearProjection (Mobius.Classification.specialCommutator R A) = 1 ∨
      MobiusElliptic (mobiusSpecialLinearProjection (Mobius.Classification.specialCommutator R A)))
    (ht : Matrix.trace (Mobius.Classification.specialCommutator R A : Auxiliary.Algebra.ComplexMatrix2) = 2) :
    Mobius.Classification.specialCommutator R A = 1 := by
  let C := Mobius.Classification.specialCommutator R A
  have hproj : mobiusSpecialLinearProjection C = 1 := by
    rcases hC with he | he
    · exact he
    · obtain ⟨r, _, hr, hh⟩ := (mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four _ he.1).mp he
      rw [mobiusSquaredTrace_specialLinearProjection, ht] at hh
      have hreal := congrArg Complex.re hh
      norm_num at hreal
      linarith
  apply Subtype.ext
  rcases (mobiusSpecialLinearProjection_eq_one_iff C).mp hproj with h | h
  · exact h
  · change Matrix.trace (C : Auxiliary.Algebra.ComplexMatrix2) = 2 at ht
    rw [h, Matrix.trace_fin_two] at ht
    norm_num at ht

/-- A vanishing off-diagonal entry in the pair lemma forces both to vanish. -/
theorem specialLinear_elliptic_commutator_offDiagonal_zero (R A : Auxiliary.Algebra.SpecialLinear2)
    (hR01 : R 0 1 = 0) (hR10 : R 1 0 = 0) (hRd : R 1 1 = conj (R 0 0))
    (hRi : (R 0 0).im ≠ 0)
    (hC : mobiusSpecialLinearProjection (Mobius.Classification.specialCommutator R A) = 1 ∨
      MobiusElliptic (mobiusSpecialLinearProjection (Mobius.Classification.specialCommutator R A)))
    (hz : A 0 1 = 0 ∨ A 1 0 = 0) : A 0 1 = 0 ∧ A 1 0 = 0 := by
  have ht : Matrix.trace (Mobius.Classification.specialCommutator R A : Auxiliary.Algebra.ComplexMatrix2) = 2 := by
    rw [Mobius.Classification.specialCommutator_trace_triangular R A hR10, hR01]
    rcases hz with hb | hc
    · simp [hb]
    · simp [hc]
  have hCid := specialLinear_elliptic_commutator_trace_two R A hC ht
  have hcomm : Commute R A := by
    change R * A = A * R
    change R * A * R⁻¹ * A⁻¹ = 1 at hCid
    have hh : R * A * R⁻¹ = A := by
      simpa only [one_mul] using (mul_inv_eq_iff_eq_mul.mp hCid)
    exact mul_inv_eq_iff_eq_mul.mp hh
  exact specialLinear_commuting_diagonal_offDiagonal_zero R A hR01 hR10 hRd hRi hcomm

/-- The matrix hypotheses of produce a common actual vertical point without any group-wide ellipticity assumption. -/
theorem specialLinear_elliptic_pair_vertical_fixed (R A : Auxiliary.Algebra.SpecialLinear2)
    (hR01 : R 0 1 = 0) (hR10 : R 1 0 = 0) (hRd : R 1 1 = conj (R 0 0))
    (hRi : (R 0 0).im ≠ 0) (hA : MobiusElliptic (mobiusSpecialLinearProjection A))
    (hRA : MobiusElliptic (mobiusSpecialLinearProjection (R * A)))
    (hC : mobiusSpecialLinearProjection (Mobius.Classification.specialCommutator R A) = 1 ∨
      MobiusElliptic (mobiusSpecialLinearProjection (Mobius.Classification.specialCommutator R A))) :
    ∃ p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, mobiusSpecialLinearProjection R • p = p ∧
      mobiusSpecialLinearProjection A • p = p := by
  have hAd := specialLinear_real_traces_conjugate_diagonal R A hR01 hR10 hRd hRi
    (specialLinear_elliptic_or_identity_trace A (Or.inr hA)).1
    (specialLinear_elliptic_or_identity_trace (R * A) (Or.inr hRA)).1
  by_cases hc : A 1 0 = 0
  · obtain ⟨hb, _⟩ := specialLinear_elliptic_commutator_offDiagonal_zero R A hR01 hR10 hRd hRi hC (Or.inr hc)
    refine ⟨⟨Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 1, show (0 : ℝ) < 1 from zero_lt_one⟩, ?_, ?_⟩
    · exact specialLinear_vertical_fixed R 1 zero_lt_one hRd (by simp [hR01, hR10])
    · exact specialLinear_vertical_fixed A 1 zero_lt_one hAd (by simp [hb, hc])
  · have hnorm := specialLinear_elliptic_commutator_diagonal_bound R A hR01 hR10 hRd hRi hAd hC
    have hstrict : Complex.normSq (A 0 0) < 1 := by
      apply lt_of_le_of_ne hnorm
      intro he
      have hd := A.det_coe
      rw [Matrix.det_fin_two, hAd, Complex.mul_conj, he, Complex.ofReal_one] at hd
      have hprod : A 0 1 * A 1 0 = 0 := by linear_combination -hd
      have hb := (mul_eq_zero.mp hprod).resolve_right hc
      exact hc (specialLinear_elliptic_commutator_offDiagonal_zero R A hR01 hR10 hRd hRi hC (Or.inl hb)).2
    obtain ⟨t, ht, hb⟩ := specialLinear_positive_vertical_ratio A hAd hstrict hc
    refine ⟨⟨Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 t, ht⟩, ?_, specialLinear_vertical_fixed A t ht
      hAd hb⟩
    exact specialLinear_vertical_fixed R t ht hRd (by simp [hR01, hR10])

/-- second assertion, expressed as intersection of the actual H3 fixed axes. -/
theorem elliptic_axes_intersect_of_product_and_commutator_elliptic (f g : complexMobiusGroup)
    (hf : MobiusElliptic f) (hg : MobiusElliptic g) (hfg : MobiusElliptic (f * g))
    (hcomm : mobiusCommutator f g = 1 ∨ MobiusElliptic (mobiusCommutator f g)) :
    (mobiusAxis f ∩ mobiusAxis g).Nonempty := by
  obtain ⟨k, hk, hkn, hconj⟩ := (mobiusElliptic_iff_conjugate_standard f).mp hf
  obtain ⟨q, hq⟩ := isConj_iff.mp hconj
  obtain ⟨R, hR, hR01, hR10, hRd, hRi⟩ := unit_standard_specialLinear_diagonal k hk hkn
  obtain ⟨A, hA⟩ := mobiusSpecialLinearProjection_surjective (q * g * q⁻¹)
  have hAE : MobiusElliptic (mobiusSpecialLinearProjection A) := by
    rw [hA]
    exact (mobiusElliptic_conjugation g q).mpr hg
  have hRAE : MobiusElliptic (mobiusSpecialLinearProjection (R * A)) := by
    rw [map_mul, hR, hA, ← hq]
    simpa only [mul_assoc, inv_mul_cancel_left] using (mobiusElliptic_conjugation (f * g) q).mpr hfg
  have hCproj : mobiusSpecialLinearProjection (Mobius.Classification.specialCommutator R A) =
      q * mobiusCommutator f g * q⁻¹ := by
    simp only [Mobius.Classification.specialCommutator, map_mul, map_inv, hR, hA, ← hq,
      mobiusCommutator]
    group
  have hCE : mobiusSpecialLinearProjection (Mobius.Classification.specialCommutator R A) = 1 ∨
      MobiusElliptic (mobiusSpecialLinearProjection (Mobius.Classification.specialCommutator R A)) := by
    rw [hCproj]
    rcases hcomm with he | he
    · exact Or.inl (by simp [he])
    · exact Or.inr ((mobiusElliptic_conjugation _ q).mpr he)
  obtain ⟨p, hpR, hpA⟩ := specialLinear_elliptic_pair_vertical_fixed R A hR01 hR10 hRd hRi hAE hRAE hCE
  refine ⟨q⁻¹ • p, ?_, ?_⟩
  · rw [hR, ← hq] at hpR
    have hh := congrArg (fun p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => q⁻¹ • p) hpR
    change f • (q⁻¹ • p) = q⁻¹ • p
    simpa only [mul_smul, inv_smul_smul] using hh
  · rw [hA] at hpA
    have hh := congrArg (fun p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => q⁻¹ • p) hpA
    change g • (q⁻¹ • p) = q⁻¹ • p
    simpa only [mul_smul, inv_smul_smul] using hh


/-- Reflection in the actual zero-height boundary plane, in quaternion coordinates. -/
def mobiusBoundaryReflection : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace ≃ₜ OnePoint
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace :=
  quaternionConjugateHom (Inversive.planeReflectionHomeomorph (Inversive.northPole 2) 0
    (by intro h; have hn := Inversive.norm_northPole 2; rw [h, norm_zero] at hn; norm_num at hn))

@[simp] theorem mobiusBoundaryReflection_infty : mobiusBoundaryReflection ∞ = ∞ := by
  rfl

@[simp] theorem mobiusBoundaryReflection_coe (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    mobiusBoundaryReflection (q : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
      (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q)
        (-Hyperbolic.QuaternionHalfSpace.quaternionHeight q) : OnePoint
        Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) := by
  change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion
    (Inversive.planeReflectionHomeomorph (Inversive.northPole 2) 0 _
      ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q : Inversive.Euclidean 3) :
        Inversive.ExtendedEuclidean 3)) = _
  rw [Inversive.planeReflectionHomeomorph_apply, Inversive.planeReflection_coe]
  change (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion (Inversive.planeReflectionFinite _ _ _) :
    OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) = _
  rw [cayley_plane_reflection_coordinates, Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply]

theorem mobiusBoundaryReflection_involutive : Function.Involutive mobiusBoundaryReflection := by
  intro w
  induction w using OnePoint.rec with
  | infty => rfl
  | coe q =>
    rw [mobiusBoundaryReflection_coe, mobiusBoundaryReflection_coe,
      Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint,
        Hyperbolic.QuaternionHalfSpace.quaternionHeight_threePoint, neg_neg,
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates]

/-- Every genuine Poincare extension commutes with the boundary-plane reflection. -/
theorem mobiusBoundaryReflection_commute (f : complexMobiusGroup) :
    Commute (mobiusExtendedSpaceHom f) mobiusBoundaryReflection := by
  let F := (mobiusGeometricPoincare f : Inversive.ExtendedHomeomorph 3)
  let r := Inversive.planeReflectionHomeomorph (Inversive.northPole 2) 0
    (by intro h; have hn := Inversive.norm_northPole 2; rw [h, norm_zero] at hn; norm_num at hn)
  have hinv : F '' Function.fixedPoints r = Function.fixedPoints r := by
    rw [Inversive.fixedPoints_planeReflection]
    exact preservesNativeBoundary_of_preservesHalfSpace F
      (mobiusGeometricPoincare_preservesHalfSpaces f 1)
  have hc : Commute F r := by
    change F * r = r * F
    apply Homeomorph.ext
    intro z
    exact reflection_commutes_of_invariant_sphere F r (mobiusGeometricPoincare f).property
      (Inversive.planeReflection_isReflection _ _ _) hinv z
  exact hc.map quaternionConjugateHom

/-- Reflection preserves exactly the true full-space fixed set. -/
theorem mobiusBoundaryReflection_fixed_iff (f : complexMobiusGroup) (w : OnePoint
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    mobiusBoundaryReflection w ∈ mobiusExtendedFixedPoints f ↔ w ∈ mobiusExtendedFixedPoints f := by
  have hc := congrArg (fun H : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace ≃ₜ OnePoint
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace => H w)
    (mobiusBoundaryReflection_commute f).eq
  change mobiusExtendedSpaceHom f (mobiusBoundaryReflection w) =
    mobiusBoundaryReflection (mobiusExtendedSpaceHom f w) at hc
  change mobiusExtendedSpaceHom f (mobiusBoundaryReflection w) = mobiusBoundaryReflection w ↔
    mobiusExtendedSpaceHom f w = w
  rw [hc]
  exact mobiusBoundaryReflection.injective.eq_iff

/-- The full actual fixed set consists of the interior axis, its reflected lower-half-space copy, and the boundary fixed set. -/
theorem mobiusExtendedFixedPoints_axis_decomposition (f : complexMobiusGroup) :
    mobiusExtendedFixedPoints f =
      ((fun q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => (q.val : OnePoint
        Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)) '' mobiusAxis f) ∪
      mobiusBoundaryReflection '' ((fun q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => (q.val : OnePoint
        Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)) '' mobiusAxis f) ∪
      Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding '' mobiusBoundaryFixedPoints f := by
  ext w
  constructor
  · intro hw
    induction w using OnePoint.rec with
    | infty =>
      exact Or.inr ⟨∞, (mobiusExtendedFixedPoints_boundary_iff f ∞).mp hw, rfl⟩
    | coe q =>
      rcases lt_trichotomy (Hyperbolic.QuaternionHalfSpace.quaternionHeight q) 0 with ht | ht | ht
      · let p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
          ⟨Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal
          q) (-Hyperbolic.QuaternionHalfSpace.quaternionHeight q), neg_pos.mpr ht⟩
        have he : mobiusBoundaryReflection (p.val : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)
          = (q : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) := by
          rw [mobiusBoundaryReflection_coe, Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint,
            Hyperbolic.QuaternionHalfSpace.quaternionHeight_threePoint, neg_neg,
              Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates]
        have hp : p ∈ mobiusAxis f := by
          apply (mobiusExtendedFixedPoints_interior_iff f p).mp
          apply (mobiusBoundaryReflection_fixed_iff f (p.val : OnePoint
            Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)).mp
          rw [he]
          exact hw
        exact Or.inl (Or.inr ⟨p.val, ⟨p, hp, rfl⟩, he⟩)
      · have he : Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding
          ((Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q : ℂ) : ExtendedComplex) =
            (q : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) := by
          rw [Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding_coe]
          simpa only [ht] using congrArg ((↑) : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace → OnePoint
            Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)
            (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates q)
        refine Or.inr ⟨(Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q : ℂ), ?_, he⟩
        apply (mobiusExtendedFixedPoints_boundary_iff f _).mp
        rw [he]
        exact hw
      · let p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace := ⟨q, ht⟩
        exact Or.inl (Or.inl ⟨p, (mobiusExtendedFixedPoints_interior_iff f p).mp hw, rfl⟩)
  · rintro ((⟨q, hq, rfl⟩ | ⟨w, ⟨q, hq, rfl⟩, rfl⟩) | ⟨z, hz, rfl⟩)
    · exact (mobiusExtendedFixedPoints_interior_iff f q).mpr hq
    · exact (mobiusBoundaryReflection_fixed_iff f _).mpr
        ((mobiusExtendedFixedPoints_interior_iff f q).mpr hq)
    · exact (mobiusExtendedFixedPoints_boundary_iff f z).mpr hz
/-- An elliptic axis is a genuine Euclidean vertical line or boundary-orthogonal semicircle, not merely an abstract metric parameter. -/
theorem MobiusElliptic.axis_native_geodesic {f : complexMobiusGroup} (hf : MobiusElliptic f) :
    Hyperbolic.IsHalfSpaceGeodesicLine 2
      (upperHalfSpaceHyperbolicHomeomorph '' mobiusAxis f) := by
  obtain ⟨γ, hγ, hdist⟩ := hf.axis_metric_param
  have hgeo := Hyperbolic.halfSpace_metric_geodesic_isLine (by norm_num : 1 ≤ 2)
    (fun t => upperHalfSpaceHyperbolicHomeomorph (γ t)) (fun s t => hdist s t)
  change Hyperbolic.IsHalfSpaceGeodesicLine 2
    (Set.range ((upperHalfSpaceHyperbolicHomeomorph : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace →
      Hyperbolic.HyperbolicHalfSpace 2) ∘ γ)) at hgeo
  rw [Set.range_comp, hγ] at hgeo
  exact hgeo

/-- The complete coordinate statement of the source axis shape, with a genuine positive radius and a centre on the zero-height boundary. -/
theorem MobiusElliptic.axis_semicircle_or_vertical {f : complexMobiusGroup} (hf : MobiusElliptic f) :
    (∃ v : Inversive.Euclidean 3, Hyperbolic.halfSpaceHeight 2 v = 0 ∧
      ∀ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, q ∈ mobiusAxis f ↔
        Hyperbolic.halfSpaceHorizontalPart (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val) = v) ∨
    ∃ x u : Inversive.Euclidean 3, ‖u‖ = 1 ∧ Hyperbolic.halfSpaceHeight 2 u = 0 ∧
      ∃ c r : ℝ, 0 < r ∧ ∀ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, q ∈ mobiusAxis f ↔
        Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val ∈ Set.range
          (Hyperbolic.halfSpacePlaneEmbed x u) ∧
        ‖Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val - Hyperbolic.halfSpacePlaneEmbed x u
          (c : ℂ)‖ = r := by
  have hmem (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) : upperHalfSpaceHyperbolicHomeomorph q ∈
      upperHalfSpaceHyperbolicHomeomorph '' mobiusAxis f ↔ q ∈ mobiusAxis f := by
    constructor
    · rintro ⟨p, hp, he⟩
      exact upperHalfSpaceHyperbolicHomeomorph.injective he ▸ hp
    · intro hq
      exact ⟨q, hq, rfl⟩
  rcases hf.axis_native_geodesic with ⟨v, hv, hL⟩ | ⟨x, u, hu, hu0, c, r, hr, hL⟩
  · refine Or.inl ⟨v, hv, ?_⟩
    intro q
    rw [← hmem q, hL]
    rfl
  · refine Or.inr ⟨x, u, hu, hu0, c, r, hr, ?_⟩
    intro q
    rw [← hmem q, hL]
    rfl


/-- A fixed boundary point supplies an eigenvalue of its determinant-one representative. -/
theorem specialLinear_fixed_characteristic (A : Auxiliary.Algebra.SpecialLinear2) (z : ℂ)
    (hz : (mobiusSpecialLinearProjection A).val z = z) :
    (A 1 0 * z + A 1 1) ^ 2 - Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) *
      (A 1 0 * z + A 1 1) + 1 = 0 := by
  change fractionalLinear (Matrix.SpecialLinearGroup.toGL A) z = z at hz
  have hf := (Mobius.Classification.fractionalLinear_fixed_coe_iff _ z).mp hz
  change A 1 0 * (z * z) + (A 1 1 - A 0 0) * z + (-A 0 1) = 0 at hf
  have hd := A.det_coe
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.trace_fin_two]
  linear_combination A 1 0 * hf - hd

/-- The two elliptic characteristic roots have equal real part. -/
theorem specialLinear_elliptic_characteristic_re (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : MobiusElliptic (mobiusSpecialLinearProjection A)) (z : ℂ)
    (hz : z ^ 2 - Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) * z + 1 = 0) :
    z.re = (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).re / 2 := by
  have hti := (specialLinear_elliptic_or_identity_trace A (Or.inr hA)).1
  obtain ⟨r, _, hr, ht⟩ := (mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four _ hA.1).mp hA
  rw [mobiusSquaredTrace_specialLinearProjection] at ht
  have htr := congrArg Complex.re ht
  simp only [pow_two, Complex.mul_re, hti, mul_zero, sub_zero, Complex.ofReal_re] at htr
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_two, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im,
    Complex.zero_re, Complex.zero_im, hti, zero_mul, add_zero, sub_zero] at hre him
  have hzi : z.im ≠ 0 := by
    intro hzi
    rw [hzi, zero_mul, sub_zero] at hre
    nlinarith [sq_nonneg (2 * z.re - (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).re)]
  have hm : (2 * z.re - (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).re) * z.im = 0 := by
    linear_combination him
  have he := (mul_eq_zero.mp hm).resolve_right hzi
  linarith

/-- The literal quaternion fixed equation at a positive vertical height is exactly the weighted unitary entry relation. -/
theorem quaternionMatrixExpression_vertical_fixed_iff (A : Auxiliary.Algebra.ComplexMatrix2) (hA : A.det ≠ 0)
    (t : ℝ) (ht : 0 < t) :
    quaternionMatrixExpression A (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 t) =
      (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 t : ℍ) ↔
      A 1 1 = conj (A 0 0) ∧ A 0 1 = -conj (A 1 0) * (t : ℂ) ^ 2 := by
  have hd := quaternionMatrixDenominator_ne_zero A hA (⟨Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 t,
    ht⟩ : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace)
  rw [quaternionMatrixExpression, mul_inv_eq_iff_eq_mul₀ hd]
  simp only [QuaternionAlgebra.ext_iff, Complex.ext_iff]
  simp [Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, pow_two, Complex.mul_re, Complex.mul_im]
  constructor
  · rintro ⟨hbr, hbi, har, hai⟩
    have hre : (A 0 0).re = (A 1 1).re := by
      apply mul_right_cancel₀ ht.ne'
      linear_combination har
    have him : (A 0 0).im = -(A 1 1).im := by
      apply mul_right_cancel₀ ht.ne'
      linear_combination hai
    exact ⟨⟨by linarith, by linarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
  · rintro ⟨⟨hdr, hdi⟩, ⟨hbr, hbi⟩⟩
    exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith⟩

/-- The actual H3 action fixes a vertical point exactly under the same explicit entry conditions. -/
theorem specialLinear_vertical_fixed_iff (A : Auxiliary.Algebra.SpecialLinear2) (t : ℝ) (ht : 0 < t) :
    mobiusSpecialLinearProjection A • (mobiusVerticalPoint t ht) = mobiusVerticalPoint t ht ↔
      A 1 1 = conj (A 0 0) ∧ A 0 1 = -conj (A 1 0) * (t : ℂ) ^ 2 := by
  constructor
  · intro h
    apply (quaternionMatrixExpression_vertical_fixed_iff (A : Auxiliary.Algebra.ComplexMatrix2) (by simp) t ht).mp
    have hh := congrArg (fun q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => (q.val : ℍ)) h
    rw [mobiusUpperHalfSpace_smul, mobiusPoincareHom_specialLinearProjection] at hh
    change ((poincareSpecialLinearMap A (mobiusVerticalPoint t ht)).val : ℍ) =
      ((mobiusVerticalPoint t ht).val : ℍ) at hh
    rw [poincareSpecialLinearMap_quaternion] at hh
    exact hh
  · rintro ⟨hd, hb⟩
    exact specialLinear_vertical_fixed A t ht hd hb
/-- For an elliptic map fixing one, its other finite fixed point is negative real precisely when its axis meets the actual vertical ray. -/
theorem specialLinear_elliptic_one_second_vertical_iff (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : MobiusElliptic (mobiusSpecialLinearProjection A)) (w : ℂ) (hw1 : w ≠ 1)
    (hc : A 1 0 ≠ 0)
    (h1 : (mobiusSpecialLinearProjection A).val (1 : ℂ) = (1 : ℂ))
    (hw : (mobiusSpecialLinearProjection A).val w = w) :
    (∃ t : ℝ, ∃ ht : 0 < t,
      mobiusSpecialLinearProjection A • mobiusVerticalPoint t ht = mobiusVerticalPoint t ht) ↔
      w.im = 0 ∧ w.re < 0 := by
  have hf1 := (Mobius.Classification.fractionalLinear_fixed_coe_iff (Matrix.SpecialLinearGroup.toGL A) 1).mp h1
  have hfw := (Mobius.Classification.fractionalLinear_fixed_coe_iff (Matrix.SpecialLinearGroup.toGL A) w).mp hw
  change A 1 0 * (1 * 1) + (A 1 1 - A 0 0) * 1 + (-A 0 1) = 0 at hf1
  change A 1 0 * (w * w) + (A 1 1 - A 0 0) * w + (-A 0 1) = 0 at hfw
  have hp : (w - 1) * (A 1 0 * w + A 0 1) = 0 := by
    linear_combination hfw - w * hf1
  have hbw : A 0 1 = -A 1 0 * w := by
    have he := (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hw1)
    linear_combination he
  constructor
  · rintro ⟨t, ht, hfix⟩
    obtain ⟨hAd, hb⟩ := (specialLinear_vertical_fixed_iff A t ht).mp hfix
    have hr := congrArg Complex.re hf1
    rw [hAd, hb] at hr
    simp [pow_two, Complex.mul_re, Complex.mul_im] at hr
    have hcre : (A 1 0).re = 0 := by
      have hm : (A 1 0).re * (1 + t ^ 2) = 0 := by nlinarith
      exact (mul_eq_zero.mp hm).resolve_right (by positivity)
    have hconj : conj (A 1 0) = -A 1 0 := by
      apply Complex.ext <;> simp [hcre]
    rw [hconj, neg_neg] at hb
    have heq : w = -(t : ℂ) ^ 2 := by
      apply mul_left_cancel₀ hc
      linear_combination -hb + hbw
    rw [heq]
    constructor
    · rw [← Complex.ofReal_pow]
      simp only [Complex.neg_im, Complex.ofReal_im, neg_zero]
    · rw [← Complex.ofReal_pow, Complex.neg_re, Complex.ofReal_re]
      nlinarith [sq_pos_of_pos ht]
  · rintro ⟨hwi, hwr⟩
    have hroot1 := specialLinear_elliptic_characteristic_re A hA (A 1 0 * 1 + A 1 1)
      (specialLinear_fixed_characteristic A 1 h1)
    have hrootw := specialLinear_elliptic_characteristic_re A hA (A 1 0 * w + A 1 1)
      (specialLinear_fixed_characteristic A w hw)
    have hcre : (A 1 0).re = 0 := by
      simp only [Complex.add_re, Complex.mul_re,
        hwi, mul_zero, sub_zero, mul_one] at hroot1 hrootw
      have hm : (A 1 0).re * (1 - w.re) = 0 := by nlinarith
      exact (mul_eq_zero.mp hm).resolve_right (by linarith)
    have hbre : (A 0 1).re = 0 := by
      rw [hbw]
      simp [Complex.mul_re, hcre, hwi]
    have hdiag : A 1 1 = conj (A 0 0) := by
      have hre := congrArg Complex.re hf1
      have him := (specialLinear_elliptic_or_identity_trace A (Or.inr hA)).1
      simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, mul_one, hcre, hbre,
        Complex.zero_re] at hre
      simp only [Matrix.trace_fin_two, Complex.add_im] at him
      apply Complex.ext
      · simp only [Complex.conj_re]
        linarith
      · simp only [Complex.conj_im]
        linarith
    let t := Real.sqrt (-w.re)
    have ht : 0 < t := Real.sqrt_pos.mpr (by linarith)
    have ht2 : t ^ 2 = -w.re := Real.sq_sqrt (by linarith)
    have hwcast : w = (w.re : ℂ) := by
      apply Complex.ext <;> simp [hwi]
    have hconj : conj (A 1 0) = -A 1 0 := by
      apply Complex.ext <;> simp [hcre]
    refine ⟨t, ht, (specialLinear_vertical_fixed_iff A t ht).mpr ⟨hdiag, ?_⟩⟩
    rw [hconj, neg_neg, hbw, hwcast]
    rw [← Complex.ofReal_pow, ht2]
    push_cast
    ring

/-- The actual geometric cyclic order in this normalization is exactly a negative real fourth point. -/
theorem complexCyclicOrder_zero_one_infty_iff (w : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ 1) :
    ComplexCyclicOrder (0 : ℂ) (1 : ℂ) ∞ w ↔ w.im = 0 ∧ w.re < 0 := by
  have hd : QuadrupleDistinct ((0 : ℂ) : ExtendedComplex) (1 : ℂ) ∞ w := by
    constructor
    · simp
    · refine ⟨OnePoint.coe_ne_infty _, ?_, OnePoint.coe_ne_infty _, ?_, ?_⟩
      · exact fun h => hw0 (OnePoint.coe_injective h.symm)
      · exact fun h => hw1 (OnePoint.coe_injective h.symm)
      · exact (OnePoint.coe_ne_infty w).symm
  rw [complexCyclicOrder_iff_crossRatio_real_gt_one _ _ _ _ hd, extendedCrossRatio_infty_third]
  simp only [sub_zero, div_one, Complex.sub_im, Complex.sub_re, Complex.one_im,
    Complex.one_re, zero_sub]
  constructor
  · rintro ⟨hi, hr⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hi, hr⟩
    exact ⟨by linarith, by linarith⟩
/-- The actual intersection of interior fixed axes is invariant under conjugation. -/
theorem mobiusAxes_intersect_conjugation (f g q : complexMobiusGroup) :
    (mobiusAxis (q * f * q⁻¹) ∩ mobiusAxis (q * g * q⁻¹)).Nonempty ↔
      (mobiusAxis f ∩ mobiusAxis g).Nonempty := by
  constructor
  · rintro ⟨p, hpf, hpg⟩
    refine ⟨q⁻¹ • p, ?_, ?_⟩
    · have h := congrArg (fun p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => q⁻¹ • p) hpf
      change f • (q⁻¹ • p) = q⁻¹ • p
      simpa only [mul_smul, inv_smul_smul] using h
    · have h := congrArg (fun p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => q⁻¹ • p) hpg
      change g • (q⁻¹ • p) = q⁻¹ • p
      simpa only [mul_smul, inv_smul_smul] using h
  · rintro ⟨p, hpf, hpg⟩
    refine ⟨q • p, ?_, ?_⟩
    · change (q * f * q⁻¹) • (q • p) = q • p
      simp only [mul_smul, inv_smul_smul, show f • p = p from hpf]
    · change (q * g * q⁻¹) • (q • p) = q • p
      simp only [mul_smul, inv_smul_smul, show g • p = p from hpg]

/-- A nonidentity actual map fixing zero and infinity is a multiplication standard representative. -/
theorem mobius_fixed_zero_infty_standard (f : complexMobiusGroup) (hf : f ≠ 1)
    (h0 : f.val (0 : ℂ) = (0 : ℂ)) (hi : f.val ∞ = ∞) :
    ∃ k : ℂˣ, (k : ℂ) ≠ 1 ∧ f = mobiusStandardElement k := by
  let F := complexMobiusEquivFractionalLinear f
  have hiF : (F : Equiv.Perm ExtendedComplex) ∞ = ∞ := hi
  obtain ⟨k, b, hF⟩ := Mobius.Classification.affine_of_fixes_infty F hiF
  have hb : b = 0 := by
    have h0F : (F : Equiv.Perm ExtendedComplex) (0 : ℂ) = (0 : ℂ) := h0
    rw [hF, matrixProjection_apply, Mobius.Classification.affineMatrix_coe, OnePoint.coe_eq_coe] at h0F
    simpa only [mul_zero, zero_add] using h0F
  have hk : (k : ℂ) ≠ 1 := by
    intro he
    apply hf
    apply mobius_eq_one_of_fixes_zero_one_infty f h0 _ hi
    change (F : Equiv.Perm ExtendedComplex) (1 : ℂ) = (1 : ℂ)
    rw [hF, matrixProjection_apply, Mobius.Classification.affineMatrix_coe, hb, he]
    simp
  refine ⟨k, hk, ?_⟩
  apply complexMobiusEquivFractionalLinear.injective
  rw [mobiusStandardElement_equiv]
  change F = Mobius.Classification.standardElement k
  apply Subtype.ext
  apply Equiv.ext
  intro z
  change (F : Equiv.Perm ExtendedComplex) z = Mobius.Classification.standardForm k z
  rw [hF, matrixProjection_apply]
  induction z using OnePoint.rec with
  | infty => rw [Mobius.Classification.affineMatrix_infty, Mobius.Classification.standardForm_infty]
  | coe z =>
    rw [Mobius.Classification.affineMatrix_coe, Mobius.Classification.standardForm_coe]
    simp only [hb, ite_eq_right hk, add_zero]

/-- The standard vertical axis meets an elliptic axis precisely when their normalized endpoints alternate geometrically. -/
theorem mobius_standard_axis_intersection_iff_cyclicOrder (k : ℂˣ) (hk : (k : ℂ) ≠ 1)
    (hkn : ‖(k : ℂ)‖ = 1) (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : MobiusElliptic (mobiusSpecialLinearProjection A)) (w : ℂ) (hw0 : w ≠ 0) (hw1 : w ≠ 1)
    (hc : A 1 0 ≠ 0)
    (h1 : (mobiusSpecialLinearProjection A).val (1 : ℂ) = (1 : ℂ))
    (hw : (mobiusSpecialLinearProjection A).val w = w) :
    (mobiusAxis (mobiusStandardElement k) ∩ mobiusAxis (mobiusSpecialLinearProjection A)).Nonempty ↔
      ComplexCyclicOrder (0 : ℂ) (1 : ℂ) ∞ w := by
  rw [complexCyclicOrder_zero_one_infty_iff w hw0 hw1,
    ← specialLinear_elliptic_one_second_vertical_iff A hA w hw1 hc h1 hw]
  constructor
  · rintro ⟨p, hpf, hpg⟩
    rw [mobiusStandardElement_axis k hk hkn] at hpf
    have he : p = mobiusVerticalPoint (Hyperbolic.QuaternionHalfSpace.quaternionHeight p.val) p.property := by
      apply Subtype.ext
      exact (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates p.val).symm.trans (by
        rw [show Hyperbolic.QuaternionHalfSpace.quaternionHorizontal p.val = 0 from hpf]
        rfl)
    refine ⟨Hyperbolic.QuaternionHalfSpace.quaternionHeight p.val, p.property, ?_⟩
    rw [← he]
    exact hpg
  · rintro ⟨t, ht, hpt⟩
    refine ⟨mobiusVerticalPoint t ht, ?_, hpt⟩
    rw [mobiusStandardElement_axis k hk hkn]
    exact Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint 0 t


/-- With four distinct endpoints, two actual elliptic axes meet exactly when the endpoint pairs alternate on a genuine generalized circle. -/
theorem mobius_elliptic_axes_intersect_iff_cyclicOrder (f g : complexMobiusGroup)
    (hf : MobiusElliptic f) (hg : MobiusElliptic g) (a b c d : ExtendedComplex)
    (hd : QuadrupleDistinct a c b d)
    (hfa : f.val a = a) (hfb : f.val b = b)
    (hgc : g.val c = c) (hgd : g.val d = d) :
    (mobiusAxis f ∩ mobiusAxis g).Nonempty ↔ ComplexCyclicOrder a c b d := by
  obtain ⟨q, hqa, hqc, hqb⟩ := mobius_normalize_triple a c b ⟨hd.1, hd.2.1, hd.2.2.2.1⟩
  have hqd : q.val d ≠ ∞ := by
    intro he
    exact hd.2.2.2.2.2 (q.val.injective (hqb.trans he.symm))
  obtain ⟨w, hw⟩ := OnePoint.ne_infty_iff_exists.mp hqd
  have hw0 : w ≠ 0 := by
    intro he
    exact hd.2.2.1 (q.val.injective (hqa.trans (by simpa only [he] using hw)))
  have hw1 : w ≠ 1 := by
    intro he
    exact hd.2.2.2.2.1 (q.val.injective (hqc.trans (by simpa only [he] using hw)))
  let F := q * f * q⁻¹
  let G := q * g * q⁻¹
  have hFE : MobiusElliptic F := (mobiusElliptic_conjugation f q).mpr hf
  have hGE : MobiusElliptic G := (mobiusElliptic_conjugation g q).mpr hg
  have hF0 : F.val (0 : ℂ) = (0 : ℂ) := by
    rw [show ((0 : ℂ) : ExtendedComplex) = q.val a from hqa.symm]
    change q.val (f.val (q.val.symm (q.val a))) = q.val a
    rw [q.val.symm_apply_apply, hfa]
  have hFi : F.val ∞ = ∞ := by
    rw [← hqb]
    change q.val (f.val (q.val.symm (q.val b))) = q.val b
    rw [q.val.symm_apply_apply, hfb]
  have hG1 : G.val (1 : ℂ) = (1 : ℂ) := by
    rw [show ((1 : ℂ) : ExtendedComplex) = q.val c from hqc.symm]
    change q.val (g.val (q.val.symm (q.val c))) = q.val c
    rw [q.val.symm_apply_apply, hgc]
  have hGw : G.val w = w := by
    rw [hw]
    change q.val (g.val (q.val.symm (q.val d))) = q.val d
    rw [q.val.symm_apply_apply, hgd]
  obtain ⟨k, hk, hFk⟩ := mobius_fixed_zero_infty_standard F hFE.1 hF0 hFi
  have hkn : ‖(k : ℂ)‖ = 1 := ((mobiusStandardElement_elliptic_iff k).mp (hFk ▸ hFE)).2
  obtain ⟨A, hA⟩ := mobiusSpecialLinearProjection_surjective G
  have hc : A 1 0 ≠ 0 := by
    intro hc
    have hGi : G.val ∞ = ∞ := by
      rw [← hA]
      exact (Mobius.Classification.specialLinear_fixes_infty_iff A).mpr hc
    exact hGE.1 (mobius_eq_one_of_three_fixed G (1 : ℂ) w ∞
      (fun he => hw1 (OnePoint.coe_injective he.symm))
      (OnePoint.coe_ne_infty _) (OnePoint.coe_ne_infty _) hG1 hGw hGi)
  have hnormalized : (mobiusAxis F ∩ mobiusAxis G).Nonempty ↔
      ComplexCyclicOrder (0 : ℂ) (1 : ℂ) ∞ w := by
    rw [hFk, ← hA]
    exact mobius_standard_axis_intersection_iff_cyclicOrder k hk hkn A (hA ▸ hGE)
      w hw0 hw1 hc (hA ▸ hG1) (hA ▸ hGw)
  rw [← mobiusAxes_intersect_conjugation f g q, hnormalized]
  constructor
  · intro ho
    have ht := ho.image q⁻¹
    change ComplexCyclicOrder (q.val.symm (0 : ℂ)) (q.val.symm (1 : ℂ))
      (q.val.symm ∞) (q.val.symm w) at ht
    rwa [← hqa, ← hqc, ← hqb, hw, q.val.symm_apply_apply,
      q.val.symm_apply_apply, q.val.symm_apply_apply, q.val.symm_apply_apply] at ht
  · intro ho
    have ht := ho.image q
    rwa [hqa, hqc, hqb, ← hw] at ht


open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius

/-- The actual unit-sphere point corresponding to the fixed complex boundary chart. -/
def complexSpherePoint (z : ExtendedComplex) : Inversive.Euclidean 3 :=
  (Inversive.stereographicHomeomorph 2 (extendedComplexEuclideanHomeomorph z)).val

/-- The actual sphere chart is injective, including infinity. -/
theorem complexSpherePoint_injective : Function.Injective complexSpherePoint := by
  intro z w h
  apply extendedComplexEuclideanHomeomorph.injective
  apply (Inversive.stereographicHomeomorph 2).injective
  exact Subtype.ext h

/-- The source's quaternion-derived geometric Cayley map is exactly the generic native Cayley map. -/
theorem cayleyEuclideanHomeomorph_eq_cayleyBall :
    cayleyEuclideanHomeomorph = Hyperbolic.cayleyBall 2 := rfl

/-- The real geometric Cayley map has the actual stereographic unit-sphere boundary chart. -/
theorem cayleyEuclideanHomeomorph_boundary (z : ExtendedComplex) :
    cayleyEuclideanHomeomorph
      (Inversive.extendedEquatorialEmbedding 2 (extendedComplexEuclideanHomeomorph z)) =
      (complexSpherePoint z : Inversive.ExtendedEuclidean 3) := by
  rw [cayleyEuclideanHomeomorph_eq_cayleyBall]
  exact Hyperbolic.cayleyBall_equatorial _

/-- A reflected ball plane and its genuine boundary reflection have the same literal sphere-point action. -/
theorem ballPlaneReflection_boundary_spherePoint (a : Inversive.Euclidean 3) (ha : a ≠ 0)
    (f : Inversive.GM 2)
    (hf : (Hyperbolic.poincareExtension f : Inversive.ExtendedHomeomorph 3) =
      cayleyPullback (Inversive.planeReflectionHomeomorph a 0 ha)) (z : ExtendedComplex) :
    Inversive.planeReflectionHomeomorph a 0 ha (complexSpherePoint z : Inversive.ExtendedEuclidean 3) =
      (complexSpherePoint (euclideanToComplexHom f z) : Inversive.ExtendedEuclidean 3) := by
  have hchart : extendedComplexEuclideanHomeomorph (euclideanToComplexHom f z) =
      (f : Inversive.ExtendedHomeomorph 2) (extendedComplexEuclideanHomeomorph z) := by
    rw [euclideanToComplexHom_apply, Homeomorph.apply_symm_apply]
  have h := congrArg (fun F : Inversive.ExtendedHomeomorph 3 =>
    cayleyEuclideanHomeomorph
      (F (Inversive.extendedEquatorialEmbedding 2 (extendedComplexEuclideanHomeomorph z)))) hf
  have h' : cayleyEuclideanHomeomorph
      ((Hyperbolic.poincareExtension f : Inversive.ExtendedHomeomorph 3)
        (Inversive.extendedEquatorialEmbedding 2 (extendedComplexEuclideanHomeomorph z))) =
      Inversive.planeReflectionHomeomorph a 0 ha
        (cayleyEuclideanHomeomorph
          (Inversive.extendedEquatorialEmbedding 2 (extendedComplexEuclideanHomeomorph z))) := by
    simpa only [cayleyPullback, Homeomorph.mul_apply, Homeomorph.inv_apply,
      Homeomorph.apply_symm_apply] using h
  rw [Hyperbolic.poincareExtension_extendsBoundary, ← hchart,
    cayleyEuclideanHomeomorph_boundary, cayleyEuclideanHomeomorph_boundary] at h'
  exact h'.symm

/-- Every true plane through the Euclidean ball centre pulls back to a genuine generalized complex circle. -/
theorem complexSpherePoint_plane_isGeneralizedCircle (a : Inversive.Euclidean 3) (ha : a ≠ 0) :
    IsComplexGeneralizedCircle {z : ExtendedComplex | inner ℝ (complexSpherePoint z) a = 0} := by
  obtain ⟨f, hf, hfe⟩ := ballPlaneReflection_exists_boundary a ha
  have heq : {z : ExtendedComplex | inner ℝ (complexSpherePoint z) a = 0} =
      Function.fixedPoints (euclideanToComplexHom f) := by
    ext z
    change inner ℝ (complexSpherePoint z) a = 0 ↔ euclideanToComplexHom f z = z
    have hplane : Inversive.planeReflectionHomeomorph a 0 ha
        (complexSpherePoint z : Inversive.ExtendedEuclidean 3) =
        (complexSpherePoint z : Inversive.ExtendedEuclidean 3) ↔ inner ℝ (complexSpherePoint z) a = 0 := by
      rw [Inversive.planeReflectionHomeomorph_apply, Inversive.planeReflection_coe, OnePoint.coe_eq_coe,
        Inversive.planeReflectionFinite_fixed_iff a 0 ha]
    rw [← hplane, ballPlaneReflection_boundary_spherePoint a ha f hfe,
      OnePoint.coe_eq_coe]
    exact complexSpherePoint_injective.eq_iff
  rw [heq]
  unfold IsComplexGeneralizedCircle
  rw [complexReflection_fixedPoints, complexChart_image_preimage]
  exact (Inversive.isGeneralizedSphere_iff_fixedPoints_reflection _).mpr ⟨f, hf, rfl⟩

/-- Every boundary point is sent to an actual unit Euclidean sphere point. -/
theorem complexSpherePoint_norm (z : ExtendedComplex) : ‖complexSpherePoint z‖ = 1 := by
  have h := (Inversive.stereographicHomeomorph 2 (extendedComplexEuclideanHomeomorph z)).property
  simpa only [complexSpherePoint, Metric.mem_sphere, dist_zero_right] using h

/-- The actual geometric ball conjugate intertwines the original boundary action with the sphere chart. -/
theorem mobiusBallConjugate_spherePoint (f : complexMobiusGroup) (z : ExtendedComplex) :
    mobiusBallConjugate f (complexSpherePoint z : Inversive.ExtendedEuclidean 3) =
      (complexSpherePoint (f.val z) : Inversive.ExtendedEuclidean 3) := by
  have hchart := mobiusRealRepresentative_chart f z
  rw [← cayleyEuclideanHomeomorph_boundary]
  change cayleyEuclideanHomeomorph
    ((mobiusGeometricPoincare f : Inversive.ExtendedHomeomorph 3)
      (cayleyEuclideanHomeomorph.symm
        (cayleyEuclideanHomeomorph (Inversive.extendedEquatorialEmbedding 2
          (extendedComplexEuclideanHomeomorph z))))) = _
  rw [Homeomorph.symm_apply_apply]
  have hB := Hyperbolic.poincareExtension_extendsBoundary (mobiusRealRepresentative f)
    (extendedComplexEuclideanHomeomorph z)
  change (mobiusGeometricPoincare f : Inversive.ExtendedHomeomorph 3)
      (Inversive.extendedEquatorialEmbedding 2 (extendedComplexEuclideanHomeomorph z)) =
      Inversive.extendedEquatorialEmbedding 2
        ((mobiusRealRepresentative f : Inversive.ExtendedHomeomorph 2) (extendedComplexEuclideanHomeomorph z)) at hB
  rw [hB, hchart, cayleyEuclideanHomeomorph_boundary]

/-- The physical fixed axis in the actual Euclidean unit ball, for a nonidentity rotation. -/
def mobiusBallFixedAxis (f : complexMobiusGroup) : Set (Inversive.Euclidean 3) :=
  {x | ‖x‖ < 1 ∧ mobiusBallConjugate f (x : Inversive.ExtendedEuclidean 3) = (x : Inversive.ExtendedEuclidean 3)}

/-- Coplanarity means containment of all three actual axes in one true plane through the ball centre. -/
def MobiusBallAxesCoplanar (f g h : complexMobiusGroup) : Prop :=
  ∃ a : Inversive.Euclidean 3, a ≠ 0 ∧
    ∀ x : Inversive.Euclidean 3, x ∈ mobiusBallFixedAxis f ∨ x ∈ mobiusBallFixedAxis g ∨
      x ∈ mobiusBallFixedAxis h → inner ℝ x a = 0

/-- A true plane containing a fixed ball axis contains every actual sphere endpoint of that axis. -/
theorem mobiusBallFixedAxis_plane_contains_boundary (f : complexMobiusGroup)
    (hf : f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) (a
      : Inversive.Euclidean 3)
    (hplane : ∀ x ∈ mobiusBallFixedAxis f, inner ℝ x a = 0)
    (z : ExtendedComplex) (hz : f.val z = z) : inner ℝ (complexSpherePoint z) a = 0 := by
  obtain ⟨L, hL⟩ := (mobiusBallConjugate_orthogonal_iff_fixJ f).mpr hf
  have hLfix : L (complexSpherePoint z) = complexSpherePoint z := by
    apply OnePoint.coe_injective
    rw [← Inversive.cartanLinearExtensionHom_coe, ← hL, mobiusBallConjugate_spherePoint, hz]
  have hhalf : (1 / 2 : ℝ) • complexSpherePoint z ∈ mobiusBallFixedAxis f := by
    constructor
    · rw [norm_smul, complexSpherePoint_norm, mul_one, Real.norm_eq_abs]
      norm_num
    · rw [hL, Inversive.cartanLinearExtensionHom_coe, map_smul, hLfix]
  have h := hplane _ hhalf
  rw [inner_smul_left] at h
  norm_num at h
  exact h

/-- Coplanar physical axes force all their actual boundary fixed sets into one genuine complex circle. -/
theorem mobiusBallAxesCoplanar_boundary_circle (f g h : complexMobiusGroup)
    (hf : f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
    (hg : g • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
    (hh : h • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) (hc
      : MobiusBallAxesCoplanar f g h) :
    ∃ S : Set ExtendedComplex, IsComplexGeneralizedCircle S ∧
      (∀ z : ExtendedComplex, f.val z = z → z ∈ S) ∧
      (∀ z : ExtendedComplex, g.val z = z → z ∈ S) ∧
      (∀ z : ExtendedComplex, h.val z = z → z ∈ S) := by
  obtain ⟨a, ha, hplane⟩ := hc
  refine ⟨{z | inner ℝ (complexSpherePoint z) a = 0},
    complexSpherePoint_plane_isGeneralizedCircle a ha, ?_, ?_, ?_⟩
  · intro z hz
    exact mobiusBallFixedAxis_plane_contains_boundary f hf a
      (fun x hx => hplane x (Or.inl hx)) z hz
  · intro z hz
    exact mobiusBallFixedAxis_plane_contains_boundary g hg a
      (fun x hx => hplane x (Or.inr (Or.inl hx))) z hz
  · intro z hz
    exact mobiusBallFixedAxis_plane_contains_boundary h hh a
      (fun x hx => hplane x (Or.inr (Or.inr hx))) z hz

/-- A genuine circle through zero and infinity is a genuine real line through zero. -/
theorem complexGeneralizedCircle_zero_infty_line {S : Set ExtendedComplex}
    (hS : IsComplexGeneralizedCircle S) (h0 : ((0 : ℂ) : ExtendedComplex) ∈ S)
    (hi : (∞ : ExtendedComplex) ∈ S) :
    ∃ n : ℂ, n ≠ 0 ∧ S = complexLine n 0 := by
  rcases (isComplexGeneralizedCircle_iff S).mp hS with ⟨c, r, _, rfl⟩ | ⟨n, t, hn, rfl⟩
  · exact False.elim (complexCircle_infty c r hi)
  · have ht : t = 0 := by simpa only [complexLine_coe, inner_zero_left, eq_comm] using h0
    exact ⟨n, hn, by rw [ht]⟩

/-- Two finite points on a genuine circle through zero and infinity have real quotient direction. -/
theorem complexGeneralizedCircle_zero_infty_area {S : Set ExtendedComplex}
    (hS : IsComplexGeneralizedCircle S) (h0 : ((0 : ℂ) : ExtendedComplex) ∈ S)
    (hi : (∞ : ExtendedComplex) ∈ S) (z w : ℂ)
    (hz : (z : ExtendedComplex) ∈ S) (hw : (w : ExtendedComplex) ∈ S) :
    (z * conj w).im = 0 := by
  obtain ⟨n, hn, rfl⟩ := complexGeneralizedCircle_zero_infty_line hS h0 hi
  have hz' := (complexLine_coe n z 0).mp hz
  have hw' := (complexLine_coe n w 0).mp hw
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    mul_comm] at hz' hw'
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
  by_cases hnr : n.re = 0
  · have hni : n.im ≠ 0 := by
      intro hni
      apply hn
      apply Complex.ext <;> simp only [Complex.zero_re, Complex.zero_im] <;> assumption
    have hz0 : z.im = 0 := by
      have hm : z.im * n.im = 0 := by rw [hnr] at hz'; nlinarith
      exact (mul_eq_zero.mp hm).resolve_right hni
    have hw0 : w.im = 0 := by
      have hm : w.im * n.im = 0 := by rw [hnr] at hw'; nlinarith
      exact (mul_eq_zero.mp hm).resolve_right hni
    simp only [hz0, hw0, neg_zero, mul_zero, zero_mul, add_zero]
  · apply (mul_eq_zero.mp (show n.re * (z.re * -w.im + z.im * w.re) = 0 by
      linear_combination -w.im * hz' + z.im * hw')).resolve_left hnr

/-- Nonreal rotation separates the two nonzero normalized fixed-point directions. -/
theorem complex_nonreal_rotation_fixed_directions (u c z w : ℂ)
    (hu : u.im ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0)
    (hzline : (c * z).re = 0) (hwline : (conj u * c * w).re = 0) :
    (z * conj w).im ≠ 0 := by
  intro harea
  have he : (c * z) * conj (c * w) = (Complex.normSq c : ℂ) * (z * conj w) := by
    simp only [map_mul, ← Complex.mul_conj]
    ring
  have hxy : ((c * z) * conj (c * w)).im = 0 := by
    rw [he]
    simp only [Complex.mul_im, Complex.ofReal_im, harea, mul_zero, zero_mul, add_zero]
  have hxim : (c * z).im ≠ 0 := by
    intro hi
    apply mul_ne_zero hc hz
    apply Complex.ext
    · exact hzline
    · exact hi
  have hmul : (c * z).im * (c * w).re = 0 := by
    simpa only [Complex.mul_im, Complex.conj_re, Complex.conj_im,
      hzline, zero_mul, zero_add] using hxy
  have hyr : (c * w).re = 0 := (mul_eq_zero.mp hmul).resolve_left hxim
  rw [mul_assoc] at hwline
  have huy : u.im * (c * w).im = 0 := by
    simpa only [Complex.mul_re, Complex.conj_re, Complex.conj_im, hyr,
      mul_zero, neg_mul, sub_neg_eq_add, zero_add] using hwline
  have hyi : (c * w).im = 0 := (mul_eq_zero.mp huy).resolve_left hu
  apply mul_ne_zero hc hw
  apply Complex.ext
  · exact hyr
  · exact hyi

/-- A nonzero lower-left coefficient prevents the actual projective transformation from being identity. -/
theorem specialLinear_lower_nonzero_ne_one (A : Auxiliary.Algebra.SpecialLinear2) (hc : A 1 0 ≠ 0) :
    mobiusSpecialLinearProjection A ≠ 1 := by
  intro he
  have hi := congrArg (fun f : complexMobiusGroup => f.val ∞) he
  change fractionalLinear (Matrix.SpecialLinearGroup.toGL A) ∞ = ∞ at hi
  rw [fractionalLinear_infty] at hi
  change (if A 1 0 = 0 then ∞ else ((A 0 0 / A 1 0 : ℂ) : ExtendedComplex)) = ∞ at hi
  rw [ite_eq_right hc] at hi
  exact OnePoint.coe_ne_infty _ hi

/-- Nonzero off-diagonal entries give a nonzero finite boundary fixed point of the actual matrix action. -/
theorem specialLinear_exists_nonzero_finite_fixed (A : Auxiliary.Algebra.SpecialLinear2)
    (hb : A 0 1 ≠ 0) (hc : A 1 0 ≠ 0) :
    ∃ z : ℂ, z ≠ 0 ∧
      (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) z = z := by
  have hinf : (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) ∞ ≠ ∞ := by
    change fractionalLinear (Matrix.SpecialLinearGroup.toGL A) ∞ ≠ ∞
    rw [fractionalLinear_infty]
    change (if A 1 0 = 0 then ∞ else ((A 0 0 / A 1 0 : ℂ) : ExtendedComplex)) ≠ ∞
    rw [ite_eq_right hc]
    exact OnePoint.coe_ne_infty _
  have hA : mobiusSpecialLinearProjection A ≠ 1 := by
    intro he
    apply hinf
    rw [he]
    rfl
  obtain ⟨z, hz⟩ := mobius_nonidentity_has_boundary_fixed _ hA
  have hzinf : z ≠ ∞ := by
    intro he
    subst z
    exact hinf hz
  obtain ⟨w, rfl⟩ := OnePoint.ne_infty_iff_exists.mp hzinf
  refine ⟨w, ?_, hz⟩
  intro hw
  subst w
  change fractionalLinear (Matrix.SpecialLinearGroup.toGL A) (0 : ℂ) = (0 : ℂ) at hz
  have hp := (Mobius.Classification.fractionalLinear_fixed_coe_iff _ 0).mp hz
  change A 1 0 * (0 * 0) + (A 1 1 - A 0 0) * 0 + (-A 0 1) = 0 at hp
  simp only [mul_zero, zero_add, neg_eq_zero] at hp
  exact hb hp

/-- The normalized three-fixed-pair nonconcyclicity calculation only requires ellipticity and nonzero off-diagonals. -/
theorem specialLinear_elliptic_three_fixedSets_not_circle (R A : Auxiliary.Algebra.SpecialLinear2)
    (hR01 : R 0 1 = 0) (hR10 : R 1 0 = 0) (hRd : R 1 1 = conj (R 0 0))
    (hRi : (R 0 0).im ≠ 0)
    (hAe : MobiusElliptic (mobiusSpecialLinearProjection A))
    (hRAe : MobiusElliptic (mobiusSpecialLinearProjection (R * A)))
    (hb : A 0 1 ≠ 0) (hc : A 1 0 ≠ 0) :
    ¬∃ S : Set ExtendedComplex, IsComplexGeneralizedCircle S ∧
      ((0 : ℂ) : ExtendedComplex) ∈ S ∧ (∞ : ExtendedComplex) ∈ S ∧
      (∀ z : ExtendedComplex, (mobiusSpecialLinearProjection A).val z = z → z ∈ S) ∧
      (∀ z : ExtendedComplex, (mobiusSpecialLinearProjection (R * A)).val z = z → z ∈ S) := by
  have hAd := specialLinear_real_traces_conjugate_diagonal R A hR01 hR10 hRd hRi
    (specialLinear_elliptic_or_identity_trace A (Or.inr hAe)).1
    (specialLinear_elliptic_or_identity_trace (R * A) (Or.inr hRAe)).1
  have hRu : R 0 0 ≠ 0 := by intro he; apply hRi; rw [he]; rfl
  have hRAc : (R * A) 1 0 = conj (R 0 0) * A 1 0 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      hR10, hRd, zero_mul, zero_add]
  have hRAb : (R * A) 0 1 = R 0 0 * A 0 1 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      hR01, zero_mul, add_zero]
  have hRAc0 : (R * A) 1 0 ≠ 0 := by
    rw [hRAc]
    exact mul_ne_zero ((map_ne_zero (starRingEnd ℂ)).mpr hRu) hc
  have hRAb0 : (R * A) 0 1 ≠ 0 := by rw [hRAb]; exact mul_ne_zero hRu hb
  have hRAd : (R * A) 1 1 = conj ((R * A) 0 0) := by
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      hR01, hR10, zero_mul, zero_add, add_zero, hRd, hAd, map_mul]
  obtain ⟨z, hz0, hz⟩ := specialLinear_exists_nonzero_finite_fixed A hb hc
  obtain ⟨w, hw0, hw⟩ := specialLinear_exists_nonzero_finite_fixed (R * A) hRAb0 hRAc0
  have hzline := specialLinear_elliptic_fixed_line A hAd
    (specialLinear_elliptic_real_diagonal_sq_lt A hAe hAd) z hz
  have hwline := specialLinear_elliptic_fixed_line (R * A) hRAd
    (specialLinear_elliptic_real_diagonal_sq_lt (R * A) hRAe hRAd) w hw
  have hzre : (A 1 0 * z).re = 0 := by
    simpa only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      neg_mul, sub_neg_eq_add, mul_neg, neg_neg, mul_comm] using hzline
  have hwre : (conj (R 0 0) * A 1 0 * w).re = 0 := by
    rw [← hRAc]
    simpa only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      neg_mul, sub_neg_eq_add, mul_neg, neg_neg, mul_comm] using hwline
  rintro ⟨S, hS, h0, hi, hAS, hRAS⟩
  exact complex_nonreal_rotation_fixed_directions (R 0 0) (A 1 0) z w hRi hc hz0 hw0 hzre hwre
    (complexGeneralizedCircle_zero_infty_area hS h0 hi z w (hAS _ hz) (hRAS _ hw))

/-- The geometric elliptic and parabolic classes are disjoint. -/
theorem MobiusElliptic.not_parabolic {f : complexMobiusGroup} (he : MobiusElliptic f) :
    ¬MobiusParabolic f := by
  intro hp
  obtain ⟨r, _, hr, ht⟩ := (mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four f he.1).mp he
  have hfour := (mobius_parabolic_iff_squaredTrace_eq_four f he.1).mp hp
  rw [hfour] at ht
  have h := congrArg Complex.re ht
  norm_num at h
  linarith

/-- The actual commutator of two maps fixing j also fixes j. -/
theorem mobiusCommutator_fixJ (f g : complexMobiusGroup)
    (hf : f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
    (hg : g • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) :
    mobiusCommutator f g • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ =
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
  have hfi : f⁻¹ • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
    := inv_smul_eq_iff.mpr hf.symm
  have hgi : g⁻¹ • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
    := inv_smul_eq_iff.mpr hg.symm
  simp only [mobiusCommutator, mul_smul, hfi, hgi, hf, hg]

/-- Two nonidentity rotations with a common boundary fixed point have the same full boundary fixed set. -/
theorem mobius_fixJ_common_boundary_same_fixedPoints (f g : complexMobiusGroup)
    (hf0 : f ≠ 1) (hg0 : g ≠ 1)
    (hf : f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
    (hg : g • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
      (hcommon : MobiusCommonFixedPoint f g) :
    MobiusSameFixedPoints f g := by
  rcases mobius_commonFixedPoint_commutator_dichotomy f g hf0 hg0 hcommon with ⟨_, _, hs⟩ | ⟨hp, _, _⟩
  · exact hs
  · have he : MobiusElliptic (mobiusCommutator f g) :=
      (mobiusElliptic_iff_H3_fixed _ hp.1).mpr ⟨_, mobiusCommutator_fixJ f g hf hg⟩
    exact False.elim (he.not_parabolic hp)

/-- Actual boundary fixed sets are transported exactly by conjugation. -/
theorem mobiusSameFixedPoints_conjugation (f g q : complexMobiusGroup) :
    MobiusSameFixedPoints (q * f * q⁻¹) (q * g * q⁻¹) ↔ MobiusSameFixedPoints f g := by
  constructor
  · intro h z
    have hz := h (q.val z)
    simpa only [mobius_conjugate_boundary_fixed_iff, Equiv.symm_apply_apply] using hz
  · intro h z
    rw [mobius_conjugate_boundary_fixed_iff, mobius_conjugate_boundary_fixed_iff]
    exact h _

/-- Distinct full fixed sets rule out an inverse pair of transformations. -/
theorem mobius_product_ne_one_of_different_fixedPoints (f g : complexMobiusGroup)
    (h : ¬MobiusSameFixedPoints f g) : f * g ≠ 1 := by
  intro he
  have hgi : g = f⁻¹ := eq_inv_of_mul_eq_one_right he
  apply h
  intro z
  rw [hgi]
  change f.val z = z ↔ f.val.symm z = z
  rw [Equiv.symm_apply_eq]
  exact eq_comm

/-- The fixed set of a conjugate is contained in the image of any set containing the original fixed set. -/
theorem mobius_conjugate_fixed_subset_image (f q : complexMobiusGroup)
    (S : Set ExtendedComplex) (hS : ∀ z : ExtendedComplex, f.val z = z → z ∈ S) :
    ∀ z : ExtendedComplex, (q * f * q⁻¹).val z = z → z ∈ q.val '' S := by
  intro z hz
  exact ⟨q.val.symm z, hS _ ((mobius_conjugate_boundary_fixed_iff f q z).mp hz), q.val.apply_symm_apply z⟩

/-- Distinct axes of two genuine ball rotations force their product to be nonidentity and the three physical axes to be noncoplanar. -/
theorem mobius_fixJ_different_fixedPoints_three_axes (f g : complexMobiusGroup)
    (hf0 : f ≠ 1) (hg0 : g ≠ 1)
    (hfJ : f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
    (hgJ : g • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
    (hsame : ¬MobiusSameFixedPoints f g) :
    f * g ≠ 1 ∧ ¬MobiusBallAxesCoplanar f g (f * g) := by
  have hfg0 := mobius_product_ne_one_of_different_fixedPoints f g hsame
  have hfgJ : (f * g) • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ =
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by rw [mul_smul, hgJ, hfJ]
  have hf : MobiusElliptic f := (mobiusElliptic_iff_H3_fixed f hf0).mpr ⟨_, hfJ⟩
  have hg : MobiusElliptic g := (mobiusElliptic_iff_H3_fixed g hg0).mpr ⟨_, hgJ⟩
  have hfg : MobiusElliptic (f * g) := (mobiusElliptic_iff_H3_fixed _ hfg0).mpr ⟨_, hfgJ⟩
  have hncommon : ¬MobiusCommonFixedPoint f g :=
    fun h => hsame (mobius_fixJ_common_boundary_same_fixedPoints f g hf0 hg0 hfJ hgJ h)
  obtain ⟨k, hk, hkn, hconj⟩ := (mobiusElliptic_iff_conjugate_standard f).mp hf
  obtain ⟨q, hq⟩ := isConj_iff.mp hconj
  obtain ⟨R, hR, hR01, hR10, hRd, hRi⟩ := unit_standard_specialLinear_diagonal k hk hkn
  obtain ⟨A, hA⟩ := mobiusSpecialLinearProjection_surjective (q * g * q⁻¹)
  have hAE : MobiusElliptic (mobiusSpecialLinearProjection A) := by
    rw [hA]
    exact (mobiusElliptic_conjugation g q).mpr hg
  have hRAE : MobiusElliptic (mobiusSpecialLinearProjection (R * A)) := by
    rw [map_mul, hR, hA, ← hq]
    simpa only [mul_assoc, inv_mul_cancel_left] using (mobiusElliptic_conjugation (f * g) q).mpr hfg
  have hnq : ¬MobiusCommonFixedPoint (q * f * q⁻¹) (q * g * q⁻¹) := by
    rintro ⟨z, hzF, hzG⟩
    apply hncommon
    exact ⟨q.val.symm z, (mobius_conjugate_boundary_fixed_iff f q z).mp hzF,
      (mobius_conjugate_boundary_fixed_iff g q z).mp hzG⟩
  have hstd0 : (mobiusStandardElement k).val (0 : ℂ) = (0 : ℂ) := by
    rw [mobiusStandardElement_coe]
    simp only [ite_eq_right hk, mul_zero]
  have hb : A 0 1 ≠ 0 := by
    intro hb
    apply hnq
    refine ⟨(0 : ℂ), by rw [hq]; exact hstd0, ?_⟩
    rw [← hA]
    change fractionalLinear (Matrix.SpecialLinearGroup.toGL A) (0 : ℂ) = (0 : ℂ)
    apply (Mobius.Classification.fractionalLinear_fixed_coe_iff _ 0).mpr
    change A 1 0 * (0 * 0) + (A 1 1 - A 0 0) * 0 + (-A 0 1) = 0
    simp only [hb, mul_zero, zero_add, neg_zero]
  have hc : A 1 0 ≠ 0 := by
    intro hc
    apply hnq
    refine ⟨∞, by rw [hq]; exact mobiusStandardElement_infty k, ?_⟩
    rw [← hA]
    change fractionalLinear (Matrix.SpecialLinearGroup.toGL A) ∞ = ∞
    rw [fractionalLinear_infty]
    change (if A 1 0 = 0 then ∞ else ((A 0 0 / A 1 0 : ℂ) : ExtendedComplex)) = ∞
    rw [ite_eq_left hc]
  refine ⟨hfg0, ?_⟩
  intro hcop
  obtain ⟨S, hS, hSf, hSg, hSfg⟩ :=
    mobiusBallAxesCoplanar_boundary_circle f g (f * g) hfJ hgJ hfgJ hcop
  apply specialLinear_elliptic_three_fixedSets_not_circle R A hR01 hR10 hRd hRi hAE hRAE hb hc
  refine ⟨q.val '' S, hS.image q.property.1, ?_, ?_, ?_, ?_⟩
  · apply mobius_conjugate_fixed_subset_image f q S hSf
    rw [hq]
    exact hstd0
  · apply mobius_conjugate_fixed_subset_image f q S hSf
    rw [hq]
    exact mobiusStandardElement_infty k
  · rw [hA]
    exact mobius_conjugate_fixed_subset_image g q S hSg
  · intro z hz
    apply mobius_conjugate_fixed_subset_image (f * g) q S hSfg z
    have he : q * (f * g) * q⁻¹ = mobiusSpecialLinearProjection (R * A) := by
      rw [map_mul, hR, hA, ← hq]
      group
    rw [he]
    exact hz

/-- The true complex sphere chart covers the entire Euclidean unit sphere. -/
theorem complexSpherePoint_exists (x : Inversive.Euclidean 3) (hx : ‖x‖ = 1) :
    ∃ z : ExtendedComplex, complexSpherePoint z = x := by
  let v : Metric.sphere (0 : Inversive.Euclidean 3) 1 := ⟨x, by
    simpa only [Metric.mem_sphere, dist_zero_right] using hx⟩
  refine ⟨extendedComplexEuclideanHomeomorph.symm ((Inversive.stereographicHomeomorph 2).symm v), ?_⟩
  simp only [complexSpherePoint, Homeomorph.apply_symm_apply]
  rfl

/-- A genuine ball rotation fixes a sphere direction exactly when its linear rotation fixes that vector. -/
theorem mobiusBallConjugate_boundary_fixed_iff (f : complexMobiusGroup)
    (L : Inversive.Euclidean 3 ≃ₗᵢ[ℝ] Inversive.Euclidean 3)
    (hL : mobiusBallConjugate f = Inversive.cartanLinearExtensionHom L) (z : ExtendedComplex) :
    f.val z = z ↔ L (complexSpherePoint z) = complexSpherePoint z := by
  have he : (complexSpherePoint (f.val z) : Inversive.ExtendedEuclidean 3) =
      (L (complexSpherePoint z) : Inversive.ExtendedEuclidean 3) := by
    rw [← mobiusBallConjugate_spherePoint, hL, Inversive.cartanLinearExtensionHom_coe]
  constructor
  · intro hz
    apply OnePoint.coe_injective
    rw [← he, hz]
  · intro hz
    apply complexSpherePoint_injective
    apply OnePoint.coe_injective
    rw [he, hz]

/-- Equal full boundary fixed sets give equal literal fixed axes in the genuine ball. -/
theorem mobiusBallFixedAxis_eq_of_same_fixedPoints (f g : complexMobiusGroup)
    (hf : f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
    (hg : g • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) (hs
      : MobiusSameFixedPoints f g) :
    mobiusBallFixedAxis f = mobiusBallFixedAxis g := by
  obtain ⟨L, hL⟩ := (mobiusBallConjugate_orthogonal_iff_fixJ f).mpr hf
  obtain ⟨M, hM⟩ := (mobiusBallConjugate_orthogonal_iff_fixJ g).mpr hg
  have he : ∀ x : Inversive.Euclidean 3, L x = x ↔ M x = x := by
    intro x
    by_cases hx : x = 0
    · subst x
      simp only [map_zero]
    · have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
      have hv : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
        rw [norm_smul_of_nonneg (inv_nonneg.mpr (norm_nonneg x)), inv_mul_cancel₀ hn]
      obtain ⟨z, hz⟩ := complexSpherePoint_exists _ hv
      have hrec : x = ‖x‖ • complexSpherePoint z := by
        rw [hz, smul_smul, mul_inv_cancel₀ hn, one_smul]
      constructor
      · intro hfix
        have hzL : L (complexSpherePoint z) = complexSpherePoint z := by
          rw [hz, map_smul, hfix]
        have hzM := (mobiusBallConjugate_boundary_fixed_iff g M hM z).mp
          ((hs z).mp ((mobiusBallConjugate_boundary_fixed_iff f L hL z).mpr hzL))
        conv_lhs => rw [hrec]
        rw [map_smul, hzM, ← hrec]
      · intro hfix
        have hzM : M (complexSpherePoint z) = complexSpherePoint z := by
          rw [hz, map_smul, hfix]
        have hzL := (mobiusBallConjugate_boundary_fixed_iff f L hL z).mp
          ((hs z).mpr ((mobiusBallConjugate_boundary_fixed_iff g M hM z).mpr hzM))
        conv_lhs => rw [hrec]
        rw [map_smul, hzL, ← hrec]
  ext x
  change (‖x‖ < 1 ∧ mobiusBallConjugate f (x : Inversive.ExtendedEuclidean 3) = (x : Inversive.ExtendedEuclidean 3)) ↔
    (‖x‖ < 1 ∧ mobiusBallConjugate g (x : Inversive.ExtendedEuclidean 3) = (x : Inversive.ExtendedEuclidean 3))
  rw [hL, hM, Inversive.cartanLinearExtensionHom_coe, Inversive.cartanLinearExtensionHom_coe,
    OnePoint.coe_eq_coe, OnePoint.coe_eq_coe, he x]

/-- Every nonidentity genuine ball rotation has exactly two distinct actual boundary fixed points. -/
theorem mobius_fixJ_two_boundary_fixed (f : complexMobiusGroup) (hf0 : f ≠ 1)
    (hf : f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) :
    ∃ a b : ExtendedComplex, a ≠ b ∧ ∀ z : ExtendedComplex, f.val z = z ↔ z = a ∨ z = b := by
  have he : MobiusElliptic f := (mobiusElliptic_iff_H3_fixed f hf0).mpr ⟨_, hf⟩
  rcases mobius_nonidentity_fixedPoint_dichotomy f hf0 with ⟨a, ha⟩ | hpair
  · exact False.elim (he.not_parabolic ⟨hf0, a, ha⟩)
  · exact hpair

/-- Two common endpoints and the ball centre stay fixed throughout the actual generated subgroup. -/
theorem mobius_generated_pair_fixes (f g : complexMobiusGroup) (a b : ExtendedComplex)
    (hfa : f.val a = a) (hfb : f.val b = b) (hga : g.val a = a) (hgb : g.val b = b)
    (hf : f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) (hg
      : g • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
    (k : complexMobiusGroup) (hk : k ∈ Subgroup.closure ({f, g} : Set complexMobiusGroup)) :
    k.val a = a ∧ k.val b = b ∧ k • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ =
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
  induction hk using Subgroup.closure_induction with
  | mem k hk =>
      rcases Set.mem_insert_iff.mp hk with rfl | hk
      · exact ⟨hfa, hfb, hf⟩
      · have he : k = g := Set.mem_singleton_iff.mp hk
        subst k
        exact ⟨hga, hgb, hg⟩
  | one => exact ⟨rfl, rfl, one_smul _ _⟩
  | mul x y _ _ hx hy =>
      refine ⟨?_, ?_, ?_⟩
      · change x.val (y.val a) = a
        rw [hy.1, hx.1]
      · change x.val (y.val b) = b
        rw [hy.2.1, hx.2.1]
      · rw [mul_smul, hy.2.2, hx.2.2]
  | inv x _ hx =>
      refine ⟨?_, ?_, inv_smul_eq_iff.mpr hx.2.2.symm⟩
      · change x.val.symm a = a
        exact (Equiv.symm_apply_eq x.val).mpr hx.1.symm
      · change x.val.symm b = b
        exact (Equiv.symm_apply_eq x.val).mpr hx.2.1.symm

/-- With equal initial endpoint pairs, every nonidentity generated rotation has the same full endpoint pair and actual physical axis. -/
theorem mobius_fixJ_same_fixedPoints_generated_axis (f g : complexMobiusGroup)
    (hf0 : f ≠ 1) (hf : f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ =
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
    (hg : g • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) (hs
      : MobiusSameFixedPoints f g) :
    ∀ k ∈ Subgroup.closure ({f, g} : Set complexMobiusGroup), k ≠ 1 →
      MobiusSameFixedPoints k f ∧ mobiusBallFixedAxis k = mobiusBallFixedAxis f := by
  obtain ⟨a, b, hab, hp⟩ := mobius_fixJ_two_boundary_fixed f hf0 hf
  have hfa : f.val a = a := (hp a).mpr (Or.inl rfl)
  have hfb : f.val b = b := (hp b).mpr (Or.inr rfl)
  intro k hk hk0
  obtain ⟨hka, hkb, hkJ⟩ := mobius_generated_pair_fixes f g a b hfa hfb
    ((hs a).mp hfa) ((hs b).mp hfb) hf hg k hk
  have hsame : MobiusSameFixedPoints k f := by
    intro z
    rw [hp z]
    constructor
    · intro hkz
      by_cases hza : z = a
      · exact Or.inl hza
      by_cases hzb : z = b
      · exact Or.inr hzb
      exact False.elim (hk0 (mobius_eq_one_of_three_fixed k a b z hab (Ne.symm hza) (Ne.symm hzb) hka hkb hkz))
    · rintro (rfl | rfl)
      · exact hka
      · exact hkb
  exact ⟨hsame, mobiusBallFixedAxis_eq_of_same_fixedPoints k f hkJ hf hsame⟩

/-- genuine ball rotations either generate a group with one endpoint pair and physical axis, or have three actual noncoplanar axes. -/
theorem common_halfSpace_fixedPoint_axis_dichotomy (f g : complexMobiusGroup) (hf0 : f ≠ 1) (hg0 : g ≠ 1)
    (hf : f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) (hg
      : g • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) :
    (∀ k ∈ Subgroup.closure ({f, g} : Set complexMobiusGroup), k ≠ 1 →
      MobiusSameFixedPoints k f ∧ mobiusBallFixedAxis k = mobiusBallFixedAxis f) ∨
    ∃ h ∈ Subgroup.closure ({f, g} : Set complexMobiusGroup), h ≠ 1 ∧ ¬MobiusBallAxesCoplanar f g h := by
  by_cases hs : MobiusSameFixedPoints f g
  · exact Or.inl (mobius_fixJ_same_fixedPoints_generated_axis f g hf0 hf hg hs)
  · obtain ⟨hfg, hnonplane⟩ := mobius_fixJ_different_fixedPoints_three_axes f g hf0 hg0 hf hg hs
    refine Or.inr ⟨f * g, ?_, hfg, hnonplane⟩
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert f {g}))
      (Subgroup.subset_closure (Set.mem_insert_of_mem f (Set.mem_singleton g)))

/-- With the hypotheses stated directly in the actual geometric ball model. -/
theorem common_ball_origin_fixedPoint_axis_dichotomy (f g : complexMobiusGroup) (hf0 : f ≠ 1) (hg0 : g ≠ 1)
    (hf : mobiusBallConjugate f ((0 : Inversive.Euclidean 3) : Inversive.ExtendedEuclidean 3) = ((0 :
      Inversive.Euclidean 3) : Inversive.ExtendedEuclidean 3))
    (hg : mobiusBallConjugate g ((0 : Inversive.Euclidean 3) : Inversive.ExtendedEuclidean 3) = ((0 :
      Inversive.Euclidean 3) : Inversive.ExtendedEuclidean 3)) :
    (∀ k ∈ Subgroup.closure ({f, g} : Set complexMobiusGroup), k ≠ 1 →
      MobiusSameFixedPoints k f ∧ mobiusBallFixedAxis k = mobiusBallFixedAxis f) ∨
    ∃ h ∈ Subgroup.closure ({f, g} : Set complexMobiusGroup), h ≠ 1 ∧ ¬MobiusBallAxesCoplanar f g h := by
  exact common_halfSpace_fixedPoint_axis_dichotomy f g hf0 hg0 ((mobiusBallConjugate_fix_zero_iff f).mp hf)
    ((mobiusBallConjugate_fix_zero_iff g).mp hg)



/-- A real horizontal translation sends the actual quaternion vertical ray to the standard vertical ray. -/
theorem affineMobius_translate_vertical (a : ℂ) (t : ℝ) (ht : 0 < t) :
    affineMobius 1 (-a) one_ne_zero • Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint a t ht =
      mobiusVerticalPoint t ht := by
  apply Subtype.ext
  rw [affineMobius_smul]
  simp only [Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint_horizontal,
    Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint_height, one_mul,
    add_neg_cancel, norm_one, mobiusVerticalPoint]

/-- Fixing two distinct actual heights on the standard vertical ray forces both off-diagonal entries to vanish. -/
theorem specialLinear_two_vertical_points_offDiagonal_zero (A : Auxiliary.Algebra.SpecialLinear2)
    (h1 : mobiusSpecialLinearProjection A • mobiusVerticalPoint 1 zero_lt_one =
      mobiusVerticalPoint 1 zero_lt_one)
    (h2 : mobiusSpecialLinearProjection A • mobiusVerticalPoint 2 (by norm_num) =
      mobiusVerticalPoint 2 (by norm_num)) :
    A 0 1 = 0 ∧ A 1 0 = 0 ∧ A 1 1 = conj (A 0 0) := by
  have hfirst := (specialLinear_vertical_fixed_iff A 1 zero_lt_one).mp h1
  have hsecond := (specialLinear_vertical_fixed_iff A 2 (by norm_num)).mp h2
  have hcstar : conj (A 1 0) = 0 := by
    norm_num at hfirst hsecond
    linear_combination (1 / 3 : ℂ) * hsecond.2 - (1 / 3 : ℂ) * hfirst.2
  have hc : A 1 0 = 0 := (map_eq_zero (starRingEnd ℂ)).mp hcstar
  refine ⟨?_, hc, hfirst.1⟩
  rw [hc, map_zero, neg_zero, zero_mul] at hfirst
  exact hfirst.2

/-- If the true axis is a vertical ray, its translated conjugate fixes every standard positive height. -/
theorem mobius_axis_vertical_conjugate_fixed (f : complexMobiusGroup) (a : ℂ)
    (ha : ∀ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, q ∈ mobiusAxis f ↔
      Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val = a)
    (t : ℝ) (ht : 0 < t) :
    (affineMobius 1 (-a) one_ne_zero * f * (affineMobius 1 (-a) one_ne_zero)⁻¹) •
      mobiusVerticalPoint t ht = mobiusVerticalPoint t ht := by
  let q := affineMobius 1 (-a) one_ne_zero
  have hp : f • Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint a t ht =
    Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint a t ht :=
    (ha (Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint a t ht)).mpr
      (Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint_horizontal a t ht)
  rw [← affineMobius_translate_vertical a t ht]
  change (q * f * q⁻¹) • (q • Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint a t ht) = q •
    Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint a t ht
  rw [mul_smul, mul_smul, inv_smul_smul, hp]

/-- A nonidentity map fixing zero and infinity has precisely those two actual boundary fixed points. -/
theorem mobius_boundary_fixed_iff_zero_infty (f : complexMobiusGroup) (hf : f ≠ 1)
    (h0 : f.val (0 : ℂ) = (0 : ℂ)) (hi : f.val ∞ = ∞) (z : ExtendedComplex) :
    f.val z = z ↔ z = (0 : ℂ) ∨ z = ∞ := by
  constructor
  · intro hz
    by_cases hz0 : z = (0 : ℂ)
    · exact Or.inl hz0
    by_cases hzi : z = ∞
    · exact Or.inr hzi
    exact False.elim (hf (mobius_eq_one_of_three_fixed f (0 : ℂ) ∞ z
      (OnePoint.coe_ne_infty 0) (Ne.symm hz0) (Ne.symm hzi) h0 hi hz))
  · rintro (rfl | rfl)
    · exact h0
    · exact hi

/-- The endpoints of an actual vertical elliptic axis are exactly its finite base point and infinity. -/
theorem mobius_axis_vertical_boundary_fixed_iff (f : complexMobiusGroup) (hf : f ≠ 1) (a : ℂ)
    (ha : ∀ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, q ∈ mobiusAxis f ↔
      Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val = a)
    (z : ExtendedComplex) : f.val z = z ↔ z = (a : ExtendedComplex) ∨ z = ∞ := by
  let q := affineMobius 1 (-a) one_ne_zero
  let F := q * f * q⁻¹
  obtain ⟨A, hA⟩ := mobiusSpecialLinearProjection_surjective F
  have h1 : mobiusSpecialLinearProjection A • mobiusVerticalPoint 1 zero_lt_one =
      mobiusVerticalPoint 1 zero_lt_one := by
    rw [hA]
    exact mobius_axis_vertical_conjugate_fixed f a ha 1 zero_lt_one
  have h2 : mobiusSpecialLinearProjection A • mobiusVerticalPoint 2 (by norm_num) =
      mobiusVerticalPoint 2 (by norm_num) := by
    rw [hA]
    exact mobius_axis_vertical_conjugate_fixed f a ha 2 (by norm_num)
  obtain ⟨hb, hc, _⟩ := specialLinear_two_vertical_points_offDiagonal_zero A h1 h2
  have hF0 : F ≠ 1 := by
    intro he
    apply hf
    calc
      f = q⁻¹ * (q * f * q⁻¹) * q := by group
      _ = q⁻¹ * 1 * q := by rw [show q * f * q⁻¹ = 1 from he]
      _ = 1 := by group
  have hz0 : F.val (0 : ℂ) = (0 : ℂ) := by
    rw [← hA]
    change fractionalLinear (Matrix.SpecialLinearGroup.toGL A) (0 : ℂ) = (0 : ℂ)
    apply (Mobius.Classification.fractionalLinear_fixed_coe_iff _ 0).mpr
    change A 1 0 * (0 * 0) + (A 1 1 - A 0 0) * 0 + (-A 0 1) = 0
    simp only [hb, mul_zero, zero_add, neg_zero]
  have hzi : F.val ∞ = ∞ := by
    rw [← hA]
    change fractionalLinear (Matrix.SpecialLinearGroup.toGL A) ∞ = ∞
    rw [fractionalLinear_infty]
    change (if A 1 0 = 0 then ∞ else ((A 0 0 / A 1 0 : ℂ) : ExtendedComplex)) = ∞
    rw [ite_eq_left hc]
  have hqa : q.val (a : ExtendedComplex) = (0 : ℂ) := by
    change (affineMobius 1 (-a) one_ne_zero : Equiv.Perm ExtendedComplex) a = (0 : ℂ)
    rw [affineMobius_coe]
    change ((1 * a + -a : ℂ) : ExtendedComplex) = (0 : ℂ)
    simp only [one_mul, add_neg_cancel]
  have hqi : q.val ∞ = ∞ := by
    change (affineMobius 1 (-a) one_ne_zero : Equiv.Perm ExtendedComplex) ∞ = ∞
    rw [affineMobius_coe]
    exact affineHomeomorph_infty 1 (-a) one_ne_zero
  have hbound := mobius_boundary_fixed_iff_zero_infty F hF0 hz0 hzi (q.val z)
  change (q * f * q⁻¹).val (q.val z) = q.val z ↔ q.val z = (0 : ℂ) ∨ q.val z = ∞ at hbound
  rw [mobius_conjugate_boundary_fixed_iff, Equiv.symm_apply_apply, ← hqa, ← hqi] at hbound
  simpa only [q.val.injective.eq_iff] using hbound

/-- A true vertical upper-half-space axis extends to precisely the complete signed Euclidean line and infinity. -/
theorem mobius_extended_fixed_iff_of_vertical_axis (f : complexMobiusGroup) (hf : f ≠ 1) (a : ℂ)
    (ha : ∀ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, q ∈ mobiusAxis f ↔
      Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val = a)
    (w : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    w ∈ mobiusExtendedFixedPoints f ↔
      w = ∞ ∨ ∃ t : ℝ, w = (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint a t : OnePoint
        Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) := by
  constructor
  · intro hw
    rw [mobiusExtendedFixedPoints_axis_decomposition] at hw
    rcases hw with ((⟨p, hp, rfl⟩ | ⟨v, ⟨p, hp, rfl⟩, rfl⟩) | ⟨z, hz, rfl⟩)
    · refine Or.inr ⟨Hyperbolic.QuaternionHalfSpace.quaternionHeight p.val, ?_⟩
      rw [← (ha p).mp hp, Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates]
    · rw [mobiusBoundaryReflection_coe]
      exact Or.inr ⟨-Hyperbolic.QuaternionHalfSpace.quaternionHeight p.val, by rw [(ha p).mp hp]⟩
    · rcases (mobius_axis_vertical_boundary_fixed_iff f hf a ha z).mp hz with rfl | rfl
      · exact Or.inr ⟨0, Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding_coe a⟩
      · exact Or.inl rfl
  · rintro (rfl | ⟨t, rfl⟩)
    · exact (mobiusExtendedFixedPoints_boundary_iff f ∞).mpr
        ((mobius_axis_vertical_boundary_fixed_iff f hf a ha ∞).mpr (Or.inr rfl))
    · rcases lt_trichotomy t 0 with ht | ht | ht
      · let p := Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint a (-t) (neg_pos.mpr ht)
        have hp : p ∈ mobiusAxis f := (ha p).mpr (Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint_horizontal a
          (-t) _)
        have hfix := (mobiusBoundaryReflection_fixed_iff f (p.val : OnePoint
          Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)).mpr
          ((mobiusExtendedFixedPoints_interior_iff f p).mpr hp)
        simpa only [mobiusBoundaryReflection_coe, p, Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint_horizontal,
          Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint_height, neg_neg] using hfix
      · subst t
        exact (mobiusExtendedFixedPoints_boundary_iff f (a : ℂ)).mpr
          ((mobius_axis_vertical_boundary_fixed_iff f hf a ha a).mpr (Or.inl rfl))
      · exact (mobiusExtendedFixedPoints_interior_iff f (Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint a t ht)).mpr
          ((ha _).mpr (Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint_horizontal a t ht))

/-- Native horizontal projection is exactly zeroing the quaternion height in the fixed Euclidean chart. -/
theorem euclideanThreeQuaternion_horizontalPart (x : Inversive.Euclidean 3) :
    Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion (Hyperbolic.halfSpaceHorizontalPart x) =
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal
        (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x)) 0 := by
  apply Subtype.ext
  apply Quaternion.ext <;>
    simp [Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion, Hyperbolic.halfSpaceHorizontalPart,
      Hyperbolic.halfSpaceHeight,
      Hyperbolic.halfSpaceVerticalUnit, Hyperbolic.QuaternionHalfSpace.quaternionThreePoint,
        Hyperbolic.QuaternionHalfSpace.quaternionHorizontal]

/-- The native Euclidean vertical-axis alternative gives the literal quaternion horizontal-coordinate alternative. -/
theorem mobius_axis_native_vertical_to_quaternion (f : complexMobiusGroup) (v : Inversive.Euclidean 3)
    (hv : Hyperbolic.halfSpaceHeight 2 v = 0)
    (haxis : ∀ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, q ∈ mobiusAxis f ↔
      Hyperbolic.halfSpaceHorizontalPart (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val) = v) :
    ∃ a : ℂ, ∀ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, q ∈ mobiusAxis f ↔
      Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val = a := by
  let a := Hyperbolic.QuaternionHalfSpace.quaternionHorizontal
    (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion v)
  have hvq : Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion v =
    Hyperbolic.QuaternionHalfSpace.quaternionThreePoint a 0 := by
    have hh : Hyperbolic.QuaternionHalfSpace.quaternionHeight
      (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion v) = 0 := hv
    rw [← Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates
      (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion v), hh]
  refine ⟨a, ?_⟩
  intro q
  rw [haxis q]
  constructor
  · intro he
    have h := congrArg Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion he
    rw [euclideanThreeQuaternion_horizontalPart, LinearIsometryEquiv.apply_symm_apply, hvq] at h
    simpa only [Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint] using congrArg
      Hyperbolic.QuaternionHalfSpace.quaternionHorizontal h
  · intro he
    apply Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.injective
    rw [euclideanThreeQuaternion_horizontalPart, LinearIsometryEquiv.apply_symm_apply, hvq, he]



/-- The actual Euclidean vertical-plane chart in quaternion coordinates. -/
def mobiusNativePlanePoint (x u : Inversive.Euclidean 3) (z : ℂ) :
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace :=
  Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion (Hyperbolic.halfSpacePlaneEmbed x u z)

theorem mobiusNativePlanePoint_continuous (x u : Inversive.Euclidean 3) :
    Continuous (mobiusNativePlanePoint x u) := by
  unfold mobiusNativePlanePoint Hyperbolic.halfSpacePlaneEmbed
  exact Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.continuous.comp
    (continuous_const.add (Hyperbolic.halfSpacePlaneEmbedCLM u).continuous)

theorem mobiusNativePlanePoint_height (x u : Inversive.Euclidean 3)
    (hu0 : Hyperbolic.halfSpaceHeight 2 u = 0) (z : ℂ) :
    Hyperbolic.QuaternionHalfSpace.quaternionHeight (mobiusNativePlanePoint x u z) = z.im := by
  rw [← euclideanThreeQuaternion_symm_height]
  change Hyperbolic.halfSpaceHeight 2 (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm
    (mobiusNativePlanePoint x u z)) = _
  rw [mobiusNativePlanePoint, Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm_apply_apply]
  exact Hyperbolic.halfSpacePlaneEmbed_height x u hu0 z

/-- The literal positive semicircle parameter, including its two limiting boundary endpoints. -/
def mobiusSemicircleParam (c r s : ℝ) : ℂ :=
  ((c + s : ℝ) : ℂ) + (Real.sqrt (r ^ 2 - s ^ 2) : ℂ) * Complex.I

theorem mobiusSemicircleParam_continuous (c r : ℝ) :
    Continuous (mobiusSemicircleParam c r) := by
  unfold mobiusSemicircleParam
  fun_prop

theorem mobiusSemicircleParam_im_pos (c r s : ℝ) (_hr : 0 < r)
    (hs : s ∈ Set.Ioo (-r) r) : 0 < (mobiusSemicircleParam c r s).im := by
  simp only [mobiusSemicircleParam, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, zero_add, add_zero]
  apply Real.sqrt_pos.mpr
  nlinarith [mul_pos (sub_pos.mpr hs.2) (by linarith [hs.1] : 0 < r + s)]

theorem mobiusSemicircleParam_norm (c r s : ℝ) (hr : 0 < r)
    (hs : s ∈ Set.Icc (-r) r) : ‖mobiusSemicircleParam c r s - (c : ℂ)‖ = r := by
  have hs2 : 0 ≤ r ^ 2 - s ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) (by linarith [hs.1] : 0 ≤ r + s)]
  apply (sq_eq_sq₀ (norm_nonneg _) hr.le).mp
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [mobiusSemicircleParam, Complex.sub_re, Complex.add_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, add_zero, Complex.sub_im, Complex.add_im,
    Complex.mul_im, mul_one, zero_add]
  nlinarith [Real.sq_sqrt hs2]

@[simp] theorem mobiusSemicircleParam_left (c r : ℝ) :
    mobiusSemicircleParam c r (-r) = ((c - r : ℝ) : ℂ) := by
  simp [mobiusSemicircleParam, sub_eq_add_neg]

@[simp] theorem mobiusSemicircleParam_right (c r : ℝ) :
    mobiusSemicircleParam c r r = ((c + r : ℝ) : ℂ) := by
  simp [mobiusSemicircleParam]

/-- A true fixed set is closed on the actual compactified Euclidean three-space. -/
theorem mobiusExtendedFixedPoints_isClosed (f : complexMobiusGroup) :
    IsClosed (mobiusExtendedFixedPoints f) :=
  isClosed_eq (mobiusExtendedSpaceHom f).continuous continuous_id

/-- The two actual zero-height endpoints of an elliptic semicircular axis are genuine full-space fixed points. -/
theorem mobius_semicircle_axis_endpoints_fixed (f : complexMobiusGroup)
    (x u : Inversive.Euclidean 3) (hu : ‖u‖ = 1) (hu0 : Hyperbolic.halfSpaceHeight 2 u = 0)
    (c r : ℝ) (hr : 0 < r)
    (haxis : ∀ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, q ∈ mobiusAxis f ↔
      Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val ∈ Set.range
        (Hyperbolic.halfSpacePlaneEmbed x u) ∧
      ‖Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val - Hyperbolic.halfSpacePlaneEmbed x u (c
        : ℂ)‖ = r) :
    (mobiusNativePlanePoint x u ((c-r : ℝ) : ℂ) : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) ∈
      mobiusExtendedFixedPoints f ∧
    (mobiusNativePlanePoint x u ((c+r : ℝ) : ℂ) : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) ∈
      mobiusExtendedFixedPoints f := by
  let γ : ℝ → OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace := fun s =>
    (mobiusNativePlanePoint x u (mobiusSemicircleParam c r s) : OnePoint
      Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)
  have hc : Continuous γ := OnePoint.continuous_coe.comp
    ((mobiusNativePlanePoint_continuous x u).comp (mobiusSemicircleParam_continuous c r))
  have hclosed : IsClosed (γ ⁻¹' mobiusExtendedFixedPoints f) :=
    (mobiusExtendedFixedPoints_isClosed f).preimage hc
  have hsub : Set.Ioo (-r) r ⊆ γ ⁻¹' mobiusExtendedFixedPoints f := by
    intro s hs
    have ht : 0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight (mobiusNativePlanePoint x u
      (mobiusSemicircleParam c r s)) := by
      rw [mobiusNativePlanePoint_height x u hu0]
      exact mobiusSemicircleParam_im_pos c r s hr hs
    let q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace := ⟨mobiusNativePlanePoint x u (mobiusSemicircleParam c
      r s), ht⟩
    apply (mobiusExtendedFixedPoints_interior_iff f q).mpr
    apply (haxis q).mpr
    change Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm
      (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion _) ∈ _ ∧
      ‖Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm
        (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion _) - _‖ = r
    rw [Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm_apply_apply]
    refine ⟨⟨mobiusSemicircleParam c r s, rfl⟩, ?_⟩
    have hn := Hyperbolic.halfSpacePlaneEmbed_dist x u hu hu0 (mobiusSemicircleParam c r s) (c : ℂ)
    rw [dist_eq_norm, dist_eq_norm] at hn
    rw [hn]
    exact mobiusSemicircleParam_norm c r s hr ⟨hs.1.le, hs.2.le⟩
  have hs := closure_minimal hsub hclosed
  rw [closure_Ioo (by linarith : -r ≠ r)] at hs
  have hl := hs (show -r ∈ Set.Icc (-r) r from ⟨le_rfl, by linarith⟩)
  have hr' := hs (show r ∈ Set.Icc (-r) r from ⟨by linarith, le_rfl⟩)
  simpa only [Set.mem_preimage, γ, mobiusSemicircleParam_left, mobiusSemicircleParam_right] using And.intro hl hr'


/-- Reflection in the true boundary plane is complex conjugation in each actual vertical-plane chart. -/
theorem mobiusNativePlanePoint_reflection (x u : Inversive.Euclidean 3)
    (hu0 : Hyperbolic.halfSpaceHeight 2 u = 0) (z : ℂ) :
    mobiusBoundaryReflection (mobiusNativePlanePoint x u z : OnePoint
      Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
      (mobiusNativePlanePoint x u (conj z) : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) := by
  rw [mobiusBoundaryReflection_coe]
  apply congrArg ((↑) : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace → OnePoint
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)
  rw [mobiusNativePlanePoint, ← cayley_plane_reflection_coordinates]
  change Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion (Inversive.planeReflectionFinite
    (Inversive.northPole 2) 0 (Hyperbolic.halfSpacePlaneEmbed x u z)) =
    Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion (Hyperbolic.halfSpacePlaneEmbed x u (conj z))
  apply congrArg Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion
  change Inversive.planeReflectionFinite (Inversive.northPole 2) 0 (Hyperbolic.halfSpacePlaneEmbed x u z) =
    Hyperbolic.halfSpacePlaneEmbed x u (conj z)
  have hn : Inversive.northPole 2 = Hyperbolic.halfSpaceVerticalUnit 2 := rfl
  rw [Inversive.planeReflectionFinite, hn, Hyperbolic.inner_halfSpaceVerticalUnit,
    Hyperbolic.halfSpacePlaneEmbed_height x u hu0, Hyperbolic.halfSpaceVerticalUnit_norm]
  simp only [sub_zero, one_pow, div_one, Hyperbolic.halfSpacePlaneEmbed, Hyperbolic.halfSpacePlaneEmbedCLM,
    Hyperbolic.twoPlaneEmbedCLM_apply, Complex.conj_re, Complex.conj_im, neg_smul]
  module

/-- Every real coordinate of a genuine vertical plane lies on the actual complex boundary. -/
theorem mobiusNativePlanePoint_real_boundary (x u : Inversive.Euclidean 3)
    (hu0 : Hyperbolic.halfSpaceHeight 2 u = 0) (s : ℝ) :
    Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal
      (mobiusNativePlanePoint x u (s : ℂ)) : ℂ) =
      (mobiusNativePlanePoint x u (s : ℂ) : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) := by
  rw [Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding_coe]
  apply congrArg ((↑) : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace → OnePoint
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)
  have ht : Hyperbolic.QuaternionHalfSpace.quaternionHeight (mobiusNativePlanePoint x u (s : ℂ)) = 0 := by
    rw [mobiusNativePlanePoint_height x u hu0]
    rfl
  simpa only [ht] using Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates (mobiusNativePlanePoint x
    u (s : ℂ))

/-- The Euclidean plane chart is injective because its linear part is an isometry. -/
theorem mobiusNativePlanePoint_injective (x u : Inversive.Euclidean 3)
    (hu : ‖u‖ = 1) (hu0 : Hyperbolic.halfSpaceHeight 2 u = 0) :
    Function.Injective (mobiusNativePlanePoint x u) := by
  intro z w he
  have hp := Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.injective he
  have hh := congrArg (Hyperbolic.halfSpacePlaneProject x u) hp
  simpa only [Hyperbolic.halfSpacePlaneProject_embed x u hu hu0] using hh

/-- The positive part of the actual plane circle is exactly an elliptic semicircular fixed axis. -/
theorem mobius_semicircle_positive_fixed (f : complexMobiusGroup)
    (x u : Inversive.Euclidean 3) (hu : ‖u‖ = 1) (hu0 : Hyperbolic.halfSpaceHeight 2 u = 0)
    (c r : ℝ)
    (haxis : ∀ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, q ∈ mobiusAxis f ↔
      Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val ∈ Set.range
        (Hyperbolic.halfSpacePlaneEmbed x u) ∧
      ‖Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val - Hyperbolic.halfSpacePlaneEmbed x u (c
        : ℂ)‖ = r)
    (z : ℂ) (hz : 0 < z.im) (hn : ‖z - (c : ℂ)‖ = r) :
    (mobiusNativePlanePoint x u z : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) ∈
      mobiusExtendedFixedPoints f := by
  have ht : 0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight (mobiusNativePlanePoint x u z) := by
    rwa [mobiusNativePlanePoint_height x u hu0]
  let q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace := ⟨mobiusNativePlanePoint x u z, ht⟩
  apply (mobiusExtendedFixedPoints_interior_iff f q).mpr
  apply (haxis q).mpr
  change Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm
    (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion _) ∈ _ ∧
    ‖Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm
      (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion _) - _‖ = r
  rw [Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm_apply_apply]
  refine ⟨⟨z, rfl⟩, ?_⟩
  have hh := Hyperbolic.halfSpacePlaneEmbed_dist x u hu hu0 z (c : ℂ)
  rw [dist_eq_norm, dist_eq_norm] at hh
  exact hh.trans hn

/-- The two real boundary points on a positive-radius plane circle are its literal endpoints. -/
theorem complex_circle_zero_im_endpoints (c r : ℝ) (_hr : 0 < r) (z : ℂ)
    (hzi : z.im = 0) (hn : ‖z - (c : ℂ)‖ = r) :
    z = ((c - r : ℝ) : ℂ) ∨ z = ((c + r : ℝ) : ℂ) := by
  have hsq := congrArg (fun a : ℝ => a ^ 2) hn
  rw [Complex.sq_norm, Complex.normSq_apply] at hsq
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    hzi, sub_zero, mul_zero, add_zero] at hsq
  have hh : (z.re - c) ^ 2 = r ^ 2 := by nlinarith
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp hh with he | he
  · right
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      linarith
    · simpa only [Complex.ofReal_im] using hzi
  · left
    apply Complex.ext
    · simp only [Complex.ofReal_re]
      linarith
    · simpa only [Complex.ofReal_im] using hzi


/-- A semicircular actual axis has exactly its two literal endpoints as boundary fixed points. -/
theorem mobius_semicircle_axis_boundary_fixed_iff (f : complexMobiusGroup) (hf : f ≠ 1)
    (x u : Inversive.Euclidean 3) (hu : ‖u‖ = 1) (hu0 : Hyperbolic.halfSpaceHeight 2 u = 0)
    (c r : ℝ) (hr : 0 < r)
    (haxis : ∀ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, q ∈ mobiusAxis f ↔
      Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val ∈ Set.range
        (Hyperbolic.halfSpacePlaneEmbed x u) ∧
      ‖Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val - Hyperbolic.halfSpacePlaneEmbed x u (c
        : ℂ)‖ = r)
    (z : ExtendedComplex) :
    f.val z = z ↔
      z = (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal (mobiusNativePlanePoint x u ((c-r : ℝ) : ℂ)) : ℂ) ∨
      z = (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal (mobiusNativePlanePoint x u ((c+r : ℝ) : ℂ)) : ℂ) := by
  let a : ℂ := Hyperbolic.QuaternionHalfSpace.quaternionHorizontal (mobiusNativePlanePoint x u ((c-r : ℝ) : ℂ))
  let b : ℂ := Hyperbolic.QuaternionHalfSpace.quaternionHorizontal (mobiusNativePlanePoint x u ((c+r : ℝ) : ℂ))
  have ha := mobiusNativePlanePoint_real_boundary x u hu0 (c-r)
  have hb := mobiusNativePlanePoint_real_boundary x u hu0 (c+r)
  obtain ⟨hla, hra⟩ := mobius_semicircle_axis_endpoints_fixed f x u hu hu0 c r hr haxis
  have hfa : f.val (a : ExtendedComplex) = a := by
    apply (mobiusExtendedFixedPoints_boundary_iff f (a : ExtendedComplex)).mp
    simpa only [a, ha] using hla
  have hfb : f.val (b : ExtendedComplex) = b := by
    apply (mobiusExtendedFixedPoints_boundary_iff f (b : ExtendedComplex)).mp
    simpa only [b, hb] using hra
  have hab : (a : ExtendedComplex) ≠ b := by
    intro he
    have hp := congrArg Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding he
    rw [ha, hb, OnePoint.coe_eq_coe] at hp
    have hh := mobiusNativePlanePoint_injective x u hu hu0 hp
    have hre := congrArg Complex.re hh
    simp only [Complex.ofReal_re] at hre
    linarith
  constructor
  · intro hz
    by_cases hza : z = (a : ExtendedComplex)
    · exact Or.inl hza
    by_cases hzb : z = (b : ExtendedComplex)
    · exact Or.inr hzb
    exact False.elim (hf (mobius_eq_one_of_three_fixed f z a b hza hzb hab hz hfa hfb))
  · rintro (rfl | rfl)
    · exact hfa
    · exact hfb

/-- Every interior point of a genuine semicircular axis has its actual isometric complex-plane coordinate. -/
theorem mobius_semicircle_axis_coordinates (f : complexMobiusGroup)
    (x u : Inversive.Euclidean 3) (hu : ‖u‖ = 1) (hu0 : Hyperbolic.halfSpaceHeight 2 u = 0)
    (c r : ℝ)
    (haxis : ∀ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, q ∈ mobiusAxis f ↔
      Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val ∈ Set.range
        (Hyperbolic.halfSpacePlaneEmbed x u) ∧
      ‖Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val - Hyperbolic.halfSpacePlaneEmbed x u (c
        : ℂ)‖ = r)
    (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) (hq : q ∈ mobiusAxis f) :
    ∃ z : ℂ, ‖z - (c : ℂ)‖ = r ∧ mobiusNativePlanePoint x u z = q.val := by
  obtain ⟨⟨z, hz⟩, hn⟩ := (haxis q).mp hq
  have he : mobiusNativePlanePoint x u z = q.val := by
    unfold mobiusNativePlanePoint
    rw [hz, Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply]
  refine ⟨z, ?_, he⟩
  have hd := Hyperbolic.halfSpacePlaneEmbed_dist x u hu hu0 z (c : ℂ)
  rw [dist_eq_norm, dist_eq_norm, hz] at hd
  exact hd.symm.trans hn

/-- The entire three-dimensional fixed set is a literal positive-radius Euclidean circle in a vertical isometric plane, with centre on the boundary. -/
theorem mobius_extended_fixed_of_semicircle_axis (f : complexMobiusGroup) (hf : f ≠ 1)
    (x u : Inversive.Euclidean 3) (hu : ‖u‖ = 1) (hu0 : Hyperbolic.halfSpaceHeight 2 u = 0)
    (c r : ℝ) (hr : 0 < r)
    (haxis : ∀ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, q ∈ mobiusAxis f ↔
      Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val ∈ Set.range
        (Hyperbolic.halfSpacePlaneEmbed x u) ∧
      ‖Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val - Hyperbolic.halfSpacePlaneEmbed x u (c
        : ℂ)‖ = r) :
    mobiusExtendedFixedPoints f =
      (fun z : ℂ => (mobiusNativePlanePoint x u z : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)) ''
        {z : ℂ | ‖z - (c : ℂ)‖ = r} := by
  have hl := (mobius_semicircle_axis_endpoints_fixed f x u hu hu0 c r hr haxis).1
  have hr' := (mobius_semicircle_axis_endpoints_fixed f x u hu hu0 c r hr haxis).2
  have hnorml : ‖(((c-r : ℝ) : ℂ) - (c : ℂ))‖ = r := by
    simpa only [mobiusSemicircleParam_left] using
      mobiusSemicircleParam_norm c r (-r) hr ⟨le_rfl, by linarith⟩
  have hnormr : ‖(((c+r : ℝ) : ℂ) - (c : ℂ))‖ = r := by
    simpa only [mobiusSemicircleParam_right] using
      mobiusSemicircleParam_norm c r r hr ⟨by linarith, le_rfl⟩
  have hnormconj (z : ℂ) (hz : ‖z - (c : ℂ)‖ = r) : ‖conj z - (c : ℂ)‖ = r := by
    have he : conj z - (c : ℂ) = conj (z - (c : ℂ)) := by simp
    rw [he, Complex.norm_conj]
    exact hz
  ext w
  constructor
  · intro hw
    rw [mobiusExtendedFixedPoints_axis_decomposition] at hw
    rcases hw with (⟨q, hq, rfl⟩ | ⟨_, ⟨q, hq, rfl⟩, rfl⟩) | ⟨z, hz, rfl⟩
    · obtain ⟨z, hn, he⟩ := mobius_semicircle_axis_coordinates f x u hu hu0 c r haxis q hq
      exact ⟨z, hn, congrArg ((↑) : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace → OnePoint
        Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) he⟩
    · obtain ⟨z, hn, he⟩ := mobius_semicircle_axis_coordinates f x u hu hu0 c r haxis q hq
      refine ⟨conj z, hnormconj z hn, ?_⟩
      change (mobiusNativePlanePoint x u (conj z) : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
        mobiusBoundaryReflection (q.val : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)
      rw [← he, mobiusNativePlanePoint_reflection x u hu0]
    · rcases (mobius_semicircle_axis_boundary_fixed_iff f hf x u hu hu0 c r hr haxis z).mp hz with he | he
      · rw [he, mobiusNativePlanePoint_real_boundary x u hu0]
        exact ⟨((c-r : ℝ) : ℂ), hnorml, rfl⟩
      · rw [he, mobiusNativePlanePoint_real_boundary x u hu0]
        exact ⟨((c+r : ℝ) : ℂ), hnormr, rfl⟩
  · rintro ⟨z, hn, rfl⟩
    rcases lt_trichotomy 0 z.im with hz | hz | hz
    · exact mobius_semicircle_positive_fixed f x u hu hu0 c r haxis z hz hn
    · rcases complex_circle_zero_im_endpoints c r hr z hz.symm hn with rfl | rfl
      · exact hl
      · exact hr'
    · have hcpos : 0 < (conj z).im := by simpa only [Complex.conj_im] using neg_pos.mpr hz
      have hfix := mobius_semicircle_positive_fixed f x u hu hu0 c r haxis (conj z) hcpos (hnormconj z hn)
      have hrfix := (mobiusBoundaryReflection_fixed_iff f _).mpr hfix
      rw [mobiusNativePlanePoint_reflection x u hu0] at hrfix
      simpa only [starRingEnd_self_apply] using hrfix



/-- The whole elliptic fixed set is a literal generalized Euclidean circle orthogonal to the complex boundary plane. -/
theorem MobiusElliptic.full_fixed_generalized_circle {f : complexMobiusGroup} (hf : MobiusElliptic f) :
    (∃ a : ℂ, mobiusExtendedFixedPoints f =
      {w : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace | w = ∞ ∨
        ∃ t : ℝ, w = (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint a t : OnePoint
          Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)}) ∨
    ∃ x u : Inversive.Euclidean 3, ‖u‖ = 1 ∧ Hyperbolic.halfSpaceHeight 2 u = 0 ∧
      ∃ c r : ℝ, 0 < r ∧ mobiusExtendedFixedPoints f =
        (fun z : ℂ => (mobiusNativePlanePoint x u z : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)) ''
          {z : ℂ | ‖z - (c : ℂ)‖ = r} := by
  rcases hf.axis_semicircle_or_vertical with ⟨v, hv, haxis⟩ | ⟨x, u, hu, hu0, c, r, hr, haxis⟩
  · obtain ⟨a, ha⟩ := mobius_axis_native_vertical_to_quaternion f v hv haxis
    exact Or.inl ⟨a, Set.ext (mobius_extended_fixed_iff_of_vertical_axis f hf.1 a ha)⟩
  · exact Or.inr ⟨x, u, hu, hu0, c, r, hr,
      mobius_extended_fixed_of_semicircle_axis f hf.1 x u hu hu0 c r hr haxis⟩


/-- The actual Euclidean plane-circle parametrization has the derivative given by its genuine linear plane embedding. -/
theorem halfSpacePlaneCircle_hasDerivAt {n : ℕ} (x u : Inversive.Euclidean (n + 1)) (c r θ : ℝ) :
    HasDerivAt (fun t : ℝ => Hyperbolic.halfSpacePlaneEmbed x u (circleMap (c : ℂ) r t))
      (Hyperbolic.halfSpacePlaneEmbedCLM u (circleMap 0 r θ * Complex.I)) θ := by
  exact (Hyperbolic.halfSpacePlaneEmbed_hasFDerivAt x u _).comp_hasDerivAt θ
    (hasDerivAt_circleMap (c : ℂ) r θ)

/-- At the first genuine boundary endpoint, the circle tangent is the upward vertical radius vector. -/
theorem halfSpacePlaneCircle_hasDerivAt_zero {n : ℕ} (x u : Inversive.Euclidean (n + 1)) (c r : ℝ) :
    HasDerivAt (fun t : ℝ => Hyperbolic.halfSpacePlaneEmbed x u (circleMap (c : ℂ) r t))
      (r • Hyperbolic.halfSpaceVerticalUnit n) 0 := by
  simpa [circleMap, Hyperbolic.halfSpacePlaneEmbedCLM, Hyperbolic.twoPlaneEmbedCLM_apply] using
    halfSpacePlaneCircle_hasDerivAt x u c r 0

/-- At the opposite genuine boundary endpoint, the circle tangent is the downward vertical radius vector. -/
theorem halfSpacePlaneCircle_hasDerivAt_pi {n : ℕ} (x u : Inversive.Euclidean (n + 1)) (c r : ℝ) :
    HasDerivAt (fun t : ℝ => Hyperbolic.halfSpacePlaneEmbed x u (circleMap (c : ℂ) r t))
      ((-r) • Hyperbolic.halfSpaceVerticalUnit n) Real.pi := by
  simpa [circleMap, Complex.exp_pi_mul_I, Hyperbolic.halfSpacePlaneEmbedCLM,
    Hyperbolic.twoPlaneEmbedCLM_apply] using halfSpacePlaneCircle_hasDerivAt x u c r Real.pi

/-- Both endpoints of a real-centred plane circle lie on the actual zero-height boundary. -/
theorem halfSpacePlaneCircle_endpoints_height_zero {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (hu : Hyperbolic.halfSpaceHeight n u = 0) (c r : ℝ) :
    Hyperbolic.halfSpaceHeight n (Hyperbolic.halfSpacePlaneEmbed x u (circleMap (c : ℂ) r 0)) = 0 ∧
    Hyperbolic.halfSpaceHeight n (Hyperbolic.halfSpacePlaneEmbed x u (circleMap (c : ℂ) r Real.pi)) = 0 := by
  constructor <;> rw [Hyperbolic.halfSpacePlaneEmbed_height x u hu] <;>
    simp [circleMap, Complex.exp_pi_mul_I]

/-- Positive-radius circles meet the actual horizontal boundary orthogonally: both endpoint tangents are nonzero and perpendicular to every boundary direction. -/
theorem halfSpacePlaneCircle_endpoints_orthogonal {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (hu : Hyperbolic.halfSpaceHeight n u = 0) (c r : ℝ) (hr : 0 < r) :
    deriv (fun t : ℝ => Hyperbolic.halfSpacePlaneEmbed x u (circleMap (c : ℂ) r t)) 0 ≠ 0 ∧
    deriv (fun t : ℝ => Hyperbolic.halfSpacePlaneEmbed x u (circleMap (c : ℂ) r t)) Real.pi ≠ 0 ∧
    (∀ v : Inversive.Euclidean (n + 1), Hyperbolic.halfSpaceHeight n v = 0 →
      inner ℝ (deriv (fun t : ℝ => Hyperbolic.halfSpacePlaneEmbed x u (circleMap (c : ℂ) r t)) 0) v = 0 ∧
      inner ℝ (deriv (fun t : ℝ => Hyperbolic.halfSpacePlaneEmbed x u (circleMap (c : ℂ) r t)) Real.pi) v = 0) ∧
    Hyperbolic.halfSpaceHeight n (Hyperbolic.halfSpacePlaneEmbed x u (circleMap (c : ℂ) r 0)) = 0 ∧
    Hyperbolic.halfSpaceHeight n (Hyperbolic.halfSpacePlaneEmbed x u (circleMap (c : ℂ) r Real.pi)) = 0 := by
  rw [(halfSpacePlaneCircle_hasDerivAt_zero x u c r).deriv,
    (halfSpacePlaneCircle_hasDerivAt_pi x u c r).deriv]
  have hv : Hyperbolic.halfSpaceVerticalUnit n ≠ 0 := by
    intro he
    have hn := Hyperbolic.halfSpaceVerticalUnit_norm n
    rw [he, norm_zero] at hn
    exact zero_ne_one hn
  refine ⟨smul_ne_zero hr.ne' hv, smul_ne_zero (neg_ne_zero.mpr hr.ne') hv, ?_,
    halfSpacePlaneCircle_endpoints_height_zero x u hu c r⟩
  intro v hheight
  constructor <;> rw [inner_smul_left, Hyperbolic.halfSpaceVerticalUnit_inner, hheight, mul_zero]


end LowDimensionalTopology.Geometry.Mobius
