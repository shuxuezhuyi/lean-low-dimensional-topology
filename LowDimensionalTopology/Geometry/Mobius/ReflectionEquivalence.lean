/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.Orientation
public import LowDimensionalTopology.Geometry.Mobius.Circle.ComplexReflections
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.Conformal
public import LowDimensionalTopology.Geometry.Mobius.FractionalLinear
public import Mathlib.Analysis.Complex.OperatorNorm
/-!
# The complex Möbius group and actual orientation

The general reflection group is transported through the standard real isometric complex chart. Its positive real-Jacobian part is proved to be precisely the fractional-linear group. Both inclusions concern actual transformations of the whole one-point compactification, including every pole and infinity.

The orientation condition is a derivative condition on regular finite charts; it is not defined by reflection-word parity. The real two-dimensional and complex-coordinate conditions are proved equivalent.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint ComplexConjugate
open Filter Complex
namespace LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Auxiliary.Analysis LowDimensionalTopology.Geometry.Mobius

def finiteComplexPart (f : Equiv.Perm ExtendedComplex) (z : ℂ) : ℂ :=
  (f (z : ExtendedComplex)).elim 0 id

def PreservesComplexOrientation (f : Equiv.Perm ExtendedComplex) : Prop :=
  ∀ z : ℂ, f (z : ExtendedComplex) ≠ ∞ → Auxiliary.Analysis.directlyConformalAt (finiteComplexPart f) z

def complexConjugation : Equiv.Perm ExtendedComplex :=
  Complex.conjCLE.toHomeomorph.onePointCongr.toEquiv
@[simp] theorem complexConjugation_coe (z : ℂ) :
    complexConjugation z = (conj z : ℂ) := rfl
@[simp] theorem complexConjugation_infty : complexConjugation ∞ = ∞ := rfl

theorem complexConjugation_sq : complexConjugation * complexConjugation = 1 := by
  ext z
  induction z using OnePoint.rec <;> simp [Equiv.Perm.mul_apply]

theorem complexConjugation_twice (f : Equiv.Perm ExtendedComplex) :
    complexConjugation * (complexConjugation * f) = f := by
  rw [← mul_assoc, complexConjugation_sq, one_mul]

theorem complexConjugation_inv : complexConjugation⁻¹ = complexConjugation := by
  exact inv_eq_of_mul_eq_one_left complexConjugation_sq

theorem complexConjugation_fractionalLinear (g : FractionalLinearMatrix) :
    complexConjugation * fractionalLinear g =
      fractionalLinear (g.map (starRingEnd ℂ)) * complexConjugation := by
  ext z
  exact OnePoint.map_smul (starRingEnd ℂ) g z

theorem complexConjugation_normalizes {f : Equiv.Perm ExtendedComplex}
    (hf : f ∈ fractionalLinearGroup) :
    complexConjugation * f * complexConjugation ∈ fractionalLinearGroup := by
  obtain ⟨g, rfl⟩ := hf
  change complexConjugation * fractionalLinear g * complexConjugation ∈ _
  rw [complexConjugation_fractionalLinear, mul_assoc, complexConjugation_sq, mul_one]
  exact ⟨g.map (starRingEnd ℂ), rfl⟩

def fractionalOrAntiGroup : Subgroup (Equiv.Perm ExtendedComplex) where
  carrier := {f | f ∈ fractionalLinearGroup ∨ f * complexConjugation ∈ fractionalLinearGroup}
  one_mem' := Or.inl (one_mem _)
  mul_mem' {f g} hf hg := by
    rcases hf with hf | hf <;> rcases hg with hg | hg
    · exact Or.inl (fractionalLinearGroup.mul_mem hf hg)
    · exact Or.inr (by simpa only [mul_assoc] using fractionalLinearGroup.mul_mem hf hg)
    · apply Or.inr
      have hm := fractionalLinearGroup.mul_mem hf (complexConjugation_normalizes hg)
      simpa only [mul_assoc, complexConjugation_sq, complexConjugation_twice, one_mul] using hm
    · apply Or.inl
      have hm := fractionalLinearGroup.mul_mem hf (complexConjugation_normalizes hg)
      simpa only [mul_assoc, complexConjugation_sq, complexConjugation_twice, one_mul, mul_one] using hm
  inv_mem' {f} hf := by
    rcases hf with hf | hf
    · exact Or.inl (fractionalLinearGroup.inv_mem hf)
    · apply Or.inr
      have hm := complexConjugation_normalizes (fractionalLinearGroup.inv_mem hf)
      simpa only [mul_inv_rev, complexConjugation_inv, mul_assoc,
        complexConjugation_sq, complexConjugation_twice, one_mul] using hm

theorem mem_fractionalOrAntiGroup (f : Equiv.Perm ExtendedComplex) :
    f ∈ fractionalOrAntiGroup ↔
      f ∈ fractionalLinearGroup ∨ f * complexConjugation ∈ fractionalLinearGroup := Iff.rfl

theorem fractionalLinear_denominator_ne_zero (g : FractionalLinearMatrix) (z : ℂ)
    (hz : fractionalLinear g z ≠ ∞) : g 1 0 * z + g 1 1 ≠ 0 := by
  intro h
  apply hz
  simp [fractionalLinear_coe, h]

theorem finiteComplexPart_fractionalLinear (g : FractionalLinearMatrix) (z : ℂ)
    (hz : g 1 0 * z + g 1 1 ≠ 0) :
    finiteComplexPart (fractionalLinear g) z = (g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) := by
  simp [finiteComplexPart, fractionalLinear_coe, hz]

theorem fractionalLinear_hasDerivAt (g : FractionalLinearMatrix) (z : ℂ)
    (hz : g 1 0 * z + g 1 1 ≠ 0) :
    HasDerivAt (finiteComplexPart (fractionalLinear g))
      ((g 0 0 * g 1 1 - g 0 1 * g 1 0) / (g 1 0 * z + g 1 1) ^ 2) z := by
  have hq : HasDerivAt (fun w : ℂ ↦ (g 0 0 * w + g 0 1) / (g 1 0 * w + g 1 1))
      ((g 0 0 * g 1 1 - g 0 1 * g 1 0) / (g 1 0 * z + g 1 1) ^ 2) z := by
    convert! (((hasDerivAt_id z).const_mul (g 0 0)).add_const (g 0 1)).div
      (((hasDerivAt_id z).const_mul (g 1 0)).add_const (g 1 1)) hz using 2
    ring
  apply hq.congr_of_eventuallyEq
  have he : ∀ᶠ w : ℂ in 𝓝 z, g 1 0 * w + g 1 1 ≠ 0 :=
    (by fun_prop : ContinuousAt (fun w : ℂ ↦ g 1 0 * w + g 1 1) z).eventually_ne hz
  filter_upwards [he] with w hw
  exact finiteComplexPart_fractionalLinear g w hw

theorem fractionalLinear_derivative_ne_zero (g : FractionalLinearMatrix) (z : ℂ)
    (hz : g 1 0 * z + g 1 1 ≠ 0) :
    (g 0 0 * g 1 1 - g 0 1 * g 1 0) / (g 1 0 * z + g 1 1) ^ 2 ≠ 0 := by
  apply div_ne_zero
  · simpa [Matrix.det_fin_two] using g.det_ne_zero
  · exact pow_ne_zero _ hz

theorem fractionalLinear_preserves_orientation (g : FractionalLinearMatrix) :
    PreservesComplexOrientation (fractionalLinear g) := by
  intro z hz
  have hden := fractionalLinear_denominator_ne_zero g z hz
  have hd := fractionalLinear_hasDerivAt g z hden
  apply Auxiliary.Analysis.complexDifferentiable_directlyConformalAt hd.differentiableAt
  rw [hd.deriv]
  exact fractionalLinear_derivative_ne_zero g z hden

theorem finiteComplexPart_anti (g : FractionalLinearMatrix) :
    finiteComplexPart (fractionalLinear g * complexConjugation) =
      finiteComplexPart (fractionalLinear g) ∘ conj := rfl

theorem fractionalLinear_anti_det_neg (g : FractionalLinearMatrix) (z : ℂ)
    (hz : (fractionalLinear g * complexConjugation) (z : ExtendedComplex) ≠ ∞) :
    LinearMap.det (fderiv ℝ (finiteComplexPart (fractionalLinear g * complexConjugation)) z).toLinearMap < 0 := by
  have hden : g 1 0 * conj z + g 1 1 ≠ 0 :=
    fractionalLinear_denominator_ne_zero g (conj z) hz
  have hd := fractionalLinear_hasDerivAt g (conj z) hden
  rw [finiteComplexPart_anti]
  rw [fderiv_comp z (hd.differentiableAt.restrictScalars ℝ) Complex.conjCLE.differentiableAt]
  have hconjD : fderiv ℝ (conj : ℂ → ℂ) z = (Complex.conjCLE : ℂ →L[ℝ] ℂ) :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.fderiv
  rw [hconjD]
  change LinearMap.det ((fderiv ℝ (finiteComplexPart (fractionalLinear g)) (conj z)).toLinearMap.comp
    Complex.conjCLE.toLinearMap) < 0
  rw [LinearMap.det_comp]
  have hpos : 0 < LinearMap.det (fderiv ℝ (finiteComplexPart (fractionalLinear g)) (conj z)).toLinearMap := by
    rw [Auxiliary.Analysis.complex_real_fderiv_det hd.differentiableAt, hd.deriv]
    exact Complex.normSq_pos.mpr (fractionalLinear_derivative_ne_zero g (conj z) hden)
  have hconj : LinearMap.det Complex.conjCLE.toLinearMap = -1 := Complex.det_conjLIE
  rw [hconj]
  linarith

theorem exists_regular_complex_point (f : Equiv.Perm ExtendedComplex) :
    ∃ z : ℂ, f (z : ExtendedComplex) ≠ ∞ := by
  by_cases h0 : f ((0 : ℂ) : ExtendedComplex) = ∞
  · refine ⟨1, ?_⟩
    intro h1
    have he := f.injective (h1.trans h0.symm)
    simp at he
  · exact ⟨0, h0⟩

theorem fractionalLinear_anti_not_preserves_orientation (g : FractionalLinearMatrix) :
    ¬ PreservesComplexOrientation (fractionalLinear g * complexConjugation) := by
  intro h
  obtain ⟨z, hz⟩ := exists_regular_complex_point (fractionalLinear g * complexConjugation)
  exact (not_lt_of_gt (h z hz).2) (fractionalLinear_anti_det_neg g z hz)

theorem fractionalOrAnti_orientation_iff {f : Equiv.Perm ExtendedComplex}
    (hf : f ∈ fractionalOrAntiGroup) :
    PreservesComplexOrientation f ↔ f ∈ fractionalLinearGroup := by
  constructor
  · intro hp
    rcases hf with hf | hf
    · exact hf
    · obtain ⟨g, hg⟩ := (mem_fractionalLinearGroup _).mp hf
      have heq : f = fractionalLinear g * complexConjugation := by
        rw [hg, mul_assoc, complexConjugation_sq, mul_one]
      rw [heq] at hp
      exact False.elim (fractionalLinear_anti_not_preserves_orientation g hp)
  · intro hf
    obtain ⟨g, rfl⟩ := (mem_fractionalLinearGroup _).mp hf
    exact fractionalLinear_preserves_orientation g


open LowDimensionalTopology.Geometry.Inversive

def euclideanToComplexHom : Inversive.ExtendedHomeomorph 2 →* Equiv.Perm ExtendedComplex where
  toFun f := (extendedComplexEuclideanHomeomorph.toEquiv.trans f.toEquiv).trans
    extendedComplexEuclideanHomeomorph.symm.toEquiv
  map_one' := by ext z; simp
  map_mul' f g := by ext z; simp [Equiv.Perm.mul_apply]

theorem euclideanToComplexHom_apply (f : Inversive.ExtendedHomeomorph 2) (z : ExtendedComplex) :
    euclideanToComplexHom f z = extendedComplexEuclideanHomeomorph.symm
      (f (extendedComplexEuclideanHomeomorph z)) := rfl

@[simp] theorem complexEuclidean_symm_coe (x : Inversive.Euclidean 2) :
    extendedComplexEuclideanHomeomorph.symm (x : Inversive.ExtendedEuclidean 2) =
      (Complex.orthonormalBasisOneI.repr.symm x : ExtendedComplex) := rfl
@[simp] theorem complexEuclidean_symm_infty : extendedComplexEuclideanHomeomorph.symm ∞ = ∞ := rfl

def complexGeneralMobiusGroup : Subgroup (Equiv.Perm ExtendedComplex) :=
  (Inversive.generalMobiusGroup 2).map euclideanToComplexHom

def complexUnitRotation (a : ℂ) (x : Inversive.Euclidean 2) : Inversive.Euclidean 2 :=
  Complex.orthonormalBasisOneI.repr ((a / (‖a‖ : ℂ)) * Complex.orthonormalBasisOneI.repr.symm x)

theorem complexUnitRotation_isometry (a : ℂ) (ha : a ≠ 0) : Isometry (complexUnitRotation a) := by
  have hunit : ‖a / (‖a‖ : ℂ)‖ = 1 := by simp [norm_ne_zero_iff.mpr ha]
  have hm : Isometry (fun z : ℂ ↦ (a / (‖a‖ : ℂ)) * z) := by
    apply Isometry.of_dist_eq
    intro z w
    rw [dist_eq_norm, ← mul_sub, norm_mul, hunit, one_mul, ← dist_eq_norm]
  exact Complex.orthonormalBasisOneI.repr.isometry.comp
    (hm.comp Complex.orthonormalBasisOneI.repr.symm.isometry)

theorem affine_mem_complexGeneralMobiusGroup (a b : ℂ) (ha : a ≠ 0) :
    (affineHomeomorph a b ha).toEquiv ∈ complexGeneralMobiusGroup := by
  let R := Inversive.euclideanIsometryHomeomorph (complexUnitRotation a) (complexUnitRotation_isometry a ha)
  let h := Inversive.translationHomeomorph (Complex.orthonormalBasisOneI.repr b) *
    Inversive.dilationHomeomorph ‖a‖ (norm_ne_zero_iff.mpr ha) * R
  have hmem : h ∈ Inversive.generalMobiusGroup 2 :=
    (Inversive.generalMobiusGroup 2).mul_mem
      ((Inversive.generalMobiusGroup 2).mul_mem (Inversive.translation_mem_generalMobiusGroup _)
        (Inversive.dilation_mem_generalMobiusGroup _ (norm_pos_iff.mpr ha)))
      (Inversive.euclideanIsometry_mem_generalMobiusGroup _ _)
  refine ⟨h, hmem, ?_⟩
  ext z
  change euclideanToComplexHom h z = affineHomeomorph a b ha z
  induction z using OnePoint.rec with
  | infty =>
    simp [euclideanToComplexHom_apply, h, R,
      extendedComplexEuclideanHomeomorph_infty, affineHomeomorph_infty]
  | coe z =>
    rw [euclideanToComplexHom_apply, extendedComplexEuclideanHomeomorph_coe]
    simp only [h, R, Homeomorph.mul_apply, Inversive.euclideanIsometryHomeomorph_coe,
      Inversive.dilationHomeomorph_coe, Inversive.translationHomeomorph_coe, complexEuclidean_symm_coe,
      affineHomeomorph_coe, OnePoint.coe_eq_coe]
    simp only [map_add, map_smul, complexUnitRotation,
      LinearIsometryEquiv.symm_apply_apply]
    rw [Complex.real_smul]
    congr 1
    field_simp [Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)]

theorem complexConj_mem_complexGeneralMobiusGroup :
    Complex.conjCLE.toHomeomorph.onePointCongr.toEquiv ∈ complexGeneralMobiusGroup := by
  let r : Inversive.Euclidean 2 → Inversive.Euclidean 2 := fun x ↦
    Complex.orthonormalBasisOneI.repr (conj (Complex.orthonormalBasisOneI.repr.symm x))
  have hr : Isometry r := Complex.orthonormalBasisOneI.repr.isometry.comp
    (Complex.conjLIE.isometry.comp Complex.orthonormalBasisOneI.repr.symm.isometry)
  refine ⟨Inversive.euclideanIsometryHomeomorph r hr,
    Inversive.euclideanIsometry_mem_generalMobiusGroup r hr, ?_⟩
  ext z
  induction z using OnePoint.rec with
  | infty => simp [euclideanToComplexHom_apply, extendedComplexEuclideanHomeomorph_infty]
  | coe z =>
    rw [euclideanToComplexHom_apply, extendedComplexEuclideanHomeomorph_coe,
      Inversive.euclideanIsometryHomeomorph_coe, complexEuclidean_symm_coe]
    simp only [r, LinearIsometryEquiv.symm_apply_apply]
    rfl

theorem fractionalLinearOfCoefficients_affine_eq (a b d : ℂ)
    (h : a * d - b * 0 ≠ 0) :
    fractionalLinearOfCoefficients a b 0 d h =
      (affineHomeomorph (a / d) (b / d)
        (div_ne_zero (by intro ha; simp [ha] at h) (by intro hd; simp [hd] at h))).toEquiv := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp [fractionalLinearOfCoefficients_infty, Homeomorph.coe_toEquiv, affineHomeomorph_infty]
  | coe z =>
    simp only [fractionalLinearOfCoefficients_affine, Homeomorph.coe_toEquiv,
      affineHomeomorph_coe, OnePoint.coe_eq_coe]
    field_simp

theorem fractionalLinearOfCoefficients_nonaffine_eq (a b c d : ℂ)
    (h : a * d - b * c ≠ 0) (hc : c ≠ 0) :
    fractionalLinearOfCoefficients a b c d h =
      (affineHomeomorph (-(a * d - b * c) / c ^ 2) (a / c)
        (div_ne_zero (neg_ne_zero.mpr h) (pow_ne_zero 2 hc))).toEquiv *
      reciprocal * (affineHomeomorph 1 (d / c) one_ne_zero).toEquiv := by
  ext z
  simp only [Equiv.Perm.mul_apply, Homeomorph.coe_toEquiv]
  induction z using OnePoint.rec with
  | infty => simp [affineHomeomorph_infty, reciprocal_infty,
      affineHomeomorph_coe, fractionalLinearOfCoefficients_infty, hc]
  | coe z =>
    by_cases hz : c * z + d = 0
    · have hp := (denominator_eq_zero_iff c d z hc).mp hz
      subst z
      have hzero : -d / c + d / c = 0 := by ring
      simp only [affineHomeomorph_coe, one_mul, hzero, reciprocal_zero,
        affineHomeomorph_infty, fractionalLinearOfCoefficients_coe, hz, ite_true]
    · have hden : z + d / c ≠ 0 := by
        rw [ne_eq, add_eq_zero_iff_eq_neg]
        simpa [neg_div] using (denominator_eq_zero_iff c d z hc).not.mp hz
      simp only [affineHomeomorph_coe, one_mul, reciprocal_coe _ hden,
        fractionalLinearOfCoefficients_coe, ite_eq_right hz, OnePoint.coe_eq_coe]
      field_simp [hc, hz, hden]
      field_simp [show z * c + d ≠ 0 by simpa only [mul_comm] using hz]
      ring

theorem fractionalLinear_mem_complexGeneralMobiusGroup_of_reciprocal
    (hr : reciprocal ∈ complexGeneralMobiusGroup) (g : FractionalLinearMatrix) :
    fractionalLinear g ∈ complexGeneralMobiusGroup := by
  obtain ⟨h, heq⟩ := fractionalLinear_matrix_coefficients g
  rw [← heq]
  generalize g 0 0 = a at *
  generalize g 0 1 = b at *
  generalize g 1 0 = c at *
  generalize g 1 1 = d at *
  by_cases hc : c = 0
  · subst c
    rw [fractionalLinearOfCoefficients_affine_eq]
    exact affine_mem_complexGeneralMobiusGroup _ _ _
  · rw [fractionalLinearOfCoefficients_nonaffine_eq a b c d h hc]
    exact complexGeneralMobiusGroup.mul_mem
      (complexGeneralMobiusGroup.mul_mem (affine_mem_complexGeneralMobiusGroup _ _ _) hr)
      (affine_mem_complexGeneralMobiusGroup _ _ _)



theorem reciprocal_mem_complexGeneralMobiusGroup : reciprocal ∈ complexGeneralMobiusGroup := by
  have hs : euclideanToComplexHom (Inversive.sphereInversionHomeomorph (0 : Inversive.Euclidean 2) 1 one_ne_zero) ∈
      complexGeneralMobiusGroup := ⟨_, Inversive.sphereInversion_isReflection 0 1 zero_lt_one
        |>.mem_generalMobiusGroup, rfl⟩
  have he : euclideanToComplexHom (Inversive.sphereInversionHomeomorph (0 : Inversive.Euclidean 2) 1 one_ne_zero) =
      reciprocal * complexConjugation := Mobius.ReflectionBridge.unitSphere_eq_reciprocal_conjugation
  rw [he] at hs
  have hm := complexGeneralMobiusGroup.mul_mem hs complexConj_mem_complexGeneralMobiusGroup
  change reciprocal * complexConjugation * complexConjugation ∈ complexGeneralMobiusGroup at hm
  simpa only [mul_assoc, complexConjugation_sq, mul_one] using hm

theorem fractionalLinear_mem_complexGeneralMobiusGroup (g : FractionalLinearMatrix) :
    fractionalLinear g ∈ complexGeneralMobiusGroup :=
  fractionalLinear_mem_complexGeneralMobiusGroup_of_reciprocal reciprocal_mem_complexGeneralMobiusGroup g

theorem reflection_complex_anti {f : Inversive.ExtendedHomeomorph 2} (hf : Inversive.IsReflection f) :
    euclideanToComplexHom f * complexConjugation ∈ fractionalLinearGroup := by
  rcases hf with ⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩
  · have he := Mobius.ReflectionBridge.sphereAnti_eq (Complex.orthonormalBasisOneI.repr.symm c) r hr.ne'
    simp only [LinearIsometryEquiv.apply_symm_apply] at he
    change euclideanToComplexHom (Inversive.sphereInversionHomeomorph c r hr.ne') = _ at he
    rw [he, mul_assoc]
    change _ * (complexConjugation * complexConjugation) ∈ _
    rw [complexConjugation_sq, mul_one]
    exact ⟨coefficientMatrix _ _ _ _ _, rfl⟩
  · have hac : Complex.orthonormalBasisOneI.repr.symm a ≠ 0 := by
      intro h; apply ha
      simpa only [LinearIsometryEquiv.apply_symm_apply, map_zero] using congrArg Complex.orthonormalBasisOneI.repr h
    have he := Mobius.ReflectionBridge.planeAnti_eq (Complex.orthonormalBasisOneI.repr.symm a) t hac
    simp only [LinearIsometryEquiv.apply_symm_apply] at he
    change euclideanToComplexHom (Inversive.planeReflectionHomeomorph a t ha) = _ at he
    rw [he, mul_assoc]
    change _ * (complexConjugation * complexConjugation) ∈ _
    rw [complexConjugation_sq, mul_one]
    exact ⟨coefficientMatrix _ _ _ _ _, rfl⟩

theorem complexGeneralMobiusGroup_le_fractionalOrAntiGroup :
    complexGeneralMobiusGroup ≤ fractionalOrAntiGroup := by
  rintro f ⟨g, hg, rfl⟩
  have hle : Inversive.generalMobiusGroup 2 ≤ fractionalOrAntiGroup.comap euclideanToComplexHom := by
    change Subgroup.closure {f | Inversive.IsReflection f} ≤ _
    apply (Subgroup.closure_le _).mpr
    intro h hh
    exact Or.inr (reflection_complex_anti hh)
  exact hle hg

theorem fractionalOrAntiGroup_le_complexGeneralMobiusGroup :
    fractionalOrAntiGroup ≤ complexGeneralMobiusGroup := by
  intro f hf
  rcases hf with hf | hf
  · obtain ⟨g, rfl⟩ := (mem_fractionalLinearGroup _).mp hf
    exact fractionalLinear_mem_complexGeneralMobiusGroup g
  · obtain ⟨g, hg⟩ := (mem_fractionalLinearGroup _).mp hf
    have he : f = fractionalLinear g * complexConjugation := by
      rw [hg, mul_assoc, complexConjugation_sq, mul_one]
    rw [he]
    exact complexGeneralMobiusGroup.mul_mem (fractionalLinear_mem_complexGeneralMobiusGroup g)
      complexConj_mem_complexGeneralMobiusGroup

theorem complexGeneralMobiusGroup_eq_fractionalOrAntiGroup :
    complexGeneralMobiusGroup = fractionalOrAntiGroup :=
  le_antisymm complexGeneralMobiusGroup_le_fractionalOrAntiGroup
    fractionalOrAntiGroup_le_complexGeneralMobiusGroup

theorem complexGeneralMobius_orientation_iff {f : Equiv.Perm ExtendedComplex}
    (hf : f ∈ complexGeneralMobiusGroup) :
    PreservesComplexOrientation f ↔ f ∈ fractionalLinearGroup :=
  fractionalOrAnti_orientation_iff (complexGeneralMobiusGroup_le_fractionalOrAntiGroup hf)

/-- In complex coordinates, using the actual derivative sign. -/
def complexMobiusGroup : Subgroup (Equiv.Perm ExtendedComplex) where
  carrier := {f | f ∈ complexGeneralMobiusGroup ∧ PreservesComplexOrientation f}
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    exact (complexGeneralMobius_orientation_iff (one_mem _)).mpr (one_mem _)
  mul_mem' {f g} hf hg := by
    have hm := complexGeneralMobiusGroup.mul_mem hf.1 hg.1
    exact ⟨hm, (complexGeneralMobius_orientation_iff hm).mpr
      (fractionalLinearGroup.mul_mem
        ((complexGeneralMobius_orientation_iff hf.1).mp hf.2)
        ((complexGeneralMobius_orientation_iff hg.1).mp hg.2))⟩
  inv_mem' {f} hf := by
    have hm := complexGeneralMobiusGroup.inv_mem hf.1
    exact ⟨hm, (complexGeneralMobius_orientation_iff hm).mpr
      (fractionalLinearGroup.inv_mem ((complexGeneralMobius_orientation_iff hf.1).mp hf.2))⟩

@[simp] theorem mem_complexMobiusGroup (f : Equiv.Perm ExtendedComplex) :
    f ∈ complexMobiusGroup ↔ f ∈ complexGeneralMobiusGroup ∧ PreservesComplexOrientation f := Iff.rfl

/-- The actual orientation-preserving reflection group is the fractional-linear group. -/
theorem complexMobiusGroup_eq_fractionalLinearGroup : complexMobiusGroup = fractionalLinearGroup := by
  ext f
  constructor
  · exact fun hf ↦ (complexGeneralMobius_orientation_iff hf.1).mp hf.2
  · intro hf
    have hg := fractionalOrAntiGroup_le_complexGeneralMobiusGroup (Or.inl hf)
    exact ⟨hg, (complexGeneralMobius_orientation_iff hg).mpr hf⟩

/-- Zero-valued finite-coordinate projections commute with the real isometric chart. -/
theorem finiteComplexPart_coordinates (f : Inversive.ExtendedHomeomorph 2) (z : ℂ) :
    finiteComplexPart (euclideanToComplexHom f) z =
      Complex.orthonormalBasisOneI.repr.symm
        (Inversive.finiteEuclideanPart f (Complex.orthonormalBasisOneI.repr z)) := by
  rw [finiteComplexPart, euclideanToComplexHom_apply, extendedComplexEuclideanHomeomorph_coe]
  rw [Inversive.finiteEuclideanPart]
  generalize f (Complex.orthonormalBasisOneI.repr z : Inversive.ExtendedEuclidean 2) = w
  induction w using OnePoint.rec <;> simp

theorem regular_coordinates_iff (f : Inversive.ExtendedHomeomorph 2) (z : ℂ) :
    euclideanToComplexHom f (z : ExtendedComplex) ≠ ∞ ↔
      f (Complex.orthonormalBasisOneI.repr z : Inversive.ExtendedEuclidean 2) ≠ ∞ := by
  rw [euclideanToComplexHom_apply, extendedComplexEuclideanHomeomorph_coe]
  constructor
  · intro h hw
    exact h (by rw [hw]; rfl)
  · intro h hw
    apply h
    apply extendedComplexEuclideanHomeomorph.symm.injective
    exact hw

theorem preservesOrientation_coordinates_iff (f : Inversive.ExtendedHomeomorph 2) :
    PreservesComplexOrientation (euclideanToComplexHom f) ↔ Inversive.PreservesOrientation f := by
  have heq : finiteComplexPart (euclideanToComplexHom f) =
      fun z ↦ Complex.orthonormalBasisOneI.repr.symm
        (Inversive.finiteEuclideanPart f (Complex.orthonormalBasisOneI.repr z)) := by
    funext z
    exact finiteComplexPart_coordinates f z
  constructor
  · intro h x hx
    have hh := h (Complex.orthonormalBasisOneI.repr.symm x)
      ((regular_coordinates_iff f _).mpr (by simpa only [LinearIsometryEquiv.apply_symm_apply] using hx))
    rw [heq] at hh
    have hchart := Inversive.directlyConformalAt_isometricConjugate_iff
      Complex.orthonormalBasisOneI.repr.symm (f := Inversive.finiteEuclideanPart f) (x := x)
    exact hchart.mp hh
  · intro h z hz
    rw [heq]
    have hh := h (Complex.orthonormalBasisOneI.repr z) ((regular_coordinates_iff f z).mp hz)
    simpa only [LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_apply_apply] using
      Inversive.directlyConformalAt_isometricConjugate Complex.orthonormalBasisOneI.repr.symm hh

/-- The complex criterion agrees with the genuine real two-dimensional orientation criterion. -/
theorem realMobius_orientation_iff_fractionalLinear {f : Inversive.ExtendedHomeomorph 2}
    (hf : f ∈ Inversive.generalMobiusGroup 2) :
    Inversive.PreservesOrientation f ↔ euclideanToComplexHom f ∈ fractionalLinearGroup := by
  rw [← preservesOrientation_coordinates_iff]
  exact complexGeneralMobius_orientation_iff ⟨f, hf, rfl⟩

theorem euclideanToComplexHom_injective : Function.Injective euclideanToComplexHom := by
  intro f g h
  ext x
  apply extendedComplexEuclideanHomeomorph.symm.injective
  have he := congrArg (fun k : Equiv.Perm ExtendedComplex ↦
    k (extendedComplexEuclideanHomeomorph.symm x)) h
  simpa only [euclideanToComplexHom_apply, Homeomorph.apply_symm_apply] using he

/-- The coordinate identification preserves multiplication and inverses. -/
def complexMobiusEquivFractionalLinear : complexMobiusGroup ≃* fractionalLinearGroup :=
  MulEquiv.subgroupCongr complexMobiusGroup_eq_fractionalLinearGroup

@[simp] theorem complexMobiusEquivFractionalLinear_apply (f : complexMobiusGroup) :
    (complexMobiusEquivFractionalLinear f : Equiv.Perm ExtendedComplex) = f := rfl

/-- Membership is exactly real reflection-group membership with positive Jacobian,
transported by the standard isometric complex chart. -/
theorem mem_complexMobiusGroup_iff_real (f : Equiv.Perm ExtendedComplex) :
    f ∈ complexMobiusGroup ↔ ∃ g : Inversive.ExtendedHomeomorph 2,
      g ∈ Inversive.generalMobiusGroup 2 ∧ Inversive.PreservesOrientation g ∧ euclideanToComplexHom g = f := by
  constructor
  · rintro ⟨⟨g, hg, he⟩, hp⟩
    refine ⟨g, hg, ?_, he⟩
    exact (preservesOrientation_coordinates_iff g).mp (he.symm ▸ hp)
  · rintro ⟨g, hg, hp, rfl⟩
    exact ⟨⟨g, hg, rfl⟩, (preservesOrientation_coordinates_iff g).mpr hp⟩


/-! ## Reflection-word parity in real dimension two -/


theorem fractional_and_anti_disjoint {f : Equiv.Perm ExtendedComplex}
    (hf : f ∈ fractionalLinearGroup) : f * complexConjugation ∉ fractionalLinearGroup := by
  intro ha
  obtain ⟨g, hg⟩ := (mem_fractionalLinearGroup _).mp ha
  have heq : f = fractionalLinear g * complexConjugation := by
    rw [hg, mul_assoc, complexConjugation_sq, mul_one]
  have hp := (fractionalOrAnti_orientation_iff (Or.inl hf)).mpr hf
  rw [heq] at hp
  exact fractionalLinear_anti_not_preserves_orientation g hp

theorem anti_mul_direct {f g : Equiv.Perm ExtendedComplex}
    (hf : f * complexConjugation ∈ fractionalLinearGroup) (hg : g ∈ fractionalLinearGroup) :
    f * g * complexConjugation ∈ fractionalLinearGroup := by
  have hm := fractionalLinearGroup.mul_mem hf (complexConjugation_normalizes hg)
  simpa only [mul_assoc, complexConjugation_sq, complexConjugation_twice, one_mul] using hm

theorem anti_mul_anti {f g : Equiv.Perm ExtendedComplex}
    (hf : f * complexConjugation ∈ fractionalLinearGroup)
    (hg : g * complexConjugation ∈ fractionalLinearGroup) :
    f * g ∈ fractionalLinearGroup := by
  have hm := fractionalLinearGroup.mul_mem hf (complexConjugation_normalizes hg)
  simpa only [mul_assoc, complexConjugation_sq, complexConjugation_twice, one_mul, mul_one] using hm

theorem reflectionWord_complex_normal_form (l : List (Inversive.ExtendedHomeomorph 2))
    (hl : ∀ f ∈ l, Inversive.IsReflection f) :
    (Even l.length → euclideanToComplexHom l.prod ∈ fractionalLinearGroup) ∧
    (Odd l.length → euclideanToComplexHom l.prod * complexConjugation ∈ fractionalLinearGroup) := by
  induction l with
  | nil => simp
  | cons f l ih =>
    have hf := reflection_complex_anti (hl f (by simp))
    have hi := ih (fun g hg ↦ hl g (by simp [hg]))
    simp only [List.length_cons, List.prod_cons, map_mul]
    constructor
    · intro he
      apply anti_mul_anti hf
      exact hi.2 (by simpa only [Nat.even_add_one, Nat.not_even_iff_odd] using he)
    · intro ho
      apply anti_mul_direct hf
      exact hi.1 (by simpa only [Nat.odd_add_one, Nat.not_odd_iff_even] using ho)

theorem reflectionWord_complex_fractional_iff_even (l : List (Inversive.ExtendedHomeomorph 2))
    (hl : ∀ f ∈ l, Inversive.IsReflection f) :
    euclideanToComplexHom l.prod ∈ fractionalLinearGroup ↔ Even l.length := by
  have h := reflectionWord_complex_normal_form l hl
  constructor
  · intro hf
    by_contra he
    exact fractional_and_anti_disjoint hf (h.2 (Nat.not_even_iff_odd.mp he))
  · exact h.1

/-- In real dimension two, reflection-word parity agrees with the actual derivative sign. -/
theorem reflectionWord_preservesOrientation_iff_even (l : List (Inversive.ExtendedHomeomorph 2))
    (hl : ∀ f ∈ l, Inversive.IsReflection f) :
    Inversive.PreservesOrientation l.prod ↔ Even l.length := by
  have hm : l.prod ∈ Inversive.generalMobiusGroup 2 :=
    (Inversive.generalMobiusGroup 2).list_prod_mem (fun f hf ↦ (hl f hf).mem_generalMobiusGroup)
  exact (realMobius_orientation_iff_fractionalLinear hm).trans
    (reflectionWord_complex_fractional_iff_even l hl)

/-- The parity is a property of the actual transformation, independent of its word. -/
theorem reflectionWord_even_iff_of_prod_eq (l k : List (Inversive.ExtendedHomeomorph 2))
    (hl : ∀ f ∈ l, Inversive.IsReflection f) (hk : ∀ f ∈ k, Inversive.IsReflection f) (h : l.prod = k.prod) :
    Even l.length ↔ Even k.length := by
  rw [← reflectionWord_preservesOrientation_iff_even l hl,
    ← reflectionWord_preservesOrientation_iff_even k hk, h]

theorem generalMobius_preservesOrientation_iff_even_word {f : Inversive.ExtendedHomeomorph 2}
    (hf : f ∈ Inversive.generalMobiusGroup 2) :
    Inversive.PreservesOrientation f ↔ ∃ l : List (Inversive.ExtendedHomeomorph 2),
      (∀ g ∈ l, Inversive.IsReflection g) ∧ l.prod = f ∧ Even l.length := by
  constructor
  · intro hp
    obtain ⟨l, hl, hprod⟩ := (Inversive.mem_generalMobiusGroup_iff f).mp hf
    exact ⟨l, hl, hprod, (reflectionWord_preservesOrientation_iff_even l hl).mp (hprod.symm ▸ hp)⟩
  · rintro ⟨l, hl, rfl, he⟩
    exact (reflectionWord_preservesOrientation_iff_even l hl).mpr he


def ReversesComplexOrientation (f : Equiv.Perm ExtendedComplex) : Prop :=
  ∀ z : ℂ, f (z : ExtendedComplex) ≠ ∞ → Auxiliary.Analysis.indirectlyConformalAt (finiteComplexPart f) z

theorem fractionalLinear_anti_reverses_orientation (g : FractionalLinearMatrix) :
    ReversesComplexOrientation (fractionalLinear g * complexConjugation) := by
  intro z hz
  refine ⟨?_, fractionalLinear_anti_det_neg g z hz⟩
  rw [finiteComplexPart_anti]
  have hconj : ConformalAt (conj : ℂ → ℂ) z :=
    ⟨Complex.conjCLE, Complex.conjCLE.hasFDerivAt, isConformalMap_conj⟩
  exact ((fractionalLinear_preserves_orientation g (conj z) hz).1).comp z hconj

theorem fractionalLinear_not_reverses_orientation (g : FractionalLinearMatrix) :
    ¬ ReversesComplexOrientation (fractionalLinear g) := by
  intro h
  obtain ⟨z, hz⟩ := exists_regular_complex_point (fractionalLinear g)
  exact (not_lt_of_gt (fractionalLinear_preserves_orientation g z hz).2) (h z hz).2

theorem fractionalOrAnti_reverses_iff {f : Equiv.Perm ExtendedComplex}
    (hf : f ∈ fractionalOrAntiGroup) :
    ReversesComplexOrientation f ↔ f * complexConjugation ∈ fractionalLinearGroup := by
  constructor
  · intro hp
    rcases hf with hf | hf
    · obtain ⟨g, rfl⟩ := (mem_fractionalLinearGroup _).mp hf
      exact False.elim (fractionalLinear_not_reverses_orientation g hp)
    · exact hf
  · intro hf
    obtain ⟨g, hg⟩ := (mem_fractionalLinearGroup _).mp hf
    have heq : f = fractionalLinear g * complexConjugation := by
      rw [hg, mul_assoc, complexConjugation_sq, mul_one]
    rw [heq]
    exact fractionalLinear_anti_reverses_orientation g

theorem reversesOrientation_coordinates_iff (f : Inversive.ExtendedHomeomorph 2) :
    ReversesComplexOrientation (euclideanToComplexHom f) ↔ Inversive.ReversesOrientation f := by
  have heq : finiteComplexPart (euclideanToComplexHom f) =
      fun z ↦ Complex.orthonormalBasisOneI.repr.symm
        (Inversive.finiteEuclideanPart f (Complex.orthonormalBasisOneI.repr z)) := by
    funext z
    exact finiteComplexPart_coordinates f z
  constructor
  · intro h x hx
    have hh := h (Complex.orthonormalBasisOneI.repr.symm x)
      ((regular_coordinates_iff f _).mpr (by simpa only [LinearIsometryEquiv.apply_symm_apply] using hx))
    rw [heq] at hh
    have hchart := Inversive.indirectlyConformalAt_isometricConjugate_iff
      Complex.orthonormalBasisOneI.repr.symm (f := Inversive.finiteEuclideanPart f) (x := x)
    exact hchart.mp hh
  · intro h z hz
    rw [heq]
    have hh := h (Complex.orthonormalBasisOneI.repr z) ((regular_coordinates_iff f z).mp hz)
    simpa only [LinearIsometryEquiv.symm_symm, LinearIsometryEquiv.symm_apply_apply] using
      Inversive.indirectlyConformalAt_isometricConjugate Complex.orthonormalBasisOneI.repr.symm hh

theorem reflectionWord_complex_anti_iff_odd (l : List (Inversive.ExtendedHomeomorph 2))
    (hl : ∀ f ∈ l, Inversive.IsReflection f) :
    euclideanToComplexHom l.prod * complexConjugation ∈ fractionalLinearGroup ↔ Odd l.length := by
  have h := reflectionWord_complex_normal_form l hl
  constructor
  · intro hf
    by_contra he
    exact fractional_and_anti_disjoint (h.1 (Nat.not_odd_iff_even.mp he)) hf
  · exact h.2

/-- The odd-word criterion also uses the actual negative real Jacobian. -/
theorem reflectionWord_reversesOrientation_iff_odd (l : List (Inversive.ExtendedHomeomorph 2))
    (hl : ∀ f ∈ l, Inversive.IsReflection f) :
    Inversive.ReversesOrientation l.prod ↔ Odd l.length := by
  have hm : l.prod ∈ Inversive.generalMobiusGroup 2 :=
    (Inversive.generalMobiusGroup 2).list_prod_mem (fun f hf ↦ (hl f hf).mem_generalMobiusGroup)
  rw [← reversesOrientation_coordinates_iff]
  exact (fractionalOrAnti_reverses_iff (complexGeneralMobiusGroup_le_fractionalOrAntiGroup
    ⟨l.prod, hm, rfl⟩)).trans (reflectionWord_complex_anti_iff_odd l hl)


/-- The canonical real two-dimensional group transports to the complex group
with exactly the same derivative orientation criterion. -/
theorem realMobiusGroup_map_eq_complexMobiusGroup :
    (Inversive.orientationPreservingMobiusGroup 2).map euclideanToComplexHom = complexMobiusGroup := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg.1, rfl⟩, (preservesOrientation_coordinates_iff g).mpr hg.2⟩
  · intro hf
    obtain ⟨g, hgm, hgp, hgf⟩ := (mem_complexMobiusGroup_iff_real f).mp hf
    exact ⟨g, ⟨hgm, hgp⟩, hgf⟩

theorem realMobiusGroup_map_eq_fractionalLinearGroup :
    (Inversive.orientationPreservingMobiusGroup 2).map euclideanToComplexHom = fractionalLinearGroup :=
  realMobiusGroup_map_eq_complexMobiusGroup.trans complexMobiusGroup_eq_fractionalLinearGroup

/-- The canonical real M₂ and the fractional-linear group are isomorphic,
with the standard coordinate change intertwining their point actions. -/
def mobiusEquivFractionalLinear : Inversive.orientationPreservingMobiusGroup 2 ≃* fractionalLinearGroup :=
  ((Inversive.orientationPreservingMobiusGroup 2).equivMapOfInjective euclideanToComplexHom
    euclideanToComplexHom_injective).trans
    (MulEquiv.subgroupCongr realMobiusGroup_map_eq_fractionalLinearGroup)

@[simp] theorem mobiusEquivFractionalLinear_apply (f : Inversive.orientationPreservingMobiusGroup 2) :
    (mobiusEquivFractionalLinear f : Equiv.Perm ExtendedComplex) = euclideanToComplexHom f := rfl

theorem mobiusEquivFractionalLinear_action (f : Inversive.orientationPreservingMobiusGroup 2)
    (z : ExtendedComplex) :
    (mobiusEquivFractionalLinear f : Equiv.Perm ExtendedComplex) z =
      extendedComplexEuclideanHomeomorph.symm
        ((f : Inversive.ExtendedHomeomorph 2) (extendedComplexEuclideanHomeomorph z)) := rfl

end LowDimensionalTopology.Geometry.Mobius
