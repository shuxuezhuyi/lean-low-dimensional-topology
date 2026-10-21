/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Mobius.Classification
public import LowDimensionalTopology.Geometry.Mobius.ReflectionEquivalence

/-!
# Invariants of the geometric complex Möbius group

All invariants and classification statements are transported along the proved,
action-compatible identification with the fractional linear transformation group.
-/

@[expose] public section

open scoped OnePoint

namespace LowDimensionalTopology.Geometry.Mobius

/-- The inverse equivalence preserves the underlying permutation as well. -/
theorem complexMobiusEquivFractionalLinear_symm_apply (f : fractionalLinearGroup) :
    (complexMobiusEquivFractionalLinear.symm f : Equiv.Perm ExtendedComplex) =
      (f : Equiv.Perm ExtendedComplex) := by
  simpa only [complexMobiusEquivFractionalLinear.apply_symm_apply] using
    (complexMobiusEquivFractionalLinear_apply (complexMobiusEquivFractionalLinear.symm f)).symm

/-- matrix projection to the actual orientation-preserving reflection group. -/
noncomputable def mobiusMatrixProjection : FractionalLinearMatrix →* complexMobiusGroup :=
  complexMobiusEquivFractionalLinear.symm.toMonoidHom.comp matrixProjection

theorem mobiusMatrixProjection_equiv (A : FractionalLinearMatrix) :
    complexMobiusEquivFractionalLinear (mobiusMatrixProjection A) = matrixProjection A :=
  complexMobiusEquivFractionalLinear.apply_symm_apply _

theorem mobiusMatrixProjection_apply (A : FractionalLinearMatrix) (z : ExtendedComplex) :
    (mobiusMatrixProjection A : Equiv.Perm ExtendedComplex) z = fractionalLinear A z := by
  change (complexMobiusEquivFractionalLinear.symm (matrixProjection A) :
    Equiv.Perm ExtendedComplex) z = _
  rw [complexMobiusEquivFractionalLinear_symm_apply, matrixProjection_apply]

/-- The projected permutation is exactly the matrix action, including the pole and infinity. -/
theorem mobiusMatrixProjection_coe (A : FractionalLinearMatrix) :
    (mobiusMatrixProjection A : Equiv.Perm ExtendedComplex) = fractionalLinear A := by
  apply Equiv.ext
  exact mobiusMatrixProjection_apply A

/-- Every matrix action has an actual orientation-preserving reflection-group representative. -/
theorem mobiusMatrixProjection_real (A : FractionalLinearMatrix) :
    ∃ g : Inversive.ExtendedHomeomorph 2, g ∈ Inversive.generalMobiusGroup 2 ∧
      Inversive.PreservesOrientation g ∧ euclideanToComplexHom g = fractionalLinear A := by
  have h := (mem_complexMobiusGroup_iff_real
    (mobiusMatrixProjection A : Equiv.Perm ExtendedComplex)).mp (mobiusMatrixProjection A).property
  rw [mobiusMatrixProjection_coe] at h
  exact h

theorem mobiusMatrixProjection_surjective : Function.Surjective mobiusMatrixProjection :=
  complexMobiusEquivFractionalLinear.symm.surjective.comp matrixProjection_surjective

theorem mobiusMatrixProjection_eq_one_iff (A : FractionalLinearMatrix) :
    mobiusMatrixProjection A = 1 ↔
      ∃ u : ℂˣ, A = Matrix.GeneralLinearGroup.scalar (Fin 2) u := by
  have he : mobiusMatrixProjection A = 1 ↔ matrixProjection A = 1 := by
    constructor
    · intro h
      have h' := congrArg complexMobiusEquivFractionalLinear h
      simpa only [mobiusMatrixProjection_equiv, map_one] using h'
    · intro h
      change complexMobiusEquivFractionalLinear.symm (matrixProjection A) = 1
      rw [h, map_one]
  exact he.trans (matrixProjection_eq_one_iff A)

theorem mobiusMatrixProjection_kernel :
    mobiusMatrixProjection.ker = Subgroup.center FractionalLinearMatrix := by
  ext A
  rw [MonoidHom.mem_ker, mobiusMatrixProjection_eq_one_iff,
    Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨fun ⟨u, hu⟩ => ⟨u, hu.symm⟩, fun ⟨u, hu⟩ => ⟨u, hu.symm⟩⟩

/-- The actual geometric complex Möbius group is the quotient by the scalar center. -/
noncomputable def projectiveMobiusEquiv :
    Matrix.ProjGenLinGroup (Fin 2) ℂ ≃* complexMobiusGroup :=
  projectiveFractionalEquiv.trans complexMobiusEquivFractionalLinear.symm

/-- The determinant-one matrix projection to the actual geometric group. -/
noncomputable def mobiusSpecialLinearProjection : Auxiliary.Algebra.SpecialLinear2 →* complexMobiusGroup :=
  complexMobiusEquivFractionalLinear.symm.toMonoidHom.comp specialLinearProjection

theorem mobiusSpecialLinearProjection_equiv (A : Auxiliary.Algebra.SpecialLinear2) :
    complexMobiusEquivFractionalLinear (mobiusSpecialLinearProjection A) = specialLinearProjection A :=
  complexMobiusEquivFractionalLinear.apply_symm_apply _

theorem mobiusSpecialLinearProjection_surjective :
    Function.Surjective mobiusSpecialLinearProjection :=
  complexMobiusEquivFractionalLinear.symm.surjective.comp specialLinearProjection_surjective

theorem mobiusSpecialLinearProjection_eq_iff (A : Auxiliary.Algebra.SpecialLinear2) (f : complexMobiusGroup) :
    mobiusSpecialLinearProjection A = f ↔ specialLinearProjection A =
      complexMobiusEquivFractionalLinear f := by
  rw [← complexMobiusEquivFractionalLinear.injective.eq_iff, mobiusSpecialLinearProjection_equiv]

theorem mobiusSpecialLinearProjection_eq_one_iff (A : Auxiliary.Algebra.SpecialLinear2) :
    mobiusSpecialLinearProjection A = 1 ↔
      (A : Auxiliary.Algebra.ComplexMatrix2) = 1 ∨ (A : Auxiliary.Algebra.ComplexMatrix2) = -1 := by
  rw [mobiusSpecialLinearProjection_eq_iff, map_one, specialLinearProjection_eq_one_iff]

theorem mobiusSpecialLinearProjection_kernel :
    mobiusSpecialLinearProjection.ker = Subgroup.center Auxiliary.Algebra.SpecialLinear2 := by
  ext A
  rw [MonoidHom.mem_ker, mobiusSpecialLinearProjection_eq_one_iff]
  exact (specialLinearProjection_eq_one_iff A).symm.trans (by
    rw [← MonoidHom.mem_ker, specialLinearProjection_kernel])

/-- The determinant-one quotient description of the actual geometric complex group. -/
noncomputable def projectiveSpecialMobiusEquiv :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℂ ≃* complexMobiusGroup :=
  projectiveSpecialFractionalEquiv.trans complexMobiusEquivFractionalLinear.symm

/-- Every geometric map has exactly two distinct determinant-one representatives. -/
theorem mobiusSpecialLinear_exactly_two_representatives (f : complexMobiusGroup) :
    ∃ A B : Auxiliary.Algebra.SpecialLinear2, A ≠ B ∧ mobiusSpecialLinearProjection A = f ∧
      mobiusSpecialLinearProjection B = f ∧ ∀ C : Auxiliary.Algebra.SpecialLinear2,
        mobiusSpecialLinearProjection C = f ↔ C = A ∨ C = B := by
  obtain ⟨A, B, hAB, hA, hB, hC⟩ :=
    specialLinear_exactly_two_representatives (complexMobiusEquivFractionalLinear f)
  exact ⟨A, B, hAB, (mobiusSpecialLinearProjection_eq_iff A f).mpr hA,
    (mobiusSpecialLinearProjection_eq_iff B f).mpr hB,
    fun C => (mobiusSpecialLinearProjection_eq_iff C f).trans (hC C)⟩

/-- equation: squared trace on the actual geometric group. -/
noncomputable def mobiusSquaredTrace (f : complexMobiusGroup) : ℂ :=
  fractionalSquaredTrace (complexMobiusEquivFractionalLinear f)

/-- The normalized Frobenius norm on the actual geometric group. -/
noncomputable def mobiusNormalizedNorm (f : complexMobiusGroup) : ℝ :=
  fractionalNormalizedNorm (complexMobiusEquivFractionalLinear f)

/-- The absolute trace is the nonnegative square root of the modulus of squared trace. -/
noncomputable def mobiusTraceAbs (f : complexMobiusGroup) : ℝ := Real.sqrt ‖mobiusSquaredTrace f‖

theorem mobiusSquaredTrace_projection (A : FractionalLinearMatrix) :
    mobiusSquaredTrace (mobiusMatrixProjection A) = matrixSquaredTrace A := by
  rw [mobiusSquaredTrace, mobiusMatrixProjection_equiv, fractionalSquaredTrace_projection]

theorem mobiusNormalizedNorm_projection (A : FractionalLinearMatrix) :
    mobiusNormalizedNorm (mobiusMatrixProjection A) = matrixNormalizedNorm A := by
  rw [mobiusNormalizedNorm, mobiusMatrixProjection_equiv, fractionalNormalizedNorm_projection]

theorem mobiusTraceAbs_projection (A : FractionalLinearMatrix) :
    mobiusTraceAbs (mobiusMatrixProjection A) = matrixTraceAbs A := by
  rw [mobiusTraceAbs, mobiusSquaredTrace_projection]
  rfl

theorem mobiusSquaredTrace_specialLinearProjection (A : Auxiliary.Algebra.SpecialLinear2) :
    mobiusSquaredTrace (mobiusSpecialLinearProjection A) = (A : Auxiliary.Algebra.ComplexMatrix2).trace ^ 2 := by
  rw [mobiusSquaredTrace, mobiusSpecialLinearProjection_equiv,
    fractionalSquaredTrace_specialLinearProjection]

theorem mobiusNormalizedNorm_specialLinearProjection (A : Auxiliary.Algebra.SpecialLinear2) :
    mobiusNormalizedNorm (mobiusSpecialLinearProjection A) = Auxiliary.Algebra.matrixNorm A := by
  rw [mobiusNormalizedNorm, mobiusSpecialLinearProjection_equiv,
    fractionalNormalizedNorm_specialLinearProjection]

/-- conjugation preserves squared trace on the actual geometric group. -/
theorem mobiusSquaredTrace_conjugation (f q : complexMobiusGroup) :
    mobiusSquaredTrace (q * f * q⁻¹) = mobiusSquaredTrace f := by
  simp only [mobiusSquaredTrace, map_mul, map_inv, fractionalSquaredTrace_conjugation]

/-- The canonical equivalence transports conjugacy in both directions. -/
theorem complexMobius_isConj_iff (f g : complexMobiusGroup) :
    IsConj f g ↔ IsConj (complexMobiusEquivFractionalLinear f)
      (complexMobiusEquivFractionalLinear g) := by
  constructor
  · exact complexMobiusEquivFractionalLinear.toMonoidHom.map_isConj
  · intro h
    obtain ⟨q, hq⟩ := isConj_iff.mp h
    apply isConj_iff.mpr
    refine ⟨complexMobiusEquivFractionalLinear.symm q, ?_⟩
    apply complexMobiusEquivFractionalLinear.injective
    simpa only [map_mul, map_inv, complexMobiusEquivFractionalLinear.apply_symm_apply] using hq

/-- The standard form as an actual orientation-preserving geometric map. -/
noncomputable def mobiusStandardElement (k : ℂˣ) : complexMobiusGroup :=
  complexMobiusEquivFractionalLinear.symm (Mobius.Classification.standardElement k)

theorem mobiusStandardElement_equiv (k : ℂˣ) :
    complexMobiusEquivFractionalLinear (mobiusStandardElement k) = Mobius.Classification.standardElement k :=
  complexMobiusEquivFractionalLinear.apply_symm_apply _

theorem mobiusStandardElement_apply (k : ℂˣ) (z : ExtendedComplex) :
    (mobiusStandardElement k : Equiv.Perm ExtendedComplex) z = Mobius.Classification.standardForm k z := by
  rw [mobiusStandardElement, complexMobiusEquivFractionalLinear_symm_apply,
    Mobius.Classification.standardElement_apply]

theorem mobiusStandardElement_coe (k : ℂˣ) (z : ℂ) :
    (mobiusStandardElement k : Equiv.Perm ExtendedComplex) z =
      ((if (k : ℂ) = 1 then z + 1 else (k : ℂ) * z : ℂ) : ExtendedComplex) := by
  rw [mobiusStandardElement_apply, Mobius.Classification.standardForm_coe]

theorem mobiusStandardElement_infty (k : ℂˣ) :
    (mobiusStandardElement k : Equiv.Perm ExtendedComplex) ∞ = ∞ := by
  rw [mobiusStandardElement_apply, Mobius.Classification.standardForm_infty]

theorem mobiusStandardElement_squaredTrace (k : ℂˣ) :
    mobiusSquaredTrace (mobiusStandardElement k) = (k : ℂ) + (k : ℂ)⁻¹ + 2 := by
  rw [mobiusSquaredTrace, mobiusStandardElement_equiv, Mobius.Classification.standardElement_squaredTrace]

/-- The exact one- or two-point boundary fixed-point dichotomy in the actual group. -/
theorem mobius_nonidentity_fixedPoint_dichotomy (f : complexMobiusGroup) (hf : f ≠ 1) :
    (∃ a : ExtendedComplex, ∀ z : ExtendedComplex,
      (f : Equiv.Perm ExtendedComplex) z = z ↔ z = a) ∨
    (∃ a b : ExtendedComplex, a ≠ b ∧ ∀ z : ExtendedComplex,
      (f : Equiv.Perm ExtendedComplex) z = z ↔ z = a ∨ z = b) := by
  have hf' : complexMobiusEquivFractionalLinear f ≠ 1 := by
    intro h
    apply hf
    exact complexMobiusEquivFractionalLinear.injective (by simpa only [map_one] using h)
  simpa only [complexMobiusEquivFractionalLinear_apply] using
    Mobius.Classification.nonidentity_fixedPoint_dichotomy (complexMobiusEquivFractionalLinear f) hf'

/-- Every actual nonidentity Möbius map is conjugate within the actual group to a standard form. -/
theorem mobius_nonidentity_conjugate_standard (f : complexMobiusGroup) (hf : f ≠ 1) :
    ∃ k : ℂˣ, IsConj f (mobiusStandardElement k) := by
  have hf' : complexMobiusEquivFractionalLinear f ≠ 1 := by
    intro h
    apply hf
    exact complexMobiusEquivFractionalLinear.injective (by simpa only [map_one] using h)
  obtain ⟨k, hk⟩ := Mobius.Classification.nonidentity_conjugate_standard
    (complexMobiusEquivFractionalLinear f) hf'
  refine ⟨k, (complexMobius_isConj_iff _ _).mpr ?_⟩
  rw [mobiusStandardElement_equiv]
  exact hk

/-- on the geometric orientation-preserving reflection group. -/
theorem mobius_isConj_iff_squaredTrace_eq (f g : complexMobiusGroup) (hf : f ≠ 1) (hg : g ≠ 1) :
    IsConj f g ↔ mobiusSquaredTrace f = mobiusSquaredTrace g := by
  have hf' : complexMobiusEquivFractionalLinear f ≠ 1 := by
    intro h
    exact hf (complexMobiusEquivFractionalLinear.injective (by simpa only [map_one] using h))
  have hg' : complexMobiusEquivFractionalLinear g ≠ 1 := by
    intro h
    exact hg (complexMobiusEquivFractionalLinear.injective (by simpa only [map_one] using h))
  rw [complexMobius_isConj_iff]
  exact Mobius.Classification.fractional_isConj_iff_squaredTrace_eq _ _ hf' hg'

@[simp] theorem complexMobiusEquiv_eq_one_iff (f : complexMobiusGroup) :
    complexMobiusEquivFractionalLinear f = 1 ↔ f = 1 := by
  constructor
  · intro h
    apply complexMobiusEquivFractionalLinear.injective
    simpa only [map_one] using h
  · rintro rfl
    exact map_one _

theorem complexMobius_commute_iff (f g : complexMobiusGroup) :
    Commute f g ↔ Commute (complexMobiusEquivFractionalLinear f)
      (complexMobiusEquivFractionalLinear g) := by
  change f * g = g * f ↔ _ * _ = _ * _
  rw [← map_mul, ← map_mul]
  exact complexMobiusEquivFractionalLinear.injective.eq_iff.symm

/-- The boundary definition of parabolic for the actual geometric group. -/
def MobiusBoundaryParabolic (f : complexMobiusGroup) : Prop :=
  f ≠ 1 ∧ ∃ a : ExtendedComplex, ∀ z : ExtendedComplex,
    (f : Equiv.Perm ExtendedComplex) z = z ↔ z = a

theorem mobiusBoundaryParabolic_iff (f : complexMobiusGroup) :
    MobiusBoundaryParabolic f ↔ Mobius.Classification.BoundaryParabolic
      (complexMobiusEquivFractionalLinear f) := by
  simp only [MobiusBoundaryParabolic, Mobius.Classification.BoundaryParabolic,
    complexMobiusEquivFractionalLinear_apply, ne_eq, complexMobiusEquiv_eq_one_iff]

/-- The actual-group commutator in the source order. -/
noncomputable def mobiusCommutator (f g : complexMobiusGroup) : complexMobiusGroup :=
  f * g * f⁻¹ * g⁻¹

theorem mobiusCommutator_equiv (f g : complexMobiusGroup) :
    complexMobiusEquivFractionalLinear (mobiusCommutator f g) =
      Mobius.Classification.commutatorElement (complexMobiusEquivFractionalLinear f)
        (complexMobiusEquivFractionalLinear g) := by
  simp only [mobiusCommutator, Mobius.Classification.commutatorElement, map_mul, map_inv]

/-- The sign-independent commutator trace on actual geometric maps. -/
noncomputable def mobiusCommutatorTrace (f g : complexMobiusGroup) : ℂ :=
  Mobius.Classification.commutatorTrace (complexMobiusEquivFractionalLinear f)
    (complexMobiusEquivFractionalLinear g)

theorem mobiusCommutatorTrace_representatives (f g : complexMobiusGroup)
    (A B : Auxiliary.Algebra.SpecialLinear2) (hA : mobiusSpecialLinearProjection A = f)
    (hB : mobiusSpecialLinearProjection B = g) :
    mobiusCommutatorTrace f g =
      (Mobius.Classification.specialCommutator A B : Auxiliary.Algebra.ComplexMatrix2).trace :=
  Mobius.Classification.commutatorTrace_representatives _ _ A B
    ((mobiusSpecialLinearProjection_eq_iff A f).mp hA)
    ((mobiusSpecialLinearProjection_eq_iff B g).mp hB)

/-- Sharing a boundary fixed point, stated using the actual geometric action. -/
def MobiusCommonFixedPoint (f g : complexMobiusGroup) : Prop :=
  ∃ z : ExtendedComplex, (f : Equiv.Perm ExtendedComplex) z = z ∧
    (g : Equiv.Perm ExtendedComplex) z = z

theorem mobiusCommonFixedPoint_iff (f g : complexMobiusGroup) :
    MobiusCommonFixedPoint f g ↔ Mobius.Classification.CommonFixedPoint
      (complexMobiusEquivFractionalLinear f) (complexMobiusEquivFractionalLinear g) := by
  simp only [MobiusCommonFixedPoint, Mobius.Classification.CommonFixedPoint,
    complexMobiusEquivFractionalLinear_apply]

/-- Equality of the two boundary fixed sets in the actual geometric action. -/
def MobiusSameFixedPoints (f g : complexMobiusGroup) : Prop :=
  ∀ z : ExtendedComplex, (f : Equiv.Perm ExtendedComplex) z = z ↔
    (g : Equiv.Perm ExtendedComplex) z = z

theorem mobiusSameFixedPoints_iff (f g : complexMobiusGroup) :
    MobiusSameFixedPoints f g ↔ Mobius.Classification.SameFixedPoints
      (complexMobiusEquivFractionalLinear f) (complexMobiusEquivFractionalLinear g) := by
  simp only [MobiusSameFixedPoints, Mobius.Classification.SameFixedPoints,
    complexMobiusEquivFractionalLinear_apply]

/-- For the actual geometric group. -/
theorem mobius_parabolic_iff_squaredTrace_eq_four (f : complexMobiusGroup) (hf : f ≠ 1) :
    MobiusBoundaryParabolic f ↔ mobiusSquaredTrace f = 4 := by
  rw [mobiusBoundaryParabolic_iff]
  exact Mobius.Classification.fractional_parabolic_iff_squaredTrace_eq_four _ (by simpa only [ne_eq,
    complexMobiusEquiv_eq_one_iff] using hf)

/-- For the actual geometric group. -/
theorem mobius_commonFixedPoint_iff_commutatorTrace_eq_two (f g : complexMobiusGroup) :
    MobiusCommonFixedPoint f g ↔ mobiusCommutatorTrace f g = 2 := by
  rw [mobiusCommonFixedPoint_iff]
  exact Mobius.Classification.fractional_commonFixedPoint_iff_commutatorTrace_eq_two _ _

/-- For the actual geometric group and its actual boundary action. -/
theorem mobius_commonFixedPoint_commutator_dichotomy (f g : complexMobiusGroup) (hf : f ≠ 1) (hg : g ≠ 1)
    (hcommon : MobiusCommonFixedPoint f g) :
    (mobiusCommutator f g = 1 ∧ Commute f g ∧ MobiusSameFixedPoints f g) ∨
    (MobiusBoundaryParabolic (mobiusCommutator f g) ∧ ¬ Commute f g ∧ ¬ MobiusSameFixedPoints f g) := by
  have hf' : complexMobiusEquivFractionalLinear f ≠ 1 := by
    simpa only [ne_eq, complexMobiusEquiv_eq_one_iff] using hf
  have hg' : complexMobiusEquivFractionalLinear g ≠ 1 := by
    simpa only [ne_eq, complexMobiusEquiv_eq_one_iff] using hg
  rcases Mobius.Classification.fractional_commonFixedPoint_commutator_dichotomy _ _ hf' hg'
    ((mobiusCommonFixedPoint_iff f g).mp hcommon)
    with ⟨hc, hcomm, hs⟩ | ⟨hp, hcomm, hs⟩
  · left
    refine ⟨?_, (complexMobius_commute_iff f g).mpr hcomm,
      (mobiusSameFixedPoints_iff f g).mpr hs⟩
    apply complexMobiusEquivFractionalLinear.injective
    simpa only [mobiusCommutator_equiv, map_one] using hc
  · right
    refine ⟨(mobiusBoundaryParabolic_iff _).mpr ?_, ?_, ?_⟩
    · rw [mobiusCommutator_equiv]
      exact hp
    · exact fun h => hcomm ((complexMobius_commute_iff f g).mp h)
    · exact fun h => hs ((mobiusSameFixedPoints_iff f g).mp h)

/-- The equivalence preserves exact group order. -/
theorem mobius_orderOf_equiv (f : complexMobiusGroup) :
    orderOf (complexMobiusEquivFractionalLinear f) = orderOf f :=
  orderOf_injective complexMobiusEquivFractionalLinear.toMonoidHom
    complexMobiusEquivFractionalLinear.injective f

/-- An actual nonidentity map has order two exactly at squared trace zero. -/
theorem mobius_orderOf_eq_two_iff_squaredTrace_eq_zero (f : complexMobiusGroup) (hf : f ≠ 1) :
    orderOf f = 2 ↔ mobiusSquaredTrace f = 0 := by
  rw [← mobius_orderOf_equiv]
  exact Mobius.Classification.orderOf_eq_two_iff_squaredTrace_eq_zero _
    (by simpa only [ne_eq, complexMobiusEquiv_eq_one_iff] using hf)

/-- The translation conjugacy characterization of the actual boundary-parabolic definition. -/
theorem mobiusBoundaryParabolic_iff_conjugate_translation (f : complexMobiusGroup) (hf : f ≠ 1) :
    MobiusBoundaryParabolic f ↔ IsConj f (mobiusStandardElement 1) := by
  rw [mobiusBoundaryParabolic_iff, complexMobius_isConj_iff, mobiusStandardElement_equiv]
  exact Mobius.Classification.boundaryParabolic_iff_conjugate_translation _
    (by simpa only [ne_eq, complexMobiusEquiv_eq_one_iff] using hf)

/-- A finite-order actual map has a nontranslation standard form of unit modulus.
The equivalence with the geometric interior definition of elliptic is separate. -/
theorem mobius_finite_order_conjugate_unit_standard (f : complexMobiusGroup) (hf : f ≠ 1)
    (hfin : IsOfFinOrder f) :
    ∃ k : ℂˣ, (k : ℂ) ≠ 1 ∧ ‖(k : ℂ)‖ = 1 ∧ IsConj f (mobiusStandardElement k) := by
  have hfin' : IsOfFinOrder (complexMobiusEquivFractionalLinear f) := by
    obtain ⟨n, hn, hp⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨n, hn, ?_⟩
    rw [← map_pow, hp, map_one]
  obtain ⟨k, hk1, hkn, hk⟩ := Mobius.Classification.finite_order_conjugate_unit_standard
    (complexMobiusEquivFractionalLinear f)
    (by simpa only [ne_eq, complexMobiusEquiv_eq_one_iff] using hf) hfin'
  refine ⟨k, hk1, hkn, (complexMobius_isConj_iff _ _).mpr ?_⟩
  rw [mobiusStandardElement_equiv]
  exact hk

/-- coprime rotation angles and the cosine trace formula in the actual group. -/
theorem mobius_exact_order_angle_squaredTrace (f : complexMobiusGroup) (hf : f ≠ 1)
    (n : ℕ) (hn : 0 < n) (ho : orderOf f = n) :
    ∃ k : ℂˣ, ∃ m < n, m.Coprime n ∧ IsConj f (mobiusStandardElement k) ∧
      Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) / n)) = (k : ℂ) ∧
      mobiusSquaredTrace f = ((4 * Real.cos (Real.pi * m / n) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨k, m, hm, hmn, hk, he, htrace⟩ := Mobius.Classification.exact_order_angle_squaredTrace
    (complexMobiusEquivFractionalLinear f)
    (by simpa only [ne_eq, complexMobiusEquiv_eq_one_iff] using hf) n hn
    ((mobius_orderOf_equiv f).trans ho)
  refine ⟨k, m, hm, hmn, (complexMobius_isConj_iff _ _).mpr ?_, he, htrace⟩
  rw [mobiusStandardElement_equiv]
  exact hk

/-- The sharp bound and the two equality rotations in the actual group. -/
theorem mobius_finiteOrder_standard_conjugate_and_squaredTrace_bound_with_equality (f : complexMobiusGroup) (hf : f ≠ 1)
    (n : ℕ) (hn : 0 < n) (ho : orderOf f = n) :
    ∃ k : ℂˣ, IsConj f (mobiusStandardElement k) ∧
      (mobiusSquaredTrace f).im = 0 ∧
      (mobiusSquaredTrace f).re ≤ 4 * Real.cos (Real.pi / n) ^ 2 ∧
      ((mobiusSquaredTrace f).re = 4 * Real.cos (Real.pi / n) ^ 2 ↔
        (k : ℂ) = Complex.exp (2 * Real.pi * Complex.I / n) ∨
        (k : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I / n))) := by
  obtain ⟨k, hk, him, hb, he⟩ :=
    Mobius.Classification.fractional_finiteOrder_standard_conjugate_and_squaredTrace_bound_with_equality
    (complexMobiusEquivFractionalLinear f)
    (by simpa only [ne_eq, complexMobiusEquiv_eq_one_iff] using hf) n hn
    ((mobius_orderOf_equiv f).trans ho)
  refine ⟨k, (complexMobius_isConj_iff _ _).mpr ?_, him, hb, he⟩
  rw [mobiusStandardElement_equiv]
  exact hk

end LowDimensionalTopology.Geometry.Mobius
