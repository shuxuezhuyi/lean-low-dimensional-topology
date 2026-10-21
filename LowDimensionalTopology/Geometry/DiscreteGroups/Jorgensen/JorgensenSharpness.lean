/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.FiniteOrbit
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.TypeOneGroups
public import LowDimensionalTopology.Geometry.Mobius.InvariantDisc.InvariantDiscConverse
public import LowDimensionalTopology.Geometry.Mobius.Topology
public import LowDimensionalTopology.Geometry.Mobius.Trace.MobiusInvariants
public import LowDimensionalTopology.Geometry.DiscreteGroups.Matrix
@[expose] public section
noncomputable section
open Set
open scoped OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius

/-- The unit-translation generator in the sharpness example. -/
def jorgensenSharpnessTranslation : Mobius.complexMobiusGroup := mobiusTranslation 1

/-- The determinant-one lift of the negative reciprocal generator. -/
def jorgensenSharpnessInversionLift : Auxiliary.Algebra.SpecialLinear2 :=
  ⟨!![0, -1; 1, 0], by simp⟩

/-- The actual negative reciprocal Mobius transformation. -/
def jorgensenSharpnessInversion : Mobius.complexMobiusGroup :=
  Mobius.mobiusSpecialLinearProjection jorgensenSharpnessInversionLift

/-- The actual two-generator group used to attain equality. -/
def jorgensenSharpnessGroup : Subgroup Mobius.complexMobiusGroup :=
  Subgroup.closure ({jorgensenSharpnessTranslation, jorgensenSharpnessInversion} :
    Set Mobius.complexMobiusGroup)

/-- The unit-translation generator agrees with the genuine standard form. -/
theorem jorgensenSharpnessTranslation_standard :
    jorgensenSharpnessTranslation = Mobius.mobiusStandardElement 1 := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  induction z using OnePoint.rec with
  | infty => simp [jorgensenSharpnessTranslation, mobiusTranslation_infty, Mobius.mobiusStandardElement_infty]
  | coe z => simp [jorgensenSharpnessTranslation, mobiusTranslation_coe, Mobius.mobiusStandardElement_coe]

/-- The standard integral translation matrix projects to the chosen actual translation. -/
theorem jorgensenSharpnessTranslation_lift :
    Mobius.mobiusSpecialLinearProjection Mobius.invariantDiscTranslationLift = jorgensenSharpnessTranslation := by
  rw [Mobius.invariantDiscTranslationLift_projection, jorgensenSharpnessTranslation_standard]

/-- The second generator sends infinity to the finite point zero. -/
theorem jorgensenSharpnessInversion_infty :
    jorgensenSharpnessInversion.val ∞ = ((0 : ℂ) : Mobius.ExtendedComplex) := by
  rw [jorgensenSharpnessInversion, Mobius.invariantDisc_specialLinear_action, Mobius.fractionalLinear_infty]
  norm_num [jorgensenSharpnessInversionLift, Matrix.SpecialLinearGroup.toGL]

/-- At every finite nonzero input the second generator is negative reciprocal. -/
theorem jorgensenSharpnessInversion_coe (z : ℂ) (hz : z ≠ 0) :
    jorgensenSharpnessInversion.val z = ((-1 / z : ℂ) : Mobius.ExtendedComplex) := by
  rw [jorgensenSharpnessInversion, Mobius.invariantDisc_specialLinear_action, Mobius.fractionalLinear_coe]
  simp [jorgensenSharpnessInversionLift, Matrix.SpecialLinearGroup.toGL, hz]

/-- The translation lift belongs to the discrete integral-entry Picard matrix group. -/
theorem jorgensenSharpnessTranslation_mem_picard :
    Mobius.invariantDiscTranslationLift ∈ DiscreteGroups.MatrixGroups.picardGroup := by
  apply (DiscreteGroups.MatrixGroups.mem_picardGroup_iff _).mpr
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨1, by simp [Mobius.invariantDiscTranslationLift]⟩
  · exact ⟨1, by simp [Mobius.invariantDiscTranslationLift]⟩
  · exact ⟨0, by simp [Mobius.invariantDiscTranslationLift]⟩
  · exact ⟨1, by simp [Mobius.invariantDiscTranslationLift]⟩

/-- The negative reciprocal lift belongs to the same discrete matrix group. -/
theorem jorgensenSharpnessInversion_mem_picard :
    jorgensenSharpnessInversionLift ∈ DiscreteGroups.MatrixGroups.picardGroup := by
  apply (DiscreteGroups.MatrixGroups.mem_picardGroup_iff _).mpr
  intro i j
  fin_cases i <;> fin_cases j
  · exact ⟨0, by simp [jorgensenSharpnessInversionLift]⟩
  · exact ⟨-1, by simp [jorgensenSharpnessInversionLift]⟩
  · exact ⟨1, by simp [jorgensenSharpnessInversionLift]⟩
  · exact ⟨0, by simp [jorgensenSharpnessInversionLift]⟩

/-- The generated genuine group lies in the projective image of that discrete matrix group. -/
theorem jorgensenSharpnessGroup_le_picard :
    jorgensenSharpnessGroup ≤ DiscreteGroups.MatrixGroups.picardGroup.map Mobius.mobiusSpecialLinearProjection := by
  apply (Subgroup.closure_le _).mpr
  intro f hf
  rcases Set.mem_insert_iff.mp hf with rfl | hf
  · exact Subgroup.mem_map.mpr ⟨Mobius.invariantDiscTranslationLift,
      jorgensenSharpnessTranslation_mem_picard, jorgensenSharpnessTranslation_lift⟩
  · have hf' : f = jorgensenSharpnessInversion := Set.mem_singleton_iff.mp hf
    subst f
    exact Subgroup.mem_map.mpr ⟨jorgensenSharpnessInversionLift,
      jorgensenSharpnessInversion_mem_picard, rfl⟩

/-- The equality example is discrete in the actual uniform Mobius topology. -/
theorem jorgensenSharpnessGroup_discrete : Mobius.IsDiscreteMobiusSubgroup jorgensenSharpnessGroup := by
  let picardSharpnessDiscrete : DiscreteTopology DiscreteGroups.MatrixGroups.picardGroup :=
    DiscreteGroups.MatrixGroups.picardGroup_discrete
  have hd := Mobius.discreteSpecialLinear_image DiscreteGroups.MatrixGroups.picardGroup
  exact isDiscrete_iff_discreteTopology.mp
    ((isDiscrete_iff_discreteTopology.mpr hd).mono jorgensenSharpnessGroup_le_picard)

/-- A positive-periodic boundary point of unit translation must be infinity. -/
theorem jorgensenSharpnessTranslation_periodic (z : Mobius.ExtendedComplex) (m : ℕ) (hm : 0 < m)
    (hz : (jorgensenSharpnessTranslation ^ m).val z = z) : z = ∞ := by
  rw [jorgensenSharpnessTranslation_standard] at hz
  induction z using OnePoint.rec with
  | infty => rfl
  | coe z =>
    simp only [Mobius.mobiusStandardElement_pow_coe, Units.val_one, ite_true, OnePoint.coe_eq_coe] at hz
    have hzero : (m : ℂ) = 0 := add_left_cancel (hz.trans (add_zero z).symm)
    exact False.elim (hm.ne' (Nat.cast_eq_zero.mp hzero))

/-- Both displayed generators belong to the genuine generated subgroup. -/
theorem jorgensenSharpnessGroup_generators :
    jorgensenSharpnessTranslation ∈ jorgensenSharpnessGroup ∧
      jorgensenSharpnessInversion ∈ jorgensenSharpnessGroup := by
  constructor <;> apply Subgroup.subset_closure <;> simp

/-- The example is genuinely non-elementary, including the possible interior-orbit branch. -/
theorem jorgensenSharpnessGroup_nonElementary : IsNonElementary jorgensenSharpnessGroup := by
  intro he
  obtain ⟨hT, hS⟩ := jorgensenSharpnessGroup_generators
  rcases (isElementary_iff_boundary_or_interior _).mp he with ⟨z, hz⟩ | ⟨q, hq⟩
  · let t : jorgensenSharpnessGroup := ⟨jorgensenSharpnessTranslation, hT⟩
    let s : jorgensenSharpnessGroup := ⟨jorgensenSharpnessInversion, hS⟩
    obtain ⟨m, hm, hfix⟩ := DiscreteGroups.Action.exists_positive_power_fixing_finite_orbit z hz t
    have hzinf : z = ∞ := jorgensenSharpnessTranslation_periodic z m hm
      (hfix z (MulAction.mem_orbit_self z))
    have hsinfty : s • z = ∞ := jorgensenSharpnessTranslation_periodic (s • z) m hm
      (hfix (s • z) (MulAction.mem_orbit z s))
    rw [hzinf] at hsinfty
    change jorgensenSharpnessInversion.val ∞ = ∞ at hsinfty
    rw [jorgensenSharpnessInversion_infty] at hsinfty
    exact (OnePoint.coe_ne_infty (0 : ℂ)) hsinfty
  · have hTell := finite_H3_orbit_all_elliptic _ q hq jorgensenSharpnessTranslation hT
      (by rw [jorgensenSharpnessTranslation_standard]; exact Mobius.mobiusStandardElement_ne_one 1)
    exact hTell.not_parabolic ((mobiusTranslation_parabolic_iff 1).mpr one_ne_zero)

/-- The squared trace of unit translation is exactly four. -/
theorem jorgensenSharpnessTranslation_squaredTrace :
    Mobius.mobiusSquaredTrace jorgensenSharpnessTranslation = 4 := by
  rw [← jorgensenSharpnessTranslation_lift, Mobius.mobiusSquaredTrace_specialLinearProjection]
  norm_num [Mobius.invariantDiscTranslationLift, Matrix.trace_fin_two]

/-- The canonical commutator trace of the equality pair is three. -/
theorem jorgensenSharpness_commutatorTrace :
    Mobius.mobiusCommutatorTrace jorgensenSharpnessTranslation jorgensenSharpnessInversion = 3 := by
  change Mobius.mobiusCommutatorTrace jorgensenSharpnessTranslation
    (Mobius.mobiusSpecialLinearProjection jorgensenSharpnessInversionLift) = 3
  rw [Mobius.mobiusCommutatorTrace_representatives _ _ Mobius.invariantDiscTranslationLift
    jorgensenSharpnessInversionLift jorgensenSharpnessTranslation_lift rfl]
  change Matrix.trace
    (((Mobius.invariantDiscTranslationLift : Auxiliary.Algebra.ComplexMatrix2) *
      (jorgensenSharpnessInversionLift : Auxiliary.Algebra.ComplexMatrix2)) *
      Matrix.adjugate (Mobius.invariantDiscTranslationLift : Auxiliary.Algebra.ComplexMatrix2) *
      Matrix.adjugate (jorgensenSharpnessInversionLift : Auxiliary.Algebra.ComplexMatrix2)) = 3
  norm_num [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.trace_fin_two, Mobius.invariantDiscTranslationLift, jorgensenSharpnessInversionLift]

/-- The actual discrete non-elementary pair attains the bound one. -/
theorem jorgensenSharpness_defect_eq_one :
    ‖Mobius.mobiusSquaredTrace jorgensenSharpnessTranslation - 4‖ +
      ‖Mobius.mobiusCommutatorTrace jorgensenSharpnessTranslation jorgensenSharpnessInversion - 2‖ = 1 := by
  rw [jorgensenSharpnessTranslation_squaredTrace, jorgensenSharpness_commutatorTrace]
  norm_num

/-- Equality is realized by a genuine discrete non-elementary two-generator Mobius group. -/
theorem jorgensenSharpness_exists : ∃ f g : Mobius.complexMobiusGroup,
    Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)) ∧
      IsNonElementary (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)) ∧
        ‖Mobius.mobiusSquaredTrace f - 4‖ + ‖Mobius.mobiusCommutatorTrace f g - 2‖ = 1 :=
  ⟨jorgensenSharpnessTranslation, jorgensenSharpnessInversion, jorgensenSharpnessGroup_discrete,
    jorgensenSharpnessGroup_nonElementary, jorgensenSharpness_defect_eq_one⟩

end LowDimensionalTopology.Geometry.DiscreteGroups
