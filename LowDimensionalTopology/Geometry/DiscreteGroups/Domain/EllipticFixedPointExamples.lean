/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.DiscreteGroups.Domain.PicardDiscontinuity
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenSharpness
public import LowDimensionalTopology.Geometry.DiscreteGroups.Packing.MobiusPackings
@[expose] public section
open Set Filter
open scoped Topology OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
noncomputable section

/-- The negative reciprocal is a nonidentity actual elliptic Mobius map. -/
theorem modularInversion_elliptic : Mobius.MobiusElliptic jorgensenSharpnessInversion := by
  have hn : jorgensenSharpnessInversion ≠ 1 := by
    intro h
    have hi := jorgensenSharpnessInversion_infty
    rw [h] at hi
    exact OnePoint.coe_ne_infty (0 : ℂ) hi.symm
  apply (Mobius.mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four _ hn).mpr
  refine ⟨0, le_rfl, by norm_num, ?_⟩
  rw [jorgensenSharpnessInversion, Mobius.mobiusSquaredTrace_specialLinearProjection]
  norm_num [Matrix.trace_fin_two, jorgensenSharpnessInversionLift]

theorem modularInversion_fixed_I :
    jorgensenSharpnessInversion.val (Complex.I : ℂ) = (Complex.I : ℂ) := by
  rw [jorgensenSharpnessInversion_coe Complex.I Complex.I_ne_zero]
  norm_num [Complex.div_I]

/-- Both integral modular generators preserve the actual standard upper half-disc. -/
theorem modularGroup_preserves_halfDisc (g : jorgensenSharpnessGroup) :
    g.val.val '' Mobius.standardComplexHalfDisc = Mobius.standardComplexHalfDisc := by
  let K : Subgroup Mobius.complexMobiusGroup :=
    MulAction.stabilizer Mobius.complexMobiusGroup Mobius.standardComplexHalfDisc
  have hle : jorgensenSharpnessGroup ≤ K := by
    apply (Subgroup.closure_le K).mpr
    intro f hf
    rcases Set.mem_insert_iff.mp hf with h | h
    · subst f
      exact Mobius.unitTranslation_preserves_standardHalfDisc
    · have h : f = jorgensenSharpnessInversion := Set.mem_singleton_iff.mp h
      subst f
      apply Mobius.specialLinear_real_preserves_halfDisc jorgensenSharpnessInversionLift
      intro i j
      fin_cases i <;> fin_cases j <;> norm_num [jorgensenSharpnessInversionLift]
  exact hle g.property

/-- The standard modular elliptic fixed point is genuinely an ordinary point. -/
theorem modularInversion_fixed_I_ordinary :
    (Complex.I : Mobius.ExtendedComplex) ∈ mobiusOrdinarySet jorgensenSharpnessGroup := by
  have hi : (Complex.I : Mobius.ExtendedComplex) ∈ Mobius.standardComplexHalfDisc := by
    apply mem_connectedComponentIn
    simp
  have hproper : Mobius.standardComplexHalfDisc ≠ Set.univ := by
    intro h
    have hz : ((0 : ℂ) : Mobius.ExtendedComplex) ∈ Mobius.standardComplexHalfDisc := by rw [h]; trivial
    have hz' := connectedComponentIn_subset Mobius.complexRealAxisᶜ (Complex.I : Mobius.ExtendedComplex) hz
    simp at hz'
  exact mobius_proper_invariant_open_subset_ordinary jorgensenSharpnessGroup
    jorgensenSharpnessGroup_nonElementary Mobius.standardComplexHalfDisc
    Mobius.standardComplexHalfDisc_isDisc.isOpen hproper
    (fun g z hz => by rw [← modularGroup_preserves_halfDisc g]; exact ⟨z, hz, rfl⟩) hi

/-- The actual Picard subgroup is non-elementary because it contains the modular subgroup. -/
theorem picardMobiusGroup_nonElementary : IsNonElementary picardMobiusGroup := by
  intro h
  exact jorgensenSharpnessGroup_nonElementary (h.mono jorgensenSharpnessGroup_le_picard)

/-- The dense Gaussian parabolic fixed points force the actual Picard limit set to be the sphere. -/
theorem picardMobiusGroup_limitSet : mobiusLimitSet picardMobiusGroup = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  apply (mobiusLimitSet_isClosed picardMobiusGroup).closure_subset_iff.mpr ?_
    (picardParabolicFixedPointSet_dense.closure_eq ▸ Set.mem_univ z)
  rintro w ⟨g, hg, hw⟩
  exact mobius_parabolic_fixed_mem_limitSet picardMobiusGroup picardMobiusGroup_nonElementary
    g hg w hw

/-- The same genuine elliptic fixed point belongs to the larger Picard group's limit set. -/
theorem modularInversion_fixed_I_picard_limit :
    (Complex.I : Mobius.ExtendedComplex) ∈ mobiusLimitSet picardMobiusGroup := by
  rw [picardMobiusGroup_limitSet]
  trivial

/-- elliptic fixed points can occur in either set, even for discrete non-elementary groups. -/
theorem mobius_elliptic_fixed_points_either_set :
    (∃ H : Subgroup Mobius.complexMobiusGroup, Mobius.IsDiscreteMobiusSubgroup H ∧ IsNonElementary H ∧
      ∃ f : H, Mobius.MobiusElliptic f.val ∧ ∃ z : Mobius.ExtendedComplex,
        f.val.val z = z ∧ z ∈ mobiusOrdinarySet H) ∧
    (∃ H : Subgroup Mobius.complexMobiusGroup, Mobius.IsDiscreteMobiusSubgroup H ∧ IsNonElementary H ∧
      ∃ f : H, Mobius.MobiusElliptic f.val ∧ ∃ z : Mobius.ExtendedComplex,
        f.val.val z = z ∧ z ∈ mobiusLimitSet H) := by
  constructor
  · exact ⟨jorgensenSharpnessGroup, jorgensenSharpnessGroup_discrete,
      jorgensenSharpnessGroup_nonElementary,
      ⟨jorgensenSharpnessInversion, jorgensenSharpnessGroup_generators.2⟩,
      modularInversion_elliptic, Complex.I, modularInversion_fixed_I,
      modularInversion_fixed_I_ordinary⟩
  · exact ⟨picardMobiusGroup, picardMobiusGroup_discrete,
      picardMobiusGroup_nonElementary,
      ⟨jorgensenSharpnessInversion,
        jorgensenSharpnessGroup_le_picard jorgensenSharpnessGroup_generators.2⟩,
      modularInversion_elliptic, Complex.I, modularInversion_fixed_I,
      modularInversion_fixed_I_picard_limit⟩

end
end LowDimensionalTopology.Geometry.DiscreteGroups
