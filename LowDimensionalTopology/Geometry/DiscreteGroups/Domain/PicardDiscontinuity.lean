/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.LimitSet.MobiusOrbitLimits
public import Mathlib.Topology.Instances.Rat
@[expose] public section
open Set Filter Matrix
open scoped Topology OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
noncomputable section

/-- The actual Picard group is the geometric image of the Gaussian determinant-one matrix group. -/
def picardMobiusGroup : Subgroup Mobius.complexMobiusGroup :=
  DiscreteGroups.MatrixGroups.picardGroup.map Mobius.mobiusSpecialLinearProjection

theorem picardMobiusGroup_discrete : Mobius.IsDiscreteMobiusSubgroup picardMobiusGroup := by
  let : DiscreteTopology DiscreteGroups.MatrixGroups.picardGroup := DiscreteGroups.MatrixGroups.picardGroup_discrete
  exact Mobius.discreteSpecialLinear_image DiscreteGroups.MatrixGroups.picardGroup

/-- A determinant-one Gaussian matrix with the prescribed finite parabolic fixed point. -/
def picardParabolicGaussian (p : GaussianInt) (r : ℤ) :
    Matrix.SpecialLinearGroup (Fin 2) GaussianInt :=
  ⟨!![1 - p * r, p ^ 2; -(r : GaussianInt) ^ 2, 1 + p * r], by
    rw [Matrix.det_fin_two]
    dsimp
    ring⟩

def picardParabolicLift (p : GaussianInt) (r : ℤ) : Auxiliary.Algebra.SpecialLinear2 :=
  Matrix.SpecialLinearGroup.map GaussianInt.toComplex (picardParabolicGaussian p r)

theorem picardParabolicLift_matrix (p : GaussianInt) (r : ℤ) :
    (picardParabolicLift p r : Auxiliary.Algebra.ComplexMatrix2) =
      !![1 - (p : ℂ) * r, (p : ℂ) ^ 2; -(r : ℂ) ^ 2, 1 + (p : ℂ) * r] := by
  ext i j
  change GaussianInt.toComplex ((picardParabolicGaussian p r) i j) = _
  fin_cases i <;> fin_cases j <;> simp [picardParabolicGaussian]

theorem picardParabolicLift_mem (p : GaussianInt) (r : ℤ) :
    picardParabolicLift p r ∈ DiscreteGroups.MatrixGroups.picardGroup :=
  ⟨picardParabolicGaussian p r, rfl⟩

theorem picardParabolic_projection_ne_one (p : GaussianInt) (r : ℤ) (hr : r ≠ 0) :
    Mobius.mobiusSpecialLinearProjection (picardParabolicLift p r) ≠ 1 := by
  intro he
  rcases (Mobius.mobiusSpecialLinearProjection_eq_one_iff _).mp he with h | h
  all_goals
    have hc := congrArg (fun A : Auxiliary.Algebra.ComplexMatrix2 => A 1 0) h
    rw [picardParabolicLift_matrix] at hc
    simp at hc
    exact hr (by exact_mod_cast hc)

theorem picardParabolic_projection_parabolic (p : GaussianInt) (r : ℤ) (hr : r ≠ 0) :
    Mobius.MobiusParabolic (Mobius.mobiusSpecialLinearProjection (picardParabolicLift p r)) := by
  apply (Mobius.mobius_parabolic_iff_squaredTrace_eq_four _ (picardParabolic_projection_ne_one p r hr)).mpr
  rw [Mobius.mobiusSquaredTrace_specialLinearProjection, Matrix.trace_fin_two]
  rw [show (picardParabolicLift p r) 0 0 = 1 - (p : ℂ) * r from
    congrArg (fun A : Auxiliary.Algebra.ComplexMatrix2 => A 0 0) (picardParabolicLift_matrix p r)]
  rw [show (picardParabolicLift p r) 1 1 = 1 + (p : ℂ) * r from
    congrArg (fun A : Auxiliary.Algebra.ComplexMatrix2 => A 1 1) (picardParabolicLift_matrix p r)]
  ring

theorem picardParabolic_projection_fixed (p : GaussianInt) (r : ℤ) (hr : r ≠ 0) :
    (Mobius.mobiusSpecialLinearProjection (picardParabolicLift p r)).val
      (((p : ℂ) / r : ℂ) : Mobius.ExtendedComplex) = (((p : ℂ) / r : ℂ) : Mobius.ExtendedComplex) := by
  rw [Mobius.invariantDisc_specialLinear_action, Mobius.fractionalLinear_coe]
  have hrC : (r : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hr
  have hm := picardParabolicLift_matrix p r
  have hden : (-(r : ℂ) ^ 2) * ((p : ℂ) / r) + (1 + (p : ℂ) * r) = 1 := by
    field_simp; ring
  have hnum : (1 - (p : ℂ) * r) * ((p : ℂ) / r) + (p : ℂ) ^ 2 = (p : ℂ) / r := by
    field_simp; ring
  change (if (picardParabolicLift p r) 1 0 * ((p : ℂ) / r) +
      (picardParabolicLift p r) 1 1 = 0 then ∞ else
      ((((picardParabolicLift p r) 0 0 * ((p : ℂ) / r) + (picardParabolicLift p r) 0 1) /
        ((picardParabolicLift p r) 1 0 * ((p : ℂ) / r) + (picardParabolicLift p r) 1 1) : ℂ) :
          Mobius.ExtendedComplex)) = _
  simp only [show (picardParabolicLift p r) 1 0 = -(r : ℂ) ^ 2 from
    congrArg (fun A : Auxiliary.Algebra.ComplexMatrix2 => A 1 0) hm,
    show (picardParabolicLift p r) 1 1 = 1 + (p : ℂ) * r from
    congrArg (fun A : Auxiliary.Algebra.ComplexMatrix2 => A 1 1) hm,
    show (picardParabolicLift p r) 0 0 = 1 - (p : ℂ) * r from
    congrArg (fun A : Auxiliary.Algebra.ComplexMatrix2 => A 0 0) hm,
    show (picardParabolicLift p r) 0 1 = (p : ℂ) ^ 2 from
    congrArg (fun A : Auxiliary.Algebra.ComplexMatrix2 => A 0 1) hm,
    hden, hnum, one_ne_zero, ite_false, div_one]

/-- Complex rational-coordinate points admit the real-integer denominator used in the source example. -/
theorem picard_rational_pair_quotient (a b : ℚ) :
    ∃ p : GaussianInt, ∃ r : ℤ, r ≠ 0 ∧ (a : ℂ) + (b : ℂ) * Complex.I = (p : ℂ) / r := by
  refine ⟨⟨a.num * b.den, b.num * a.den⟩, (a.den * b.den : ℕ), ?_, ?_⟩
  · exact_mod_cast mul_ne_zero a.den_nz b.den_nz
  · rw [GaussianInt.toComplex_def']
    have ha : (a : ℂ) = (a.num : ℂ) / a.den := by exact_mod_cast a.num_div_den.symm
    have hb : (b : ℂ) = (b.num : ℂ) / b.den := by exact_mod_cast b.num_div_den.symm
    rw [ha, hb]
    push_cast
    field_simp

/-- Rational real and imaginary coordinates are dense in the actual complex plane. -/
theorem picard_rational_pair_denseRange :
    DenseRange (fun x : ℚ × ℚ => (x.1 : ℂ) + (x.2 : ℂ) * Complex.I) := by
  have hp : DenseRange (fun x : ℚ × ℚ => ((x.1 : ℝ), (x.2 : ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hh := Complex.equivRealProdCLM.symm.toHomeomorph.surjective.denseRange.comp hp
    Complex.equivRealProdCLM.symm.continuous
  change DenseRange (fun x : ℚ × ℚ => Complex.equivRealProdCLM.symm ((x.1 : ℝ), (x.2 : ℝ))) at hh
  simpa only [Complex.equivRealProdCLM_symm_apply, Complex.ofReal_ratCast] using hh

/-- The image definition has exactly the Gaussian-entry coefficient interpretation. -/
theorem mem_picardMobiusGroup_iff (f : Mobius.complexMobiusGroup) :
    f ∈ picardMobiusGroup ↔ ∃ A : Auxiliary.Algebra.SpecialLinear2,
      (∀ i j, ∃ z : GaussianInt, (z : ℂ) = A i j) ∧ Mobius.mobiusSpecialLinearProjection A = f := by
  change f ∈ DiscreteGroups.MatrixGroups.picardGroup.map Mobius.mobiusSpecialLinearProjection ↔ _
  simp only [Subgroup.mem_map, DiscreteGroups.MatrixGroups.mem_picardGroup_iff]

/-- The actual parabolic fixed-point set used. -/
def picardParabolicFixedPointSet : Set Mobius.ExtendedComplex :=
  {z | ∃ g : picardMobiusGroup, Mobius.MobiusParabolic g.val ∧ g.val.val z = z}

theorem picard_rational_pair_mem_fixedPointSet (a b : ℚ) :
    (((a : ℂ) + (b : ℂ) * Complex.I : ℂ) : Mobius.ExtendedComplex) ∈ picardParabolicFixedPointSet := by
  obtain ⟨p, r, hr, he⟩ := picard_rational_pair_quotient a b
  let A := picardParabolicLift p r
  have hA : Mobius.mobiusSpecialLinearProjection A ∈ picardMobiusGroup :=
    Subgroup.mem_map.mpr ⟨A, picardParabolicLift_mem p r, rfl⟩
  refine ⟨⟨Mobius.mobiusSpecialLinearProjection A, hA⟩, picardParabolic_projection_parabolic p r hr, ?_⟩
  rw [he]
  exact picardParabolic_projection_fixed p r hr

theorem picardParabolicFixedPointSet_dense : Dense picardParabolicFixedPointSet := by
  have hd : DenseRange (fun x : ℚ × ℚ =>
      (((x.1 : ℂ) + (x.2 : ℂ) * Complex.I : ℂ) : Mobius.ExtendedComplex)) :=
    OnePoint.denseRange_coe.comp picard_rational_pair_denseRange OnePoint.continuous_coe
  apply Dense.mono _ hd
  rintro z ⟨x, rfl⟩
  exact picard_rational_pair_mem_fixedPointSet x.1 x.2

/-- Picard's group has no nonempty open sphere domain satisfying ambient discontinuity. -/
theorem picardMobiusGroup_no_open_discontinuity (D : Set Mobius.ExtendedComplex)
    (hD : IsOpen D) (hne : D.Nonempty) : ¬IsMobiusDiscontinuousOn picardMobiusGroup D := by
  intro hdisc
  obtain ⟨z, hzD, g, hg, hfix⟩ := picardParabolicFixedPointSet_dense.inter_open_nonempty D hD hne
  exact not_discontinuous_on_set_containing_parabolic_or_loxodromic_fixedPoint picardMobiusGroup D g (Or.inl hg) z
    hzD hfix hdisc

/-- discreteness, dense parabolic fixed points and no open discontinuity domain. -/
theorem picard_discrete_parabolic_fixedPoints_dense_nowhere_discontinuous : Mobius.IsDiscreteMobiusSubgroup
    picardMobiusGroup ∧
    Dense picardParabolicFixedPointSet ∧
      ∀ D : Set Mobius.ExtendedComplex, IsOpen D → D.Nonempty →
        ¬IsMobiusDiscontinuousOn picardMobiusGroup D :=
  ⟨picardMobiusGroup_discrete, picardParabolicFixedPointSet_dense,
    picardMobiusGroup_no_open_discontinuity⟩

end
end LowDimensionalTopology.Geometry.DiscreteGroups
