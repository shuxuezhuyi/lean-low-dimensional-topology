module
public import LowDimensionalTopology.Geometry.Mobius.Classification
public import LowDimensionalTopology.Geometry.Mobius.FractionalLinear
public import LowDimensionalTopology.Geometry.Mobius.ReflectionEquivalence
public import LowDimensionalTopology.Geometry.Mobius.Trace.MobiusInvariants
public import Mathlib.Tactic.Ring

/-!
# Affine Möbius transformations and their multipliers.

The stabilizer of infinity has affine representatives with uniquely determined
coefficients. The linear coefficient defines a homomorphism, which restricts to any
subgroup fixing infinity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Function Filter
open scoped OnePoint ComplexConjugate Pointwise RealInnerProductSpace

namespace LowDimensionalTopology.Geometry.Mobius

/-- The actual geometric Mobius maps that fix infinity. -/
def mobiusInftyStabilizer : Subgroup complexMobiusGroup where
  carrier := {f | (f : Equiv.Perm ExtendedComplex) ∞ = ∞}
  one_mem' := rfl
  mul_mem' {f g} hf hg := by
    change (f : Equiv.Perm ExtendedComplex) ((g : Equiv.Perm ExtendedComplex) ∞) = ∞
    rw [hg, hf]
  inv_mem' {f} hf := by
    apply (f : Equiv.Perm ExtendedComplex).injective
    change (f : Equiv.Perm ExtendedComplex) ((f : Equiv.Perm ExtendedComplex).symm ∞) =
      (f : Equiv.Perm ExtendedComplex) ∞
    rw [Equiv.apply_symm_apply, hf]

/-- Fixing infinity gives an affine representation in the actual geometric Mobius group. -/
theorem mobius_affine_of_fixes_infty (f : complexMobiusGroup)
    (hfix : (f : Equiv.Perm ExtendedComplex) ∞ = ∞) :
    ∃ a : ℂˣ, ∃ b : ℂ, f = mobiusMatrixProjection (Classification.affineMatrix a b) := by
  have hfix' : (complexMobiusEquivFractionalLinear f : Equiv.Perm ExtendedComplex) ∞ = ∞ := by
    simpa only [complexMobiusEquivFractionalLinear_apply] using hfix
  obtain ⟨a, b, hab⟩ := Classification.affine_of_fixes_infty
    (complexMobiusEquivFractionalLinear f) hfix'
  refine ⟨a, b, complexMobiusEquivFractionalLinear.injective ?_⟩
  rw [mobiusMatrixProjection_equiv]
  exact hab

/-- Two affine formulas have the same coefficients. -/
theorem affine_coefficients_unique {a a' : ℂˣ} {b b' : ℂ}
    (h : ∀ z : ℂ, (a : ℂ) * z + b = (a' : ℂ) * z + b') : a = a' ∧ b = b' := by
  have hb : b = b' := by simpa only [mul_zero, zero_add] using h 0
  have ha : (a : ℂ) = (a' : ℂ) := by
    have h1 := h 1
    rw [mul_one, mul_one, hb] at h1
    exact add_right_cancel h1
  exact ⟨Units.ext ha, hb⟩

/-- Multiplication by a nonzero complex number as an actual geometric Mobius map. -/
def mobiusScaling (a : ℂˣ) : complexMobiusGroup :=
  mobiusMatrixProjection (Classification.affineMatrix a 0)

/-- The multiplier is the nonzero linear coefficient of the affine representative. -/
def mobiusMultiplier (f : mobiusInftyStabilizer) : ℂˣ :=
  Classical.choose (mobius_affine_of_fixes_infty f.1 f.2)

/-- The translation coefficient of the chosen affine representative. -/
def mobiusAffineConstant (f : mobiusInftyStabilizer) : ℂ :=
  Classical.choose (Classical.choose_spec (mobius_affine_of_fixes_infty f.1 f.2))

theorem mobiusScaling_coe (a : ℂˣ) (z : ℂ) :
    (mobiusScaling a : Equiv.Perm ExtendedComplex) z = ((a : ℂ) * z : ℂ) := by
  rw [mobiusScaling, mobiusMatrixProjection_apply, Classification.affineMatrix_coe]
  simp

theorem mobiusScaling_infty (a : ℂˣ) :
    (mobiusScaling a : Equiv.Perm ExtendedComplex) ∞ = ∞ := by
  rw [mobiusScaling, mobiusMatrixProjection_apply, Classification.affineMatrix_infty]

/-- An actual map fixing zero and infinity is a genuine complex multiplication map. -/
theorem mobius_fix_zero_infty_eq_scaling (f : complexMobiusGroup)
    (hzero : (f : Equiv.Perm ExtendedComplex) (0 : ℂ) = (0 : ℂ))
    (hinfty : (f : Equiv.Perm ExtendedComplex) ∞ = ∞) :
    ∃ a : ℂˣ, f = mobiusScaling a := by
  obtain ⟨a, b, hf⟩ := mobius_affine_of_fixes_infty f hinfty
  have hb : b = 0 := by
    rw [hf, mobiusMatrixProjection_apply, Classification.affineMatrix_coe] at hzero
    have h := OnePoint.coe_injective hzero
    simpa only [mul_zero, zero_add] using h
  exact ⟨a, by simpa only [hb, mobiusScaling] using hf⟩

theorem mobius_affine_representation (f : mobiusInftyStabilizer) :
    f.1 = mobiusMatrixProjection
      (Classification.affineMatrix (mobiusMultiplier f) (mobiusAffineConstant f)) :=
  Classical.choose_spec (Classical.choose_spec (mobius_affine_of_fixes_infty f.1 f.2))

/-- The coefficient formula is the actual action on every finite complex point. -/
theorem mobius_affine_formula (f : mobiusInftyStabilizer) (z : ℂ) :
    (f.1 : Equiv.Perm ExtendedComplex) (z : ExtendedComplex) =
      (((mobiusMultiplier f : ℂ) * z + mobiusAffineConstant f : ℂ) : ExtendedComplex) := by
  rw [mobius_affine_representation f, mobiusMatrixProjection_apply,
    Classification.affineMatrix_coe]

/-- The chosen multiplier and constant are independent of the affine representation. -/
theorem mobius_affine_parameters_unique (f : mobiusInftyStabilizer) {a : ℂˣ} {b : ℂ}
    (h : ∀ z : ℂ, (f.1 : Equiv.Perm ExtendedComplex) z = ((a : ℂ) * z + b : ℂ)) :
    mobiusMultiplier f = a ∧ mobiusAffineConstant f = b := by
  apply affine_coefficients_unique
  intro z
  apply OnePoint.coe_injective
  exact (mobius_affine_formula f z).symm.trans (h z)

/-- Composition multiplies the linear coefficients and has the usual affine constant. -/
theorem mobius_affine_parameters_mul (f g : mobiusInftyStabilizer) :
    mobiusMultiplier (f * g) = mobiusMultiplier f * mobiusMultiplier g ∧
      mobiusAffineConstant (f * g) =
        (mobiusMultiplier f : ℂ) * mobiusAffineConstant g + mobiusAffineConstant f := by
  apply mobius_affine_parameters_unique
  intro z
  change (f.1 : Equiv.Perm ExtendedComplex) ((g.1 : Equiv.Perm ExtendedComplex) z) = _
  rw [mobius_affine_formula g, mobius_affine_formula f]
  congr 1
  simp only [Units.val_mul]
  ring

/-- The identity has multiplier one and constant zero. -/
theorem mobius_affine_parameters_one :
    mobiusMultiplier 1 = 1 ∧ mobiusAffineConstant 1 = 0 := by
  apply mobius_affine_parameters_unique
  intro z
  simp

/-- The multiplier is a homomorphism on the full infinity stabilizer. -/
def mobiusMultiplierHom : mobiusInftyStabilizer →* ℂˣ where
  toFun := mobiusMultiplier
  map_one' := mobius_affine_parameters_one.1
  map_mul' f g := (mobius_affine_parameters_mul f g).1

/-- Restrict the actual multiplier homomorphism to any subgroup fixing infinity. -/
def subgroupMultiplierHom (G : Subgroup complexMobiusGroup) (hG : G ≤ mobiusInftyStabilizer) :
    G →* ℂˣ := mobiusMultiplierHom.comp (Subgroup.inclusion hG)

/-- The multipliers in the specified subgroup form a multiplicative subgroup. -/
def subgroupMultiplierRange (G : Subgroup complexMobiusGroup) (hG : G ≤ mobiusInftyStabilizer) :
    Subgroup ℂˣ := (subgroupMultiplierHom G hG).range

end LowDimensionalTopology.Geometry.Mobius
