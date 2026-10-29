module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
public import LowDimensionalTopology.External.LiZhongQC.Ch11.S36_Hamilton

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set
open scoped UpperHalfPlane Manifold

namespace LowDimensionalTopology.Geometry.Teichmuller.AutomorphicQuadratic

/-- All holomorphic quadratic coefficients on the upper half-plane that
satisfy the literal pointwise automorphy law. No norm bound is imposed. -/
def coefficientSubmodule
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :
    Submodule ℂ (ℍ → ℂ) where
  carrier := {f | MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧
    ∀ γ ∈ Γ, ∀ z : ℍ,
      f (γ • z) * deriv (LiZhongQC.h36p_m γ) (z : ℂ) ^ 2 = f z}
  zero_mem' := ⟨mdifferentiable_const, fun _ _ _ => by simp⟩
  add_mem' := by
    rintro f g ⟨hf, ha⟩ ⟨hg, hb⟩
    refine ⟨hf.add hg, fun γ hγ z => ?_⟩
    simp only [Pi.add_apply, add_mul, ha γ hγ z, hb γ hγ z]
  smul_mem' := by
    rintro c f ⟨hf, ha⟩
    refine ⟨MDifferentiable.const_smul c hf, fun γ hγ z => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ha γ hγ z]

/-- The full complex vector space of unweighted holomorphic automorphic forms. -/
abbrev Space (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)) :=
  ↥(coefficientSubmodule Γ)

/-- Complex differentiability in the native half-plane charts and the
literal derivative law agree with the usual denominator-four presentation. -/
theorem mem_coefficientSubmodule_iff
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (f : ℍ → ℂ) :
    f ∈ coefficientSubmodule Γ ↔
      DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) LiZhongQC.upperHalf ∧
        ∀ γ ∈ Γ, ∀ z : ℍ,
          f (γ • z) / ((γ 1 0 : ℂ) * (z : ℂ) + γ 1 1) ^ 4 = f z := by
  constructor
  · rintro ⟨hf, ha⟩
    refine ⟨UpperHalfPlane.mdifferentiable_iff.mp hf, fun γ hγ z => ?_⟩
    have h := ha γ hγ z
    rw [(LiZhongQC.h36p_m_hasDerivAt γ z.im_pos).deriv] at h
    simpa only [div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow, ← pow_mul] using h
  · rintro ⟨hf, ha⟩
    refine ⟨UpperHalfPlane.mdifferentiable_iff.mpr hf, fun γ hγ z => ?_⟩
    rw [(LiZhongQC.h36p_m_hasDerivAt γ z.im_pos).deriv]
    simpa only [div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow, ← pow_mul] using ha γ hγ z

end LowDimensionalTopology.Geometry.Teichmuller.AutomorphicQuadratic
