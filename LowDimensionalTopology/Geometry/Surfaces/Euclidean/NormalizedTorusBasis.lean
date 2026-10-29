module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

open Module

namespace LowDimensionalTopology.Geometry.Surfaces

/-- The ordered real basis `1, τ`, defined by its actual real coordinates.
This construction makes no assertion about canonical topological markings. -/
def normalizedTorusBasis (τ : UpperHalfPlane) : Basis (Fin 2) ℝ ℂ :=
  Basis.ofEquivFun
    { toFun := fun z => ![z.re - z.im / τ.im * τ.re, z.im / τ.im]
      invFun := fun c => (c 0 : ℂ) + (c 1 : ℂ) * (τ : ℂ)
      left_inv := fun z => by
        apply Complex.ext <;>
          simp [Complex.mul_re, Complex.mul_im, τ.im_ne_zero]
      right_inv := fun c => by
        ext i
        fin_cases i <;>
          simp [Complex.mul_re, Complex.mul_im, τ.im_ne_zero]
      map_add' := fun z w => by
        ext i
        fin_cases i
        · simp [add_div, add_mul]
          ring
        · simp [add_div]
      map_smul' := fun r z => by
        ext i
        fin_cases i <;>
          simp [Complex.real_smul, Complex.mul_re, Complex.mul_im] <;> ring }

@[simp]
theorem normalizedTorusBasis_zero (τ : UpperHalfPlane) :
    normalizedTorusBasis τ 0 = 1 := by
  apply Basis.apply_eq_iff.mpr
  ext j
  fin_cases j <;>
    simp [normalizedTorusBasis, Basis.ofEquivFun_repr_apply]

@[simp]
theorem normalizedTorusBasis_one (τ : UpperHalfPlane) :
    normalizedTorusBasis τ 1 = (τ : ℂ) := by
  apply Basis.apply_eq_iff.mpr
  ext j
  fin_cases j <;>
    simp [normalizedTorusBasis, Basis.ofEquivFun_repr_apply, τ.im_ne_zero]

/-- The integer period lattice of this actual real basis is `ℤ + ℤ τ`. -/
theorem normalizedTorusBasis_span (τ : UpperHalfPlane) :
    Submodule.span ℤ (Set.range (normalizedTorusBasis τ)) =
      Submodule.span ℤ ({(1 : ℂ), (τ : ℂ)} : Set ℂ) := by
  have hr : Set.range (normalizedTorusBasis τ) = {(1 : ℂ), (τ : ℂ)} := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨0, normalizedTorusBasis_zero τ⟩
      · exact ⟨1, normalizedTorusBasis_one τ⟩
  rw [hr]

end LowDimensionalTopology.Geometry.Surfaces
