/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.StandardAutomorphisms
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ConformalTypes
public import Mathlib.Analysis.Complex.UpperHalfPlane.FixedPoints
public import Mathlib.Analysis.Complex.UpperHalfPlane.Manifold
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

/-!
# The real projective special linear group as Aut(H)

The quotient is Mathlib's existing `PSL(2, ℝ)`. Its target consists of actual
homeomorphisms of the original upper half-plane, holomorphic in both directions.
The real determinant-one action is onto this target and has exactly the sign
kernel. No orientation-reversing general-linear action is included.
-/

@[expose] public section
noncomputable section

set_option autoImplicit false

open scoped UpperHalfPlane MatrixGroups Manifold

namespace LowDimensionalTopology.Geometry.Surfaces

/-- Biholomorphic self-homeomorphisms of the actual upper-half-plane manifold. -/
def upperHalfPlaneHolomorphicAutomorphismSubgroup : Subgroup (ℍ ≃ₜ ℍ) where
  carrier := {H | MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H ∧
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H.symm}
  one_mem' := ⟨mdifferentiable_id, mdifferentiable_id⟩
  mul_mem' := by
    intro F G hF hG
    exact ⟨hF.1.comp hG.1, hG.2.comp hF.2⟩
  inv_mem' := by
    intro F hF
    exact ⟨hF.2, hF.1⟩

/-- The real determinant-one action as actual biholomorphic homeomorphisms. -/
def realSLUpperHalfPlaneAutHom : SL(2, ℝ) →*
    upperHalfPlaneHolomorphicAutomorphismSubgroup where
  toFun A := ⟨Homeomorph.smul (α := ℍ) (Matrix.SpecialLinearGroup.mapGL ℝ A), by
    constructor
    · exact UpperHalfPlane.mdifferentiable_smul (by simp)
    · rw [Homeomorph.smul_symm]
      exact UpperHalfPlane.mdifferentiable_smul (by simp)⟩
  map_one' := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro z
    change (Matrix.SpecialLinearGroup.mapGL ℝ (1 : SL(2, ℝ))) • z = z
    simp only [map_one, one_smul]
  map_mul' A B := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro z
    change (A * B) • z = A • (B • z)
    exact mul_smul A B z

/-- This is the original special-linear action on every actual point. -/
theorem realSLUpperHalfPlaneAutHom_apply (A : SL(2, ℝ)) (z : ℍ) :
    (realSLUpperHalfPlaneAutHom A).val z = A • z := rfl

private theorem exists_realSLUpperHalfPlaneAut_eq (H : ℍ ≃ₜ ℍ)
    (hH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H) :
    ∃ A : SL(2, ℝ), (realSLUpperHalfPlaneAutHom A).val = H := by
  obtain ⟨A, _, hA⟩ := upperHalfPlane_analytic_automorphism_real_form H hH
  refine ⟨A, Homeomorph.ext fun z => ?_⟩
  apply UpperHalfPlane.ext
  exact (LiZhongQC.h36t_coe_smul A z).trans (hA z).2.symm

/-- For a homeomorphism, the inverse holomorphicity in the group definition is
automatic; the target contains every holomorphic self-homeomorphism. -/
theorem mem_upperHalfPlaneHolomorphicAutomorphismSubgroup_iff (H : ℍ ≃ₜ ℍ) :
    H ∈ upperHalfPlaneHolomorphicAutomorphismSubgroup ↔
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H := by
  constructor
  · exact fun h => h.1
  · intro hH
    obtain ⟨A, hA⟩ := exists_realSLUpperHalfPlaneAut_eq H hH
    exact hA ▸ (realSLUpperHalfPlaneAutHom A).property

/-- Every actual biholomorphic upper-half-plane automorphism comes from SL(2,R). -/
theorem realSLUpperHalfPlaneAutHom_surjective :
    Function.Surjective realSLUpperHalfPlaneAutHom := by
  intro H
  obtain ⟨A, hA⟩ := exists_realSLUpperHalfPlaneAut_eq H.val H.property.1
  exact ⟨A, Subtype.ext hA⟩

private theorem realSL_mapGL_eq_toGL (A : SL(2, ℝ)) :
    Matrix.SpecialLinearGroup.mapGL ℝ A = Matrix.SpecialLinearGroup.toGL A := by
  ext i j
  rfl

/-- The action kernel is exactly the center used in Mathlib's PSL quotient. -/
theorem realSLUpperHalfPlaneAutHom_kernel :
    realSLUpperHalfPlaneAutHom.ker = Subgroup.center SL(2, ℝ) := by
  ext A
  rw [MonoidHom.mem_ker]
  constructor
  · intro hA
    have hfix : ∀ z : ℍ, (Matrix.SpecialLinearGroup.mapGL ℝ A) • z = z := by
      intro z
      exact congrArg (fun H : upperHalfPlaneHolomorphicAutomorphismSubgroup => H.val z) hA
    have hc := UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mp hfix
    rw [realSL_mapGL_eq_toGL] at hc
    exact (Matrix.SpecialLinearGroup.toGL_mem_center_iff A).mp hc
  · intro hA
    have hc := (Matrix.SpecialLinearGroup.toGL_mem_center_iff A).mpr hA
    have hfix := UpperHalfPlane.forall_smul_eq_self_iff_mem_center.mpr hc
    apply Subtype.ext
    apply Homeomorph.ext
    intro z
    change (Matrix.SpecialLinearGroup.mapGL ℝ A) • z = z
    rw [realSL_mapGL_eq_toGL]
    exact hfix z

/-- In degree two over R the quotient center consists of precisely I and -I. -/
theorem realSL_mem_center_iff_sign (A : SL(2, ℝ)) :
    A ∈ Subgroup.center SL(2, ℝ) ↔ A = 1 ∨ A = -1 := by
  constructor
  · intro hA
    obtain ⟨r, hr, he⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
    have hr2 : r ^ 2 = 1 := by simpa only [Fintype.card_fin] using hr
    rcases sq_eq_one_iff.mp hr2 with hr | hr
    · left
      apply Subtype.ext
      simpa [hr] using he.symm
    · right
      apply Subtype.ext
      simpa only [hr, map_neg, map_one, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.SpecialLinearGroup.coe_one] using he.symm
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨-1, by norm_num, by
        simp only [map_neg, map_one, Matrix.SpecialLinearGroup.coe_neg,
          Matrix.SpecialLinearGroup.coe_one]⟩

/-- The action forgets exactly the two scalar signs, not any further matrices. -/
theorem realSLUpperHalfPlaneAutHom_eq_one_iff (A : SL(2, ℝ)) :
    realSLUpperHalfPlaneAutHom A = 1 ↔ A = 1 ∨ A = -1 := by
  change A ∈ realSLUpperHalfPlaneAutHom.ker ↔ _
  rw [realSLUpperHalfPlaneAutHom_kernel]
  exact realSL_mem_center_iff_sign A

/-- PSL(2,R), with Mathlib's literal quotient carrier, is the full actual Aut(H). -/
def realPSLUpperHalfPlaneAutEquiv : Matrix.ProjectiveSpecialLinearGroup (Fin 2) ℝ ≃*
    upperHalfPlaneHolomorphicAutomorphismSubgroup :=
  QuotientGroup.liftEquiv (Subgroup.center SL(2, ℝ))
    realSLUpperHalfPlaneAutHom_surjective realSLUpperHalfPlaneAutHom_kernel.symm

/-- The quotient identification retains the original determinant-one action. -/
theorem realPSLUpperHalfPlaneAutEquiv_mk (A : SL(2, ℝ)) :
    realPSLUpperHalfPlaneAutEquiv (QuotientGroup.mk A) = realSLUpperHalfPlaneAutHom A :=
  QuotientGroup.liftEquiv_mk _ _ _ A

/-- The identified automorphism has the original real fractional-linear formula. -/
theorem realPSLUpperHalfPlaneAutEquiv_mk_apply (A : SL(2, ℝ)) (z : ℍ) :
    ((realPSLUpperHalfPlaneAutEquiv (QuotientGroup.mk A)).val z : ℂ) =
      ((A 0 0 : ℂ) * z + A 0 1) / ((A 1 0 : ℂ) * z + A 1 1) := by
  rw [realPSLUpperHalfPlaneAutEquiv_mk]
  exact LiZhongQC.h36t_coe_smul A z

/-- The new Aut(H) realization agrees with the existing global sphere map. -/
theorem realSLUpperHalfPlaneAutHom_mobius_action (A : SL(2, ℝ)) (z : ℍ) :
    (Hyperbolic.realSLMobius A).val (z : ℂ) =
      ((((realSLUpperHalfPlaneAutHom A).val z : ℍ) : ℂ) : Mobius.ExtendedComplex) :=
  Hyperbolic.realSLMobius_action A z

end LowDimensionalTopology.Geometry.Surfaces
