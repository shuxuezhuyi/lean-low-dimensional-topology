module

public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalFrickeGenerators
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ParabolicEllipticNormalForms

/-!
# Nonzero coefficients of given normalized canonical generators

The actual final generator's fixed points at zero and infinity force its real
matrix representative to be diagonal. The existing canonical-presentation and
compact-cover theorem then gives nonzero off-diagonal coefficients for every
other actual generator. The ordered marking is a genuine equivalence with the
deck group of the same original surface covering; no SL lift of that group is
assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Surfaces

open Teichmuller Hyperbolic

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] {R : RiemannSurface X}

/-- In a given normalized canonically marked model of the original compact
surface, every actual generator other than the final b-generator has `b*c ≠ 0`.
Only the fixed-point consequences of the book normalization are needed. -/
theorem HyperbolicSurfaceModel.markedDeck_matrices_bc_ne_zero_of_final_fixed_zero_infty
    (M : HyperbolicSurfaceModel R) {g : ℕ} (hg : 1 < g)
    (ρ : LiZhongQC.surfaceGroup g ≃* deck M.halfPlaneCover)
    (A : (Fin g ⊕ Fin g) → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : ∀ s (z : ℍ), A s • z = ρ (PresentedGroup.of s) • z)
    (hD0 : (realSLMobius (A (Sum.inr (finalHandle hg)))).val (0 : ℂ) = (0 : ℂ))
    (hDinf : (realSLMobius (A (Sum.inr (finalHandle hg)))).val ∞ = ∞)
    (s : Fin g ⊕ Fin g)
    (hs : realSLMobius (A s) ≠ realSLMobius (A (Sum.inr (finalHandle hg)))) :
    A s 0 1 * A s 1 0 ≠ 0 := by
  let D := A (Sum.inr (finalHandle hg))
  have hD10 : D 1 0 = 0 := (realSLMobius_fixed_infty_iff D).mp hDinf
  have hpoly := (Mobius.Classification.fractionalLinear_fixed_coe_iff
    (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map Complex.ofRealHom D)) 0).mp
      (show Mobius.fractionalLinear _ ((0 : ℂ) : Mobius.ExtendedComplex) = (0 : ℂ) by
        simpa only [realSLMobius, MonoidHom.comp_apply,
          Mobius.invariantDisc_specialLinear_action] using hD0)
  have hD01 : D 0 1 = 0 := by
    change (D 1 0 : ℂ) * (0 * 0) + ((D 1 1 : ℂ) - (D 0 0 : ℂ)) * 0 +
      -(D 0 1 : ℂ) = 0 at hpoly
    have hb : (D 0 1 : ℂ) = 0 := by simpa using hpoly
    exact Complex.ofReal_eq_zero.mp hb
  have hs' : s ≠ Sum.inr (finalHandle hg) := by
    intro h
    exact hs (congrArg (fun t : Fin g ⊕ Fin g => realSLMobius (A t)) h)
  obtain ⟨hb, hc⟩ := M.markedDeck_matrices_offDiagonal_ne_zero hg ρ A hA
    hD01 hD10 s hs'
  exact mul_ne_zero hb hc

end LowDimensionalTopology.Geometry.Surfaces
