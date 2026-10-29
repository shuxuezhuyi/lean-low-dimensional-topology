module

public import LowDimensionalTopology.Geometry.Teichmuller.BersIntegralSurjectivity
public import LowDimensionalTopology.Geometry.Teichmuller.BersAutomorphicCompleteness
public import LowDimensionalTopology.Geometry.Teichmuller.BersPeterssonDuality

/-!
# The true Bers derivative quotient in its exact original automorphic norm

Surjectivity is supplied by the literal harmonic preimages and reproducing
integral. The resulting continuous-linear equivalence retains the original
L-infinity quotient norm and the original lower-half-plane weighted norm.
Composition with the actual Petersson pairing yields the automorphic model's
canonical map to the continuous quadratic dual.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

open Surfaces NativePetersson

variable {Γ : Subgroup GammaMeasurableBeltrami.Deck}

/-- Restriction to the proved automorphic image preserves the entire kernel. -/
theorem automorphicIntegralOperator_ker (hΓ : LiZhongQC.IsFuchsian Γ) :
    (automorphicIntegralOperator hΓ).ker = infinitesimalSubmodule Γ := by
  ext μ
  change automorphicIntegralOperator hΓ μ = 0 ↔ integralOperator Γ μ = 0
  constructor
  · exact fun h => congrArg Subtype.val h
  · exact fun h => Subtype.ext h

/-- The original bounded Bers derivative descends through its actual closed kernel. -/
def quotientIntegralOperator (hΓ : LiZhongQC.IsFuchsian Γ) :
    TangentQuotient Γ →L[ℂ] Automorphic Γ :=
  (infinitesimalSubmodule Γ).liftQL (automorphicIntegralOperator hΓ)
    (automorphicIntegralOperator_ker hΓ).symm.le

theorem quotientIntegralOperator_ker (hΓ : LiZhongQC.IsFuchsian Γ) :
    (quotientIntegralOperator hΓ).ker = ⊥ := by
  exact Submodule.ker_liftQ_eq_bot (infinitesimalSubmodule Γ)
    (automorphicIntegralOperator hΓ).toLinearMap
    (automorphicIntegralOperator_ker hΓ).symm.le
    (automorphicIntegralOperator_ker hΓ).le

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X) (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

include R p hp in
/-- Every exact bounded automorphic vector has an actual derivative-quotient preimage. -/
theorem quotientIntegralOperator_surjective (hΓ : LiZhongQC.IsFuchsian Γ) :
    Function.Surjective (quotientIntegralOperator hΓ) := by
  intro φ
  obtain ⟨μ, hμ⟩ := automorphicIntegralOperator_surjective R p hp hΓ φ
  exact ⟨Submodule.Quotient.mk μ, hμ⟩

/-- The canonical quotient isomorphism is induced by the actual derivative,
with both original norms and continuous inverse proved by the Banach theorem. -/
def derivativeQuotientEquiv (hΓ : LiZhongQC.IsFuchsian Γ) :
    TangentQuotient Γ ≃L[ℂ] Automorphic Γ := by
  letI : CompleteSpace (Automorphic Γ) := automorphic_completeSpace Γ
  exact ContinuousLinearEquiv.ofBijective (quotientIntegralOperator hΓ)
    (quotientIntegralOperator_ker hΓ)
    (LinearMap.range_eq_top.mpr (quotientIntegralOperator_surjective R p hp hΓ))

/-- Every quotient class is sent by its unchanged Bers derivative. -/
theorem derivativeQuotientEquiv_apply_mk (hΓ : LiZhongQC.IsFuchsian Γ)
    (μ : GammaMeasurableBeltrami.Space Γ) :
    derivativeQuotientEquiv R p hp hΓ (Submodule.Quotient.mk μ) =
      automorphicIntegralOperator hΓ μ := rfl

/-- At the base point this is precisely the already proved actual Fréchet derivative. -/
theorem derivativeQuotientEquiv_apply_mk_fderiv (hΓ : LiZhongQC.IsFuchsian Γ)
    (μ : GammaMeasurableBeltrami.Space Γ) :
    derivativeQuotientEquiv R p hp hΓ (Submodule.Quotient.mk μ) =
      fderiv ℂ (automorphicProjection hΓ) 0 μ := by
  rw [fderiv_automorphicProjection hΓ]
  exact derivativeQuotientEquiv_apply_mk R p hp hΓ μ

/-- The actual automorphic tangent model is canonically the continuous dual of
the full native quadratic space, with its exact full Petersson norm. -/
def automorphicPeterssonDuality
    (hΓ : LiZhongQC.IsFuchsian Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) :
    Automorphic Γ ≃L[ℂ] StrongDual ℂ (NativePetersson.Space R P p hp F hF) :=
  (derivativeQuotientEquiv R p hp hΓ).symm.trans
    (NativePetersson.dualityEquiv R P p hp F hF)

/-- The composed isomorphism is still the literal original pairing on every
actual derivative image; surjectivity proves this specifies every input. -/
theorem automorphicPeterssonDuality_apply_derivative
    (hΓ : LiZhongQC.IsFuchsian Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (μ : GammaMeasurableBeltrami.Space Γ)
    (q : NativePetersson.Space R P p hp F hF) :
    automorphicPeterssonDuality R p hp hΓ P F hF (automorphicIntegralOperator hΓ μ) q =
      ∫ z in UpperHalfPlane.coe '' F,
        GammaMeasurableBeltrami.planeRepresentative μ.val z *
          QuadraticBergman.uniformizedQuadratic R p
            (NativePetersson.toQuadratic R P p hp F hF q) z := by
  have he := (derivativeQuotientEquiv R p hp hΓ).symm_apply_apply
    (Submodule.Quotient.mk μ)
  rw [derivativeQuotientEquiv_apply_mk] at he
  change NativePetersson.dualityEquiv R P p hp F hF
    ((derivativeQuotientEquiv R p hp hΓ).symm (automorphicIntegralOperator hΓ μ)) q = _
  rw [he]
  exact NativePetersson.dualityEquiv_apply_mk R P p hp F hF μ q

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
