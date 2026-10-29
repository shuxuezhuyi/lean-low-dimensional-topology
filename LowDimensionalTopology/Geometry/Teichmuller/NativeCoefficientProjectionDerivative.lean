module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientProjection
public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalPeterssonDuality
public import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

/-!
# The actual coefficient projection has the original Bers tangent derivative

The coefficient projection is the actual normalized group-coefficient quotient
map to marked surfaces. Its already proved exact coordinate formula, the
uniform weighted Fréchet estimate, and the actual chart inverse show that this
map is manifold differentiable at zero. The chain rule identifies its genuine
manifold derivative with the original Bers derivative and canonical tangent
quotient. The original identity-marked base point is used throughout.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hPresentation : Unproved.HandleGroupPresentation g)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : UpperHalfPlane → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

local notation "B" => GammaMeasurableBeltrami.Space Γ
local notation "E" => Fin (3 * g - 3) → ℂ

/-- The actual marked-surface projection, written in its actual Bers chart,
has the derivative obtained from the proved weighted Banach derivative. -/
theorem hasFDerivAt_coefficientProjection_coordinates :
    HasFDerivAt
      (fun μ : B => bersCoordinates R hg hgenus hPresentation hΓ hfree hp
        (coefficientProjection R hg hgenus hPresentation hΓ hfree hp μ))
      ((weightedLinearBersCoordinates R hg hgenus hPresentation hΓ hp).toContinuousLinearMap.comp
        (BersWeighted.automorphicIntegralOperator hΓ)) 0 := by
  let e := (weightedLinearBersCoordinates R hg hgenus hPresentation hΓ hp).toContinuousLinearMap
  have hd := e.hasFDerivAt.comp 0 (BersWeighted.hasFDerivAt_automorphicProjection hΓ)
  apply hd.congr_of_eventuallyEq
  exact Eventually.of_forall fun μ =>
    coefficientProjection_coordinates R hg hgenus hPresentation hΓ hfree hp μ

variable (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})

/-- Inverting the actual chart recovers the independently defined quotient
projection. This is a proved identity of maps, not its definition. -/
theorem coefficientProjection_eq_chartSymm (μ : B) :
    letI := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
    coefficientProjection R hg hgenus hPresentation hΓ hfree hp μ =
      (chartAt E (basePoint R)).symm
        (bersCoordinates R hg hgenus hPresentation hΓ hfree hp
          (coefficientProjection R hg hgenus hPresentation hΓ hfree hp μ)) := by
  let := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
  change coefficientProjection R hg hgenus hPresentation hΓ hfree hp μ =
    (chartAt E (basePoint R)).symm
      ((chartAt E (basePoint R))
        (coefficientProjection R hg hgenus hPresentation hΓ hfree hp μ))
  apply Eq.symm
  apply (chartAt E (basePoint R)).left_inv
  change coefficientProjection R hg hgenus hPresentation hΓ hfree hp μ ∈ (univ : Set _)
  trivial

/-- The actual compatible-coefficient projection is manifold differentiable
at the zero coefficient for the original canonical quotient topology. -/
theorem mdifferentiableAt_coefficientProjection_zero :
    letI := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
    MDifferentiableAt 𝓘(ℂ, B) 𝓘(ℂ, E)
      (coefficientProjection R hg hgenus hPresentation hΓ hfree hp) 0 := by
  let := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
  let : IsManifold 𝓘(ℂ, E) ω (TeichmullerSpace.{u, u} R) :=
    canonicalComplex_isManifold R hg hgenus hPresentation hΓ hfree hp hsmooth
  have hf := (hasFDerivAt_coefficientProjection_coordinates R hg hgenus hPresentation
    hΓ hfree hp).differentiableAt.mdifferentiableAt
  have hc := (mdifferentiable_chart (I := 𝓘(ℂ, E)) (basePoint R)).symm.mdifferentiableAt
    ((chartAt E (basePoint R)).map_source (mem_chart_source E (basePoint R)))
  have hzero : bersCoordinates R hg hgenus hPresentation hΓ hfree hp
      (coefficientProjection R hg hgenus hPresentation hΓ hfree hp (0 : B)) =
      (chartAt E (basePoint R)) (basePoint R) := by
    rw [coefficientProjection_zero]; rfl
  have hcomp := hc.comp_of_eq 0 hf hzero
  apply hcomp.congr_of_eventuallyEq
  exact Eventually.of_forall fun μ =>
    coefficientProjection_eq_chartSymm R hg hgenus hPresentation hΓ hfree hp hsmooth μ

/-- The genuine manifold derivative, in the genuine Bers tangent frame, is
exactly the original bounded Bers integral operator. -/
theorem canonicalBaseTangentEquiv_mfderiv_coefficientProjection (μ : B) :
    letI := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
    canonicalBaseTangentEquiv R hg hgenus hPresentation hΓ hfree hp hsmooth
      (mfderiv 𝓘(ℂ, B) 𝓘(ℂ, E)
        (coefficientProjection R hg hgenus hPresentation hΓ hfree hp) 0 μ) =
      BersWeighted.automorphicIntegralOperator hΓ μ := by
  let := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
  let : IsManifold 𝓘(ℂ, E) ω (TeichmullerSpace.{u, u} R) :=
    canonicalComplex_isManifold R hg hgenus hPresentation hΓ hfree hp hsmooth
  have hpj := mdifferentiableAt_coefficientProjection_zero R hg hgenus hPresentation
    hΓ hfree hp hsmooth
  have hchart : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E)
      (chartAt E (basePoint R))
      (coefficientProjection R hg hgenus hPresentation hΓ hfree hp (0 : B)) := by
    rw [coefficientProjection_zero]
    exact (mdifferentiable_chart (I := 𝓘(ℂ, E)) (basePoint R)).mdifferentiableAt
      (mem_chart_source E (basePoint R))
  have hchain := mfderiv_comp_apply 0 hchart hpj μ
  have hd := (hasFDerivAt_coefficientProjection_coordinates R hg hgenus hPresentation
    hΓ hfree hp).hasMFDerivAt
  change mfderiv 𝓘(ℂ, B) 𝓘(ℂ, E)
      (fun ν => bersCoordinates R hg hgenus hPresentation hΓ hfree hp
        (coefficientProjection R hg hgenus hPresentation hΓ hfree hp ν)) 0 μ = _ at hchain
  rw [hd.mfderiv, coefficientProjection_zero] at hchain
  have hframe := canonicalBersTangentEquiv_coordinate_apply R hg hgenus hPresentation
    hΓ hfree hp hsmooth (basePoint R)
    (mfderiv 𝓘(ℂ, B) 𝓘(ℂ, E)
      (coefficientProjection R hg hgenus hPresentation hΓ hfree hp) 0 μ)
  apply (weightedLinearBersCoordinates R hg hgenus hPresentation hΓ hp).injective
  exact hframe.trans hchain.symm

/-- The canonical quotient tangent vector is the actual derivative of the
actual marked-surface coefficient projection at the original identity point. -/
theorem mfderiv_coefficientProjection_eq_quotient (μ : B) :
    letI := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
    mfderiv 𝓘(ℂ, B) 𝓘(ℂ, E)
        (coefficientProjection R hg hgenus hPresentation hΓ hfree hp) 0 μ =
      canonicalDerivativeQuotientTangentEquiv R hg hgenus hPresentation hΓ hfree hp hsmooth
        (Submodule.Quotient.mk μ) := by
  let := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
  apply (canonicalBaseTangentEquiv R hg hgenus hPresentation hΓ hfree hp hsmooth).injective
  rw [canonicalBaseTangentEquiv_mfderiv_coefficientProjection]
  change BersWeighted.automorphicIntegralOperator hΓ μ =
    (canonicalBaseTangentEquiv R hg hgenus hPresentation hΓ hfree hp hsmooth)
      ((canonicalBaseTangentEquiv R hg hgenus hPresentation hΓ hfree hp hsmooth).symm
        (BersWeighted.derivativeQuotientEquiv R p hp hΓ (Submodule.Quotient.mk μ)))
  rw [ContinuousLinearEquiv.apply_symm_apply, BersWeighted.derivativeQuotientEquiv_apply_mk]

/-- The canonical tangent-dual isomorphism evaluates on the actual projection
derivative by the literal original fundamental-region integral. -/
theorem canonicalBasePeterssonDuality_mfderiv_coefficientProjection
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (μ : B) (q : NativePetersson.Space R P p hp F hF) :
    letI := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
    canonicalBasePeterssonDuality R hg hgenus hPresentation hΓ hfree hp hsmooth P F hF
      (mfderiv 𝓘(ℂ, B) 𝓘(ℂ, E)
        (coefficientProjection R hg hgenus hPresentation hΓ hfree hp) 0 μ) q =
      ∫ z in UpperHalfPlane.coe '' F,
        GammaMeasurableBeltrami.planeRepresentative μ.val z *
          QuadraticBergman.uniformizedQuadratic R p
            (NativePetersson.toQuadratic R P p hp F hF q) z := by
  let := canonicalComplexChartedSpace R hg hgenus hPresentation hΓ hfree hp hsmooth
  rw [mfderiv_coefficientProjection_eq_quotient]
  exact canonicalBasePeterssonDuality_apply_quotient R hg hgenus hPresentation hΓ hfree hp
    hsmooth P F hF μ q

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
