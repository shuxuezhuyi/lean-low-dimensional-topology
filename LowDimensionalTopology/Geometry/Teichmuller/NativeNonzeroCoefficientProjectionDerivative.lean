module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeNonzeroBersDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientProjectionDerivative

/-!
# The actual nonzero coefficient projection and original tangent transport

The independently defined marked-surface coefficient projection retains its
proved Bers coordinate formula. Its genuine nonzero Banach derivative and
the actual canonical chart inverse prove manifold differentiability at the
original coefficient. The actual Bers tangent frame identifies its manifold
derivative with that genuine weighted derivative. The actual coordinate
translation derivative therefore transports original tangent vectors by the
literal deformed Bers integral after the normalized coefficient derivative.

The handle presentation is the already proved canonical one. Quantitative
quasiconformal smoothing occurs only as the existing explicit premise for
the canonical atlas on the independently realized quotient topology.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces NormalizedCoefficientTransport

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : UpperHalfPlane → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

local notation "B" => GammaMeasurableBeltrami.Space Γ
local notation "E" => Fin (3 * g - 3) → ℂ

/-- On its coefficient ball the actual projection is the original independently defined quotient value. -/
theorem coefficientProjection_ball (ν : GammaMeasurableBeltrami.Ball Γ) :
    coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val =
      coefficientProjectionBall R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν := by
  simp only [coefficientProjection,
    dite_eq_left (GammaMeasurableBeltrami.Ball.norm_lt_one ν)]

/-- The original marked-surface projection has the actual nonzero derivative in its Bers coordinates. -/
theorem hasFDerivAt_coefficientProjection_coordinates_nonzero
    (ν : GammaMeasurableBeltrami.Ball Γ) :
    HasFDerivAt
      (fun μ : B => bersCoordinates R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp μ))
      ((weightedLinearBersCoordinates R hg hgenus
          (canonicalHandleGroupPresentation g) hΓ hp).toContinuousLinearMap.comp
        (nonzeroBersDerivative R hp hg hgenus hΓ ν)) ν.val := by
  let e := (weightedLinearBersCoordinates R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hp).toContinuousLinearMap
  have hd := e.hasFDerivAt.comp ν.val
    (hasFDerivAt_automorphicProjection_nonzero R hp hg hgenus hΓ ν)
  apply hd.congr_of_eventuallyEq
  exact Eventually.of_forall fun μ => coefficientProjection_coordinates R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp μ

variable (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{u})

/-- Every actual canonical chart recovers the independently defined original projection. -/
theorem coefficientProjection_eq_chartSymm_at (a : TeichmullerSpace.{u, u} R) (μ : B) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp μ =
      (chartAt E a).symm (bersCoordinates R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp μ)) := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  change coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp μ =
    (chartAt E a).symm ((chartAt E a)
      (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp μ))
  apply Eq.symm
  apply (chartAt E a).left_inv
  change coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp μ ∈
    (univ : Set _)
  trivial

/-- Manifold differentiability is for the original coefficient projection and quotient topology. -/
theorem mdifferentiableAt_coefficientProjection_nonzero
    (ν : GammaMeasurableBeltrami.Ball Γ) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    MDifferentiableAt 𝓘(ℂ, B) 𝓘(ℂ, E)
      (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp) ν.val := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  let : IsManifold 𝓘(ℂ, E) ω (TeichmullerSpace.{u, u} R) :=
    canonicalComplex_isManifold R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
  let a := coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val
  have hf := (hasFDerivAt_coefficientProjection_coordinates_nonzero R hg hgenus
    hΓ hfree hp ν).differentiableAt.mdifferentiableAt
  have hc := (mdifferentiable_chart (I := 𝓘(ℂ, E)) a).symm.mdifferentiableAt
    ((chartAt E a).map_source (mem_chart_source E a))
  have hvalue : bersCoordinates R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp
      (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val) =
        (chartAt E a) a := rfl
  have hcomp := hc.comp_of_eq ν.val hf hvalue
  apply hcomp.congr_of_eventuallyEq
  exact Eventually.of_forall fun μ => coefficientProjection_eq_chartSymm_at R hg hgenus
    hΓ hfree hp hsmooth a μ

/-- The genuine chart tangent derivative is precisely the genuine original weighted nonzero derivative. -/
theorem canonicalBersTangentEquiv_mfderiv_coefficientProjection_nonzero
    (ν : GammaMeasurableBeltrami.Ball Γ) (μ : B) :
    letI := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
      hΓ hfree hp hsmooth
    canonicalBersTangentEquiv R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
      (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val)
      (mfderiv 𝓘(ℂ, B) 𝓘(ℂ, E)
        (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp) ν.val μ) =
      nonzeroBersDerivative R hp hg hgenus hΓ ν μ := by
  let := canonicalComplexChartedSpace R hg hgenus (canonicalHandleGroupPresentation g)
    hΓ hfree hp hsmooth
  let : IsManifold 𝓘(ℂ, E) ω (TeichmullerSpace.{u, u} R) :=
    canonicalComplex_isManifold R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
  let a := coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp ν.val
  have hpj := mdifferentiableAt_coefficientProjection_nonzero R hg hgenus hΓ hfree hp hsmooth ν
  have hchart : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) (chartAt E a) a :=
    (mdifferentiable_chart (I := 𝓘(ℂ, E)) a).mdifferentiableAt (mem_chart_source E a)
  have hchain := mfderiv_comp_apply ν.val hchart hpj μ
  have hd := (hasFDerivAt_coefficientProjection_coordinates_nonzero R hg hgenus
    hΓ hfree hp ν).hasMFDerivAt
  change mfderiv 𝓘(ℂ, B) 𝓘(ℂ, E)
    (fun κ => bersCoordinates R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp
      (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp κ))
      ν.val μ = _ at hchain
  rw [hd.mfderiv] at hchain
  have hframe := canonicalBersTangentEquiv_coordinate_apply R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth a
    (mfderiv 𝓘(ℂ, B) 𝓘(ℂ, E)
      (coefficientProjection R hg hgenus (canonicalHandleGroupPresentation g) hΓ hfree hp) ν.val μ)
  apply (weightedLinearBersCoordinates R hg hgenus (canonicalHandleGroupPresentation g) hΓ hp).injective
  exact hframe.trans hchain.symm

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
