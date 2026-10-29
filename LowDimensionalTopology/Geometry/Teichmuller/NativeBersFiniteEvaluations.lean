module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeInverseBersGerm
public import LowDimensionalTopology.Geometry.Teichmuller.BersWeightedCoordinates
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.FDeriv.Prod

/-!
# Genuine finite-dimensional holomorphy from actual Bers point evaluations

Evaluation is on the faithful lower-half-plane function, with its canonical
zero extension. These complex-linear forms separate the full native
weighted automorphic space. In finite dimension they span its entire dual,
so scalar holomorphy at each actual point implies vector differentiability
in the unchanged weighted norm.

The concrete consumer applies this argument to the independently defined
normalized inverse Bers germ and its proved Ahlfors-Bers scalar families.
The final closed-surface consumer obtains finite dimension from the actual
existing weighted coordinate equivalence and the proved handle presentation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- Actual lower-half-plane point evaluation, as a complex-linear form. -/
def lowerEvaluationLinear (z : Lower) : Automorphic Γ →ₗ[ℂ] ℂ :=
  ((LinearMap.proj (z : ℂ)).comp decodeLinearMap).comp (automorphicSubmodule Γ).subtype

@[simp] theorem lowerEvaluationLinear_apply (z : Lower) (φ : Automorphic Γ) :
    lowerEvaluationLinear z φ = (φ.toSource : ℂ → ℂ) z := rfl

/-- Every value is retained; no almost-everywhere function quotient is evaluated. -/
theorem lowerEvaluationLinear_separates {φ ψ : Automorphic Γ}
    (h : ∀ z : Lower, lowerEvaluationLinear z φ = lowerEvaluationLinear z ψ) : φ = ψ := by
  apply Subtype.ext
  apply decode_injective
  funext z
  by_cases hz : z ∈ LiZhongQC.lowerHalf
  · simpa only [lowerEvaluationLinear_apply, Automorphic.toSource_apply] using h ⟨z, hz⟩
  · rw [decode_off φ.val hz, decode_off ψ.val hz]

/-- The actual point evaluations have zero common kernel on the full native space. -/
theorem iInf_ker_lowerEvaluationLinear_eq_bot :
    (⨅ z : Lower, LinearMap.ker (lowerEvaluationLinear (Γ := Γ) z)) = ⊥ := by
  apply le_antisymm ?_ bot_le
  intro φ hφ
  have hzero : φ = 0 := by
    apply lowerEvaluationLinear_separates
    intro z
    have hz : lowerEvaluationLinear z φ = 0 := (Submodule.mem_iInf _).mp hφ z
    simpa only [map_zero] using hz
  simpa only [Submodule.mem_bot] using hzero

/-- Every coordinate functional is a finite linear combination of actual point evaluations. -/
theorem linearFunctional_mem_span_lowerEvaluations [FiniteDimensional ℂ (Automorphic Γ)]
    (K : Automorphic Γ →ₗ[ℂ] ℂ) :
    K ∈ Submodule.span ℂ (range (lowerEvaluationLinear (Γ := Γ))) := by
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  rw [iInf_ker_lowerEvaluationLinear_eq_bot]
  exact bot_le

/-- Scalar holomorphy at every actual point gives it for every linear coordinate. -/
theorem differentiableOn_linearFunctional_of_lowerEvaluations
    [FiniteDimensional ℂ (Automorphic Γ)] {P : Set ℂ} (F : ℂ → Automorphic Γ)
    (hF : ∀ z : Lower, DifferentiableOn ℂ (fun t => lowerEvaluationLinear z (F t)) P)
    (K : Automorphic Γ →ₗ[ℂ] ℂ) :
    DifferentiableOn ℂ (fun t => K (F t)) P := by
  have hK := linearFunctional_mem_span_lowerEvaluations K
  induction hK using Submodule.span_induction with
  | mem L hL =>
    obtain ⟨z, rfl⟩ := hL
    exact hF z
  | zero =>
    simpa only [LinearMap.zero_apply] using
      (differentiableOn_const (𝕜 := ℂ) (s := P) (c := (0 : ℂ)))
  | add _ _ _ _ h₁ h₂ =>
    apply (h₁.add h₂).congr
    intro t _
    simp only [LinearMap.add_apply, Pi.add_apply]
  | smul c _ _ hL =>
    apply (hL.const_smul c).congr
    intro t _
    simp only [LinearMap.smul_apply, Pi.smul_apply]

/-- The upgrade is in the actual weighted norm, through its finite-basis continuous equivalence. -/
theorem differentiableOn_of_lowerEvaluations [FiniteDimensional ℂ (Automorphic Γ)]
    {P : Set ℂ} (F : ℂ → Automorphic Γ)
    (hF : ∀ z : Lower, DifferentiableOn ℂ (fun t => lowerEvaluationLinear z (F t)) P) :
    DifferentiableOn ℂ F P := by
  let e := (Module.finBasis ℂ (Automorphic Γ)).equivFunL
  have hcoords : DifferentiableOn ℂ (e ∘ F) P := by
    apply differentiableOn_pi.mpr
    intro i
    have hi := differentiableOn_linearFunctional_of_lowerEvaluations F hF
      ((LinearMap.proj i).comp e.toContinuousLinearMap.toLinearMap)
    apply hi.congr
    intro t _
    simp only [LinearMap.comp_apply, LinearMap.proj_apply, Function.comp_apply,
      ContinuousLinearMap.coe_coe, ContinuousLinearEquiv.coe_coe]
  exact e.comp_differentiableOn_iff.mp hcoords

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Surfaces

variable {Γ : Subgroup Deck}

/-- The actual scalar Ahlfors-Bers family is genuinely vector differentiable along every curve. -/
theorem inverseBersGerm_curve_differentiableOn
    [FiniteDimensional ℂ (BersWeighted.Automorphic Γ)]
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    {P : Set ℂ} (hP : IsOpen P)
    (q : ℂ → BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hq : DifferentiableOn ℂ q P) (hbound : ∀ t ∈ P, ‖q t‖ < inverseSectionRadius ν) :
    DifferentiableOn ℂ (fun t => inverseBersGerm hΓ ν (q t)) P := by
  apply BersWeighted.differentiableOn_of_lowerEvaluations
  intro z
  simpa only [BersWeighted.lowerEvaluationLinear_apply] using
    inverseBersGerm_scalar_differentiableOn hΓ ν hP q hq hbound z.property

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)

include R hp hg hgenus in
/-- Actual closed uniformization proves finite dimension; no extra finite-dimensional premise remains. -/
theorem inverseBersGerm_curve_differentiableOn_of_uniformization
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    {P : Set ℂ} (hP : IsOpen P)
    (q : ℂ → BersWeighted.Automorphic (deformedGroup hΓ ν))
    (hq : DifferentiableOn ℂ q P) (hbound : ∀ t ∈ P, ‖q t‖ < inverseSectionRadius ν) :
    DifferentiableOn ℂ (fun t => inverseBersGerm hΓ ν (q t)) P := by
  let e := TeichmullerSpace.weightedLinearBersEquiv R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hp
  let : FiniteDimensional ℂ (BersWeighted.Automorphic Γ) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  exact inverseBersGerm_curve_differentiableOn hΓ ν hP q hq hbound

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
