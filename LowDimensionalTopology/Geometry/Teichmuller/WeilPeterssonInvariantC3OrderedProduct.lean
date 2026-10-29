module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonKernelSquareIntegrals

/-!
# The ordered product with the original first-region third-term slots

The existing ordered product applies with the upper coefficient roles
exchanged. The second cut tends to zero at each fixed positive first cut,
then the first cut tends to zero on the same given region cylinder.
This is a product statement, not an identification of original radial limits.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3 * g - 3) → ℂ
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth

/-- The native product with the third first-region coefficient order has
genuine finite and intermediate integrability and the original ordered
two-cut limit. Its upper pairing has roles w,u and its lower pairing v,s. -/
theorem nativeWeilPetersson_third_first_region_invariant_ordered_tendsto
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (u v w s : E) :
    let A : E → E → ℍ × ℍ → ℂ := fun a b q =>
      SourceKernel.bilinear (μ ν P F hF a) (μ ν P F hF b) q.1 q.2
    let cut : E → E → ℝ → ℍ × ℍ → ℂ := fun a b e q =>
      SourceKernel.invariantBilinear (μ ν P F hF a) (μ ν P F hF b) e q.1 q.2
    let cylinderMeasure := (flatArea.restrict F).prod flatArea
    (∀ (e t : ℝ), 0 < e → e < 1 / 16 → 0 < t → t < 1 / 16 →
      Integrable (fun q : ℍ × ℍ => cut w u e q * conj (cut v s t q)) cylinderMeasure) ∧
    (∀ e : ℝ, 0 < e → e < 1 / 16 →
      Integrable (fun q : ℍ × ℍ => cut w u e q * conj (A v s q)) cylinderMeasure ∧
      Tendsto (fun t : ℝ => ∫ q : ℍ × ℍ, cut w u e q * conj (cut v s t q) ∂cylinderMeasure)
        (𝓝[>] (0 : ℝ)) (𝓝 (∫ q : ℍ × ℍ, cut w u e q * conj (A v s q) ∂cylinderMeasure))) ∧
    Tendsto (fun e : ℝ => ∫ q : ℍ × ℍ, cut w u e q * conj (A v s q) ∂cylinderMeasure)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ q : ℍ × ℍ, A w u q * conj (A v s q) ∂cylinderMeasure)) ∧
    (Filter.limUnder (𝓝[>] (0 : ℝ)) fun e : ℝ =>
      Filter.limUnder (𝓝[>] (0 : ℝ)) fun t : ℝ =>
        ∫ q : ℍ × ℍ, cut w u e q * conj (cut v s t q) ∂cylinderMeasure) =
      ∫ q : ℍ × ℍ, A w u q * conj (A v s q) ∂cylinderMeasure := by
  let := C
  have h := nativeWeilPetersson_invariant_bilinear_product_ordered_tendsto
    R hp hg hgenus hΓ hfree hsmooth ν P F hF w v u s false
  simpa only [Bool.false_eq_true, ↓reduceIte, id_eq] using h

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
