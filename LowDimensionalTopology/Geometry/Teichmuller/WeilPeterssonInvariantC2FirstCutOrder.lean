module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonKernelSquareIntegrals

/-!
# The first-cut order of the actual second invariant product

The conjugated original second mixed term removes the first raw cut before
the second. Conjugating the existing ordered product after exchanging its
two coefficient roles proves precisely this order on the same inserted
fundamental-region cylinder. No spatial variable or singular limit is
interchanged, and the reversed third-term pairing is not used here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

private theorem second_conj_integral_product
    (cylinderMeasure : Measure (ℍ × ℍ)) (f g : ℍ × ℍ → ℂ) :
    conj (∫ q : ℍ × ℍ, f q * conj (g q) ∂cylinderMeasure) =
      ∫ q : ℍ × ℍ, g q * conj (f q) ∂cylinderMeasure := by
  rw [← integral_conj]
  apply integral_congr_ae
  exact Eventually.of_forall fun q => by
    simp only [map_mul, Complex.conj_conj, mul_comm]

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

/-- For the second pairing, the first raw exclusion is removed first.
Each fixed-second-cut limit and its completed outer limit occur on the
same given fundamental-region cylinder. This is the order supplied by
the conjugated original second mixed term. -/
theorem nativeWeilPetersson_second_invariant_first_cut_ordered_tendsto
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (u v w s : E) :
    let A : E → E → ℍ × ℍ → ℂ := fun a b q =>
      SourceKernel.bilinear (μ ν P F hF a) (μ ν P F hF b) q.1 q.2
    let cut : E → E → ℝ → ℍ × ℍ → ℂ := fun a b e q =>
      SourceKernel.invariantBilinear (μ ν P F hF a) (μ ν P F hF b) e q.1 q.2
    let cylinderMeasure := (flatArea.restrict F).prod flatArea
    (∀ (e t : ℝ), 0 < e → e < 1 / 16 → 0 < t → t < 1 / 16 →
      Integrable (fun q : ℍ × ℍ => cut u w t q * conj (cut v s e q)) cylinderMeasure) ∧
    (∀ e : ℝ, 0 < e → e < 1 / 16 →
      Integrable (fun q : ℍ × ℍ => A u w q * conj (cut v s e q)) cylinderMeasure ∧
      Tendsto (fun t : ℝ => ∫ q : ℍ × ℍ, cut u w t q * conj (cut v s e q) ∂cylinderMeasure)
        (𝓝[>] (0 : ℝ)) (𝓝 (∫ q : ℍ × ℍ, A u w q * conj (cut v s e q) ∂cylinderMeasure))) ∧
    Tendsto (fun e : ℝ => ∫ q : ℍ × ℍ, A u w q * conj (cut v s e q) ∂cylinderMeasure)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ q : ℍ × ℍ, A u w q * conj (A v s q) ∂cylinderMeasure)) ∧
    (Filter.limUnder (𝓝[>] (0 : ℝ)) fun e : ℝ =>
      Filter.limUnder (𝓝[>] (0 : ℝ)) fun t : ℝ =>
        ∫ q : ℍ × ℍ, cut u w t q * conj (cut v s e q) ∂cylinderMeasure) =
      ∫ q : ℍ × ℍ, A u w q * conj (A v s q) ∂cylinderMeasure := by
  let := C
  let A : E → E → ℍ × ℍ → ℂ := fun a b q =>
    SourceKernel.bilinear (μ ν P F hF a) (μ ν P F hF b) q.1 q.2
  let cut : E → E → ℝ → ℍ × ℍ → ℂ := fun a b e q =>
    SourceKernel.invariantBilinear (μ ν P F hF a) (μ ν P F hF b) e q.1 q.2
  let cylinderMeasure := (flatArea.restrict F).prod flatArea
  have h := nativeWeilPetersson_invariant_bilinear_product_ordered_tendsto
    R hp hg hgenus hΓ hfree hsmooth ν P F hF v u s w false
  have hfinite (e t : ℝ) (he : 0 < e) (he16 : e < 1 / 16)
      (ht : 0 < t) (ht16 : t < 1 / 16) :
      Integrable (fun q : ℍ × ℍ => cut u w t q * conj (cut v s e q)) cylinderMeasure := by
    have hi := Complex.conjCLE.toContinuousLinearMap.integrable_comp (h.1 e t he he16 ht ht16)
    apply hi.congr
    exact Eventually.of_forall fun q => by
      change conj (cut v s e q * conj (cut u w t q)) = cut u w t q * conj (cut v s e q)
      simp only [map_mul, Complex.conj_conj, mul_comm]
  have hinner (e : ℝ) (he : 0 < e) (he16 : e < 1 / 16) :
      Integrable (fun q : ℍ × ℍ => A u w q * conj (cut v s e q)) cylinderMeasure ∧
      Tendsto (fun t : ℝ => ∫ q : ℍ × ℍ, cut u w t q * conj (cut v s e q) ∂cylinderMeasure)
        (𝓝[>] (0 : ℝ)) (𝓝 (∫ q : ℍ × ℍ, A u w q * conj (cut v s e q) ∂cylinderMeasure)) := by
    have hi := h.2.1 e he he16
    have hlim := (Complex.continuous_conj.tendsto _).comp hi.2
    refine ⟨?_, ?_⟩
    · apply (Complex.conjCLE.toContinuousLinearMap.integrable_comp hi.1).congr
      exact Eventually.of_forall fun q => by
        change conj (cut v s e q * conj (A u w q)) = A u w q * conj (cut v s e q)
        simp only [map_mul, Complex.conj_conj, mul_comm]
    · simpa only [Function.comp_def, Bool.false_eq_true, ↓reduceIte, id_eq,
        second_conj_integral_product] using hlim
  have houter : Tendsto
      (fun e : ℝ => ∫ q : ℍ × ℍ, A u w q * conj (cut v s e q) ∂cylinderMeasure)
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ q : ℍ × ℍ, A u w q * conj (A v s q) ∂cylinderMeasure)) := by
    have hlim := (Complex.continuous_conj.tendsto _).comp h.2.2.1
    simpa only [Function.comp_def, Bool.false_eq_true, ↓reduceIte, id_eq,
      second_conj_integral_product] using hlim
  refine ⟨hfinite, hinner, houter, ?_⟩
  have heq : ∀ᶠ e in 𝓝[>] (0 : ℝ),
      (Filter.limUnder (𝓝[>] (0 : ℝ)) fun t : ℝ =>
        ∫ q : ℍ × ℍ, cut u w t q * conj (cut v s e q) ∂cylinderMeasure) =
      ∫ q : ℍ × ℍ, A u w q * conj (cut v s e q) ∂cylinderMeasure := by
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 16)] with e he
    exact (hinner e he.1 he.2).2.limUnder_eq
  exact (houter.congr' (Filter.Eventually.mono heq fun _ h => h.symm)).limUnder_eq

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
