module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalWPCartanCoordinateRegularity
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalWeilPeterssonFormCartan
public import LowDimensionalTopology.Geometry.Teichmuller.NativeRealTangentTrivialization
public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# The field-defined original WP Lie form

The whole smooth Cartan expression is transported into the actual alternating
tangent bundle. The explicit Cartan identity identifies it with the actual
pullback-time derivative along every given family of the same native field.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "T" => TeichmullerSpace R
local notation "E" => Fin (3*g-3) → ℂ
local notation "RI" => 𝓘(ℝ, E)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "c" => nativeWeilPeterssonCoordinateChart
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "D" => nativeWeilPeterssonRealTangentCoordinateEquiv
  R hp hg hgenus hΓ hfree hsmooth
local notation "Ω" => nativeWeilPeterssonFundamentalRealCoordinateForm
  R hp hg hgenus hΓ hfree hsmooth (basePoint R)
local notation "realManifold" => Topology.IsOpenEmbedding.isManifold_singleton
  (I := RI) (n := ω)
  (canonicalBersCoordinates_isOpenEmbedding R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth)

/-- The whole Cartan coordinate expression for the same original WP form. -/
def nativeWPCartanCoordinateRHS :
    letI := C
    letI : IsManifold RI ω T := realManifold
    FormInterior.SmoothVectorField RI (M := T) → E → E [⋀^Fin 2]→L[ℝ] ℝ := by
  let := C
  let : IsManifold RI ω T := realManifold
  intro W z
  let ξ : E → E := fun y => D ((c).symm y) (W ((c).symm y))
  exact extDerivWithin (fun y => (Ω y).curryLeft (ξ y)) (c).target z +
    (extDerivWithin Ω (c).target z).curryLeft (ξ z)

local notation "RHS" => nativeWPCartanCoordinateRHS R hp hg hgenus hΓ hfree hsmooth

/-- Pull the whole coordinate expression back to the same native tangent fibre. -/
def nativeWPCartanLieFormValue :
    letI := C
    letI : IsManifold RI ω T := realManifold
    FormInterior.SmoothVectorField RI (M := T) →
      ∀ q : T, TangentSpace RI q [⋀^Fin 2]→L[ℝ] ℝ := by
  let := C
  let : IsManifold RI ω T := realManifold
  intro W q
  exact (RHS W (c q)).compContinuousLinearMap (D q).toContinuousLinearMap

local notation "Value" => nativeWPCartanLieFormValue R hp hg hgenus hΓ hfree hsmooth

/-- The actual tangent trivialization reads exactly the original Cartan expression. -/
theorem nativeWPCartanLieFormValue_coordinates :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (W : FormInterior.SmoothVectorField RI (M := T)) (a q : T),
      (Value W q).compContinuousLinearMap
        ((trivializationAt E (TangentSpace RI) a).symmL ℝ q) = RHS W (c q) := by
  let := C
  let : IsManifold RI ω T := realManifold
  intro W a q
  rw [nativeWeilPeterssonRealTangentCoordinateEquiv_symmL
    R hp hg hgenus hΓ hfree hsmooth a q]
  apply ContinuousAlternatingMap.ext
  intro v
  change RHS W (c q) (fun i => D q ((D q).symm (v i))) = RHS W (c q) v
  congr 1
  funext i
  exact (D q).apply_symm_apply (v i)

/-- The field-only Cartan value is an actual smooth alternating tangent section. -/
theorem contMDiff_nativeWPCartanLieFormValue
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ W : FormInterior.SmoothVectorField RI (M := T),
      ContMDiff RI (ModelWithCorners.prod RI 𝓘(ℝ, E [⋀^Fin 2]→L[ℝ] ℝ)) ∞
        (fun q => TotalSpace.mk' (E [⋀^Fin 2]→L[ℝ] ℝ) q (Value W q)) := by
  let := C
  let : IsManifold RI ω T := realManifold
  intro W a
  apply (Bundle.contMDiffAt_section a).mpr
  simp only [FormInterior.form_trivialization]
  have hRHS : ContDiffOn ℝ ∞ (RHS W) (c).target :=
    nativeWP_cartanCoordinateRHS_contDiffOn R hp hg hgenus hΓ hfree hsmooth hWP W
  have hca : c a ∈ (c).target := (c).map_source (mem_chart_source E a)
  have hR : ContDiffAt ℝ ∞ (RHS W) (c a) :=
    hRHS.contDiffAt ((c).open_target.mem_nhds hca)
  have hc : ContMDiffAt RI RI ∞ c a := by
    change ContMDiffAt RI RI ∞ (extChartAt RI (basePoint R)) a
    exact contMDiffAt_extChartAt' (mem_chart_source E a)
  apply (hR.comp_contMDiffAt hc).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun q =>
    nativeWPCartanLieFormValue_coordinates R hp hg hgenus hΓ hfree hsmooth W a q

/-- The original WP Lie form defined by its whole smooth Cartan expression. -/
def nativeWeilPeterssonFormLieDerivative
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    FormInterior.SmoothVectorField RI (M := T) → FormInterior.SmoothForm RI (M := T) 2 := by
  let := C
  let : IsManifold RI ω T := realManifold
  intro W
  exact ⟨Value W, contMDiff_nativeWPCartanLieFormValue
    R hp hg hgenus hΓ hfree hsmooth hWP W⟩

private theorem nativeWPCartanLieFormValue_apply :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (W : FormInterior.SmoothVectorField RI (M := T)) (q : T)
      (a b : TangentSpace RI q),
      Value W q ![a,b] =
        extDerivWithin (fun y : E => (Ω y).curryLeft
          (D ((c).symm y) (W ((c).symm y)))) (c).target (c q) ![D q a,D q b] +
        extDerivWithin Ω (c).target (c q) ![D q (W q),D q a,D q b] := by
  let := C
  let : IsManifold RI ω T := realManifold
  intro W q a b
  have hleft : (c).symm (c q) = q := (c).left_inv (mem_chart_source E q)
  change (RHS W (c q)) (fun i => D q (![a,b] i)) = _
  dsimp only [nativeWPCartanCoordinateRHS]
  rw [hleft]
  change
    extDerivWithin (fun y : E => (Ω y).curryLeft
      (D ((c).symm y) (W ((c).symm y)))) (c).target (c q)
        (fun i => D q (![a,b] i)) +
      extDerivWithin Ω (c).target (c q)
        (Matrix.vecCons (D q (W q)) (fun i => D q (![a,b] i))) = _
  congr 1
  · congr 1
    funext i
    fin_cases i <;> rfl
  · congr 1
    funext i
    fin_cases i <;> rfl

/-- The actual given-flow derivative is this same field-defined whole form
under the explicit Cartan identity. Thus its value is independent of which
actual same-field family realizes the existing local-flow inputs. -/
theorem nativeWP_formLieDerivativeAlong_eq_field
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth)
    (V : TopologicalSpace.Opens T) (ε : ℝ) (hε : 0 < ε) (Φ : ℝ → T → T) :
    letI := C
    letI : IsManifold RI ω T := realManifold
    ∀ (W Y Z : FormInterior.SmoothVectorField RI (M := T))
      (hzero : ∀ r ∈ V, Φ 0 r = r)
      (hflow : ∀ s ∈ Ioo (-ε) ε, ∀ t ∈ Ioo (-ε) ε,
        ∀ r ∈ V, s+t ∈ Ioo (-ε) ε → Φ t r ∈ V → Φ (s+t) r = Φ s (Φ t r))
      (hΦ : ContMDiffOn (𝓘(ℝ).prod RI) RI ∞
        (fun z : ℝ × T => Φ z.1 z.2) (Ioo (-ε) ε ×ˢ (V : Set T)))
      (hgen : ∀ t ∈ Ioo (-ε) ε, ∀ r ∈ V,
        mfderiv 𝓘(ℝ) RI (fun s : ℝ => Φ s r) t
          ((NormedSpace.fromTangentSpace (𝕜 := ℝ) t).symm 1) = W (Φ t r)),
      Unproved.Teichmuller.OriginalWeilPeterssonFormCartanAlong
        R hp hg hgenus hΓ hfree hsmooth hWP V ε hε Φ W Y Z hzero hflow hΦ hgen →
      ∀ (q : T) (hq : q ∈ V),
        nativeWeilPeterssonFormLieDerivativeAlong R hp hg hgenus hΓ hfree hsmooth
          q V hq ε hε Φ W hzero hflow hΦ hgen =
        nativeWeilPeterssonFormLieDerivative R hp hg hgenus hΓ hfree hsmooth hWP W q := by
  let := C
  let : IsManifold RI ω T := realManifold
  intro W Y Z hzero hflow hΦ hgen hCartan q hq
  apply ContinuousAlternatingMap.ext
  intro v
  have h := hCartan.1 q hq (v 0) (v 1)
  rw [← nativeWPCartanLieFormValue_apply R hp hg hgenus hΓ hfree hsmooth
    W q (v 0) (v 1)] at h
  have hv : (![v 0,v 1] : Fin 2 → TangentSpace RI q) = v := by
    funext i
    fin_cases i <;> rfl
  simpa only [hv, nativeWeilPeterssonFormLieDerivative, ContMDiffSection.coeFn_mk] using h

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
