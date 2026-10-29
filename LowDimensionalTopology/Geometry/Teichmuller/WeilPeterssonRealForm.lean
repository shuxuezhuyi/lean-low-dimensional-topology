module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonRealCoefficients
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.Topology.Algebra.Module.Alternating.Basic
public import Mathlib.Tactic.FinCases

/-!
# Real WP fibre forms with the English normalization
Real scalar forms on the original tangent carrier. Continuous fibres and smooth
fixed coordinate evaluations do not assert a global smooth Riemannian bundle.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "TI" => 𝓘(ℂ, E)
local notation "C" => canonicalComplexChartedSpace R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp hsmooth
local notation "H" => nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth
local notation "coord" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth

/-- The same first-linear original WP product is bilinear over the real field. -/
def nativeWeilPeterssonHermitianRealBilinMap (a : TeichmullerSpace.{0,0} R) :
    letI := C
    TangentSpace TI a →ₗ[ℝ] TangentSpace TI a →ₗ[ℝ] ℂ := by
  let := C
  letI : InnerProductSpace.Core ℂ (TangentSpace TI a) := H a
  refine LinearMap.mk₂ ℝ (fun v w => (H a).inner w v) ?_ ?_ ?_ ?_
  · exact fun v z w => InnerProductSpace.Core.inner_add_right (𝕜 := ℂ) w v z
  · intro r v w
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),
      InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ), smul_eq_mul]
  · exact fun v w z => (H a).add_left w z v
  · intro r v w
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),
      InnerProductSpace.Core.inner_smul_left (𝕜 := ℂ), smul_eq_mul]
    have hr : (starRingEnd ℂ) (r : ℂ) = (r : ℂ) := RCLike.conj_ofReal r
    exact congrArg (fun z : ℂ => z * (H a).inner w v) hr

/-- The real WP pairing is twice the real part of the original Hermitian form. -/
def nativeWeilPeterssonRealBilinForm (a : TeichmullerSpace.{0,0} R) :
    letI := C; LinearMap.BilinForm ℝ (TangentSpace TI a) := by
  let := C
  exact (2 : ℝ) • (nativeWeilPeterssonHermitianRealBilinMap
    R hp hg hgenus hΓ hfree hsmooth a).compr₂ Complex.reLm

/-- Symmetry of the actual real WP pairing. -/
theorem nativeWeilPeterssonRealBilinForm_symm (a : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v w, nativeWeilPeterssonRealBilinForm R hp hg hgenus hΓ hfree hsmooth a v w =
      nativeWeilPeterssonRealBilinForm R hp hg hgenus hΓ hfree hsmooth a w v := by
  let := C
  intro v w
  change 2 * ((H a).inner w v).re = 2 * ((H a).inner v w).re
  simpa only [Complex.conj_re] using
    congrArg (fun z : ℂ => 2 * z.re) ((H a).conj_inner_symm v w)

/-- Strict positivity uses definiteness of the unchanged original integral form. -/
theorem nativeWeilPeterssonRealBilinForm_pos (a : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v, v ≠ 0 → 0 <
      nativeWeilPeterssonRealBilinForm R hp hg hgenus hΓ hfree hsmooth a v v := by
  let := C
  let : InnerProductSpace.Core ℂ (TangentSpace TI a) := H a
  intro v hv
  have hne : ((H a).inner v v).re ≠ 0 := by
    intro hz
    apply hv
    apply (H a).definite v
    have him : ((H a).inner v v).im = 0 :=
      InnerProductSpace.Core.inner_self_im (𝕜 := ℂ) v
    exact Complex.ext hz him
  exact mul_pos (by norm_num) (lt_of_le_of_ne ((H a).re_inner_nonneg v) hne.symm)

/-- The original fundamental form is the continuous real alternating
two-form `-2 Im h`, on exactly the same native tangent fibre. -/
def nativeWeilPeterssonFundamentalForm (a : TeichmullerSpace.{0,0} R) :
    letI := C; TangentSpace TI a [⋀^Fin 2]→L[ℝ] ℝ := by
  let := C
  letI : InnerProductSpace.Core ℂ (TangentSpace TI a) := H a
  let B := (-2 : ℝ) • (nativeWeilPeterssonHermitianRealBilinMap
    R hp hg hgenus hΓ hfree hsmooth a).compr₂ Complex.imLm
  let A : TangentSpace TI a [⋀^Fin 2]→ₗ[ℝ] ℝ :=
    { MultilinearMap.mk' (fun v => B (v 0) (v 1))
        (fun v i x y => by fin_cases i <;> simp)
        (fun v i r x => by fin_cases i <;> simp) with
      map_eq_zero_of_eq' := by
        intro v i j hv hij
        have h01 : v 0 = v 1 := by fin_cases i <;> fin_cases j <;> simp_all
        change -2 * ((H a).inner (v 1) (v 0)).im = 0
        rw [h01]
        have him : ((H a).inner (v 1) (v 1)).im = 0 :=
          InnerProductSpace.Core.inner_self_im (𝕜 := ℂ) (v 1)
        rw [him, mul_zero] }
  let L : TangentSpace TI a ≃ₗ[ℝ] E := (coord a).toLinearEquiv.restrictScalars ℝ
  let F : E →L[ℝ] E →L[ℝ] ℝ :=
    (B.compl₁₂ L.symm.toLinearMap L.symm.toLinearMap).toContinuousBilinearMap
  refine { A with cont := ?_ }
  have hL (v : TangentSpace TI a) : L.symm ((coord a) v) = v :=
    (coord a).symm_apply_apply v
  have h0 : Continuous (fun v : Fin 2 → TangentSpace TI a => (coord a) (v 0)) :=
    (coord a).continuous.comp (continuous_apply 0)
  have h1 : Continuous (fun v : Fin 2 → TangentSpace TI a => (coord a) (v 1)) :=
    (coord a).continuous.comp (continuous_apply 1)
  change Continuous (fun v : Fin 2 → TangentSpace TI a => B (v 0) (v 1))
  simpa only [F, LinearMap.toContinuousBilinearMap_apply, LinearMap.compl₁₂_apply,
    Function.comp_def, Function.uncurry, LinearEquiv.coe_coe, hL] using
    F.continuous₂.comp (h0.prodMk h1)

/-- The first-linear source slots and the exact English sign and factor. -/
@[simp] theorem nativeWeilPeterssonFundamentalForm_apply (a : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v, nativeWeilPeterssonFundamentalForm R hp hg hgenus hΓ hfree hsmooth a v =
      -2 * ((H a).inner (v 1) (v 0)).im := by
  let := C
  exact fun _ => rfl

/-- The defining English identity with `J` represented by complex multiplication. -/
theorem nativeWeilPeterssonFundamentalForm_eq_realBilinForm
    (a : TeichmullerSpace.{0,0} R) :
    letI := C
    ∀ v w, nativeWeilPeterssonFundamentalForm R hp hg hgenus hΓ hfree hsmooth a ![v,w] =
      nativeWeilPeterssonRealBilinForm R hp hg hgenus hΓ hfree hsmooth a (Complex.I • v) w := by
  let := C
  let : InnerProductSpace.Core ℂ (TangentSpace TI a) := H a
  intro v w
  change -2 * ((H a).inner w v).im = 2 * ((H a).inner w (Complex.I • v)).re
  rw [InnerProductSpace.Core.inner_smul_right (𝕜 := ℂ)]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub]
  ring

/-- Actual inverse-coordinate evaluations of this fundamental form are smooth
under the named analytic input; this is a finite-chart consumer only. -/
theorem contDiffOn_nativeWeilPeterssonFundamentalForm_of_localSmoothness
    (hWP : Unproved.Teichmuller.WeilPeterssonLocalCoefficientSmoothness
      R hp hg hgenus hΓ hfree hsmooth) (a : TeichmullerSpace.{0,0} R) (v w : E) :
    letI := C
    ContDiffOn ℝ ∞ (fun t => let q := (chart a).symm t
      nativeWeilPeterssonFundamentalForm R hp hg hgenus hΓ hfree hsmooth q
        ![(coord q).symm v, (coord q).symm w]) (chart a).target := by
  let := C
  apply (contDiffOn_nativeWeilPeterssonRealCoordinatePairing_of_localSmoothness
    R hp hg hgenus hΓ hfree hsmooth hWP a (Complex.I • v) w).congr
  intro t _
  rw [nativeWeilPeterssonFundamentalForm_eq_realBilinForm]
  change 2 * ((H _).inner ((coord _).symm w) (Complex.I • (coord _).symm v)).re =
    2 * ((H _).inner ((coord _).symm w) ((coord _).symm (Complex.I • v))).re
  rw [map_smul]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
