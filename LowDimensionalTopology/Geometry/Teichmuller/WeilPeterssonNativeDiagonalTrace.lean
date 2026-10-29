module

public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonHarmonicDiagonalTrace
public import LowDimensionalTopology.Geometry.Teichmuller.WeilPeterssonRealCoefficients

/-!
# The actual original native WP diagonal trace

Actual harmonic classes are represented by original quadratic differentials.
The proved harmonic trace therefore applies to the genuine native tangent
image, with its a.e. representatives and original selected Core. The existing
real coefficient expansion and the same Hermitian symmetry recover the full
complex self-pairing, giving the unchanged original finite-coordinate trace.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

open Surfaces GammaMeasurableBeltrami

private theorem sesquilinear_congr_ae {u v u' v' : ℍ → ℂ}
    (hu : u =ᵐ[flatArea] u') (hv : v =ᵐ[flatArea] v') (ζ z : ℍ) :
    sesquilinear u v ζ z = sesquilinear u' v' ζ z := by
  unfold sesquilinear
  apply integral_congr_ae
  filter_upwards [hv] with ξ hξ
  apply integral_congr_ae
  filter_upwards [hu] with η hη
  simp only [sesquilinearIntegrand, hξ, hη]

private theorem beltramiPairing_congr_ae (F : Set ℍ) {u v u' v' : ℍ → ℂ}
    (hu : u =ᵐ[flatArea] u') (hv : v =ᵐ[flatArea] v') :
    WeilPetersson.beltramiPairing F u v = WeilPetersson.beltramiPairing F u' v' := by
  unfold WeilPetersson.beltramiPairing WeilPetersson.weightedPairing
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae hu, ae_restrict_of_ae hv] with ξ hξ hξ'
  rw [hξ, hξ']

/-- The trace retains the actual harmonic class and its original region,
without imposing a pointwise representative or any trace hypothesis. -/
theorem harmonic_class_sesquilinear_diagonal_trace
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (p : ℍ → X) {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (b c : NativePetersson.Harmonic R P p hp F hF) :
    (∫ ζ in F, sesquilinear (fun η => b.val.val η) (fun ξ => c.val.val ξ) ζ ζ ∂flatArea) =
      (-(Real.pi ^ 2 / 12) : ℂ) * WeilPetersson.beltramiPairing F b.val.val c.val.val := by
  obtain ⟨q, hq⟩ := (NativePetersson.mem_harmonicSubmodule_iff_exists_quadratic
    R P p hp F hF b.val).mp b.property
  obtain ⟨r, hr⟩ := (NativePetersson.mem_harmonicSubmodule_iff_exists_quadratic
    R P p hp F hF c.val).mp c.property
  have hb : (fun η : ℍ => b.val.val η) =ᵐ[flatArea] NativeHarmonicBeltrami.coefficient R p q := by
    rw [← hq]
    exact ae_hyperbolic_iff.mp (NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp q)
  have hc : (fun ξ : ℍ => c.val.val ξ) =ᵐ[flatArea] NativeHarmonicBeltrami.coefficient R p r := by
    rw [← hr]
    exact ae_hyperbolic_iff.mp (NativeHarmonicBeltrami.ofQuadratic_coe_ae R p hp r)
  calc
    _ = ∫ ζ in F, sesquilinear (NativeHarmonicBeltrami.coefficient R p q)
        (NativeHarmonicBeltrami.coefficient R p r) ζ ζ ∂flatArea :=
      integral_congr_ae (Eventually.of_forall fun ζ => sesquilinear_congr_ae hb hc ζ ζ)
    _ = _ := (harmonic_sesquilinear_diagonal_trace R p hp P F hF q r).trans
      (congrArg (fun z : ℂ => (-(Real.pi ^ 2 / 12) : ℂ) * z)
        (beltramiPairing_congr_ae F hb hc)).symm

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

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
local notation "β" => coefficientProjection R hg hgenus
  (canonicalHandleGroupPresentation g) hΓ hfree hp
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "H" => nativeWeilPeterssonCore R hp hg hgenus hΓ hfree hsmooth
local notation "chart" => nativeWeilPeterssonCoordinateChart R hp hg hgenus hΓ hfree hsmooth
local notation "coeff" => nativeWeilPeterssonLocalCoefficient R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth

private theorem coordinate_inner_self_eq_sum (a : TeichmullerSpace R) (v t : E) :
    letI := C
    (H ((chart a).symm t)).inner ((K ((chart a).symm t)).symm v)
      ((K ((chart a).symm t)).symm v) =
        ∑ j, ∑ k, v j * conj (v k) * coeff a j k t := by
  classical
  let := C
  let q := (chart a).symm t
  let x := (K q).symm v
  let S : ℂ := ∑ j, ∑ k, v j * conj (v k) * coeff a j k t
  have hre := nativeWeilPeterssonRealCoordinatePairing_eq_sum
    R hp hg hgenus hΓ hfree hsmooth a v v t
  change 2 * ((H q).inner x x).re = 2 * S.re at hre
  have hcoreim : ((H q).inner x x).im = 0 := by
    have hi := congrArg Complex.im ((H q).conj_inner_symm x x)
    simp only [Complex.conj_im] at hi
    linarith
  have hSconj : conj S = S := by
    dsimp only [S]
    simp only [map_sum, map_mul, Complex.conj_conj,
      nativeWeilPeterssonLocalCoefficient_conj R hp hg hgenus hΓ hfree hsmooth]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hSim : S.im = 0 := by
    have hi := congrArg Complex.im hSconj
    simp only [Complex.conj_im] at hi
    linarith
  apply Complex.ext
  · linarith
  · exact hcoreim.trans hSim.symm

/-- The actual native harmonic image gives exactly the original selected
Core pairing at the same coefficient point. -/
theorem nativeWeilPetersson_sesquilinear_diagonal_trace_core
    (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (u v : E) :
    letI := C
    (∫ ζ in F, SourceKernel.sesquilinear (μ ν P F hF u) (μ ν P F hF v) ζ ζ ∂flatArea) =
      (-(Real.pi ^ 2 / 12) : ℂ) *
        (H (β ν.val)).inner ((K (β ν.val)).symm v) ((K (β ν.val)).symm u) := by
  let := C
  let b := TH ν P F hF hsmooth ((K (β ν.val)).symm u)
  let c := TH ν P F hF hsmooth ((K (β ν.val)).symm v)
  have h := SourceKernel.harmonic_class_sesquilinear_diagonal_trace
    (deformedNativeSurface R hgenus hΓ hp ν) (deformedTargetCover R hgenus hΓ hp ν)
    (deformedNativeSurface_uniformization R hgenus hΓ hp ν) P F hF b c
  exact h.trans (congrArg (fun z : ℂ => (-(Real.pi ^ 2 / 12) : ℂ) * z)
    (nativeWeilPeterssonCore_integral R hp hg hgenus hΓ hfree hsmooth ν P F hF
      ((K (β ν.val)).symm u) ((K (β ν.val)).symm v))).symm

/-- The exact original native diagonal trace, for every coefficient point
and every original chart, with no diagonal-control or PV premise. -/
theorem nativeWeilPetersson_sesquilinear_diagonal_trace
    (a : TeichmullerSpace R) (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F) (v : E) :
    (∫ ζ in F, SourceKernel.sesquilinear (μ ν P F hF v) (μ ν P F hF v) ζ ζ ∂flatArea) =
      ((-(Real.pi ^ 2 / 12) : ℝ) : ℂ) *
        ∑ j, ∑ k, v j * conj (v k) * coeff a j k ((chart a) (β ν.val)) := by
  let := C
  have hq : (chart a).symm ((chart a) (β ν.val)) = β ν.val :=
    (chart a).left_inv (show β ν.val ∈ (chart a).source from mem_chart_source E (β ν.val))
  have hs := coordinate_inner_self_eq_sum R hp hg hgenus hΓ hfree hsmooth
    a v ((chart a) (β ν.val))
  rw [hq] at hs
  have h := (nativeWeilPetersson_sesquilinear_diagonal_trace_core
    R hp hg hgenus hΓ hfree hsmooth ν P F hF v v).trans
      (congrArg (fun z : ℂ => (-(Real.pi ^ 2 / 12) : ℂ) * z) hs)
  simpa only [Complex.ofReal_neg, Complex.ofReal_div, Complex.ofReal_pow,
    Complex.ofReal_ofNat] using h

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
