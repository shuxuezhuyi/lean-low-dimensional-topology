module

public import LowDimensionalTopology.Unproved.Teichmuller.WeilPeterssonMixedKernelControl
public import Mathlib.Tactic.Ring

/-!
# Mixed WP kernel control from the existing analytic inputs

This draft proves the exact proposed mixed control; it adds no analytic
obligation. Actual source directions are chosen L-infinity representatives,
so their linearity is used only almost everywhere inside ordinary integrals.
The singular A kernel is never distributed over an addition or a scalar.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

private theorem sesquilinear_congr_ae {u u' v v' : ℍ → ℂ}
    (hu : u =ᵐ[flatArea] u') (hv : v =ᵐ[flatArea] v') (ζ z : ℍ) :
    sesquilinear u v ζ z = sesquilinear u' v' ζ z := by
  unfold sesquilinear
  apply integral_congr_ae
  filter_upwards [hv] with ξ hξ
  apply integral_congr_ae
  filter_upwards [hu] with η hη
  simp only [sesquilinearIntegrand, hη, hξ]

private theorem sesquilinear_add_left (u w v : ℍ → ℂ) (ζ z : ℍ)
    (hu : SesquilinearIntegralExists u v ζ z)
    (hw : SesquilinearIntegralExists w v ζ z) :
    sesquilinear (u + w) v ζ z = sesquilinear u v ζ z + sesquilinear w v ζ z := by
  have hi (ξ : ℍ) :
      (∫ η : ℍ, sesquilinearIntegrand (u + w) v ζ z ξ η ∂flatArea) =
        (∫ η : ℍ, sesquilinearIntegrand u v ζ z ξ η ∂flatArea) +
          ∫ η : ℍ, sesquilinearIntegrand w v ζ z ξ η ∂flatArea := by
    have he : sesquilinearIntegrand (u + w) v ζ z ξ =
        fun η => sesquilinearIntegrand u v ζ z ξ η +
          sesquilinearIntegrand w v ζ z ξ η := by
      funext η
      simp only [sesquilinearIntegrand, Pi.add_apply]
      ring
    rw [he, integral_add (hu.1 ξ) (hw.1 ξ)]
  simp only [sesquilinear, hi, integral_add hu.2 hw.2]

private theorem sesquilinear_add_right (u v w : ℍ → ℂ) (ζ z : ℍ)
    (hv : SesquilinearIntegralExists u v ζ z)
    (hw : SesquilinearIntegralExists u w ζ z) :
    sesquilinear u (v + w) ζ z = sesquilinear u v ζ z + sesquilinear u w ζ z := by
  have hi (ξ : ℍ) :
      (∫ η : ℍ, sesquilinearIntegrand u (v + w) ζ z ξ η ∂flatArea) =
        (∫ η : ℍ, sesquilinearIntegrand u v ζ z ξ η ∂flatArea) +
          ∫ η : ℍ, sesquilinearIntegrand u w ζ z ξ η ∂flatArea := by
    have he : sesquilinearIntegrand u (v + w) ζ z ξ =
        fun η => sesquilinearIntegrand u v ζ z ξ η +
          sesquilinearIntegrand u w ζ z ξ η := by
      funext η
      simp only [sesquilinearIntegrand, Pi.add_apply, map_add]
      ring
    rw [he, integral_add (hv.1 ξ) (hw.1 ξ)]
  simp only [sesquilinear, hi, integral_add hv.2 hw.2]

private theorem sesquilinear_smul_left (c : ℂ) (u v : ℍ → ℂ) (ζ z : ℍ) :
    sesquilinear (c • u) v ζ z = c * sesquilinear u v ζ z := by
  have he (ξ η : ℍ) : sesquilinearIntegrand (c • u) v ζ z ξ η =
      c * sesquilinearIntegrand u v ζ z ξ η := by
    simp only [sesquilinearIntegrand, Pi.smul_apply, smul_eq_mul]
    ring
  simp only [sesquilinear, he, integral_const_mul]

private theorem sesquilinear_smul_right (c : ℂ) (u v : ℍ → ℂ) (ζ z : ℍ) :
    sesquilinear u (c • v) ζ z = conj c * sesquilinear u v ζ z := by
  have he (ξ η : ℍ) : sesquilinearIntegrand u (c • v) ζ z ξ η =
      conj c * sesquilinearIntegrand u v ζ z ξ η := by
    simp only [sesquilinearIntegrand, Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  simp only [sesquilinear, he, integral_const_mul]

private theorem four_mixed_real (u v : ℍ → ℂ) (ζ z : ℍ) :
    four u v v u ζ z =
      ((‖bilinear u v ζ z + bilinear v u ζ z‖ ^ 2 +
        2 * ‖sesquilinear u v ζ z‖ ^ 2 : ℝ) : ℂ) := by
  unfold four
  rw [add_comm (bilinear v u ζ z) (bilinear u v ζ z)]
  calc
    _ = (bilinear u v ζ z + bilinear v u ζ z) *
          conj (bilinear u v ζ z + bilinear v u ζ z) +
        2 * (sesquilinear u v ζ z * conj (sesquilinear u v ζ z)) := by ring
    _ = _ := by
      rw [Complex.mul_conj', Complex.mul_conj']
      push_cast
      ring

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson.SourceKernel

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport WeilPetersson

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})

local notation "E" => Fin (3*g-3) → ℂ
local notation "hP" => canonicalHandleGroupPresentation g
local notation "C" => canonicalComplexChartedSpace R hg hgenus hP hΓ hfree hp hsmooth
local notation "β" => coefficientProjection R hg hgenus hP hΓ hfree hp
local notation "K" => nativeWeilPeterssonCoordinateEquiv R hp hg hgenus hΓ hfree hsmooth
local notation "TH" => nonzeroTangentHarmonicEquiv R hp hg hgenus hΓ hfree
local notation "μ" => nativeWeilPeterssonSourceDirection R hp hg hgenus hΓ hfree hsmooth

variable (ν : Ball Γ)
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

private theorem sourceDirection_add_ae (u w : E) :
    μ ν P F hF (u + w) =ᵐ[flatArea] μ ν P F hF u + μ ν P F hF w := by
  let := C
  apply ae_hyperbolic_iff.mp
  change (fun z => (TH ν P F hF hsmooth ((K (β ν.val)).symm (u + w))).val.val z) =ᵐ[volume] _
  rw [map_add, map_add]
  exact Lp.coeFn_add _ _

private theorem sourceDirection_smul_ae (c : ℂ) (u : E) :
    μ ν P F hF (c • u) =ᵐ[flatArea] c • μ ν P F hF u := by
  let := C
  apply ae_hyperbolic_iff.mp
  change (fun z => (TH ν P F hF hsmooth ((K (β ν.val)).symm (c • u))).val.val z) =ᵐ[volume] _
  rw [map_smul, map_smul]
  exact Lp.coeFn_smul c _

omit ν P F hF in
/-- The proposed mixed control is a consequence of the original PV and
diagonal obligations. No new unresolved analytic premise is required. -/
theorem nativeWeilPeterssonMixedKernelControl_of_secondVariation_diagonal
    (hvary : Unproved.Teichmuller.WeilPeterssonPrincipalValueSecondVariation
      R hp hg hgenus hΓ hfree hsmooth)
    (hdiag : Unproved.Teichmuller.WeilPeterssonDiagonalKernelControl
      R hp hg hgenus hΓ hfree hsmooth) :
    LowDimensionalTopology.Unproved.Teichmuller.WeilPeterssonMixedKernelControl
      R hp hg hgenus hΓ hfree hsmooth := by
  intro ν P F hF v
  let B (u w : E) := SourceKernel.sesquilinear (μ ν P F hF u) (μ ν P F hF w)
  have he := (hvary (β ν.val) ν P F hF).1.2.1
  have ha (u w s : E) : B (u + w) s = B u s + B w s := by
    funext ζ z
    exact (SourceKernel.sesquilinear_congr_ae
      (sourceDirection_add_ae R hp hg hgenus hΓ hfree hsmooth ν P F hF u w)
      EventuallyEq.rfl ζ z).trans
        (SourceKernel.sesquilinear_add_left _ _ _ ζ z (he u s ζ z) (he w s ζ z))
  have hs (c : ℂ) (u s : E) : B (c • u) s = c • B u s := by
    funext ζ z
    exact (SourceKernel.sesquilinear_congr_ae
      (sourceDirection_smul_ae R hp hg hgenus hΓ hfree hsmooth ν P F hF c u)
      EventuallyEq.rfl ζ z).trans
        (SourceKernel.sesquilinear_smul_left c _ _ ζ z)
  have ha' (u w s : E) : B u (w + s) = B u w + B u s := by
    funext ζ z
    exact (SourceKernel.sesquilinear_congr_ae EventuallyEq.rfl
      (sourceDirection_add_ae R hp hg hgenus hΓ hfree hsmooth ν P F hF w s) ζ z).trans
        (SourceKernel.sesquilinear_add_right _ _ _ ζ z (he u w ζ z) (he u s ζ z))
  have hs' (c : ℂ) (u s : E) : B u (c • s) = conj c • B u s := by
    funext ζ z
    exact (SourceKernel.sesquilinear_congr_ae EventuallyEq.rfl
      (sourceDirection_smul_ae R hp hg hgenus hΓ hfree hsmooth ν P F hF c s) ζ z).trans
        (SourceKernel.sesquilinear_smul_right c _ _ ζ z)
  refine ⟨⟨fun u w => ha u w v, fun c u => hs c u v⟩, ?_⟩
  intro u
  let e (ζ z : ℍ) : ℝ :=
    ‖SourceKernel.bilinear (μ ν P F hF u) (μ ν P F hF v) ζ z +
      SourceKernel.bilinear (μ ν P F hF v) (μ ν P F hF u) ζ z‖ ^ 2 +
      2 * ‖B u v ζ z‖ ^ 2
  have hfour := (hvary (β ν.val) ν P F hF).1.2.2 u v v u
  have hreal (ζ z : ℍ) :
      SourceKernel.four (μ ν P F hF u) (μ ν P F hF v)
        (μ ν P F hF v) (μ ν P F hF u) ζ z = (e ζ z : ℂ) :=
    SourceKernel.four_mixed_real _ _ ζ z
  have hi (ζ : ℍ) : Integrable (e ζ) flatArea := by
    simpa only [hreal, RCLike.re_eq_complex_re, Complex.ofReal_re] using (hfour.1 ζ).re
  have ho : IntegrableOn (fun ζ => ∫ z : ℍ, e ζ z ∂flatArea) F flatArea := by
    simpa only [hreal, integral_complex_ofReal, RCLike.re_eq_complex_re,
      Complex.ofReal_re] using hfour.2.re
  refine ⟨hi, ho, ?_⟩
  intro ζ
  have hc (w : E) : Continuous (B w w ζ) :=
    (hdiag (β ν.val) ν P F hF w).2.2.1 ζ
  have hpol : B u v ζ = fun z =>
      (B (u + v) (u + v) ζ z + Complex.I * B (u + Complex.I • v) (u + Complex.I • v) ζ z -
        (1 + Complex.I) * (B u u ζ z + B v v ζ z)) / 2 := by
    funext z
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
    simp only [ha, hs, ha', hs', Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.conj_I]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  apply ((((hc (u + v)).add ((hc (u + Complex.I • v)).const_mul Complex.I)).sub
    (((hc u).add (hc v)).const_mul (1 + Complex.I))).div_const 2).congr
  intro z
  exact congrFun hpol.symm z

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
