module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalGenusOneParameterSupport
public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneWeilPeterssonParameter
public import LowDimensionalTopology.Geometry.Teichmuller.AnalyticCoverDescent

/-!
# The actual atlas Beltrami integral on a normalized torus

The scalar product is formed from genuine original-atlas differentials.
Actual chart derivative phases cancel in its pullback to the plane cover.
Its integral uses the same normalized measure on the original torus carrier.
Specified actual cover representatives identify it with the parameter pairing.
The flat harmonic relation uses the same positive cover density.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces

private theorem beltrami_phase_product (a b d : ℂ) (hd : d ≠ 0) :
    (a * conj d / d) * conj (b * conj d / d) = a * conj b := by
  have hdc : conj d ≠ 0 := by simpa using hd
  simp only [map_div₀, map_mul, Complex.conj_conj]
  field_simp [hd, hdc]

/-- The actual two Beltrami tensors give a scalar on the existing torus.
The evaluation theorem below removes the selected chart from its meaning. -/
def torusPointwiseBeltramiProduct (τ : ℍ)
    (μ ν : BeltramiDifferential (normalizedTorusModel τ).surface.toRiemannAtlas)
    (x : ComplexTorusCarrier) : ℂ :=
  let A := (normalizedTorusModel τ).surface.toRiemannAtlas
  let c := A.cover x
  let e : BeltramiDifferential.Chart A := ⟨c.choose, c.choose_spec.1⟩
  μ.coeff e ⟨e.val x, e.val.map_source c.choose_spec.2⟩ *
    conj (ν.coeff e ⟨e.val x, e.val.map_source c.choose_spec.2⟩)

/-- Every actual complex chart computes the same scalar product. -/
theorem torusPointwiseBeltramiProduct_eq_coeff (τ : ℍ)
    (μ ν : BeltramiDifferential (normalizedTorusModel τ).surface.toRiemannAtlas)
    (e : BeltramiDifferential.Chart (normalizedTorusModel τ).surface.toRiemannAtlas)
    (x : ComplexTorusCarrier) (hx : x ∈ e.val.source) :
    torusPointwiseBeltramiProduct τ μ ν x =
      μ.coeff e ⟨e.val x, e.val.map_source hx⟩ *
        conj (ν.coeff e ⟨e.val x, e.val.map_source hx⟩) := by
  let A := (normalizedTorusModel τ).surface.toRiemannAtlas
  let c := A.cover x
  let E : BeltramiDifferential.Chart A := ⟨c.choose, c.choose_spec.1⟩
  have hE : x ∈ E.val.source := c.choose_spec.2
  change μ.coeff E ⟨E.val x, E.val.map_source hE⟩ *
    conj (ν.coeff E ⟨E.val x, E.val.map_source hE⟩) = _
  rw [μ.compatible E e x hE hx, ν.compatible E e x hE hx]
  exact beltrami_phase_product _ _ _
    (BeltramiDifferential.transition_deriv_ne_zero E e x hE hx)

/-- The original analytic covering has nonzero derivative in every actual
target chart containing its image. -/
theorem normalizedTorusCoverChart_deriv_ne_zero (τ : ℍ)
    (e : BeltramiDifferential.Chart (normalizedTorusModel τ).surface.toRiemannAtlas)
    (z : ℂ) (hz : (normalizedTorusModel τ).projection z ∈ e.val.source) :
    deriv (e.val ∘ (normalizedTorusModel τ).projection) z ≠ 0 := by
  obtain ⟨P, hfun, hzP, hPa, _hsub⟩ :=
    analyticLocalHomeomorph_coordinateSheet (normalizedTorusModel τ).analytic_projection
      (normalizedTorusModel τ).covering.isLocalHomeomorph
      (OpenPartialHomeomorph.refl ℂ) rfl e.val e.property z (by trivial) hz
  have heq : (P : ℂ → ℂ) = e.val ∘ (normalizedTorusModel τ).projection := by
    simpa [riemannChartMap, Function.comp_def] using hfun
  rw [← heq]
  exact openPartialHomeomorph_analytic_forward_deriv_ne_zero P hPa z hzP

/-- Pulling both tensors to the actual plane cover leaves their scalar
product unchanged; the two genuine cover-chart derivative phases cancel. -/
theorem torusPointwiseBeltramiProduct_cover (τ : ℍ)
    (μ ν : BeltramiDifferential (normalizedTorusModel τ).surface.toRiemannAtlas)
    (z : ℂ) :
    torusPointwiseBeltramiProduct τ μ ν ((normalizedTorusModel τ).projection z) =
      torusCoverBeltramiValue τ μ z * conj (torusCoverBeltramiValue τ ν z) := by
  let A := (normalizedTorusModel τ).surface.toRiemannAtlas
  let p := (normalizedTorusModel τ).projection
  let c := A.cover (p z)
  let e : BeltramiDifferential.Chart A := ⟨c.choose, c.choose_spec.1⟩
  let a := μ.coeff e ⟨e.val (p z), e.val.map_source c.choose_spec.2⟩
  let b := ν.coeff e ⟨e.val (p z), e.val.map_source c.choose_spec.2⟩
  let d := deriv (e.val ∘ p) z
  have hd : d ≠ 0 := normalizedTorusCoverChart_deriv_ne_zero τ e z c.choose_spec.2
  change a * conj b = (a * conj d / d) * conj (b * conj d / d)
  exact (beltrami_phase_product a b d hd).symm

/-- The literal integral of the actual atlas tensors on the existing torus,
using the genuine normalized unit-area measure. -/
def torusAtlasBeltramiPairing (τ : ℍ)
    (μ ν : BeltramiDifferential (normalizedTorusModel τ).surface.toRiemannAtlas) : ℂ :=
  ∫ x : ComplexTorusCarrier, torusPointwiseBeltramiProduct τ μ ν x
    ∂normalizedTorusUnitAreaMeasure τ

/-- Specified cover representatives identify the actual atlas integral with
the parameter pairing on the same genuine normalized torus measure. -/
theorem torusAtlasBeltramiPairing_eq_parameterPairing (τ : ℍ)
    (μ ν : BeltramiDifferential (normalizedTorusModel τ).surface.toRiemannAtlas)
    (u v : ℂ)
    (hμ : ∀ z : ℂ, torusCoverBeltramiValue τ μ z = u * tangentBeltrami τ)
    (hν : ∀ z : ℂ, torusCoverBeltramiValue τ ν z = v * tangentBeltrami τ) :
    torusAtlasBeltramiPairing τ μ ν = pairing τ u v := by
  unfold torusAtlasBeltramiPairing pairing
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    obtain ⟨z, rfl⟩ := (normalizedTorusModel τ).surjective x
    rw [torusPointwiseBeltramiProduct_cover, hμ z, hν z])

/-- The original atlas integral has the specified coefficient for the given
actual cover representatives, retaining the same original chart data. -/
theorem torusAtlasBeltramiPairing_eq (τ : ℍ)
    (μ ν : BeltramiDifferential (normalizedTorusModel τ).surface.toRiemannAtlas)
    (u v : ℂ)
    (hμ : ∀ z : ℂ, torusCoverBeltramiValue τ μ z = u * tangentBeltrami τ)
    (hν : ∀ z : ℂ, torusCoverBeltramiValue τ ν z = v * tangentBeltrami τ) :
    torusAtlasBeltramiPairing τ μ ν =
      ((1 / (4 * τ.im ^ 2) : ℝ) : ℂ) * u * conj v := by
  rw [torusAtlasBeltramiPairing_eq_parameterPairing τ μ ν u v hμ hν, pairing_eq]

/-- The entire-cover quadratic coefficient associated to the flat harmonic
representative. It is a coefficient on the covering plane with the same
positive flat density and infinitesimal Beltrami value. -/
def flatHarmonicQuadraticCoverCoefficient (τ : ℍ) (u : ℂ) : ℂ :=
  ((normalizedTorusFlatDensity τ ^ 2 : ℝ) : ℂ) * conj (u * tangentBeltrami τ)

theorem flatHarmonicQuadraticCoverCoefficient_analytic (τ : ℍ) (u : ℂ) :
    AnalyticOnNhd ℂ (fun _ : ℂ => flatHarmonicQuadraticCoverCoefficient τ u) univ := by
  intro z _hz
  exact analyticAt_const

/-- The flat harmonic relation between the cover coefficient, the positive
flat density and the specified infinitesimal Beltrami coefficient. -/
theorem tangentBeltrami_eq_flatHarmonicCoverCoefficient (τ : ℍ) (u : ℂ) :
    u * tangentBeltrami τ =
      conj (flatHarmonicQuadraticCoverCoefficient τ u) /
        ((normalizedTorusFlatDensity τ ^ 2 : ℝ) : ℂ) := by
  have hd : ((normalizedTorusFlatDensity τ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (ne_of_gt (normalizedTorusFlatDensity_pos τ)))
  simp only [flatHarmonicQuadraticCoverCoefficient, map_mul,
    Complex.conj_ofReal, Complex.conj_conj]
  field_simp [hd]

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
