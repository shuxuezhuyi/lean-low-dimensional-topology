module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalClosedVectorFieldLocalVariation
public import LowDimensionalTopology.Geometry.Teichmuller.SmoothMetricLieUniqueness
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHorizontalTensorOrthogonality

/-!
# The native metric Lie tensor and actual diffeomorphism directions

A concrete classical local-variation input supplies actual families in the
existing homotopy-identity group. The native tensor is constructed from their
literal pullbacks, and the full coordinate law proves family independence.
The same tensor image is exactly the set of actual local family directions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
namespace SmoothSurfaceMetric

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- Every actual native field has a smooth symmetric pullback variation
from a family in the existing homotopy-identity group. -/
theorem exists_metricLieTensor_localVariation
    (hvar : Unproved.Teichmuller.OriginalClosedVectorFieldLocalVariation R)
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X),
      ∃ L : SmoothSymmetricTwoTensor R,
        HasOriginalMetricLieCoordinates R g V L ∧
        ∃ (epsilon : ℝ), 0 < epsilon ∧
          ∃ Phi : ℝ → ↥(OrientedSurfaceAut.homotopyIdentitySubgroup R),
            (∀ x : X, (Phi 0).val.smooth.toHomeomorph x = x) ∧
            ContMDiffOn (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
              (fun p : ℝ × X => (Phi p.1).val.smooth.toHomeomorph p.2)
              (Set.Ioo (-epsilon) epsilon ×ˢ Set.univ) ∧
            (∀ (e : OriginalComplexChart R.toRiemannSurface)
                (x : X) (hx : x ∈ e.val.source),
              HasDerivAt (fun t : ℝ => e.val ((Phi t).val.smooth.toHomeomorph x))
                (SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx (V x)) 0) ∧
            ∀ (x : X) (a b : RealSurfaceTangent R.toRiemannSurface x),
              HasDerivAt (fun t : ℝ => (pullback (Phi t).val.smooth g).inner x a b)
                (L.val x a b) 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro V
  rcases hvar V with ⟨epsilon, hepsilon, Phi, hzero, hPhi, hV⟩
  let Psi : ℝ → SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface :=
    fun t => (Phi t).val.smooth
  have hjoint (x : X) : ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × X => (Psi p.1).toHomeomorph p.2) (0, x) :=
    hPhi.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
      ⟨⟨neg_lt_zero.mpr hepsilon, hepsilon⟩, Set.mem_univ x⟩)
  rcases exists_metricLieTensor_of_smoothFamily R Psi g hzero hjoint V hV with
    ⟨L, hL, hcoord⟩
  exact ⟨L, hcoord, epsilon, hepsilon, Phi, hzero, hPhi, hV, hL⟩

/-- The native metric Lie tensor, selected from actual local family variations. -/
def nativeMetricLie
    (hvar : Unproved.Teichmuller.OriginalClosedVectorFieldLocalVariation R)
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X) → SmoothSymmetricTwoTensor R := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact fun V => (exists_metricLieTensor_localVariation R hvar g V).choose

/-- The selected tensor has the full original coordinate law for every field. -/
theorem nativeMetricLie_hasOriginalCoordinates
    (hvar : Unproved.Teichmuller.OriginalClosedVectorFieldLocalVariation R)
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X),
      HasOriginalMetricLieCoordinates R g V (nativeMetricLie R hvar g V) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro V
  exact (exists_metricLieTensor_localVariation R hvar g V).choose_spec.1

/-- The chosen tensor retains an actual family, its same-field velocity and
the literal pullback derivative on all original tangent pairs. -/
theorem nativeMetricLie_localVariation
    (hvar : Unproved.Teichmuller.OriginalClosedVectorFieldLocalVariation R)
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X),
      ∃ (epsilon : ℝ), 0 < epsilon ∧
        ∃ Phi : ℝ → ↥(OrientedSurfaceAut.homotopyIdentitySubgroup R),
          (∀ x : X, (Phi 0).val.smooth.toHomeomorph x = x) ∧
          ContMDiffOn (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
            (fun p : ℝ × X => (Phi p.1).val.smooth.toHomeomorph p.2)
            (Set.Ioo (-epsilon) epsilon ×ˢ Set.univ) ∧
          (∀ (e : OriginalComplexChart R.toRiemannSurface)
              (x : X) (hx : x ∈ e.val.source),
            HasDerivAt (fun t : ℝ => e.val ((Phi t).val.smooth.toHomeomorph x))
              (SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx (V x)) 0) ∧
          ∀ (x : X) (a b : RealSurfaceTangent R.toRiemannSurface x),
            HasDerivAt (fun t : ℝ => (pullback (Phi t).val.smooth g).inner x a b)
              ((nativeMetricLie R hvar g V).val x a b) 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro V
  exact (exists_metricLieTensor_localVariation R hvar g V).choose_spec.2

/-- Every given family with this same velocity differentiates to the selected
native tensor; no choice of family changes the scalar derivative. -/
theorem nativeMetricLie_hasDerivAt_of_sameVelocity
    (hvar : Unproved.Teichmuller.OriginalClosedVectorFieldLocalVariation R)
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (Phi : ℝ → SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface)
    (hzero : ∀ x : X, (Phi 0).toHomeomorph x = x) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    (∀ x : X, ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
      (fun p : ℝ × X => (Phi p.1).toHomeomorph p.2) (0, x)) →
    ∀ V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X),
      (∀ (e : OriginalComplexChart R.toRiemannSurface)
          (x : X) (hx : x ∈ e.val.source),
        HasDerivAt (fun t : ℝ => e.val ((Phi t).toHomeomorph x))
          (SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx (V x)) 0) →
      ∀ (x : X) (a b : RealSurfaceTangent R.toRiemannSurface x),
        HasDerivAt (fun t : ℝ => (pullback (Phi t) g).inner x a b)
          ((nativeMetricLie R hvar g V).val x a b) 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro hPhi V hV
  exact hasDerivAt_pullback_of_sameNativeVelocity R Phi g hzero hPhi V hV
    (nativeMetricLie R hvar g V) (nativeMetricLie_hasOriginalCoordinates R hvar g V)

end SmoothSurfaceMetric

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- Actual metric directions of local families in the existing Diff0 group. -/
def diffeomorphismVerticalTensors (g : SmoothSurfaceMetric R.toRiemannSurface) :
    Set (SmoothSymmetricTwoTensor R) :=
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  {L | ∃ (epsilon : ℝ), 0 < epsilon ∧
    ∃ Phi : ℝ → ↥(OrientedSurfaceAut.homotopyIdentitySubgroup R),
      (∀ x : X, (Phi 0).val.smooth.toHomeomorph x = x) ∧
      ContMDiffOn (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
        (fun p : ℝ × X => (Phi p.1).val.smooth.toHomeomorph p.2)
        (Set.Ioo (-epsilon) epsilon ×ˢ Set.univ) ∧
      ∀ (x : X) (a b : RealSurfaceTangent R.toRiemannSurface x),
        HasDerivAt (fun t : ℝ => (SmoothSurfaceMetric.pullback (Phi t).val.smooth g).inner x a b)
          (L.val x a b) 0}

/-- The all-field native Lie image is exactly the actual Diff0-family directions. -/
theorem diffeomorphismVerticalTensors_eq_range_nativeMetricLie
    (hvar : Unproved.Teichmuller.OriginalClosedVectorFieldLocalVariation R)
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    diffeomorphismVerticalTensors R g =
      Set.range (SmoothSurfaceMetric.nativeMetricLie R hvar g) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  ext L
  constructor
  · rintro ⟨epsilon, hepsilon, Phi, hzero, hPhi, hL⟩
    let Psi : ℝ → SmoothSurfaceEquiv R.toRiemannSurface R.toRiemannSurface :=
      fun t => (Phi t).val.smooth
    have hjoint (x : X) : ContMDiffAt (𝓘(ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, ℂ) ∞
        (fun p : ℝ × X => (Psi p.1).toHomeomorph p.2) (0, x) :=
      hPhi.contMDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds
        ⟨⟨neg_lt_zero.mpr hepsilon, hepsilon⟩, Set.mem_univ x⟩)
    rcases SmoothSurfaceMetric.exists_nativeMetricLie_of_smoothFamily R Psi g hzero hjoint with
      ⟨V, K, hV, hK, hcoord⟩
    have hLK : L = K := by
      apply Subtype.ext
      apply ContMDiffSection.ext
      intro x
      ext a b
      exact (hL x a b).unique (hK x a b)
    have hKcanonical : K = SmoothSurfaceMetric.nativeMetricLie R hvar g V :=
      SmoothSurfaceMetric.metricLieTensor_unique R g V K
        (SmoothSurfaceMetric.nativeMetricLie R hvar g V) hcoord
        (SmoothSurfaceMetric.nativeMetricLie_hasOriginalCoordinates R hvar g V)
    exact ⟨V, hKcanonical.symm.trans hLK.symm⟩
  · rintro ⟨V, rfl⟩
    rcases SmoothSurfaceMetric.nativeMetricLie_localVariation R hvar g V with
      ⟨epsilon, hepsilon, Phi, hzero, hPhi, hV, hL⟩
    exact ⟨epsilon, hepsilon, Phi, hzero, hPhi, hL⟩

/-- The actual all-field Lie directions are orthogonal exactly when the whole
native divergence covector vanishes, under the concrete Green input. -/
theorem nativeMetricLie_orthogonality_iff_divergence_zero
    (hvar : Unproved.Teichmuller.OriginalClosedVectorFieldLocalVariation R)
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R g)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u})
    (hgreen : Unproved.Teichmuller.OriginalClosedMetricTensorGreen.{u}) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ h : SmoothSymmetricTwoTensor R,
      (∀ V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X),
        metricTensorL2Pairing R g harea h (SmoothSurfaceMetric.nativeMetricLie R hvar g V) = 0) ↔
      ∀ x : X, (metricTensorDivergence R g hdiv h).toFun x = 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact metricTensorL2Pairing_lie_eq_zero_iff_divergence_zero R g harea hdiv hgreen
    (SmoothSurfaceMetric.nativeMetricLie R hvar g)
    (SmoothSurfaceMetric.nativeMetricLie_hasOriginalCoordinates R hvar g)

/-- Both actual vertical families have exactly the original holomorphic
quadratic image as their orthogonal complement. -/
theorem original_horizontal_orthogonality_of_localVariation
    (hvar : Unproved.Teichmuller.OriginalClosedVectorFieldLocalVariation R)
    (G : AtlasInducedMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R G.metric)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u})
    (hgreen : Unproved.Teichmuller.OriginalClosedMetricTensorGreen.{u}) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ h : SmoothSymmetricTwoTensor R,
      ((∀ psi : C^∞⟮𝓘(ℝ, ℂ), X; ℝ⟯,
          metricTensorL2Pairing R G.metric harea h
            (conformalScaleLinear (R := R) G.metric psi) = 0) ∧
        (∀ V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X),
          metricTensorL2Pairing R G.metric harea h
            (SmoothSurfaceMetric.nativeMetricLie R hvar G.metric V) = 0)) ↔
      h ∈ horizontalQuadraticTensors R := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact original_horizontal_orthogonality_iff R G harea hdiv hgreen
    (SmoothSurfaceMetric.nativeMetricLie R hvar G.metric)
    (SmoothSurfaceMetric.nativeMetricLie_hasOriginalCoordinates R hvar G.metric)

end LowDimensionalTopology.Geometry.Teichmuller
