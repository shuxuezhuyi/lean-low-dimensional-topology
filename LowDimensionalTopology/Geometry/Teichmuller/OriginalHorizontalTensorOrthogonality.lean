module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricTensorGreen
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalConformalTensorOrthogonality
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalHorizontalQuadraticTensors
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalNativeTTQuadraticEquivalence

/-!
# The original horizontal image for a given native Lie producer

For a compatible metric on the same original complex surface, conformal and
Green orthogonality give the two whole native TT conditions. The already
proved original TT correspondence supplies the actual holomorphic quadratic
differential. The source convention is twice its real tensor. Existence of
the all-vector-field Lie producer remains an explicit independent boundary.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces AtlasMetricConstruction
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

local instance canonicalHorizontalGreenTensorSMul : SMul ℝ (SmoothSymmetricTwoTensor R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact canonicalHorizontalTensorSMul R

/-- Read the public TT equivalence on its actual inverse image, preserving
the full original tangent slots. No local CR argument is repeated. -/
private theorem native_tt_exists_quadratic_tensor
    (G : AtlasInducedMetric R.toRiemannSurface)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u})
    (h : SmoothSymmetricTwoTensor R) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    (∀ x : X, metricTensorTrace R G.metric h x = 0) →
    (∀ x : X, (metricTensorDivergence R G.metric hdiv h).toFun x = 0) →
      ∃ Q : HolomorphicQuadraticDifferential R.toRiemannAtlas,
        quadraticDifferentialTensor R Q = h := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  intro htrace hzero
  let TT : Type u := {k : SmoothSymmetricTwoTensor R //
    (∀ x : X, metricTensorTrace R G.metric k x = 0) ∧
      (∀ x : X, (metricTensorDivergence R G.metric hdiv k).toFun x = 0)}
  obtain ⟨E, hformula, _⟩ := exists_native_tensor_quadratic_equiv R G hdiv
  let t : TT := ⟨h, htrace, hzero⟩
  let Q : HolomorphicQuadraticDifferential R.toRiemannAtlas := E.symm t
  have hEQ : (E Q).val = h := congrArg Subtype.val (E.apply_symm_apply t)
  refine ⟨Q, ?_⟩
  apply Subtype.ext
  apply ContMDiffSection.ext
  intro x
  ext v w
  let e := chosenChart R.toRiemannSurface x
  have hx : x ∈ e.val.source := mem_chart_source ℂ x
  have hrep := hformula Q x (e.val x) (e.val.map_source hx)
  rw [hEQ] at hrep
  let P (y : X) : Prop :=
    ∀ (a b : RealSurfaceTangent R.toRiemannSurface y),
      h.val.toFun y a b =
        (Q.val x (e.val x) * originalChartDifferential R.toRiemannSurface e y a *
          originalChartDifferential R.toRiemannSurface e y b).re
  have hPy : P (e.val.symm (e.val x)) := by
    intro a b
    let y : X := e.val.symm (e.val x)
    have hy : y ∈ e.val.source := e.val.map_target (e.val.map_source hx)
    let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e y hy
    have hr := hrep a b
    change h.val.toFun y a b = (Q.val x (e.val x) * D a * D b).re at hr
    have ha : D a = originalChartDifferential R.toRiemannSurface e y a :=
      SmoothSurfaceEquiv.originalChartDifferentialEquiv_apply e y hy a
    have hb : D b = originalChartDifferential R.toRiemannSurface e y b :=
      SmoothSurfaceEquiv.originalChartDifferentialEquiv_apply e y hy b
    change h.val.toFun y a b =
      (Q.val x (e.val x) * originalChartDifferential R.toRiemannSurface e y a *
        originalChartDifferential R.toRiemannSurface e y b).re
    exact hr.trans (congrArg Complex.re
      (congrArg₂ (fun u v : ℂ => Q.val x (e.val x) * u * v) ha hb))
  have hPx : P x := (e.val.left_inv hx) ▸ hPy
  exact (quadraticDifferentialTensor_apply R Q x x hx v w).trans (hPx v w).symm

/-- Only the source's fixed factor two is needed on the actual native tensor. -/
private theorem quadraticDifferentialTensor_two
    (Q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    quadraticDifferentialTensor R ((2 : ℂ) • Q) =
      (2 : ℝ) • quadraticDifferentialTensor R Q := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  apply Subtype.ext
  apply ContMDiffSection.ext
  intro x
  ext v w
  let e := chosenChart R.toRiemannSurface x
  have hx : x ∈ e.val.source := mem_chart_source ℂ x
  change (quadraticDifferentialTensor R ((2 : ℂ) • Q)).val.toFun x v w =
    (2 : ℝ) * (quadraticDifferentialTensor R Q).val.toFun x v w
  rw [quadraticDifferentialTensor_apply R ((2 : ℂ) • Q) x x hx v w,
    quadraticDifferentialTensor_apply R Q x x hx v w]
  change ((2 : ℂ) * Q.val x (e.val x) *
      originalChartDifferential R.toRiemannSurface e x v *
      originalChartDifferential R.toRiemannSurface e x w).re =
    (2 : ℝ) * (Q.val x (e.val x) *
      originalChartDifferential R.toRiemannSurface e x v *
      originalChartDifferential R.toRiemannSurface e x w).re
  let z : ℂ := Q.val x (e.val x) *
    originalChartDifferential R.toRiemannSurface e x v *
    originalChartDifferential R.toRiemannSurface e x w
  have hm : (2 : ℂ) * Q.val x (e.val x) *
      originalChartDifferential R.toRiemannSurface e x v *
      originalChartDifferential R.toRiemannSurface e x w = (2 : ℂ) * z := by
    dsimp only [z]
    ring
  have hr : ((2 : ℂ) * z).re = (2 : ℝ) * z.re := by
    rw [Complex.mul_re]
    norm_num
  exact (congrArg Complex.re hm).trans hr

private theorem native_tt_iff_horizontal_image
    (G : AtlasInducedMetric R.toRiemannSurface)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u})
    (h : SmoothSymmetricTwoTensor R) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    ((∀ x : X, metricTensorTrace R G.metric h x = 0) ∧
      (∀ x : X, (metricTensorDivergence R G.metric hdiv h).toFun x = 0)) ↔
      h ∈ horizontalQuadraticTensors R := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  constructor
  · rintro ⟨htrace, hzero⟩
    obtain ⟨Q, hQ⟩ := native_tt_exists_quadratic_tensor R G hdiv h htrace hzero
    change ∃ P : HolomorphicQuadraticDifferential R.toRiemannAtlas,
      (2 : ℝ) • quadraticDifferentialTensor R P = h
    refine ⟨(1 / 2 : ℂ) • Q, ?_⟩
    have htwo : (2 : ℂ) • ((1 / 2 : ℂ) • Q) = Q := by
      rw [smul_smul]
      norm_num
    calc
      (2 : ℝ) • quadraticDifferentialTensor R ((1 / 2 : ℂ) • Q) =
          quadraticDifferentialTensor R ((2 : ℂ) • ((1 / 2 : ℂ) • Q)) :=
        (quadraticDifferentialTensor_two R ((1 / 2 : ℂ) • Q)).symm
      _ = quadraticDifferentialTensor R Q := congrArg (quadraticDifferentialTensor R) htwo
      _ = h := hQ
  · intro hh
    change ∃ Q : HolomorphicQuadraticDifferential R.toRiemannAtlas,
      (2 : ℝ) • quadraticDifferentialTensor R Q = h at hh
    obtain ⟨Q, hQ⟩ := hh
    have hrep : h = quadraticDifferentialTensor R ((2 : ℂ) • Q) :=
      hQ.symm.trans (quadraticDifferentialTensor_two R Q).symm
    constructor
    · intro x
      rw [hrep]
      exact metricTensorTrace_quadraticDifferentialTensor R G ((2 : ℂ) • Q) x
    · intro x
      rw [hrep]
      exact metricTensorDivergence_quadraticDifferentialTensor R G hdiv ((2 : ℂ) • Q) x

/-- For a GIVEN actual all-vector-field Lie producer with its FULL native
coordinate certificate, both orthogonalities are exactly the source2ReQ image. -/
theorem original_horizontal_orthogonality_iff
    (G : AtlasInducedMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R G.metric)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u})
    (hgreen : Unproved.Teichmuller.OriginalClosedMetricTensorGreen.{u}) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ (ℒ : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X) →
        SmoothSymmetricTwoTensor R),
      (∀ V, HasOriginalMetricLieCoordinates R G.metric V (ℒ V)) →
      ∀ h : SmoothSymmetricTwoTensor R,
        ((∀ ψ : C^∞⟮𝓘(ℝ, ℂ), X; ℝ⟯,
            metricTensorL2Pairing R G.metric harea h
              (conformalScaleLinear (R := R) G.metric ψ) = 0) ∧
          (∀ V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X),
            metricTensorL2Pairing R G.metric harea h (ℒ V) = 0)) ↔
          h ∈ horizontalQuadraticTensors R := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  dsimp only
  intro ℒ hℒ h
  have hc := metricTensorL2Pairing_conformalScale_eq_zero_iff R G.metric harea h
  have hg := metricTensorL2Pairing_lie_eq_zero_iff_divergence_zero
    R G.metric harea hdiv hgreen ℒ hℒ h
  exact (and_congr hc hg).trans (native_tt_iff_horizontal_image R G hdiv h)

end LowDimensionalTopology.Geometry.Teichmuller
