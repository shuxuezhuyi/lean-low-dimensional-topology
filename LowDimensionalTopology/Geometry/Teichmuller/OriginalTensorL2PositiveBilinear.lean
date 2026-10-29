module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalTensorL2Integrability
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalTensorPointwisePositive
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricAreaFullSupport

/-!
# Positive symmetric bilinearity of the original tensor integral

Raising an index is linear in the original tensor. Ordinary trace and the
same finite metric-area integral preserve that linearity. The positive-area
support and continuity upgrade zero self-contraction almost everywhere to
the whole original smooth symmetric section being zero.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open MeasureTheory
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The real scalar action already inherited from the same native symmetric-tensor submodule. -/
local instance canonicalNativeL2TensorSMul : SMul ℝ (SmoothSymmetricTwoTensor R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact Submodule.smul (symmetricTwoTensorSubmodule R)

/-- The real module already inherited from the same native symmetric-tensor submodule. -/
local instance canonicalNativeS2Module : Module ℝ (SmoothSymmetricTwoTensor R) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact Submodule.module (symmetricTwoTensorSubmodule R)

private theorem raised_add (g : SmoothSurfaceMetric R.toRiemannSurface)
    (h k : SmoothSymmetricTwoTensor R) (x : X) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    metricRaisedTensor R g (h + k) x =
      metricRaisedTensor R g h x + metricRaisedTensor R g k x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let V := TangentSpace 𝓘(ℝ, ℂ) x
  let gB : LinearMap.BilinForm ℝ V := (g.inner x).toLinearMap₁₂
  let A : Module.Dual ℝ V →ₗ[ℝ] V :=
    (gB.toDual (metricForm_nondegenerate R g x)).symm.toLinearMap
  change A.comp ((h + k).val.toFun x).toLinearMap₁₂ =
    A.comp (h.val.toFun x).toLinearMap₁₂ + A.comp (k.val.toFun x).toLinearMap₁₂
  have hv : (h + k).val.toFun x = h.val.toFun x + k.val.toFun x := rfl
  rw [hv, map_add, LinearMap.comp_add]

private theorem raised_smul (g : SmoothSurfaceMetric R.toRiemannSurface)
    (c : ℝ) (h : SmoothSymmetricTwoTensor R) (x : X) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    metricRaisedTensor R g (c • h : SmoothSymmetricTwoTensor R) x = c • metricRaisedTensor R g h x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let V := TangentSpace 𝓘(ℝ, ℂ) x
  let gB : LinearMap.BilinForm ℝ V := (g.inner x).toLinearMap₁₂
  let A : Module.Dual ℝ V →ₗ[ℝ] V :=
    (gB.toDual (metricForm_nondegenerate R g x)).symm.toLinearMap
  change A.comp ((c • h : SmoothSymmetricTwoTensor R).val.toFun x).toLinearMap₁₂ =
    c • A.comp (h.val.toFun x).toLinearMap₁₂
  have hv : (c • h : SmoothSymmetricTwoTensor R).val.toFun x = c • h.val.toFun x := rfl
  rw [hv, map_smul, LinearMap.comp_smul]

private theorem pointwise_add_left (g : SmoothSurfaceMetric R.toRiemannSurface)
    (h k l : SmoothSymmetricTwoTensor R) (x : X) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    metricTensorPointwisePairing R g (h + k) l x =
      metricTensorPointwisePairing R g h l x + metricTensorPointwisePairing R g k l x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let V := TangentSpace 𝓘(ℝ, ℂ) x
  change LinearMap.trace ℝ V
      ((metricRaisedTensor R g (h + k) x).comp (metricRaisedTensor R g l x)) =
    LinearMap.trace ℝ V ((metricRaisedTensor R g h x).comp (metricRaisedTensor R g l x)) +
      LinearMap.trace ℝ V ((metricRaisedTensor R g k x).comp (metricRaisedTensor R g l x))
  rw [raised_add, LinearMap.add_comp, map_add]

private theorem pointwise_smul_left (g : SmoothSurfaceMetric R.toRiemannSurface)
    (c : ℝ) (h k : SmoothSymmetricTwoTensor R) (x : X) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    metricTensorPointwisePairing R g (c • h : SmoothSymmetricTwoTensor R) k x =
      c * metricTensorPointwisePairing R g h k x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let V := TangentSpace 𝓘(ℝ, ℂ) x
  change LinearMap.trace ℝ V
      ((metricRaisedTensor R g (c • h : SmoothSymmetricTwoTensor R) x).comp (metricRaisedTensor R g k x)) =
    c * LinearMap.trace ℝ V ((metricRaisedTensor R g h x).comp (metricRaisedTensor R g k x))
  rw [raised_smul, LinearMap.smul_comp]
  simpa only [smul_eq_mul] using
    (map_smul (LinearMap.trace ℝ V) c
      ((metricRaisedTensor R g h x).comp (metricRaisedTensor R g k x)))

/-- The same original contraction integral on all smooth symmetric tensors
is a positive symmetric real bilinear form, with whole-section nondegeneracy. -/
theorem exists_metricTensorL2BilinForm
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R g) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isRealManifold
    ∃ B : LinearMap.BilinForm ℝ (SmoothSymmetricTwoTensor R),
      (∀ h k : SmoothSymmetricTwoTensor R,
        B h k = metricTensorL2Pairing R g harea h k) ∧
      (∀ h k : SmoothSymmetricTwoTensor R, B h k = B k h) ∧
      (∀ h : SmoothSymmetricTwoTensor R, 0 ≤ B h h) ∧
      (∀ h : SmoothSymmetricTwoTensor R, B h h = 0 ↔ h = 0) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let μ : Measure X := harea.exists.choose
  let : Measure.IsOpenPosMeasure μ := originalMetricArea_isOpenPosMeasure R g harea
  let F : SmoothSymmetricTwoTensor R → SmoothSymmetricTwoTensor R → ℝ :=
    metricTensorL2Pairing R g harea
  have hi (h k : SmoothSymmetricTwoTensor R) :
      Integrable (metricTensorPointwisePairing R g h k) μ :=
    integrable_metricTensorPointwisePairing R g harea h k
  have ha (h k l : SmoothSymmetricTwoTensor R) : F (h + k) l = F h l + F k l := by
    change (∫ x, metricTensorPointwisePairing R g (h + k) l x ∂μ) =
      (∫ x, metricTensorPointwisePairing R g h l x ∂μ) +
        (∫ x, metricTensorPointwisePairing R g k l x ∂μ)
    have hp : metricTensorPointwisePairing R g (h + k) l =
        fun x => metricTensorPointwisePairing R g h l x +
          metricTensorPointwisePairing R g k l x :=
      funext (fun x => pointwise_add_left R g h k l x)
    rw [hp]
    exact integral_add (hi h l) (hi k l)
  have hs (c : ℝ) (h k : SmoothSymmetricTwoTensor R) : F (c • h : SmoothSymmetricTwoTensor R) k = c * F h k := by
    change (∫ x, metricTensorPointwisePairing R g (c • h : SmoothSymmetricTwoTensor R) k x ∂μ) =
      c * (∫ x, metricTensorPointwisePairing R g h k x ∂μ)
    have hp : metricTensorPointwisePairing R g (c • h : SmoothSymmetricTwoTensor R) k =
        fun x => c * metricTensorPointwisePairing R g h k x :=
      funext (fun x => pointwise_smul_left R g c h k x)
    rw [hp]
    exact integral_const_mul c _
  have hsym (h k : SmoothSymmetricTwoTensor R) : F h k = F k h := by
    change (∫ x, metricTensorPointwisePairing R g h k x ∂μ) =
      ∫ x, metricTensorPointwisePairing R g k h x ∂μ
    exact integral_congr_ae (Filter.Eventually.of_forall
      (fun x => metricTensorPointwisePairing_symm R g h k x))
  let B : LinearMap.BilinForm ℝ (SmoothSymmetricTwoTensor R) :=
    { toFun := fun h =>
        { toFun := fun k => F h k
          map_add' := fun k l => by
            rw [hsym h (k + l), ha k l h, hsym k h, hsym l h]
          map_smul' := fun c k => by
            change F h (c • k : SmoothSymmetricTwoTensor R) = c * F h k
            rw [hsym h (c • k : SmoothSymmetricTwoTensor R), hs c k h, hsym k h] }
      map_add' := fun h k => by
        ext l
        exact ha h k l
      map_smul' := fun c h => by
        ext k
        change F (c • h : SmoothSymmetricTwoTensor R) k = c * F h k
        exact hs c h k }
  refine ⟨B, ?_, ?_, ?_, ?_⟩
  · intro h k
    rfl
  · intro h k
    exact hsym h k
  · intro h
    change 0 ≤ ∫ x, metricTensorPointwisePairing R g h h x ∂μ
    exact integral_nonneg (fun x => metricTensorPointwisePairing_self_nonneg R g h x)
  · intro h
    constructor
    · intro hz
      have hzI : (∫ x, metricTensorPointwisePairing R g h h x ∂μ) = 0 := hz
      have hn (x : X) : 0 ≤ metricTensorPointwisePairing R g h h x :=
        metricTensorPointwisePairing_self_nonneg R g h x
      have hae : metricTensorPointwisePairing R g h h =ᵐ[μ] 0 :=
        (integral_eq_zero_iff_of_nonneg hn (hi h h)).mp hzI
      have hc := continuous_metricTensorPointwisePairing R g h h
      have hpoint : metricTensorPointwisePairing R g h h = 0 :=
        (hc.ae_eq_iff_eq μ continuous_zero).mp hae
      apply Subtype.ext
      apply ContMDiffSection.ext
      intro x
      change h.val.toFun x = 0
      exact (metricTensorPointwisePairing_self_eq_zero_iff R g h x).mp
        (congrFun hpoint x)
    · intro hz
      subst h
      exact map_zero (B 0)

end LowDimensionalTopology.Geometry.Teichmuller
