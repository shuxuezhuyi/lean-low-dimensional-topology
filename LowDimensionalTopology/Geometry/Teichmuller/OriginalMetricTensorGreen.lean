module

public import LowDimensionalTopology.Unproved.Teichmuller.OriginalClosedMetricTensorGreen
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMetricAreaFullSupport
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Original metric duals and the precise tensor Green consumer

The dual vector field remains in the original tangent bundle. Smoothness is
read in one fixed bundle chart using the inverse of its actual metric form
on the standard complex model. The scalar evaluation uses the existing Hom
bundle operation. The orthogonality result retains an actual Lie producer
and its full coordinate certificate explicitly.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Filter Set Topology MeasureTheory
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- Evaluation of a smooth original covector on a smooth original vector
field is a genuine smooth scalar on the same surface. -/
theorem contMDiff_original_covector_vectorField_apply :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ (δ : ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℝ) ∞
        (fun x : X => TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ))
      (V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X)),
      ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (fun x => δ.toFun x (V.toFun x)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change ∀ (δ : ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℝ) ∞
      (fun x : X => TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ))
    (V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X)),
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (fun x => δ.toFun x (V.toFun x))
  intro δ V x₀
  have ht := (δ.contMDiff x₀).clm_bundle_apply (V.contMDiff x₀)
  have hs := (Bundle.contMDiffAt_section x₀).mp ht
  change ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (fun x => δ.toFun x (V.toFun x)) x₀ at hs
  exact hs

/-- Every smooth original covector has a smooth vector field dual under the
given original positive metric, with equality on every original tangent slot. -/
theorem exists_original_metric_dual_smoothVectorField
    (g : SmoothSurfaceMetric R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ δ : ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℝ) ∞
        (fun x : X => TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ),
      ∃ V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X),
        ∀ (x : X) (w : TangentSpace 𝓘(ℝ, ℂ) x),
          g.inner x (V.toFun x) w = δ.toFun x w := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change ∀ δ : ContMDiffSection 𝓘(ℝ, ℂ) (ℂ →L[ℝ] ℝ) ∞
      (fun x : X => TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ),
    ∃ V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X),
      ∀ (x : X) (w : TangentSpace 𝓘(ℝ, ℂ) x),
        g.inner x (V.toFun x) w = δ.toFun x w
  intro δ
  let W : (x : X) → TangentSpace 𝓘(ℝ, ℂ) x := fun x =>
    (LinearMap.BilinForm.toDual (g.inner x).toLinearMap₁₂
      (metricForm_nondegenerate R g x)).symm (δ.toFun x).toLinearMap
  have hspec (x : X) (w : TangentSpace 𝓘(ℝ, ℂ) x) :
      g.inner x (W x) w = δ.toFun x w :=
    LinearMap.BilinForm.apply_toDual_symm_apply
      (B := (g.inner x).toLinearMap₁₂) (hB := metricForm_nondegenerate R g x)
      (δ.toFun x).toLinearMap w
  refine ⟨⟨W, ?_⟩, ?_⟩
  · intro x₀
    let : NormedAddCommGroup (ℂ →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (σ₁₂ := RingHom.id ℝ) (E := ℂ) (F := ℝ)
    let : NormedAddCommGroup (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (σ₁₂ := RingHom.id ℝ) (E := ℂ) (F := ℂ →L[ℝ] ℝ)
    let t := trivializationAt ℂ (TangentSpace 𝓘(ℝ, ℂ)) x₀
    let c := trivializationAt ℝ (fun _ : X => ℝ) x₀
    let G : X → ℂ →L[ℝ] ℂ →L[ℝ] ℝ := fun y =>
      ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℝ, ℂ))
        (ℂ →L[ℝ] ℝ) (fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ)
        x₀ y x₀ y (g.inner y)
    let B : X → ℂ →L[ℝ] ℝ := fun y =>
      ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℝ, ℂ))
        ℝ (fun _ : X => ℝ) x₀ y x₀ y (δ.toFun y)
    have hG : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞ G x₀ := by
      have hg := g.contMDiff x₀
      simp only [contMDiffAt_hom_bundle] at hg
      exact hg.2
    have hB : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℝ) ∞ B x₀ := by
      have hδ := δ.contMDiff x₀
      simp only [contMDiffAt_hom_bundle] at hδ
      exact hδ.2
    have ht₀ : x₀ ∈ t.baseSet := mem_baseSet_trivializationAt _ _ _
    have hc (y : X) : y ∈ c.baseSet := by
      have hy := mem_baseSet_trivializationAt ℝ (fun _ : X => ℝ) y
      simpa only [c, Bundle.Trivial.fiberBundle_trivializationAt'] using hy
    have hGvalue (y : X) (hy : y ∈ t.baseSet) (a b : ℂ) :
        G y a b = g.inner y (t.symmL ℝ y a) (t.symmL ℝ y b) := by
      change ContinuousLinearMap.inCoordinates ℂ (TangentSpace 𝓘(ℝ, ℂ))
        (ℂ →L[ℝ] ℝ) (fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ)
        x₀ y x₀ y (g.inner y) a b = _
      rw [inCoordinates_apply_eq₂ hy hy (hc y)]
      simp only [Bundle.Trivial.fiberBundle_trivializationAt',
        Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply,
        t.symmL_apply (R := ℝ) (F := ℂ)
          (E := fun y : X => TangentSpace 𝓘(ℝ, ℂ) y) hy]
      rfl
    have hBvalue (y : X) (hy : y ∈ t.baseSet) (a : ℂ) :
        B y a = δ.toFun y (t.symmL ℝ y a) := by
      change c.continuousLinearMapAt ℝ y (δ.toFun y (t.symmL ℝ y a)) = _
      simp only [c, Bundle.Trivial.fiberBundle_trivializationAt',
        Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]
    have hnd (y : X) (hy : y ∈ t.baseSet) : (G y).toLinearMap₁₂.Nondegenerate := by
      have hpos (a : ℂ) (ha : a ≠ 0) : 0 < G y a a := by
        rw [hGvalue y hy]
        apply g.pos y
        intro hz
        have he := congrArg (t.continuousLinearMapAt ℝ y) hz
        rw [t.continuousLinearMapAt_symmL hy, map_zero] at he
        exact ha he
      constructor
      · intro a ha
        by_contra hne
        exact (ne_of_gt (hpos a hne)) (ha a)
      · intro a ha
        by_contra hne
        exact (ne_of_gt (hpos a hne)) (ha a)
    have hInv (y : X) (hy : y ∈ t.baseSet) : (G y).IsInvertible := by
      have hinj : Function.Injective (G y) := by
        intro a b hab
        apply sub_eq_zero.mp
        apply (hnd y hy).1
        intro w
        change G y (a - b) w = 0
        rw [map_sub, sub_apply, hab, sub_self]
      have hsurj : Function.Surjective (G y) := by
        intro f
        refine ⟨(LinearMap.BilinForm.toDual (G y).toLinearMap₁₂
          (hnd y hy)).symm f.toLinearMap, ?_⟩
        ext w
        exact LinearMap.BilinForm.apply_toDual_symm_apply
          (B := (G y).toLinearMap₁₂) (hB := hnd y hy) f.toLinearMap w
      let E := ContinuousLinearEquiv.ofBijective (G y)
        (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
      exact ⟨E, ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
    have hi : ContDiffAt ℝ ∞
        (ContinuousLinearMap.inverse : (ℂ →L[ℝ] ℂ →L[ℝ] ℝ) →
          (ℂ →L[ℝ] ℝ) →L[ℝ] ℂ) (G x₀) :=
      (hInv x₀ ht₀).contDiffAt_map_inverse
    have hmodel : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
        (fun y => (G y).inverse (B y)) x₀ :=
      (hi.comp_contMDiffAt hG).clm_apply hB
    apply (Bundle.contMDiffAt_section x₀).mpr
    apply hmodel.congr_of_eventuallyEq
    filter_upwards [t.open_baseSet.mem_nhds ht₀] with y hy
    change (t ⟨y, W y⟩).2 = (G y).inverse (B y)
    rw [← Trivialization.continuousLinearMapAt_apply_of_mem ℝ t hy]
    have heq : G y (t.continuousLinearMapAt ℝ y (W y)) = B y := by
      ext b
      rw [hGvalue y hy, hBvalue y hy, t.symmL_continuousLinearMapAt hy]
      exact hspec y (t.symmL ℝ y b)
    exact ((hInv y hy).inverse_apply_eq.mpr heq.symm).symm
  · intro x w
    exact hspec x w

/-- For an actual native Lie producer with the full original coordinate
certificate, its orthogonal tensors are exactly those of zero whole divergence. -/
theorem metricTensorL2Pairing_lie_eq_zero_iff_divergence_zero
    (g : SmoothSurfaceMetric R.toRiemannSurface)
    (harea : Unproved.Teichmuller.OriginalSmoothMetricAreaMeasure R g)
    (hdiv : Unproved.Teichmuller.OriginalSmoothMetricTensorDivergence.{u})
    (hgreen : Unproved.Teichmuller.OriginalClosedMetricTensorGreen.{u}) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ∀ (ℒ : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X) →
        SmoothSymmetricTwoTensor R),
      (∀ V, HasOriginalMetricLieCoordinates R g V (ℒ V)) →
      ∀ h : SmoothSymmetricTwoTensor R,
        (∀ V : FormInterior.SmoothVectorField 𝓘(ℝ, ℂ) (M := X),
          metricTensorL2Pairing R g harea h (ℒ V) = 0) ↔
        ∀ x : X, (metricTensorDivergence R g hdiv h).toFun x = 0 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  let μ : Measure X := harea.exists.choose
  let : CompactSpace X := R.compactSpace
  let : IsFiniteMeasure μ := harea.exists.choose_spec.1
  let : Measure.IsOpenPosMeasure μ := originalMetricArea_isOpenPosMeasure R g harea
  dsimp only
  intro ℒ hℒ h
  constructor
  · intro horth
    let δ := metricTensorDivergence R g hdiv h
    obtain ⟨V, hV⟩ := exists_original_metric_dual_smoothVectorField R g δ
    have hg := hgreen X R g harea hdiv V (ℒ V) h (hℒ V)
    rw [horth V] at hg
    have hzI : (∫ x, δ.toFun x (V.toFun x) ∂μ) = 0 := by
      change 0 = -2 * (∫ x, δ.toFun x (V.toFun x) ∂μ) at hg
      linarith
    have hn (x : X) : 0 ≤ δ.toFun x (V.toFun x) := by
      rw [← hV x (V.toFun x)]
      by_cases hz : V.toFun x = 0
      · simp [hz]
      · exact (g.pos x (V.toFun x) hz).le
    have hc : Continuous (fun x => δ.toFun x (V.toFun x)) :=
      (contMDiff_original_covector_vectorField_apply R δ V).continuous
    have hi : Integrable (fun x => δ.toFun x (V.toFun x)) μ := by
      have hu : IntegrableOn (fun x => δ.toFun x (V.toFun x)) Set.univ μ :=
        ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ hc.continuousOn
      simpa only [IntegrableOn, Measure.restrict_univ] using hu
    have hae : (fun x => δ.toFun x (V.toFun x)) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg hn hi).mp hzI
    have hp : (fun x => δ.toFun x (V.toFun x)) = 0 :=
      (hc.ae_eq_iff_eq μ continuous_zero).mp hae
    intro x
    have hz : δ.toFun x (V.toFun x) = 0 := congrFun hp x
    have hVz : V.toFun x = 0 := by
      by_contra hne
      have hpos := g.pos x (V.toFun x) hne
      rw [hV x (V.toFun x)] at hpos
      exact (ne_of_gt hpos) hz
    ext w
    change δ.toFun x w = 0
    rw [← hV x w, hVz, map_zero, zero_apply]
  · intro hzero V
    rw [hgreen X R g harea hdiv V (ℒ V) h (hℒ V)]
    have hf : (fun x => (metricTensorDivergence R g hdiv h).toFun x (V.toFun x)) = 0 := by
      funext x
      exact congrArg (fun α : TangentSpace 𝓘(ℝ, ℂ) x →L[ℝ] ℝ => α (V.toFun x)) (hzero x)
    rw [hf, integral_zero' X ℝ, mul_zero]

end LowDimensionalTopology.Geometry.Teichmuller
