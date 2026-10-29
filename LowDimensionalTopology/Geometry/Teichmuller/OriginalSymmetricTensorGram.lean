module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalSymmetricTensors
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-!
# Actual original-chart coordinates of smooth symmetric tensors

The two slots are the original real tangent fibres. Coordinates use the
inverse of the actual original chart differential. Their smoothness follows
from the existing nested Hom bundle trivialization argument for metric Gram
forms, using the given tensor's smooth section instead of a positive metric.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The actual original symmetric tensor in the inverse differential frame. -/
def symmetricTensorGramForm (ξ : SmoothSymmetricTwoTensor R)
    (e : OriginalComplexChart R.toRiemannSurface) (x : X)
    (hx : x ∈ e.val.source) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv e x hx
  letI : IsNormableSpace ℝ (RealSurfaceTangent R.toRiemannSurface x) := D.isNormableSpace
  exact (ξ.val.toFun x).bilinearComp
    D.symm.toContinuousLinearMap D.symm.toContinuousLinearMap

/-- Coordinates are totalized only outside this actual original chart source. -/
def symmetricTensorGramInChart (ξ : SmoothSymmetricTwoTensor R)
    (e : OriginalComplexChart R.toRiemannSurface) (x : X) :
    ℂ →L[ℝ] ℂ →L[ℝ] ℝ := by
  classical
  exact if hx : x ∈ e.val.source then symmetricTensorGramForm R ξ e x hx else 0

@[simp]
theorem symmetricTensorGramInChart_eq (ξ : SmoothSymmetricTwoTensor R)
    (e : OriginalComplexChart R.toRiemannSurface) (x : X) (hx : x ∈ e.val.source) :
    symmetricTensorGramInChart R ξ e x = symmetricTensorGramForm R ξ e x hx := by
  classical
  simp only [symmetricTensorGramInChart, dite_eq_left hx]

/-- The actual original tensor coordinates are infinitely smooth on every
valid chart source, in that chart's genuine tangent trivialization. -/
theorem symmetricTensorGramInChart_contMDiffOn
    (ξ : SmoothSymmetricTwoTensor R) (e : OriginalComplexChart R.toRiemannSurface) :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
      (symmetricTensorGramInChart R ξ e) e.val.source := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
    (symmetricTensorGramInChart R ξ e) e.val.source
  let : ∀ y : X, IsNormableSpace ℝ (TangentSpace 𝓘(ℝ, ℂ) y) := fun y => by
    let a : OriginalComplexChart R.toRiemannSurface := ⟨chartAt ℂ y, chart_mem_atlas ℂ y⟩
    exact (SmoothSurfaceEquiv.originalChartDifferentialEquiv a y
      (mem_chart_source ℂ y)).isNormableSpace
  intro x₀ hx₀
  let t : Trivialization ℂ
      (TotalSpace.proj : TotalSpace ℂ
        (fun y : X => TangentSpace 𝓘(ℝ, ℂ) y) → X) :=
    (tangentBundleCore 𝓘(ℝ, ℂ) X).localTriv ⟨e.val, e.property⟩
  let : MemTrivializationAtlas t := ⟨⟨⟨e.val, e.property⟩, rfl⟩⟩
  let c : Trivialization ℝ
      (TotalSpace.proj : TotalSpace ℝ (fun _ : X => ℝ) → X) :=
    trivializationAt ℝ (fun _ : X => ℝ) x₀
  let h : Trivialization (ℂ →L[ℝ] ℝ)
      (TotalSpace.proj : TotalSpace (ℂ →L[ℝ] ℝ)
        (fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) → X) :=
    t.continuousLinearMap (RingHom.id ℝ) c
  let T : Trivialization (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
      (TotalSpace.proj : TotalSpace (ℂ →L[ℝ] ℂ →L[ℝ] ℝ)
        (fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ]
          TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) → X) :=
    t.continuousLinearMap (RingHom.id ℝ) h
  have ht₀ : x₀ ∈ t.baseSet := hx₀
  have hc (y : X) : y ∈ c.baseSet := by
    have hy := mem_baseSet_trivializationAt ℝ (fun _ : X => ℝ) y
    simpa only [c, Bundle.Trivial.fiberBundle_trivializationAt'] using hy
  have hT₀ : x₀ ∈ T.baseSet := ⟨ht₀, ht₀, hc x₀⟩
  have hg := (T.contMDiffAt_section_iff (IB := 𝓘(ℝ, ℂ)) (n := ∞)
    (s := fun y : X => ξ.val.toFun y) hT₀).mp (ξ.val.contMDiff x₀)
  apply ContMDiffAt.contMDiffWithinAt
  apply hg.congr_of_eventuallyEq
  filter_upwards [e.val.open_source.mem_nhds hx₀] with y hy
  rw [symmetricTensorGramInChart_eq R ξ e y hy]
  have ht : y ∈ t.baseSet := hy
  have hh : y ∈ h.baseSet := ⟨ht, hc y⟩
  let D : TangentSpace 𝓘(ℝ, ℂ) y ≃L[ℝ] ℂ :=
    SmoothSurfaceEquiv.originalChartDifferentialEquiv e y hy
  have hD : t.continuousLinearMapAt ℝ y = originalChartDifferential R.toRiemannSurface e y := by
    have hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (e.val : X → ℂ) y :=
      mdifferentiableAt_atlas (I := 𝓘(ℝ, ℂ)) e.property hy
    change
      ((tangentBundleCore 𝓘(ℝ, ℂ) X).localTriv ⟨e.val, e.property⟩).continuousLinearMapAt
        ℝ y = mvfderiv 𝓘(ℝ, ℂ) (e.val : X → ℂ) y
    rw [(tangentBundleCore 𝓘(ℝ, ℂ) X).localTriv_continuousLinearMapAt ht,
      hd.mvfderiv]
    simp only [tangentBundleCore_coordChange, writtenInExtChartAt,
      extChartAt_self_eq, extChartAt_coe, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id]
    ext v
    rfl
  have hsymm (a : ℂ) : t.symmL ℝ y a = D.symm a := by
    apply D.injective
    have ha : D (t.symmL ℝ y a) = a := by
      change originalChartDifferential R.toRiemannSurface e y (t.symmL ℝ y a) = a
      rw [← hD]
      exact t.continuousLinearMapAt_symmL ht a
    exact ha.trans (D.apply_symm_apply a).symm
  symm
  ext a b
  change (h.continuousLinearMapAt ℝ y (ξ.val.toFun y (t.symmL ℝ y a))) b =
    ξ.val.toFun y (D.symm a) (D.symm b)
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ h hh,
    Trivialization.continuousLinearMap_apply]
  change c.continuousLinearMapAt ℝ y
    (ξ.val.toFun y (t.symmL ℝ y a) (t.symmL ℝ y b)) = _
  simp only [c, Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply,
    hsymm a, hsymm b]

end LowDimensionalTopology.Geometry.Teichmuller
