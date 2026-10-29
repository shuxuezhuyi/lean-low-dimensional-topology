module

public import LowDimensionalTopology.Geometry.Teichmuller.RawMetricGram
public import Mathlib.Geometry.Manifold.VectorBundle.Hom
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Smooth original-chart Gram entries of arbitrary surface metrics

The coordinate form is totalized by zero outside the actual chart source.
Its smoothness on that source is read from the actual original nested Hom
bundle. No compatibility of the metric with the original complex atlas is
assumed. The literal metric Beltrami coefficient is consequently smooth there.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Bundle Set
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] {R : RiemannSurface X}

/-- The actual coordinate Gram form, with an irrelevant zero totalization
outside the source of this same original chart. -/
def metricGramInChart (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R)
    (x : X) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ := by
  classical
  exact if hx : x ∈ e.val.source then metricGramForm g e x hx else 0

@[simp]
theorem metricGramInChart_eq (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R)
    (x : X) (hx : x ∈ e.val.source) :
    metricGramInChart g e x = metricGramForm g e x hx := by
  classical
  simp only [metricGramInChart, dite_eq_left hx]

/-- In any original chart, the actual metric has infinitely smooth real Gram
entries. The proof uses the chart's own genuine tangent trivialization. -/
theorem metricGramInChart_contMDiffOn
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R) :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
      (metricGramInChart g e) e.val.source := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
    (metricGramInChart g e) e.val.source
  let : ∀ y : X, IsNormableSpace ℝ (TangentSpace 𝓘(ℝ, ℂ) y) := fun y => by
    let a : OriginalComplexChart R := ⟨chartAt ℂ y, chart_mem_atlas ℂ y⟩
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
    (s := fun y : X => g.inner y) hT₀).mp (g.contMDiff x₀)
  apply ContMDiffAt.contMDiffWithinAt
  apply hg.congr_of_eventuallyEq
  filter_upwards [e.val.open_source.mem_nhds hx₀] with y hy
  rw [metricGramInChart_eq g e y hy]
  have ht : y ∈ t.baseSet := hy
  have hh : y ∈ h.baseSet := ⟨ht, hc y⟩
  let D : TangentSpace 𝓘(ℝ, ℂ) y ≃L[ℝ] ℂ :=
    SmoothSurfaceEquiv.originalChartDifferentialEquiv e y hy
  have hD : t.continuousLinearMapAt ℝ y = originalChartDifferential R e y := by
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
      change originalChartDifferential R e y (t.symmL ℝ y a) = a
      rw [← hD]
      exact t.continuousLinearMapAt_symmL ht a
    exact ha.trans (D.apply_symm_apply a).symm
  symm
  ext a b
  change (h.continuousLinearMapAt ℝ y (g.inner y (t.symmL ℝ y a))) b =
    g.inner y (D.symm a) (D.symm b)
  rw [Trivialization.continuousLinearMapAt_apply_of_mem ℝ h hh,
    Trivialization.continuousLinearMap_apply]
  change c.continuousLinearMapAt ℝ y
    (g.inner y (t.symmL ℝ y a) (t.symmL ℝ y b)) = _
  simp only [c, Bundle.Trivial.fiberBundle_trivializationAt',
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply,
    hsymm a, hsymm b]

/-- The literal E,F,G expression, totalized only outside this original chart. -/
def metricBeltramiInChart (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R)
    (x : X) : ℂ :=
  metricBeltramiFromGram (metricGramInChart g e x 1 1)
    (metricGramInChart g e x 1 Complex.I)
    (metricGramInChart g e x Complex.I Complex.I)

/-- This smooth chart function agrees with the previously constructed literal
coefficient on every valid point of the same original chart. -/
theorem metricBeltramiInChart_eq (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R)
    (x : X) (hx : x ∈ e.val.source) :
    metricBeltramiInChart g e x = metricBeltramiInOriginalChart g e x hx := by
  rw [metricBeltramiInOriginalChart_eq_gram]
  simp only [metricBeltramiInChart, metricGramInChart_eq g e x hx,
    metricGramE, metricGramF, metricGramG]

/-- Every raw smooth metric has a genuinely C∞ literal Beltrami coefficient
on every original chart source. -/
theorem metricBeltramiInChart_contMDiffOn
    (g : SmoothSurfaceMetric R) (e : OriginalComplexChart R) :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (metricBeltramiInChart g e) e.val.source := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (metricBeltramiInChart g e) e.val.source
  let E : X → ℝ := fun x => metricGramInChart g e x 1 1
  let F : X → ℝ := fun x => metricGramInChart g e x 1 Complex.I
  let G : X → ℝ := fun x => metricGramInChart g e x Complex.I Complex.I
  have hB : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℂ →L[ℝ] ℝ) ∞
      (metricGramInChart g e) e.val.source := metricGramInChart_contMDiffOn g e
  have hE : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ E e.val.source :=
    (hB.clm_apply contMDiffOn_const).clm_apply contMDiffOn_const
  have hF : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ F e.val.source :=
    (hB.clm_apply contMDiffOn_const).clm_apply contMDiffOn_const
  have hG : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ G e.val.source :=
    (hB.clm_apply contMDiffOn_const).clm_apply contMDiffOn_const
  intro x hx
  have hpos : 0 < E x ∧ 0 < G x ∧ 0 < E x * G x - F x ^ 2 := by
    simpa only [E, F, G, metricGramInChart_eq g e x hx,
      metricGramE, metricGramF, metricGramG] using metricGram_positive g e x hx
  have hΔ := (hE.mul hG).sub (hF.pow 2)
  have hs := ContDiffAt.comp_contMDiffWithinAt
    (f := fun y : X => E y * G y - F y ^ 2) (x := x)
    (Real.contDiffAt_sqrt hpos.2.2.ne') (hΔ x hx)
  have hden : ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞
      (fun y => E y + G y + 2 * Real.sqrt (E y * G y - F y ^ 2)) e.val.source x :=
    ((hE.add hG) x hx).add ((contMDiffWithinAt_const (c := (2 : ℝ))).mul hs)
  have hdenpos : 0 < E x + G x + 2 * Real.sqrt (E x * G x - F x ^ 2) :=
    add_pos (add_pos hpos.1 hpos.2.1)
      (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.sqrt_pos.mpr hpos.2.2))
  have hnum : ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
      (fun y => ((E y - G y : ℝ) : ℂ) + 2 * Complex.I * (F y : ℂ)) e.val.source x :=
    (Complex.ofRealCLM.contDiff.comp_contMDiffWithinAt ((hE.sub hG) x hx)).add
      ((ContinuousLinearMap.mul ℝ ℂ (2 * Complex.I)).contDiff.comp_contMDiffWithinAt
        (Complex.ofRealCLM.contDiff.comp_contMDiffWithinAt (hF x hx)))
  have hinv := ContDiffAt.comp_contMDiffWithinAt
    (f := fun y : X =>
      ((E y + G y + 2 * Real.sqrt (E y * G y - F y ^ 2) : ℝ) : ℂ)) (x := x)
    (contDiffAt_inv ℝ (Complex.ofReal_ne_zero.mpr hdenpos.ne'))
    (Complex.ofRealCLM.contDiff.comp_contMDiffWithinAt hden)
  change ContMDiffWithinAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞
    (fun y => (((E y - G y : ℝ) : ℂ) + 2 * Complex.I * (F y : ℂ)) /
      ((E y + G y + 2 * Real.sqrt (E y * G y - F y ^ 2) : ℝ) : ℂ)) e.val.source x
  simpa only [Function.comp_apply, div_eq_mul_inv, ContinuousLinearMap.mul_apply'] using
    ((ContinuousLinearMap.mul ℝ ℂ).contDiff.comp_contMDiffWithinAt hnum).clm_apply hinv

end LowDimensionalTopology.Geometry.Teichmuller
