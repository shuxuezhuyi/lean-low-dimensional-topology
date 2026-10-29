module

public import LowDimensionalTopology.Geometry.Teichmuller.BeltramiDifferential
public import LowDimensionalTopology.Geometry.Teichmuller.ConformalSmooth
public import LowDimensionalTopology.External.LiZhongQC.Ch01.S06_C1Quasiconformal
public import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# Beltrami differentials of smooth oriented surface equivalences

Its coefficients are actual ratios
of the two Wirtinger derivatives in the original complex charts. Target-chart
independence and the source-chart tensor law reuse Wu Xiaobin's LiZhongQC
Wirtinger chain rules (eq6_4 and eq6_5), fixed upstream commit
1c0d5473c020b66ed5106331a38a61536760b9b2, original file
LiZhongQC/Ch01/S06_C1Quasiconformal.lean. The derivative hypotheses are proved
from the actual smooth map; no quasiconformality assumption is used. This file
imports only the earlier plane C¹ material, without S22, Riemann–Roch or S23.

The target chart is allowed to vary with the point only when defining a ratio.
The ratio is then proved locally equal to the expression in any single target
chart covering the image. This is what proves continuity of the chart family.
-/

@[expose] public section

noncomputable section

open Set Topology
open scoped ComplexConjugate ContDiff Manifold

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
open LiZhongQC (complexDilatation dz dzbar)

universe u v

section TargetCoordinates

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Changing only the target complex chart does not change the Wirtinger ratio.
The real differentiability premise is supplied by a smooth coordinate map in
the application, and the transition derivative is nonzero by the original atlas. -/
theorem chartDilatation_target_eq
    (B : RiemannAtlas Y) (f : X → Y) (hf : Continuous f)
    (e : OpenPartialHomeomorph X ℂ) (g h : OpenPartialHomeomorph Y ℂ)
    (hg : g ∈ B.charts) (hh : h ∈ B.charts) {z : ℂ}
    (hzg : z ∈ riemannChartMapDomain e f g)
    (hzh : z ∈ riemannChartMapDomain e f h)
    (hfd : DifferentiableAt ℝ (riemannChartMap e f g) z) :
    complexDilatation (riemannChartMap e f g) z =
      complexDilatation (riemannChartMap e f h) z := by
  let F : ℂ → ℂ := riemannChartMap e f g
  let T : OpenPartialHomeomorph ℂ ℂ := g.symm.trans h
  have hzT : F z ∈ T.source := by
    refine ⟨g.map_source hzg.2, ?_⟩
    change g.symm (g (f (e.symm z))) ∈ h.source
    rw [g.left_inv hzg.2]
    exact hzh.2
  have hT : AnalyticOnNhd ℂ T T.source := B.compatible g hg h hh
  have hEq : riemannChartMap e f h =ᶠ[𝓝 z] T ∘ F := by
    filter_upwards [(riemannChartMapDomain_isOpen e f g hf).mem_nhds hzg] with w hw
    change h (f (e.symm w)) = h (g.symm (g (f (e.symm w))))
    rw [g.left_inv hw.2]
  have hratio : complexDilatation (riemannChartMap e f h) z =
      complexDilatation (T ∘ F) z := by
    simp only [complexDilatation, dz, dzbar, hEq.fderiv_eq]
  rw [hratio]
  exact (LiZhongQC.complexDilatation_comp_conformal_left hfd
    (hT (F z) hzT).differentiableAt
    (B.transition_deriv_ne_zero g h hg hh (F z) hzT)).symm

end TargetCoordinates

namespace SmoothSurfaceEquiv

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {R : RiemannSurface X} {S : RiemannSurface Y}

/-- A native real smooth map is C¹ in every pair of actual original charts,
including charts not chosen by the atlas's `chartAt` function. -/
theorem chartMap_contDiffOn_real
    (f : SmoothSurfaceEquiv R S)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ R.charts)
    (g : OpenPartialHomeomorph Y ℂ) (hg : g ∈ S.charts) :
    ContDiffOn ℝ 1 (riemannChartMap e f.toHomeomorph g)
      (riemannChartMapDomain e f.toHomeomorph g) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := S.toRiemannAtlas.isRealManifold
  have heMax : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ X :=
    IsManifold.subset_maximalAtlas he
  have hgMax : g ∈ IsManifold.maximalAtlas 𝓘(ℝ, ℂ) ∞ Y :=
    IsManifold.subset_maximalAtlas hg
  have hreal : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ f.toHomeomorph :=
    f.contMDiff_toFun
  intro z hz
  have h := ((contMDiffAt_iff_of_mem_maximalAtlas heMax hgMax
    (e.map_target hz.1) hz.2).1 (hreal.contMDiffAt (x := e.symm z))).2
  have hc : ContDiffAt ℝ ∞ (riemannChartMap e f.toHomeomorph g) z := by
    simpa only [OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
      Set.range_id, contDiffWithinAt_univ, riemannChartMap,
      e.right_inv hz.1] using h
  exact (hc.of_le (by simp)).contDiffWithinAt

/-- The actual positive real determinant implies the strict Wirtinger inequality. -/
theorem chartMap_wirtinger_lt
    (f : SmoothSurfaceEquiv R S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ R.charts)
    (g : OpenPartialHomeomorph Y ℂ) (hg : g ∈ S.charts)
    {z : ℂ} (hz : z ∈ riemannChartMapDomain e f.toHomeomorph g) :
    ‖dzbar (riemannChartMap e f.toHomeomorph g) z‖ <
      ‖dz (riemannChartMap e f.toHomeomorph g) z‖ := by
  have hD := riemannChartMapDomain_isOpen e f.toHomeomorph g f.toHomeomorph.continuous
  have hd : DifferentiableAt ℝ (riemannChartMap e f.toHomeomorph g) z :=
    ((f.chartMap_contDiffOn_real e he g hg).differentiableOn one_ne_zero).differentiableAt
      (hD.mem_nhds hz)
  have hJ := hf e he g hg z hz
  change 0 < LinearMap.det
    (fderiv ℝ (riemannChartMap e f.toHomeomorph g) z : ℂ →ₗ[ℝ] ℂ) at hJ
  rw [LiZhongQC.det_fderiv_eq_jacobian hd] at hJ
  unfold LiZhongQC.jacobian at hJ
  nlinarith [norm_nonneg (dzbar (riemannChartMap e f.toHomeomorph g) z),
    norm_nonneg (dz (riemannChartMap e f.toHomeomorph g) z)]

/-- The coefficient ratio is continuous on every actual fixed-chart domain. -/
theorem continuousOn_chartDilatation
    (f : SmoothSurfaceEquiv R S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (e : OpenPartialHomeomorph X ℂ) (he : e ∈ R.charts)
    (g : OpenPartialHomeomorph Y ℂ) (hg : g ∈ S.charts) :
    ContinuousOn (complexDilatation (riemannChartMap e f.toHomeomorph g))
      (riemannChartMapDomain e f.toHomeomorph g) := by
  let F : ℂ → ℂ := riemannChartMap e f.toHomeomorph g
  let D : Set ℂ := riemannChartMapDomain e f.toHomeomorph g
  have hD : IsOpen D :=
    riemannChartMapDomain_isOpen e f.toHomeomorph g f.toHomeomorph.continuous
  have hC1 : ContDiffOn ℝ 1 F D := f.chartMap_contDiffOn_real e he g hg
  have hfd : ContinuousOn (fderiv ℝ F) D :=
    hC1.continuousOn_fderiv_of_isOpen hD le_rfl
  have hdzc : ContinuousOn (dz F) D := by
    unfold dz
    exact (((hfd.clm_apply continuousOn_const).sub
      (continuousOn_const.mul (hfd.clm_apply continuousOn_const))).div_const _)
  have hdzbarc : ContinuousOn (dzbar F) D := by
    unfold dzbar
    exact (((hfd.clm_apply continuousOn_const).add
      (continuousOn_const.mul (hfd.clm_apply continuousOn_const))).div_const _)
  have hdz0 : ∀ z ∈ D, dz F z ≠ 0 := by
    intro z hz hzero
    have hlt := f.chartMap_wirtinger_lt hf e he g hg hz
    change ‖dzbar F z‖ < ‖dz F z‖ at hlt
    rw [hzero, norm_zero] at hlt
    exact (norm_nonneg _).not_gt hlt
  exact hdzbarc.div hdzc hdz0

/-- Choose an actual target chart only to define the raw pointwise coefficient. -/
def targetChart (S : RiemannSurface Y) (y : Y) :
    BeltramiDifferential.Chart S.toRiemannAtlas :=
  ⟨(S.cover y).choose, (S.cover y).choose_spec.1⟩

private theorem mem_targetChart_source (S : RiemannSurface Y) (y : Y) :
    y ∈ (targetChart S y).val.source :=
  (S.cover y).choose_spec.2

/-- The coefficient in an actual source chart, using any chart at the image point.
Only its values on the source chart's target will be used. -/
def rawBeltramiCoefficient (f : SmoothSurfaceEquiv R S)
    (e : BeltramiDifferential.Chart R.toRiemannAtlas) (z : ℂ) : ℂ :=
  let g := targetChart S (f.toHomeomorph (e.val.symm z))
  complexDilatation (riemannChartMap e.val f.toHomeomorph g.val) z

/-- Every target chart covering the actual image point gives the same coefficient. -/
theorem rawBeltramiCoefficient_eq_chartDilatation
    (f : SmoothSurfaceEquiv R S)
    (e : BeltramiDifferential.Chart R.toRiemannAtlas) {z : ℂ} (hz : z ∈ e.val.target)
    (g : OpenPartialHomeomorph Y ℂ) (hg : g ∈ S.charts)
    (hgz : f.toHomeomorph (e.val.symm z) ∈ g.source) :
    f.rawBeltramiCoefficient e z =
      complexDilatation (riemannChartMap e.val f.toHomeomorph g) z := by
  let g₀ := targetChart S (f.toHomeomorph (e.val.symm z))
  have hz₀ : z ∈ riemannChartMapDomain e.val f.toHomeomorph g₀.val :=
    ⟨hz, mem_targetChart_source S _⟩
  have hD := riemannChartMapDomain_isOpen e.val f.toHomeomorph g₀.val
    f.toHomeomorph.continuous
  have hfd : DifferentiableAt ℝ (riemannChartMap e.val f.toHomeomorph g₀.val) z :=
    ((f.chartMap_contDiffOn_real e.val e.property g₀.val g₀.property).differentiableOn
      one_ne_zero).differentiableAt (hD.mem_nhds hz₀)
  exact chartDilatation_target_eq S.toRiemannAtlas f.toHomeomorph
    f.toHomeomorph.continuous e.val g₀.val g g₀.property hg hz₀ ⟨hz, hgz⟩ hfd

/-- Although the chosen target chart can vary discontinuously, its ratio agrees
locally with one fixed chart ratio, and hence is continuous on the source target. -/
theorem continuousOn_rawBeltramiCoefficient
    (f : SmoothSurfaceEquiv R S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (e : BeltramiDifferential.Chart R.toRiemannAtlas) :
    ContinuousOn (f.rawBeltramiCoefficient e) e.val.target := by
  intro z hz
  let g := targetChart S (f.toHomeomorph (e.val.symm z))
  have hzD : z ∈ riemannChartMapDomain e.val f.toHomeomorph g.val :=
    ⟨hz, mem_targetChart_source S _⟩
  have hD := riemannChartMapDomain_isOpen e.val f.toHomeomorph g.val
    f.toHomeomorph.continuous
  have hμ := f.continuousOn_chartDilatation hf e.val e.property g.val g.property
  have hEq : f.rawBeltramiCoefficient e =ᶠ[𝓝 z]
      complexDilatation (riemannChartMap e.val f.toHomeomorph g.val) := by
    filter_upwards [hD.mem_nhds hzD] with w hw
    exact f.rawBeltramiCoefficient_eq_chartDilatation e hw.1 g.val g.property hw.2
  exact ((hμ.continuousAt (hD.mem_nhds hzD)).congr_of_eventuallyEq hEq).continuousWithinAt

/-- A genuine continuous coefficient on every actual original source chart target. -/
def continuousBeltramiCoefficient
    (f : SmoothSurfaceEquiv R S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (e : BeltramiDifferential.Chart R.toRiemannAtlas) : C(e.val.target, ℂ) :=
  ⟨fun z => f.rawBeltramiCoefficient e z.val,
    continuousOn_iff_continuous_domRestrict.mp (f.continuousOn_rawBeltramiCoefficient hf e)⟩

/-- The exact (-1,1) law in any two actual original source charts. -/
theorem rawBeltramiCoefficient_source_change
    (f : SmoothSurfaceEquiv R S)
    (e e' : BeltramiDifferential.Chart R.toRiemannAtlas)
    (x : X) (hxe : x ∈ e.val.source) (hxe' : x ∈ e'.val.source) :
    f.rawBeltramiCoefficient e (e.val x) =
      f.rawBeltramiCoefficient e' (e'.val x) *
        conj (deriv (e.val.symm.trans e'.val) (e.val x)) /
          deriv (e.val.symm.trans e'.val) (e.val x) := by
  let g := targetChart S (f.toHomeomorph x)
  let T : OpenPartialHomeomorph ℂ ℂ := e.val.symm.trans e'.val
  let F : ℂ → ℂ := riemannChartMap e'.val f.toHomeomorph g.val
  have hxg : f.toHomeomorph x ∈ g.val.source := mem_targetChart_source S _
  have hzT : e.val x ∈ T.source := by
    refine ⟨e.val.map_source hxe, ?_⟩
    change e.val.symm (e.val x) ∈ e'.val.source
    rwa [e.val.left_inv hxe]
  have hT : AnalyticOnNhd ℂ T T.source :=
    R.compatible e.val e.property e'.val e'.property
  have hEq : riemannChartMap e.val f.toHomeomorph g.val =ᶠ[𝓝 (e.val x)] F ∘ T := by
    filter_upwards [T.open_source.mem_nhds hzT] with w hw
    change g.val (f.toHomeomorph (e.val.symm w)) =
      g.val (f.toHomeomorph (e'.val.symm (e'.val (e.val.symm w))))
    have hwe : e.val.symm w ∈ e'.val.source := hw.2
    have hinv : e'.val.symm (e'.val (e.val.symm w)) = e.val.symm w :=
      e'.val.left_inv hwe
    rw [hinv]
  have hratio : complexDilatation (riemannChartMap e.val f.toHomeomorph g.val) (e.val x) =
      complexDilatation (F ∘ T) (e.val x) := by
    simp only [complexDilatation, dz, dzbar, hEq.fderiv_eq]
  have hTe : T (e.val x) = e'.val x := by
    change e'.val (e.val.symm (e.val x)) = e'.val x
    rw [e.val.left_inv hxe]
  have hzF : e'.val x ∈ riemannChartMapDomain e'.val f.toHomeomorph g.val := by
    refine ⟨e'.val.map_source hxe', ?_⟩
    change f.toHomeomorph (e'.val.symm (e'.val x)) ∈ g.val.source
    rwa [e'.val.left_inv hxe']
  have hDF := riemannChartMapDomain_isOpen e'.val f.toHomeomorph g.val
    f.toHomeomorph.continuous
  have hFd : DifferentiableAt ℝ F (T (e.val x)) := by
    rw [hTe]
    exact ((f.chartMap_contDiffOn_real e'.val e'.property g.val g.property).differentiableOn
      one_ne_zero).differentiableAt (hDF.mem_nhds hzF)
  have hpre := LiZhongQC.complexDilatation_comp_conformal_right
    (g := F) (hT (e.val x) hzT).differentiableAt
    (R.toRiemannAtlas.transition_deriv_ne_zero e.val e'.val e.property e'.property
      (e.val x) hzT) hFd
  have hμe := f.rawBeltramiCoefficient_eq_chartDilatation e
    (e.val.map_source hxe) g.val g.property (by rwa [e.val.left_inv hxe])
  have hμe' := f.rawBeltramiCoefficient_eq_chartDilatation e'
    (e'.val.map_source hxe') g.val g.property (by rwa [e'.val.left_inv hxe'])
  rw [hμe, hμe', hratio, hpre, hTe]
  change complexDilatation F (e'.val x) *
      (conj (deriv T (e.val x)) / deriv T (e.val x)) =
    complexDilatation F (e'.val x) * conj (deriv T (e.val x)) / deriv T (e.val x)
  ring

/-- The continuous Beltrami tensor of a real smooth orientation-preserving surface
map, with the original atlas's actual transformation law proved above. -/
def beltrami
    (f : SmoothSurfaceEquiv R S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph) :
    BeltramiDifferential R.toRiemannAtlas := by
  refine ⟨fun e => f.continuousBeltramiCoefficient hf e, ?_⟩
  intro e e' x hxe hxe'
  exact f.rawBeltramiCoefficient_source_change e e' x hxe hxe'

/-- An arbitrary target chart computes the coefficient of the actual tensor. -/
theorem beltrami_coeff_eq_chartDilatation
    (f : SmoothSurfaceEquiv R S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (e : BeltramiDifferential.Chart R.toRiemannAtlas) (z : e.val.target)
    (g : OpenPartialHomeomorph Y ℂ) (hg : g ∈ S.charts)
    (hgz : f.toHomeomorph (e.val.symm z.val) ∈ g.source) :
    (f.beltrami hf).coeff e z =
      complexDilatation (riemannChartMap e.val f.toHomeomorph g) z.val :=
  f.rawBeltramiCoefficient_eq_chartDilatation e z.property g hg hgz

/-- The actual positive Jacobian makes every tensor coefficient have norm below one. -/
theorem beltrami_coeff_norm_lt_one
    (f : SmoothSurfaceEquiv R S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (e : BeltramiDifferential.Chart R.toRiemannAtlas) (z : e.val.target) :
    ‖(f.beltrami hf).coeff e z‖ < 1 := by
  let g := targetChart S (f.toHomeomorph (e.val.symm z.val))
  have hzD : z.val ∈ riemannChartMapDomain e.val f.toHomeomorph g.val :=
    ⟨z.property, mem_targetChart_source S _⟩
  rw [f.beltrami_coeff_eq_chartDilatation hf e z g.val g.property hzD.2]
  have hlt := f.chartMap_wirtinger_lt hf e.val e.property g.val g.property hzD
  have hdzpos : 0 < ‖dz (riemannChartMap e.val f.toHomeomorph g.val) z.val‖ :=
    lt_of_le_of_lt (norm_nonneg _) hlt
  rw [complexDilatation, norm_div, div_lt_one hdzpos]
  exact hlt

/-- The tensor's intrinsic pointwise norm is everywhere strictly below one. -/
theorem beltrami_abs_lt_one
    (f : SmoothSurfaceEquiv R S)
    (hf : PreservesComplexOrientation R.toRiemannAtlas S.toRiemannAtlas f.toHomeomorph)
    (x : X) : (f.beltrami hf).abs x < 1 := by
  obtain ⟨e, he, hx⟩ := R.cover x
  rw [BeltramiDifferential.abs_eq_coeff _ ⟨e, he⟩ x hx]
  exact f.beltrami_coeff_norm_lt_one hf ⟨e, he⟩ ⟨e x, e.map_source hx⟩

end SmoothSurfaceEquiv

end LowDimensionalTopology.Geometry.Teichmuller
