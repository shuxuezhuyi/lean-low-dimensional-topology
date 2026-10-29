module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.QuotientMetric
public import LowDimensionalTopology.Geometry.Teichmuller.AtlasMetricLocalForms

/-!
# Local Poincaré densities from the original disk cover

An actual local sheet of the given hyperbolic surface cover supplies a positive
smooth scalar in any original complex chart. Its analyticity and nonzero
derivative follow from the same cover. These local densities prepare the metric
on the original surface; the global tensor and its pullback identity are separate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Hyperbolic

variable {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}

/-- The actual inverse covering coordinate expressed in an original chart. -/
def discCoverSheetCoordinate (e : OriginalComplexChart R)
    (l : OpenPartialHomeomorph extendedUnitDisc X) : OpenPartialHomeomorph ℂ ℂ :=
  (discFiniteChart.symm.trans (l.trans e.val)).symm

/-- The prescribed disk density pulled back to the original chart coordinate. -/
def discCoverSheetDensity (e : OriginalComplexChart R)
    (l : OpenPartialHomeomorph extendedUnitDisc X) (x : X) : ℝ :=
  let F := discCoverSheetCoordinate e l
  poincareLengthDensity (F (e.val x)) ^ 2 * ‖deriv F (e.val x)‖ ^ 2

/-- Analyticity of the inverse coordinate follows from the given covering. -/
theorem discCoverSheetCoordinate_analytic (M : HyperbolicSurfaceModel R)
    (e : OriginalComplexChart R) (l : OpenPartialHomeomorph extendedUnitDisc X)
    (hl : M.discCover = (l : extendedUnitDisc → X)) :
    AnalyticOnNhd ℂ (discCoverSheetCoordinate e l) (discCoverSheetCoordinate e l).source := by
  let G := discFiniteChart.symm.trans (l.trans e.val)
  have hsub : G.source ⊆ riemannChartMapDomain discFiniteChart M.discCover e.val := by
    intro t ht
    refine ⟨ht.1, ?_⟩
    change M.discCover (discFiniteChart.symm t) ∈ e.val.source
    rw [hl]
    exact ht.2.2
  have hG : AnalyticOnNhd ℂ G G.source := by
    apply AnalyticOnNhd.congr G.open_source
      ((M.discCover_analytic.2 discFiniteChart discFiniteChart_mem e.val e.property).mono hsub)
    intro t _ht
    change e.val (M.discCover (discFiniteChart.symm t)) = e.val (l (discFiniteChart.symm t))
    rw [hl]
  change AnalyticOnNhd ℂ G.symm G.target
  exact openPartialHomeomorph_analytic_inverse G hG

/-- The actual sheet gives a positive smooth scalar on the unchanged surface. -/
theorem discCoverSheetDensity_smooth_pos (M : HyperbolicSurfaceModel R)
    (e : OriginalComplexChart R) (l : OpenPartialHomeomorph extendedUnitDisc X)
    (hl : M.discCover = (l : extendedUnitDisc → X)) :
    let := R.toRiemannAtlas.toChartedSpace
    ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (discCoverSheetDensity e l) (e.val.source ∩ l.target) ∧
      ∀ x ∈ e.val.source ∩ l.target, 0 < discCoverSheetDensity e l x := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let F := discCoverSheetCoordinate e l
  have hF : AnalyticOnNhd ℂ F F.source := discCoverSheetCoordinate_analytic M e l hl
  have hmem (x : X) (hx : x ∈ e.val.source ∩ l.target) : e.val x ∈ F.source := by
    change (e.val x ∈ e.val.target ∧ e.val.symm (e.val x) ∈ l.target) ∧
      l.symm (e.val.symm (e.val x)) ∈ discFiniteChart.source
    rw [e.val.left_inv hx.1, discFiniteChart_source]
    exact ⟨⟨e.val.map_source hx.1, hx.2⟩, mem_univ _⟩
  have hdisc (x : X) (hx : x ∈ e.val.source ∩ l.target) : ‖F (e.val x)‖ < 1 := by
    have h : F (e.val x) ∈ discFiniteChart.target := (F.map_source (hmem x hx)).1
    simpa only [discFiniteChart_target, Metric.mem_ball, dist_zero_right] using h
  refine ⟨?_, ?_⟩
  · intro x hx
    have hFr : ContDiffAt ℝ ∞ F (e.val x) :=
      (hF (e.val x) (hmem x hx)).contDiffAt.restrict_scalars ℝ
    have hDr : ContDiffAt ℝ ∞ (deriv F) (e.val x) :=
      (hF (e.val x) (hmem x hx)).deriv.contDiffAt.restrict_scalars ℝ
    have hNF : ContDiffAt ℝ ∞ (fun t : ℂ => ‖F t‖ ^ 2) (e.val x) :=
      (contDiff_norm_sq ℝ).contDiffAt.comp (e.val x) hFr
    have hND : ContDiffAt ℝ ∞ (fun t : ℂ => ‖deriv F t‖ ^ 2) (e.val x) :=
      (contDiff_norm_sq ℝ).contDiffAt.comp (e.val x) hDr
    have hden : 1 - ‖F (e.val x)‖ ^ 2 ≠ 0 := by
      have hlt := hdisc x hx
      have hn := norm_nonneg (F (e.val x))
      nlinarith
    have hρ : ContDiffAt ℝ ∞ (fun t : ℂ => poincareLengthDensity (F t)) (e.val x) := by
      simpa only [poincareLengthDensity, Pi.div_def] using
        (contDiffAt_const (c := (2 : ℝ))).div (contDiffAt_const.sub hNF) hden
    have hcoord : ContDiffAt ℝ ∞
        (fun t : ℂ => poincareLengthDensity (F t) ^ 2 * ‖deriv F t‖ ^ 2) (e.val x) :=
      (hρ.pow 2).mul hND
    have heSmooth : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ e.val x :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas e.property) hx.1
    exact (hcoord.comp_contMDiffAt heSmooth).contMDiffWithinAt
  · intro x hx
    change 0 < poincareLengthDensity (F (e.val x)) ^ 2 * ‖deriv F (e.val x)‖ ^ 2
    exact mul_pos (sq_pos_of_pos (poincareLengthDensity_pos (hdisc x hx)))
      (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
        (openPartialHomeomorph_analytic_forward_deriv_ne_zero F hF (e.val x) (hmem x hx))))

/-- Every original-chart point has such a density from the same actual cover. -/
theorem exists_discCoverSheetDensity (M : HyperbolicSurfaceModel R)
    (e : OriginalComplexChart R) (x : X) (hx : x ∈ e.val.source) :
    let := R.toRiemannAtlas.toChartedSpace
    ∃ l : OpenPartialHomeomorph extendedUnitDisc X,
      M.discCover = (l : extendedUnitDisc → X) ∧ x ∈ e.val.source ∩ l.target ∧
      ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ) ∞ (discCoverSheetDensity e l) (e.val.source ∩ l.target) ∧
        ∀ y ∈ e.val.source ∩ l.target, 0 < discCoverSheetDensity e l y := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨z, hz⟩ := M.discCover_surjective x
  obtain ⟨l, hzl, hl⟩ := M.discCover_covering.isLocalHomeomorph z
  have hxl : x ∈ l.target := by
    have he : l z = x := (congrFun hl z).symm.trans hz
    exact he ▸ l.map_source hzl
  obtain ⟨hs, hp⟩ := discCoverSheetDensity_smooth_pos M e l hl
  exact ⟨l, hl, ⟨hx, hxl⟩, hs, hp⟩

end LowDimensionalTopology.Geometry.Teichmuller
