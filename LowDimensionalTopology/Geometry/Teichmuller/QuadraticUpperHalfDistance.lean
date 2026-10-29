module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticPiecewiseSmoothDistance
public import LowDimensionalTopology.Geometry.Teichmuller.DECoverDescent

/-! Quadratic distance between fixed endpoints in the original upper half-plane. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory Topology
open scoped UpperHalfPlane ENNReal NNReal ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

private theorem upperHalf_native_chart (x : ℍ) :
    let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
    chartAt ℂ x = UpperHalfPlane.ofComplex.symm := by
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  have h := chart_mem_atlas ℂ x
  change chartAt ℂ x ∈ ({UpperHalfPlane.ofComplex.symm} :
    Set (OpenPartialHomeomorph ℍ ℂ)) at h
  exact Set.mem_singleton_iff.mp h

/-- A holomorphic coefficient on H, in the same native H atlas and zero off its chart target. -/
def upperHalfNativeQuadratic (φ : ℂ → ℂ) (hφ : DifferentiableOn ℂ φ upperHalf) :
    HolomorphicQuadraticDifferential upperHalfNativeSurface.toRiemannAtlas := by
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  have hq : IsHolQuadDiff (fun (_ : ℍ) z => upperHalf.indicator φ z) := by
    have hchart (x : ℍ) : chartAt ℂ x = UpperHalfPlane.ofComplex.symm := by
      have hc := chart_mem_atlas ℂ x
      change chartAt ℂ x ∈ ({UpperHalfPlane.ofComplex.symm} :
        Set (OpenPartialHomeomorph ℍ ℂ)) at hc
      exact Set.mem_singleton_iff.mp hc
    have htarget (x : ℍ) : (chartAt ℂ x).target = upperHalf := by
      rw [hchart x]
      change (UpperHalfPlane.isOpenEmbedding_coe.toOpenPartialHomeomorph UpperHalfPlane.coe).target = _
      rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, UpperHalfPlane.range_coe]
      rfl
    have htransition (x y : ℍ) (z : ℂ) (hz : z ∈ upperHalf) :
        chartTransition x y z = z := by
      change chartAt ℂ x ((chartAt ℂ y).symm z) = z
      rw [hchart x, hchart y]
      change (UpperHalfPlane.ofComplex z : ℂ) = z
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos hz]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro x z hz
      rw [htarget x] at hz
      exact Set.indicator_of_notMem hz _
    · intro x y z hz _
      rw [htarget y] at hz
      have hd : deriv (chartTransition x y) z = 1 := by
        have he : chartTransition x y =ᶠ[𝓝 z] id :=
          Filter.eventually_of_mem (isOpen_upperHalf.mem_nhds hz)
            fun w hw => htransition x y w hw
        rw [he.deriv_eq, deriv_id]
      rw [hd, htransition x y z hz]
      simp
    · intro x
      rw [htarget x]
      exact hφ.congr fun z hz => Set.indicator_of_mem hz _
  exact ⟨fun _ z => upperHalf.indicator φ z, hq⟩

/-- The existing smooth-path infimum specialized to two fixed original H endpoints. -/
abbrev upperHalfPiecewiseSmoothQuadraticDistance (φ : ℂ → ℂ)
    (hφ : DifferentiableOn ℂ φ upperHalf) (a b : ℍ) : ℝ≥0∞ :=
  piecewiseSmoothQuadraticDistance upperHalfNativeSurface (upperHalfNativeQuadratic φ hφ) a b

/-- The same fixed-endpoint distance is the literal infimum of the original H coefficient integrals. -/
theorem upperHalfPiecewiseSmoothQuadraticDistance_eq_iInf_integral (φ : ℂ → ℂ)
    (hφ : DifferentiableOn ℂ φ upperHalf) (a b : ℍ) :
    upperHalfPiecewiseSmoothQuadraticDistance φ hφ a b =
      ⨅ (γ : Path a b) (_ : HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface γ),
        ∫⁻ t in Ioo (0 : ℝ) 1, phiDensity φ (γ.extend t : ℂ) *
          ‖deriv (fun v : ℝ => (γ.extend v : ℂ)) t‖ₑ := by
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  unfold upperHalfPiecewiseSmoothQuadraticDistance piecewiseSmoothQuadraticDistance
  refine iInf_congr fun γ => iInf_congr fun hγ => ?_
  obtain ⟨n, τ, x, h0, hn, hτ, _, _, hlen⟩ :=
    quadraticLengthPath_eq_integrals_of_piecewiseSmooth upperHalfNativeSurface
      (upperHalfNativeQuadratic φ hφ) γ hγ
  rw [hlen]
  have hsum := utm_a_lintegral_sum_eq (fun t => phiDensity φ (γ.extend t : ℂ) *
    ‖deriv (fun v : ℝ => (γ.extend v : ℂ)) t‖ₑ) n τ hτ.monotone
  rw [h0, hn] at hsum
  refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsum
  refine setLIntegral_congr_fun measurableSet_Ioo fun t _ => ?_
  have he : (fun v : ℝ => chartAt ℂ (x i) (γ.extend v)) =
      (fun v : ℝ => (γ.extend v : ℂ)) := by
    funext v
    rw [upperHalf_native_chart]
    rfl
  rw [he, upperHalf_native_chart (x i)]
  change phiDensity (upperHalf.indicator φ) (γ.extend t : ℂ) *
      ‖deriv (fun v : ℝ => (γ.extend v : ℂ)) t‖ₑ =
    phiDensity φ (γ.extend t : ℂ) * ‖deriv (fun v : ℝ => (γ.extend v : ℂ)) t‖ₑ
  have htH : (γ.extend t : ℂ) ∈ upperHalf := (γ.extend t).im_pos
  simp only [phiDensity]
  rw [Set.indicator_of_mem htH]

end LowDimensionalTopology.Geometry.Teichmuller
