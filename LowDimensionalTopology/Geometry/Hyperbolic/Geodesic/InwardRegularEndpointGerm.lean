module

public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.Finite
public import Mathlib.Analysis.Complex.UpperHalfPlane.Topology

/-! Inward regular germs in the exact finite native geodesic segment. -/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic

private theorem ray_short_mem_closedSegment {z w u : ℍ} (R : HRayAt z)
    (hzw : z ≠ w) (hw : w ∈ R.val) (hu : u ∈ R.val)
    (hd : dist z u < dist z w) : u ∈ closedHSegment z w := by
  obtain ⟨γ, hγ, s, hs, hR, _⟩ := R.isRay
  rcases hR with hR | hR
  · rw [hR] at hw hu
    obtain ⟨t, ht, rfl⟩ := hw
    obtain ⟨r, hr, rfl⟩ := hu
    have hdist : dist (γ s) (γ r) < dist (γ s) (γ t) := by simpa only [hs] using hd
    rw [hγ.1.dist_eq, hγ.1.dist_eq, Real.dist_eq, Real.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr hr), abs_of_nonpos (sub_nonpos.mpr ht)] at hdist
    refine ⟨γ, hγ, s, t, ht, hs, rfl, r, ⟨hr, ?_⟩, rfl⟩
    linarith
  · rw [hR] at hw hu
    obtain ⟨t, ht, rfl⟩ := hw
    obtain ⟨r, hr, rfl⟩ := hu
    have hdist : dist (γ s) (γ r) < dist (γ s) (γ t) := by simpa only [hs] using hd
    rw [hγ.1.dist_eq, hγ.1.dist_eq, Real.dist_eq, Real.dist_eq,
      abs_of_nonneg (sub_nonneg.mpr hr), abs_of_nonneg (sub_nonneg.mpr ht)] at hdist
    rw [closedHSegment_comm hzw]
    refine ⟨γ, hγ, t, s, ht, rfl, hs, r, ⟨?_, hr⟩, rfl⟩
    linarith

/-- At the first endpoint, a genuine nonzero regular germ enters this exact
finite segment. It does not differentiate any old continuous path parameter. -/
theorem HalfPlaneLine.exists_inward_regular_endpoint_germ (L : HalfPlaneLine)
    (z w : ℍ) (hzw : z ≠ w) (hz : z ∈ L.carrier) (hw : w ∈ L.carrier) :
    ∃ (γ : ℝ → ℍ) (a : ℝ), a ≠ 0 ∧ γ 0 = z ∧ ContinuousAt γ 0 ∧
      HasDerivAt (fun t => (γ t : ℂ)) (a • L.tangentAt z) 0 ∧
      deriv (fun t => (γ t : ℂ)) 0 ≠ 0 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioo (0 : ℝ) ε, γ t ∈ openHSegment z w := by
  let R := hRayThrough z w hzw
  have hwR : w ∈ R.val := hRayThrough_mem z w hzw
  have hRL : R.supportLine = L :=
    R.supportLine.eq_of_two_points L hzw R.start_mem_support (R.subset_support hwR) hz hw
  obtain ⟨_, c, hc, hc0, ε, hε, hcR⟩ := R.tangentVector_isForward
  let γ : ℝ → ℍ := fun t => UpperHalfPlane.ofComplex (c t)
  have hγ0 : γ 0 = z := by
    change UpperHalfPlane.ofComplex (c 0) = z
    rw [hc0]
    exact UpperHalfPlane.ofComplex_apply z
  have ht : Tendsto c (𝓝 0) (𝓝 (z : ℂ)) := by
    simpa only [hc0] using hc.continuousAt.tendsto
  have he := (UpperHalfPlane.eventuallyEq_coe_comp_ofComplex z.im_pos).comp_tendsto ht
  change (fun t => (γ t : ℂ)) =ᶠ[𝓝 0] c at he
  have hv : R.tangentVector = R.tangentSign • L.tangentAt z := by
    rw [HRayAt.tangentVector, hRL]
  have hder : HasDerivAt (fun t => (γ t : ℂ)) (R.tangentSign • L.tangentAt z) 0 := by
    rw [← hv]
    exact hc.congr_of_eventuallyEq he
  have hcont : ContinuousAt γ 0 :=
    UpperHalfPlane.isEmbedding_coe.isInducing.continuousAt_iff.mpr hder.continuousAt
  have hclose : ∀ᶠ t in 𝓝 0, dist z (γ t) < dist z w := by
    have hlim : ContinuousAt (fun t => dist z (γ t)) 0 := continuousAt_const.dist hcont
    have hlt : dist z (γ 0) < dist z w := by
      rw [hγ0, dist_self]
      exact dist_pos.mpr hzw
    exact hlim.eventually (Iio_mem_nhds hlt)
  have hforward : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ R.val \ {z} := by
    filter_upwards [Ioo_mem_nhdsGT hε] with t ht
    obtain ⟨u, hu, huc⟩ := hcR t ht
    have hγu : γ t = u := by
      change UpperHalfPlane.ofComplex (c t) = u
      rw [← huc]
      exact UpperHalfPlane.ofComplex_apply u
    rw [hγu]
    exact hu
  have hinside : ∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ∈ openHSegment z w := by
    filter_upwards [hforward, hclose.filter_mono nhdsWithin_le_nhds] with t hR ht
    have hne : γ t ≠ w := by
      intro heq
      rw [heq] at ht
      exact lt_irrefl _ ht
    exact (mem_openHSegment_iff hzw).mpr
      ⟨ray_short_mem_closedSegment R hzw hwR hR.1 ht, hR.2, hne⟩
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hinside
  have hder0 : deriv (fun t => (γ t : ℂ)) 0 ≠ 0 := by
    rw [hder.deriv]
    exact smul_ne_zero R.tangentSign_ne_zero (L.tangentAt_ne_zero z)
  exact ⟨γ, R.tangentSign, R.tangentSign_ne_zero, hγ0, hcont, hder, hder0,
    δ, hδ, fun t ht => hsub ht⟩

end LowDimensionalTopology.Geometry.Hyperbolic
