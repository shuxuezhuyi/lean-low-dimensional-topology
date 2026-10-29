module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicSegments
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Local geodesic arc traces determine one complete line

The parameter of an arc is not assumed to be unit-speed or absolutely
continuous. Local injectivity is precisely the nondegeneracy supplied by an
arc. Two nearby distinct points then determine the local complete line;
connectedness propagates that line across the whole real parameter.
-/

public section
noncomputable section
open Set Filter
open scoped UpperHalfPlane Topology

namespace LowDimensionalTopology.Geometry.Hyperbolic

private theorem hLine_eq_of_common_arc_germ
    {f : ℝ → ℍ} (hfinj : IsLocallyInjective f)
    {S T : Set ℍ} (hS : IsHalfPlaneHLine S) (hT : IsHalfPlaneHLine T) {x : ℝ}
    (hfS : ∀ᶠ t in 𝓝 x, f t ∈ S) (hfT : ∀ᶠ t in 𝓝 x, f t ∈ T) : S = T := by
  obtain ⟨U, hUopen, hxU, hUinj⟩ := hfinj x
  have hnear := (hfS.and hfT).and (hUopen.mem_nhds hxU)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hx : (f x ∈ S ∧ f x ∈ T) ∧ x ∈ U := hnear.self_of_nhds
  have hyball : x + ε / 2 ∈ Metric.ball x ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    have he : x + ε / 2 - x = ε / 2 := by ring
    rw [he, abs_of_pos (half_pos hε)]
    linarith
  have hy := hsub hyball
  have hne : f x ≠ f (x + ε / 2) := by
    intro he
    have ht := hUinj hx.2 hy.2 he
    linarith
  exact isHLine_eq_of_two_points hS hT hne hx.1.1 hy.1.1 hx.1.2 hy.1.2

/-- Genuine local arc germs contained in hyperbolic lines propagate to one
complete line. Local injectivity belongs to the arc hypothesis; the original
parametrization is retained without a unit-speed restriction. -/
theorem exists_hLine_containing_range_of_locally_geodesic_arcs
    {f : ℝ → ℍ} (hfinj : IsLocallyInjective f)
    (hloc : ∀ x : ℝ, ∃ S : Set ℍ,
      IsHalfPlaneHLine S ∧ ∀ᶠ t in 𝓝 x, f t ∈ S) :
    ∃ S : Set ℍ, IsHalfPlaneHLine S ∧ range f ⊆ S := by
  classical
  choose G hG hfG using hloc
  have hconst : IsLocallyConstant G := by
    apply (IsLocallyConstant.iff_eventually_eq G).mpr
    intro x
    obtain ⟨U, hUsub, hUopen, hxU⟩ := eventually_nhds_iff.mp (hfG x)
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    have hfx : ∀ᶠ t in 𝓝 y, f t ∈ G x :=
      Filter.mem_of_superset (hUopen.mem_nhds hy) hUsub
    exact hLine_eq_of_common_arc_germ hfinj (hG y) (hG x) (hfG y) hfx
  refine ⟨G 0, hG 0, ?_⟩
  rintro _ ⟨t, rfl⟩
  rw [← hconst.apply_eq_of_preconnectedSpace t 0]
  exact (hfG t).self_of_nhds

end LowDimensionalTopology.Geometry.Hyperbolic
