module

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicSegments
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Local unit-speed hyperbolic geodesics extend to complete geodesics

Two complete unit-speed geodesics agreeing at two distinct parameter values
agree everywhere. Consequently each local unit-speed geodesic germ determines
a unique complete parameter. The germ parameters form a locally constant map
on the connected real line, so a locally geodesic curve has one global parameter.
-/

public section
noncomputable section
open Set Filter
open scoped UpperHalfPlane Topology

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Agreement at two distinct actual times determines a complete unit-speed
geodesic, including its parametrization and orientation. -/
theorem IsHGeodesicParam.eq_of_eq_two_times {γ δ : ℝ → ℍ}
    (hγ : IsHGeodesicParam γ) (hδ : IsHGeodesicParam δ)
    {s t : ℝ} (hst : s ≠ t) (hs : γ s = δ s) (ht : γ t = δ t) : γ = δ := by
  have hne : γ s ≠ γ t := hγ.1.injective.ne hst
  have hrange : range γ = range δ := isHLine_eq_of_two_points hγ.2 hδ.2 hne
    (mem_range_self s) (mem_range_self t) ⟨s, hs.symm⟩ ⟨t, ht.symm⟩
  funext u
  obtain ⟨v, hv⟩ : γ u ∈ range δ := hrange ▸ mem_range_self u
  have hdist (a : ℝ) (ha : γ a = δ a) : |v - a| = |u - a| := by
    calc
      |v - a| = dist (δ v) (δ a) := by
        simpa only [Real.dist_eq] using (hδ.1.dist_eq v a).symm
      _ = dist (γ u) (γ a) := by rw [hv, ← ha]
      _ = |u - a| := by simpa only [Real.dist_eq] using hγ.1.dist_eq u a
  have hsSq : (v - s) ^ 2 = (u - s) ^ 2 :=
    (sq_abs (v - s)).symm.trans
      ((congrArg (fun x : ℝ => x ^ 2) (hdist s hs)).trans (sq_abs (u - s)))
  have htSq : (v - t) ^ 2 = (u - t) ^ 2 :=
    (sq_abs (v - t)).symm.trans
      ((congrArg (fun x : ℝ => x ^ 2) (hdist t ht)).trans (sq_abs (u - t)))
  have hproduct : (t - s) * (v - u) = 0 := by nlinarith only [hsSq, htSq]
  have hvu : v = u := sub_eq_zero.mp
    ((mul_eq_zero.mp hproduct).resolve_left (sub_ne_zero.mpr hst.symm))
  exact hv.symm.trans (congrArg δ hvu)

/-- An actual common unit-speed geodesic germ fixes the complete parameter. -/
theorem IsHGeodesicParam.eq_of_eventuallyEq {γ δ : ℝ → ℍ}
    (hγ : IsHGeodesicParam γ) (hδ : IsHGeodesicParam δ) {x : ℝ}
    (h : γ =ᶠ[𝓝 x] δ) : γ = δ := by
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp h
  have hx : γ x = δ x := h.eq_of_nhds
  have hx' : γ (x + ε / 2) = δ (x + ε / 2) := by
    apply hsub
    rw [Metric.mem_ball, Real.dist_eq]
    have he : x + ε / 2 - x = ε / 2 := by ring
    rw [he, abs_of_pos (half_pos hε)]
    linarith
  exact hγ.eq_of_eq_two_times hδ (by intro he; linarith) hx hx'

/-- A genuinely locally unit-speed geodesic on the whole real line is a
complete unit-speed geodesic. Locality is actual eventual equality with a
geodesic parameter, without any assumed common axis or global parameter. -/
theorem isHGeodesicParam_of_locally {f : ℝ → ℍ}
    (hloc : ∀ x : ℝ, ∃ γ : ℝ → ℍ,
      IsHGeodesicParam γ ∧ f =ᶠ[𝓝 x] γ) : IsHGeodesicParam f := by
  classical
  choose g hg hfg using hloc
  have hconst : IsLocallyConstant g := by
    apply (IsLocallyConstant.iff_eventually_eq g).mpr
    intro x
    obtain ⟨U, hUeq, hUopen, hxU⟩ := eventually_nhds_iff.mp (hfg x)
    filter_upwards [hUopen.mem_nhds hxU] with y hy
    have hfx : f =ᶠ[𝓝 y] g x :=
      Filter.mem_of_superset (hUopen.mem_nhds hy) hUeq
    exact (hg y).eq_of_eventuallyEq (hg x) ((hfg y).symm.trans hfx)
  have heq : f = g 0 := by
    funext t
    exact (hfg t).eq_of_nhds.trans
      (congrFun (hconst.apply_eq_of_preconnectedSpace t 0) t)
  rw [heq]
  exact hg 0

end LowDimensionalTopology.Geometry.Hyperbolic
