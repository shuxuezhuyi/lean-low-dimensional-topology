/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.NativeIsometryDiscontinuity
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.NativeIsometryMeasure
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.PerpendicularBisectors
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaFinite
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Polygon

/-- Even an orientation-reversing nonidentity native isometry has actual hyperbolic-area-null fixed locus. -/
theorem nativeIsometry_nonidentity_fixed_volume_zero (f:ℍ≃ᵢℍ) (hf:f≠1) :
    volume {z:ℍ|f z=z}=0 := by
  have hex:∃p:ℍ,f p≠p:=by
    by_contra hn
    push Not at hn
    exact hf (IsometryEquiv.ext hn)
  obtain ⟨p,hp⟩:=hex
  obtain ⟨L,hL⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_hEquidistantLine hp.symm
  apply measure_mono_null (t:=L.carrier) _ L.volume_zero
  intro z hz
  rw [hL]
  change dist z p=dist z (f p)
  calc
    dist z p=dist (f z) (f p):=(f.isometry.dist_eq z p).symm
    _=dist z (f p):=by rw [hz]

/-- Actual native discreteness implies countability through the proved compact-set discontinuity condition. -/
theorem nativeDiscreteIsometrySubgroup_countable_of_discontinuous (H:Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] :
    Countable H := (nativeIsometrySubgroup_discontinuous H).countable_of_nonempty UpperHalfPlane.I

/-- The genuine density measure is nonzero on the actual hyperbolic plane. -/
theorem nativeHalfPlane_volume_univ_ne_zero : volume (univ:Set ℍ)≠0 := by
  have hv:volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph (fun _=>1) (Ioo (0:ℝ) 1))=1:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph_volume _ _ measurable_const measurableSet_Ioo (by intro x hx;norm_num)]
    simp
  intro hz
  have h:volume (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneAboveGraph (fun _=>1) (Ioo (0:ℝ)
    1))≤volume (univ:Set ℍ):=
    measure_mono (subset_univ _)
  rw [hv,hz] at h
  norm_num at h

/-- Almost every actual point has trivial stabilizer for every countable native subgroup, including reflection groups. -/
theorem nativeCountableIsometrySubgroup_free_points_ae (H:Subgroup (ℍ≃ᵢℍ)) [Countable H] :
    ∀ᵐw:ℍ∂volume,∀g:H,g•w=w→g=1 := by
  have hnull:volume (⋃g:H,⋃(_h:g≠1),{w:ℍ|g•w=w})=0:=by
    apply measure_iUnion_null
    intro g
    apply measure_iUnion_null
    intro hg
    exact nativeIsometry_nonidentity_fixed_volume_zero g.val (fun he=>hg (Subtype.ext he))
  apply ae_iff.mpr
  apply measure_mono_null _ hnull
  intro w hw
  push Not at hw
  obtain ⟨g,hg,hne⟩:=hw
  exact mem_iUnion.mpr ⟨g,mem_iUnion.mpr ⟨hne,hg⟩⟩

/-- Every countable native subgroup has a genuine free center; no conformality or finite fixed-point assertion is used. -/
theorem nativeCountableIsometrySubgroup_exists_free_point (H:Subgroup (ℍ≃ᵢℍ)) [Countable H] :
    ∃w:ℍ,∀g:H,g•w=w→g=1 := by
  by_contra hn
  have hnull:=ae_iff.mp (nativeCountableIsometrySubgroup_free_points_ae H)
  apply nativeHalfPlane_volume_univ_ne_zero
  apply measure_mono_null _ hnull
  intro w _hw
  exact fun hw=>hn ⟨w,hw⟩

/-- Every actual discrete full native isometry subgroup has an original point with trivial stabilizer. -/
theorem nativeDiscreteIsometrySubgroup_exists_free_point (H:Subgroup (ℍ≃ᵢℍ)) [DiscreteTopology H] :
    ∃w:ℍ,∀g:H,g•w=w→g=1 := by
  let :=nativeDiscreteIsometrySubgroup_countable_of_discontinuous H
  exact nativeCountableIsometrySubgroup_exists_free_point H

end LowDimensionalTopology.Geometry.Fuchsian
