module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonIdealCycles
public import LowDimensionalTopology.Geometry.Fuchsian.LimitSet.Approximation.ApproximationRays
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology UpperHalfPlane OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- The two genuine model actions are coordinates of the same original group action. -/
theorem discAction_halfPlane_intertwine {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (z : 𝔻) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.discAction g z) = P.halfPlaneAction g (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z) := by
  calc
    _ = P.halfPlaneCoordinate (g • P.finiteCoordinate.symm z) := rfl
    _ = P.halfPlaneAction g (P.halfPlaneCoordinate (P.finiteCoordinate.symm z)) :=
      (P.halfPlaneAction_coordinate g _).symm
    _ = P.halfPlaneAction g (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z) := by
      congr 1
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.finiteCoordinate (P.finiteCoordinate.symm z)) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z
      rw [P.finiteCoordinate.apply_symm_apply]

/-- One genuine hyperbolic generator or its inverse gives compact inverse-ray returns
for every actual ending ray in the original disc model. -/
theorem hyperbolic_fixed_disc_compact_ray_returns
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val)
    (ξ : ℂ) (hfix : f.val.val (ξ : OnePoint ℂ) = (ξ : OnePoint ℂ)) :
    ∃ g : H, (g=f ∨ g=f⁻¹) ∧ Function.Injective (fun n : ℕ => g^n) ∧
      HasDiscOrbitCompactRayIntersection P (fun n => g^n) ξ := by
  obtain ⟨g,hgf,hg,hreturns⟩ := P.hyperbolic_fixed_halfPlane_ray_returns f hf ξ hfix
  refine ⟨g,hgf,hg,?_⟩
  intro v R hR
  have hEnd : R.toHalfPlane.idealEndpoint = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (ξ : OnePoint ℂ) := by
    rw [R.toHalfPlane_idealEndpoint,hR]
  obtain ⟨K,hK,hmeet⟩ := hreturns (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane v) R.toHalfPlane hEnd
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' K,hK.image _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.continuous,?_⟩
  intro n
  obtain ⟨w,hwK,hwR⟩ := hmeet n
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w,?_,⟨w,hwK,rfl⟩⟩
  have hcoord : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.discAction (g^n) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w)) =
      P.halfPlaneAction (g^n) w := by
    rw [discAction_halfPlane_intertwine,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  change P.halfPlaneAction (g^n) w ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane '' R.val at hwR
  rw [←hcoord] at hwR
  obtain ⟨u,hu,heu⟩ := hwR
  change P.discAction (g^n) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w) ∈ R.val
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective heu ▸ hu

/-- Both actual hyperbolic fixed endpoints are points of approximation for the original
Fuchsian group, with one sequence of distinct genuine powers working at every basepoint. -/
theorem hyperbolic_fixed_pointOfApproximation
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val)
    (ξ : ℂ) (hfix : f.val.val (ξ : OnePoint ℂ) = (ξ : OnePoint ℂ)) :
    IsFuchsianPointOfApproximation P ξ := by
  have hlim : (ξ : OnePoint ℂ) ∈ fuchsianLimitSet H := subset_closure ⟨f,Or.inr hf.1,hfix⟩
  have hξ : ‖ξ‖ = 1 := fuchsian_limit_finite_norm_one P ξ hlim
  obtain ⟨g,_hgf,hg,hcomp⟩ := hyperbolic_fixed_disc_compact_ray_returns P f hf ξ hfix
  have hrays : HasDiscOrbitRayBound P (fun n => g^n) ξ :=
    (disc_orbit_ray_bound_iff_compact P (fun n => g^n) ξ).mpr hcomp
  have hrates : ∀ w : 𝔻, HasDiscOrbitMatrixRate P (fun n => g^n) ξ w :=
    (disc_orbit_all_rates_iff_ray_bound P (fun n => g^n) ξ hξ).mpr hrays
  exact ⟨hlim,fun w => ⟨(fun n => g^n),hg,hrates w⟩⟩

end LowDimensionalTopology.Geometry.Fuchsian
