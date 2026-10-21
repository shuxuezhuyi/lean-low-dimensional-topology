/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureSidePairingProfile
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane Complex.UnitDisc OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

section ActualMixedPolygon
variable {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (ρ : Equiv.Perm (Fin n))
    (hρ : Function.Involutive ρ) (hθρ : ∀ i, θ i = θ (finRotate n (ρ i)))
    (hPeriod : ∀ i : Fin n, 0 < θ i → ∃ N : ℕ,
      3 ≤ N ∧ ((ρ.trans (finRotate n))^[N]) i = i ∧ θ i = _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N)
local notation "Γ₀" => cofiniteMixedTangentialMobiusGroup θ d hθ hd hb ρ hρ hθρ
local notation "P₀" => cofiniteMixedTangentialHalfPlaneData θ d hθ hd hb ρ hρ hθρ hPeriod
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb
include hPeriod

/-- Every parabolic fixed point of the actual entire auxiliary group has
an actual original zero-corner representative. The output is a literal
original ideal point and an element of the unchanged whole half-plane group. -/
theorem mixedTangential_parabolic_fixedPoint_zero_corner
    (f : Γ₀)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (ξ : Mobius.ExtendedComplex)
    (hfix : f.val.val ξ = ξ) :
    ∃ a : Γ₀, ∃ i : Fin n, θ i = 0 ∧
      a.val.val ξ = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm ((Q₀).vertices i)).val := by
  let F := (P₀).cayleyCoordinate '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (Q₀).interior)
  let E := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius Γ₀
  have hact (a : Γ₀) (p : Mobius.ExtendedComplex) :
      (E a).val.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val p) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (a.val.val p) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (a.val.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val p))) = _
    rw [Equiv.symm_apply_apply]
  have hfN : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (E f).val :=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius, rfl⟩)).mp hf
  have hfixN : (E f).val.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val ξ) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val ξ := by
    rw [hact, hfix]
  have hD := cofiniteMixedTangential_projective_disc_convex θ d hθ hd hb ρ hρ hθρ hPeriod
  obtain ⟨aN, η, haN, hη⟩ :=
    hD.locallyFinite.parabolic_fixedPoint_orbit_mem_idealBoundary (E f) hfN
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val ξ) hfixN
  have hη' := (mem_fuchsianPolygonIdealBoundary (P₀).cayleyData F η).mp hη
  have himage : (fun x => ((P₀).cayleyData.finiteCoordinate x : ℂ)) '' F =
      (Q₀).complexInterior := by
    rw [← image_image, cofiniteMixedTangential_projective_disc_finite_region θ d hθ hd hb ρ hρ hθρ hPeriod]
    exact (Q₀).interior_complex_image
  have hcl : η ∈ closure (Q₀).complexInterior := himage ▸ hη'.1
  rw [(Q₀).closure_complexInterior] at hcl
  have hnot : η ∉ (Q₀).complexInterior := by
    intro hi
    have hn := (Q₀).complexInterior_subset_disc hi
    simp only [Metric.mem_ball, dist_zero_right, hη'.2, lt_self_iff_false] at hn
  obtain ⟨p, hp, hpe⟩ := hcl.resolve_left hnot
  have hpn : ‖(p : ℂ)‖ = 1 := hpe.symm ▸ hη'.2
  obtain ⟨i, hpi⟩ := (Q₀).ideal_boundary_is_vertex p hp hpn
  have hvi : ‖((Q₀).vertices i : ℂ)‖ = 1 := hpi ▸ hpn
  have hi : θ i = 0 := (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_ideal_iff θ d hθ hd i).mp hvi
  have hηv : η = ((Q₀).vertices i : ℂ) := hpe.symm.trans (congrArg (fun z : 𝕔𝔻 => (z : ℂ)) hpi)
  rw [hηv] at haN
  let a := E.symm aN
  refine ⟨a, i, hi, ?_⟩
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.injective
  have ha := hact a ξ
  rw [E.apply_symm_apply] at ha
  have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscToExtended ((Q₀).vertices i) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm ((Q₀).vertices i)).val := by
    simpa only [Homeomorph.apply_symm_apply, _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius_apply] using
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_toExtended (_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayleyHomeomorph.symm ((Q₀).vertices i))
  exact ha.symm.trans (haN.trans hm)

end ActualMixedPolygon
end LowDimensionalTopology.Geometry.Fuchsian
