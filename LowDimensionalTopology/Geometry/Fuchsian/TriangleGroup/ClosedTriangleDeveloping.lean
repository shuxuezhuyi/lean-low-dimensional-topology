/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleVertexStars
public import LowDimensionalTopology.Geometry.Polygon.Development.PackingDevelopmentHomeomorph
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  Set
  Topology
open scoped UpperHalfPlane Pointwise

/-- The independently proved literal ideal-triangle packing transports through the actual native normalizer. -/
theorem closedTriangle_packing_of_gamma_zero (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta) (hγ:T.gamma=0)
    (g:ℍ≃ᵢℍ) (hg:g∈triangleReflectionGroup T) (hne:g≠1) :
    Disjoint (g • T.interior) T.interior := by
  have hs:T.alpha+T.beta<Real.pi:=by simpa only [hγ,add_zero] using T.angle_sum_lt_pi
  let U:=prescribedIdealHTriangle T.alpha T.beta ha.nonneg hb.nonneg hs
  obtain ⟨e,hG,hI⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.ideal_group_and_interior_canonical T hγ
  have hgU:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate e (triangleReflectionGroup T)=triangleReflectionGroup U:=by
    rw [hG]
    exact (prescribedIdealHTriangle_reflection_eq_normalized _ _ _ _ _).symm
  have hiU:e '' T.interior=U.interior:=by
    rw [hI]
    exact (prescribedIdealHTriangle_interior_graph _ _ _ _ _).symm
  have hgm:e*g*e⁻¹∈triangleReflectionGroup U:=by
    rw [←hgU]
    exact ⟨g,hg,rfl⟩
  have hgn:e*g*e⁻¹≠1:=by
    intro h
    apply hne
    calc
      g=e⁻¹*(e*g*e⁻¹)*e:=by group
      _=1:=by rw [h];simp
  have hD:=prescribedIdealHTriangle_reflection_packing T.alpha T.beta ha hb hs (e*g*e⁻¹) hgm hgn
  apply disjoint_left.mpr
  rintro z ⟨x,hx,hgx⟩ hz
  have hxU:e x∈U.interior:=hiU ▸ mem_image_of_mem e hx
  have hzU:e z∈U.interior:=hiU ▸ mem_image_of_mem e hz
  apply disjoint_left.mp hD ?_ hzU
  refine ⟨e x,hxU,?_⟩
  change e (g (e.symm (e x)))=e z
  change g x=z at hgx
  rw [e.symm_apply_apply,hgx]

theorem closedTriangle_ideal_reflection_packing (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (hIdeal:T.alpha=0 ∨T.beta=0 ∨T.gamma=0)
    (g:ℍ≃ᵢℍ) (hg:g∈triangleReflectionGroup T) (hne:g≠1) :
    Disjoint (g • T.interior) T.interior := by
  have h1:=closedHTriangle_cycle_angles T
  have h2:=closedHTriangle_cycle_angles T.cycle
  rcases hIdeal with hα|hβ|hγ
  · have h:=closedTriangle_packing_of_gamma_zero T.cycle (h1.1.symm ▸ hb) (h1.2.1.symm ▸ hc)
      (h1.2.2.trans hα) g (by simpa only [triangleReflectionGroup_cycle] using hg) hne
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.cycle_interior] using h
  · have h:=closedTriangle_packing_of_gamma_zero T.cycle.cycle
      ((h2.1.trans h1.2.1).symm ▸ hc) ((h2.2.1.trans h1.2.2).symm ▸ ha)
      (h2.2.2.trans (h1.1.trans hβ)) g (by simpa only [triangleReflectionGroup_cycle] using hg) hne
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.cycle_interior] using h
  · exact closedTriangle_packing_of_gamma_zero T ha hb hγ g hg hne

/--
Actual local tessellation, independent original packing and closed orbit covering construct the genuine global
homeomorphism in every ideal configuration; compactness is used only in the all-finite branch.
-/
def closedTriangle_developingHomeomorph (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) : (closedTrianglePoincarePairing T).Development≃ₜℍ := by
  let S:=closedTrianglePoincarePairing T
  let : IsIsometricSMul S.Generated ℍ:=⟨fun g=>g.val.isometry⟩
  have hA:=closedTriangle_integral_local_tessellation T ha hb hc
  by_cases hIdeal:T.alpha=0 ∨T.beta=0 ∨T.gamma=0
  · have hPack:∀g k:S.Generated,g≠k→Disjoint (g • T.interior) (k • T.interior):=by
      intro g k hne
      rw [disjoint_smul_set_right,←mul_smul]
      have hN:k⁻¹*g≠(1:S.Generated):=by intro h;exact hne (inv_mul_eq_one.mp h).symm
      exact closedTriangle_ideal_reflection_packing T ha hb hc hIdeal (k⁻¹*g).val
        (by rw [←closedTrianglePoincarePairing_generated];exact (k⁻¹*g).property)
        (fun h=>hN (Subtype.ext h))
    have hFD:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.fundamentalDomain_of_integral_angles T ha hb hc
    have hCover:∀z:ℍ,∃g:S.Generated,∃p:(closedTrianglePoincarePolygon T).Point,g • p.val=z:=by
      intro z
      obtain ⟨g,y,hy,hgy⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.closure_covering (triangleReflectionGroup T) ℍ hFD z
      let gS:S.Generated:=⟨g.val,by rw [closedTrianglePoincarePairing_generated];exact g.property⟩
      exact ⟨gS,⟨y,(closedTrianglePoincarePolygon_carrier T).symm ▸ hy⟩,hgy⟩
    exact hA.homeomorph_of_packing_cover S T.interior_isOpen
      (closedTrianglePoincarePolygon_carrier T).le hPack hCover
  · push Not at hIdeal
    have hCompact:IsCompact (closedTrianglePoincarePolygon T).carrier:=by
      obtain ⟨U,hU⟩:=positive_angle_closedTriangle_has_finite_model T
        (lt_of_le_of_ne ha.nonneg (Ne.symm hIdeal.1))
        (lt_of_le_of_ne hb.nonneg (Ne.symm hIdeal.2.1))
        (lt_of_le_of_ne hc.nonneg (Ne.symm hIdeal.2.2))
      rw [closedTrianglePoincarePolygon_carrier,←hU,U.interior_toClosedHTriangle]
      exact U.closure_isCompact
    exact (hA.covering_homeomorph_of_compact S (closedTrianglePoincare_metric_assumptions T)
      (closedTrianglePoincarePolygon_carrier T).le hCompact).2.homeomorph


theorem closedTriangle_developingHomeomorph_apply
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (q:(closedTrianglePoincarePairing T).Development) :
    closedTriangle_developingHomeomorph T ha hb hc q=(closedTrianglePoincarePairing T).evaluation q := by
  unfold closedTriangle_developingHomeomorph
  dsimp only
  split <;> rfl

end LowDimensionalTopology.Geometry.Fuchsian
