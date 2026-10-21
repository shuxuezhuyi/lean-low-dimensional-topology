/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetIncidence
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureNoncutChamber
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
  (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
  (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)

local notation "θ₀" => generalCoreTheta g orders s t
local notation "hθ₀" => generalCoreTheta_mem g orders s t ho hdef
local notation "ρ₀" => generalCoreAuxPairing g orders s t
local notation "hρ₀" => generalCoreAuxPairing_involutive g orders s t
local notation "hθρ₀" => generalCoreAuxPairing_angle_profile g orders s t
local notation "hp₀" => generalCoreAux_positive_angular_periods g orders s t ho hdef
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ₀ d hθ₀ hd hb
local notation "S₀" => generalCoreAuxSidePairing g orders s t ho hdef d hd hb
local notation "H₀" => generalCoreTargetGroup g orders s t ho hdef d hd hb
local notation "Γ₀" => cofiniteMixedTangentialMobiusGroup θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀
local notation "PΓ₀" => cofiniteMixedTangentialHalfPlaneData θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hp₀

/-- The literal original incircle contact of a canonical side. Self sides
will give order-two cones; no ellipticity is built into this point. -/
def generalCoreSelfSideFoot (i : Fin (generalCoreAngles g orders s t).length) : ℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ₀ d hd (finRotate _ i))

/-- Every retained side contact misses all auxiliary cut walls, by actual
whole-group side incidence and the genuine nonvertex geometry. -/
theorem generalCoreSelfSideFoot_not_wall (i : Fin (generalCoreAngles g orders s t).length)
    (hi : ¬ generalCoreIsCutSide g orders s t i) :
    generalCoreSelfSideFoot g orders s t d hd i ∉
      generalCoreCutWallUnion g orders s t ho hdef d hd hb := by
  apply generalCoreNoncutSide_nonvertex_not_wall g orders s t ho hdef d hd hb i hi
  · exact cofiniteTangential_foot_mem_side θ₀ d hθ₀ hd hb i
  · exact cofiniteTangential_actual_foot_nonvertex θ₀ d hθ₀ hd hb i

/-- The actual auxiliary native and physical Cayley-disc entire stabilizers
are isomorphic, without restricting to selected elliptic generators. -/
def generalCoreAux_projective_disc_stabilizerEquiv (x : ℍ) :
    MulAction.stabilizer (S₀).Generated x ≃*
      MulAction.stabilizer (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius Γ₀)
        ((PΓ₀).cayleyCoordinate x) := by
  let E := (cofiniteMixedTangentialGroupEquiv θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀).trans
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius Γ₀)
  have hAct (a : (S₀).Generated) (z : ℍ) :
      (PΓ₀).cayleyCoordinate (a.val z) = E a • (PΓ₀).cayleyCoordinate z :=
    cofiniteMixedTangential_coordinate_action θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hp₀ a z
  refine {
    toFun := fun a => ⟨E a.val, (hAct a.val x).symm.trans
      (congrArg (PΓ₀).cayleyCoordinate a.property)⟩
    invFun := fun a => ⟨E.symm a.val, ?_⟩
    left_inv := fun a => Subtype.ext (E.symm_apply_apply a.val)
    right_inv := fun a => Subtype.ext (E.apply_symm_apply a.val)
    map_mul' := fun a b => Subtype.ext (E.map_mul a.val b.val)
  }
  apply (PΓ₀).cayleyCoordinate.injective
  change (PΓ₀).cayleyCoordinate ((E.symm a.val).val x) = (PΓ₀).cayleyCoordinate x
  rw [hAct, E.apply_symm_apply]
  exact a.property

/-- Each true retained self-side contributes an actual order-two point of
the entire target group. The order is neither a lower bound nor the order
of a chosen cyclic subgroup. -/
theorem generalCoreSelfSideFoot_target_stabilizer_card
    (i : Fin (generalCoreAngles g orders s t).length)
    (hi : ¬ generalCoreIsCutSide g orders s t i) (hself : ρ₀ i = i) :
    Nat.card (MulAction.stabilizer H₀ (generalCoreSelfSideFoot g orders s t d hd i)) = 2 := by
  let x := generalCoreSelfSideFoot g orders s t d hd i
  have hx : x ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).carrier :=
    (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)
      (cofiniteTangential_foot_mem_side θ₀ d hθ₀ hd hb i)
  calc
    Nat.card (MulAction.stabilizer H₀ x) = Nat.card (MulAction.stabilizer (S₀).Generated x) :=
      generalCoreTarget_stabilizer_card_eq_aux g orders s t ho hdef d hd hb x hx
        (generalCoreSelfSideFoot_not_wall g orders s t ho hdef d hd hb i hi)
    _ = Nat.card (MulAction.stabilizer (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius Γ₀)
        ((PΓ₀).cayleyCoordinate x)) :=
      Nat.card_congr (generalCoreAux_projective_disc_stabilizerEquiv g orders s t ho hdef d hd hb x).toEquiv
    _ = 2 := cofiniteMixedTangential_self_foot_pointOrder θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hp₀ i hself

/-- Distinct retained original self-side labels stay distinct under every
element of the actual target group, including any additional word. -/
theorem generalCoreSelfSideFoot_target_orbit_injective
    (i j : Fin (generalCoreAngles g orders s t).length) (hi : ρ₀ i = i) (hj : ρ₀ j = j)
    (a : H₀) (ha : a.val (generalCoreSelfSideFoot g orders s t d hd i) =
      generalCoreSelfSideFoot g orders s t d hd j) : i = j :=
  cofiniteMixedTangential_self_foot_orbit_injective θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hp₀ i j hi hj
    ⟨a.val, generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb a.property⟩ ha

/-- No true self-side contact shares an actual target-group orbit with any
original finite vertex, including the ordinary cycle and all cone corners. -/
theorem generalCoreSelfSideFoot_not_target_vertex_orbit
    (i j : Fin (generalCoreAngles g orders s t).length) (hi : ρ₀ i = i)
    (x : ℍ) (hx : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x) = (Q₀).vertices j)
    (a : H₀) (ha : a.val (generalCoreSelfSideFoot g orders s t d hd i) = x) : False :=
  cofiniteMixedTangential_self_foot_not_vertex_orbit θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hp₀ i j hi x hx
    ⟨a.val, generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb a.property⟩ ha

end LowDimensionalTopology.Geometry.Fuchsian
