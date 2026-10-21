/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetFibreRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
  (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
  (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)

local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
  (generalCoreTheta_mem g orders s t ho hdef) hd hb
local notation "P₀" => _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀
local notation "S₀" => generalCoreAuxSidePairing g orders s t ho hdef d hd hb
local notation "H₀" => generalCoreTargetGroup g orders s t ho hdef d hd hb
local notation "W₀" => generalCoreCutWallUnion g orders s t ho hdef d hd hb

/-- Every whole-auxiliary-group incidence between original polygon points
whose target misses the actual walls is already an incidence in the target
subgroup. This is proved for every auxiliary element, not chosen generators. -/
theorem generalCoreAux_incidence_mem_target (x : ℍ) (hx : x ∈ (P₀).carrier)
    (hxW : x ∉ W₀) (γ : (S₀).Generated) (y : ℍ) (hy : y ∈ (P₀).carrier)
    (hγ : γ.val y = x) : γ.val ∈ H₀ := by
  let p : (P₀).Point := ⟨x, hx⟩
  let q : (P₀).Point := ⟨y, hy⟩
  have hproj : (S₀).project (γ, q) = (S₀).project (1, p) := by
    apply generalCoreAux_evaluation_injective g orders s t ho hdef d hd hb
    exact hγ
  exact generalCoreTargetFibre_labels g orders s t ho hdef d hd hb p hxW (γ, q) hproj

/-- The whole auxiliary orbit relation on actual original off-wall polygon
points equals the target orbit relation. The second point need only belong
to the original carrier, so this also covers all original off-wall pairs. -/
theorem generalCoreAux_orbit_iff_target (x y : ℍ) (hx : x ∈ (P₀).carrier)
    (hy : y ∈ (P₀).carrier) (hxW : x ∉ W₀) :
    (∃ γ : (S₀).Generated, γ.val y = x) ↔ ∃ k : H₀, k.val y = x := by
  constructor
  · rintro ⟨γ, hγ⟩
    exact ⟨⟨γ.val, generalCoreAux_incidence_mem_target g orders s t ho hdef d hd hb
      x hx hxW γ y hy hγ⟩, hγ⟩
  · rintro ⟨k, hk⟩
    exact ⟨⟨k.val, generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb k.property⟩, hk⟩

/-- The entire actual point stabilizer in the target is isomorphic to the
entire auxiliary point stabilizer at every original off-wall point. Neither
side is replaced by a selected cyclic subgroup. -/
def generalCoreTarget_stabilizerEquivAux (x : ℍ) (hx : x ∈ (P₀).carrier) (hxW : x ∉ W₀) :
    MulAction.stabilizer H₀ x ≃* MulAction.stabilizer (S₀).Generated x where
  toFun a := ⟨⟨a.val.val,
    generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb a.val.property⟩, a.property⟩
  invFun a := ⟨⟨a.val.val,
    generalCoreAux_incidence_mem_target g orders s t ho hdef d hd hb
      x hx hxW a.val x hx a.property⟩, a.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

/-- In particular the exact full stabilizer orders agree for the actual
target and auxiliary groups at every original off-wall polygon point. -/
theorem generalCoreTarget_stabilizer_card_eq_aux (x : ℍ)
    (hx : x ∈ (P₀).carrier) (hxW : x ∉ W₀) :
    Nat.card (MulAction.stabilizer H₀ x) = Nat.card (MulAction.stabilizer (S₀).Generated x) :=
  Nat.card_congr (generalCoreTarget_stabilizerEquivAux g orders s t ho hdef d hd hb x hx hxW).toEquiv

end LowDimensionalTopology.Geometry.Fuchsian
