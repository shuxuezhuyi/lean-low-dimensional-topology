/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureOrderTwoCones
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureCutAxisIncidence
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane Pointwise Classical
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

/-- Every non-two original mark has its actual outer vertex in the frozen
core polygon. The zero marks remain literal cusp labels. -/
def generalCoreOuterIndex (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : Fin (orders ++ List.replicate s 0).length)
    (hj : (orders ++ List.replicate s 0).getD j.val 2 ≠ 2) :
    Fin (generalCoreAngles g orders s t).length :=
  ⟨4 * g + cofiniteConstructionMarkBaseNat (orders ++ List.replicate s 0) j.val + 1, by
    have hb := generalSignatureAux_outer_bound (generalCoreBaseAngle g orders s t) g
      (orders ++ List.replicate s 0) j.val j.isLt hj
    have hlen := (congrArg List.length (generalCoreAngles_eq_auxAngleList g orders s t)).trans
      (generalSignatureAuxAngleList_length (generalCoreBaseAngle g orders s t) g
        (orders ++ List.replicate s 0) t)
    omega⟩

theorem generalCoreOuterIndex_injective (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j k : Fin (orders ++ List.replicate s 0).length)
    (hj : (orders ++ List.replicate s 0).getD j.val 2 ≠ 2)
    (hk : (orders ++ List.replicate s 0).getD k.val 2 ≠ 2)
    (h : generalCoreOuterIndex g orders s t j hj = generalCoreOuterIndex g orders s t k hk) : j = k := by
  have he := congrArg Fin.val h
  change 4 * g + cofiniteConstructionMarkBaseNat _ j.val + 1 =
    4 * g + cofiniteConstructionMarkBaseNat _ k.val + 1 at he
  apply Fin.ext
  apply cofiniteConstructionMarkBaseNat_injective (orders ++ List.replicate s 0)
  omega

theorem generalCoreOuterIndex_not_cut (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : Fin (orders ++ List.replicate s 0).length)
    (hj : (orders ++ List.replicate s 0).getD j.val 2 ≠ 2) :
    ¬ generalCoreIsCutSide g orders s t (generalCoreOuterIndex g orders s t j hj) := by
  have hb := generalSignatureAux_outer_bound (generalCoreBaseAngle g orders s t) g
    (orders ++ List.replicate s 0) j.val j.isLt hj
  intro hc
  have hc' := hc.1
  change (cofiniteConstructionSideAngles (generalCoreBaseAngle g orders s t) g
    (orders ++ List.replicate s 0)).length ≤
      4 * g + cofiniteConstructionMarkBaseNat (orders ++ List.replicate s 0) j.val + 1 at hc'
  omega

theorem generalCoreOuterIndex_angle (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : Fin (orders ++ List.replicate s 0).length)
    (hj : (orders ++ List.replicate s 0).getD j.val 2 ≠ 2) :
    generalCoreTheta g orders s t (generalCoreOuterIndex g orders s t j hj) =
      cofiniteConstructionConeAngle ((orders ++ List.replicate s 0).getD j.val 2) := by
  let β := generalCoreBaseAngle g orders s t
  let ms := orders ++ List.replicate s 0
  let i := generalCoreOuterIndex g orders s t j hj
  have hget (n : ℕ) : (generalCoreAngles g orders s t).getD n β =
      (generalSignatureAuxAngleList β g ms t).getD n β :=
    congrArg (fun L : List ℝ => L.getD n β) (generalCoreAngles_eq_auxAngleList g orders s t)
  change (generalCoreAngles g orders s t)[i] = _
  simp only [Fin.getElem_fin]
  rw [← List.getD_eq_getElem _ β i.isLt, hget]
  exact generalSignatureAux_outer_angle β g ms t j.val j.isLt hj

theorem generalCoreOuterIndex_step (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : Fin (orders ++ List.replicate s 0).length)
    (hj : (orders ++ List.replicate s 0).getD j.val 2 ≠ 2) :
    ((generalCoreAuxPairing g orders s t).trans (finRotate _))
      (generalCoreOuterIndex g orders s t j hj) = generalCoreOuterIndex g orders s t j hj := by
  let β := generalCoreBaseAngle g orders s t
  let ms := orders ++ List.replicate s 0
  let i := generalCoreOuterIndex g orders s t j hj
  have hs := generalSignatureAux_outer_step β g ms j.val j.isLt hj
  have hi := i.isLt
  apply Fin.ext
  change (finRotate _ (generalCoreAuxPairing g orders s t i)).val = i.val
  rw [generalSignatureAux_finRotate_val, generalCoreAuxPairing_val]
  change (if generalSignatureAuxPairNat β g ms (4 * g + cofiniteConstructionMarkBaseNat ms j.val + 1) + 1 =
      (generalCoreAngles g orders s t).length then 0 else
      generalSignatureAuxPairNat β g ms (4 * g + cofiniteConstructionMarkBaseNat ms j.val + 1) + 1) =
    4 * g + cofiniteConstructionMarkBaseNat ms j.val + 1
  rw [hs, ite_eq_right (by change ¬ i.val = _; omega)]

theorem generalCoreOuterIndex_class_singleton (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : Fin (orders ++ List.replicate s 0).length)
    (hj : (orders ++ List.replicate s 0).getD j.val 2 ≠ 2)
    (k : Fin (generalCoreAngles g orders s t).length) :
    Relation.EqvGen (fun a b => b = ((generalCoreAuxPairing g orders s t).trans (finRotate _)) a)
      (generalCoreOuterIndex g orders s t j hj) k ↔ k = generalCoreOuterIndex g orders s t j hj := by
  let τ := (generalCoreAuxPairing g orders s t).trans (finRotate _)
  let i := generalCoreOuterIndex g orders s t j hj
  have hfix : τ i = i := generalCoreOuterIndex_step g orders s t j hj
  have hchain (a b) (h : Relation.EqvGen (fun a b => b = τ a) a b) : a = i ↔ b = i := by
    induction h with
    | rel a b hab =>
      subst b
      constructor
      · rintro rfl; exact hfix
      · intro he
        apply τ.injective
        exact he.trans hfix.symm
    | refl a => rfl
    | symm a b h ih => exact ih.symm
    | trans a b c hab hbc ihab ihbc => exact ihab.trans ihbc
  constructor
  · intro h
    exact (hchain i k h).mp rfl
  · rintro rfl
    exact Relation.EqvGen.refl _

section ActualOuterCones
variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
local notation "θ₀" => generalCoreTheta g orders s t
local notation "hθ₀" => generalCoreTheta_mem g orders s t ho hdef
local notation "ρ₀" => generalCoreAuxPairing g orders s t
local notation "hρ₀" => generalCoreAuxPairing_involutive g orders s t
local notation "hθρ₀" => generalCoreAuxPairing_angle_profile g orders s t
local notation "hPeriod₀" => generalCoreAux_positive_angular_periods g orders s t ho hdef
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ₀ d hθ₀ hd hb
local notation "S₀" => generalCoreAuxSidePairing g orders s t ho hdef d hd hb
local notation "PΓ₀" => cofiniteMixedTangentialHalfPlaneData θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀
local notation "W₀" => generalCoreCutWallUnion g orders s t ho hdef d hd hb

/-- The physical finite vertex of an actual non-two original mark. -/
def generalCoreOuterPoint (j : Fin (orders ++ List.replicate s 0).length)
    (hj : (orders ++ List.replicate s 0).getD j.val 2 ≠ 2) : ℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (cofiniteMixedTangentialVertexDisc θ₀ d hθ₀ hd hb
    (generalCoreOuterIndex g orders s t j hj))

/-- The actual full auxiliary stabilizer at every finite outer mark has
exactly the prescribed order, from its entire singleton corner class. -/
theorem generalCoreOuterPoint_aux_pointOrder
    (j : Fin (orders ++ List.replicate s 0).length)
    (hm : 3 ≤ (orders ++ List.replicate s 0).getD j.val 2) :
    fuchsianPointOrder (PΓ₀).cayleyData ((PΓ₀).cayleyCoordinate
      (generalCoreOuterPoint g orders s t ho hdef d hd hb j (by omega))) =
      (orders ++ List.replicate s 0).getD j.val 2 := by
  let hj : (orders ++ List.replicate s 0).getD j.val 2 ≠ 2 := by omega
  let i := generalCoreOuterIndex g orders s t j hj
  let m := (orders ++ List.replicate s 0).getD j.val 2
  have hmr : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by dsimp only [m]; omega)
  have hi : 0 < θ₀ i := by
    rw [generalCoreOuterIndex_angle]
    exact div_pos (by positivity) hmr
  have hsum := cofiniteMixedTangential_vertex_class_angle_sum θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀ i hi
  let R := fun a b => Relation.EqvGen (fun a b => b = ((ρ₀).trans (finRotate _)) a) a b
  let a : {k // R i k} := ⟨i, Relation.EqvGen.refl _⟩
  have hs : (∑ k : {k // R i k}, θ₀ k.val) = θ₀ i := by
    apply Finset.sum_eq_single a
    · intro b _ hb
      exact False.elim (hb (Subtype.ext ((generalCoreOuterIndex_class_singleton g orders s t j hj b.val).mp b.property)))
    · simp
  rw [hs, generalCoreOuterIndex_angle] at hsum
  have hpor : (0 : ℝ) < fuchsianPointOrder (PΓ₀).cayleyData ((PΓ₀).cayleyCoordinate
      (generalCoreOuterPoint g orders s t ho hdef d hd hb j hj)) := by
    exact_mod_cast (PΓ₀).cayleyData.pointOrder_pos ((PΓ₀).cayleyCoordinate
      (generalCoreOuterPoint g orders s t ho hdef d hd hb j hj))
  have hreal : (fuchsianPointOrder (PΓ₀).cayleyData ((PΓ₀).cayleyCoordinate
      (generalCoreOuterPoint g orders s t ho hdef d hd hb j hj)) : ℝ) = (m : ℝ) := by
    have he : 2 * Real.pi * (fuchsianPointOrder (PΓ₀).cayleyData ((PΓ₀).cayleyCoordinate
        (generalCoreOuterPoint g orders s t ho hdef d hd hb j hj)) : ℝ) = 2 * Real.pi * (m : ℝ) :=
      (div_eq_div_iff hmr.ne' hpor.ne').mp hsum
    exact mul_left_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero) he
  exact_mod_cast hreal

/-- A finite outer mark is its actual original closed-model vertex. -/
theorem generalCoreOuterPoint_coordinate
    (j : Fin (orders ++ List.replicate s 0).length)
    (hm : 3 ≤ (orders ++ List.replicate s 0).getD j.val 2) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
      (generalCoreOuterPoint g orders s t ho hdef d hd hb j (by omega))) =
      (Q₀).vertices (generalCoreOuterIndex g orders s t j (by omega)) := by
  have hmr : (0 : ℝ) < (orders ++ List.replicate s 0).getD j.val 2 := by exact_mod_cast (by omega : 0 < (orders ++ List.replicate s 0).getD j.val 2)
  have hi : 0 < θ₀ (generalCoreOuterIndex g orders s t j (by omega)) := by
    rw [generalCoreOuterIndex_angle]
    exact div_pos (by positivity) hmr
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane _)) = _
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  exact (cofiniteMixedTangentialVertexDisc_coordinate θ₀ d hθ₀ hd hb _ hi).symm

theorem generalCoreOuterPoint_mem_carrier
    (j : Fin (orders ++ List.replicate s 0).length)
    (hm : 3 ≤ (orders ++ List.replicate s 0).getD j.val 2) :
    generalCoreOuterPoint g orders s t ho hdef d hd hb j (by omega) ∈
      (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).carrier := by
  apply (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).side_subset_carrier
    (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ (generalCoreOuterIndex g orders s t j (by omega)))
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc _) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment _ _
  rw [generalCoreOuterPoint_coordinate g orders s t ho hdef d hd hb j hm]
  exact _root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_left_mem _ _

/-- A finite outer cone vertex avoids every auxiliary translated cut wall.
The original complete wall incidence is proved separately and is consumed here. -/
theorem generalCoreOuterPoint_not_wall
    (j : Fin (orders ++ List.replicate s 0).length)
    (hm : 3 ≤ (orders ++ List.replicate s 0).getD j.val 2) :
    generalCoreOuterPoint g orders s t ho hdef d hd hb j (by omega) ∉ W₀ := by
  let hj : (orders ++ List.replicate s 0).getD j.val 2 ≠ 2 := by omega
  let i := generalCoreOuterIndex g orders s t j hj
  let x := generalCoreOuterPoint g orders s t ho hdef d hd hb j hj
  have hx := generalCoreOuterPoint_coordinate g orders s t ho hdef d hd hb j hm
  have hxP := generalCoreOuterPoint_mem_carrier g orders s t ho hdef d hd hb j hm
  have hni : ¬ generalCoreIsCutSide g orders s t i := generalCoreOuterIndex_not_cut g orders s t j hj
  have hpred : ρ₀ i = (finRotate _).symm i := by
    apply (finRotate _).injective
    rw [Equiv.apply_symm_apply]
    exact generalCoreOuterIndex_step g orders s t j hj
  have hnp : ¬ generalCoreIsCutSide g orders s t ((finRotate _).symm i) := by
    intro hc
    apply hni
    apply (generalCoreAuxPairing_isCut_iff g orders s t i).mp
    rwa [hpred]
  intro hxW
  obtain ⟨a, ha⟩ := mem_iUnion.mp
    ((generalCoreAux_carrier_wall_iff g orders s t ho hdef d hd hb x hxP).mp hxW)
  let cut := generalCoreBoundarySideIndex g orders s t a 1
  have hc : generalCoreIsCutSide g orders s t cut :=
    (generalCoreBoundarySideIndex_cut_iff g orders s t a 1).mpr rfl
  have hlabels := cofiniteJordan_vertex_side_labels Q₀ i (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x) hx.symm
    (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ cut)
    (by
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x) ∈ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ cut
      change x ∈ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ cut at ha
      simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc] using ha)
  rcases hlabels with hprev | hnext
  · exact hnp ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀).injective hprev ▸ hc)
  · exact hni ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀).injective hnext ▸ hc)

/-- Every prescribed finite outer occurrence has its exact full stabilizer
order in the actual target group, including all additional group words. -/
theorem generalCoreOuterPoint_target_stabilizer_card
    (j : Fin (orders ++ List.replicate s 0).length)
    (hm : 3 ≤ (orders ++ List.replicate s 0).getD j.val 2) :
    Nat.card (MulAction.stabilizer (generalCoreTargetGroup g orders s t ho hdef d hd hb)
      (generalCoreOuterPoint g orders s t ho hdef d hd hb j (by omega))) =
        (orders ++ List.replicate s 0).getD j.val 2 := by
  let hj : (orders ++ List.replicate s 0).getD j.val 2 ≠ 2 := by omega
  let x := generalCoreOuterPoint g orders s t ho hdef d hd hb j hj
  calc
    Nat.card (MulAction.stabilizer (generalCoreTargetGroup g orders s t ho hdef d hd hb) x) =
        Nat.card (MulAction.stabilizer (S₀).Generated x) :=
      generalCoreTarget_stabilizer_card_eq_aux g orders s t ho hdef d hd hb x
        (generalCoreOuterPoint_mem_carrier g orders s t ho hdef d hd hb j hm)
        (generalCoreOuterPoint_not_wall g orders s t ho hdef d hd hb j hm)
    _ = Nat.card (MulAction.stabilizer
        (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteMixedTangentialMobiusGroup θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀))
        ((PΓ₀).cayleyCoordinate x)) := Nat.card_congr
      (generalCoreAux_projective_disc_stabilizerEquiv g orders s t ho hdef d hd hb x).toEquiv
    _ = _ := generalCoreOuterPoint_aux_pointOrder g orders s t ho hdef d hd hb j hm

/-- Different actual finite outer labels cannot be identified by any
word of the entire target group. -/
theorem generalCoreOuterPoint_target_orbit_injective
    (j k : Fin (orders ++ List.replicate s 0).length)
    (hj : 3 ≤ (orders ++ List.replicate s 0).getD j.val 2)
    (hk : 3 ≤ (orders ++ List.replicate s 0).getD k.val 2)
    (a : generalCoreTargetGroup g orders s t ho hdef d hd hb)
    (ha : a.val (generalCoreOuterPoint g orders s t ho hdef d hd hb j (by omega)) =
      generalCoreOuterPoint g orders s t ho hdef d hd hb k (by omega)) : j = k := by
  have hrel := cofiniteMixedTangential_vertex_orbit_label θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hPeriod₀
    (generalCoreOuterIndex g orders s t k (by omega)) (generalCoreOuterIndex g orders s t j (by omega))
    _ _ (generalCoreOuterPoint_coordinate g orders s t ho hdef d hd hb k hk)
    (generalCoreOuterPoint_coordinate g orders s t ho hdef d hd hb j hj)
    ⟨a.val, generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb a.property⟩ ha
  have hi := (generalCoreOuterIndex_class_singleton g orders s t k (by omega) _).mp hrel
  exact generalCoreOuterIndex_injective g orders s t j k (by omega) (by omega) hi

end ActualOuterCones
end LowDimensionalTopology.Geometry.Fuchsian
