/- Actual ordinary-corner stabilizers for, 2026-10-20. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureOrderTwoCones
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

/-- The actual ordinary labels remain distinct across an empty prefix,
order-two marks, all other marks and the literal boundary triples. -/
theorem generalSignatureAuxBaseNat_injective (β : ℝ) (g : ℕ) (ms : List ℕ) :
    Function.Injective (generalSignatureAuxBaseNat β g ms) := by
  intro a b hab
  by_cases ha : a < 4 * g + ms.length <;> by_cases hb : b < 4 * g + ms.length
  · simp only [generalSignatureAuxBaseNat, ha, hb, ite_true] at hab
    exact cofiniteConstructionBaseNat_injective g ms hab
  · have hp := cofiniteConstructionBaseNat_bound β g ms a ha
    simp only [generalSignatureAuxBaseNat, ha, hb, ite_true, ite_false] at hab
    omega
  · have hp := cofiniteConstructionBaseNat_bound β g ms b hb
    simp only [generalSignatureAuxBaseNat, ha, hb, ite_true, ite_false] at hab
    omega
  · simp only [generalSignatureAuxBaseNat, ha, hb, ite_false] at hab
    omega

/-- An ordinary-cycle label in the unchanged frozen canonical core polygon. -/
def generalCoreBaseCycleIndex (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (a : Fin (4 * g + (orders ++ List.replicate s 0).length + t)) :
    Fin (generalCoreAngles g orders s t).length :=
  (finCongr (congrArg List.length (generalCoreAngles_eq_auxAngleList g orders s t))).symm
    (generalSignatureAuxBaseIndex (generalCoreBaseAngle g orders s t) g
      (orders ++ List.replicate s 0) t a)

theorem generalCoreBaseCycleIndex_val (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (a : Fin (4 * g + (orders ++ List.replicate s 0).length + t)) :
    (generalCoreBaseCycleIndex g orders s t a).val =
      generalSignatureAuxBaseNat (generalCoreBaseAngle g orders s t) g
        (orders ++ List.replicate s 0) a.val := rfl

theorem generalCoreBaseCycleIndex_injective (g : ℕ) (orders : List ℕ) (s t : ℕ) :
    Function.Injective (generalCoreBaseCycleIndex g orders s t) := by
  intro a b hab
  apply Fin.ext
  exact generalSignatureAuxBaseNat_injective _ g _ (congrArg Fin.val hab)

theorem generalCoreBaseCycleIndex_angle (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (a : Fin (4 * g + (orders ++ List.replicate s 0).length + t)) :
    generalCoreTheta g orders s t (generalCoreBaseCycleIndex g orders s t a) =
      generalCoreBaseAngle g orders s t := by
  let β := generalCoreBaseAngle g orders s t
  let i := generalCoreBaseCycleIndex g orders s t a
  change (generalCoreAngles g orders s t)[i] = β
  simp only [Fin.getElem_fin]
  rw [← List.getD_eq_getElem _ β i.isLt]
  calc
    (generalCoreAngles g orders s t).getD i.val β =
        (generalSignatureAuxAngleList β g (orders ++ List.replicate s 0) t).getD i.val β :=
      congrArg (fun L : List ℝ => L.getD i.val β) (generalCoreAngles_eq_auxAngleList g orders s t)
    _ = β := generalSignatureAuxBaseNat_angle β g (orders ++ List.replicate s 0) t a.val

theorem generalCoreBaseCycleIndex_next (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (a : Fin (4 * g + (orders ++ List.replicate s 0).length + t)) :
    ((generalCoreAuxPairing g orders s t).trans (finRotate _))
      (generalCoreBaseCycleIndex g orders s t a) =
        generalCoreBaseCycleIndex g orders s t (finRotate _ a) := by
  let e := finCongr (congrArg List.length (generalCoreAngles_eq_auxAngleList g orders s t))
  apply e.injective
  change e (finRotate _ (generalCoreAuxPairing g orders s t
    (generalCoreBaseCycleIndex g orders s t a))) = _
  rw [generalSignature_finCongr_rotate]
  change finRotate _ (generalSignatureAuxPairing (generalCoreBaseAngle g orders s t) g
    (orders ++ List.replicate s 0) t (generalSignatureAuxBaseIndex
      (generalCoreBaseAngle g orders s t) g (orders ++ List.replicate s 0) t a)) =
      generalSignatureAuxBaseIndex (generalCoreBaseAngle g orders s t) g
        (orders ++ List.replicate s 0) t (finRotate _ a)
  exact (generalSignatureAuxBaseIndex_next _ g _ t a).symm

/-- Every original ordinary label belongs to the same full natural corner
class, proved from the actual one-step permutation rather than angle equality. -/
theorem generalCoreBaseCycleIndex_related (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (a b : Fin (4 * g + (orders ++ List.replicate s 0).length + t)) :
    Relation.EqvGen (fun i j => j = ((generalCoreAuxPairing g orders s t).trans (finRotate _)) i)
      (generalCoreBaseCycleIndex g orders s t a) (generalCoreBaseCycleIndex g orders s t b) := by
  let B := 4 * g + (orders ++ List.replicate s 0).length + t
  let τ := (generalCoreAuxPairing g orders s t).trans (finRotate _)
  let index := generalCoreBaseCycleIndex g orders s t
  let ordinaryBaseCountNeZero : NeZero B := a.neZero
  let z : Fin B := ⟨0, a.pos⟩
  have hiter (k : ℕ) (c : Fin B) : τ^[k] (index c) = index ((finRotate B)^[k] c) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact generalCoreBaseCycleIndex_next g orders s t _
  have hfrom (c : Fin B) : Relation.EqvGen (fun i j => j = τ i) (index z) (index c) := by
    have hchain (k : ℕ) : Relation.EqvGen (fun i j => j = τ i) (index z) (τ^[k] (index z)) := by
      induction k with
      | zero => exact Relation.EqvGen.refl _
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact Relation.EqvGen.trans _ _ _ ih (Relation.EqvGen.rel _ _ rfl)
    have hrot : (finRotate B)^[c.val] z = c := by
      rw [← finCycle_eq_finRotate_iterate (k := c)]
      change (0 : Fin B) + c = c
      exact zero_add c
    have he := hchain c.val
    rw [hiter, hrot] at he
    exact he
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hfrom a)) (hfrom b)

section ActualOrdinaryCorners
variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
local notation "B₀" => (4 * g + List.length (orders ++ List.replicate s 0) + t)
local notation "β₀" => generalCoreBaseAngle g orders s t
local notation "θ₀" => generalCoreTheta g orders s t
local notation "hθ₀" => generalCoreTheta_mem g orders s t ho hdef
local notation "ρ₀" => generalCoreAuxPairing g orders s t
local notation "hρ₀" => generalCoreAuxPairing_involutive g orders s t
local notation "hθρ₀" => generalCoreAuxPairing_angle_profile g orders s t
local notation "hp₀" => generalCoreAux_positive_angular_periods g orders s t ho hdef
local notation "PΓ₀" => cofiniteMixedTangentialHalfPlaneData θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hp₀
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ₀ d hθ₀ hd hb
local notation "S₀" => generalCoreAuxSidePairing g orders s t ho hdef d hd hb

/-- The full actual auxiliary stabilizer at an ordinary corner is trivial.
Its genuine corner class contains B distinct labels, of total angle 2*pi;
the complete class-angle formula forces its whole point order to be one. -/
theorem generalCoreBaseCycle_aux_pointOrder_one (a : Fin B₀) :
    fuchsianPointOrder (PΓ₀).cayleyData ((PΓ₀).cayleyCoordinate
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (cofiniteMixedTangentialVertexDisc θ₀ d hθ₀ hd hb
        (generalCoreBaseCycleIndex g orders s t a)))) = 1 := by
  let i := generalCoreBaseCycleIndex g orders s t a
  let R := Relation.EqvGen (fun j k => k = ((ρ₀).trans (finRotate _)) j)
  have hBc : B₀ = generalCoreBaseCount g orders s t := by
    simp [generalCoreBaseCount, Nat.add_assoc]
  have hB : 0 < B₀ := by
    have hh := generalCore_base_count g orders s t hdef
    omega
  have hβ : 0 < β₀ := by
    unfold generalCoreBaseAngle
    have hh : (0 : ℝ) < generalCoreBaseCount g orders s t := by exact_mod_cast (hBc ▸ hB)
    exact div_pos (by positivity) hh
  have hi : 0 < θ₀ i := by rw [generalCoreBaseCycleIndex_angle]; exact hβ
  let f : Fin B₀ → {j // R i j} := fun b =>
    ⟨generalCoreBaseCycleIndex g orders s t b, generalCoreBaseCycleIndex_related g orders s t a b⟩
  have hf : Function.Injective f := by
    intro b c he
    exact generalCoreBaseCycleIndex_injective g orders s t (congrArg Subtype.val he)
  have hcard : B₀ ≤ Fintype.card {j // R i j} := by
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
  have hs : (∑ j : {j // R i j}, θ₀ j.val) = (Fintype.card {j // R i j} : ℝ) * β₀ := by
    calc
      (∑ j : {j // R i j}, θ₀ j.val) = ∑ _j : {j // R i j}, β₀ := by
        apply Finset.sum_congr rfl
        intro j _hj
        exact (cofiniteMixedTangential_corner_relation_angle θ₀ ρ₀ hθρ₀ j.property).trans
          (generalCoreBaseCycleIndex_angle g orders s t a)
      _ = _ := by simp
  have hbase : (B₀ : ℝ) * β₀ = 2 * Real.pi := by
    unfold generalCoreBaseAngle
    rw [← hBc]
    field_simp
    push_cast
    rfl
  have hsum := cofiniteMixedTangential_vertex_class_angle_sum θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀ hp₀ i hi
  rw [hs] at hsum
  have hge : 2 * Real.pi ≤ (Fintype.card {j // R i j} : ℝ) * β₀ := by
    rw [← hbase]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hβ.le
  rw [hsum] at hge
  let m := fuchsianPointOrder (PΓ₀).cayleyData ((PΓ₀).cayleyCoordinate
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (cofiniteMixedTangentialVertexDisc θ₀ d hθ₀ hd hb i)))
  have hm : 0 < m := (PΓ₀).cayleyData.pointOrder_pos _
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hle : (m : ℝ) ≤ 1 := by
    have hh := (le_div_iff₀ hmr).mp hge
    nlinarith [Real.pi_pos]
  have hn : m ≤ 1 := by exact_mod_cast hle
  exact Nat.le_antisymm hn hm

/-- Every physical representative of any original ordinary label has the
entire auxiliary native point stabilizer of order one. -/
theorem generalCoreBaseCycle_stabilizer_card_one
    (i : Fin (generalCoreAngles g orders s t).length) (a : Fin B₀)
    (ha : generalSignatureAuxBaseNat β₀ g (orders ++ List.replicate s 0) a.val = i.val)
    (x : ℍ) (hx : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x) = (Q₀).vertices i) :
    Nat.card (MulAction.stabilizer (S₀).Generated x) = 1 := by
  have hei : generalCoreBaseCycleIndex g orders s t a = i := Fin.ext ha
  have hβ : 0 < β₀ := by
    unfold generalCoreBaseAngle
    have hh : (0 : ℝ) < generalCoreBaseCount g orders s t := by
      have hc := generalCore_base_count g orders s t hdef
      exact_mod_cast (by omega : 0 < generalCoreBaseCount g orders s t)
    exact div_pos (by positivity) hh
  have hi : 0 < θ₀ i := by rw [← hei, generalCoreBaseCycleIndex_angle]; exact hβ
  have hcoord := cofiniteMixedTangentialVertexDisc_coordinate θ₀ d hθ₀ hd hb i hi
  have hxdisc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x = cofiniteMixedTangentialVertexDisc θ₀ d hθ₀ hd hb i :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective (hx.trans hcoord)
  have hxnative : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (cofiniteMixedTangentialVertexDisc θ₀ d hθ₀ hd hb i) = x := by
    rw [← hxdisc, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  calc
    Nat.card (MulAction.stabilizer (S₀).Generated x) =
        Nat.card (MulAction.stabilizer
          (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius (cofiniteMixedTangentialMobiusGroup θ₀ d hθ₀ hd hb ρ₀ hρ₀ hθρ₀))
          ((PΓ₀).cayleyCoordinate x)) :=
      Nat.card_congr (generalCoreAux_projective_disc_stabilizerEquiv g orders s t ho hdef d hd hb x).toEquiv
    _ = 1 := by
      change fuchsianPointOrder (PΓ₀).cayleyData ((PΓ₀).cayleyCoordinate x) = 1
      rw [← hxnative, ← hei]
      exact generalCoreBaseCycle_aux_pointOrder_one g orders s t ho hdef d hd hb a

end ActualOrdinaryCorners
end LowDimensionalTopology.Geometry.Fuchsian
