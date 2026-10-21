/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureOrderTwoCones
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane
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

/-- The unchanged literal side of an order-two occurrence of the original
order list. Appended zero cusp labels do not add order-two occurrences. -/
def generalCoreOrderTwoSideIndex (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : {j : Fin orders.length // orders[j] = 2}) :
    Fin (generalCoreAngles g orders s t).length :=
  ⟨4 * g + cofiniteConstructionMarkBaseNat (orders ++ List.replicate s 0) j.val.val, by
    have hj : j.val.val < (orders ++ List.replicate s 0).length := by
      simpa only [List.length_append, List.length_replicate] using
        lt_of_lt_of_le j.val.isLt (Nat.le_add_right orders.length s)
    have hb := cofiniteConstructionMarkBaseNat_bound (generalCoreBaseAngle g orders s t)
      (orders ++ List.replicate s 0) j.val.val hj
    have hlen := (congrArg List.length (generalCoreAngles_eq_auxAngleList g orders s t)).trans
      (generalSignatureAuxAngleList_length (generalCoreBaseAngle g orders s t) g
        (orders ++ List.replicate s 0) t)
    simp only [cofiniteConstructionSideAngles, List.length_append, List.length_replicate] at hlen
    omega⟩

/-- Its numerical position is strictly inside the original handle/cone/cusp
prefix, so a true order-two side is never one of the new cut sides. -/
theorem generalCoreOrderTwoSideIndex_prefix (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : {j : Fin orders.length // orders[j] = 2}) :
    (generalCoreOrderTwoSideIndex g orders s t j).val <
      (cofiniteConstructionSideAngles (generalCoreBaseAngle g orders s t) g
        (orders ++ List.replicate s 0)).length := by
  have hj : j.val.val < (orders ++ List.replicate s 0).length := by
    simp only [List.length_append, List.length_replicate]
    omega
  have hb := cofiniteConstructionMarkBaseNat_bound (generalCoreBaseAngle g orders s t)
    (orders ++ List.replicate s 0) j.val.val hj
  simp only [cofiniteConstructionSideAngles, List.length_append, List.length_replicate]
  exact Nat.add_lt_add_left hb _

theorem generalCoreOrderTwoSideIndex_noncut (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : {j : Fin orders.length // orders[j] = 2}) :
    ¬ generalCoreIsCutSide g orders s t (generalCoreOrderTwoSideIndex g orders s t j) := by
  intro h
  exact (not_le_of_gt (generalCoreOrderTwoSideIndex_prefix g orders s t j)) h.1

theorem generalCoreOrderTwoSideIndex_fixed (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : {j : Fin orders.length // orders[j] = 2}) :
    generalCoreAuxPairing g orders s t (generalCoreOrderTwoSideIndex g orders s t j) =
      generalCoreOrderTwoSideIndex g orders s t j := by
  let ms := orders ++ List.replicate s 0
  have hj : j.val.val < ms.length := by simp only [ms, List.length_append, List.length_replicate]; omega
  let k : Fin ms.length := ⟨j.val.val, hj⟩
  have hk : ms[k] = 2 := by
    change (orders ++ List.replicate s 0)[j.val.val] = 2
    simpa only [Fin.getElem_fin, List.getElem_append_left j.val.isLt] using j.property
  apply Fin.ext
  rw [generalCoreAuxPairing_val]
  change generalSignatureAuxPairNat (generalCoreBaseAngle g orders s t) g ms _ = _
  rw [generalSignatureAuxPairNat, ite_eq_left
    (generalCoreOrderTwoSideIndex_prefix g orders s t j)]
  exact (cofiniteConstructionPairNat_fixed_iff (generalCoreBaseAngle g orders s t) g ms _
    (generalCoreOrderTwoSideIndex_prefix g orders s t j)).mpr ⟨k, hk, rfl⟩

/-- Repeated equal orders retain their separate original occurrence labels. -/
theorem generalCoreOrderTwoSideIndex_injective (g : ℕ) (orders : List ℕ) (s t : ℕ) :
    Function.Injective (generalCoreOrderTwoSideIndex g orders s t) := by
  intro i j h
  apply Subtype.ext
  apply Fin.ext
  apply cofiniteConstructionMarkBaseNat_injective (orders ++ List.replicate s 0)
  exact Nat.add_left_cancel (congrArg Fin.val h)

/-- All and only retained auxiliary self-sides are the original order-two
occurrences. The appended cusps are zero and the new boundary self-sides
are exactly the omitted cuts. -/
theorem generalCoreNoncutSelfSide_iff (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (i : Fin (generalCoreAngles g orders s t).length) :
    (¬ generalCoreIsCutSide g orders s t i ∧ generalCoreAuxPairing g orders s t i = i) ↔
      ∃ j : {j : Fin orders.length // orders[j] = 2}, generalCoreOrderTwoSideIndex g orders s t j = i := by
  let β := generalCoreBaseAngle g orders s t
  let ms := orders ++ List.replicate s 0
  let p := (cofiniteConstructionSideAngles β g ms).length
  constructor
  · rintro ⟨hncut, hself⟩
    have hval := congrArg Fin.val hself
    rw [generalCoreAuxPairing_val] at hval
    change generalSignatureAuxPairNat β g ms i.val = i.val at hval
    have hip : i.val < p := by
      by_contra hge
      change (if i.val < p then _ else _) = i.val at hval
      rw [ite_eq_right hge] at hval
      change p + generalSignatureAuxBoundaryPairNat (i.val - p) = i.val at hval
      have hfix : generalSignatureAuxBoundaryPairNat (i.val - p) = i.val - p := by omega
      have hmod := (generalSignatureAuxBoundaryPairNat_fixed_iff (i.val - p)).mp hfix
      apply hncut
      change p ≤ i.val ∧ (i.val - p) % 3 = 1
      exact ⟨by omega, hmod⟩
    rw [generalSignatureAuxPairNat, ite_eq_left hip] at hval
    obtain ⟨k, hk, hki⟩ := (cofiniteConstructionPairNat_fixed_iff β g ms i.val hip).mp hval
    have hkord : k.val < orders.length := by
      by_contra hge
      have hget : ms.getD k.val 0 = 2 := by
        rw [List.getD_eq_getElem _ 0 k.isLt]
        exact hk
      change (orders ++ List.replicate s 0).getD k.val 0 = 2 at hget
      rw [List.getD_append_right _ _ _ _ (by omega)] at hget
      simp at hget
    let j : Fin orders.length := ⟨k.val, hkord⟩
    have hj : orders[j] = 2 := by
      have h := hk
      change (orders ++ List.replicate s 0)[k.val] = 2 at h
      change orders[k.val] = 2
      simpa only [List.getElem_append_left hkord] using h
    exact ⟨⟨j, hj⟩, Fin.ext hki⟩
  · rintro ⟨j, rfl⟩
    exact ⟨generalCoreOrderTwoSideIndex_noncut g orders s t j,
      generalCoreOrderTwoSideIndex_fixed g orders s t j⟩

/-- The complete actual retained self-side label set is exactly the original
order-two occurrence set, preserving repeated occurrences separately. -/
def generalCoreOrderTwoSideLabelEquiv (g : ℕ) (orders : List ℕ) (s t : ℕ) :
    {i : Fin (generalCoreAngles g orders s t).length //
      ¬ generalCoreIsCutSide g orders s t i ∧ generalCoreAuxPairing g orders s t i = i} ≃
      {j : Fin orders.length // orders[j] = 2} :=
  (Equiv.ofBijective (fun j : {j : Fin orders.length // orders[j] = 2} =>
    (⟨generalCoreOrderTwoSideIndex g orders s t j,
      generalCoreOrderTwoSideIndex_noncut g orders s t j,
      generalCoreOrderTwoSideIndex_fixed g orders s t j⟩ :
      {i : Fin (generalCoreAngles g orders s t).length //
        ¬ generalCoreIsCutSide g orders s t i ∧ generalCoreAuxPairing g orders s t i = i}))
    ⟨fun _ _ he => generalCoreOrderTwoSideIndex_injective g orders s t (congrArg Subtype.val he),
      fun i => by
        obtain ⟨j, hj⟩ := (generalCoreNoncutSelfSide_iff g orders s t i.val).mp i.property
        exact ⟨j, Subtype.ext hj⟩⟩).symm

variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
  (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
  (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)

/-- The actual native point for each original order-two occurrence. -/
def generalCoreOrderTwoPoint (j : {j : Fin orders.length // orders[j] = 2}) : ℍ :=
  generalCoreSelfSideFoot g orders s t d hd (generalCoreOrderTwoSideIndex g orders s t j)

/-- Each original order-two occurrence has exactly order two in the full
actual target stabilizer, without any extra geometric premise. -/
theorem generalCoreOrderTwoPoint_stabilizer_card
    (j : {j : Fin orders.length // orders[j] = 2}) :
    Nat.card (MulAction.stabilizer (generalCoreTargetGroup g orders s t ho hdef d hd hb)
      (generalCoreOrderTwoPoint g orders s t d hd j)) = 2 :=
  generalCoreSelfSideFoot_target_stabilizer_card g orders s t ho hdef d hd hb
    (generalCoreOrderTwoSideIndex g orders s t j)
    (generalCoreOrderTwoSideIndex_noncut g orders s t j)
    (generalCoreOrderTwoSideIndex_fixed g orders s t j)

/-- Repeated order-two occurrences remain distinct under the entire actual
original target group, rather than only under selected generators. -/
theorem generalCoreOrderTwoPoint_orbit_injective
    (i j : {j : Fin orders.length // orders[j] = 2})
    (a : generalCoreTargetGroup g orders s t ho hdef d hd hb)
    (ha : a.val (generalCoreOrderTwoPoint g orders s t d hd i) =
      generalCoreOrderTwoPoint g orders s t d hd j) : i = j :=
  generalCoreOrderTwoSideIndex_injective g orders s t
    (generalCoreSelfSideFoot_target_orbit_injective g orders s t ho hdef d hd hb
      (generalCoreOrderTwoSideIndex g orders s t i) (generalCoreOrderTwoSideIndex g orders s t j)
      (generalCoreOrderTwoSideIndex_fixed g orders s t i)
      (generalCoreOrderTwoSideIndex_fixed g orders s t j) a ha)

/-- No original order-two occurrence is identified with any actual original
finite vertex, including a cone of higher order or an ordinary corner. -/
theorem generalCoreOrderTwoPoint_not_vertex_orbit
    (i : {j : Fin orders.length // orders[j] = 2})
    (j : Fin (generalCoreAngles g orders s t).length) (x : ℍ)
    (hx : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x) =
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
        (generalCoreTheta_mem g orders s t ho hdef) hd hb).vertices j)
    (a : generalCoreTargetGroup g orders s t ho hdef d hd hb)
    (ha : a.val (generalCoreOrderTwoPoint g orders s t d hd i) = x) : False :=
  generalCoreSelfSideFoot_not_target_vertex_orbit g orders s t ho hdef d hd hb
    (generalCoreOrderTwoSideIndex g orders s t i) j
    (generalCoreOrderTwoSideIndex_fixed g orders s t i) x hx a ha

end LowDimensionalTopology.Geometry.Fuchsian
