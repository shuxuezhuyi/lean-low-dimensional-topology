/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureOrderTwoLabels
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureOuterCones
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

/-- The literal original order occurrence inside the unchanged list obtained
by appending zero cusp labels. Its numerical position is unchanged. -/
def generalCoreOrderMarkIndex (orders : List ℕ) (s : ℕ) (j : Fin orders.length) :
    Fin (orders ++ List.replicate s 0).length :=
  ⟨j.val, by simp only [List.length_append, List.length_replicate]; omega⟩

theorem generalCoreOrderMarkIndex_getD (orders : List ℕ) (s : ℕ) (j : Fin orders.length) :
    (orders ++ List.replicate s 0).getD (generalCoreOrderMarkIndex orders s j).val 2 = orders[j] := by
  change (orders ++ List.replicate s 0).getD j.val 2 = orders[j]
  have hj : j.val < (orders ++ List.replicate s 0).length := by
    simp only [List.length_append, List.length_replicate]
    omega
  simp only [List.getD_eq_getElem _ 2 hj, List.getElem_append_left j.isLt, Fin.getElem_fin]

variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
  (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
  (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)

/-- The actual native cone point for every original order occurrence. The
order-two contact and higher-order finite vertex remain distinct geometries. -/
def generalCoreConePoint (j : Fin orders.length) : ℍ :=
  if hj : orders[j] = 2 then generalCoreOrderTwoPoint g orders s t d hd ⟨j, hj⟩
  else generalCoreOuterPoint g orders s t ho hdef d hd hb (generalCoreOrderMarkIndex orders s j)
    (by rw [generalCoreOrderMarkIndex_getD]; exact hj)

theorem generalCoreConePoint_of_two (j : Fin orders.length) (hj : orders[j] = 2) :
    generalCoreConePoint g orders s t ho hdef d hd hb j =
      generalCoreOrderTwoPoint g orders s t d hd ⟨j, hj⟩ := by
  simp only [generalCoreConePoint, dite_eq_left hj]

theorem generalCoreConePoint_of_ne_two (j : Fin orders.length) (hj : orders[j] ≠ 2) :
    generalCoreConePoint g orders s t ho hdef d hd hb j =
      generalCoreOuterPoint g orders s t ho hdef d hd hb (generalCoreOrderMarkIndex orders s j)
        (by rw [generalCoreOrderMarkIndex_getD]; exact hj) := by
  simp only [generalCoreConePoint, dite_eq_right hj]

/-- Every original order occurrence has precisely its prescribed whole
target stabilizer order. No chosen cyclic subgroup supplies this order. -/
theorem generalCoreConePoint_stabilizer_card (j : Fin orders.length) :
    Nat.card (MulAction.stabilizer (generalCoreTargetGroup g orders s t ho hdef d hd hb)
      (generalCoreConePoint g orders s t ho hdef d hd hb j)) = orders[j] := by
  have hjmin : 2 ≤ orders[j] := ho _ (List.getElem_mem j.isLt)
  by_cases hj : orders[j] = 2
  · rw [generalCoreConePoint_of_two g orders s t ho hdef d hd hb j hj, hj]
    exact generalCoreOrderTwoPoint_stabilizer_card g orders s t ho hdef d hd hb ⟨j, hj⟩
  · rw [generalCoreConePoint_of_ne_two g orders s t ho hdef d hd hb j hj]
    have hm : 3 ≤ (orders ++ List.replicate s 0).getD (generalCoreOrderMarkIndex orders s j).val 2 := by
      rw [generalCoreOrderMarkIndex_getD]
      omega
    simpa only [generalCoreOrderMarkIndex_getD] using
      generalCoreOuterPoint_target_stabilizer_card g orders s t ho hdef d hd hb
        (generalCoreOrderMarkIndex orders s j) hm

/-- Different original list occurrences remain distinct under the entire
actual target group, even when their prescribed orders are equal. -/
theorem generalCoreConePoint_orbit_injective (j k : Fin orders.length)
    (a : generalCoreTargetGroup g orders s t ho hdef d hd hb)
    (ha : a.val (generalCoreConePoint g orders s t ho hdef d hd hb j) =
      generalCoreConePoint g orders s t ho hdef d hd hb k) : j = k := by
  have hjmin : 2 ≤ orders[j] := ho _ (List.getElem_mem j.isLt)
  have hkmin : 2 ≤ orders[k] := ho _ (List.getElem_mem k.isLt)
  by_cases hj : orders[j] = 2 <;> by_cases hk : orders[k] = 2
  · rw [generalCoreConePoint_of_two g orders s t ho hdef d hd hb j hj,
      generalCoreConePoint_of_two g orders s t ho hdef d hd hb k hk] at ha
    exact congrArg Subtype.val
      (generalCoreOrderTwoPoint_orbit_injective g orders s t ho hdef d hd hb ⟨j, hj⟩ ⟨k, hk⟩ a ha)
  · rw [generalCoreConePoint_of_two g orders s t ho hdef d hd hb j hj,
      generalCoreConePoint_of_ne_two g orders s t ho hdef d hd hb k hk] at ha
    have hmk : 3 ≤ (orders ++ List.replicate s 0).getD (generalCoreOrderMarkIndex orders s k).val 2 := by
      rw [generalCoreOrderMarkIndex_getD]
      omega
    exact False.elim (generalCoreOrderTwoPoint_not_vertex_orbit g orders s t ho hdef d hd hb
      ⟨j, hj⟩ (generalCoreOuterIndex g orders s t (generalCoreOrderMarkIndex orders s k) (by omega)) _
      (generalCoreOuterPoint_coordinate g orders s t ho hdef d hd hb
        (generalCoreOrderMarkIndex orders s k) hmk) a ha)
  · rw [generalCoreConePoint_of_ne_two g orders s t ho hdef d hd hb j hj,
      generalCoreConePoint_of_two g orders s t ho hdef d hd hb k hk] at ha
    have hmj : 3 ≤ (orders ++ List.replicate s 0).getD (generalCoreOrderMarkIndex orders s j).val 2 := by
      rw [generalCoreOrderMarkIndex_getD]
      omega
    have hrev : (a⁻¹).val (generalCoreOrderTwoPoint g orders s t d hd ⟨k, hk⟩) =
        generalCoreOuterPoint g orders s t ho hdef d hd hb
          (generalCoreOrderMarkIndex orders s j) (by rw [generalCoreOrderMarkIndex_getD]; exact hj) := by
      rw [← ha]
      exact a.val.symm_apply_apply _
    exact False.elim (generalCoreOrderTwoPoint_not_vertex_orbit g orders s t ho hdef d hd hb
      ⟨k, hk⟩ (generalCoreOuterIndex g orders s t (generalCoreOrderMarkIndex orders s j) (by omega)) _
      (generalCoreOuterPoint_coordinate g orders s t ho hdef d hd hb
        (generalCoreOrderMarkIndex orders s j) hmj) a⁻¹ hrev)
  · rw [generalCoreConePoint_of_ne_two g orders s t ho hdef d hd hb j hj,
      generalCoreConePoint_of_ne_two g orders s t ho hdef d hd hb k hk] at ha
    have hmj : 3 ≤ (orders ++ List.replicate s 0).getD (generalCoreOrderMarkIndex orders s j).val 2 := by
      rw [generalCoreOrderMarkIndex_getD]
      omega
    have hmk : 3 ≤ (orders ++ List.replicate s 0).getD (generalCoreOrderMarkIndex orders s k).val 2 := by
      rw [generalCoreOrderMarkIndex_getD]
      omega
    have he := generalCoreOuterPoint_target_orbit_injective g orders s t ho hdef d hd hb
      (generalCoreOrderMarkIndex orders s j) (generalCoreOrderMarkIndex orders s k) hmj hmk a ha
    apply Fin.ext
    exact congrArg (fun z : Fin (orders ++ List.replicate s 0).length => z.val) he

end LowDimensionalTopology.Geometry.Fuchsian
