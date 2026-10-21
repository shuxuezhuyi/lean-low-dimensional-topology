/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureOuterCones
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane Classical
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

/-- The literal appended zero mark of each original cusp occurrence. -/
def generalCoreCuspMarkIndex (orders : List ℕ) (s : ℕ) (j : Fin s) :
    Fin (orders ++ List.replicate s 0).length :=
  ⟨orders.length + j.val, by simp only [List.length_append, List.length_replicate]; omega⟩

theorem generalCoreCuspMarkIndex_getD (orders : List ℕ) (s : ℕ) (j : Fin s) :
    (orders ++ List.replicate s 0).getD (generalCoreCuspMarkIndex orders s j).val 2 = 0 := by
  rw [List.getD_append_right _ _ _ _ (by change orders.length ≤ orders.length + j.val; omega)]
  change (List.replicate s 0).getD (orders.length + j.val - orders.length) 2 = 0
  rw [Nat.add_sub_cancel_left]
  exact List.getD_replicate 0 j.isLt

/-- The genuine original ideal corner corresponding to each cusp label. -/
def generalCoreCuspIndex (g : ℕ) (orders : List ℕ) (s t : ℕ) (j : Fin s) :
    Fin (generalCoreAngles g orders s t).length :=
  generalCoreOuterIndex g orders s t (generalCoreCuspMarkIndex orders s j)
    (by rw [generalCoreCuspMarkIndex_getD]; decide)

theorem generalCoreCuspIndex_angle (g : ℕ) (orders : List ℕ) (s t : ℕ) (j : Fin s) :
    generalCoreTheta g orders s t (generalCoreCuspIndex g orders s t j) = 0 := by
  rw [generalCoreCuspIndex, generalCoreOuterIndex_angle, generalCoreCuspMarkIndex_getD]
  norm_num [cofiniteConstructionConeAngle]

theorem generalCoreCuspIndex_injective (g : ℕ) (orders : List ℕ) (s t : ℕ) :
    Function.Injective (generalCoreCuspIndex g orders s t) := by
  intro j k h
  have hm := generalCoreOuterIndex_injective g orders s t _ _ _ _ h
  have he := congrArg Fin.val hm
  apply Fin.ext
  change orders.length + j.val = orders.length + k.val at he
  omega

theorem generalCoreCuspIndex_step (g : ℕ) (orders : List ℕ) (s t : ℕ) (j : Fin s) :
    ((generalCoreAuxPairing g orders s t).trans (finRotate _))
      (generalCoreCuspIndex g orders s t j) = generalCoreCuspIndex g orders s t j :=
  generalCoreOuterIndex_step g orders s t _ _

theorem generalCoreCuspIndex_class_singleton (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (j : Fin s) (i : Fin (generalCoreAngles g orders s t).length) :
    Relation.EqvGen (fun a b => b = ((generalCoreAuxPairing g orders s t).trans (finRotate _)) a)
      (generalCoreCuspIndex g orders s t j) i ↔ i = generalCoreCuspIndex g orders s t j :=
  generalCoreOuterIndex_class_singleton g orders s t _ _ i

/-- The zero angles of the actual original core are exactly the prescribed
cusp occurrences. In particular no finite cone or boundary corner is counted. -/
theorem generalCoreTheta_zero_iff (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (i : Fin (generalCoreAngles g orders s t).length) :
    generalCoreTheta g orders s t i = 0 ↔ ∃ j : Fin s, generalCoreCuspIndex g orders s t j = i := by
  let β := generalCoreBaseAngle g orders s t
  let ms := orders ++ List.replicate s 0
  let L := generalSignatureAuxAngleList β g ms t
  let e := finCongr (congrArg List.length (generalCoreAngles_eq_auxAngleList g orders s t))
  have hget (n : ℕ) : (generalCoreAngles g orders s t).getD n β = L.getD n β :=
    congrArg (fun A : List ℝ => A.getD n β) (generalCoreAngles_eq_auxAngleList g orders s t)
  have hi : L[e i] = generalCoreTheta g orders s t i := by
    simp only [Fin.getElem_fin]
    rw [← List.getD_eq_getElem L β (e i).isLt]
    change L.getD i.val β = _
    rw [← hget]
    exact List.getD_eq_getElem _ β i.isLt
  have hB := generalCore_base_count g orders s t hdef
  have hβ : 0 < β := by
    dsimp only [β, generalCoreBaseAngle]
    have hp : (0 : ℝ) < generalCoreBaseCount g orders s t := by exact_mod_cast (by omega : 0 < generalCoreBaseCount g orders s t)
    exact div_pos (by positivity) hp
  constructor
  · intro hz
    have hzL : L[e i] = 0 := hi.trans hz
    rcases generalSignatureAux_corner_label_cover β g ms t (e i) with
      ⟨a, ha⟩ | ⟨j, hj, hji⟩ | ⟨j, r, hr⟩
    · have haθ : L[generalSignatureAuxBaseIndex β g ms t a] = β :=
        (List.getD_eq_getElem L β (generalSignatureAuxBaseIndex β g ms t a).isLt).symm.trans
          (generalSignatureAuxBaseNat_angle β g ms t a.val)
      have hzB : L[generalSignatureAuxBaseIndex β g ms t a] = 0 := by
        simpa only [ha] using hzL
      exact (hβ.ne' (haθ.symm.trans hzB)).elim
    · have hjD : ms.getD j.val 2 ≠ 2 := by
        simpa only [List.getD_eq_getElem ms 2 j.isLt, Fin.getElem_fin] using hj
      have hOuter : generalCoreOuterIndex g orders s t j hjD = i := Fin.ext hji
      have hzM : ms.getD j.val 2 = 0 := by
        have hangle := generalCoreOuterIndex_angle g orders s t j hjD
        rw [hOuter, hz] at hangle
        by_contra hm
        have hmR : (0 : ℝ) < ms.getD j.val 2 := by exact_mod_cast (Nat.pos_of_ne_zero hm)
        have hp : 0 < cofiniteConstructionConeAngle (ms.getD j.val 2) := div_pos (by positivity) hmR
        exact hp.ne' hangle.symm
      have hzero : ms[j] = 0 := by
        simpa only [List.getD_eq_getElem ms 2 j.isLt, Fin.getElem_fin] using hzM
      have hjge : orders.length ≤ j.val := by
        by_contra hn
        have hjlt : j.val < orders.length := by omega
        change (orders ++ List.replicate s 0)[j.val] = 0 at hzero
        rw [List.getElem_append_left hjlt] at hzero
        have hm := ho _ (List.getElem_mem hjlt)
        omega
      let k : Fin s := ⟨j.val - orders.length, by
        have hb := j.isLt
        simp only [ms, List.length_append, List.length_replicate] at hb
        omega⟩
      have hmark : j = generalCoreCuspMarkIndex orders s k := by
        apply Fin.ext
        change j.val = orders.length + (j.val - orders.length)
        omega
      refine ⟨k, ?_⟩
      simpa only [hmark, generalCoreCuspIndex] using hOuter
    · have hzR : L[generalSignatureAuxBoundaryRightIndex β g ms t j r] = 0 := by
        simpa only [hr] using hzL
      have hR := generalSignatureAuxBoundaryRightIndex_angle β g ms t j r
      exact ((ne_of_gt (by positivity : (0 : ℝ) < Real.pi / 2)) (hR.symm.trans hzR)).elim
  · rintro ⟨j, rfl⟩
    exact generalCoreCuspIndex_angle g orders s t j

/-- Exact occurrence labels of all original zero corners, preserving the
source count s without identifying any occurrence. -/
def generalCoreCuspLabelEquiv (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t) :
    {i : Fin (generalCoreAngles g orders s t).length // generalCoreTheta g orders s t i = 0} ≃ Fin s :=
  (Equiv.ofBijective (fun j : Fin s =>
    (⟨generalCoreCuspIndex g orders s t j, generalCoreCuspIndex_angle g orders s t j⟩ :
      {i : Fin (generalCoreAngles g orders s t).length // generalCoreTheta g orders s t i = 0}))
    ⟨fun _ _ he => generalCoreCuspIndex_injective g orders s t (congrArg Subtype.val he),
      fun i => by
        obtain ⟨j, hj⟩ := (generalCoreTheta_zero_iff g orders s t ho hdef i.val).mp i.property
        exact ⟨j, Subtype.ext hj⟩⟩).symm

theorem generalCore_zero_angle_card (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t) :
    Nat.card {i : Fin (generalCoreAngles g orders s t).length // generalCoreTheta g orders s t i = 0} = s :=
  (Nat.card_congr (generalCoreCuspLabelEquiv g orders s t ho hdef)).trans (Nat.card_fin s)

/-- Each of these original zero corners is an actual ideal vertex of the
same original polygon, not the finite fallback used by finite-corner code. -/
theorem generalCoreCuspVertex_ideal (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
    (j : Fin s) :
    ‖((_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
      (generalCoreTheta_mem g orders s t ho hdef) hd hb).vertices
      (generalCoreCuspIndex g orders s t j) : ℂ)‖ = 1 :=
  cofiniteTangential_zero_vertex_ideal (generalCoreTheta g orders s t) d
    (generalCoreTheta_mem g orders s t ho hdef) hd _ (generalCoreCuspIndex_angle g orders s t j)

end LowDimensionalTopology.Geometry.Fuchsian
