/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureCutAxisIncidence
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
open Set Topology
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

local notation "Qcore" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
  (generalCoreTheta_mem g orders s t ho hdef) hd hb
local notation "Pcore" => _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Qcore
local notation "Saux" => generalCoreAuxSidePairing g orders s t ho hdef d hd hb
local notation "Ecore" => _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Qcore
local notation "idx" => generalCoreBoundarySideIndex g orders s t
local notation "Ccut" => generalCoreCutSegment g orders s t ho hdef d hd hb
local notation "Kcut" => (fun j : Fin t => _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier (_root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonLine Qcore (idx j 1)))
local notation "Fcut" => (fun j : Fin t => generalCoreTargetGenerator g orders s t ho hdef d hd hb (idx j 0))

/-- The actual boundary translation preserves the complete actual cut axis. -/
theorem generalCoreBoundaryGenerator_axis_image (j : Fin t) :
    Fcut j '' Kcut j = Kcut j := by
  have h := generalSignature_zpow_saturation_image (Fcut j) (Ccut j)
  simpa only [generalCoreCutSegment_zpow_cover g orders s t ho hdef d hd hb j] using h

/-- Every actual original pairing map incident to a cut point preserves the
complete support of that very same cut, including at either finite right corner. -/
theorem generalCoreCutSegment_side_support (j : Fin t) (z : ℍ) (hz : z ∈ Ccut j)
    (a : (Pcore).Side) (ha : z ∈ a.val) : (Saux).element a '' Kcut j = Kcut j := by
  have hn0 := generalCoreBoundarySideIndex_next_zero g orders s t j
  have hn1 := generalCoreBoundarySideIndex_next_one g orders s t j
  have hinc := generalSignature_cut_side_incidence Qcore (idx j 0) z
    (by simpa only [hn0, generalCoreCutSegment] using hz) a ha
  simp only [hn0, hn1] at hinc
  have he0 : (Saux).element (Ecore (idx j 0)) = Fcut j := by
    change cofiniteTangentPairingElement _ _ _ _ _
      ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Qcore).symm (Ecore (idx j 0)))
      (generalCoreAuxPairing g orders s t ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Qcore).symm (Ecore (idx j 0)))) = _
    rw [Equiv.symm_apply_apply]
    rfl
  have hp0 : (Saux).paired (Ecore (idx j 0)) = Ecore (idx j 2) := by
    change Ecore (generalCoreAuxPairing g orders s t
      ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Qcore).symm (Ecore (idx j 0)))) = _
    rw [Equiv.symm_apply_apply, generalCoreBoundarySideIndex_pair_zero]
  rcases hinc with rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · apply generalSignature_side_image_support Qcore (idx j 1)
    have hs := (Saux).side_image (Ecore (idx j 1))
    have hp1 : (Saux).paired (Ecore (idx j 1)) = Ecore (idx j 1) := by
      change Ecore (generalCoreAuxPairing g orders s t
        ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Qcore).symm (Ecore (idx j 1)))) = _
      rw [Equiv.symm_apply_apply, generalCoreBoundarySideIndex_pair_one]
    rw [hp1] at hs
    exact hs
  · rw [he0]
    exact generalCoreBoundaryGenerator_axis_image g orders s t ho hdef d hd hb j
  · have hinv := (Saux).element_paired (Ecore (idx j 0))
    rw [hp0, he0] at hinv
    rw [hinv]
    exact MulAction.mem_stabilizer_iff.mp
      ((MulAction.stabilizer (ℍ ≃ᵢ ℍ) (Kcut j)).inv_mem
        (MulAction.mem_stabilizer_iff.mpr
          (generalCoreBoundaryGenerator_axis_image g orders s t ho hdef d hd hb j)))

/-- Different prescribed cuts cannot meet in the actual original polygon;
the original side incidence and literal triple indices determine the label. -/
theorem generalCoreCutSegment_label_unique (j k : Fin t) (z : ℍ)
    (hzj : z ∈ Ccut j) (hzk : z ∈ Ccut k) : j = k := by
  have hinc := generalSignature_cut_side_incidence Qcore (idx j 0) z
    (by simpa only [generalCoreBoundarySideIndex_next_zero, generalCoreCutSegment] using hzj)
    (Ecore (idx k 1)) hzk
  simp only [generalCoreBoundarySideIndex_next_zero, generalCoreBoundarySideIndex_next_one] at hinc
  rcases hinc with he | ⟨_, he⟩ | ⟨_, he⟩
  all_goals
    have hi := congrArg Fin.val ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Qcore).injective he)
    change _ + 3 * k.val + 1 = _ + 3 * j.val + _ at hi
    apply Fin.ext
    omega

/-- The actual physical complete cut support, as well as its original cut
label, is preserved throughout the full original gluing relation. -/
theorem generalCoreCutSegment_gluing_support (j : Fin t) (a b : (Saux).Copy)
    (hab : Relation.EqvGen (Saux).Step a b) (ha : a.2.val ∈ Ccut j) :
    b.2.val ∈ Ccut j ∧ a.1.val '' Kcut j = b.1.val '' Kcut j := by
  have hstep (L : Set ℍ) (a b : (Saux).Copy) (hab : (Saux).Step a b)
      (ha : a.2.val ∈ Ccut j ∧ a.1.val '' Kcut j = L) :
      b.2.val ∈ Ccut j ∧ b.1.val '' Kcut j = L := by
    rcases hab with rfl | ⟨side, hside, hpoint, hindex⟩
    · exact ha
    · have hpoint' : b.2.val ∈ Ccut j := by
        rw [hpoint]
        exact generalCoreCutSegment_side_step g orders s t ho hdef d hd hb j _ ha.1 side hside
      have hsupport := generalCoreCutSegment_side_support g orders s t ho hdef d hd hb
        j a.2.val ha.1 side hside
      have heq : a.1.val = b.1.val * (Saux).element side := congrArg Subtype.val hindex
      have himage : a.1.val '' Kcut j = b.1.val '' Kcut j := by
        calc
          a.1.val '' Kcut j = (fun z => b.1.val ((Saux).element side z)) '' Kcut j := by
            rw [heq]
            rfl
          _ = b.1.val '' ((Saux).element side '' Kcut j) := by rw [image_image]
          _ = b.1.val '' Kcut j := by rw [hsupport]
      exact ⟨hpoint', himage.symm.trans ha.2⟩
  have hchain (L : Set ℍ) (a b : (Saux).Copy) (hab : Relation.EqvGen (Saux).Step a b) :
      (a.2.val ∈ Ccut j ∧ a.1.val '' Kcut j = L) ↔
      (b.2.val ∈ Ccut j ∧ b.1.val '' Kcut j = L) := by
    induction hab with
    | rel a b hab => exact ⟨hstep L a b hab, hstep L b a ((Saux).step_symm hab)⟩
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b c _ _ ihab ihbc => exact ihab.trans ihbc
  have hb := (hchain (a.1.val '' Kcut j) a b hab).mp ⟨ha, rfl⟩
  exact ⟨hb.1, hb.2.symm⟩

/-- Two actual auxiliary translates of original cut segments can meet only
with the same original boundary label and the same complete physical axis. -/
theorem generalCoreCutSegment_translated_incidence (γ δ : (Saux).Generated)
    (j k : Fin t) (z w : ℍ) (hz : z ∈ Ccut j) (hw : w ∈ Ccut k)
    (he : γ.val z = δ.val w) : j = k ∧ γ.val '' Kcut j = δ.val '' Kcut k := by
  let a : (Saux).Copy := (γ, ⟨z, (Pcore).side_subset_carrier (Ecore (idx j 1)) hz⟩)
  let b : (Saux).Copy := (δ, ⟨w, (Pcore).side_subset_carrier (Ecore (idx k 1)) hw⟩)
  have hproj : (Saux).project a = (Saux).project b := by
    apply generalCoreAux_evaluation_injective g orders s t ho hdef d hd hb
    exact he
  have hchain := ((Saux).project_eq_iff a b).mp hproj
  obtain ⟨hwj, hsupport⟩ := generalCoreCutSegment_gluing_support g orders s t ho hdef d hd hb
    j a b hchain hz
  have hjk := generalCoreCutSegment_label_unique g orders s t ho hdef d hd hb j k w hwj hw
  subst k
  exact ⟨rfl, hsupport⟩

/-- All powers of the actual retained boundary generator preserve its
complete native cut axis. -/
theorem generalCoreBoundaryGenerator_axis_zpow_image (j : Fin t) (m : ℤ) :
    (Fcut j ^ m) '' Kcut j = Kcut j :=
  MulAction.mem_stabilizer_iff.mp
    ((MulAction.stabilizer (ℍ ≃ᵢ ℍ) (Kcut j)).zpow_mem
      (MulAction.mem_stabilizer_iff.mpr
        (generalCoreBoundaryGenerator_axis_image g orders s t ho hdef d hd hb j)) m)

/-- The complete actual auxiliary cut axes have no transverse or isolated
incidence: any intersection forces equality of their entire physical supports
and of their original prescribed boundary labels. -/
theorem generalCoreCutAxis_translated_incidence (γ δ : (Saux).Generated)
    (j k : Fin t) (x : ℍ) (hxγ : x ∈ γ.val '' Kcut j) (hxδ : x ∈ δ.val '' Kcut k) :
    j = k ∧ γ.val '' Kcut j = δ.val '' Kcut k := by
  obtain ⟨z, hz, heγ⟩ := hxγ
  obtain ⟨w, hw, heδ⟩ := hxδ
  dsimp only at hz hw
  rw [← generalCoreCutSegment_zpow_cover g orders s t ho hdef d hd hb j] at hz
  rw [← generalCoreCutSegment_zpow_cover g orders s t ho hdef d hd hb k] at hw
  obtain ⟨m, u, hu, hmu⟩ := mem_iUnion.mp hz
  obtain ⟨n, v, hv, hnv⟩ := mem_iUnion.mp hw
  let Fj : (Saux).Generated := ⟨Fcut j,
    generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb
      (generalCoreBoundarySideIndex_generator_mem g orders s t ho hdef d hd hb j)⟩
  let Fk : (Saux).Generated := ⟨Fcut k,
    generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb
      (generalCoreBoundarySideIndex_generator_mem g orders s t ho hdef d hd hb k)⟩
  have hjpow : (Fj ^ m).val = Fcut j ^ m := map_zpow (Saux).Generated.subtype Fj m
  have hkpow : (Fk ^ n).val = Fcut k ^ n := map_zpow (Saux).Generated.subtype Fk n
  have he : (γ * Fj ^ m).val u = (δ * Fk ^ n).val v := by
    change γ.val ((Fj ^ m).val u) = δ.val ((Fk ^ n).val v)
    rw [hjpow, hkpow, hmu, hnv]
    exact heγ.trans heδ.symm
  obtain ⟨hjk, hsupport⟩ := generalCoreCutSegment_translated_incidence
    g orders s t ho hdef d hd hb (γ * Fj ^ m) (δ * Fk ^ n) j k u v hu hv he
  have hγsupport : (γ * Fj ^ m).val '' Kcut j = γ.val '' Kcut j := by
    calc
      (γ * Fj ^ m).val '' Kcut j = γ.val '' ((Fj ^ m).val '' Kcut j) := by
        rw [image_image]
        rfl
      _ = γ.val '' Kcut j := by
        rw [hjpow, generalCoreBoundaryGenerator_axis_zpow_image]
  have hδsupport : (δ * Fk ^ n).val '' Kcut k = δ.val '' Kcut k := by
    calc
      (δ * Fk ^ n).val '' Kcut k = δ.val '' ((Fk ^ n).val '' Kcut k) := by
        rw [image_image]
        rfl
      _ = δ.val '' Kcut k := by
        rw [hkpow, generalCoreBoundaryGenerator_axis_zpow_image]
  exact ⟨hjk, hγsupport.symm.trans (hsupport.trans hδsupport)⟩

end LowDimensionalTopology.Geometry.Fuchsian
