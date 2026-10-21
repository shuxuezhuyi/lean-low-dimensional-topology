/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetCayleyPoints
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureBaseCycleOrderOne
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
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
local notation "β₀" => generalCoreBaseAngle g orders s t
local notation "ms₀" => orders ++ List.replicate s 0
local notation "θ₀" => generalCoreTheta g orders s t
local notation "hθ₀" => generalCoreTheta_mem g orders s t ho hdef
local notation "ρ₀" => generalCoreAuxPairing g orders s t
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ₀ d hθ₀ hd hb
local notation "S₀" => generalCoreAuxSidePairing g orders s t ho hdef d hd hb
local notation "H₀" => generalCoreTargetGroup g orders s t ho hdef d hd hb
local notation "W₀" => generalCoreCutWallUnion g orders s t ho hdef d hd hb

/-- Every nonvertex of the actual original polygon fixed by a nontrivial
target element is one of the original order-two occurrences. -/
theorem generalCoreTarget_nonvertex_cone (x : ℍ)
    (hx : x ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).carrier) (hxW : x ∉ W₀)
    (hxv : x ∉ _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q₀)
    (a : H₀) (ha : a ≠ 1) (hfix : a.val x = x) :
    ∃ j : Fin orders.length, x = generalCoreConePoint g orders s t ho hdef d hd hb j := by
  let γ : (S₀).Generated := ⟨a.val, generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb a.property⟩
  have hγne : γ ≠ 1 := by
    intro he
    exact ha (Subtype.ext (congrArg (fun z : (S₀).Generated => z.val) he))
  rcases cofiniteMixedTangential_nonvertex_closed_incidence θ₀ d hθ₀ hd hb ρ₀
      (generalCoreAuxPairing_involutive g orders s t)
      (generalCoreAuxPairing_angle_profile g orders s t)
      (generalCoreAux_positive_angular_periods g orders s t ho hdef)
      x hx hxv γ x hx hfix with hγone | ⟨i, hxi, hγi⟩
  · exact False.elim (hγne hγone)
  · let side := _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i
    have hγi' : γ = ((S₀).generator side)⁻¹ := hγi
    have hinv : ((S₀).generator side)⁻¹ • x = x := by rw [← hγi']; exact hfix
    have hgen : (S₀).generator side • x = x := by
      calc
        (S₀).generator side • x = (S₀).generator side • (((S₀).generator side)⁻¹ • x) := congrArg _ hinv.symm
        _ = x := smul_inv_smul _ _
    have hself : ρ₀ i = i := by
      have hxpair : x ∈ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ (ρ₀ i) := by
        have h : (S₀).element side x ∈ ((S₀).paired side).val := by
          rw [← (S₀).side_image side]
          exact ⟨x, hxi, rfl⟩
        have he : (S₀).element side x = x := hgen
        rw [he] at h
        have hp := cofiniteTangentialJordanSidePairing_paired_index θ₀ d hθ₀ hd hb ρ₀
          (generalCoreAuxPairing_involutive g orders s t)
          (generalCoreAuxPairing_angle_profile g orders s t) i
        have hp' : (S₀).paired side = _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ (ρ₀ i) := hp
        rw [hp'] at h
        exact h
      by_contra hne
      exact hxv (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygon_common_sides_vertex Q₀ hne hxpair hxi)
    have hnoncut : ¬ generalCoreIsCutSide g orders s t i := by
      intro hcut
      obtain ⟨j, hj⟩ := (generalCoreIsCutSide_iff g orders s t i).mp hcut
      apply hxW
      have hxcut : x ∈ generalCoreCutSegment g orders s t ho hdef d hd hb j := by
        unfold generalCoreCutSegment
        rw [← hj]
        exact hxi
      exact mem_iUnion.mpr ⟨1, x, mem_iUnion.mpr ⟨j, hxcut⟩, rfl⟩
    obtain ⟨j, hj⟩ := (generalCoreNoncutSelfSide_iff g orders s t i).mp ⟨hnoncut, hself⟩
    have hxfoot : x = generalCoreSelfSideFoot g orders s t d hd i := by
      have hf : cofiniteTangentPairingElement θ₀ d hθ₀ hd hb i i x = x := by
        change (S₀).element side x = x at hgen
        have helem : (S₀).element side = cofiniteTangentPairingElement θ₀ d hθ₀ hd hb i (ρ₀ i) :=
          cofiniteTangentialJordanSidePairing_element_index θ₀ d hθ₀ hd hb ρ₀
            (generalCoreAuxPairing_involutive g orders s t)
            (generalCoreAuxPairing_angle_profile g orders s t) i
        rw [helem, hself] at hgen
        exact hgen
      exact cofiniteTangentPairingElement_fixed_subsingleton θ₀ d hθ₀ hd hb i i hf
        (cofiniteTangentPairingElement_self_foot θ₀ d hθ₀ hd hb i)
    refine ⟨j.val, ?_⟩
    rw [generalCoreConePoint_of_two g orders s t ho hdef d hd hb j.val j.property]
    change x = generalCoreSelfSideFoot g orders s t d hd (generalCoreOrderTwoSideIndex g orders s t j)
    rw [hj]
    exact hxfoot

/-- A genuine finite original vertex fixed by a nontrivial target element
is a listed higher-order cone; ordinary corners and actual boundary corners
are excluded by proved full stabilizer and cut-wall geometry. -/
theorem generalCoreTarget_vertex_cone (x : ℍ)
    (_hx : x ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).carrier) (hxW : x ∉ W₀)
    (i : Fin (generalCoreAngles g orders s t).length)
    (hxi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x) = (Q₀).vertices i)
    (a : H₀) (ha : a ≠ 1) (hfix : a.val x = x) :
    ∃ j : Fin orders.length, x = generalCoreConePoint g orders s t ho hdef d hd hb j := by
  let e := finCongr (congrArg List.length (generalCoreAngles_eq_auxAngleList g orders s t))
  rcases generalSignatureAux_corner_label_cover β₀ g ms₀ t (e i) with
    ⟨b, hbase⟩ | ⟨j, hj, hji⟩ | ⟨j, r, hjr⟩
  · have hbi : generalSignatureAuxBaseNat β₀ g ms₀ b.val = i.val := congrArg Fin.val hbase
    have hc := generalCoreBaseCycle_stabilizer_card_one g orders s t ho hdef d hd hb i b hbi x hxi
    let γ : MulAction.stabilizer (S₀).Generated x :=
      ⟨⟨a.val, generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb a.property⟩, hfix⟩
    have hγ : γ = 1 := (Nat.card_eq_one_iff_unique.mp hc).1.elim γ 1
    exact False.elim (ha (Subtype.ext (congrArg (fun z : MulAction.stabilizer (S₀).Generated x => z.val.val) hγ)))
  · have hjget : (ms₀).getD j.val 2 ≠ 2 := by simpa only [List.getD_eq_getElem _ 2 j.isLt, Fin.getElem_fin] using hj
    have hii : generalCoreOuterIndex g orders s t j hjget = i := Fin.ext hji
    have hiangle : 0 < θ₀ i := cofiniteTangential_native_vertex_positive θ₀ d hθ₀ hd hb i x hxi.symm
    have hjpos : 0 < cofiniteConstructionConeAngle ((ms₀).getD j.val 2) := by
      rw [← generalCoreOuterIndex_angle g orders s t j hjget, hii]
      exact hiangle
    have hjzero : (ms₀).getD j.val 2 ≠ 0 := by
      intro hz
      rw [hz, cofiniteConstructionConeAngle] at hjpos
      norm_num at hjpos
    have hjord : j.val < orders.length := by
      by_contra hn
      apply hjzero
      rw [List.getD_append_right _ _ _ _ (by omega)]
      have hjs : j.val - orders.length < s := by
        have hlen := j.isLt
        simp only [List.length_append, List.length_replicate] at hlen
        omega
      change (List.replicate s 0).getD (j.val - orders.length) 2 = 0
      have hrep : j.val - orders.length < (List.replicate s (0 : ℕ)).length := by
        simpa only [List.length_replicate] using hjs
      simp only [List.getD_eq_getElem (List.replicate s (0 : ℕ)) 2 hrep, List.getElem_replicate]
    let k : Fin orders.length := ⟨j.val, hjord⟩
    have hjmark : generalCoreOrderMarkIndex orders s k = j := Fin.ext rfl
    have hkget : (ms₀).getD j.val 2 = orders[k] := by
      rw [← hjmark, generalCoreOrderMarkIndex_getD]
    have hkmin : 2 ≤ orders[k] := ho _ (List.getElem_mem k.isLt)
    have hknot : orders[k] ≠ 2 := hkget ▸ hjget
    have hm : 3 ≤ (ms₀).getD j.val 2 := by rw [hkget]; omega
    refine ⟨k, ?_⟩
    rw [generalCoreConePoint_of_ne_two g orders s t ho hdef d hd hb k hknot]
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.injective
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.isEmbedding_discToClosedModel.injective
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
      (generalCoreOuterPoint g orders s t ho hdef d hd hb (generalCoreOrderMarkIndex orders s k) _))
    have hmk : 3 ≤ (ms₀).getD (generalCoreOrderMarkIndex orders s k).val 2 := by
      rw [generalCoreOrderMarkIndex_getD]
      omega
    rw [generalCoreOuterPoint_coordinate g orders s t ho hdef d hd hb
      (generalCoreOrderMarkIndex orders s k) hmk]
    have hindex : generalCoreOuterIndex g orders s t (generalCoreOrderMarkIndex orders s k)
        (by omega) = i := Fin.ext hji
    exact hxi.trans (congrArg (Q₀).vertices hindex).symm
  · have hival : i.val = (cofiniteConstructionSideAngles β₀ g ms₀).length + 3 * j.val + (r.val + 1) :=
      (congrArg Fin.val hjr).symm
    have hxcut : x ∈ generalCoreCutSegment g orders s t ho hdef d hd hb j := by
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc x) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelDiscHSegment _ _
      rw [hxi]
      fin_cases r
      · have hi : i = generalCoreBoundarySideIndex g orders s t j 1 := Fin.ext hival
        rw [hi]
        exact _root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_left_mem _ _
      · have hi : i = finRotate _ (generalCoreBoundarySideIndex g orders s t j 1) := by
          rw [generalCoreBoundarySideIndex_next_one]
          exact Fin.ext hival
        rw [hi]
        exact _root_.LowDimensionalTopology.Geometry.Polygon.closedModelDiscHSegment_right_mem _ _
    exact False.elim (hxW (mem_iUnion.mpr ⟨1, x, mem_iUnion.mpr ⟨j, hxcut⟩, rfl⟩))

/-- Complete original-carrier exhaustion: every point of the actual closed
polygon off the actual walls with a nontrivial whole target stabilizer is
one of the original cone occurrences. -/
theorem generalCoreTarget_carrier_fixed_cone (x : ℍ)
    (hx : x ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).carrier) (hxW : x ∉ W₀)
    (a : H₀) (ha : a ≠ 1) (hfix : a.val x = x) :
    ∃ j : Fin orders.length, x = generalCoreConePoint g orders s t ho hdef d hd hb j := by
  by_cases hv : x ∈ _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q₀
  · obtain ⟨i, hi⟩ := hv
    exact generalCoreTarget_vertex_cone g orders s t ho hdef d hd hb x hx hxW i hi.symm a ha hfix
  · exact generalCoreTarget_nonvertex_cone g orders s t ho hdef d hd hb x hx hxW hv a ha hfix

/-- Every nontrivial actual target fixed point is in the entire target orbit
of a genuine original cone occurrence. This is a whole-group exhaustion. -/
theorem generalCoreTarget_fixed_cone_orbit
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (generalCoreTargetMobiusGroup g orders s t ho hdef d hd hb))
    (x : ℍ) (a : H₀) (ha : a ≠ 1) (hfix : a.val x = x) :
    ∃ (j : Fin orders.length) (b : H₀),
      b.val x = generalCoreConePoint g orders s t ho hdef d hd hb j := by
  obtain ⟨b, y, hy, hyW, hby⟩ := generalCoreTarget_fixed_original_representative
    g orders s t ho hdef d hd hb hNE x a ha hfix
  let c : H₀ := b⁻¹ * a * b
  have hc : c ≠ 1 := by
    intro he
    apply ha
    have h := congrArg (fun k : H₀ => b * k * b⁻¹) he
    simpa [c, mul_assoc] using h
  have hcy : c.val y = y := by
    change b.val.symm (a.val (b.val y)) = y
    rw [hby, hfix, ← hby, b.val.symm_apply_apply]
  obtain ⟨j, hj⟩ := generalCoreTarget_carrier_fixed_cone g orders s t ho hdef d hd hb y hy hyW c hc hcy
  exact ⟨j, b⁻¹, by change b.val.symm x = _; rw [← hby, b.val.symm_apply_apply, hj]⟩

end LowDimensionalTopology.Geometry.Fuchsian
