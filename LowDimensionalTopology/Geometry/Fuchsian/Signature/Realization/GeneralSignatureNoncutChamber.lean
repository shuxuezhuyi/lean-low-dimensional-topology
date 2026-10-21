/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureTargetFibreRestriction
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
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

/-- A true incircle contact is strictly closer to the original centre than
all prescribed vertices, including ideal vertices. It is a genuine side nonvertex. -/
theorem cofiniteTangential_actual_foot_nonvertex {n : ℕ} (θ : Fin n → ℝ) (d : ℝ)
    (hθ : ∀ i, θ i ∈ Ico (0 : ℝ) Real.pi) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance θ d = Real.pi) (i : Fin n) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot θ d hd (finRotate n i)) ∉
      _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon θ d hθ hd hb) := by
  rintro ⟨j, hj⟩
  have hα := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle_bounds (hθ j) hd
  have hc := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle_cos_pos (hθ j) hd
  have hcos : Real.cos (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ j) d) < 1 := by
    simpa only [Real.cos_zero] using Real.cos_lt_cos_of_nonneg_of_le_pi
      (show (0 : ℝ) ≤ 0 from le_rfl) (show _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialHalfAngle (θ j) d ≤ Real.pi by
        linarith [Real.pi_pos, hα.2]) hα.1
  have ht := _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangential_tanh_pos hd
  have hbig : Real.tanh d < _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate (θ j) d := by
    unfold _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate
    apply (lt_div_iff₀ hc).mpr
    nlinarith
  have hn := congrArg (fun p : Complex.UnitClosedDisc => ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate p‖) hj
  change ‖_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex θ d hθ hd j)‖ = _ at hn
  rw [_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialVertex_coordinate, _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedKleinCoordinate_disc_inclusion,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane, _root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot_coordinate] at hn
  simp only [norm_smul, Real.norm_eq_abs,
    abs_of_pos (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialVertexCoordinate_pos (hθ j) hd),
    abs_of_pos ht, _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleUnit_norm, mul_one] at hn
  exact hbig.ne hn.symm

section ActualNoncutSides
variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d)
    (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)
local notation "Q₀" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
  (generalCoreTheta_mem g orders s t ho hdef) hd hb
local notation "S₀" => generalCoreAuxSidePairing g orders s t ho hdef d hd hb
local notation "W₀" => generalCoreCutWallUnion g orders s t ho hdef d hd hb

/-- Every genuine interior point of a retained side misses every translated
cut. Whole auxiliary-group incidence is used; this is not a selected-neighbour assertion. -/
theorem generalCoreNoncutSide_nonvertex_not_wall
    (i : Fin (generalCoreAngles g orders s t).length)
    (hi : ¬ generalCoreIsCutSide g orders s t i) (x : ℍ)
    (hx : x ∈ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i)
    (hv : x ∉ _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q₀) :
    x ∉ W₀ := by
  intro hxW
  obtain ⟨γ, z, hz, hγ⟩ := mem_iUnion.mp hxW
  obtain ⟨j, hzj⟩ := mem_iUnion.mp hz
  let cut := generalCoreBoundarySideIndex g orders s t j 1
  have hc : generalCoreIsCutSide g orders s t cut :=
    (generalCoreBoundarySideIndex_cut_iff g orders s t j 1).mpr rfl
  have hxP : x ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).carrier :=
    (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i) hx
  have hzP : z ∈ (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).carrier :=
    (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).side_subset_carrier (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ cut) hzj
  have hinc := cofiniteMixedTangential_nonvertex_closed_incidence
    (generalCoreTheta g orders s t) d (generalCoreTheta_mem g orders s t ho hdef) hd hb
    (generalCoreAuxPairing g orders s t) (generalCoreAuxPairing_involutive g orders s t)
    (generalCoreAuxPairing_angle_profile g orders s t)
    (generalCoreAux_positive_angular_periods g orders s t ho hdef) x hxP hv γ z hzP hγ
  rcases hinc with hγone | ⟨k, hk, hγk⟩
  · have hzx : z = x := by simpa only [hγone, OneMemClass.coe_one, IsometryEquiv.coe_one, id_eq] using hγ
    have hix : i = cut := by
      by_contra hne
      exact hv (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygon_common_sides_vertex Q₀ hne hx (hzx ▸ hzj))
    exact hi (hix.symm ▸ hc)
  · have hki : k = i := by
      by_contra hne
      exact hv (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygon_common_sides_vertex Q₀ hne hk hx)
    subst k
    have he := congrArg (fun w : ℍ => (S₀).element (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i) w) hγ
    rw [hγk] at he
    change (S₀).element (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)
      (((S₀).element (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)).symm z) =
      (S₀).element (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i) x at he
    rw [IsometryEquiv.apply_symm_apply] at he
    have hzside : z ∈ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ (generalCoreAuxPairing g orders s t i) := by
      rw [he]
      have h : (S₀).element (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i) x ∈
          ((S₀).paired (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)).val := by
        rw [← (S₀).side_image (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i)]
        exact ⟨x, hx, rfl⟩
      have hpaired : (S₀).paired (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i) =
          _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ (generalCoreAuxPairing g orders s t i) :=
        cofiniteTangentialJordanSidePairing_paired_index (generalCoreTheta g orders s t) d
          (generalCoreTheta_mem g orders s t ho hdef) hd hb (generalCoreAuxPairing g orders s t)
          (generalCoreAuxPairing_involutive g orders s t)
          (generalCoreAuxPairing_angle_profile g orders s t) i
      rw [hpaired] at h
      exact h
    have hzv : z ∉ _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q₀ := by
      rw [he]
      exact cofiniteJordan_pairing_nonvertex Q₀ S₀ i hx hv
    have hpair : generalCoreAuxPairing g orders s t i = cut := by
      by_contra hne
      exact hzv (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygon_common_sides_vertex Q₀ hne hzside hzj)
    apply hi
    apply (generalCoreAuxPairing_isCut_iff g orders s t i).mp
    exact hpair.symm ▸ hc

/-- The original closed tile away from cuts lies in the actual center chamber.
This follows from its connected dense interior, rather than assuming a path. -/
theorem generalCoreCutChamber_contains_base_tile_off_walls :
    (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀).carrier ∩ W₀ᶜ ⊆
      generalCoreCutChamber g orders s t ho hdef d hd hb UpperHalfPlane.I := by
  let P := _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀
  have hI := generalCoreAux_center_mem_interior g orders s t ho hdef d hd hb
  have hIW := generalCoreAux_interior_avoids_cutWalls g orders s t ho hdef d hd hb _ hI
  have hbody : IsPreconnected (P.carrier ∩ W₀ᶜ) :=
    (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_interior_isConnected Q₀).isPreconnected.subset_closure
      (fun x hx => ⟨P.interior_subset_carrier hx,
        generalCoreAux_interior_avoids_cutWalls g orders s t ho hdef d hd hb x hx⟩)
      (fun _ hx => (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_carrier Q₀) ▸ hx.1)
  exact hbody.subset_connectedComponentIn ⟨P.interior_subset_carrier hI, hIW⟩ inter_subset_right

/-- Each true original noncut side map preserves the same actual open chamber.
An actual finite incircle contact provides the crossing point. -/
theorem generalCoreNoncutGenerator_stabilizes_chamber
    (i : Fin (generalCoreAngles g orders s t).length)
    (hi : ¬ generalCoreIsCutSide g orders s t i) :
    generalCoreTargetGenerator g orders s t ho hdef d hd hb i ''
        generalCoreCutChamber g orders s t ho hdef d hd hb UpperHalfPlane.I =
      generalCoreCutChamber g orders s t ho hdef d hd hb UpperHalfPlane.I := by
  let A := generalCoreTargetGenerator g orders s t ho hdef d hd hb i
  let U := generalCoreCutChamber g orders s t ho hdef d hd hb UpperHalfPlane.I
  let P := _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀
  let side := _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Q₀ i
  let x := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (_root_.LowDimensionalTopology.Geometry.Polygon.polygonOrderedTangentialFoot (generalCoreTheta g orders s t) d hd
    (finRotate _ i))
  have hx : x ∈ _root_.LowDimensionalTopology.Geometry.Polygon.finitePolygonSide Q₀ i := cofiniteTangential_foot_mem_side
    (generalCoreTheta g orders s t) d (generalCoreTheta_mem g orders s t ho hdef) hd hb i
  have hxv : x ∉ _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonNativeVertices Q₀ := cofiniteTangential_actual_foot_nonvertex
    (generalCoreTheta g orders s t) d (generalCoreTheta_mem g orders s t ho hdef) hd hb i
  have hxW : x ∉ W₀ := generalCoreNoncutSide_nonvertex_not_wall g orders s t ho hdef d hd hb i hi x hx hxv
  have hAaux : A ∈ (S₀).Generated := generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb
    (generalCoreTargetGenerator_mem g orders s t ho hdef d hd hb i hi)
  have hW : A '' W₀ = W₀ := generalCoreCutWallUnion_image g orders s t ho hdef d hd hb A hAaux
  have hyP : A x ∈ P.carrier := by
    have hy : (S₀).element side x ∈ ((S₀).paired side).val := by
      rw [← (S₀).side_image side]
      exact ⟨x, hx, rfl⟩
    apply P.side_subset_carrier ((S₀).paired side)
    simpa only [side, generalCoreAuxSidePairing, generalCoreTargetGenerator,
      cofiniteTangentialJordanSidePairing_element_index, A] using hy
  have hyW : A x ∉ W₀ := by
    intro hy
    have hpre : A x ∈ A '' W₀ := hW.symm ▸ hy
    obtain ⟨z, hz, he⟩ := hpre
    exact hxW (A.injective he ▸ hz)
  have hbody := generalCoreCutChamber_contains_base_tile_off_walls g orders s t ho hdef d hd hb
  have hxU : x ∈ U := hbody ⟨P.side_subset_carrier side hx, hxW⟩
  have hyU : A x ∈ U := hbody ⟨hyP, hyW⟩
  have hI := generalCoreAux_center_mem_interior g orders s t ho hdef d hd hb
  have hIW := generalCoreAux_interior_avoids_cutWalls g orders s t ho hdef d hd hb _ hI
  have hcompl : A '' W₀ᶜ = W₀ᶜ := by rw [image_compl_eq A.bijective, hW]
  have hcomp : A '' U = connectedComponentIn W₀ᶜ (A UpperHalfPlane.I) := by
    have h := A.toHomeomorph.image_connectedComponentIn
      (show UpperHalfPlane.I ∈ W₀ᶜ from hIW)
    change A '' connectedComponentIn W₀ᶜ UpperHalfPlane.I =
      connectedComponentIn (A '' W₀ᶜ) (A UpperHalfPlane.I) at h
    simpa only [hcompl, U, generalCoreCutChamber] using h
  have hyComp : A x ∈ connectedComponentIn W₀ᶜ (A UpperHalfPlane.I) :=
    hcomp ▸ mem_image_of_mem A hxU
  exact hcomp.trans ((connectedComponentIn_eq hyComp).trans (connectedComponentIn_eq hyU).symm)

/-- The actual subgroup generated by the true sides stabilizes the actual
center chamber. No chamber-preservation hypothesis is supplied. -/
theorem generalCoreTargetGroup_le_chamber_stabilizer :
    generalCoreTargetGroup g orders s t ho hdef d hd hb ≤
      MulAction.stabilizer (ℍ ≃ᵢ ℍ)
        (generalCoreCutChamber g orders s t ho hdef d hd hb UpperHalfPlane.I) := by
  apply (Subgroup.closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  apply MulAction.mem_stabilizer_iff.mpr
  exact generalCoreNoncutGenerator_stabilizes_chamber g orders s t ho hdef d hd hb i.val i.property

/-- Every actual element of the true target group preserves the original chamber. -/
theorem generalCoreTargetGroup_chamber_image (a : ℍ ≃ᵢ ℍ)
    (ha : a ∈ generalCoreTargetGroup g orders s t ho hdef d hd hb) :
    a '' generalCoreCutChamber g orders s t ho hdef d hd hb UpperHalfPlane.I =
      generalCoreCutChamber g orders s t ho hdef d hd hb UpperHalfPlane.I :=
  MulAction.mem_stabilizer_iff.mp (generalCoreTargetGroup_le_chamber_stabilizer
    g orders s t ho hdef d hd hb ha)

/-- The true target group's whole closed-tile saturation is exactly the
closure of its actual chamber, as proved from its real original side maps. -/
theorem generalCoreTargetTileSaturation_eq_chamber_closure :
    generalCoreTargetTileSaturation g orders s t ho hdef d hd hb =
      closure (generalCoreCutChamber g orders s t ho hdef d hd hb UpperHalfPlane.I) := by
  let U := generalCoreCutChamber g orders s t ho hdef d hd hb UpperHalfPlane.I
  let P := _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Q₀
  have hPI : P.interior ⊆ U := by
    intro x hx
    exact generalCoreCutChamber_contains_base_tile_off_walls g orders s t ho hdef d hd hb
      ⟨P.interior_subset_carrier hx,
        generalCoreAux_interior_avoids_cutWalls g orders s t ho hdef d hd hb x hx⟩
  have hPC : P.carrier ⊆ closure U := by
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_carrier Q₀]
    exact closure_mono hPI
  apply subset_antisymm
  · intro x hx
    obtain ⟨a, ha, y, hy, rfl⟩ := mem_iUnion₂.mp hx
    have hcont := a.toHomeomorph.image_closure U
    change a '' closure U = closure (a '' U) at hcont
    have hyim : a y ∈ a '' closure U := mem_image_of_mem a (hPC hy)
    have hEq := generalCoreTargetGroup_chamber_image g orders s t ho hdef d hd hb a ha
    change a '' U = U at hEq
    rw [hEq] at hcont
    exact hcont ▸ hyim
  · exact closure_minimal (generalCoreTargetTileSaturation_base_chamber_cover
      g orders s t ho hdef d hd hb)
      (generalCoreTargetTileSaturation_isClosed g orders s t ho hdef d hd hb)

/-- Convexity of the entire actual target saturation follows from the actual
geodesic chamber and its proved equality with the closed saturation. -/
theorem generalCoreTargetTileSaturation_hConvex :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (generalCoreTargetTileSaturation g orders s t ho hdef d hd hb) := by
  rw [generalCoreTargetTileSaturation_eq_chamber_closure]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex.closure
  apply generalCoreCutChamber_hConvex
  exact generalCoreAux_interior_avoids_cutWalls g orders s t ho hdef d hd hb _
    (generalCoreAux_center_mem_interior g orders s t ho hdef d hd hb)

end ActualNoncutSides
end LowDimensionalTopology.Geometry.Fuchsian
