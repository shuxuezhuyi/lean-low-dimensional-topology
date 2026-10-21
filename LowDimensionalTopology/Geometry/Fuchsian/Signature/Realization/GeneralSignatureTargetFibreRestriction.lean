/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureCutWalls
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

variable (g : ℕ) (orders : List ℕ) (s t : ℕ)
  (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
  (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi)

local notation "Qcore" => _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
  (generalCoreTheta_mem g orders s t ho hdef) hd hb
local notation "Pcore" => _root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon Qcore
local notation "Saux" => generalCoreAuxSidePairing g orders s t ho hdef d hd hb
local notation "Htarget" => generalCoreTargetGroup g orders s t ho hdef d hd hb
local notation "Wcut" => generalCoreCutWallUnion g orders s t ho hdef d hd hb

/-- The actual noncut subgroup saturates the original closed core polygon.
No convexity, core containment or covering property is assigned to this set. -/
def generalCoreTargetTileSaturation : Set ℍ :=
  ⋃ k ∈ Htarget, k '' (Pcore).carrier

/-- The complete actual auxiliary-group cut-wall union is invariant under
every actual auxiliary element, by literal multiplication of its tile labels. -/
theorem generalCoreCutWallUnion_image (k : ℍ ≃ᵢ ℍ) (hk : k ∈ (Saux).Generated) :
    k '' Wcut = Wcut := by
  unfold generalCoreCutWallUnion
  apply subset_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨a, z, hz, rfl⟩ := mem_iUnion.mp hy
    exact mem_iUnion.mpr ⟨⟨k * a.val, (Saux).Generated.mul_mem hk a.property⟩, z, hz, rfl⟩
  · intro x hx
    obtain ⟨a, z, hz, rfl⟩ := mem_iUnion.mp hx
    refine ⟨(k⁻¹ * a.val) z, mem_iUnion.mpr
      ⟨⟨k⁻¹ * a.val, (Saux).Generated.mul_mem ((Saux).Generated.inv_mem hk) a.property⟩,
        z, hz, rfl⟩, ?_⟩
    change (k * (k⁻¹ * a.val)) z = a.val z
    rw [mul_inv_cancel_left]

/-- The proved actual mixed-polygon developing map is injective on every
original closed side and finite vertex, with the actual auxiliary periods. -/
theorem generalCoreAux_evaluation_injective : Function.Injective (Saux).evaluation :=
  cofiniteMixedTangential_evaluation_injective (generalCoreTheta g orders s t) d
    (generalCoreTheta_mem g orders s t ho hdef) hd hb (generalCoreAuxPairing g orders s t)
    (generalCoreAuxPairing_involutive g orders s t)
    (generalCoreAuxPairing_angle_profile g orders s t)
    (generalCoreAux_positive_angular_periods g orders s t ho hdef)

/-- The actual polygon is centered at the upper half-plane origin. -/
theorem generalCoreAux_center_mem_interior : UpperHalfPlane.I ∈ (Pcore).interior := by
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I ∈ (Qcore).interior
  have hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc UpperHalfPlane.I = 0 := by
    rw [← _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_zero,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  rw [hz]
  exact _root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon_origin_mem (generalCoreTheta g orders s t) d
    (generalCoreTheta_mem g orders s t ho hdef) hd hb

/-- The original polygon interior misses every actual auxiliary cut wall.
Global developing injectivity and original interior gluing rigidity derive
this fact, rather than supplying a packing or wall-separation hypothesis. -/
theorem generalCoreAux_interior_avoids_cutWalls (x : ℍ) (hx : x ∈ (Pcore).interior) :
    x ∉ Wcut := by
  intro hxW
  unfold generalCoreCutWallUnion at hxW
  obtain ⟨a, z, hz, haz⟩ := mem_iUnion.mp hxW
  obtain ⟨j, hzcut⟩ := mem_iUnion.mp hz
  let side := _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Qcore (generalCoreBoundarySideIndex g orders s t j 1)
  have hzside : z ∈ side.val := hzcut
  let p : (Pcore).Point := ⟨x, (Pcore).interior_subset_carrier hx⟩
  let q : (Pcore).Point := ⟨z, (Pcore).side_subset_carrier side hzside⟩
  have hproj : (Saux).project (a, q) = (Saux).project (1, p) := by
    apply generalCoreAux_evaluation_injective g orders s t ho hdef d hd hb
    exact haz
  have hcopy : (a, q) = (1, p) :=
    (Saux).gluing_interior_rigid (((Saux).project_eq_iff _ _).mp hproj) (Or.inr hx)
  have hzx : z = x := congrArg (fun c : (Saux).Copy => c.2.val) hcopy
  exact Set.disjoint_left.mp ((Pcore).interior_disjoint_side side) hx (hzx ▸ hzside)

/-- A genuine cut-side step is impossible at an actual evaluation point
outside the complete auxiliary cut-wall union. -/
theorem generalCoreTarget_step_mem (a b : (Saux).Copy) (hstep : (Saux).Step a b)
    (hwall : (Saux).copyEvaluation a ∉ Wcut) (ha : a.1.val ∈ Htarget) :
    b.1.val ∈ Htarget := by
  rcases hstep with he | ⟨side, hside, _hpoint, hindex⟩
  · exact he ▸ ha
  · have hnoncut : ¬ generalCoreIsCutSide g orders s t
        ((_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Qcore).symm side) := by
      intro hcut
      obtain ⟨j, hj⟩ := (generalCoreIsCutSide_iff g orders s t _).mp hcut
      have hsideEq : side = _root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Qcore
          (generalCoreBoundarySideIndex g orders s t j 1) := by
        apply (_root_.LowDimensionalTopology.Geometry.Polygon.jordanPolygonSideEquiv Qcore).symm.injective
        simpa only [Equiv.symm_apply_apply] using hj
      have hsideCut : a.2.val ∈ generalCoreCutSegment g orders s t ho hdef d hd hb j := by
        rw [hsideEq] at hside
        exact hside
      apply hwall
      unfold generalCoreCutWallUnion
      exact mem_iUnion.mpr ⟨a.1, a.2.val, mem_iUnion.mpr ⟨j, hsideCut⟩, rfl⟩
    have hgen := generalCoreAuxSidePairing_element_mem_target g orders s t ho hdef d hd hb
      side hnoncut
    have he : a.1.val = b.1.val * (Saux).element side := congrArg Subtype.val hindex
    have hbindex : b.1.val = a.1.val * ((Saux).element side)⁻¹ := by
      rw [he]
      group
    rw [hbindex]
    exact (Htarget).mul_mem ha ((Htarget).inv_mem hgen)

/-- At a point away from the actual cut walls, the entire original gluing
class uses retained side maps. This proves the finite-fan restriction for
all actual vertices at once, including elliptic and ordinary corners. -/
theorem generalCoreTargetFibre_labels (p : (Pcore).Point) (hp : p.val ∉ Wcut)
    (c : (Saux).Copy) (hc : (Saux).project c = (Saux).project (1, p)) :
    c.1.val ∈ Htarget := by
  have hchain (a b : (Saux).Copy) (h : Relation.EqvGen (Saux).Step a b) :
      (Saux).copyEvaluation a ∉ Wcut →
        (a.1.val ∈ Htarget ↔ b.1.val ∈ Htarget) := by
    induction h with
    | rel a b hab =>
      intro haW
      have hbW : (Saux).copyEvaluation b ∉ Wcut := by
        rw [← (Saux).step_evaluation hab]
        exact haW
      exact ⟨generalCoreTarget_step_mem g orders s t ho hdef d hd hb a b hab haW,
        generalCoreTarget_step_mem g orders s t ho hdef d hd hb b a
          ((Saux).step_symm hab) hbW⟩
    | refl a => intro _; exact Iff.rfl
    | symm a b hab ih =>
      intro hbW
      have haW : (Saux).copyEvaluation a ∉ Wcut := by
        rw [(Saux).gluing_evaluation hab]
        exact hbW
      exact (ih haW).symm
    | trans a b c hab _hbc ihab ihbc =>
      intro haW
      have hbW : (Saux).copyEvaluation b ∉ Wcut := by
        rw [← (Saux).gluing_evaluation hab]
        exact haW
      exact (ihab haW).trans (ihbc hbW)
  have he := ((Saux).project_eq_iff (1, p) c).mp hc.symm
  have hp' : (Saux).copyEvaluation (1, p) ∉ Wcut := by
    simpa only [_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.copyEvaluation, one_smul] using hp
  exact (hchain (1, p) c he hp').mp (Htarget).one_mem

/--
Genuine local tessellation supplies a full metric ball in the actual target tile union
at every original polygon point outside the actual cut walls. No local fan,
target cover or local openness premise is supplied.
-/
theorem generalCoreTargetTileSaturation_base_ball (p : (Pcore).Point) (hp : p.val ∉ Wcut) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball p.val r ⊆
      generalCoreTargetTileSaturation g orders s t ho hdef d hd hb := by
  obtain ⟨r, hr, hlocal⟩ :=
    (generalCore_auxiliary_local_tessellation g orders s t ho hdef d hd hb).local_radius p
  have himage : (Saux).copyEvaluation '' (Saux).copyNeighborhood (1, p) r = Metric.ball p.val r := by
    simpa only [_root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing.copyEvaluation, one_smul] using
      (hlocal r hr le_rfl).image_eq
  refine ⟨r, hr, ?_⟩
  intro x hx
  rw [← himage] at hx
  obtain ⟨b, hbnear, rfl⟩ := hx
  obtain ⟨c, hc, hindex, _hdist⟩ := hbnear
  have hbH : b.1.val ∈ Htarget := by
    rw [hindex]
    exact generalCoreTargetFibre_labels g orders s t ho hdef d hd hb p hp c hc
  exact mem_iUnion₂.mpr ⟨b.1.val, hbH, b.2.val, b.2.property, rfl⟩

/-- Every actual target tile point outside the complete cut walls has a full
ambient ball in the actual target saturation. This is the required genuine
local openness mechanism for the final chamber-cover argument. -/
theorem generalCoreTargetTileSaturation_local_ball (x : ℍ)
    (hx : x ∈ generalCoreTargetTileSaturation g orders s t ho hdef d hd hb)
    (hxW : x ∉ Wcut) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆
      generalCoreTargetTileSaturation g orders s t ho hdef d hd hb := by
  obtain ⟨a, ha, p, hp, rfl⟩ := mem_iUnion₂.mp hx
  have haux : a ∈ (Saux).Generated :=
    generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb ha
  have hwall := generalCoreCutWallUnion_image g orders s t ho hdef d hd hb a haux
  have hpW : p ∉ Wcut := by
    intro hpW
    exact hxW (hwall ▸ mem_image_of_mem a hpW)
  obtain ⟨r, hr, hball⟩ := generalCoreTargetTileSaturation_base_ball g orders s t ho hdef
    d hd hb ⟨p, hp⟩ hpW
  refine ⟨r, hr, ?_⟩
  intro y hy
  have hyinv : a.symm y ∈ Metric.ball p r := by
    change dist (a.symm y) p < r
    rw [← a.dist_eq (a.symm y) p, a.apply_symm_apply]
    exact hy
  obtain ⟨b, hbH, z, hz, he⟩ := mem_iUnion₂.mp (hball hyinv)
  refine mem_iUnion₂.mpr ⟨a * b, (Htarget).mul_mem ha hbH, z, hz, ?_⟩
  change a (b z) = y
  rw [he, a.apply_symm_apply]

/-- The actual target closed-tile union is closed, by restriction of the
proved locally finite auxiliary tessellation to the actual target subgroup. -/
theorem generalCoreTargetTileSaturation_isClosed :
    IsClosed (generalCoreTargetTileSaturation g orders s t ho hdef d hd hb) := by
  let inc : Htarget → (Saux).Generated :=
    Subgroup.inclusion (generalCoreTargetGroup_le_aux g orders s t ho hdef d hd hb)
  have hinj : Function.Injective inc := by
    intro a b he
    apply Subtype.ext
    exact congrArg (fun z : (Saux).Generated => z.val) he
  have hlfbase := generalCoreAux_native_closed_tiles_locallyFinite g orders s t ho hdef d hd hb
  have hlf := hlfbase.comp_injective hinj
  have hlf' : LocallyFinite (fun k : Htarget => k.val '' (Pcore).carrier) := by
    simp only [_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_carrier]
    change LocallyFinite (fun k : Htarget => k.val ''
      closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (Qcore).interior))
    exact hlf
  have hc : ∀ k : Htarget, IsClosed (k.val '' (Pcore).carrier) := by
    intro k
    rw [_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon_carrier]
    exact k.val.toHomeomorph.isClosedMap _ isClosed_closure
  have he : (⋃ k : Htarget, k.val '' (Pcore).carrier) =
      generalCoreTargetTileSaturation g orders s t ho hdef d hd hb := by
    ext x
    constructor
    · intro hx
      obtain ⟨k, hk⟩ := mem_iUnion.mp hx
      exact mem_iUnion₂.mpr ⟨k.val, k.property, hk⟩
    · intro hx
      obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
      exact mem_iUnion.mpr ⟨⟨k, hk⟩, hxk⟩
  rw [← he]
  exact hlf'.isClosed_iUnion hc

/-- The actual target saturation is open off the complete closed cut-wall
union. Both required geometric inputs have been proved for this very group. -/
theorem generalCoreTargetTileSaturation_off_walls_isOpen :
    IsOpen (generalCoreTargetTileSaturation g orders s t ho hdef d hd hb ∩ Wcutᶜ) := by
  rw [Metric.isOpen_iff]
  intro x hx
  obtain ⟨r, hr, hball⟩ :=
    generalCoreTargetTileSaturation_local_ball g orders s t ho hdef d hd hb x hx.1 hx.2
  obtain ⟨u, hu, hwall⟩ := Metric.isOpen_iff.mp
    (generalCoreCutWallUnion_isClosed g orders s t ho hdef d hd hb).isOpen_compl x hx.2
  refine ⟨min r u, lt_min hr hu, ?_⟩
  intro y hy
  exact ⟨hball (Metric.ball_subset_ball (min_le_left _ _) hy),
    hwall (Metric.ball_subset_ball (min_le_right _ _) hy)⟩

/--
The entire actual component containing the original center is covered
by the original noncut subgroup's closed core tiles. The cover is derived
from genuine local tessellation, cut avoidance, local finiteness and connectedness.
-/
theorem generalCoreTargetTileSaturation_base_chamber_cover :
    connectedComponentIn Wcutᶜ UpperHalfPlane.I ⊆
      generalCoreTargetTileSaturation g orders s t ho hdef d hd hb := by
  let U := generalCoreTargetTileSaturation g orders s t ho hdef d hd hb
  let C := connectedComponentIn Wcutᶜ UpperHalfPlane.I
  have hI := generalCoreAux_center_mem_interior g orders s t ho hdef d hd hb
  have hIW : UpperHalfPlane.I ∉ Wcut :=
    generalCoreAux_interior_avoids_cutWalls g orders s t ho hdef d hd hb _ hI
  have hIU : UpperHalfPlane.I ∈ U :=
    mem_iUnion₂.mpr ⟨1, (Htarget).one_mem, UpperHalfPlane.I,
      (Pcore).interior_subset_carrier hI, rfl⟩
  have hC : C ⊆ Wcutᶜ := connectedComponentIn_subset _ _
  have hUclosed : IsClosed U := generalCoreTargetTileSaturation_isClosed g orders s t ho hdef d hd hb
  have hUopen : IsOpen (U ∩ Wcutᶜ) :=
    generalCoreTargetTileSaturation_off_walls_isOpen g orders s t ho hdef d hd hb
  have hcl : closure (U ∩ Wcutᶜ) ⊆ U := closure_minimal inter_subset_left hUclosed
  have hconn : IsPreconnected C := isPreconnected_connectedComponentIn
  have hcover : C ⊆ U ∩ Wcutᶜ := hconn.subset_of_closure_inter_subset hUopen
    ⟨UpperHalfPlane.I, mem_connectedComponentIn hIW, hIU, hIW⟩
    (fun _ hx => ⟨hcl hx.1, hC hx.2⟩)
  exact hcover.trans inter_subset_left

end LowDimensionalTopology.Geometry.Fuchsian
