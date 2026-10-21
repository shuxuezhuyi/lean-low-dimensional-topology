/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareKlein.Ambient
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleTopology
public import Mathlib.Topology.Piecewise

/-!
# Genuine triangles with finite or ideal vertices
-/

@[expose] public section
open Set Module
open scoped UpperHalfPlane OnePoint Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem exists_discLine_closedCarrier_through (p : 𝕔𝔻) : ∃ L : DiscLine, p ∈ L.closedCarrier := by
  let q0 := discToClosedModel (0 : 𝔻)
  let q1 := Complex.UnitClosedDisc.mk (1 : ℂ) (by norm_num)
  have h01 : q0 ≠ q1 := by
    intro he
    have hc := congrArg (fun q : 𝕔𝔻 => (q : ℂ)) he
    change (0 : ℂ) = 1 at hc
    exact zero_ne_one hc
  by_cases hp0 : p = q0
  · have hp1 : p ≠ q1 := hp0 ▸ h01
    obtain ⟨L,hL,_⟩ := existsUnique_discLine_closedCarrier p q1 hp1
    exact ⟨L,hL.1⟩
  · obtain ⟨L,hL,_⟩ := existsUnique_discLine_closedCarrier p q0 hp0
    exact ⟨L,hL.1⟩

theorem exists_discLine_closedCarrier_through_any (p q : 𝕔𝔻) :
    ∃ L : DiscLine, p ∈ L.closedCarrier ∧ q ∈ L.closedCarrier := by
  by_cases hpq : p = q
  · subst q
    obtain ⟨L,hp⟩ := exists_discLine_closedCarrier_through p
    exact ⟨L,hp,hp⟩
  · exact (existsUnique_discLine_closedCarrier p q hpq).exists

/-- Actual compactified disc vertices; noncollinearity refers to actual closures of genuine
native circle/diameter h-lines, including their true ideal endpoints. -/
structure ClosedDiscTriangle where
  a : 𝕔𝔻
  b : 𝕔𝔻
  c : 𝕔𝔻
  noncollinear : ¬ ∃ L : DiscLine,
    a ∈ L.closedCarrier ∧ b ∈ L.closedCarrier ∧ c ∈ L.closedCarrier

theorem ClosedDiscTriangle.a_ne_b (T : ClosedDiscTriangle) : T.a ≠ T.b := by
  intro he
  obtain ⟨L,ha,hc⟩ := exists_discLine_closedCarrier_through_any T.a T.c
  exact T.noncollinear ⟨L,ha,he ▸ ha,hc⟩

theorem ClosedDiscTriangle.b_ne_c (T : ClosedDiscTriangle) : T.b ≠ T.c := by
  intro he
  obtain ⟨L,ha,hb⟩ := exists_discLine_closedCarrier_through_any T.a T.b
  exact T.noncollinear ⟨L,ha,hb,he ▸ hb⟩

theorem ClosedDiscTriangle.c_ne_a (T : ClosedDiscTriangle) : T.c ≠ T.a := by
  intro he
  obtain ⟨L,ha,hb⟩ := exists_discLine_closedCarrier_through_any T.a T.b
  exact T.noncollinear ⟨L,ha,hb,he.symm ▸ ha⟩

def ClosedDiscTriangle.sideLineA (T : ClosedDiscTriangle) : DiscLine :=
  (existsUnique_discLine_closedCarrier T.b T.c T.b_ne_c).exists.choose

def ClosedDiscTriangle.sideLineB (T : ClosedDiscTriangle) : DiscLine :=
  (existsUnique_discLine_closedCarrier T.c T.a T.c_ne_a).exists.choose

def ClosedDiscTriangle.sideLineC (T : ClosedDiscTriangle) : DiscLine :=
  (existsUnique_discLine_closedCarrier T.a T.b T.a_ne_b).exists.choose

theorem ClosedDiscTriangle.a_mem_sideLineB (T : ClosedDiscTriangle) : T.a ∈ T.sideLineB.closedCarrier :=
  (existsUnique_discLine_closedCarrier T.c T.a T.c_ne_a).exists.choose_spec.2

theorem ClosedDiscTriangle.c_mem_sideLineB (T : ClosedDiscTriangle) : T.c ∈ T.sideLineB.closedCarrier :=
  (existsUnique_discLine_closedCarrier T.c T.a T.c_ne_a).exists.choose_spec.1

theorem ClosedDiscTriangle.b_not_mem_sideLineB (T : ClosedDiscTriangle) : T.b ∉ T.sideLineB.closedCarrier :=
  fun hb => T.noncollinear ⟨T.sideLineB,T.a_mem_sideLineB,hb,T.c_mem_sideLineB⟩






















theorem ClosedDiscTriangle.klein_vertices_linearIndependent (T : ClosedDiscTriangle) :
    LinearIndependent ℝ ![closedKleinCoordinate T.b - closedKleinCoordinate T.a,
      closedKleinCoordinate T.c - closedKleinCoordinate T.a] := by
  apply linearIndependent_fin2.mpr
  refine ⟨sub_ne_zero.mpr (closedKleinCoordinate_injective.ne T.c_ne_a),?_⟩
  intro r he
  change r • (closedKleinCoordinate T.c - closedKleinCoordinate T.a) =
    closedKleinCoordinate T.b - closedKleinCoordinate T.a at he
  obtain ⟨a,t,_,hL⟩ := T.sideLineB.closedKlein_affine_equation
  have ha := (hL T.a).mp T.a_mem_sideLineB
  have hc := (hL T.c).mp T.c_mem_sideLineB
  have hb : inner ℝ a (closedKleinCoordinate T.b) = t := by
    have hd : inner ℝ a (closedKleinCoordinate T.b - closedKleinCoordinate T.a) = 0 := by
      rw [← he,inner_smul_right,inner_sub_right,hc,ha,sub_self,mul_zero]
    rw [inner_sub_right,ha] at hd
    linarith
  exact T.b_not_mem_sideLineB ((hL T.b).mpr hb)

def ClosedDiscTriangle.kleinBasis (T : ClosedDiscTriangle) : Basis (Fin 2) ℝ ℂ :=
  basisOfLinearIndependentOfCardEqFinrank T.klein_vertices_linearIndependent
    (by simp only [Fintype.card_fin,Complex.finrank_real_complex])

theorem ClosedDiscTriangle.kleinBasis_zero (T : ClosedDiscTriangle) :
    T.kleinBasis 0 = closedKleinCoordinate T.b - closedKleinCoordinate T.a := by
  change (basisOfLinearIndependentOfCardEqFinrank _ _ : Basis (Fin 2) ℝ ℂ) 0 = _
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

theorem ClosedDiscTriangle.kleinBasis_one (T : ClosedDiscTriangle) :
    T.kleinBasis 1 = closedKleinCoordinate T.c - closedKleinCoordinate T.a := by
  change (basisOfLinearIndependentOfCardEqFinrank _ _ : Basis (Fin 2) ℝ ℂ) 1 = _
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl

def ClosedDiscTriangle.coordinateLinear (T : ClosedDiscTriangle) : ℂ ≃ₗ[ℝ] ℝ × ℝ :=
  T.kleinBasis.equivFun.trans (LinearEquiv.finTwoArrow ℝ ℝ)

def ClosedDiscTriangle.coordinateHomeomorph (T : ClosedDiscTriangle) : ℂ ≃ₜ ℝ × ℝ :=
  (Homeomorph.subRight (closedKleinCoordinate T.a)).trans
    T.coordinateLinear.toContinuousLinearEquiv.toHomeomorph

def ClosedDiscTriangle.coordinate (T : ClosedDiscTriangle) (x : 𝕔𝔻) : ℝ × ℝ :=
  T.coordinateHomeomorph (closedKleinCoordinate x)

def ClosedDiscTriangle.coordinateDomain (T : ClosedDiscTriangle) : Set (ℝ × ℝ) :=
  T.coordinateHomeomorph '' Metric.closedBall (0 : ℂ) 1

theorem ClosedDiscTriangle.coordinate_a (T : ClosedDiscTriangle) : T.coordinate T.a = (0,0) := by
  change T.coordinateLinear (closedKleinCoordinate T.a - closedKleinCoordinate T.a) = 0
  rw [sub_self,map_zero]

theorem ClosedDiscTriangle.coordinate_b (T : ClosedDiscTriangle) : T.coordinate T.b = (1,0) := by
  change T.coordinateLinear (closedKleinCoordinate T.b - closedKleinCoordinate T.a) = _
  rw [← T.kleinBasis_zero]
  change (T.kleinBasis.equivFun (T.kleinBasis 0) 0,
    T.kleinBasis.equivFun (T.kleinBasis 0) 1) = (1,0)
  simp only [Basis.equivFun_self,ite_true,Fin.zero_ne_one,ite_false]

theorem ClosedDiscTriangle.coordinate_c (T : ClosedDiscTriangle) : T.coordinate T.c = (0,1) := by
  change T.coordinateLinear (closedKleinCoordinate T.c - closedKleinCoordinate T.a) = _
  rw [← T.kleinBasis_one]
  change (T.kleinBasis.equivFun (T.kleinBasis 1) 0,
    T.kleinBasis.equivFun (T.kleinBasis 1) 1) = (0,1)
  simp only [Basis.equivFun_self,show (1 : Fin 2) ≠ 0 by decide,ite_false,ite_true]



def ClosedDiscTriangle.ambientCoordinateHomeomorph (T : ClosedDiscTriangle) : ℂ ≃ₜ ℝ × ℝ :=
  ambientKleinHomeomorph.trans T.coordinateHomeomorph

theorem ClosedDiscTriangle.ambientCoordinateHomeomorph_closed (T : ClosedDiscTriangle) (p : 𝕔𝔻) :
    T.ambientCoordinateHomeomorph (p : ℂ) = T.coordinate p := by
  change T.coordinateHomeomorph (ambientKleinHomeomorph (p : ℂ)) = _
  rw [ambientKleinHomeomorph_closed]
  rfl

def ClosedDiscTriangle.closedCarrier (T : ClosedDiscTriangle) : Set 𝕔𝔻 :=
  closedDiscHConvexHull {T.a,T.b,T.c}

def ClosedDiscTriangle.sideA (T : ClosedDiscTriangle) : Set 𝕔𝔻 := closedModelDiscHSegment T.b T.c

def ClosedDiscTriangle.sideB (T : ClosedDiscTriangle) : Set 𝕔𝔻 := closedModelDiscHSegment T.c T.a

def ClosedDiscTriangle.sideC (T : ClosedDiscTriangle) : Set 𝕔𝔻 := closedModelDiscHSegment T.a T.b


def ClosedDiscTriangle.coordinateAffine (T : ClosedDiscTriangle) : ℂ →ᵃ[ℝ] ℝ × ℝ :=
  T.coordinateLinear.toAffineEquiv.toAffineMap.comp
    (AffineEquiv.vaddConst ℝ (closedKleinCoordinate T.a)).symm.toAffineMap

theorem standardClosedTriangle_eq_convexHull : standardClosedTriangle =
    convexHull ℝ {((0,0) : ℝ × ℝ),(1,0),(0,1)} := by
  apply subset_antisymm
  · apply standardClosedTriangle_subset_convex (convex_convexHull ℝ _)
    all_goals apply subset_convexHull ℝ _; simp
  · apply convexHull_min _ standardClosedTriangle_convex
    intro p hp
    simp only [mem_insert_iff,mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> norm_num [standardClosedTriangle]

theorem ClosedDiscTriangle.coordinate_image_closedCarrier (T : ClosedDiscTriangle) :
    T.coordinate '' T.closedCarrier = standardClosedTriangle := by
  calc
    _ = T.coordinateAffine '' (closedKleinCoordinate '' T.closedCarrier) := (image_image _ _ _).symm
    _ = T.coordinateAffine '' convexHull ℝ (closedKleinCoordinate '' {T.a,T.b,T.c}) := by
      rw [ClosedDiscTriangle.closedCarrier,closedDiscHConvexHull_klein_image]
    _ = convexHull ℝ (T.coordinateAffine '' (closedKleinCoordinate '' {T.a,T.b,T.c})) :=
      T.coordinateAffine.image_convexHull _
    _ = convexHull ℝ (T.coordinate '' {T.a,T.b,T.c}) := by rw [image_image]; rfl
    _ = _ := by
      rw [image_insert_eq,image_insert_eq,image_singleton,T.coordinate_a,T.coordinate_b,
        T.coordinate_c,← standardClosedTriangle_eq_convexHull]

theorem ClosedDiscTriangle.coordinate_image_segment (T : ClosedDiscTriangle) (p q : 𝕔𝔻) :
    T.coordinate '' closedModelDiscHSegment p q = segment ℝ (T.coordinate p) (T.coordinate q) := by
  calc
    _ = T.coordinateAffine '' (closedKleinCoordinate '' closedModelDiscHSegment p q) :=
      (image_image _ _ _).symm
    _ = _ := by
      rw [closedKlein_image_closedModelDiscHSegment]
      exact image_segment ℝ T.coordinateAffine (closedKleinCoordinate p) (closedKleinCoordinate q)

def ClosedDiscTriangle.complexClosedCarrier (T : ClosedDiscTriangle) : Set ℂ :=
  ((↑) : 𝕔𝔻 → ℂ) '' T.closedCarrier

/-- The ordinary open triangle bounded by the actual compactified side arcs. -/
def ClosedDiscTriangle.complexInterior (T : ClosedDiscTriangle) : Set ℂ := interior T.complexClosedCarrier

theorem ClosedDiscTriangle.ambient_image_closedCarrier (T : ClosedDiscTriangle) :
    T.ambientCoordinateHomeomorph '' T.complexClosedCarrier = standardClosedTriangle := by
  rw [ClosedDiscTriangle.complexClosedCarrier,image_image]
  have he : (fun p : 𝕔𝔻 => T.ambientCoordinateHomeomorph (p : ℂ)) = T.coordinate :=
    funext T.ambientCoordinateHomeomorph_closed
  rw [he,T.coordinate_image_closedCarrier]

theorem ClosedDiscTriangle.ambient_image_interior (T : ClosedDiscTriangle) :
    T.ambientCoordinateHomeomorph '' T.complexInterior = standardOpenTriangle := by
  change T.ambientCoordinateHomeomorph '' interior T.complexClosedCarrier = _
  rw [T.ambientCoordinateHomeomorph.image_interior,T.ambient_image_closedCarrier,
    standardClosedTriangle_interior]

theorem ClosedDiscTriangle.complexClosedCarrier_isCompact (T : ClosedDiscTriangle) :
    IsCompact T.complexClosedCarrier := by
  apply T.ambientCoordinateHomeomorph.isCompact_image.mp
  rw [T.ambient_image_closedCarrier]
  exact standardClosedTriangle_isCompact

theorem ClosedDiscTriangle.complexInterior_nonempty (T : ClosedDiscTriangle) : T.complexInterior.Nonempty := by
  have hm : (T.ambientCoordinateHomeomorph '' T.complexInterior).Nonempty := by
    rw [T.ambient_image_interior]
    exact ⟨(1/3,1/3),by norm_num [standardOpenTriangle]⟩
  exact image_nonempty.mp hm

theorem ClosedDiscTriangle.complexInterior_closure (T : ClosedDiscTriangle) :
    closure T.complexInterior = T.complexClosedCarrier := by
  apply T.ambientCoordinateHomeomorph.injective.image_injective
  rw [T.ambientCoordinateHomeomorph.image_closure,T.ambient_image_interior,
    standardOpenTriangle_closure,T.ambient_image_closedCarrier]


theorem ClosedDiscTriangle.complexClosedCarrier_subset_closedBall (T : ClosedDiscTriangle) :
    T.complexClosedCarrier ⊆ Metric.closedBall 0 1 := by
  rintro x ⟨p,_,rfl⟩
  simpa only [Metric.mem_closedBall,dist_zero_right] using p.norm_le_one

theorem ClosedDiscTriangle.complexInterior_subset_disc (T : ClosedDiscTriangle) :
    T.complexInterior ⊆ Metric.ball 0 1 := by
  have hm := interior_mono T.complexClosedCarrier_subset_closedBall
  rw [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hm
  exact hm

def ClosedDiscTriangle.interior (T : ClosedDiscTriangle) : Set 𝔻 :=
  ((↑) : 𝔻 → ℂ) ⁻¹' T.complexInterior

theorem ClosedDiscTriangle.interior_complex_image (T : ClosedDiscTriangle) :
    ((↑) : 𝔻 → ℂ) '' T.interior = T.complexInterior := by
  apply image_preimage_eq_of_subset
  intro z hz
  have hn : ‖z‖ < 1 := by
    simpa only [Metric.mem_ball,dist_zero_right] using T.complexInterior_subset_disc hz
  exact ⟨Complex.UnitDisc.mk z hn,rfl⟩

theorem ClosedDiscTriangle.complexInterior_isOpen (T : ClosedDiscTriangle) : IsOpen T.complexInterior :=
  isOpen_interior

theorem ClosedDiscTriangle.complexInterior_isPreconnected (T : ClosedDiscTriangle) :
    IsPreconnected T.complexInterior := by
  apply T.ambientCoordinateHomeomorph.isEmbedding.isInducing.isPreconnected_image.mp
  rw [T.ambient_image_interior,← standardClosedTriangle_interior]
  exact standardClosedTriangle_convex.interior.isPreconnected

theorem ClosedDiscTriangle.complexExterior_isPreconnected (T : ClosedDiscTriangle) :
    IsPreconnected (closure T.complexInterior)ᶜ := by
  apply T.ambientCoordinateHomeomorph.isEmbedding.isInducing.isPreconnected_image.mp
  rw [T.ambientCoordinateHomeomorph.image_compl,T.complexInterior_closure,T.ambient_image_closedCarrier]
  have hc := convexDomain_sdiff_standardClosedTriangle_isPreconnected
    (D := univ) convex_univ isOpen_univ (mem_univ _) (mem_univ _)
  simpa only [sdiff_eq,univ_inter] using hc

theorem ClosedDiscTriangle.ambient_image_frontier (T : ClosedDiscTriangle) :
    T.ambientCoordinateHomeomorph '' frontier T.complexInterior = frontier standardClosedTriangle := by
  rw [frontier,T.complexInterior_isOpen.interior_eq,T.complexInterior_closure,
    image_sdiff T.ambientCoordinateHomeomorph.injective,
    T.ambient_image_closedCarrier,T.ambient_image_interior,
    frontier,standardClosedTriangle_isClosed.closure_eq,standardClosedTriangle_interior]

theorem ClosedDiscTriangle.ambient_image_segment (T : ClosedDiscTriangle) (p q : 𝕔𝔻) :
    T.ambientCoordinateHomeomorph '' (((↑) : 𝕔𝔻 → ℂ) '' closedModelDiscHSegment p q) =
      segment ℝ (T.coordinate p) (T.coordinate q) := by
  rw [image_image]
  have he : (fun p : 𝕔𝔻 => T.ambientCoordinateHomeomorph (p : ℂ)) = T.coordinate :=
    funext T.ambientCoordinateHomeomorph_closed
  rw [he,T.coordinate_image_segment]

theorem ClosedDiscTriangle.complexInterior_frontier (T : ClosedDiscTriangle) :
    frontier T.complexInterior = ((↑) : 𝕔𝔻 → ℂ) '' (T.sideA ∪ T.sideB ∪ T.sideC) := by
  apply T.ambientCoordinateHomeomorph.injective.image_injective
  rw [T.ambient_image_frontier,standardClosedTriangle_frontier,image_union,image_union,image_union,image_union]
  change _ = T.ambientCoordinateHomeomorph '' (((↑) : 𝕔𝔻 → ℂ) '' closedModelDiscHSegment T.b T.c) ∪
    T.ambientCoordinateHomeomorph '' (((↑) : 𝕔𝔻 → ℂ) '' closedModelDiscHSegment T.c T.a) ∪
    T.ambientCoordinateHomeomorph '' (((↑) : 𝕔𝔻 → ℂ) '' closedModelDiscHSegment T.a T.b)
  rw [T.ambient_image_segment,T.ambient_image_segment,T.ambient_image_segment,
    T.coordinate_a,T.coordinate_b,T.coordinate_c]

theorem ClosedDiscTriangle.boundary_circle_homeomorph (T : ClosedDiscTriangle) :
    Nonempty (frontier T.complexInterior ≃ₜ Metric.sphere (0 : ℝ × ℝ) 1) := by
  obtain ⟨h,_,_,hf⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    standardClosedTriangle_convex
    (by rw [standardClosedTriangle_interior]; exact ⟨(1/3,1/3),by norm_num [standardOpenTriangle]⟩)
    standardClosedTriangle_isCompact.isBounded
  exact ⟨(T.ambientCoordinateHomeomorph.isEmbedding.homeomorphImage (frontier T.complexInterior)).trans
    ((Homeomorph.setCongr T.ambient_image_frontier).trans
      ((h.isEmbedding.homeomorphImage (frontier standardClosedTriangle)).trans (Homeomorph.setCongr hf)))⟩

theorem ClosedDiscTriangle.exists_jordan_curve (T : ClosedDiscTriangle) :
    ∃ γ : Metric.sphere (0 : ℝ × ℝ) 1 → ℂ, Continuous γ ∧ Function.Injective γ ∧
      range γ = ((↑) : 𝕔𝔻 → ℂ) '' (T.sideA ∪ T.sideB ∪ T.sideC) := by
  obtain ⟨h⟩ := T.boundary_circle_homeomorph
  let γ : Metric.sphere (0 : ℝ × ℝ) 1 → ℂ := fun p => (h.symm p).val
  refine ⟨γ,continuous_subtype_val.comp h.symm.continuous,?_,?_⟩
  · intro p q he
    apply h.symm.injective
    exact Subtype.ext he
  · rw [← T.complexInterior_frontier]
    ext x
    constructor
    · rintro ⟨p,rfl⟩
      exact (h.symm p).property
    · intro hx
      refine ⟨h ⟨x,hx⟩,?_⟩
      change (h.symm (h ⟨x,hx⟩)).val = x
      rw [h.symm_apply_apply]

theorem ClosedDiscTriangle.bounded_component_iff_mem (T : ClosedDiscTriangle) {x : ℂ}
    (hx : x ∉ frontier T.complexInterior) :
    Bornology.IsBounded (connectedComponentIn (frontier T.complexInterior)ᶜ x) ↔ x ∈ T.complexInterior := by
  apply complex_bounded_component_iff_mem T.complexInterior_isOpen
    T.complexInterior_isPreconnected T.complexExterior_isPreconnected _ hx
  rw [T.complexInterior_closure]
  exact T.complexClosedCarrier_isCompact


theorem standardOpenTriangle_convex : Convex ℝ standardOpenTriangle := by
  rw [← standardClosedTriangle_interior]
  exact standardClosedTriangle_convex.interior

def ClosedDiscTriangle.discCoordinate (T : ClosedDiscTriangle) (z : 𝔻) : ℝ × ℝ :=
  T.coordinate (discToClosedModel z)

theorem ClosedDiscTriangle.ambientCoordinateHomeomorph_disc (T : ClosedDiscTriangle) (z : 𝔻) :
    T.ambientCoordinateHomeomorph (z : ℂ) = T.discCoordinate z :=
  T.ambientCoordinateHomeomorph_closed (discToClosedModel z)

theorem ClosedDiscTriangle.discCoordinate_image_interior (T : ClosedDiscTriangle) :
    T.discCoordinate '' T.interior = standardOpenTriangle := by
  have he : T.ambientCoordinateHomeomorph '' (((↑) : 𝔻 → ℂ) '' T.interior) =
      T.discCoordinate '' T.interior := by
    rw [image_image]
    apply image_congr
    intro z _
    exact T.ambientCoordinateHomeomorph_disc z
  rw [← he,T.interior_complex_image,T.ambient_image_interior]

theorem ClosedDiscTriangle.interior_discHConvex (T : ClosedDiscTriangle) : DiscHConvex T.interior := by
  have him : T.coordinateAffine '' (kleinCoordinate '' T.interior) = standardOpenTriangle := by
    rw [image_image]
    have he : (fun z : 𝔻 => T.coordinateAffine (kleinCoordinate z)) = T.discCoordinate := by
      funext z
      change T.coordinateLinear (kleinCoordinate z - closedKleinCoordinate T.a) =
        T.coordinateLinear (closedKleinCoordinate (discToClosedModel z) - closedKleinCoordinate T.a)
      rw [closedKleinCoordinate_disc_inclusion]
    rw [he,T.discCoordinate_image_interior]
  have hp : kleinCoordinate '' T.interior = T.coordinateAffine ⁻¹' standardOpenTriangle := by
    rw [← him]
    exact (T.coordinateHomeomorph.preimage_image _).symm
  apply (discHConvex_iff_klein_convex _).mpr
  rw [hp]
  exact standardOpenTriangle_convex.affine_preimage T.coordinateAffine

theorem ClosedDiscTriangle.interior_nonempty (T : ClosedDiscTriangle) : T.interior.Nonempty := by
  have hm : (((↑) : 𝔻 → ℂ) '' T.interior).Nonempty := by
    rw [T.interior_complex_image]
    exact T.complexInterior_nonempty
  exact image_nonempty.mp hm

theorem ClosedDiscTriangle.interior_isOpen (T : ClosedDiscTriangle) : IsOpen T.interior :=
  T.complexInterior_isOpen.preimage Complex.UnitDisc.continuous_coe

theorem ClosedDiscTriangle.interior_isPreconnected (T : ClosedDiscTriangle) : IsPreconnected T.interior :=
  T.interior_discHConvex.isPreconnected

/-- Existing finite native triangles give actual compactified triangles without changing their vertices. -/
def DiscTriangle.toClosedDiscTriangle (T : DiscTriangle) : ClosedDiscTriangle where
  a := discToClosedModel T.a
  b := discToClosedModel T.b
  c := discToClosedModel T.c
  noncollinear := by
    rintro ⟨L,ha,hb,hc⟩
    exact T.noncollinear ⟨L,(L.closedCarrier_mem_interior_iff T.a).mp ha,
      (L.closedCarrier_mem_interior_iff T.b).mp hb,(L.closedCarrier_mem_interior_iff T.c).mp hc⟩

end
end LowDimensionalTopology.Geometry.Hyperbolic
