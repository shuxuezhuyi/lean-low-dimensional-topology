/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.IdealTriangleCorners
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.ClosedHalfPlane
public import Mathlib.Analysis.Convex.StrictConvexSpace

/-!
# True opposite-side crossings for finite and ideal triangles
-/

@[expose] public section
open Set Module
open scoped UpperHalfPlane OnePoint Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem ClosedDiscTriangle.open_opposite_segment_subset_openDomain (T : ClosedDiscTriangle) :
    {p : ℝ × ℝ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 + p.2 = 1} ⊆ T.openCoordinateDomain := by
  intro p hp
  let w := p.1 • closedKleinCoordinate T.b + p.2 • closedKleinCoordinate T.c
  have hb : closedKleinCoordinate T.b ∈ Metric.closedBall (0 : ℂ) 1 :=
    range_closedKleinCoordinate ▸ mem_range_self T.b
  have hc : closedKleinCoordinate T.c ∈ Metric.closedBall (0 : ℂ) 1 :=
    range_closedKleinCoordinate ▸ mem_range_self T.c
  have hw : w ∈ _root_.interior (Metric.closedBall (0 : ℂ) 1) :=
    strictConvex_closedBall ℝ (0 : ℂ) 1 hb hc (closedKleinCoordinate_injective.ne T.b_ne_c)
      hp.1 hp.2.1 hp.2.2
  rw [interior_closedBall (0 : ℂ) (by norm_num : (1 : ℝ) ≠ 0)] at hw
  refine ⟨w,hw,?_⟩
  have hsub : w - closedKleinCoordinate T.a =
      p.1 • (closedKleinCoordinate T.b - closedKleinCoordinate T.a) +
        p.2 • (closedKleinCoordinate T.c - closedKleinCoordinate T.a) := by
    change p.1 • closedKleinCoordinate T.b + p.2 • closedKleinCoordinate T.c - _ = _
    calc
      _ = p.1 • closedKleinCoordinate T.b + p.2 • closedKleinCoordinate T.c -
          (p.1 + p.2) • closedKleinCoordinate T.a := by rw [hp.2.2,one_smul]
      _ = _ := by module
  have hbF := T.coordinate_b
  have hcF := T.coordinate_c
  change T.coordinateLinear (closedKleinCoordinate T.b - closedKleinCoordinate T.a) = (1,0) at hbF
  change T.coordinateLinear (closedKleinCoordinate T.c - closedKleinCoordinate T.a) = (0,1) at hcF
  change T.coordinateLinear (w - closedKleinCoordinate T.a) = p
  rw [hsub,map_add,map_smul,map_smul,hbF,hcF]
  ext <;> simp

def ClosedDiscTriangle.openSideA (T : ClosedDiscTriangle) : Set 𝕔𝔻 :=
  {p | p ∈ T.sideA ∧ p ≠ T.b ∧ p ≠ T.c}

theorem ClosedDiscTriangle.mem_sideA_iff_coordinate (T : ClosedDiscTriangle) (x : 𝕔𝔻) :
    x ∈ T.sideA ↔ 0 ≤ (T.coordinate x).1 ∧ 0 ≤ (T.coordinate x).2 ∧
      (T.coordinate x).1 + (T.coordinate x).2 = 1 := by
  change x ∈ closedModelDiscHSegment T.b T.c ↔ _
  rw [T.mem_closedSegment_iff_coordinate,T.coordinate_b,T.coordinate_c,standard_opposite_segment]
  rfl

theorem ClosedDiscTriangle.mem_openSideA_iff_coordinate (T : ClosedDiscTriangle) (x : 𝕔𝔻) :
    x ∈ T.openSideA ↔ 0 < (T.coordinate x).1 ∧ 0 < (T.coordinate x).2 ∧
      (T.coordinate x).1 + (T.coordinate x).2 = 1 := by
  change (x ∈ T.sideA ∧ x ≠ T.b ∧ x ≠ T.c) ↔ _
  rw [T.mem_sideA_iff_coordinate]
  constructor
  · rintro ⟨⟨hu,hv,hs⟩,hxb,hxc⟩
    have hu0 : (T.coordinate x).1 ≠ 0 := by
      intro he
      apply hxc
      apply T.coordinate_injective
      rw [T.coordinate_c]
      ext <;> dsimp <;> linarith
    have hv0 : (T.coordinate x).2 ≠ 0 := by
      intro he
      apply hxb
      apply T.coordinate_injective
      rw [T.coordinate_b]
      ext <;> dsimp <;> linarith
    exact ⟨lt_of_le_of_ne hu hu0.symm,lt_of_le_of_ne hv hv0.symm,hs⟩
  · rintro ⟨hu,hv,hs⟩
    refine ⟨⟨hu.le,hv.le,hs⟩,?_,?_⟩
    · intro he
      rw [he,T.coordinate_b] at hv
      exact lt_irrefl 0 hv
    · intro he
      rw [he,T.coordinate_c] at hu
      exact lt_irrefl 0 hu

def ClosedDiscTriangle.halfPlaneOpenSideA (T : ClosedDiscTriangle) : Set ℍ :=
  (discToClosedModel ∘ halfPlaneToDisc) ⁻¹' T.openSideA

theorem ClosedDiscTriangle.mem_halfPlaneOpenSideA_iff (T : ClosedDiscTriangle) (x : ℍ) :
    x ∈ T.halfPlaneOpenSideA ↔ 0 < (T.halfPlaneCoordinate x).1 ∧
      0 < (T.halfPlaneCoordinate x).2 ∧
        (T.halfPlaneCoordinate x).1 + (T.halfPlaneCoordinate x).2 = 1 :=
  T.mem_openSideA_iff_coordinate _

theorem ClosedDiscTriangle.halfPlaneCoordinate_image_closedHSegment (T : ClosedDiscTriangle)
    (z w : ℍ) : T.halfPlaneCoordinate '' closedHSegment z w =
      segment ℝ (T.halfPlaneCoordinate z) (T.halfPlaneCoordinate w) := by
  calc
    _ = T.coordinateAffine '' (halfPlaneKleinCoordinate '' closedHSegment z w) :=
      (image_image _ _ _).symm
    _ = _ := by
      rw [halfPlaneKlein_image_closedHSegment]
      exact image_segment ℝ T.coordinateAffine (halfPlaneKleinCoordinate z) (halfPlaneKleinCoordinate w)

theorem ClosedDiscTriangle.mem_closedHSegment_iff_halfPlaneCoordinate (T : ClosedDiscTriangle)
    (z w x : ℍ) : x ∈ closedHSegment z w ↔
      T.halfPlaneCoordinate x ∈ segment ℝ (T.halfPlaneCoordinate z) (T.halfPlaneCoordinate w) := by
  rw [← T.halfPlaneCoordinate_image_closedHSegment]
  exact T.halfPlaneCoordinate_isOpenEmbedding.injective.mem_set_image.symm

theorem ClosedDiscTriangle.halfPlane_ray_meets_open_opposite_side (T : ClosedDiscTriangle)
    {z : ℍ} (ha : T.a = discToClosedModel (halfPlaneToDisc z)) (R : HRayAt z)
    {x : ℍ} (hx : x ∈ T.halfPlaneInterior) (hxR : x ∈ R.val) :
    ∃ y : ℍ, y ∈ T.halfPlaneOpenSideA ∧ y ∈ R.val := by
  obtain ⟨hu,hv,hs⟩ := (T.mem_halfPlaneInterior_iff x).mp hx
  let s := (T.halfPlaneCoordinate x).1 + (T.halfPlaneCoordinate x).2
  have hs0 : 0 < s := add_pos hu hv
  let p : ℝ × ℝ := ((T.halfPlaneCoordinate x).1 / s,(T.halfPlaneCoordinate x).2 / s)
  have hp1 : 0 < p.1 := div_pos hu hs0
  have hp2 : 0 < p.2 := div_pos hv hs0
  have hpsum : p.1 + p.2 = 1 := by
    change (T.halfPlaneCoordinate x).1 / s + (T.halfPlaneCoordinate x).2 / s = 1
    rw [← add_div]
    exact div_self (ne_of_gt hs0)
  have hpD := T.open_opposite_segment_subset_openDomain ⟨hp1,hp2,hpsum⟩
  rw [← T.halfPlaneCoordinate_range] at hpD
  obtain ⟨y,hy⟩ := hpD
  have hySide : y ∈ T.halfPlaneOpenSideA := by
    rw [T.mem_halfPlaneOpenSideA_iff,hy]
    exact ⟨hp1,hp2,hpsum⟩
  have hzy : z ≠ y := by
    intro he
    have hh : (T.halfPlaneCoordinate z).1 = p.1 := by rw [he,hy]
    rw [T.halfPlaneCoordinate_at_a ha] at hh
    exact (ne_of_gt hp1) hh.symm
  have hzx : z ≠ x := by
    intro he
    rw [← he,T.halfPlaneCoordinate_at_a ha] at hu
    exact lt_irrefl 0 hu
  have hxSeg : x ∈ closedHSegment z y := by
    rw [T.mem_closedHSegment_iff_halfPlaneCoordinate,T.halfPlaneCoordinate_at_a ha,hy]
    refine ⟨1-s,s,by linarith,hs0.le,by ring,?_⟩
    ext <;> simp only [Prod.smul_fst,Prod.smul_snd,Prod.fst_add,Prod.snd_add,
      Prod.fst_zero,Prod.snd_zero,smul_eq_mul,mul_zero,zero_add]
    · exact mul_div_cancel₀ _ (ne_of_gt hs0)
    · exact mul_div_cancel₀ _ (ne_of_gt hs0)
  let S := hRayThrough z y hzy
  have hyS : y ∈ S.val := hRayThrough_mem _ _ _
  have hxS : x ∈ S.val := S.hConvex _ S.start_mem _ hyS hxSeg
  have hRS : R = S := R.eq_of_shared_point S hzx hxR hxS
  exact ⟨y,hySide,hRS.symm ▸ hyS⟩


theorem ClosedDiscTriangle.ray_meets_open_opposite_side (T : ClosedDiscTriangle) {z : 𝔻}
    (ha : T.a = discToClosedModel z) (R : DiscRayAt z) {x : 𝔻}
    (hx : x ∈ T.interior) (hxR : x ∈ R.val) :
    ∃ y : 𝔻, discToClosedModel y ∈ T.openSideA ∧ y ∈ R.val := by
  have hxH : discToHalfPlane x ∈ T.halfPlaneInterior := by
    change halfPlaneToDisc (discToHalfPlane x) ∈ T.interior
    rwa [halfPlaneToDisc_discToHalfPlane]
  have hxRH : discToHalfPlane x ∈ R.toHalfPlane.val := mem_image_of_mem _ hxR
  obtain ⟨y,hy,hyR⟩ := T.halfPlane_ray_meets_open_opposite_side
    (by rwa [halfPlaneToDisc_discToHalfPlane]) R.toHalfPlane hxH hxRH
  refine ⟨halfPlaneToDisc y,hy,?_⟩
  rw [R.carrier_eq_cayley]
  exact mem_image_of_mem _ hyR

theorem DiscLine.eq_of_two_closed_points (L M : DiscLine) {p q : 𝕔𝔻} (hpq : p ≠ q)
    (hpL : p ∈ L.closedCarrier) (hqL : q ∈ L.closedCarrier)
    (hpM : p ∈ M.closedCarrier) (hqM : q ∈ M.closedCarrier) : L = M := by
  obtain ⟨N,_,hN⟩ := existsUnique_discLine_closedCarrier p q hpq
  exact (hN L ⟨hpL,hqL⟩).trans (hN M ⟨hpM,hqM⟩).symm

theorem DiscLine.closedCarrier_hConvex (L : DiscLine) : ClosedDiscHConvex L.closedCarrier := by
  apply (closedDiscHConvex_iff_klein_convex _).mpr
  obtain ⟨n,t,_,he⟩ := L.exists_closedKlein_affine_chord
  rw [he]
  exact (convex_hyperplane ((innerSL ℝ n).toLinearMap.isLinear) t).inter (convex_closedBall _ _)

/-- From an actual finite or ideal vertex, the actual h-line through an interior
point reaches a finite point of the genuine open opposite side, with the interior
point between the vertex and that opposite point in the actual compactified arc. -/
theorem ClosedDiscTriangle.line_meets_open_opposite_side (T : ClosedDiscTriangle) (L : DiscLine)
    (haL : T.a ∈ L.closedCarrier) {x : 𝔻} (hx : x ∈ T.interior) (hxL : x ∈ L.carrier) :
    ∃ y : 𝔻, discToClosedModel y ∈ T.openSideA ∧ y ∈ L.carrier ∧
      discToClosedModel x ∈ closedModelDiscHSegment T.a (discToClosedModel y) := by
  have hxH : discToHalfPlane x ∈ T.halfPlaneInterior := by
    change halfPlaneToDisc (discToHalfPlane x) ∈ T.interior
    rwa [halfPlaneToDisc_discToHalfPlane]
  obtain ⟨hu,hv,hs⟩ := (T.mem_halfPlaneInterior_iff _).mp hxH
  let s := (T.halfPlaneCoordinate (discToHalfPlane x)).1 +
    (T.halfPlaneCoordinate (discToHalfPlane x)).2
  have hs0 : 0 < s := add_pos hu hv
  let p : ℝ × ℝ := ((T.halfPlaneCoordinate (discToHalfPlane x)).1 / s,
    (T.halfPlaneCoordinate (discToHalfPlane x)).2 / s)
  have hp1 : 0 < p.1 := div_pos hu hs0
  have hp2 : 0 < p.2 := div_pos hv hs0
  have hpsum : p.1 + p.2 = 1 := by
    change (T.halfPlaneCoordinate (discToHalfPlane x)).1 / s +
      (T.halfPlaneCoordinate (discToHalfPlane x)).2 / s = 1
    rw [← add_div]
    exact div_self (ne_of_gt hs0)
  have hpD := T.open_opposite_segment_subset_openDomain ⟨hp1,hp2,hpsum⟩
  rw [← T.halfPlaneCoordinate_range] at hpD
  obtain ⟨y,hy⟩ := hpD
  have hySide : discToClosedModel (halfPlaneToDisc y) ∈ T.openSideA := by
    change y ∈ T.halfPlaneOpenSideA
    rw [T.mem_halfPlaneOpenSideA_iff,hy]
    exact ⟨hp1,hp2,hpsum⟩
  have hxF : T.coordinate (discToClosedModel x) = T.halfPlaneCoordinate (discToHalfPlane x) := by
    change _ = T.coordinate (discToClosedModel (halfPlaneToDisc (discToHalfPlane x)))
    rw [halfPlaneToDisc_discToHalfPlane]
  have hyF : T.coordinate (discToClosedModel (halfPlaneToDisc y)) = p := hy
  have hax : T.a ≠ discToClosedModel x := by
    intro he
    have heF := congrArg T.coordinate he
    rw [T.coordinate_a,hxF] at heF
    have h0 := congrArg Prod.fst heF
    exact (ne_of_gt hu) h0.symm
  have hay : T.a ≠ discToClosedModel (halfPlaneToDisc y) := by
    intro he
    have heF := congrArg T.coordinate he
    rw [T.coordinate_a,hyF] at heF
    exact (ne_of_gt hp1) (congrArg Prod.fst heF).symm
  have hxSeg : discToClosedModel x ∈ closedModelDiscHSegment T.a
      (discToClosedModel (halfPlaneToDisc y)) := by
    rw [T.mem_closedSegment_iff_coordinate,T.coordinate_a,hxF,hyF]
    refine ⟨1-s,s,by linarith,hs0.le,by ring,?_⟩
    ext <;> simp only [Prod.smul_fst,Prod.smul_snd,Prod.fst_add,Prod.snd_add,
      smul_eq_mul,mul_zero,zero_add]
    · exact mul_div_cancel₀ _ (ne_of_gt hs0)
    · exact mul_div_cancel₀ _ (ne_of_gt hs0)
  obtain ⟨M,⟨haM,hyM⟩,_⟩ := existsUnique_discLine_closedCarrier T.a
    (discToClosedModel (halfPlaneToDisc y)) hay
  have hxM : discToClosedModel x ∈ M.closedCarrier := M.closedCarrier_hConvex _ haM _ hyM hxSeg
  have hLM : L = M := L.eq_of_two_closed_points M hax haL
    ((L.closedCarrier_mem_interior_iff x).mpr hxL) haM hxM
  refine ⟨halfPlaneToDisc y,hySide,?_,hxSeg⟩
  exact (L.closedCarrier_mem_interior_iff _).mp (hLM.symm ▸ hyM)


def ClosedHTriangle.openSideA (T : ClosedHTriangle) : Set ClosedHalfPlaneModel :=
  {p | p ∈ T.sideA ∧ p ≠ T.b ∧ p ≠ T.c}

theorem ClosedHTriangle.openSideA_cayley_mem (T : ClosedHTriangle) (p : ClosedHalfPlaneModel) :
    closedModelCayleyHomeomorph p ∈ T.toDiscTriangle.openSideA ↔ p ∈ T.openSideA := by
  change (closedModelCayleyHomeomorph p ∈ T.toDiscTriangle.sideA ∧
    closedModelCayleyHomeomorph p ≠ closedModelCayleyHomeomorph T.b ∧
    closedModelCayleyHomeomorph p ≠ closedModelCayleyHomeomorph T.c) ↔ _
  rw [← T.cayley_sideA]
  simp only [closedModelCayleyHomeomorph.injective.mem_set_image,
    closedModelCayleyHomeomorph.injective.ne_iff]
  rfl

theorem HalfPlaneLine.cayley_mem_carrier (L : HalfPlaneLine) (z : ℍ) :
    halfPlaneToDisc z ∈ L.toDiscLine.carrier ↔ z ∈ L.carrier := by
  rw [L.toDiscLine_carrier,L.discCarrier_eq_cayley_image]
  exact cayleyHomeomorph.injective.mem_set_image

def ClosedHTriangle.finiteCornerAtA (T : ClosedHTriangle) (z : ℍ)
    (ha : T.a = halfPlaneToClosedModel z) : T.toDiscTriangle.FiniteCorner z :=
  T.toDiscTriangle.finiteCornerAtA z (by
    change closedModelCayleyHomeomorph T.a = discToClosedModel (halfPlaneToDisc z)
    rw [ha,closedModelCayley_on_interior])

theorem ClosedHTriangle.locally_angleAtA (T : ClosedHTriangle) (z : ℍ)
    (ha : T.a = halfPlaneToClosedModel z) : ∃ r > 0,
    Metric.ball z r ∩ T.interior = Metric.ball z r ∩
      properHAngleInterior (T.finiteCornerAtA z ha).rayAB (T.finiteCornerAtA z ha).rayAC := by
  exact (T.finiteCornerAtA z ha).locally_interior (by
    change closedModelCayleyHomeomorph T.a = discToClosedModel (halfPlaneToDisc z)
    rw [ha,closedModelCayley_on_interior])

theorem ClosedHTriangle.ray_meets_open_opposite_side (T : ClosedHTriangle) {z : ℍ}
    (ha : T.a = halfPlaneToClosedModel z) (R : HRayAt z) {x : ℍ}
    (hx : x ∈ T.interior) (hxR : x ∈ R.val) :
    ∃ y : ℍ, halfPlaneToClosedModel y ∈ T.openSideA ∧ y ∈ R.val := by
  have haD : T.toDiscTriangle.a = discToClosedModel (halfPlaneToDisc z) := by
    change closedModelCayleyHomeomorph T.a = _
    rw [ha,closedModelCayley_on_interior]
  obtain ⟨y,hy,hyR⟩ := T.toDiscTriangle.halfPlane_ray_meets_open_opposite_side haD R hx hxR
  refine ⟨y,?_,hyR⟩
  apply (T.openSideA_cayley_mem _).mp
  rwa [closedModelCayley_on_interior]

theorem ClosedHTriangle.line_meets_open_opposite_side (T : ClosedHTriangle) (L : HalfPlaneLine)
    (haL : T.a ∈ L.closedCarrier) {x : ℍ} (hx : x ∈ T.interior) (hxL : x ∈ L.carrier) :
    ∃ y : ℍ, halfPlaneToClosedModel y ∈ T.openSideA ∧ y ∈ L.carrier ∧
      halfPlaneToClosedModel x ∈ closedModelHSegment T.a (halfPlaneToClosedModel y) := by
  have haD : T.toDiscTriangle.a ∈ L.toDiscLine.closedCarrier := by
    change closedModelCayleyHomeomorph T.a ∈ _
    rw [← L.cayley_image_closedCarrier]
    exact mem_image_of_mem _ haL
  obtain ⟨y,hy,hyL,hxy⟩ := T.toDiscTriangle.line_meets_open_opposite_side L.toDiscLine
    haD hx ((L.cayley_mem_carrier x).mpr hxL)
  refine ⟨discToHalfPlane y,?_,?_,?_⟩
  · apply (T.openSideA_cayley_mem _).mp
    rwa [closedModelCayley_on_interior,halfPlaneToDisc_discToHalfPlane]
  · apply (L.cayley_mem_carrier _).mp
    rwa [halfPlaneToDisc_discToHalfPlane]
  · change closedModelCayleyHomeomorph (halfPlaneToClosedModel x) ∈
      closedModelDiscHSegment (closedModelCayleyHomeomorph T.a)
        (closedModelCayleyHomeomorph (halfPlaneToClosedModel (discToHalfPlane y)))
    rw [closedModelCayley_on_interior,closedModelCayley_on_interior,halfPlaneToDisc_discToHalfPlane]
    exact hxy


theorem closedModelDiscHSegment_comm (p q : 𝕔𝔻) :
    closedModelDiscHSegment p q = closedModelDiscHSegment q p := by
  apply closedKleinCoordinate_injective.image_injective
  rw [closedKlein_image_closedModelDiscHSegment,closedKlein_image_closedModelDiscHSegment,segment_symm]

theorem DiscRayAt.trace_idealEndpoint {z : 𝔻} (R : DiscRayAt z) :
    discTraceIdealEndpoints R.val = {R.idealEndpoint} := by
  obtain ⟨_,_,_,_,_,he⟩ := R.isRay
  exact he

theorem DiscRayAt.idealEndpoint_eq_of_canonical_subset {z : 𝔻} (R : DiscRayAt z)
    (a : OnePoint ℂ) (ha : a ∈ extendedDiscIdealBoundary) (hsub : discHRay z a ⊆ R.val) :
    R.idealEndpoint = a := by
  have he : discTraceIdealEndpoints (discHRay z a) ⊆ discTraceIdealEndpoints R.val :=
    inter_subset_inter_left _ (closure_mono (image_mono hsub))
  rw [discHRay_idealEndpoints z a ha,R.trace_idealEndpoint] at he
  exact (mem_singleton_iff.mp (he (mem_singleton a))).symm

theorem ClosedDiscTriangle.cornerRayABAtA_idealEndpoint (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) (hb : ‖(T.b : ℂ)‖ = 1) :
    (T.cornerRayABAtA z ha).idealEndpoint = closedDiscToExtended T.b := by
  have hbE : closedDiscToExtended T.b ∈ extendedDiscIdealBoundary :=
    (coe_mem_extendedDiscIdealBoundary (T.b : ℂ)).mpr hb
  apply (T.cornerRayABAtA z ha).idealEndpoint_eq_of_canonical_subset _ hbE
  intro x hx
  apply T.cornerAtA_sideC_finite_subset z ha
  change discToClosedModel x ∈ closedModelDiscHSegment T.a T.b
  rw [ha,closedModelDiscHSegment_ray z T.b hb]
  exact subset_closure (mem_image_of_mem discToClosedModel hx)

theorem ClosedDiscTriangle.cornerRayACAtA_idealEndpoint (T : ClosedDiscTriangle) (z : 𝔻)
    (ha : T.a = discToClosedModel z) (hc : ‖(T.c : ℂ)‖ = 1) :
    (T.cornerRayACAtA z ha).idealEndpoint = closedDiscToExtended T.c := by
  have hcE : closedDiscToExtended T.c ∈ extendedDiscIdealBoundary :=
    (coe_mem_extendedDiscIdealBoundary (T.c : ℂ)).mpr hc
  apply (T.cornerRayACAtA z ha).idealEndpoint_eq_of_canonical_subset _ hcE
  intro x hx
  apply T.cornerAtA_sideB_finite_subset z ha
  change discToClosedModel x ∈ closedModelDiscHSegment T.c T.a
  rw [closedModelDiscHSegment_comm,ha,closedModelDiscHSegment_ray z T.c hc]
  exact subset_closure (mem_image_of_mem discToClosedModel hx)

theorem DiscTriangle.cornerRayABAtA_toClosedDiscTriangle (T : DiscTriangle) :
    T.toClosedDiscTriangle.cornerRayABAtA T.a rfl = T.rayAB := by
  apply DiscRayAt.eq_of_shared_point _ _ T.a_ne_b
  · apply T.toClosedDiscTriangle.cornerAtA_sideC_finite_subset T.a rfl
    change T.toClosedDiscTriangle.b ∈ T.toClosedDiscTriangle.sideC
    rw [T.toClosedDiscTriangle.mem_sideC_iff_coordinate,T.toClosedDiscTriangle.coordinate_b]
    norm_num
  · exact discRayThrough_mem _ _ _

theorem DiscTriangle.cornerRayACAtA_toClosedDiscTriangle (T : DiscTriangle) :
    T.toClosedDiscTriangle.cornerRayACAtA T.a rfl = T.rayAC := by
  apply DiscRayAt.eq_of_shared_point _ _ T.c_ne_a.symm
  · apply T.toClosedDiscTriangle.cornerAtA_sideB_finite_subset T.a rfl
    change T.toClosedDiscTriangle.c ∈ T.toClosedDiscTriangle.sideB
    rw [T.toClosedDiscTriangle.mem_sideB_iff_coordinate,T.toClosedDiscTriangle.coordinate_c]
    norm_num
  · exact discRayThrough_mem _ _ _

theorem DiscTriangle.cornerAngleAtA_toClosedDiscTriangle (T : DiscTriangle) :
    T.toClosedDiscTriangle.cornerAngleAtA T.a rfl = T.angleA := by
  change s(T.toClosedDiscTriangle.cornerRayABAtA T.a rfl,
    T.toClosedDiscTriangle.cornerRayACAtA T.a rfl) = _
  rw [T.cornerRayABAtA_toClosedDiscTriangle,T.cornerRayACAtA_toClosedDiscTriangle]
  rfl

end
end LowDimensionalTopology.Geometry.Hyperbolic
