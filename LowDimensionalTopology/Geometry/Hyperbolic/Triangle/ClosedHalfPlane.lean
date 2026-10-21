/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.FiniteIdealTriangleAdapters

/-!
# Actual compactified H triangles, including infinity
-/

@[expose] public section
open Set Module
open scoped UpperHalfPlane OnePoint Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem DiscLine.closedCarrier_cayley_mem (L : DiscLine) (p : ClosedHalfPlaneModel) :
    closedModelCayleyHomeomorph p ∈ L.closedCarrier ↔ p ∈ L.toHalfPlane.closedCarrier := by
  have he : closedModelCayleyHomeomorph '' L.toHalfPlane.closedCarrier = L.closedCarrier := by
    rw [L.toHalfPlane.cayley_image_closedCarrier,L.toHalfPlane_spec]
  rw [← he]
  exact closedModelCayleyHomeomorph.injective.mem_set_image

structure ClosedHTriangle where
  a : ClosedHalfPlaneModel
  b : ClosedHalfPlaneModel
  c : ClosedHalfPlaneModel
  noncollinear : ¬ ∃ L : HalfPlaneLine,
    a ∈ L.closedCarrier ∧ b ∈ L.closedCarrier ∧ c ∈ L.closedCarrier

def ClosedHTriangle.toDiscTriangle (T : ClosedHTriangle) : ClosedDiscTriangle where
  a := closedModelCayleyHomeomorph T.a
  b := closedModelCayleyHomeomorph T.b
  c := closedModelCayleyHomeomorph T.c
  noncollinear := by
    rintro ⟨L,ha,hb,hc⟩
    exact T.noncollinear ⟨L.toHalfPlane,(L.closedCarrier_cayley_mem T.a).mp ha,
      (L.closedCarrier_cayley_mem T.b).mp hb,(L.closedCarrier_cayley_mem T.c).mp hc⟩

/-- The actual geodesic convex hull in the OnePoint H compactification. -/
def closedHalfPlaneHConvexHull (S : Set ClosedHalfPlaneModel) : Set ClosedHalfPlaneModel :=
  {p | ∀ U : Set ClosedHalfPlaneModel, ClosedHalfPlaneHConvex U → S ⊆ U → p ∈ U}

theorem subset_closedHalfPlaneHConvexHull (S : Set ClosedHalfPlaneModel) :
    S ⊆ closedHalfPlaneHConvexHull S := fun _ hp _ _ hU => hU hp

theorem closedHalfPlaneHConvexHull_min {S U : Set ClosedHalfPlaneModel}
    (hU : ClosedHalfPlaneHConvex U) (hSU : S ⊆ U) : closedHalfPlaneHConvexHull S ⊆ U :=
  fun _ hp => hp U hU hSU

theorem closedHalfPlaneHConvexHull_convex (S : Set ClosedHalfPlaneModel) :
    ClosedHalfPlaneHConvex (closedHalfPlaneHConvexHull S) := by
  intro p hp q hq x hx U hU hSU
  exact hU p (hp U hU hSU) q (hq U hU hSU) hx

theorem closedHalfPlaneHConvexHull_cayley_image (S : Set ClosedHalfPlaneModel) :
    closedModelCayleyHomeomorph '' closedHalfPlaneHConvexHull S =
      closedDiscHConvexHull (closedModelCayleyHomeomorph '' S) := by
  apply subset_antisymm
  · apply image_subset_iff.mpr
    apply closedHalfPlaneHConvexHull_min
    · apply (closedHalfPlaneHConvex_iff_cayley _).mpr
      rw [closedModelCayleyHomeomorph.image_preimage]
      exact closedDiscHConvexHull_convex _
    · intro p hp
      exact subset_closedDiscHConvexHull _ (mem_image_of_mem _ hp)
  · apply closedDiscHConvexHull_min
    · exact (closedHalfPlaneHConvex_iff_cayley _).mp (closedHalfPlaneHConvexHull_convex S)
    · exact image_mono (subset_closedHalfPlaneHConvexHull S)

def ClosedHTriangle.closedCarrier (T : ClosedHTriangle) : Set ClosedHalfPlaneModel :=
  closedHalfPlaneHConvexHull {T.a,T.b,T.c}

def ClosedHTriangle.sideA (T : ClosedHTriangle) : Set ClosedHalfPlaneModel := closedModelHSegment T.b T.c

def ClosedHTriangle.sideB (T : ClosedHTriangle) : Set ClosedHalfPlaneModel := closedModelHSegment T.c T.a

def ClosedHTriangle.sideC (T : ClosedHTriangle) : Set ClosedHalfPlaneModel := closedModelHSegment T.a T.b

theorem ClosedHTriangle.cayley_closedCarrier (T : ClosedHTriangle) :
    closedModelCayleyHomeomorph '' T.closedCarrier = T.toDiscTriangle.closedCarrier := by
  rw [ClosedHTriangle.closedCarrier,closedHalfPlaneHConvexHull_cayley_image,
    image_insert_eq,image_insert_eq,image_singleton]
  rfl

theorem ClosedHTriangle.cayley_sideA (T : ClosedHTriangle) :
    closedModelCayleyHomeomorph '' T.sideA = T.toDiscTriangle.sideA :=
  cayley_image_closedModelHSegment _ _

theorem ClosedHTriangle.cayley_sideB (T : ClosedHTriangle) :
    closedModelCayleyHomeomorph '' T.sideB = T.toDiscTriangle.sideB :=
  cayley_image_closedModelHSegment _ _

theorem ClosedHTriangle.cayley_sideC (T : ClosedHTriangle) :
    closedModelCayleyHomeomorph '' T.sideC = T.toDiscTriangle.sideC :=
  cayley_image_closedModelHSegment _ _

theorem ClosedHTriangle.closedCarrier_isCompact (T : ClosedHTriangle) : IsCompact T.closedCarrier := by
  apply closedModelCayleyHomeomorph.isCompact_image.mp
  rw [T.cayley_closedCarrier]
  apply Complex.UnitClosedDisc.isEmbedding_coe.isCompact_iff.mpr
  exact T.toDiscTriangle.complexClosedCarrier_isCompact

theorem ClosedHTriangle.closedCarrier_hConvex (T : ClosedHTriangle) : ClosedHalfPlaneHConvex T.closedCarrier :=
  closedHalfPlaneHConvexHull_convex _

/-- The actual finite H open interior; the vertices themselves may include infinity. -/
def ClosedHTriangle.interior (T : ClosedHTriangle) : Set ℍ :=
  halfPlaneToDisc ⁻¹' T.toDiscTriangle.interior

theorem ClosedHTriangle.cayley_interior (T : ClosedHTriangle) :
    halfPlaneToDisc '' T.interior = T.toDiscTriangle.interior :=
  cayleyHomeomorph.image_preimage _

theorem ClosedHTriangle.interior_hConvex (T : ClosedHTriangle) : HConvex T.interior := by
  apply (hConvex_iff_cayley_discHConvex _).mpr
  rw [T.cayley_interior]
  exact T.toDiscTriangle.interior_discHConvex

theorem ClosedHTriangle.interior_nonempty (T : ClosedHTriangle) : T.interior.Nonempty := by
  have hm : (halfPlaneToDisc '' T.interior).Nonempty := by
    rw [T.cayley_interior]
    exact T.toDiscTriangle.interior_nonempty
  exact image_nonempty.mp hm

theorem ClosedHTriangle.interior_isOpen (T : ClosedHTriangle) : IsOpen T.interior :=
  T.toDiscTriangle.interior_isOpen.preimage continuous_halfPlaneToDisc

theorem ClosedHTriangle.interior_isPreconnected (T : ClosedHTriangle) : IsPreconnected T.interior :=
  T.interior_hConvex.isPreconnected


theorem ClosedDiscTriangle.closedSides_circle_homeomorph (T : ClosedDiscTriangle) :
    Nonempty (↥(T.sideA ∪ T.sideB ∪ T.sideC : Set 𝕔𝔻) ≃ₜ Metric.sphere (0 : ℝ × ℝ) 1) := by
  obtain ⟨h⟩ := T.boundary_circle_homeomorph
  exact ⟨(Complex.UnitClosedDisc.isEmbedding_coe.homeomorphImage
    (T.sideA ∪ T.sideB ∪ T.sideC)).trans
      ((Homeomorph.setCongr T.complexInterior_frontier.symm).trans h)⟩

theorem ClosedHTriangle.boundary_circle_homeomorph (T : ClosedHTriangle) :
    Nonempty (↥(T.sideA ∪ T.sideB ∪ T.sideC : Set ClosedHalfPlaneModel) ≃ₜ Metric.sphere (0 : ℝ × ℝ) 1) := by
  obtain ⟨h⟩ := T.toDiscTriangle.closedSides_circle_homeomorph
  have he : closedModelCayleyHomeomorph '' (T.sideA ∪ T.sideB ∪ T.sideC) =
      T.toDiscTriangle.sideA ∪ T.toDiscTriangle.sideB ∪ T.toDiscTriangle.sideC := by
    rw [image_union,image_union,T.cayley_sideA,T.cayley_sideB,T.cayley_sideC]
  exact ⟨(closedModelCayleyHomeomorph.isEmbedding.homeomorphImage
    (T.sideA ∪ T.sideB ∪ T.sideC)).trans ((Homeomorph.setCongr he).trans h)⟩

theorem ClosedHTriangle.exists_jordan_curve (T : ClosedHTriangle) :
    ∃ γ : Metric.sphere (0 : ℝ × ℝ) 1 → ClosedHalfPlaneModel,
      Continuous γ ∧ Function.Injective γ ∧ range γ = T.sideA ∪ T.sideB ∪ T.sideC := by
  obtain ⟨h⟩ := T.boundary_circle_homeomorph
  let γ : Metric.sphere (0 : ℝ × ℝ) 1 → ClosedHalfPlaneModel := fun p => (h.symm p).val
  refine ⟨γ,continuous_subtype_val.comp h.symm.continuous,?_,?_⟩
  · intro p q he
    apply h.symm.injective
    exact Subtype.ext he
  · ext x
    constructor
    · rintro ⟨p,rfl⟩
      exact (h.symm p).property
    · intro hx
      refine ⟨h ⟨x,hx⟩,?_⟩
      change (h.symm (h ⟨x,hx⟩)).val = x
      rw [h.symm_apply_apply]

/-- This is an actual sphere Jordan curve in the extended complex plane; an ideal vertex
may be infinity, so ordinary-plane boundedness is not imposed on this chart. -/
theorem ClosedHTriangle.exists_extended_jordan_curve (T : ClosedHTriangle) :
    ∃ γ : Metric.sphere (0 : ℝ × ℝ) 1 → OnePoint ℂ, Continuous γ ∧ Function.Injective γ ∧
      range γ = (Subtype.val : ClosedHalfPlaneModel → OnePoint ℂ) '' (T.sideA ∪ T.sideB ∪ T.sideC) := by
  obtain ⟨γ,hγc,hγi,hγr⟩ := T.exists_jordan_curve
  refine ⟨Subtype.val ∘ γ,continuous_subtype_val.comp hγc,Subtype.val_injective.comp hγi,?_⟩
  rw [range_comp,hγr]


theorem HalfPlaneLine.closedCarrier_mem_interior_iff (L : HalfPlaneLine) (z : ℍ) :
    halfPlaneToClosedModel z ∈ L.closedCarrier ↔ z ∈ L.carrier := by
  calc
    _ ↔ closedModelCayleyHomeomorph (halfPlaneToClosedModel z) ∈
        closedModelCayleyHomeomorph '' L.closedCarrier := closedModelCayleyHomeomorph.injective.mem_set_image.symm
    _ ↔ discToClosedModel (halfPlaneToDisc z) ∈ L.toDiscLine.closedCarrier := by
      rw [closedModelCayley_on_interior,L.cayley_image_closedCarrier]
    _ ↔ halfPlaneToDisc z ∈ L.toDiscLine.carrier := L.toDiscLine.closedCarrier_mem_interior_iff _
    _ ↔ z ∈ L.carrier := by
      rw [L.toDiscLine_carrier,L.discCarrier_eq_cayley_image]
      exact (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective).mem_set_image

def HTriangle.toDiscTriangle (T : HTriangle) : DiscTriangle where
  a := halfPlaneToDisc T.a
  b := halfPlaneToDisc T.b
  c := halfPlaneToDisc T.c
  noncollinear := by
    rintro ⟨L,ha,hb,hc⟩
    apply T.noncollinear
    refine ⟨L.toHalfPlane,?_,?_,?_⟩
    · simpa only [discToHalfPlane_halfPlaneToDisc] using (L.mem_carrier _).mp ha
    · simpa only [discToHalfPlane_halfPlaneToDisc] using (L.mem_carrier _).mp hb
    · simpa only [discToHalfPlane_halfPlaneToDisc] using (L.mem_carrier _).mp hc

theorem HTriangle.toDiscTriangle_toHalfPlane (T : HTriangle) : T.toDiscTriangle.toHalfPlane = T := by
  cases T with
  | mk a b c hn =>
    change HTriangle.mk (discToHalfPlane (halfPlaneToDisc a))
      (discToHalfPlane (halfPlaneToDisc b)) (discToHalfPlane (halfPlaneToDisc c)) _ = _
    simp only [discToHalfPlane_halfPlaneToDisc]

theorem HTriangle.toDiscTriangle_interior (T : HTriangle) :
    T.toDiscTriangle.interior = halfPlaneToDisc '' T.interior := by
  rw [T.toDiscTriangle.interior_eq_cayley,T.toDiscTriangle_toHalfPlane]

theorem HTriangle.toDiscTriangle_closure (T : HTriangle) :
    closure T.toDiscTriangle.interior = halfPlaneToDisc '' closure T.interior := by
  rw [T.toDiscTriangle.closure_eq_cayley,T.toDiscTriangle_toHalfPlane]

def HTriangle.toClosedHTriangle (T : HTriangle) : ClosedHTriangle where
  a := halfPlaneToClosedModel T.a
  b := halfPlaneToClosedModel T.b
  c := halfPlaneToClosedModel T.c
  noncollinear := by
    rintro ⟨L,ha,hb,hc⟩
    exact T.noncollinear ⟨L,(L.closedCarrier_mem_interior_iff T.a).mp ha,
      (L.closedCarrier_mem_interior_iff T.b).mp hb,(L.closedCarrier_mem_interior_iff T.c).mp hc⟩

theorem HTriangle.toClosedHTriangle_toDiscTriangle (T : HTriangle) :
    T.toClosedHTriangle.toDiscTriangle = T.toDiscTriangle.toClosedDiscTriangle := by
  change ClosedDiscTriangle.mk
    (closedModelCayleyHomeomorph (halfPlaneToClosedModel T.a))
    (closedModelCayleyHomeomorph (halfPlaneToClosedModel T.b))
    (closedModelCayleyHomeomorph (halfPlaneToClosedModel T.c)) _ = _
  simp only [closedModelCayley_on_interior]
  rfl

theorem HTriangle.closedCarrier_toClosedHTriangle (T : HTriangle) :
    T.toClosedHTriangle.closedCarrier = halfPlaneToClosedModel '' closure T.interior := by
  apply closedModelCayleyHomeomorph.injective.image_injective
  rw [T.toClosedHTriangle.cayley_closedCarrier,T.toClosedHTriangle_toDiscTriangle,
    T.toDiscTriangle.closedCarrier_toClosedDiscTriangle,T.toDiscTriangle_closure,
    image_image,image_image]
  apply image_congr
  intro z _
  exact (closedModelCayley_on_interior z).symm

theorem HTriangle.interior_toClosedHTriangle (T : HTriangle) :
    T.toClosedHTriangle.interior = T.interior := by
  rw [ClosedHTriangle.interior,T.toClosedHTriangle_toDiscTriangle,
    T.toDiscTriangle.interior_toClosedDiscTriangle,T.toDiscTriangle_interior]
  exact preimage_image_eq _ (show Function.Injective halfPlaneToDisc from cayleyHomeomorph.injective)

theorem HTriangle.sideA_toClosedHTriangle (T : HTriangle) :
    T.toClosedHTriangle.sideA = halfPlaneToClosedModel '' T.sideA := closedModelHSegment_interior _ _

theorem HTriangle.sideB_toClosedHTriangle (T : HTriangle) :
    T.toClosedHTriangle.sideB = halfPlaneToClosedModel '' T.sideB := closedModelHSegment_interior _ _

theorem HTriangle.sideC_toClosedHTriangle (T : HTriangle) :
    T.toClosedHTriangle.sideC = halfPlaneToClosedModel '' T.sideC := closedModelHSegment_interior _ _

end
end LowDimensionalTopology.Geometry.Hyperbolic
