/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.ClosedHull
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.ClosedDisk

/-! # Genuine finite compatibility of the compactified triangle construction -/

@[expose] public section
open Set Module
open scoped UpperHalfPlane OnePoint Topology Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

theorem HConvex.triangleCoordinate_image {S : Set ℍ} (hS : HConvex S) (T : HTriangle) :
    Convex ℝ (T.coordinate '' S) := by
  have hK : Convex ℝ (halfPlaneKleinCoordinate '' S) := by
    change Convex ℝ ((fun x : ℍ => kleinCoordinate (halfPlaneToDisc x)) '' S)
    rw [← image_image kleinCoordinate halfPlaneToDisc S]
    exact (discHConvex_iff_klein_convex _).mp ((hConvex_iff_cayley_discHConvex _).mp hS)
  have he : T.coordinate '' S = T.coordinateAffine '' (halfPlaneKleinCoordinate '' S) := by
    rw [image_image]
    apply image_congr
    intro x _
    change T.coordinateHomeomorph (halfPlaneKleinCoordinate x) = T.coordinateAffine (halfPlaneKleinCoordinate x)
    exact (T.coordinateAffine_apply _).symm
  rw [he]
  exact hK.affine_image T.coordinateAffine

theorem HTriangle.a_mem_closure_interior (T : HTriangle) : T.a ∈ closure T.interior := by
  apply T.coordinate_isOpenEmbedding.injective.mem_set_image.mp
  rw [T.coordinate_image_closure,T.coordinate_a]
  norm_num [standardClosedTriangle]

theorem HTriangle.b_mem_closure_interior (T : HTriangle) : T.b ∈ closure T.interior := by
  apply T.coordinate_isOpenEmbedding.injective.mem_set_image.mp
  rw [T.coordinate_image_closure,T.coordinate_b]
  norm_num [standardClosedTriangle]

theorem HTriangle.c_mem_closure_interior (T : HTriangle) : T.c ∈ closure T.interior := by
  apply T.coordinate_isOpenEmbedding.injective.mem_set_image.mp
  rw [T.coordinate_image_closure,T.coordinate_c]
  norm_num [standardClosedTriangle]

theorem HTriangle.closure_min_hConvex (T : HTriangle) {U : Set ℍ} (hU : HConvex U)
    (ha : T.a ∈ U) (hb : T.b ∈ U) (hc : T.c ∈ U) : closure T.interior ⊆ U := by
  have hs : standardClosedTriangle ⊆ T.coordinate '' U := by
    apply standardClosedTriangle_subset_convex (hU.triangleCoordinate_image T)
    · exact T.coordinate_a ▸ mem_image_of_mem T.coordinate ha
    · exact T.coordinate_b ▸ mem_image_of_mem T.coordinate hb
    · exact T.coordinate_c ▸ mem_image_of_mem T.coordinate hc
  intro x hx
  apply T.coordinate_isOpenEmbedding.injective.mem_set_image.mp
  apply hs
  have he := mem_image_of_mem T.coordinate hx
  rwa [T.coordinate_image_closure] at he

theorem inverseCayley_image_hConvex {S : Set 𝔻} (hS : DiscHConvex S) :
    HConvex (discToHalfPlane '' S) := by
  apply (hConvex_iff_cayley_discHConvex _).mpr
  rw [cayley_image_inverse_image]
  exact hS

theorem DiscTriangle.a_mem_closure_interior (T : DiscTriangle) : T.a ∈ closure T.interior := by
  rw [T.closure_eq_cayley]
  exact ⟨discToHalfPlane T.a,T.toHalfPlane.a_mem_closure_interior,halfPlaneToDisc_discToHalfPlane T.a⟩

theorem DiscTriangle.b_mem_closure_interior (T : DiscTriangle) : T.b ∈ closure T.interior := by
  rw [T.closure_eq_cayley]
  exact ⟨discToHalfPlane T.b,T.toHalfPlane.b_mem_closure_interior,halfPlaneToDisc_discToHalfPlane T.b⟩

theorem DiscTriangle.c_mem_closure_interior (T : DiscTriangle) : T.c ∈ closure T.interior := by
  rw [T.closure_eq_cayley]
  exact ⟨discToHalfPlane T.c,T.toHalfPlane.c_mem_closure_interior,halfPlaneToDisc_discToHalfPlane T.c⟩

theorem DiscTriangle.closure_min_discHConvex (T : DiscTriangle) {U : Set 𝔻}
    (hU : DiscHConvex U) (ha : T.a ∈ U) (hb : T.b ∈ U) (hc : T.c ∈ U) :
    closure T.interior ⊆ U := by
  intro x hx
  rw [T.closure_eq_cayley] at hx
  obtain ⟨u,hu,rfl⟩ := hx
  have huU := T.toHalfPlane.closure_min_hConvex (inverseCayley_image_hConvex hU)
    ⟨T.a,ha,rfl⟩ ⟨T.b,hb,rfl⟩ ⟨T.c,hc,rfl⟩ hu
  obtain ⟨z,hz,he⟩ := huU
  have he' := congrArg halfPlaneToDisc he
  rw [halfPlaneToDisc_discToHalfPlane] at he'
  exact he' ▸ hz

theorem discToClosedModel_image_hConvex_iff (S : Set 𝔻) :
    ClosedDiscHConvex (discToClosedModel '' S) ↔ DiscHConvex S := by
  rw [closedDiscHConvex_iff_klein_convex,discHConvex_iff_klein_convex]
  have he : closedKleinCoordinate '' (discToClosedModel '' S) = kleinCoordinate '' S := by
    rw [image_image]
    apply image_congr
    intro z _
    exact closedKleinCoordinate_disc_inclusion z
  rw [he]

theorem ClosedDiscHConvex.disc_preimage {S : Set 𝕔𝔻} (hS : ClosedDiscHConvex S) :
    DiscHConvex (discToClosedModel ⁻¹' S) := by
  intro z hz w hw u hu
  have hi := mem_image_of_mem discToClosedModel hu
  rw [← closedModelDiscHSegment_interior] at hi
  exact hS (discToClosedModel z) hz (discToClosedModel w) hw hi


theorem openEmbedding_image_interior {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsOpenEmbedding f) (S : Set X) :
    f '' _root_.interior S = _root_.interior (f '' S) := by
  apply subset_antisymm (hf.isOpenMap.image_interior_subset S)
  intro y hy
  obtain ⟨x,_,rfl⟩ := interior_subset hy
  refine ⟨x,?_,rfl⟩
  have hx : x ∈ f ⁻¹' _root_.interior (f '' S) := hy
  rw [hf.isOpenMap.preimage_interior_eq_interior_preimage hf.continuous,
    preimage_image_eq _ hf.injective] at hx
  exact hx

theorem HTriangle.interior_closure (T : HTriangle) : _root_.interior (closure T.interior) = T.interior := by
  rw [T.closure_coordinate_preimage,
    ← T.coordinate_isOpenEmbedding.isOpenMap.preimage_interior_eq_interior_preimage
      T.coordinate_isOpenEmbedding.continuous,
    standardClosedTriangle_interior,← T.coordinate_image_interior,
    preimage_image_eq _ T.coordinate_isOpenEmbedding.injective]

theorem DiscTriangle.interior_closure (T : DiscTriangle) : _root_.interior (closure T.interior) = T.interior := by
  rw [T.closure_eq_cayley]
  have he : halfPlaneToDisc '' _root_.interior (closure T.toHalfPlane.interior) =
      _root_.interior (halfPlaneToDisc '' closure T.toHalfPlane.interior) := cayleyHomeomorph.image_interior _
  rw [← he,T.toHalfPlane.interior_closure,← T.interior_eq_cayley]

theorem HTriangle.complexInterior_regularOpen (T : HTriangle) :
    _root_.interior (closure T.complexInterior) = T.complexInterior := by
  rw [T.complexInterior_closure,← openEmbedding_image_interior UpperHalfPlane.isOpenEmbedding_coe,
    T.interior_closure]
  rfl

theorem DiscTriangle.complexInterior_regularOpen (T : DiscTriangle) :
    _root_.interior (closure T.complexInterior) = T.complexInterior := by
  rw [T.complexInterior_closure,← openEmbedding_image_interior disc_isOpenEmbedding_coe,
    T.interior_closure]
  rfl

theorem DiscTriangle.closedCarrier_toClosedDiscTriangle (T : DiscTriangle) :
    T.toClosedDiscTriangle.closedCarrier = discToClosedModel '' closure T.interior := by
  apply subset_antisymm
  · change closedDiscHConvexHull {discToClosedModel T.a,discToClosedModel T.b,discToClosedModel T.c} ⊆ _
    apply closedDiscHConvexHull_min
      ((discToClosedModel_image_hConvex_iff _).mpr T.interior_discHConvex.closure)
    intro p hp
    simp only [mem_insert_iff,mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl
    · exact mem_image_of_mem _ T.a_mem_closure_interior
    · exact mem_image_of_mem _ T.b_mem_closure_interior
    · exact mem_image_of_mem _ T.c_mem_closure_interior
  · rintro p ⟨z,hz,rfl⟩
    have hpre : DiscHConvex (discToClosedModel ⁻¹' T.toClosedDiscTriangle.closedCarrier) :=
      (closedDiscHConvexHull_convex _).disc_preimage
    apply T.closure_min_discHConvex hpre _ _ _ hz
    all_goals apply subset_closedDiscHConvexHull; simp [DiscTriangle.toClosedDiscTriangle]

theorem DiscTriangle.complexClosedCarrier_toClosedDiscTriangle (T : DiscTriangle) :
    T.toClosedDiscTriangle.complexClosedCarrier = closure T.complexInterior := by
  rw [ClosedDiscTriangle.complexClosedCarrier,T.closedCarrier_toClosedDiscTriangle,image_image]
  change ((↑) : 𝔻 → ℂ) '' closure T.interior = closure T.complexInterior
  exact T.complexInterior_closure.symm

theorem DiscTriangle.complexInterior_toClosedDiscTriangle (T : DiscTriangle) :
    T.toClosedDiscTriangle.complexInterior = T.complexInterior := by
  rw [ClosedDiscTriangle.complexInterior,T.complexClosedCarrier_toClosedDiscTriangle,
    T.complexInterior_regularOpen]

theorem DiscTriangle.interior_toClosedDiscTriangle (T : DiscTriangle) :
    T.toClosedDiscTriangle.interior = T.interior := by
  rw [ClosedDiscTriangle.interior,T.complexInterior_toClosedDiscTriangle]
  change ((↑) : 𝔻 → ℂ) ⁻¹' (((↑) : 𝔻 → ℂ) '' T.interior) = T.interior
  exact preimage_image_eq _ Complex.UnitDisc.coe_injective

theorem DiscTriangle.sideA_toClosedDiscTriangle (T : DiscTriangle) :
    T.toClosedDiscTriangle.sideA = discToClosedModel '' T.sideA :=
  closedModelDiscHSegment_interior _ _

theorem DiscTriangle.sideB_toClosedDiscTriangle (T : DiscTriangle) :
    T.toClosedDiscTriangle.sideB = discToClosedModel '' T.sideB :=
  closedModelDiscHSegment_interior _ _

theorem DiscTriangle.sideC_toClosedDiscTriangle (T : DiscTriangle) :
    T.toClosedDiscTriangle.sideC = discToClosedModel '' T.sideC :=
  closedModelDiscHSegment_interior _ _

end
end LowDimensionalTopology.Geometry.Hyperbolic
