module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularNielsenMirrorClips

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open Fuchsian

private theorem closure_inter_mirror_of_open_clip {K : Set ℍ}
    (hoK : IsOpen K) (hK : HConvex K) (L : HalfPlaneLine) (p q : ℍ)
    (hpq : p ≠ q) (hclip : K ∩ L.carrier = openHSegment p q) :
    closure K ∩ L.carrier = closedHSegment p q := by
  let k : ℍ → ℂ := halfPlaneKleinCoordinate
  let U : Set ℂ := k '' K
  have hk : Topology.IsOpenEmbedding k := isOpenEmbedding_halfPlaneKleinCoordinate
  have hoU : IsOpen U := hk.isOpenMap K hoK
  have hcU : Convex ℝ U := by
    have hc := (discHConvex_iff_klein_convex _).mp
      ((hConvex_iff_cayley_discHConvex K).mp hK)
    rw [image_image] at hc
    exact hc
  have hn : (openHSegment p q).Nonempty := by
    apply closure_nonempty_iff.mp
    rw [closure_openHSegment hpq]
    exact ⟨p, mem_closedHSegment_of_dist_triangle_eq hpq (by simp)⟩
  obtain ⟨m, hm⟩ := hn
  have hmK : m ∈ K ∩ L.carrier := hclip.symm ▸ hm
  have hLc : IsClosed L.carrier := by
    have he : L.carrier = {z : ℍ | L.reflection z = z} := by
      ext z
      exact (L.reflection_fixed_iff z).symm
    rw [he]
    exact isClosed_eq (halfPlaneLineReflectionIsometry L).continuous continuous_id
  apply subset_antisymm
  · rintro z ⟨hzK, hzL⟩
    have hzU : k z ∈ closure U :=
      image_closure_subset_closure_image hk.continuous ⟨z, hzK, rfl⟩
    have hmU : k m ∈ interior U := by
      rw [hoU.interior_eq]
      exact ⟨m, hmK.1, rfl⟩
    have hs : openSegment ℝ (k z) (k m) ⊆ k '' (K ∩ L.carrier) := by
      intro y hy
      have hyU : y ∈ U := interior_subset
        (hcU.openSegment_closure_interior_subset_interior hzU hmU hy)
      obtain ⟨w, hwK, hwy⟩ := hyU
      have hyseg : y ∈ k '' closedHSegment z m := by
        rw [halfPlaneKlein_image_closedHSegment]
        exact openSegment_subset_segment ℝ (k z) (k m) hy
      obtain ⟨v, hv, hvy⟩ := hyseg
      have hwv : w = v := hk.injective (hwy.trans hvy.symm)
      exact ⟨w, ⟨hwK, hwv.symm ▸ L.hConvex z hzL m hmK.2 hv⟩, hwy⟩
    have hzcl : k z ∈ closure (k '' (K ∩ L.carrier)) :=
      closure_mono hs (segment_subset_closure_openSegment (left_mem_segment ℝ (k z) (k m)))
    have hzclip : z ∈ closure (K ∩ L.carrier) := by
      rw [hk.isEmbedding.closure_eq_preimage_closure_image]
      exact hzcl
    rwa [hclip, closure_openHSegment hpq] at hzclip
  · intro z hz
    have hzclip : z ∈ closure (K ∩ L.carrier) := by
      rw [hclip, closure_openHSegment hpq]
      exact hz
    exact ⟨closure_mono inter_subset_left hzclip,
      (closure_minimal inter_subset_right hLc) hzclip⟩

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
  (hin : 1 + r < x) (hout : x + r < E)
local notation "P" => annularPairReflectionHalfPlaneData E r x hE hr hin hout
local notation "D" => HalfPlaneFuchsianGroup.cayleyData P
local notation "hNE" => annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
local notation "K" => HalfPlaneFuchsianGroup.cayleyCoordinate P ⁻¹' fuchsianNielsenCore D hNE
local notation "S" => annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr
local notation "g" => annularDiscPeripheralWord E r x hE hr hin hout

/-- Each original mirror meets the actual closed Nielsen lift in its entire closed foot-to-foot segment. -/
theorem annularSixFeet_originalNielsenLift_closed_mirror_clips
    (hB : ∀ i : Fin 3, IsBoundaryHyperbolic (D).asFuchsianDisc (g i))
    (K12 K23 K31 : HalfPlaneLine) (p12 p21 p23 p32 p31 p13 : ℍ)
    (h12 : (S 0).OrthogonalAt K12 p12) (h21 : (S 1).OrthogonalAt K12 p21)
    (h23 : (S 1).OrthogonalAt K23 p23) (h32 : (S 2).OrthogonalAt K23 p32)
    (h31 : (S 2).OrthogonalAt K31 p31) (h13 : (S 0).OrthogonalAt K31 p13) :
    closure K ∩ (S 0).carrier = closedHSegment p12 p13 ∧
      closure K ∩ (S 1).carrier = closedHSegment p21 p23 ∧
      closure K ∩ (S 2).carrier = closedHSegment p32 p31 := by
  obtain ⟨hoK, _hnK, hcK⟩ := annularPairOriginalNielsenLift_properties E r x hE hr hin hout
  obtain ⟨hc0, hc1, hc2⟩ := annularSixFeet_originalNielsenLift_mirror_clips
    E r x hE hr hin hout hB K12 K23 K31 p12 p21 p23 p32 p31 p13
      h12 h21 h23 h32 h31 h13
  have hx : 0 < x := (add_pos zero_lt_one hr).trans hin
  obtain ⟨hne0, hne1, hne2⟩ := annular_common_perpendicular_feet_ne
    E r x (zero_lt_one.trans hE) hr hE hx
      K12 K23 K31 p12 p21 p23 p32 p31 p13 h12 h21 h23 h32 h31 h13
  exact ⟨closure_inter_mirror_of_open_clip hoK hcK (S 0) p12 p13 hne0 hc0,
    closure_inter_mirror_of_open_clip hoK hcK (S 1) p21 p23 hne1 hc1,
    closure_inter_mirror_of_open_clip hoK hcK (S 2) p32 p31 hne2.symm hc2⟩

end LowDimensionalTopology.Geometry.Hyperbolic
