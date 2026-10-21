/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.TriangleCoordinates
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.IsometryClassification
public import Mathlib.Analysis.Convex.Segment
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- A genuine Euclidean closed segment determines its unordered endpoints, including degeneracy. -/
theorem complex_segment_endpoints_eq (a b c d : ℂ)
    (h : segment ℝ a b=segment ℝ c d) : ({a,b}:Set ℂ)={c,d} := by
  have hc : c∈segment ℝ a b:=h.symm ▸ left_mem_segment ℝ c d
  have hd : d∈segment ℝ a b:=h.symm ▸ right_mem_segment ℝ c d
  by_cases hab : a=b
  · rw [hab,segment_same] at hc hd
    simp only [mem_singleton_iff] at hc hd
    simp [hab,hc,hd]
  · rw [segment_eq_image_lineMap] at hc hd
    obtain ⟨s,hs,hcs⟩:=hc
    obtain ⟨t,ht,hdt⟩:=hd
    let F : ℝ→ᵃ[ℝ] ℂ:=AffineMap.lineMap a b
    have hi : Function.Injective F:=AffineMap.lineMap_injective ℝ hab
    have him : F '' Icc (0:ℝ) 1=F '' segment ℝ s t:=by
      calc
        _ = segment ℝ a b := (segment_eq_image_lineMap ℝ a b).symm
        _ = segment ℝ c d := h
        _ = F '' segment ℝ s t := by rw [image_segment,hcs,hdt]
    have hp : Icc (0:ℝ) 1=segment ℝ s t:=hi.image_injective him
    have h0 : (0:ℝ)∈segment ℝ s t:=hp ▸ (show (0:ℝ)∈Icc (0:ℝ) 1 by norm_num)
    have h1 : (1:ℝ)∈segment ℝ s t:=hp ▸ (show (1:ℝ)∈Icc (0:ℝ) 1 by norm_num)
    rw [segment_eq_Icc'] at h0 h1
    by_cases hst : s≤t
    · have hs0 : s=0:=le_antisymm (by simpa only [min_eq_left hst] using h0.1) hs.1
      have ht1 : t=1:=le_antisymm ht.2 (by simpa only [max_eq_right hst] using h1.2)
      rw [←hcs,←hdt,hs0,ht1]
      simp
    · have hts : t≤s:=le_of_not_ge hst
      have ht0 : t=0:=le_antisymm (by simpa only [min_eq_right hts] using h0.1) ht.1
      have hs1 : s=1:=le_antisymm hs.2 (by simpa only [max_eq_left hts] using h1.2)
      rw [←hcs,←hdt,hs1,ht0]
      simp [pair_comm]

/-- Native closed-segment image compatibility includes the repeated-endpoint case. -/
theorem native_image_closedHSegment (f : ℍ≃ᵢℍ) (a b : ℍ) :
    f '' closedHSegment a b=closedHSegment (f a) (f b) := by
  by_cases hab : a=b
  · subst b
    rw [closedHSegment_self,closedHSegment_self,image_singleton]
  · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.image_closedHSegment f.isometry hab

/-- A real native isometry carrying one genuine closed hyperbolic segment to another
carries precisely its unordered endpoint pair, without a nondegeneracy premise. -/
theorem native_closedHSegment_image_endpoints (f : ℍ≃ᵢℍ) (a b c d : ℍ)
    (h : f '' closedHSegment a b=closedHSegment c d) : ({f a,f b}:Set ℍ)={c,d} := by
  have hs : closedHSegment (f a) (f b)=closedHSegment c d:=
    (native_image_closedHSegment f a b).symm.trans h
  have hk:=congrArg (fun S:Set ℍ=>halfPlaneKleinCoordinate '' S) hs
  rw [halfPlaneKlein_image_closedHSegment,halfPlaneKlein_image_closedHSegment] at hk
  have he:=complex_segment_endpoints_eq _ _ _ _ hk
  apply isOpenEmbedding_halfPlaneKleinCoordinate.injective.image_injective
  simpa only [image_insert_eq,image_singleton] using he

end LowDimensionalTopology.Geometry.Hyperbolic
