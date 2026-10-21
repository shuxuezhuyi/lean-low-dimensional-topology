/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Klein.Closed
public import Mathlib.Topology.Algebra.Affine
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped Complex.UnitDisc
set_option maxHeartbeats 600000
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The exact affine Klein parameter of a genuine finite-or-ideal hyperbolic segment. -/
def closedModelSegmentParam (a b:𝕔𝔻) (t:unitInterval) : 𝕔𝔻:=
  closedKleinToPoincare (Complex.UnitClosedDisc.mk
    (AffineMap.lineMap (closedKleinCoordinate a) (closedKleinCoordinate b) (t:ℝ)) (by
      have ht:AffineMap.lineMap (closedKleinCoordinate a) (closedKleinCoordinate b) (t:ℝ)∈
          segment ℝ (closedKleinCoordinate a) (closedKleinCoordinate b):=by
        rw [segment_eq_image_lineMap]
        exact ⟨t,t.property,rfl⟩
      exact mem_closedBall_zero_iff.mp ((convex_closedBall (0:ℂ) 1).segment_subset
        (mem_closedBall_zero_iff.mpr (closedPoincareToKlein a).norm_le_one)
        (mem_closedBall_zero_iff.mpr (closedPoincareToKlein b).norm_le_one) ht)))

theorem closedKleinCoordinate_segmentParam (a b:𝕔𝔻) (t:unitInterval) :
    closedKleinCoordinate (closedModelSegmentParam a b t)=
      AffineMap.lineMap (closedKleinCoordinate a) (closedKleinCoordinate b) (t:ℝ) := by
  change (closedPoincareToKlein (closedKleinToPoincare _):ℂ)=_
  rw [closedPoincareToKlein_closedKleinToPoincare]
  rfl

@[simp] theorem closedModelSegmentParam_zero (a b:𝕔𝔻) : closedModelSegmentParam a b 0=a := by
  apply closedKleinCoordinate_injective
  rw [closedKleinCoordinate_segmentParam]
  exact AffineMap.lineMap_apply_zero _ _

@[simp] theorem closedModelSegmentParam_one (a b:𝕔𝔻) : closedModelSegmentParam a b 1=b := by
  apply closedKleinCoordinate_injective
  rw [closedKleinCoordinate_segmentParam]
  exact AffineMap.lineMap_apply_one _ _

theorem continuous_closedModelSegmentParam (a b:𝕔𝔻) : Continuous (closedModelSegmentParam a b) := by
  apply isClosedEmbedding_closedKleinCoordinate.isEmbedding.continuous_iff.mpr
  change Continuous (fun t:unitInterval=>closedKleinCoordinate (closedModelSegmentParam a b t))
  simp only [closedKleinCoordinate_segmentParam]
  exact AffineMap.lineMap_continuous.comp continuous_subtype_val

theorem range_closedModelSegmentParam (a b:𝕔𝔻) :
    range (closedModelSegmentParam a b)=closedModelDiscHSegment a b := by
  apply subset_antisymm
  · rintro x ⟨t,rfl⟩
    apply closedKleinCoordinate_injective.mem_set_image.mp
    rw [closedKlein_image_closedModelDiscHSegment,closedKleinCoordinate_segmentParam,segment_eq_image_lineMap]
    exact ⟨t,t.property,rfl⟩
  · intro x hx
    have hKx:closedKleinCoordinate x∈segment ℝ (closedKleinCoordinate a) (closedKleinCoordinate b):=by
      rw [←closedKlein_image_closedModelDiscHSegment]
      exact mem_image_of_mem _ hx
    rw [segment_eq_image_lineMap] at hKx
    obtain ⟨t,ht,hx⟩:=hKx
    refine ⟨⟨t,ht⟩,?_⟩
    apply closedKleinCoordinate_injective
    rw [closedKleinCoordinate_segmentParam]
    exact hx

theorem closedModelSegmentParam_injective (a b:𝕔𝔻) (hab:a≠b) :
    Function.Injective (closedModelSegmentParam a b) := by
  intro t s he
  have hK:=congrArg closedKleinCoordinate he
  rw [closedKleinCoordinate_segmentParam,closedKleinCoordinate_segmentParam] at hK
  apply Subtype.ext
  exact (AffineMap.lineMap_injective ℝ (closedKleinCoordinate_injective.ne hab)) hK

/-- The actual closed segment has the genuine unit-interval topology, including both finite and ideal endpoints. -/
def closedModelSegmentHomeomorph (a b:𝕔𝔻) (hab:a≠b) :
    unitInterval≃ₜ↥(closedModelDiscHSegment a b) := by
  let :T2Space 𝕔𝔻:=Complex.UnitClosedDisc.isEmbedding_coe.t2Space
  let f:unitInterval→↥(closedModelDiscHSegment a b):=fun t=>
    ⟨closedModelSegmentParam a b t,(range_closedModelSegmentParam a b) ▸ mem_range_self t⟩
  have hf:Function.Bijective f:=by
    constructor
    · intro t s he
      exact closedModelSegmentParam_injective a b hab (congrArg Subtype.val he)
    · rintro ⟨x,hx⟩
      obtain ⟨t,ht⟩:=(range_closedModelSegmentParam a b).symm ▸ hx
      exact ⟨t,Subtype.ext ht⟩
  let e:=Equiv.ofBijective f hf
  have hc:Continuous f:=(continuous_closedModelSegmentParam a b).subtype_mk _
  exact e.toHomeomorphOfContinuousClosed hc hc.isClosedMap
end LowDimensionalTopology.Geometry.Hyperbolic
