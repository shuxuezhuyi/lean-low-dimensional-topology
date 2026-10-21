module
public import LowDimensionalTopology.Geometry.Hyperbolic.Triangle.IdealTriangleIsometries
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.NativeSegmentEndpoints
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- An actual closed-disc homeomorphism carrying one genuine closed h-line onto another
carries its intrinsic closed arc hulls onto the corresponding actual arc hulls. -/
theorem closedDiscHomeomorph_image_closedArcHull (e : 𝕔𝔻≃ₜ𝕔𝔻) (L M : DiscLine)
    (hLine : e '' L.closedCarrier=M.closedCarrier) (p q : 𝕔𝔻) :
    e '' L.closedArcHull p q=M.closedArcHull (e p) (e q) := by
  apply subset_antisymm
  · rintro y ⟨x,hx,rfl⟩ T hT hTM hp hq
    have hPre : IsPreconnected (e ⁻¹' T) := by
      have he : e ⁻¹' T=e.symm '' T := by
        ext z
        constructor
        · intro hz
          exact ⟨e z,hz,e.symm_apply_apply z⟩
        · rintro ⟨w,hw,rfl⟩
          simpa only [mem_preimage,e.apply_symm_apply] using hw
      rw [he]
      exact hT.image e.symm e.symm.continuous.continuousOn
    have hSub : e ⁻¹' T⊆L.closedCarrier := by
      intro z hz
      have hzM:=hTM hz
      rw [←hLine] at hzM
      exact e.injective.mem_set_image.mp hzM
    exact hx (e ⁻¹' T) hPre hSub hp hq
  · intro y hy
    refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
    intro T hT hTL hp hq
    have hImage : IsPreconnected (e '' T):=hT.image e e.continuous.continuousOn
    have hSub : e '' T⊆M.closedCarrier := by
      rw [←hLine]
      exact image_mono hTL
    have hyT:=hy (e '' T) hImage hSub (mem_image_of_mem e hp) (mem_image_of_mem e hq)
    obtain ⟨z,hz,hzy⟩:=hyT
    rwa [←hzy,e.symm_apply_apply]

/-- Every genuine native disc isometry preserves the actual compactified h-segment,
including every finite/ideal endpoint combination and the degenerate case. -/
theorem ClosedDiscIsometry.image_closedModelDiscHSegment (e : ClosedDiscIsometry) (p q : 𝕔𝔻) :
    e.closedMap '' closedModelDiscHSegment p q=
      closedModelDiscHSegment (e.closedMap p) (e.closedMap q) := by
  by_cases hpq : p=q
  · subst q
    rw [closedModelDiscHSegment_self,image_singleton,closedModelDiscHSegment_self]
  · obtain ⟨L,⟨hp,hq⟩,_⟩:=existsUnique_discLine_closedCarrier p q hpq
    obtain ⟨M,hM⟩:=e.image_closedLine L
    have hep : e.closedMap p∈M.closedCarrier := by rw [←hM];exact mem_image_of_mem _ hp
    have heq : e.closedMap q∈M.closedCarrier := by rw [←hM];exact mem_image_of_mem _ hq
    rw [closedModelDiscHSegment_eq_arcHull L p q hpq hp hq,
      closedModelDiscHSegment_eq_arcHull M _ _ (e.closedMap.injective.ne hpq) hep heq]
    exact closedDiscHomeomorph_image_closedArcHull e.closedMap L M hM p q

/-- Literal compactified side-image equality forces equality of the actual endpoint pairs,
with no finite-endpoint or nondegeneracy restriction. -/
theorem ClosedDiscIsometry.closed_segment_image_endpoints (e : ClosedDiscIsometry)
    (a b c d : 𝕔𝔻)
    (h : e.closedMap '' closedModelDiscHSegment a b=closedModelDiscHSegment c d) :
    ({e.closedMap a,e.closedMap b}:Set 𝕔𝔻)={c,d} := by
  have hs : closedModelDiscHSegment (e.closedMap a) (e.closedMap b)=closedModelDiscHSegment c d:=
    (e.image_closedModelDiscHSegment a b).symm.trans h
  have hk:=congrArg (fun S : Set 𝕔𝔻=>closedKleinCoordinate '' S) hs
  rw [closedKlein_image_closedModelDiscHSegment,closedKlein_image_closedModelDiscHSegment] at hk
  have he:=complex_segment_endpoints_eq _ _ _ _ hk
  apply closedKleinCoordinate_injective.image_injective
  simpa only [image_insert_eq,image_singleton] using he

end LowDimensionalTopology.Geometry.Hyperbolic
