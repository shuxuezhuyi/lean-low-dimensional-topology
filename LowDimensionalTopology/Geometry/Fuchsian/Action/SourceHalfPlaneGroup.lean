module

public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordFundamentalDomains
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S22_RiemannSurfaces

/-!
# Native half-plane data for the actual projective source group

Proper discontinuity of the original special-linear action descends to its
entire actual Mobius image. The resulting native group keeps the given source
action and both ineffective signs without choosing matrix representatives.
-/

public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius

variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}

/-- The original compact-hit condition descends to the actual Mobius image,
without selecting any homomorphic special-linear lift of that image. -/
theorem sourceFuchsian_image_discontinuous (hΓ : LiZhongQC.IsFuchsian Γ) :
    IsMobiusDiscontinuousOn (Γ.map realSLMobius) openHalfPlaneSet := by
  intro K hK hKH
  let C : Set ℍ := Mobius.halfPlaneBoundaryPoint ⁻¹' K
  have hKr : K ⊆ range Mobius.halfPlaneBoundaryPoint := by
    rwa [halfPlaneBoundaryPoint_range]
  have hC : IsCompact C :=
    halfPlaneBoundaryPoint_isOpenEmbedding.isEmbedding.isInducing.isCompact_preimage' hK hKr
  let S : Set Γ := {A | (((A.val • ·) : ℍ → ℍ) '' C ∩ C).Nonempty}
  have hS : S.Finite :=
    (Set.Finite.preimage (f := fun A : Γ => A.val)
      Subtype.val_injective.injOn (hΓ C hC)).subset (by
        intro A hA
        exact ⟨A.property, hA⟩)
  let f : Γ → Γ.map realSLMobius := fun A =>
    ⟨realSLMobius A.val, Subgroup.mem_map.mpr ⟨A.val, A.property, rfl⟩⟩
  apply (hS.image f).subset
  rintro g ⟨y, ⟨x, hx, hxy⟩, hy⟩
  obtain ⟨A, hA, hAg⟩ := Subgroup.mem_map.mp g.property
  obtain ⟨z, hzx⟩ := hKr hx
  refine ⟨⟨A, hA⟩, ?_, Subtype.ext hAg⟩
  change (((A • ·) : ℍ → ℍ) '' C ∩ C).Nonempty
  refine ⟨A • z, ⟨z, ?_, rfl⟩, ?_⟩
  · change Mobius.halfPlaneBoundaryPoint z ∈ K
    rwa [hzx]
  · change Mobius.halfPlaneBoundaryPoint (A • z) ∈ K
    have he : Mobius.halfPlaneBoundaryPoint (A • z) = y := by
      calc
        _ = (realSLMobius A).val (Mobius.halfPlaneBoundaryPoint z) :=
          (realSLMobius_action A z).symm
        _ = g.val.val x := by rw [hAg, hzx]
        _ = y := hxy
    rwa [he]

/-- The original Fuchsian condition supplies the actual native half-plane
structure on its exact entire projective image. -/
theorem sourceHalfPlaneFuchsianGroup (hΓ : LiZhongQC.IsFuchsian Γ) :
    HalfPlaneFuchsianGroup (Γ.map realSLMobius) where
  preserves g := by
    obtain ⟨A, _hA, hAg⟩ := Subgroup.mem_map.mp g.property
    rw [← hAg]
    exact realSLMobius_image_openHalfPlane A
  discrete := isMobiusDiscontinuousOn_open_discrete (Γ.map realSLMobius)
    openHalfPlaneSet openHalfPlaneSet_isComplexOpenDisc.isOpen
    openHalfPlaneSet_isComplexOpenDisc.isConnected.nonempty
    (sourceFuchsian_image_discontinuous hΓ)

end LowDimensionalTopology.Geometry.Fuchsian
