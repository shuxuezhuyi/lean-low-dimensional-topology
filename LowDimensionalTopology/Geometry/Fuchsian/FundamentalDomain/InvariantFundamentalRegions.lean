module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.LocallyFiniteFundamentalDomains
@[expose] public section
noncomputable section
open Set Topology
open scoped Pointwise OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- Actual distinct images of a region which meet the closed fundamental domain. -/
def fuchsianRegionImages {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P :
  UnitDiscFuchsianGroup H)
    (D K : Set P.domain.carrier) : Set (Set P.domain.carrier) :=
  {L | ∃ g : H, L = g • K ∧ (closure D ∩ L).Nonempty}

/-- Closed-domain coverage gives at least one image for every nonempty actual region. -/
theorem IsFuchsianFundamentalDomain.regionImages_nonempty
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D K : Set P.domain.carrier} (hD : IsFuchsianFundamentalDomain P D) (hK : K.Nonempty) :
    (fuchsianRegionImages P D K).Nonempty := by
  obtain ⟨w, hw⟩ := hK
  have hc : (⋃ g : H, fuchsianDomainTile P D g) = univ := hD.closure_cover
  have hcover : w ∈ ⋃ g : H, fuchsianDomainTile P D g := by rw [hc]; trivial
  obtain ⟨g, u, hu, hgu⟩ := mem_iUnion.mp hcover
  change g • u = w at hgu
  refine ⟨g⁻¹ • K, g⁻¹, rfl, u, hu, w, hw, ?_⟩
  change g⁻¹ • w = u
  rw [← hgu, inv_smul_smul]

/-- A compact actual region meets only finitely many inverse closed tiles. -/
theorem IsLocallyFiniteFuchsianDomain.compact_region_elements_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D K : Set P.domain.carrier} (hD : IsLocallyFiniteFuchsianDomain P D) (hK : IsCompact K) :
    {g : H | (closure D ∩ g • K).Nonempty}.Finite := by
  have hf := (hD.compact_hits_finite K hK).preimage (inv_injective : Function.Injective (Inv.inv : H → H)).injOn
  apply hf.subset
  rintro g ⟨u, hu, w, hw, hgw⟩
  change g • w = u at hgw
  refine ⟨w, ⟨u, hu, ?_⟩, hw⟩
  change g⁻¹ • u = w
  rw [← hgw, inv_smul_smul]

/-- Only finitely many images of a compact region meet a closed locally finite fundamental domain. -/
theorem IsLocallyFiniteFuchsianDomain.compact_region_images_finite
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D K : Set P.domain.carrier} (hD : IsLocallyFiniteFuchsianDomain P D) (hK : IsCompact K) :
    (fuchsianRegionImages P D K).Finite := by
  apply ((hD.compact_region_elements_finite hK).image (fun g : H => g • K)).subset
  rintro L ⟨g, rfl, hg⟩
  exact ⟨g, hg, rfl⟩

/-- proved for every nonempty compact region on the actual invariant disc. -/
theorem compact_nonempty_regionImages_nonempty_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D K : Set P.domain.carrier} (hD : IsLocallyFiniteFuchsianDomain P D)
    (hK : IsCompact K) (hnK : K.Nonempty) :
    (fuchsianRegionImages P D K).Nonempty ∧ (fuchsianRegionImages P D K).Finite :=
  ⟨hD.fundamental.regionImages_nonempty hnK, hD.compact_region_images_finite hK⟩

/-- A compact set whose region-preserving translates cover the region gives finitely many
actual region images meeting the closed fundamental domain. -/
theorem IsLocallyFiniteFuchsianDomain.region_images_finite_of_compact_cover
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {D K E : Set P.domain.carrier} (hD : IsLocallyFiniteFuchsianDomain P D) (hE : IsCompact E)
    (hcov : ∀ w ∈ K, ∃ s : H, s • K = K ∧ w ∈ s • E) :
    (fuchsianRegionImages P D K).Finite := by
  apply ((hD.compact_region_elements_finite hE).image (fun g : H => g • K)).subset
  rintro L ⟨g, rfl, z, hz, w, hw, hgw⟩
  change g • w = z at hgw
  obtain ⟨s, hs, e, he, hse⟩ := hcov w hw
  change s • e = w at hse
  refine ⟨g * s, ⟨z, hz, e, he, ?_⟩, ?_⟩
  · change (g * s) • e = z
    rw [mul_smul, hse, hgw]
  · change (g * s) • K = g • K
    rw [mul_smul, hs]

end LowDimensionalTopology.Geometry.Fuchsian
