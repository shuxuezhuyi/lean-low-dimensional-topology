module
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.CuspfreeCoreCompactness

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Fuchsian

/-- The image of the actual open Nielsen core in the original orbit quotient. -/
def threeBoundaryOpenCore
    {H : Subgroup Mobius.complexMobiusGroup} (G : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) :
    Set (Surfaces.MobiusDomainQuotient G.domain) :=
  Surfaces.mobiusDomainProjection G.domain '' fuchsianNielsenCore G hNE

/-- The image of the actual closed Nielsen core in that same orbit quotient. -/
def threeBoundaryClosedCore
    {H : Subgroup Mobius.complexMobiusGroup} (G : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) :
    Set (Surfaces.MobiusDomainQuotient G.domain) :=
  Surfaces.mobiusDomainProjection G.domain '' closure (fuchsianNielsenCore G hNE)

/-- Openness is preserved by the actual open orbit projection. -/
theorem isOpen_threeBoundaryOpenCore
    {H : Subgroup Mobius.complexMobiusGroup} (G : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) :
    IsOpen (threeBoundaryOpenCore G hNE) :=
  (Surfaces.mobiusDomainProjection_isOpenQuotientMap G.domain).isOpenMap
    _ (fuchsianNielsenCore_isOpen G hNE)

/-- Invariance makes the actual Nielsen core saturated under the orbit projection. -/
theorem preimage_threeBoundaryOpenCore
    {H : Subgroup Mobius.complexMobiusGroup} (G : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) :
    Surfaces.mobiusDomainProjection G.domain ⁻¹' threeBoundaryOpenCore G hNE =
      fuchsianNielsenCore G hNE := by
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨g, hg⟩ := Quotient.exact hxy.symm
    simpa only [hg] using fuchsianNielsenCore_invariant G hNE g y hy
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- The two actual carriers retain their evident inclusion. -/
theorem threeBoundaryOpenCore_subset_closed
    {H : Subgroup Mobius.complexMobiusGroup} (G : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) :
    threeBoundaryOpenCore G hNE ⊆ threeBoundaryClosedCore G hNE :=
  Set.image_mono subset_closure

/-- The open continuous orbit projection commutes with closure of this saturated core. -/
theorem closure_threeBoundaryOpenCore
    {H : Subgroup Mobius.complexMobiusGroup} (G : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) :
    closure (threeBoundaryOpenCore G hNE) = threeBoundaryClosedCore G hNE := by
  let π := Surfaces.mobiusDomainProjection G.domain
  have hπ := Surfaces.mobiusDomainProjection_isOpenQuotientMap G.domain
  calc
    closure (threeBoundaryOpenCore G hNE) =
        π '' (π ⁻¹' closure (threeBoundaryOpenCore G hNE)) :=
      (hπ.surjective.image_preimage _).symm
    _ = π '' closure (fuchsianNielsenCore G hNE) := by
      rw [hπ.isOpenMap.preimage_closure_eq_closure_preimage hπ.continuous,
        preimage_threeBoundaryOpenCore G hNE]
    _ = threeBoundaryClosedCore G hNE := rfl

/-- The relative frontier in the original quotient is exactly the projected
original Nielsen frontier, as required by the existing boundary-cycle cover. -/
theorem frontier_threeBoundaryOpenCore
    {H : Subgroup Mobius.complexMobiusGroup} (G : UnitDiscFuchsianGroup H)
    (hNE : DiscreteGroups.IsNonElementary H) :
    frontier (threeBoundaryOpenCore G hNE) =
      Surfaces.mobiusDomainProjection G.domain '' frontier (fuchsianNielsenCore G hNE) := by
  let π := Surfaces.mobiusDomainProjection G.domain
  have hπ := Surfaces.mobiusDomainProjection_isOpenQuotientMap G.domain
  calc
    frontier (threeBoundaryOpenCore G hNE) =
        π '' (π ⁻¹' frontier (threeBoundaryOpenCore G hNE)) :=
      (hπ.surjective.image_preimage _).symm
    _ = π '' frontier (fuchsianNielsenCore G hNE) := by
      rw [hπ.isOpenMap.preimage_frontier_eq_frontier_preimage hπ.continuous,
        preimage_threeBoundaryOpenCore G hNE]

/-- The genuine cusp-free three-end signature makes its actual closed core compact. -/
theorem isCompact_threeBoundaryClosedCore
    {H : Subgroup Mobius.complexMobiusGroup} {G : UnitDiscFuchsianGroup H}
    {hNE : DiscreteGroups.IsNonElementary H} {hFG : H.FG}
    (h : HasNielsenFuchsianSignature G hNE hFG 0 [] 0 3) :
    IsCompact (threeBoundaryClosedCore G hNE) :=
  h.isCompact_projected_closedCore

/-- The open core is relatively compact in its original quotient surface. -/
theorem isCompact_closure_threeBoundaryOpenCore
    {H : Subgroup Mobius.complexMobiusGroup} {G : UnitDiscFuchsianGroup H}
    {hNE : DiscreteGroups.IsNonElementary H} {hFG : H.FG}
    (h : HasNielsenFuchsianSignature G hNE hFG 0 [] 0 3) :
    IsCompact (closure (threeBoundaryOpenCore G hNE)) := by
  rw [closure_threeBoundaryOpenCore]
  exact isCompact_threeBoundaryClosedCore h

end LowDimensionalTopology.Geometry.Fuchsian
