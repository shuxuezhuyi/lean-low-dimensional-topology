module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.GeodesicDecomposingSystem
public import Mathlib.Topology.Connected.Basic

/-!
# Complement components and the associated decomposing-system family

The generic component family needs no maximality or geodesic premise.
The book calls this full family the associated pants decomposition when a
decomposing system is given. Proving that its members are hyperbolic pants
remains a separate geometric theorem, not a field or assumption here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X]

/-- All actual connected components of the original complement; this definition
asserts no pants classification and requires no decomposing-system proof. -/
def geodesicComplementComponents (L : Set (Set X)) : Set (Set X) :=
  {P | ∃ x ∈ (⋃₀ L)ᶜ, connectedComponentIn (⋃₀ L)ᶜ x = P}

/-- Every complement point supplies its actual component to the family. -/
theorem component_mem_geodesicComplementComponents
    (L : Set (Set X)) {x : X} (hx : x ∈ (⋃₀ L)ᶜ) :
    connectedComponentIn (⋃₀ L)ᶜ x ∈ geodesicComplementComponents L := by
  exact ⟨x, hx, rfl⟩

/-- Every generic component is nonempty and connected. -/
theorem isConnected_of_mem_geodesicComplementComponents
    (L : Set (Set X)) {P : Set X} (hP : P ∈ geodesicComplementComponents L) :
    IsConnected P := by
  rcases hP with ⟨x, hx, rfl⟩
  exact isConnected_connectedComponentIn_iff.mpr hx

/-- Different components are disjoint for every original curve family L. -/
theorem geodesicComplementComponents_pairwise_disjoint
    (L : Set (Set X)) : (geodesicComplementComponents L).Pairwise Disjoint := by
  rintro A ⟨x, _hx, rfl⟩ B ⟨y, _hy, rfl⟩ hne
  apply Set.disjoint_left.mpr
  intro z hzx hzy
  exact hne ((connectedComponentIn_eq hzx).trans (connectedComponentIn_eq hzy).symm)

/-- The whole generic family covers exactly the original complement. -/
theorem sUnion_geodesicComplementComponents (L : Set (Set X)) :
    ⋃₀ geodesicComplementComponents L = (⋃₀ L)ᶜ := by
  ext x
  constructor
  · intro hx
    rcases Set.mem_sUnion.mp hx with ⟨P, hP, hxP⟩
    rcases hP with ⟨y, _hy, rfl⟩
    exact connectedComponentIn_subset _ _ hxP
  · intro hx
    exact Set.mem_sUnion.mpr ⟨connectedComponentIn (⋃₀ L)ᶜ x,
      component_mem_geodesicComplementComponents L hx, mem_connectedComponentIn hx⟩

variable {R : ClosedRiemannSurface X}
variable {M : HyperbolicSurfaceModel R.toRiemannSurface} {L : Set (Set X)}

/-- The book's associated full complement-component family. Geometric pants
classification requires further geometric conclusions about these components. -/
def IsGeodesicDecomposingSystem.pantsDecomposition
    (_hL : IsGeodesicDecomposingSystem M L) : Set (Set X) :=
  geodesicComplementComponents L

/-- Every complement point supplies its actual component to the family. -/
theorem IsGeodesicDecomposingSystem.component_mem_pantsDecomposition
    (hL : IsGeodesicDecomposingSystem M L) {x : X} (hx : x ∈ (⋃₀ L)ᶜ) :
    connectedComponentIn (⋃₀ L)ᶜ x ∈ hL.pantsDecomposition := by
  exact component_mem_geodesicComplementComponents L hx

/-- Every member is a nonempty connected subset of the same original surface. -/
theorem IsGeodesicDecomposingSystem.isConnected_of_mem_pantsDecomposition
    (hL : IsGeodesicDecomposingSystem M L) {P : Set X}
    (hP : P ∈ hL.pantsDecomposition) : IsConnected P := by
  exact isConnected_of_mem_geodesicComplementComponents L hP

/-- Different members of the component family are disjoint. -/
theorem IsGeodesicDecomposingSystem.pantsDecomposition_pairwise_disjoint
    (hL : IsGeodesicDecomposingSystem M L) :
    hL.pantsDecomposition.Pairwise Disjoint := by
  exact geodesicComplementComponents_pairwise_disjoint L

/-- The entire family covers exactly the original complement of the curves. -/
theorem IsGeodesicDecomposingSystem.sUnion_pantsDecomposition
    (hL : IsGeodesicDecomposingSystem M L) :
    ⋃₀ hL.pantsDecomposition = (⋃₀ L)ᶜ := by
  exact sUnion_geodesicComplementComponents L

end LowDimensionalTopology.Geometry.Surfaces
