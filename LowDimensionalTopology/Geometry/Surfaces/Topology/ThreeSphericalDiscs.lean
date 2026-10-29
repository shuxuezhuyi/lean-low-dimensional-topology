module

public import LowDimensionalTopology.Unproved.Surfaces.ThreeSphericalDiscs
public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Complements of three marked spherical discs

The only outstanding input is the explicitly supplied finite relative
Jordan–Schoenflies proposition. Complements remove the full closed images.
-/

@[expose] public section

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Unproved.Surfaces

/-- Restrict the ambient homeomorphism supplied by the explicit classical
prerequisite to the complements of the three full closed disc images. -/
noncomputable def threeSphericalDiscComplementsHomeomorph
    (hHard : ThreeSphericalDiscs)
    (e f : Fin 3 → Complex.UnitClosedDisc → SphericalDiscSphere)
    (he : ∀ i, Topology.IsEmbedding (e i))
    (hf : ∀ i, Topology.IsEmbedding (f i))
    (heDisjoint : Pairwise (fun i j => Disjoint (Set.range (e i)) (Set.range (e j))))
    (hfDisjoint : Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j)))) :
    ↥((⋃ i : Fin 3, Set.range (e i))ᶜ) ≃ₜ
      ↥((⋃ i : Fin 3, Set.range (f i))ᶜ) := by
  let hex := hHard e f he hf heDisjoint hfDisjoint
  let h := Classical.choose hex
  have hh : ∀ i, h '' Set.range (e i) = Set.range (f i) :=
    Classical.choose_spec hex
  have hUnion : h '' (⋃ i : Fin 3, Set.range (e i)) =
      ⋃ i : Fin 3, Set.range (f i) := by
    simp only [Set.image_iUnion, hh]
  exact (h.image _).trans (Homeomorph.setCongr (by
    rw [h.image_compl, hUnion]))

end LowDimensionalTopology.Geometry.Surfaces
