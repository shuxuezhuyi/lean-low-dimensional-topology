module

public import Mathlib.Analysis.Complex.UnitDisc.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Homeomorph.Defs

/-!
# Three marked closed discs on the topological two-sphere

This file names the outstanding finite relative Jordan–Schoenflies input.
It supplies no proof. Only whole disc images are prescribed.
-/

@[expose] public section

namespace LowDimensionalTopology.Unproved.Surfaces

/-- The fixed topological two-sphere used by the genus-zero surface model. -/
abbrev SphericalDiscSphere : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

/-- Any two ordered triples of genuinely embedded closed two-discs with
pairwise disjoint closed images are related by an ambient sphere homeomorphism
matching corresponding whole images. This proposition is not proved here. -/
def ThreeSphericalDiscs : Prop :=
  ∀ e f : Fin 3 → Complex.UnitClosedDisc → SphericalDiscSphere,
    (∀ i, Topology.IsEmbedding (e i)) →
    (∀ i, Topology.IsEmbedding (f i)) →
    Pairwise (fun i j => Disjoint (Set.range (e i)) (Set.range (e j))) →
    Pairwise (fun i j => Disjoint (Set.range (f i)) (Set.range (f j))) →
    ∃ h : SphericalDiscSphere ≃ₜ SphericalDiscSphere,
      ∀ i, h '' Set.range (e i) = Set.range (f i)

end LowDimensionalTopology.Unproved.Surfaces
