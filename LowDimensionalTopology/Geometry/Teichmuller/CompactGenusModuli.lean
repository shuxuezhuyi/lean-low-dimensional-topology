module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed

/-!
# The literal fixed-genus biholomorphic quotient

The moduli set consists of biholomorphic equivalence classes of closed
Riemann surfaces of the given genus.

The carriers here are ordinary `Type` targets, with their actual topologies
and original compact complex atlases. No smooth marking is required. This
file gives only the stated set quotient, with no classification, comparison
with a marked quotient, or analytic-space structure.
-/

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

/-- An actual closed genus-`g` Riemann surface on an ordinary `Type` carrier. -/
structure CompactGenusSurface (g : ℕ) where
  carrier : Type
  topology : TopologicalSpace carrier
  surface : @ClosedRiemannSurface carrier topology
  hasGenus : @ClosedRiemannSurface.HasGenus carrier topology surface g

attribute [instance] CompactGenusSurface.topology

namespace CompactGenusSurface

/-- Include any given original compact genus-`g` target, retaining exactly
its carrier, topology, and complex atlas. -/
def ofSurface {X : Type} [TopologicalSpace X] (S : ClosedRiemannSurface X)
    {g : ℕ} (hg : S.HasGenus g) : CompactGenusSurface g where
  carrier := X
  topology := inferInstance
  surface := S
  hasGenus := hg

/-- The source relation is genuine biholomorphism of the original surfaces.
The existing analytic inverse theorem supplies symmetry of this relation. -/
def setoid (g : ℕ) : Setoid (CompactGenusSurface g) where
  r S T := RiemannConformallyEquivalent S.surface.toRiemannSurface T.surface.toRiemannSurface
  iseqv := ⟨fun S => RiemannConformallyEquivalent.refl S.surface.toRiemannSurface,
    fun {_S _T} h => RiemannConformallyEquivalent.symm h,
    fun {_S _T _U} h h' => RiemannConformallyEquivalent.trans h h'⟩

end CompactGenusSurface

/-- `Mg`: biholomorphic equivalence classes of all actual compact genus-`g`
Riemann surfaces with `Type` carriers. The torus case is `g = 1`. -/
def CompactGenusModuliSpace (g : ℕ) : Type 1 :=
  Quotient (CompactGenusSurface.setoid g)

namespace CompactGenusModuliSpace

/-- The biholomorphic equivalence class of the given original surface. -/
def mk {g : ℕ} (S : CompactGenusSurface g) : CompactGenusModuliSpace g :=
  Quotient.mk (CompactGenusSurface.setoid g) S

/-- Equality of moduli classes is exactly the original source's relation. -/
theorem mk_eq_mk_iff {g : ℕ} (S T : CompactGenusSurface g) :
    mk S = mk T ↔
      RiemannConformallyEquivalent S.surface.toRiemannSurface T.surface.toRiemannSurface := by
  constructor
  · exact Quotient.exact
  · intro h
    exact @Quotient.sound _ (CompactGenusSurface.setoid g) S T h

end CompactGenusModuliSpace

end LowDimensionalTopology.Geometry.Teichmuller
