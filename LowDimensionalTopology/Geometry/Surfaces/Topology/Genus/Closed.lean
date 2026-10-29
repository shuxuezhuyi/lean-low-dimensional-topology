module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.Closed
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CanonicalHandleEuler

/-!
# Genus of closed complex and hyperbolic surfaces

Genus is the existing topological handle-model invariant. A genus witness also
supplies compactness, and every closed Riemann surface of genus at least two has
an actual hyperbolic quotient structure by the established uniformization and
covering-space theorems.
-/

@[expose] public section

noncomputable section

namespace LowDimensionalTopology.Geometry.Surfaces

universe u

namespace ClosedRiemannSurface

variable {X : Type u} [TopologicalSpace X]

/-- The genus of a closed Riemann surface is its genuine topological handle genus. -/
def HasGenus (_R : ClosedRiemannSurface X) (g : ℕ) : Prop :=
  HasTopologicalGenus X g

theorem hasGenus_iff (R : ClosedRiemannSurface X) (g : ℕ) :
    R.HasGenus g ↔ HasTopologicalGenus X g := Iff.rfl

/-- A fixed surface cannot have two different topological genera. -/
theorem HasGenus.unique {R : ClosedRiemannSurface X} {g h : ℕ}
    (hg : R.HasGenus g) (hh : R.HasGenus h) : g = h :=
  hasTopologicalGenus_unique hg hh

/-- A topological genus witness supplies the compactness of a Riemann surface. -/
def ofTopologicalGenus (R : RiemannSurface X) {g : ℕ}
    (hg : HasTopologicalGenus X g) : ClosedRiemannSurface X where
  toRiemannSurface := R
  compactSpace := HandleSeparation.hasTopologicalGenus_compactSpace hg

@[simp]
theorem ofTopologicalGenus_toRiemannSurface (R : RiemannSurface X) {g : ℕ}
    (hg : HasTopologicalGenus X g) :
    (ofTopologicalGenus R hg).toRiemannSurface = R := rfl

theorem ofTopologicalGenus_hasGenus (R : RiemannSurface X) {g : ℕ}
    (hg : HasTopologicalGenus X g) : (ofTopologicalGenus R hg).HasGenus g := hg

/-- Higher genus gives hyperbolic type through the actual universal cover. -/
theorem isHyperbolicType_of_genus_ge_two (R : ClosedRiemannSurface X) {g : ℕ}
    (hg : 2 ≤ g) (hgenus : R.HasGenus g) : IsHyperbolicType R.toRiemannSurface := by
  let := R.compactSpace
  obtain ⟨C⟩ := riemannSurface_nonempty_universalCover R.toRiemannSurface
  exact C.isHyperbolicType_of_conformallyEquivalent_disc
    (C.disc_model_of_topologicalGenus_ge_two hg hgenus)

/-- Choose the proved hyperbolic structure on a closed Riemann surface of higher genus. -/
def hyperbolicOfGenusGeTwo (R : ClosedRiemannSurface X) {g : ℕ}
    (hg : 2 ≤ g) (hgenus : R.HasGenus g) : ClosedHyperbolicSurface X :=
  ClosedHyperbolicSurface.ofIsHyperbolicType R (R.isHyperbolicType_of_genus_ge_two hg hgenus)

@[simp]
theorem hyperbolicOfGenusGeTwo_toClosedRiemannSurface (R : ClosedRiemannSurface X) {g : ℕ}
    (hg : 2 ≤ g) (hgenus : R.HasGenus g) :
    (R.hyperbolicOfGenusGeTwo hg hgenus).toClosedRiemannSurface = R := rfl

end ClosedRiemannSurface

/-- An existing Riemann surface with a higher-genus topological model yields an
actual closed hyperbolic surface on that same underlying topological space. -/
theorem nonempty_closedHyperbolicSurface_of_topologicalGenus_ge_two
    {X : Type u} [TopologicalSpace X] (R : RiemannSurface X) {g : ℕ}
    (hg : 2 ≤ g) (hgenus : HasTopologicalGenus X g) :
    Nonempty (ClosedHyperbolicSurface X) :=
  ⟨(ClosedRiemannSurface.ofTopologicalGenus R hgenus).hyperbolicOfGenusGeTwo hg hgenus⟩

end LowDimensionalTopology.Geometry.Surfaces
