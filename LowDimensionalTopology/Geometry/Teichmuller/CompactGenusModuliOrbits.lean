module

public import LowDimensionalTopology.Geometry.Teichmuller.CompactGenusModuliTopology

/-!
# The full compact-genus moduli set as the actual modular orbit quotient

The map retains each actual native marked target and uses the existing
mapping class group action. Its fibers are already known. Only
surjectivity onto all compact targets uses positive smooth markability.
This is a set equivalence for the one fixed reference, with no analytic
space or reference-independence assertion.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller.MappingClassOrbitSpace

open Surfaces

variable {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}

/-- The original target projection descends to the actual mapping class orbit
quotient of native marked surfaces. -/
def toCompactGenusModuli (R : ClosedRiemannSurface X) (hgenus : R.HasGenus g) :
    MappingClassOrbitSpace.{0, 0} R → CompactGenusModuliSpace g :=
  Quotient.lift (TeichmullerSpace.toCompactGenusModuli R hgenus) (by
    intro p q hpq
    change p ∈ MulAction.orbit (MappingClassGroup R) q at hpq
    exact ((TeichmullerSpace.toCompactGenusModuli_eq_iff_exists_mappingClass
      hgenus q p).2 (MulAction.mem_orbit_iff.mp hpq)).symm)

@[simp]
theorem toCompactGenusModuli_mk (hgenus : R.HasGenus g)
    (p : TeichmullerSpace.{0, 0} R) :
    toCompactGenusModuli R hgenus (mk p) =
      TeichmullerSpace.toCompactGenusModuli R hgenus p := rfl

/-- The full target projection identifies exactly one native mapping class
orbit with each target class in its range. -/
theorem toCompactGenusModuli_injective (R : ClosedRiemannSurface X)
    (hgenus : R.HasGenus g) :
    Function.Injective (toCompactGenusModuli R hgenus) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro p q hpq
  change TeichmullerSpace.toCompactGenusModuli R hgenus p =
    TeichmullerSpace.toCompactGenusModuli R hgenus q at hpq
  apply @Quotient.sound _
    (MulAction.orbitRel (MappingClassGroup R) (TeichmullerSpace.{0, 0} R)) p q
  change p ∈ MulAction.orbit (MappingClassGroup R) q
  exact MulAction.mem_orbit_iff.mpr
    ((TeichmullerSpace.toCompactGenusModuli_eq_iff_exists_mappingClass
      hgenus q p).1 hpq.symm)

/-- The independent positive smooth marking premise supplies every actual
compact target in the full fixed-genus quotient. -/
theorem toCompactGenusModuli_surjective (R : ClosedRiemannSurface X)
    (hgenus : R.HasGenus g)
    (hmark : LowDimensionalTopology.Unproved.Teichmuller.PositiveSmoothMarkability R) :
    Function.Surjective (toCompactGenusModuli R hgenus) := by
  intro m
  obtain ⟨p, hp⟩ := TeichmullerSpace.toCompactGenusModuli_surjective R hgenus hmark m
  exact ⟨mk p, hp⟩

/-- All compact genus-g targets, up to genuine biholomorphism, are the actual
native mapping class orbits under the explicit old marking premise. -/
def equivCompactGenusModuli (R : ClosedRiemannSurface X) (hgenus : R.HasGenus g)
    (hmark : LowDimensionalTopology.Unproved.Teichmuller.PositiveSmoothMarkability R) :
    MappingClassOrbitSpace.{0, 0} R ≃ CompactGenusModuliSpace g :=
  Equiv.ofBijective (toCompactGenusModuli R hgenus)
    ⟨toCompactGenusModuli_injective R hgenus,
      toCompactGenusModuli_surjective R hgenus hmark⟩

@[simp]
theorem equivCompactGenusModuli_apply_mk (R : ClosedRiemannSurface X)
    (hgenus : R.HasGenus g)
    (hmark : LowDimensionalTopology.Unproved.Teichmuller.PositiveSmoothMarkability R)
    (p : TeichmullerSpace.{0, 0} R) :
    equivCompactGenusModuli R hgenus hmark (mk p) =
      TeichmullerSpace.toCompactGenusModuli R hgenus p := rfl

end LowDimensionalTopology.Geometry.Teichmuller.MappingClassOrbitSpace
