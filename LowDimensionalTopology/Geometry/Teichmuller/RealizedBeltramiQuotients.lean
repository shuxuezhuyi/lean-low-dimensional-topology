module

public import LowDimensionalTopology.Geometry.Teichmuller.RealizedBeltramiOrbits

/-!
# Teichmüller and moduli spaces as actual coefficient orbit quotients

These are equivalences of sets for the genuine smooth diffeomorphism actions
on actually realized continuous Beltrami coefficients. The homotopy identity
subgroup quotient is the native marked-surface Teichmüller space, and the full
orientation-preserving smooth automorphism quotient is the native unmarked
moduli space. No comparison of topologies is asserted here.
-/

@[expose] public section

noncomputable section

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v

/-- The actual coefficient orbit quotient by smooth reference automorphisms
freely homotopic to the identity. -/
def HomotopyIdentityBeltramiOrbitSpace {X : Type u} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) :=
  Quotient (MulAction.orbitRel (OrientedSurfaceAut.homotopyIdentitySubgroup R)
    (RealizedBeltramiCoefficients.{u, v} R))

namespace HomotopyIdentityBeltramiOrbitSpace

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The Diff₀ orbit of an actual coefficient. -/
def mk (μ : RealizedBeltramiCoefficients.{u, v} R) :
    HomotopyIdentityBeltramiOrbitSpace.{u, v} R :=
  Quotient.mk (MulAction.orbitRel (OrientedSurfaceAut.homotopyIdentitySubgroup R)
    (RealizedBeltramiCoefficients.{u, v} R)) μ

/-- The actual coefficient projection descends through the genuine Diff₀ action. -/
def toTeichmuller : HomotopyIdentityBeltramiOrbitSpace.{u, v} R → TeichmullerSpace.{u, v} R :=
  Quotient.lift RealizedBeltramiCoefficients.beta (by
    intro μ ν hμν
    change μ ∈ MulAction.orbit (OrientedSurfaceAut.homotopyIdentitySubgroup R) ν at hμν
    obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hμν
    calc
      RealizedBeltramiCoefficients.beta μ = RealizedBeltramiCoefficients.beta (a • ν) :=
        congrArg RealizedBeltramiCoefficients.beta ha.symm
      _ = RealizedBeltramiCoefficients.beta ν :=
        RealizedBeltramiCoefficients.beta_homotopyIdentity_smul a ν)

@[simp]
theorem toTeichmuller_mk (μ : RealizedBeltramiCoefficients.{u, v} R) :
    toTeichmuller (mk μ) = RealizedBeltramiCoefficients.beta μ := rfl

/-- Distinct Diff₀ orbits cannot define the same native marked-surface class. -/
theorem toTeichmuller_injective : Function.Injective (toTeichmuller.{u, v} (R := R)) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro μ ν hμν
  apply @Quotient.sound _
    (MulAction.orbitRel (OrientedSurfaceAut.homotopyIdentitySubgroup R)
      (RealizedBeltramiCoefficients.{u, v} R)) μ ν
  change μ ∈ MulAction.orbit (OrientedSurfaceAut.homotopyIdentitySubgroup R) ν
  exact MulAction.mem_orbit_iff.mpr
    ((RealizedBeltramiCoefficients.beta_eq_iff_exists_homotopyIdentity ν μ).1 hμν.symm)

theorem toTeichmuller_surjective : Function.Surjective (toTeichmuller.{u, v} (R := R)) := by
  intro p
  obtain ⟨μ, rfl⟩ := RealizedBeltramiCoefficients.beta_surjective p
  exact ⟨mk μ, rfl⟩

/-- Native Teichmüller classes are exactly the actual coefficient Diff₀ orbits. -/
def equivTeichmuller (R : ClosedRiemannSurface X) :
    HomotopyIdentityBeltramiOrbitSpace.{u, v} R ≃ TeichmullerSpace.{u, v} R :=
  Equiv.ofBijective toTeichmuller ⟨toTeichmuller_injective, toTeichmuller_surjective⟩

@[simp]
theorem equivTeichmuller_apply_mk (R : ClosedRiemannSurface X)
    (μ : RealizedBeltramiCoefficients.{u, v} R) :
    equivTeichmuller R (mk μ) = RealizedBeltramiCoefficients.beta μ := rfl

end HomotopyIdentityBeltramiOrbitSpace

/-- The actual coefficient orbit quotient by every smooth orientation-preserving
reference automorphism. -/
def OrientedBeltramiOrbitSpace {X : Type u} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) :=
  Quotient (MulAction.orbitRel (OrientedSurfaceAut R) (RealizedBeltramiCoefficients.{u, v} R))

namespace OrientedBeltramiOrbitSpace

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The Diff⁺ orbit of an actual coefficient. -/
def mk (μ : RealizedBeltramiCoefficients.{u, v} R) : OrientedBeltramiOrbitSpace.{u, v} R :=
  Quotient.mk (MulAction.orbitRel (OrientedSurfaceAut R)
    (RealizedBeltramiCoefficients.{u, v} R)) μ

/-- The actual unmarked target projection descends through the genuine Diff⁺ action. -/
def toModuli : OrientedBeltramiOrbitSpace.{u, v} R → ModuliSpace.{u, v} R :=
  Quotient.lift RealizedBeltramiCoefficients.forgetMarking (by
    intro μ ν hμν
    change μ ∈ MulAction.orbit (OrientedSurfaceAut R) ν at hμν
    obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.mp hμν
    calc
      RealizedBeltramiCoefficients.forgetMarking μ =
          RealizedBeltramiCoefficients.forgetMarking (a • ν) :=
        congrArg RealizedBeltramiCoefficients.forgetMarking ha.symm
      _ = RealizedBeltramiCoefficients.forgetMarking ν :=
        RealizedBeltramiCoefficients.forgetMarking_smul a ν)

@[simp]
theorem toModuli_mk (μ : RealizedBeltramiCoefficients.{u, v} R) :
    toModuli (mk μ) = RealizedBeltramiCoefficients.forgetMarking μ := rfl

/-- Distinct Diff⁺ orbits cannot define the same biholomorphic target class. -/
theorem toModuli_injective : Function.Injective (toModuli.{u, v} (R := R)) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro μ ν hμν
  apply @Quotient.sound _
    (MulAction.orbitRel (OrientedSurfaceAut R) (RealizedBeltramiCoefficients.{u, v} R)) μ ν
  change μ ∈ MulAction.orbit (OrientedSurfaceAut R) ν
  exact MulAction.mem_orbit_iff.mpr
    ((RealizedBeltramiCoefficients.forgetMarking_eq_iff_exists_smul ν μ).1 hμν.symm)

theorem toModuli_surjective : Function.Surjective (toModuli.{u, v} (R := R)) := by
  intro m
  obtain ⟨μ, rfl⟩ := RealizedBeltramiCoefficients.forgetMarking_surjective m
  exact ⟨mk μ, rfl⟩

/-- Native unmarked moduli classes are exactly the actual coefficient Diff⁺ orbits. -/
def equivModuli (R : ClosedRiemannSurface X) :
    OrientedBeltramiOrbitSpace.{u, v} R ≃ ModuliSpace.{u, v} R :=
  Equiv.ofBijective toModuli ⟨toModuli_injective, toModuli_surjective⟩

@[simp]
theorem equivModuli_apply_mk (R : ClosedRiemannSurface X)
    (μ : RealizedBeltramiCoefficients.{u, v} R) :
    equivModuli R (mk μ) = RealizedBeltramiCoefficients.forgetMarking μ := rfl

end OrientedBeltramiOrbitSpace

end LowDimensionalTopology.Geometry.Teichmuller
