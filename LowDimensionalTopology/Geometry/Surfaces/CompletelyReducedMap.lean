module

public import LowDimensionalTopology.Geometry.Surfaces.AdmissibleReduction
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Complete reduction relative to the actual cut circles

Complementary components retain their original subspace topology. Peripheral
classes are detected by homotopies inside the same component into arbitrarily
small neighborhoods of an actual removed circle. The return map is the literal
restriction of the least positive iterate of the original homeomorphism.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Surfaces

universe u
variable {X : Type u} [TopologicalSpace X]

/-- All genuine connected components of the original multicurve complement. -/
def AdmissibleMulticurve.complementComponents
    (C : AdmissibleMulticurve X) : Set (Set X) :=
  {U | ∃ x ∈ C.carrierᶜ, connectedComponentIn C.carrierᶜ x = U}

/-- A class is peripheral when it can be pushed, within the same component,
into every ambient neighborhood of one of its removed cut circles. -/
def IsPeripheralInCutComponent (C : AdmissibleMulticurve X) (U : Set X)
    (c : C(Circle, U)) : Prop :=
  ∃ d ∈ C.curves, ∀ V : Set X, IsOpen V → Set.range d.val ⊆ V →
    ∃ b : C(Circle, U), c.Homotopic b ∧ ∀ z : Circle, (b z : X) ∈ V

/-- Relative reduction uses invariant essential nonperipheral multicurves,
with both the competing map and its free homotopy taking values in the component. -/
def IsReducibleInCutComponent (C : AdmissibleMulticurve X) (U : Set X)
    (e : U ≃ₜ U) : Prop :=
  ∃ g : U ≃ₜ U,
    ContinuousMap.Homotopic (_root_.toContinuousMap e) (_root_.toContinuousMap g) ∧
      ∃ D : AdmissibleMulticurve U,
        (∀ c ∈ D.curves, ¬ IsPeripheralInCutComponent C U c.val) ∧ IsReducedBy g D

/-- A component map is irreducible relative to its actual removed cut ends. -/
def IsIrreducibleInCutComponent (C : AdmissibleMulticurve X) (U : Set X)
    (e : U ≃ₜ U) : Prop :=
  ¬ IsReducibleInCutComponent C U e

/-- Restrict the supplied homeomorphism to its actual invariant subspace. -/
def invariantComponentMap (e : X ≃ₜ X) (U : Set X) (hU : e '' U = U) : U ≃ₜ U :=
  e.sets (by
    calc
      U = e ⁻¹' (e '' U) := (Set.preimage_image_eq U e.injective).symm
      _ = e ⁻¹' U := congrArg (fun V : Set X => e ⁻¹' V) hU)

/-- The least positive power that preserves the same original component. -/
def IsLeastPositiveComponentReturn (f : X ≃ₜ X) (U : Set X) (N : ℕ) : Prop :=
  0 < N ∧ (f ^ N) '' U = U ∧
    ∀ n : ℕ, 0 < n → (f ^ n) '' U = U → N ≤ n

/-- The literal reduced map is completely reduced when every actual component
has an irreducible first return relative to the removed cut ends. -/
def IsCompletelyReducedBy (f : X ≃ₜ X) (C : AdmissibleMulticurve X) : Prop :=
  IsReducedBy f C ∧ ∀ U ∈ C.complementComponents,
    ∃ N : ℕ, ∃ hN : IsLeastPositiveComponentReturn f U N,
      IsIrreducibleInCutComponent C U (invariantComponentMap (f ^ N) U hN.2.1)

/-- Complete reduction by some actual admissible multicurve. -/
def IsCompletelyReduced (f : X ≃ₜ X) : Prop :=
  ∃ C : AdmissibleMulticurve X, IsCompletelyReducedBy f C

end LowDimensionalTopology.Geometry.Surfaces
