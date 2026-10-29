/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.OriginalCanonicalCut

/-!
# Original geometric canonical families in every genus

In genus zero the original sphere condition accompanies the explicit empty
ordered family. In positive genus the family is realized by an actual
original-orientation-compatible polygon cut and its ordered based side paths.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X]

/-- The actual empty ordered family at an original genus-zero basepoint. -/
def emptyOriginalGeneratorFamily (p : X) :
    Fin 0 × Fin 2 → FundamentalGroup X p :=
  fun i => Fin.elim0 i.1

/-- Original geometric canonicality: the explicit genus-zero empty family,
or a positive-genus actual oriented polygon-cut family at the same basepoint. -/
def IsOriginalCanonicalFamily (R : ClosedRiemannSurface X) (g : ℕ) (p : X) :
    (Fin g × Fin 2 → FundamentalGroup X p) → Prop :=
  match g with
  | 0 => fun classes => R.HasGenus 0 ∧ classes = emptyOriginalGeneratorFamily p
  | n + 1 => fun classes =>
      HasOriginalCanonicalCut R (n + 1) (Nat.zero_lt_succ n) p classes

end LowDimensionalTopology.Geometry.Surfaces
