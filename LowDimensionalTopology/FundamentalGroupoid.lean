/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# Paths and their inverses

Concatenating a path with its reverse gives a loop homotopic to the constant path.
-/

public section

namespace LowDimensionalTopology

/-- A path followed by its reverse is homotopic to the constant path. -/
theorem path_trans_symm_homotopic_refl {X : Type*} [TopologicalSpace X]
    {x y : X} (p : Path x y) :
    (p.trans p.symm).Homotopic (Path.refl x) := by
  exact Path.Homotopic.trans_symm p

end LowDimensionalTopology
