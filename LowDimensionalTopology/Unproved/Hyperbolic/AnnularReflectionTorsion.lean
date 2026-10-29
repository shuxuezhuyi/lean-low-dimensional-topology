module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairQuotientReflection
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite-order conjugacy in the original full annular mirror group

The concrete classical obligation involves only the actual native generators,
their generated subgroup, finite order and conjugacy. Importing it supplies
no proof of the obligation.
-/

@[expose] public section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Unproved.Hyperbolic

open LowDimensionalTopology.Geometry.Hyperbolic

/-- Every nonidentity finite-order element of the actual full annular mirror
group is conjugate inside that same group to one of its three original mirrors. -/
def AnnularReflectionTorsion (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
    (_hin : 1 + r < x) (_hout : x + r < E) : Prop :=
  let S := annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr
  let σ : Fin 3 → (ℍ ≃ᵢ ℍ) := fun i => halfPlaneLineReflectionIsometry (S i)
  let H : Subgroup (ℍ ≃ᵢ ℍ) := ⨆ i : Fin 3, Subgroup.zpowers (σ i)
  ∀ h ∈ H, h ≠ 1 → IsOfFinOrder h →
    ∃ k ∈ H, ∃ i : Fin 3, h = k * σ i * k⁻¹

end LowDimensionalTopology.Unproved.Hyperbolic
