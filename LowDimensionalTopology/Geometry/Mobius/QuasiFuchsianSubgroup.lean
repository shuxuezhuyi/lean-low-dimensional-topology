/-
Uses Wu Xiaobin's public circle-orientation predicate, Apache-2.0, pinned
commit 1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Mobius.Topology
public import LowDimensionalTopology.External.LiZhongQC.DouadyEarle.Extension

@[expose] public section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Mobius

/-- A discrete projective Möbius subgroup preserving a directed simple closed
sphere curve. -/
def IsQuasiFuchsianSubgroup (H : Subgroup complexMobiusGroup) : Prop :=
  IsDiscreteMobiusSubgroup H ∧
    ∃ γ : Circle → ExtendedComplex, Continuous γ ∧ Function.Injective γ ∧
      ∀ f ∈ H, ∃ h : Circle ≃ₜ Circle, _root_.HasIncreasingLift h ∧
        ∀ ζ : Circle, (f : Equiv.Perm ExtendedComplex) (γ ζ) = γ (h ζ)

end LowDimensionalTopology.Geometry.Mobius
