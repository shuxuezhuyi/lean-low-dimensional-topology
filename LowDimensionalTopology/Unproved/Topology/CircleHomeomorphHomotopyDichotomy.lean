module

public import LowDimensionalTopology.Geometry.Surfaces.EssentialSimpleFreeClasses

/-!
# The two free homotopy types of an actual circle homeomorphism

This independent classical input concerns the actual unit circle and the
existing parameter reversal. It supplies the parameterization invariance
needed when geometric embedded-circle images are used as unoriented curves.
No circle degree, covering classification or isotopy is asserted as proved.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Topology

open LowDimensionalTopology.Geometry.Surfaces

/-- Every actual circle homeomorphism is freely homotopic either to the identity
or to the explicit reversal of the circle parameter. -/
def CircleHomeomorphHomotopyDichotomy : Prop :=
  ∀ e : Circle ≃ₜ Circle,
    ContinuousMap.Homotopic (_root_.toContinuousMap e) (ContinuousMap.id Circle) ∨
      ContinuousMap.Homotopic (_root_.toContinuousMap e) circleReversal

end LowDimensionalTopology.Unproved.Topology
