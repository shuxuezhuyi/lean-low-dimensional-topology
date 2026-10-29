module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedLengthSpectrum
public import LowDimensionalTopology.Geometry.Teichmuller.MappingClassGroup
public import LowDimensionalTopology.Geometry.Teichmuller.NativeTeichmullerMetric
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge

/-!
# Sequential compactness modulo the original mapping class action

The thickness bound uses every original essential simple free class and its
actual marked hyperbolic length. Convergence uses the full-log QC metric on
the unchanged native marked quotient. This is a concrete unresolved
compactness statement; no proof is supplied by this definition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Filter
open scoped Topology

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)

/-- Uniform thickness of a sequence of actual native marked surfaces gives a
convergent subsequence after actual mapping class adjustments. -/
def NativeMumfordSequentialCompactness : Prop :=
  letI : MetricSpace (TeichmullerSpace.{0, 0} R) :=
    TeichmullerSpace.fromQCMetricSpace R hg hgenus (canonicalHandleGroupPresentation g)
  ∀ points : ℕ → TeichmullerSpace.{0, 0} R,
    (∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (c : EssentialSimpleFreeClass X),
      δ < (markedLengthSpectrum R (Nat.succ_le_of_lt hg) hgenus (points n) c : ℝ)) →
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ (χ : ℕ → MappingClassGroup R) (q : TeichmullerSpace.{0, 0} R),
        Tendsto (fun n => χ n • points (σ n)) atTop (𝓝 q)

end LowDimensionalTopology.Unproved.Teichmuller
