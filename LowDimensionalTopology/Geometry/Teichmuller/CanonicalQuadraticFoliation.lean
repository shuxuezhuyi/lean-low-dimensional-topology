module

public import LowDimensionalTopology.Geometry.Surfaces.SingularMeasuredFoliation
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.HolomorphicQuadraticDifferential
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S26_TeichmullerUniqueness

/-!
# Compatibility with the canonical measured foliation of a given differential

Natural leaf charts use the flat primitive of the same original differential.
Its imaginary coordinate specifies the transverse measure on each chart
subarc. Existence of the compatible global measure is a separate proposition.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

variable {X : Type} [TopologicalSpace X]

/-- An actual regular flat coordinate whose squared derivative is the given differential. -/
def IsQuadraticNaturalLeafChart (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (e : OpenPartialHomeomorph X ℂ) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  e.source ⊆ {p | LiZhongQC.IsRegularPoint (q : X → ℂ → ℂ) p} ∧
    ∀ p ∈ e.source, LiZhongQC.IsNaturalParameterAt (q : X → ℂ → ℂ) p
      (fun z => e ((chartAt ℂ p).symm z) - e p)

/-- The raw foliation has exactly the zeros and local horizontal plaques of the given differential. -/
def IsHorizontalFoliationAtlasOf (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (A : SingularFoliationAtlas R) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  A.singular = {p | ¬ LiZhongQC.IsRegularPoint (q : X → ℂ → ℂ) p} ∧
    ∀ p, LiZhongQC.IsRegularPoint (q : X → ℂ → ℂ) p →
      ∃ e ∈ A.charts, ∃ n : OpenPartialHomeomorph X ℂ,
        IsQuadraticNaturalLeafChart R q n ∧ LocallySamePlaques e n p

/-- Every actual subarc in a genuine flat chart has the prescribed transverse interval measure. -/
def HasCanonicalQuadraticTransverseMeasure (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (A : SingularFoliationAtlas R) (μ : TransverseInvariantMeasure A) : Prop :=
  ∀ e : OpenPartialHomeomorph X ℂ, IsQuadraticNaturalLeafChart R q e →
    ∀ (α : A.TransverseArc) (a b : unitInterval), a ≤ b →
      (∀ t ∈ Icc a b, α.curve t ∈ e.source) →
      (StrictMonoOn (fun t => (e (α.curve t)).im) (Icc a b) ∨
        StrictAntiOn (fun t => (e (α.curve t)).im) (Icc a b)) →
      μ.measure α (Icc a b) = ENNReal.ofReal |(e (α.curve b)).im - (e (α.curve a)).im|

end LowDimensionalTopology.Geometry.Teichmuller
