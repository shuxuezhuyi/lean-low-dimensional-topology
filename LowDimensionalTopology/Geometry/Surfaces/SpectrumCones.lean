module

public import LowDimensionalTopology.Geometry.Surfaces.EssentialSimpleFreeClasses
public import Mathlib.Topology.Instances.NNReal.Lemmas
public import Mathlib.Topology.Constructions

/-!
# Positive and nonnegative spectra on the original curve classes

The two source products use the same essential unoriented simple free-class
index. Their coordinate types distinguish strictly positive from nonnegative
real values. Both carry the literal inherited product topology.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped NNReal

namespace LowDimensionalTopology.Geometry.Surfaces

universe u v

/-- The source product of strictly positive real coordinates. -/
abbrev PositiveSpectrum (X : Type u) [TopologicalSpace X] :=
  EssentialSimpleFreeClass X → Set.Ioi (0 : ℝ)

/-- The source closed nonnegative coordinate cone, including the zero spectrum. -/
abbrev NonnegativeSpectrum (X : Type u) [TopologicalSpace X] :=
  EssentialSimpleFreeClass X → ℝ≥0

/-- The positive spectrum product topology is exactly coordinatewise continuity. -/
theorem continuous_positiveSpectrum_iff
    {X : Type u} [TopologicalSpace X] {A : Type v} [TopologicalSpace A]
    (f : A → PositiveSpectrum X) :
    Continuous f ↔ ∀ c, Continuous fun a => f a c :=
  continuous_pi_iff

/-- The nonnegative spectrum product topology is exactly coordinatewise continuity. -/
theorem continuous_nonnegativeSpectrum_iff
    {X : Type u} [TopologicalSpace X] {A : Type v} [TopologicalSpace A]
    (f : A → NonnegativeSpectrum X) :
    Continuous f ↔ ∀ c, Continuous fun a => f a c :=
  continuous_pi_iff

/-- Include a strictly positive spectrum without changing any real coordinate. -/
def positiveSpectrumToNonnegative
    {X : Type u} [TopologicalSpace X] (f : PositiveSpectrum X) : NonnegativeSpectrum X :=
  fun c => NNReal.mk (f c).1 (f c).2.le

/-- The original positive-to-nonnegative coordinate inclusion is continuous. -/
theorem continuous_positiveSpectrumToNonnegative
    {X : Type u} [TopologicalSpace X] :
    Continuous (positiveSpectrumToNonnegative : PositiveSpectrum X → NonnegativeSpectrum X) := by
  apply continuous_pi
  intro c
  exact (continuous_subtype_val.comp (continuous_apply c)).subtype_mk _

/-- Passing to the larger coordinate cone retains every original spectrum. -/
theorem positiveSpectrumToNonnegative_injective
    {X : Type u} [TopologicalSpace X] :
    Function.Injective (positiveSpectrumToNonnegative : PositiveSpectrum X → NonnegativeSpectrum X) := by
  intro f g h
  funext c
  apply Subtype.ext
  exact congrArg (fun k : NonnegativeSpectrum X => (k c : ℝ)) h

end LowDimensionalTopology.Geometry.Surfaces
