module

public import LowDimensionalTopology.Geometry.Surfaces.SpectrumCones
public import Mathlib.Topology.Constructions

/-!
# Positive projectivization of the original spectrum cones

A single strictly positive real factor scales every coordinate. The closed
nonnegative cone loses only its whole zero spectrum before taking the quotient;
the strictly positive product has its own quotient. Each has the quotient
topology of its original product or nonzero subspace.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Topology

namespace LowDimensionalTopology.Geometry.Surfaces

universe u

/-- Equality up to one common strictly positive real scale, including the zero orbit. -/
def nonnegativeSpectrumScaleSetoid (X : Type u) [TopologicalSpace X] :
    Setoid (NonnegativeSpectrum X) where
  r f g := ∃ c : ℝ, 0 < c ∧ ∀ a, (f a : ℝ) = c * (g a : ℝ)
  iseqv := ⟨fun f => ⟨1, zero_lt_one, fun a => (one_mul _).symm⟩, by
    intro f g h
    rcases h with ⟨c, hc, h⟩
    refine ⟨c⁻¹, inv_pos.mpr hc, fun a => ?_⟩
    rw [h a, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hc), one_mul], by
    intro f g h hfg hgh
    rcases hfg with ⟨c, hc, hfg⟩
    rcases hgh with ⟨d, hd, hgh⟩
    exact ⟨c * d, mul_pos hc hd, fun a => by rw [hfg a, hgh a, mul_assoc]⟩⟩

/-- Delete the constant zero function, retaining spectra with some zero coordinates. -/
abbrev NonzeroNonnegativeSpectrum (X : Type u) [TopologicalSpace X] :=
  {f : NonnegativeSpectrum X // f ≠ 0}

/-- The nonnegative spectrum cone modulo common positive scaling, with zero removed. -/
def ProjectiveNonnegativeSpectrum (X : Type u) [TopologicalSpace X] :=
  Quotient (Setoid.comap (Subtype.val : NonzeroNonnegativeSpectrum X → NonnegativeSpectrum X)
    (nonnegativeSpectrumScaleSetoid X))

instance projectiveNonnegativeSpectrumTopology (X : Type u) [TopologicalSpace X] :
    TopologicalSpace (ProjectiveNonnegativeSpectrum X) :=
  inferInstanceAs (TopologicalSpace (Quotient (Setoid.comap
    (Subtype.val : NonzeroNonnegativeSpectrum X → NonnegativeSpectrum X)
    (nonnegativeSpectrumScaleSetoid X))))

def projectivizeNonnegativeSpectrum {X : Type u} [TopologicalSpace X]
    (f : NonzeroNonnegativeSpectrum X) : ProjectiveNonnegativeSpectrum X :=
  Quotient.mk _ f

theorem projectivizeNonnegativeSpectrum_eq_iff {X : Type u} [TopologicalSpace X]
    (f g : NonzeroNonnegativeSpectrum X) :
    projectivizeNonnegativeSpectrum f = projectivizeNonnegativeSpectrum g ↔
      ∃ c : ℝ, 0 < c ∧ ∀ a, (f.val a : ℝ) = c * (g.val a : ℝ) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem isQuotientMap_projectivizeNonnegativeSpectrum {X : Type u} [TopologicalSpace X] :
    IsQuotientMap (projectivizeNonnegativeSpectrum (X := X)) :=
  isQuotientMap_quotient_mk'

/-- Pull common positive scaling back to the actual strictly positive product. -/
def positiveSpectrumScaleSetoid (X : Type u) [TopologicalSpace X] :
    Setoid (PositiveSpectrum X) :=
  Setoid.comap positiveSpectrumToNonnegative (nonnegativeSpectrumScaleSetoid X)

/-- The strictly positive spectrum product modulo one common positive real scale. -/
def ProjectivePositiveSpectrum (X : Type u) [TopologicalSpace X] :=
  Quotient (positiveSpectrumScaleSetoid X)

instance projectivePositiveSpectrumTopology (X : Type u) [TopologicalSpace X] :
    TopologicalSpace (ProjectivePositiveSpectrum X) :=
  inferInstanceAs (TopologicalSpace (Quotient (positiveSpectrumScaleSetoid X)))

def projectivizePositiveSpectrum {X : Type u} [TopologicalSpace X]
    (f : PositiveSpectrum X) : ProjectivePositiveSpectrum X :=
  Quotient.mk _ f

theorem projectivizePositiveSpectrum_eq_iff {X : Type u} [TopologicalSpace X]
    (f g : PositiveSpectrum X) :
    projectivizePositiveSpectrum f = projectivizePositiveSpectrum g ↔
      ∃ c : ℝ, 0 < c ∧ ∀ a, (f a : ℝ) = c * (g a : ℝ) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem isQuotientMap_projectivizePositiveSpectrum {X : Type u} [TopologicalSpace X] :
    IsQuotientMap (projectivizePositiveSpectrum (X := X)) :=
  isQuotientMap_quotient_mk'

end LowDimensionalTopology.Geometry.Surfaces
