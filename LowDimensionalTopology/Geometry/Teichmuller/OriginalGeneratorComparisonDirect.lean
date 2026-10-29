/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalGeneratorComparison
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalCanonicalCutQCTransport

/-!
# Canonical-marked comparison with explicit geometric premises

The same cut's positive transport gives the smooth-marking transport used by
the literal quotient map. Together with prescribed positive smooth realization,
it gives bijectivity of that same original quotient comparison.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

/-- The native canonical-marked comparison is bijective under positive
transport of the same cut and prescribed positive smooth realization. -/
theorem originalGeneratorComparison_bijective_of_qcCutPositiveTransport
    {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g)
    (D : OriginalOrientedCanonicalCut B.surface g
      (lt_trans Nat.zero_lt_one hg) B.point)
    (hD : D.family = B.classes)
    (hGeom : Unproved.Teichmuller.OriginalCanonicalCutQCPositiveTransport
      B.surface hg B.point D)
    (hRealize : Unproved.Teichmuller.OriginalGeneratorPrescribedPositiveSmoothRealization
      hg B) :
    Function.Bijective
      (originalGeneratorComparison hg B
        (originalCanonicalFamilyMarkingTransport_of_qcCutPositiveTransport
          hg B D hD hGeom)) := by
  exact originalGeneratorComparison_bijective hg B
    (originalCanonicalFamilyMarkingTransport_of_qcCutPositiveTransport hg B D hD hGeom) hRealize

end LowDimensionalTopology.Geometry.Teichmuller
