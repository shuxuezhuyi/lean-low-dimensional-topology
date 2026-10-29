/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.Topology.DehnAmbientHomeomorph

/-!
# The original full turn about an identified annular core

The annular neighborhood and its interior core are supplied as actual data.
The full turn uses their given circle and interval coordinates. The identified
core has the same exact rotation formula as the ambient annular map. Choosing
an annulus for an arbitrary curve and ambient orientation preservation remain
separate geometric assertions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

variable {X : Type} [TopologicalSpace X]

/-- The literal full turn for a given closed annulus and its given interior
core curve. The actual original ambient homeomorphism is retained. -/
def dehnTwistAboutCore (core : Circle → X) (e : Circle × unitInterval → X)
    (he : Topology.IsClosedEmbedding e)
    (hopen : IsOpen (e '' {p : Circle × unitInterval |
      0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}))
    (a : unitInterval) (_ha : 0 < (a : ℝ) ∧ (a : ℝ) < 1)
    (_hcore : ∀ s : Circle, e (s, a) = core s) : X ≃ₜ X :=
  dehnAmbientHomeomorph e he hopen

/-- The same ambient full turn rotates the identified actual core by its
literal annular circle coordinate. No different core map is chosen. -/
theorem dehnTwistAboutCore_apply_core (core : Circle → X)
    (e : Circle × unitInterval → X) (he : Topology.IsClosedEmbedding e)
    (hopen : IsOpen (e '' {p : Circle × unitInterval |
      0 < (p.2 : ℝ) ∧ (p.2 : ℝ) < 1}))
    (a : unitInterval) (ha : 0 < (a : ℝ) ∧ (a : ℝ) < 1)
    (hcore : ∀ s : Circle, e (s, a) = core s) (s : Circle) :
    dehnTwistAboutCore core e he hopen a ha hcore (core s) =
      core (s * Circle.exp (2 * Real.pi * (a : ℝ))) := by
  change dehnAmbientHomeomorph e he hopen (core s) = _
  rw [← hcore s, dehnAmbientHomeomorph_apply_image]
  exact hcore _

end LowDimensionalTopology.Geometry.Surfaces
