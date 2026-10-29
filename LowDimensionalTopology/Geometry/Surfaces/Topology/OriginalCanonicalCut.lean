/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedPolygonMonodromy
public import LowDimensionalTopology.External.LiZhongQC.Ch01.S07_GeometricDefinition

/-!
# Original-oriented geometric canonical cuts in positive genus

The actual polygon quotient carries its literal ordered side paths. A supplied
cut homeomorphism identifies its vertex with the original basepoint and its
open disc with the cut surface. Positivity is tested against every original
complex chart on the actual inverse chart domain. The ordered based classes
are derived from those same side paths.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Surfaces

open HandlePresentation

variable {X : Type} [TopologicalSpace X] {g : ℕ}

/-- The actual cut's plane map, using the existing closed-disc clamp and
the literal polygon quotient projection. -/
def originalCanonicalCutPlane (e : X ≃ₜ PolygonQuotient g) : C(ℂ, X) :=
  ⟨fun z => e.symm (projection g (HandleCW.closedDiscClamp z)),
    e.symm.continuous.comp ((projection_continuous g).comp
      HandleCW.closedDiscClamp_continuous)⟩

/-- An original-orientation-compatible geometric cut with its actual vertex.
The ordered loops come from the same polygon, whose interior is the cut disc. -/
structure OriginalOrientedCanonicalCut (R : ClosedRiemannSurface X)
    (g : ℕ) (hg : 0 < g) (p : X) where
  polygon : X ≃ₜ PolygonQuotient g
  vertex : polygon p = (boundaryBase g).val
  positive : ∀ c ∈ R.toRiemannAtlas.charts,
    LiZhongQC.IsSensePreserving
      (fun z => c (originalCanonicalCutPlane polygon z))
      (Metric.ball (0 : ℂ) 1 ∩ originalCanonicalCutPlane polygon ⁻¹' c.source)

namespace OriginalOrientedCanonicalCut

variable {R : ClosedRiemannSurface X} {hg : 0 < g} {p : X}

/-- The actual polygon vertex pulls back to the prescribed original basepoint. -/
theorem basepoint_eq (D : OriginalOrientedCanonicalCut R g hg p) :
    D.polygon.symm (boundaryBase g).val = p := by
  rw [← D.vertex]
  exact D.polygon.symm_apply_apply p

/-- The actual positive polygon side loop with both endpoints at the original
basepoint. The equality cast leaves its entire underlying path unchanged. -/
def loop (D : OriginalOrientedCanonicalCut R g hg p) (d : Fin g × Fin 2) : Path p p :=
  (markedPolygonLoop D.polygon d).cast D.basepoint_eq.symm D.basepoint_eq.symm

/-- Every point of the derived loop is the image of the same positive side. -/
theorem loop_apply (D : OriginalOrientedCanonicalCut R g hg p)
    (d : Fin g × Fin 2) (t : unitInterval) :
    D.loop d t = D.polygon.symm (positivePolygonLoop d t) := rfl

/-- The ordered actual fundamental-group classes of the two sides per handle. -/
def family (D : OriginalOrientedCanonicalCut R g hg p) :
    Fin g × Fin 2 → FundamentalGroup X p :=
  fun d => pathClass (D.loop d)

/-- The actual image of the whole boundary of the same cut polygon. -/
def cutGraph (D : OriginalOrientedCanonicalCut R g hg p) : Set X :=
  D.polygon.symm '' boundary g

end OriginalOrientedCanonicalCut

/-- An ordered original based family is realized by an actual compatible
oriented polygon cut, with the same original basepoint and actual side classes. -/
def HasOriginalCanonicalCut (R : ClosedRiemannSurface X) (g : ℕ) (hg : 0 < g)
    (p : X) (classes : Fin g × Fin 2 → FundamentalGroup X p) : Prop :=
  ∃ D : OriginalOrientedCanonicalCut R g hg p, D.family = classes

end LowDimensionalTopology.Geometry.Surfaces
