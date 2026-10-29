/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalGeneratorMarkedSurface
public import LowDimensionalTopology.Geometry.Teichmuller.Marking

/-!
# Geometric transport and prescribed smooth realization of ordered markings

Both propositions fix one actual higher-genus reference surface with its
original geometric canonical family. The first concerns transport by an
actual positive smooth marking. The second requires a positive smooth map
realizing every prescribed ordered target class through one common path.
All surfaces retain their original carriers, complex atlases and based
classes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller

/-- Every actual positive smooth marking of the fixed reference transports
its same original geometric canonical family to the induced family on the
unchanged target, at the actual image basepoint. -/
def OriginalCanonicalFamilyMarkingTransport {g : ℕ} (_hg : 1 < g)
    (B : OriginalGeneratorMarkedSurface g) : Prop :=
  ∀ m : MarkedRiemannSurface.{0, 0} B.surface,
    IsOriginalCanonicalFamily m.surface g (m.markingMap B.point)
      (fun d : Fin g × Fin 2 =>
        FundamentalGroup.map m.markingMap B.point (B.classes d))

/-- Every original geometrically marked target is realized by one positive
real smooth diffeomorphism from the same reference and one common basepoint
path. The same map and path identify every prescribed ordered class. -/
def OriginalGeneratorPrescribedPositiveSmoothRealization {g : ℕ} (_hg : 1 < g)
    (B : OriginalGeneratorMarkedSurface g) : Prop :=
  ∀ N : OriginalGeneratorMarkedSurface g,
    ∃ F : SmoothSurfaceEquiv B.surface.toRiemannSurface N.surface.toRiemannSurface,
      PreservesComplexOrientation B.surface.toRiemannAtlas N.surface.toRiemannAtlas
        F.toHomeomorph ∧
      ∃ c : Path (F.toHomeomorph B.point) N.point,
        ∀ d : Fin g × Fin 2,
          FundamentalGroup.fundamentalGroupMulEquivOfPath c
            (FundamentalGroup.map
              (⟨F.toHomeomorph, F.toHomeomorph.continuous⟩ : C(B.carrier, N.carrier))
              B.point (B.classes d)) = N.classes d

end LowDimensionalTopology.Unproved.Teichmuller
