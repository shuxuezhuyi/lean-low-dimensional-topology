module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalReflectedClosedSurface
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCClosedCompatibility
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.Closed

/-!
# The same marking between the two actual mirror surfaces

The reference and target are read in their conjugate native atlases. The
point map and conformal comparison witnesses are the original ones. No base
involution or new normalized lift is selected in this construction.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open Surfaces

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The mirror has the same genuine topological genus on the unchanged space. -/
theorem originalMirrorNative_hasGenus {g : ℕ} (hgenus : R.HasGenus g) :
    (originalMirrorNative R.toSourceClosedRS).HasGenus g := hgenus

/-- Keep the original point map and read its source and target in their mirrors. -/
def originalMirroredClosedMarked (m : ClosedMarked R) :
    ClosedMarked (originalMirrorNative R.toSourceClosedRS) := by
  let A := R.toSourceClosedRS
  let S := closedTarget R m
  refine
    { target := Surface.ofRiemannSurface (originalMirrorNative S).toRiemannSurface
      marking := m.marking
      qc := ?_ }
  have hqc := originalMirror_isQCRS A S m.marking m.qc
  exact (qc_closed_toNative (originalMirrorClosedRS A)
    (originalMirrorClosedRS S) m.marking hqc).1

/-- The target is literally the native mirror of the actual original target. -/
theorem originalMirroredClosedMarked_target (m : ClosedMarked R) :
    (originalMirroredClosedMarked R m).target =
      Surface.ofRiemannSurface
        (originalMirrorNative (closedTarget R m)).toRiemannSurface := rfl

/-- The actual marking is unchanged at every original point. -/
theorem originalMirroredClosedMarked_apply (m : ClosedMarked R) (x : X) :
    (originalMirroredClosedMarked R m).marking x = m.marking x := rfl

/-- The same original conformal witness and homotopy compare the mirror markings. -/
theorem originalMirroredClosedMarked_equivalent (m n : ClosedMarked R)
    (h : m.Equivalent n) :
    (originalMirroredClosedMarked R m).Equivalent
      (originalMirroredClosedMarked R n) := by
  obtain ⟨c, hc, H⟩ := h
  let S := closedTarget R m
  let T := closedTarget R n
  have hcmirror := originalMirror_isBiholomorphic S T c hc
  have hcnative := biholomorphic_closed_toNative
    (originalMirrorClosedRS S) (originalMirrorClosedRS T) c hcmirror
  exact ⟨c, hcnative, H⟩

/-- The literal unchanged-point mirror operation descends to the original quotient. -/
def originalMirroredClass :
    ClosedSpace R → ClosedSpace (originalMirrorNative R.toSourceClosedRS) :=
  Quotient.lift (fun m => mk (originalMirroredClosedMarked R m))
    (fun m n h => Quotient.sound (originalMirroredClosedMarked_equivalent R m n h))

/-- The mirror class contains the same actual marking in the actual mirror target. -/
theorem originalMirroredClass_mk (m : ClosedMarked R) :
    originalMirroredClass R (mk m) = mk (originalMirroredClosedMarked R m) := rfl

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
