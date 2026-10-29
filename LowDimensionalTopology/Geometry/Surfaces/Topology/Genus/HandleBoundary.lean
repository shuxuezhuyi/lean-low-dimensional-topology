/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CanonicalHandleCW
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Metric Topology
namespace LowDimensionalTopology.Geometry.Surfaces.HandlePresentation

/-- The actual closed complex disc used for the canonical polygon. -/
abbrev Disc := HandleSeparation.Disc

/-- The quotient by the literal oriented polygon edge identifications.
For positive genus this is the defining quotient of `CanonicalHandleSurface`. -/
abbrev PolygonQuotient (g : ℕ) := Quot (CanonicalHandleIdent g)

def projection (g : ℕ) : Disc → PolygonQuotient g := Quot.mk _

def zeroDisc : Disc := ⟨0, by simp⟩

def center (g : ℕ) : PolygonQuotient g := projection g zeroDisc

/-- The image of the geometric boundary circle, with no graph presentation assumed. -/
def boundary (g : ℕ) : Set (PolygonQuotient g) :=
  projection g '' {z : Disc | ‖z.val‖ = 1}

abbrev Boundary (g : ℕ) := ↥(boundary g)

def punctured (g : ℕ) : Set (PolygonQuotient g) := {x | x ≠ center g}

abbrev Punctured (g : ℕ) := ↥(punctured g)

instance polygonQuotientT2 (g : ℕ) : T2Space (PolygonQuotient g) :=
  HandleSeparation.canonicalHandleQuotientT2 g

theorem projection_continuous (g : ℕ) : Continuous (projection g) :=
  continuous_quot_mk

theorem projection_surjective (g : ℕ) : Function.Surjective (projection g) :=
  Quot.mk_surjective

theorem projection_closedMap (g : ℕ) : IsClosedMap (projection g) :=
  HandleCW.quotient_projection_closedMap g

@[simp] theorem projection_eq_center_iff {g : ℕ} {z : Disc} :
    projection g z = center g ↔ z = zeroDisc := by
  constructor
  · exact HandleCW.quotient_interior_fiber_singleton (by simp [zeroDisc])
  · rintro rfl
    rfl

@[simp] theorem projection_mem_punctured_iff {g : ℕ} {z : Disc} :
    projection g z ∈ punctured g ↔ z ≠ zeroDisc := by
  simp only [punctured, Set.mem_ofPred_eq, ne_eq, projection_eq_center_iff]

theorem boundary_closed (g : ℕ) : IsClosed (boundary g) :=
  projection_closedMap g _ (isClosed_eq (continuous_norm.comp continuous_subtype_val)
    continuous_const)

theorem boundary_compact (g : ℕ) : IsCompact (boundary g) :=
  (boundary_closed g).isCompact

instance boundaryCompactSpace (g : ℕ) : CompactSpace (Boundary g) :=
  isCompact_iff_compactSpace.mp (boundary_compact g)

theorem punctured_open (g : ℕ) : IsOpen (punctured g) :=
  isClosed_singleton.isOpen_compl

theorem boundary_subset_punctured (g : ℕ) : boundary g ⊆ punctured g := by
  rintro _ ⟨z, hz, rfl⟩
  rw [projection_mem_punctured_iff]
  intro he
  have : ‖(zeroDisc : Disc).val‖ = 1 := he ▸ hz
  simp [zeroDisc] at this

/-- The common endpoint of all polygon edges. -/
def boundaryBase (g : ℕ) : Boundary g :=
  ⟨projection g (handleBoundaryPoint 0),
    ⟨handleBoundaryPoint 0, handleBoundaryPoint_norm 0, rfl⟩⟩

/-- Inclusion of the actual geometric boundary in the punctured quotient. -/
def boundaryInclusion (g : ℕ) : C(Boundary g, Punctured g) :=
  ⟨fun x => ⟨x.val, boundary_subset_punctured g x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

@[simp] theorem boundaryInclusion_val (g : ℕ) (x : Boundary g) :
    (boundaryInclusion g x).val = x.val := rfl

end LowDimensionalTopology.Geometry.Surfaces.HandlePresentation
