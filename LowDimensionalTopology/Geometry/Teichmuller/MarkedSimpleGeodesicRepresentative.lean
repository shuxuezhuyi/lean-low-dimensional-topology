module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedGeodesicLength
public import LowDimensionalTopology.Geometry.Surfaces.EssentialSimpleClassHomeomorph
public import LowDimensionalTopology.Unproved.Surfaces.SimpleClosedGeodesicRepresentatives

/-!
# Simple geodesics on the actual marked target

The chosen geodesic represents one full traversal of the original embedded
circle after the actual marking. Simplicity uses the explicit classical
representative premise; geometric uniqueness and marked length use the
existing original metric theorems.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)

/-- A simple representative on the unchanged marked target, with its actual
marked length and uniqueness of its geometric image. -/
theorem exists_marked_simple_geodesic
    (m : MarkedRiemannSurface.{0, 0} R) (c : EssentialSimpleCircle X)
    (hSimple : Unproved.Surfaces.SimpleClosedGeodesicRepresentatives m.surface g
      (m.geodesicLengthModel R hg hgenus)) :
    ∃ q : OriginalClosedGeodesic (m.geodesicLengthModel R hg hgenus),
      LiZhongQC.FreelyHomotopic
        (circleRepresentativeLoop (c.mapHomeomorph m.marking.toHomeomorph).val) q.toLoop ∧
      Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → m.carrier) ∧
      markedGeodesicLength R hg hgenus (circleRepresentativeLoop c.val)
        (TeichmullerSpace.mk m) = q.length.toReal ∧
      ∀ r : OriginalClosedGeodesic (m.geodesicLengthModel R hg hgenus),
        LiZhongQC.FreelyHomotopic
          (circleRepresentativeLoop (c.mapHomeomorph m.marking.toHomeomorph).val) r.toLoop →
        Set.range r.curve = Set.range q.curve := by
  let := m.surface.compactSpace
  have hmgenus : m.surface.HasGenus g := by
    obtain ⟨e⟩ := hgenus
    exact ⟨m.marking.toHomeomorph.symm.trans e⟩
  obtain ⟨q, hq, hinj⟩ := hSimple hg hmgenus (c.mapHomeomorph m.marking.toHomeomorph)
  refine ⟨q, hq, hinj, ?_, ?_⟩
  · apply markedGeodesicLength_mk_eq R hg hgenus (circleRepresentativeLoop c.val) m
      (m.geodesicLengthModel R hg hgenus) q
    exact hq
  · intro r hr
    exact (q.trace_eq_of_freelyHomotopic r q.not_isNullHomotopicLoop
      (LiZhongQC.s30b_fh_trans (LiZhongQC.s30b_fh_symm hq) hr)).symm

/-- Select the simple geodesic on this same target in the marked circle class. -/
def MarkedRiemannSurface.simpleGeodesicRepresentative
    (m : MarkedRiemannSurface.{0, 0} R) (c : EssentialSimpleCircle X)
    (hSimple : Unproved.Surfaces.SimpleClosedGeodesicRepresentatives m.surface g
      (m.geodesicLengthModel R hg hgenus)) :
    OriginalClosedGeodesic (m.geodesicLengthModel R hg hgenus) :=
  (exists_marked_simple_geodesic R hg hgenus m c hSimple).choose

/-- The selected curve retains the original full free class and simple period. -/
theorem MarkedRiemannSurface.simpleGeodesicRepresentative_spec
    (m : MarkedRiemannSurface.{0, 0} R) (c : EssentialSimpleCircle X)
    (hSimple : Unproved.Surfaces.SimpleClosedGeodesicRepresentatives m.surface g
      (m.geodesicLengthModel R hg hgenus)) :
    let q := m.simpleGeodesicRepresentative R hg hgenus c hSimple
    LiZhongQC.FreelyHomotopic
      (circleRepresentativeLoop (c.mapHomeomorph m.marking.toHomeomorph).val) q.toLoop ∧
    Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → m.carrier) := by
  exact ⟨(exists_marked_simple_geodesic R hg hgenus m c hSimple).choose_spec.1,
    (exists_marked_simple_geodesic R hg hgenus m c hSimple).choose_spec.2.1⟩

end LowDimensionalTopology.Geometry.Teichmuller
