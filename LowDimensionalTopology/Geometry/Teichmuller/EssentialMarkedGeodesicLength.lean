module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedGeodesicLength
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedGeodesicExistence

@[expose] public section
noncomputable section
namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces
variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)

/-- Source essentiality gives an actual geodesic and positive length on each marked target. -/
theorem markedGeodesicLength_mk_exists_positive
    (α : LiZhongQC.Loop X) (hα : ¬ IsNullHomotopicLoop α)
    (m : MarkedRiemannSurface.{0, 0} R) :
    ∃ q : OriginalClosedGeodesic (m.geodesicLengthModel R hg hgenus),
      LiZhongQC.FreelyHomotopic
        ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩ q.toLoop ∧
      0 < markedGeodesicLength R hg hgenus α (TeichmullerSpace.mk m) := by
  let e := m.marking.toHomeomorph
  have htarget : ¬ IsNullHomotopicLoop
      (⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩ : LiZhongQC.Loop m.carrier) := by
    rintro ⟨y, H, h0, h1, hp⟩
    exact hα ⟨e.symm y,
      ⟨fun p => e.symm (H p), e.symm.continuous.comp H.continuous⟩,
      (fun t => (congrArg e.symm (h0 t)).trans (e.symm_apply_apply _)),
      (fun t => congrArg e.symm (h1 t)), fun s => congrArg e.symm (hp s)⟩
  let := m.surface.compactSpace
  obtain ⟨q, hq⟩ := (m.geodesicLengthModel R hg hgenus).exists_original_closed_geodesic_of_not_null
    ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩ htarget
  refine ⟨q, hq, ?_⟩
  rw [markedGeodesicLength_mk_eq R hg hgenus α m _ q hq]
  exact q.length_toReal_pos

/-- The same essential source class has positive length at every native marked point. -/
theorem markedGeodesicLength_pos (α : LiZhongQC.Loop X) (hα : ¬ IsNullHomotopicLoop α)
    (t : TeichmullerSpace.{0, 0} R) : 0 < markedGeodesicLength R hg hgenus α t := by
  refine Quotient.inductionOn t ?_
  intro m
  obtain ⟨_, _, hpos⟩ := markedGeodesicLength_mk_exists_positive R hg hgenus α hα m
  exact hpos

end LowDimensionalTopology.Geometry.Teichmuller
