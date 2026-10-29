module

public import LowDimensionalTopology.Geometry.Teichmuller.EssentialMarkedGeodesicLength
public import LowDimensionalTopology.Geometry.Surfaces.SpectrumCones
public import LowDimensionalTopology.External.TauCeti.AlgebraicTopology.UniversalCover.Circle.FundamentalGroup

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

/-- One complete positive traversal of the actual supplied circle map. -/
def circleRepresentativeLoop {X : Type} [TopologicalSpace X]
    (f : C(Circle, X)) : LiZhongQC.Loop X :=
  ⟨f 1, Circle.expLoop.map f.continuous⟩

/-- A homotopy of actual circle maps transports the same full traversal. -/
theorem circleRepresentativeLoop_homotopic {X : Type} [TopologicalSpace X]
    {f g : C(Circle, X)} (h : f.Homotopic g) :
    LiZhongQC.FreelyHomotopic (circleRepresentativeLoop f) (circleRepresentativeLoop g) :=
  LiZhongQC.s30b_fh_of_homotopic h ⟨1, Circle.expLoop⟩

/-- This direction alone does not establish essentiality of the loop. -/
theorem circleRepresentativeLoop_null_of_null {X : Type} [TopologicalSpace X]
    {f : C(Circle, X)} (h : f.Nullhomotopic) :
    IsNullHomotopicLoop (circleRepresentativeLoop f) := by
  obtain ⟨x, h⟩ := h
  exact ⟨x, circleRepresentativeLoop_homotopic h⟩

/-- The native marked length already ignores the supplied circle-map homotopy. -/
theorem markedGeodesicLength_circleRepresentative_homotopic
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)
    {f k : C(Circle, X)} (h : f.Homotopic k) (t : TeichmullerSpace.{0, 0} R) :
    markedGeodesicLength R hg hgenus (circleRepresentativeLoop f) t =
      markedGeodesicLength R hg hgenus (circleRepresentativeLoop k) t := by
  refine Quotient.inductionOn t ?_
  intro m
  exact congrArg ENNReal.toReal (LiZhongQC.s30b_fhl_congr _
    (LiZhongQC.s30b_fh_map m.markingMap.continuous
      (circleRepresentativeLoop_homotopic h)))

end LowDimensionalTopology.Geometry.Teichmuller
