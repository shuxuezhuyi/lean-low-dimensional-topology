module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticRegularLeafChart
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticLeafChartPlaques
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticProngModel

/-!
# The raw horizontal foliation atlas of the given differential

The actual zeros form the singular set. Genuine flat charts in the original
real smooth structure cover its complement, agree in their local plaques,
and have the original finite-order prong models at every zero.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces

variable {X : Type} [TopologicalSpace X]

/-- A nonzero original differential has an actual aligned horizontal foliation atlas. -/
theorem exists_horizontalFoliationAtlasOf (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0) :
    ∃ A : SingularFoliationAtlas R, IsHorizontalFoliationAtlasOf R q A := by
  let := R.toRiemannAtlas.toChartedSpace
  let C : Set (OpenPartialHomeomorph X ℂ) :=
    {e | IsQuadraticNaturalLeafChart R q e ∧ IsRealSmoothFoliationChart R e}
  have hcover (x : X) (hx : x ∉ quadraticZeroSet R q) :
      ∃ e ∈ C, x ∈ e.source := by
    let D := chooseQuadraticNaturalCoordinateData R q hq x
    have hr : LiZhongQC.IsRegularPoint (q : X → ℂ → ℂ) x := by
      by_contra h
      exact hx h
    exact ⟨D.ordinaryNeighborhood,
      ⟨D.ordinaryNeighborhood_isQuadraticNatural_of_regular hr,
        D.ordinaryNeighborhood_isRealSmooth⟩, D.ordinaryNeighborhood_data.1⟩
  let A : SingularFoliationAtlas R :=
    { singular := quadraticZeroSet R q
      singular_finite := quadraticZeroSet_finite R q hq
      charts := C
      chart_regular := by
        intro e he x hx hxzero
        exact hxzero (he.1.1 hx)
      chart_smooth := fun e he => he.2
      cover := hcover
      compatible := by
        intro e he d hd p hp
        exact quadraticNaturalLeafCharts_locallySamePlaques he.1 hd.1 hp
      prongs := by
        intro p hp
        let D := chooseQuadraticNaturalCoordinateData R q hq p
        let H := D.ordinaryNeighborhood.transHomeomorph
          (Homeomorph.mulLeft₀ (quadraticZeroScaling D.order)
            (quadraticZeroScaling_ne_zero D.order))
        have hP : 0 < D.order ∧ H.source ∩ quadraticZeroSet R q = {p} ∧
            MatchesProngModel R C D.order 1 H p :=
          D.ordinaryNeighborhood_scaledProngModel hp
        exact ⟨D.order, hP.1, H, hP.2.1, hP.2.2⟩ }
  refine ⟨A, rfl, ?_⟩
  intro p hp
  have hregular : p ∉ quadraticZeroSet R q := fun hzero => hzero hp
  obtain ⟨e, he, hpe⟩ := hcover p hregular
  refine ⟨e, he, e, he.1, e.source, e.open_source, hpe,
    fun x hx => ⟨hx, hx⟩, ?_⟩
  exact fun _ _ _ _ => Iff.rfl

end LowDimensionalTopology.Geometry.Teichmuller
