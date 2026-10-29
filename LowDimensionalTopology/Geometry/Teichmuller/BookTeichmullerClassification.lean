module

public import LowDimensionalTopology.Geometry.Teichmuller.NormalizedTeichmullerMaps

/-!
# Book-defined Teichmüller maps on the original surfaces

The definition bundles actual quasiconformality with the literal normalized
Beltrami law for a differential in the book L1 unit ball. Its equivalence with
natural parameters is proved by actual same-Beltrami comparison and positive
normalization; neither natural parameters nor a terminal differential are assumed.

The analytic source results are due to Wu Xiaobin, Li-Zhong-QC-formalization,
commit `1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0); see
`THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u v

/-- An actual QC homeomorphism is a book Teichmüller map when its coefficient is
`‖φ‖₁ conj(φ)/|φ|` for an original-atlas differential in the literal L1 unit ball.
The zero differential includes all analytic homeomorphisms. -/
def IsBookTeichmullerMap
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y) (f : X ≃ₜ Y) : Prop :=
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  LiZhongQC.IsQCRS f ∧
    ∃ φ : HolomorphicQuadraticDifferential R.toRiemannAtlas,
      φ ∈ QuadraticL1.openUnitBall R ∧ HasBookTeichmullerCoefficient R S f φ

/-- The literal book definition is equivalent to analytic maps or genuine
natural-parameter Teichmüller maps, on the unchanged original source and target. -/
theorem isBookTeichmullerMap_iff_geometric
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y) (f : X ≃ₜ Y) :
    IsBookTeichmullerMap R S f ↔
      let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f ∨
        ∃ (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
          (q' : HolomorphicQuadraticDifferential S.toRiemannAtlas) (k : ℝ),
          LiZhongQC.IsTeichmullerMap f q q' k := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := S.toRiemannAtlas.isManifold
  let := R.connectedSpace
  dsimp only [IsBookTeichmullerMap]
  constructor
  · rintro ⟨hf, φ, hφ, hμ⟩
    rcases bookCoefficient_geometric R S φ hφ f hf hμ with ⟨_, ha⟩ | ⟨q', hT⟩
    · exact Or.inl ha
    · exact Or.inr ⟨φ, q', QuadraticL1.bookNorm R φ, hT⟩
  · rintro (ha | ⟨q, q', k, hT⟩)
    · have hb := (analyticHomeomorph_iff_sourceBiholomorphic
        R.toRiemannAtlas S.toRiemannAtlas f).mp ha
      have hzero : QuadraticL1.bookNorm R
          (0 : HolomorphicQuadraticDifferential R.toRiemannAtlas) = 0 := by
        let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
          QuadraticL1.normedAddCommGroup R
        rw [← QuadraticL1.norm_eq_bookNorm R 0, norm_zero]
      exact ⟨⟨1, (LiZhongQC.isKQCRS_one_iff f).2 hb⟩, 0,
        (QuadraticL1.mem_openUnitBall R 0).mpr (by rw [hzero]; norm_num),
        analytic_hasBookTeichmullerCoefficient_zero R S f ha⟩
    · obtain ⟨φ, hφ, _, hμ⟩ := normalize_teichmullerMap_bookCoefficient R S hT
      exact ⟨hT.qc, φ, hφ, hμ⟩

end LowDimensionalTopology.Geometry.Teichmuller
