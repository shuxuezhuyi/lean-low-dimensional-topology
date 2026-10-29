module

public import LowDimensionalTopology.Geometry.Teichmuller.SourceLoopBasepoint
public import LowDimensionalTopology.Geometry.Teichmuller.FixedSourceBasedLoopCovers

/-! A single original source word covers the transported actual free class of
an arbitrary original loop, without a restriction on its original basepoint. -/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces Surfaces.HandlePresentation

/-- Choose the based representative and word once on the original source.
Every actual marked target retains the same matrix word and transported free class. -/
theorem fixedSourceLoop_word_covers_freeClass
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (e : X ≃ₜ PolygonQuotient g) (α : LiZhongQC.Loop X) :
    ∃ (β : Path (e.symm (boundaryBase g).val) (e.symm (boundaryBase g).val))
      (w : FreeGroup (StandardLabels g)),
      LiZhongQC.FreelyHomotopic α ⟨e.symm (boundaryBase g).val, β⟩ ∧
      ∀ (m : MarkedRiemannSurface.{0, 0} R) (P : NormalizedCanonicalFuchsianModel hg e m),
        LiZhongQC.Covers P.model.halfPlaneCover
          (FreeGroup.lift (fun s => P.matrices ((edgeLabelEquiv g).symm s)) w)
          ⟨m.markingMap (e.symm (boundaryBase g).val), β.map m.markingMap.continuous⟩ ∧
        LiZhongQC.FreelyHomotopic ⟨m.markingMap α.1, α.2.map m.markingMap.continuous⟩
          ⟨m.markingMap (e.symm (boundaryBase g).val), β.map m.markingMap.continuous⟩ := by
  obtain ⟨β, hβ⟩ := R.exists_source_based_loop α (e.symm (boundaryBase g).val)
  obtain ⟨w, hw⟩ := fixedSourceBasedLoop_word_covers (R := R) (hg := hg) (e := e) β
  refine ⟨β, w, hβ, ?_⟩
  intro m P
  exact ⟨hw m P, LiZhongQC.s30b_fh_map m.markingMap.continuous hβ⟩

end LowDimensionalTopology.Geometry.Teichmuller
