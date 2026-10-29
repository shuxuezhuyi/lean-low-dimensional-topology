module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeRootHorizontalFlowAction

/-!
# Bijectivity of the actual root-oriented time maps

The inverse of the same time-t map is its actual time-minus-t map on the
full complement of the critical-trajectory set.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

/-- The actual root-oriented time map has its negative-time map as inverse. -/
theorem nativeRootHorizontalTimeMap_bijective
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (β : X → ℂ → ℂ) (hβ : IsGlobalQuadraticRoot R q β) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ t : ℝ, Function.Bijective (nativeRootHorizontalTimeMap R q β t) := by
  let := R.toRiemannAtlas.toChartedSpace
  intro t
  let Ω := {p : X // p ∉ s26v_E (q : X → ℂ → ℂ)}
  let F : ℝ → Ω → Ω := nativeRootHorizontalTimeMap R q β
  have hact := nativeRootHorizontalTimeMap_action R q β hβ
  have hinv (s : ℝ) (p : Ω) : F (-s) (F s p) = p := by
    calc
      F (-s) (F s p) = F (-s + s) p := (hact.2 (-s) s p).symm
      _ = p := by rw [neg_add_cancel]; exact hact.1 p
  constructor
  · intro x y hxy
    have h := congrArg (F (-t)) hxy
    change F (-t) (F t x) = F (-t) (F t y) at h
    simpa only [hinv t] using h
  · intro y
    exact ⟨F (-t) y, by simpa only [neg_neg] using hinv (-t) y⟩

end LowDimensionalTopology.Geometry.Teichmuller
