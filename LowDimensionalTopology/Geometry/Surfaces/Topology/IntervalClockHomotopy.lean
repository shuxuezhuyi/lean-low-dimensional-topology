module

public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity
public import Mathlib.Analysis.Convex.Basic

/-! # Actual free homotopies between interval-clock parametrizations -/

public section
noncomputable section
open Set
open scoped unitInterval

namespace LowDimensionalTopology.Geometry.Surfaces

/-- Two actual loops obtained from the same continuous interval curve by clocks
with the same endpoints are freely homotopic. Convex interpolation of the actual
clocks supplies the homotopy; no injectivity, strict monotonicity or positive
interval length is required. -/
theorem freelyHomotopic_of_interval_clocks
    {X : Type*} [TopologicalSpace X] {L : ℝ}
    (F : C(Icc (0 : ℝ) L, X)) (u v : C(I, Icc (0 : ℝ) L))
    (hv0 : v 0 = u 0) (hv1 : v 1 = u 1)
    {α β : LiZhongQC.Loop X}
    (hα : ∀ t : I, α.2 t = F (u t)) (hβ : ∀ t : I, β.2 t = F (v t)) :
    LiZhongQC.FreelyHomotopic α β := by
  let W : I × I → Icc (0 : ℝ) L := fun st =>
    ⟨AffineMap.lineMap (u st.2 : ℝ) (v st.2 : ℝ) (st.1 : ℝ),
      (convex_Icc (0 : ℝ) L).lineMap_mem (u st.2).property (v st.2).property st.1.property⟩
  have hW : Continuous W := by
    dsimp only [W]
    simp only [AffineMap.lineMap_apply]
    fun_prop
  have h0 (t : I) : W (0, t) = u t := by
    apply Subtype.ext
    exact AffineMap.lineMap_apply_zero (u t : ℝ) (v t : ℝ)
  have h1 (t : I) : W (1, t) = v t := by
    apply Subtype.ext
    exact AffineMap.lineMap_apply_one (u t : ℝ) (v t : ℝ)
  have ht0 (s : I) : W (s, 0) = u 0 := by
    apply Subtype.ext
    simp only [W, hv0, AffineMap.lineMap_same_apply]
  have ht1 (s : I) : W (s, 1) = u 1 := by
    apply Subtype.ext
    simp only [W, hv1, AffineMap.lineMap_same_apply]
  let H : C(I × I, X) := F.comp ⟨W, hW⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro t
    change F (W (0, t)) = α.2 t
    rw [h0]
    exact (hα t).symm
  · intro t
    change F (W (1, t)) = β.2 t
    rw [h1]
    exact (hβ t).symm
  · intro s
    change F (W (s, 0)) = F (W (s, 1))
    rw [ht0, ht1]
    exact (hα 0).symm.trans (α.2.source.trans (α.2.target.symm.trans (hα 1)))

end LowDimensionalTopology.Geometry.Surfaces
