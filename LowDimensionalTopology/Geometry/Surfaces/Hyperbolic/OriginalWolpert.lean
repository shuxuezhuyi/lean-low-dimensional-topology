module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalHyperbolicDeckGeodesic
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.HyperbolicProducts

/-!
# Wolpert's bound for actual original closed geodesics

The actual image loop has an actual original-atlas closed geodesic in its
own free class. Both bounds retain the full original period, the same
surface models and the same quasiconformal constant. No compactness is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane unitInterval MatrixGroups ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Mobius

private theorem original_length_eq_freeLength
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M) :
    q.length = LiZhongQC.freeHomotopyLength M.halfPlaneCover q.toLoop := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, _hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨A, hAΓ, hcov, _hA, ht⟩ := q.exists_actual_hyperbolic_cover hp
  have hh : LiZhongQC.IsHyperbolic A := by
    unfold LiZhongQC.IsHyperbolic LiZhongQC.slTrace
    change 2 < |A.val 0 0 + A.val 1 1|
    rw [← Matrix.trace_fin_two]
    nlinarith [sq_abs (Matrix.trace A.val), abs_nonneg (Matrix.trace A.val)]
  have hfree := LiZhongQC.s30a_len_hyp hp hAΓ hh hcov
  rw [liZhong_translationLength_eq_native A hh] at hfree
  exact (q.length_eq_translationLength_of_covers hp A hAΓ ht hcov).trans hfree.symm

universe u

/-- Wolpert's inequalities for an actual original closed geodesic and an
actual `K`-quasiconformal map, with a genuine target geodesic representative.
This includes arbitrary full traversals, hence in particular simple geodesics. -/
theorem OriginalClosedGeodesic.exists_wolpert_image
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y}
    {M₁ : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M₁)
    (M₂ : HyperbolicSurfaceModel S) (f : X ≃ₜ Y) {K : ℝ}
    (hf : let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsKQCRS f K) :
    ∃ r : OriginalClosedGeodesic M₂,
      LiZhongQC.FreelyHomotopic ⟨f q.toLoop.1, q.toLoop.2.map f.continuous⟩ r.toLoop ∧
      q.length.toReal / K ≤ r.length.toReal ∧
      r.length.toReal ≤ K * q.length.toReal := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.t2Space
  let := R.connectedSpace
  let := R.toRiemannAtlas.isManifold
  let := S.t2Space
  let := S.connectedSpace
  let := S.toRiemannAtlas.isManifold
  obtain ⟨Γ₁, _hΓ₁, hp₁⟩ := M₁.exists_halfPlaneCover_uniformization
  obtain ⟨Γ₂, _hΓ₂, hp₂⟩ := M₂.exists_halfPlaneCover_uniformization
  let β : LiZhongQC.Loop Y := ⟨f q.toLoop.1, q.toLoop.2.map f.continuous⟩
  have hW := LiZhongQC.lemma30_3_wolpert hp₁ hp₂ f hf q.toLoop
  rw [← original_length_eq_freeLength q] at hW
  change q.length / ENNReal.ofReal K ≤ LiZhongQC.freeHomotopyLength M₂.halfPlaneCover β ∧
    LiZhongQC.freeHomotopyLength M₂.halfPlaneCover β ≤ ENNReal.ofReal K * q.length at hW
  have hq := ENNReal.toReal_pos_iff.mp q.length_toReal_pos
  have hβ : 0 < LiZhongQC.freeHomotopyLength M₂.halfPlaneCover β :=
    (ENNReal.div_pos hq.1.ne' ENNReal.ofReal_ne_top).trans_le hW.1
  obtain ⟨A, hAΓ, hcov⟩ := LiZhongQC.s30a_exists_covers hp₂ β
  have hh : LiZhongQC.IsHyperbolic A := by
    rcases LiZhongQC.s30a_classify hp₂ (LiZhongQC.s27g_actsFreely hp₂) hAΓ hcov with hz | hh
    · exact False.elim (hβ.ne' hz.1)
    · exact hh.1
  have ht : 4 < (Matrix.trace A.val) ^ 2 := by
    unfold LiZhongQC.IsHyperbolic LiZhongQC.slTrace at hh
    change 2 < |A.val 0 0 + A.val 1 1| at hh
    rw [← Matrix.trace_fin_two] at hh
    nlinarith [sq_abs (Matrix.trace A.val), abs_nonneg (Matrix.trace A.val)]
  have hA : realSLMobius A ≠ 1 := by
    intro he
    have hs := hSL_trace_sq_of_projection_one A he
    linarith
  obtain ⟨r, hrcov, _himage, _hunique⟩ :=
    M₂.exists_original_closed_geodesic_of_hyperbolic_deck A
      (LiZhongQC.s30a_p_smul hp₂ hAΓ) hA ht
  have hfree : LiZhongQC.FreelyHomotopic β r.toLoop :=
    LiZhongQC.s30a_fh_of_conj hp₂ hAΓ Γ₂.one_mem (fun _ => by simp) hcov hrcov
  have hrlen : r.length = LiZhongQC.freeHomotopyLength M₂.halfPlaneCover β :=
    (original_length_eq_freeLength r).trans (LiZhongQC.s30b_fhl_congr _ hfree).symm
  rw [← hrlen] at hW
  have hr := ENNReal.toReal_pos_iff.mp r.length_toReal_pos
  have hKpos : 0 < K := lt_of_lt_of_le one_pos hf.1
  refine ⟨r, hfree, ?_, ?_⟩
  · simpa only [ENNReal.toReal_div, ENNReal.toReal_ofReal hKpos.le] using
      ENNReal.toReal_mono hr.2.ne hW.1
  · simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hKpos.le] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hq.2.ne) hW.2

/-- The same two-sided bound at the literal maximal dilatation of the original
map and atlases. -/
theorem OriginalClosedGeodesic.exists_wolpert_image_maxDilatation
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {R : RiemannSurface X} {S : RiemannSurface Y}
    {M₁ : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M₁)
    (M₂ : HyperbolicSurfaceModel S) (f : X ≃ₜ Y)
    (hf : let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsQCRS f) :
    let := R.toRiemannAtlas.toChartedSpace
    let := S.toRiemannAtlas.toChartedSpace
    ∃ r : OriginalClosedGeodesic M₂,
      LiZhongQC.FreelyHomotopic ⟨f q.toLoop.1, q.toLoop.2.map f.continuous⟩ r.toLoop ∧
      q.length.toReal / (LiZhongQC.maxDilatationRS f).toReal ≤ r.length.toReal ∧
      r.length.toReal ≤ (LiZhongQC.maxDilatationRS f).toReal * q.length.toReal := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.connectedSpace
  exact q.exists_wolpert_image M₂ f (LiZhongQC.s29_m_isKQCRS_maxDil hf)

end LowDimensionalTopology.Geometry.Surfaces
