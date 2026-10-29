module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.HalfPlaneUniformization
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.CoveredLoops

/-!
# Actual closed axis minimizers on the original modeled surface

The projected native C1 curve and the actual source loop have the same complete
parametrization. Their literal lengths coincide, and this same curve attains
the source free-homotopy length minimum. The given matrix is not replaced by a
primitive generator or by the entire axis stabilizer.
-/

public section
noncomputable section

open Set
open scoped UpperHalfPlane unitInterval MatrixGroups ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Mobius

/-- A genuine native C1 closed curve on the given surface is the projected actual
axis interval, realizes the source loop and free-class minima, and satisfies the
trace formula for its original covering matrix. -/
theorem HyperbolicSurfaceModel.exists_closed_axis_c1_minimizer
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hdeck : ∀ z : ℍ, M.halfPlaneCover (A • z) = M.halfPlaneCover z)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2) :
    let := R.toRiemannAtlas.toChartedSpace
    ∃ (α : LiZhongQC.Loop X) (q : HyperbolicSurfaceC1CurvePiece M) (d : C1CurvePiece),
      LiZhongQC.Covers M.halfPlaneCover A α ∧
      d.a = 0 ∧ d.b = 1 ∧
      (∀ t : ℝ, d.curve t ∈ (hHyperbolicAxis A hA ht).carrier) ∧
      d.curve 1 = A • d.curve 0 ∧
      (∀ t : I, q.curve t = M.halfPlaneCover (d.curve t)) ∧
      (∀ t : I, q.curve t = α.2 t) ∧ q.curve 1 = q.curve 0 ∧
      q.length = hTranslationLength (hSLIsometry A) ∧
      LiZhongQC.poincareLengthLoop M.halfPlaneCover α = ENNReal.ofReal q.length ∧
      LiZhongQC.freeHomotopyLength M.halfPlaneCover α = ENNReal.ofReal q.length ∧
      Real.cosh (q.length / 2) ^ 2 = (Matrix.trace A.val) ^ 2 / 4 := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨α, hcov, hloop, hfree, _htrace, c, _hK, him, hproj, _hcLen,
    τ, _hτ, hc0, hc1, d, ha, hb, hcd, haxis, hdlen⟩ :=
    exists_covered_loop_realizing_translation_length hp A ((hΓ A).2 hdeck) hA ht
  let q := M.projectDiscC1Piece d.toDisc ha hb
  have hqlen : q.length = hTranslationLength (hSLIsometry A) :=
    (M.projectDiscC1Piece_length d.toDisc ha hb).trans (d.toDisc_length.trans hdlen)
  have hd0 : d.curve 0 = τ := UpperHalfPlane.ext ((hcd 0).symm.trans hc0)
  have hd1 : d.curve 1 = A • τ := UpperHalfPlane.ext ((hcd 1).symm.trans hc1)
  have hdperiod : d.curve 1 = A • d.curve 0 :=
    hd1.trans (congrArg (fun z : ℍ => A • z) hd0.symm)
  have hcoerce (t : ℝ) (htI : t ∈ Icc (0 : ℝ) 1) :
      (⟨c t, him t htI⟩ : ℍ) = d.curve t := UpperHalfPlane.ext (hcd t)
  have hqpoint (t : I) : q.curve t = α.2 t := by
    change M.halfPlaneCover (d.curve t) = α.2 t
    have h := hproj t t.property
    rw [hcoerce t t.property, Path.extend_apply α.2 t.property] at h
    exact h
  have hclosed : q.curve 1 = q.curve 0 := by
    calc
      q.curve 1 = α.2 1 := hqpoint 1
      _ = α.1 := α.2.target
      _ = α.2 0 := α.2.source.symm
      _ = q.curve 0 := (hqpoint 0).symm
  refine ⟨α, q, d, hcov, ha, hb, haxis, hdperiod, fun _ => rfl,
    hqpoint, hclosed, hqlen, ?_, ?_, ?_⟩
  · rw [hqlen]
    exact hloop
  · rw [hqlen]
    exact hfree
  · rw [hqlen]
    exact hHyperbolic_translation_trace A hA ht

end LowDimensionalTopology.Geometry.Surfaces
