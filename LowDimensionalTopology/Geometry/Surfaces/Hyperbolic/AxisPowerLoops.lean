module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.QuotientMetric
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.AxisPowerC1Piece

/-!
# Actual projected axis loops on the original hyperbolic surface

Both the surface carrier and its given model projection are retained. Projection
of an actual power interval preserves its C1 integral and actual deck period.
-/

public section
noncomputable section

open Set
open scoped UpperHalfPlane unitInterval MatrixGroups

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Mobius

/-- The given model's original disc cover, expressed in half-plane coordinates. -/
@[expose] def HyperbolicSurfaceModel.halfPlaneCover
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) : ℍ → X :=
  M.discCover ∘ discFiniteHomeomorph.symm ∘ halfPlaneToDisc

theorem HyperbolicSurfaceModel.halfPlaneCover_covering
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) : IsCoveringMap M.halfPlaneCover :=
  M.discCover_covering.comp_homeomorph (cayleyHomeomorph.trans discFiniteHomeomorph.symm)

theorem HyperbolicSurfaceModel.halfPlaneCover_surjective
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) : Function.Surjective M.halfPlaneCover :=
  M.discCover_surjective.comp
    (discFiniteHomeomorph.symm.surjective.comp cayleyHomeomorph.surjective)

/-- Project an actual disc C1 piece using the original model, with no change to
its parametrization or covering lift. -/
@[expose] def HyperbolicSurfaceModel.projectDiscC1Piece
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (c : DiscC1CurvePiece)
    (ha : c.a = 0) (hb : c.b = 1) : HyperbolicSurfaceC1CurvePiece M where
  curve := ⟨fun t => M.discCover (discFiniteHomeomorph.symm (c.curve t)),
    M.discCover_covering.continuous.comp
      (discFiniteHomeomorph.symm.continuous.comp
        (c.continuous_curve.comp_continuous continuous_subtype_val
          (fun t : I => by simpa only [ha, hb] using t.property)))⟩
  hasC1Lift := by
    refine ⟨c, ha, hb, ?_⟩
    intro t
    change discQuotientProjection M.invariant (c.curve t) =
      M.homeomorph (M.homeomorph.symm (discQuotientProjection M.invariant (c.curve t)))
    exact (M.homeomorph.apply_symm_apply _).symm

theorem HyperbolicSurfaceModel.projectDiscC1Piece_length
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (c : DiscC1CurvePiece)
    (ha : c.a = 0) (hb : c.b = 1) :
    (M.projectDiscC1Piece c ha hb).length = c.length := by
  apply HyperbolicSurfaceC1CurvePiece.length_eq_of_lift _ c ha hb
  intro t
  change discQuotientProjection M.invariant (c.curve t) =
    M.homeomorph (M.homeomorph.symm (discQuotientProjection M.invariant (c.curve t)))
  exact (M.homeomorph.apply_symm_apply _).symm

/-- Actual deck periods produce actual C1 loops of the prescribed power length
on the original surface. No primitive generator replaces the given matrix. -/
theorem HyperbolicSurfaceModel.exists_projected_axis_power_loop
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hdeck : ∀ z : ℍ, M.halfPlaneCover (A • z) = M.halfPlaneCover z)
    (hA : realSLMobius A ≠ 1) (ht : 4 < (Matrix.trace A.val) ^ 2) (n : ℕ) :
    ∃ (c : C1CurvePiece) (q : HyperbolicSurfaceC1CurvePiece M),
      c.a = 0 ∧ c.b = 1 ∧
      (∀ t : ℝ, c.curve t ∈ (hHyperbolicAxis A hA ht).carrier) ∧
      c.curve 1 = A ^ n • c.curve 0 ∧
      (∀ t : I, q.curve t = M.halfPlaneCover (c.curve t)) ∧
      q.curve 1 = q.curve 0 ∧
      q.length = (n : ℝ) * hTranslationLength (hSLIsometry A) := by
  obtain ⟨c, ha, hb, haxis, hperiod, hlen⟩ := exists_axis_power_c1_piece A hA ht n
  let q := M.projectDiscC1Piece c.toDisc ha hb
  have hpowers (m : ℕ) (z : ℍ) :
      M.halfPlaneCover (A ^ m • z) = M.halfPlaneCover z := by
    induction m with
    | zero => simp only [pow_zero, one_smul]
    | succ m ih => rw [pow_succ', mul_smul, hdeck, ih]
  refine ⟨c, q, ha, hb, haxis, hperiod, fun _ => rfl, ?_, ?_⟩
  · change M.halfPlaneCover (c.curve 1) = M.halfPlaneCover (c.curve 0)
    rw [hperiod, hpowers]
  · exact (M.projectDiscC1Piece_length c.toDisc ha hb).trans
      (c.toDisc_length.trans hlen)

end LowDimensionalTopology.Geometry.Surfaces
