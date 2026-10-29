module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersBasePoint
public import LowDimensionalTopology.Geometry.Teichmuller.BersWeightedCoordinates
public import LowDimensionalTopology.Geometry.Teichmuller.BersAutomorphicDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.GammaAtlasRealization

/-!
# The actual compatible-coefficient projection to the native Teichmuller quotient

The map is defined using the actual coefficient class and the chosen normalized
uniformization equivalence. Its value is proved to be the genuine marked QC
realization with that lifted coefficient. It is not defined by inverting a
coordinate chart. The existing Bers coordinates then give its exact coordinate
formula and identify the zero coefficient with the original identity marking.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hPresentation : Unproved.HandleGroupPresentation g)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : UpperHalfPlane → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

/-- The actual group-coefficient quotient projected to the actual native
marked-surface quotient using the normalized-lift source equivalence. -/
def coefficientProjectionBall (μ : GammaMeasurableBeltrami.Ball Γ) :
    TeichmullerSpace.{u, u} R :=
  (gammaEquiv R hg hgenus hPresentation hΓ hfree hp).symm
    (Quotient.mk _ (GammaMeasurableBeltrami.toSourceGamma μ))

/-- Retain that actual projection near zero, extending by the original base
point outside its coefficient ball for the derivative statement below. -/
def coefficientProjection (μ : GammaMeasurableBeltrami.Space Γ) :
    TeichmullerSpace.{u, u} R := by
  classical
  exact if hμ : ‖μ‖ < 1 then
    coefficientProjectionBall R hg hgenus hPresentation hΓ hfree hp
      ⟨μ, by simpa only [Metric.mem_ball, dist_zero_right] using hμ⟩
  else basePoint R

/-- Forgetting smooth native representatives recovers exactly the actual
normalized group-to-marked-surface equivalence on the original coefficient class. -/
theorem toSource_coefficientProjectionBall (μ : GammaMeasurableBeltrami.Ball Γ) :
    let := R.toRiemannAtlas.toChartedSpace
    toSource R (coefficientProjectionBall R hg hgenus hPresentation hΓ hfree hp μ) =
      sourceGammaEquiv R hg hgenus hPresentation hΓ hfree hp
        (Quotient.mk _ (GammaMeasurableBeltrami.toSourceGamma μ)) := by
  let := R.toRiemannAtlas.toChartedSpace
  change sourceEquiv R hg hgenus hPresentation
    ((sourceEquiv R hg hgenus hPresentation).symm
      (sourceGammaEquiv R hg hgenus hPresentation hΓ hfree hp
        (Quotient.mk _ (GammaMeasurableBeltrami.toSourceGamma μ)))) = _
  exact (sourceEquiv R hg hgenus hPresentation).apply_symm_apply _

/-- Any genuine marked QC realization with the given lifted coefficient
represents this actual projection. Equality follows from the chosen normalized
lift characterization and a.e. uniqueness of normalized solutions. -/
theorem coefficientProjectionBall_realization
    (μ : GammaMeasurableBeltrami.Ball Γ)
    (m : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.MarkedRS X)
    (hm : let := R.toRiemannAtlas.toChartedSpace;
      LiZhongQC.s27u_liftCoeff p m.marking =ᵐ[volume.restrict LiZhongQC.upperHalf]
        GammaMeasurableBeltrami.planeRepresentative μ.val.val) :
    let := R.toRiemannAtlas.toChartedSpace
    toSource R (coefficientProjectionBall R hg hgenus hPresentation hΓ hfree hp μ) =
      Quot.mk _ m := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  rw [toSource_coefficientProjectionBall]
  have he := Classical.choose_spec (LiZhongQC.teichGamma_equiv_teichSpace hg
    (R.sourceHasGenus hgenus hPresentation) hΓ hfree hp)
  apply (he (GammaMeasurableBeltrami.toSourceGamma μ) m).mpr
  obtain ⟨Γ', p', F, G, hp', hN, _, hG⟩ := LiZhongQC.s27u_exists_uniformization hp m
  obtain ⟨k, hk0, hk1, hmk⟩ := LiZhongQC.s27v_liftCoeff_bound hp m
  have hs := LiZhongQC.s27u_fSym_congr_ae hk0 hk1 hmk
    (norm_nonneg μ.val.val) (GammaMeasurableBeltrami.Ball.norm_lt_one μ)
    (GammaMeasurableBeltrami.planeRepresentative_isBeltramiCoeff μ.val.val) hm
  refine ⟨Γ', p', F, G, hp', hN, fun x => ?_⟩
  rw [hG x, hs]; rfl

/-- The original normalized uniformization supplies an actual marked QC
representative, with the coefficient's own bound, of this projection value. -/
theorem exists_coefficientProjectionBall_realization
    (μ : GammaMeasurableBeltrami.Ball Γ) :
    let := R.toRiemannAtlas.toChartedSpace
    ∃ m : LiZhongQC.MarkedRS X,
      LiZhongQC.IsKQCRS m.marking ((1 + ‖μ.val.val‖) / (1 - ‖μ.val.val‖)) ∧
      (LiZhongQC.s27u_liftCoeff p m.marking =ᵐ[volume.restrict LiZhongQC.upperHalf]
        GammaMeasurableBeltrami.planeRepresentative μ.val.val) ∧
      toSource R (coefficientProjectionBall R hg hgenus hPresentation hΓ hfree hp μ) =
        Quot.mk _ m := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨m, hK, hm, _⟩ :=
    GammaMeasurableBeltrami.exists_marked_atlas_tensor_normBound R hp μ
  exact ⟨m, hK, hm,
    coefficientProjectionBall_realization R hg hgenus hPresentation hΓ hfree hp μ m hm⟩

/-- The actual native projection has exactly the existing Bers coordinates of
the native weighted projection, with the original coefficient unchanged. -/
theorem coefficientProjectionBall_coordinates (μ : GammaMeasurableBeltrami.Ball Γ) :
    bersCoordinates R hg hgenus hPresentation hΓ hfree hp
        (coefficientProjectionBall R hg hgenus hPresentation hΓ hfree hp μ) =
      weightedLinearBersCoordinates R hg hgenus hPresentation hΓ hp
        (BersWeighted.automorphicProjection hΓ μ.val) := by
  have hclass : gammaEquiv R hg hgenus hPresentation hΓ hfree hp
      (coefficientProjectionBall R hg hgenus hPresentation hΓ hfree hp μ) =
      (Quotient.mk _ (GammaMeasurableBeltrami.toSourceGamma μ) : LiZhongQC.TeichGamma Γ) :=
    (gammaEquiv R hg hgenus hPresentation hΓ hfree hp).apply_symm_apply
      (Quotient.mk _ (GammaMeasurableBeltrami.toSourceGamma μ) : LiZhongQC.TeichGamma Γ)
  rw [weightedLinearBersCoordinates_apply]
  unfold bersCoordinates
  apply congrArg (linearBersCoordinates R hg hgenus hPresentation hΓ hp)
  apply Subtype.ext
  change LiZhongQC.bersMapGamma Γ
      (gammaEquiv R hg hgenus hPresentation hΓ hfree hp
        (coefficientProjectionBall R hg hgenus hPresentation hΓ hfree hp μ)) =
    ((BersWeighted.automorphicProjection hΓ μ.val).toSource : ℂ → ℂ)
  rw [hclass]
  change GammaMeasurableBeltrami.bersProjection μ =
    BersWeighted.decode (BersWeighted.projection μ.val)
  simp only [BersWeighted.projection, dite_eq_left (GammaMeasurableBeltrami.Ball.norm_lt_one μ),
    BersWeighted.decode_projectionValue]

/-- The extended native projection still has the exact weighted Bers coordinate map. -/
theorem coefficientProjection_coordinates (μ : GammaMeasurableBeltrami.Space Γ) :
    bersCoordinates R hg hgenus hPresentation hΓ hfree hp
        (coefficientProjection R hg hgenus hPresentation hΓ hfree hp μ) =
      weightedLinearBersCoordinates R hg hgenus hPresentation hΓ hp
        (BersWeighted.automorphicProjection hΓ μ) := by
  classical
  unfold coefficientProjection
  split_ifs with hμ
  · exact coefficientProjectionBall_coordinates R hg hgenus hPresentation hΓ hfree hp _
  · have hz : BersWeighted.automorphicProjection hΓ μ = 0 := by
      apply Subtype.ext
      change BersWeighted.projection μ = 0
      simp only [BersWeighted.projection, dite_eq_right hμ]
    rw [hz, ContinuousLinearEquiv.map_zero
      (weightedLinearBersCoordinates R hg hgenus hPresentation hΓ hp),
      bersCoordinates_basePoint R hg hgenus hPresentation hΓ hfree hp]

/-- The zero coefficient is the original surface with the identity marking. -/
theorem coefficientProjection_zero :
    coefficientProjection R hg hgenus hPresentation hΓ hfree hp
      (0 : GammaMeasurableBeltrami.Space Γ) = basePoint R := by
  apply bersCoordinates_injective R hg hgenus hPresentation hΓ hfree hp
  rw [coefficientProjection_coordinates]
  have hz : BersWeighted.automorphicProjection hΓ (0 : GammaMeasurableBeltrami.Space Γ) = 0 :=
    Subtype.ext BersWeighted.projection_zero
  rw [hz, ContinuousLinearEquiv.map_zero
    (weightedLinearBersCoordinates R hg hgenus hPresentation hΓ hp),
    bersCoordinates_basePoint R hg hgenus hPresentation hΓ hfree hp]

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
