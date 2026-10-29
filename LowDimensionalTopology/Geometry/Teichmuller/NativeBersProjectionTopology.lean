module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeNonzeroBersDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.NativeCoefficientProjection
public import LowDimensionalTopology.Geometry.Teichmuller.NativeGammaSourceRealization
public import LowDimensionalTopology.Geometry.Teichmuller.ComplexBersMetric

/-!
# The original full coefficient ball and Bers projection topologies

The domain is the entire compatible measurable L-infinity ball. The original
marked-surface quotient carries its proved QC metric. Transporting that same
metric through the actual normalized-lift equivalence gives twice the book
half-log metric on the actual group quotient. Its equivalence relation is
proved to be precisely equality of the original lower-half-plane maps.
No topology comparison or smoothing hypothesis is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami NormalizedCoefficientTransport

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

local notation "hP" => canonicalHandleGroupPresentation g
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "W" => weightedLinearBersCoordinates R hg hgenus hP hΓ hp
local notation "E" => gammaEquiv R hg hgenus hP hΓ hfree hp
local notation "β" => coefficientProjectionBall R hg hgenus hP hΓ hfree hp

include R hg hgenus hp in
/-- The actual Bers projection is continuous at every point of its entire native ball. -/
theorem continuousOn_automorphicProjection :
    ContinuousOn (BersWeighted.automorphicProjection hΓ) (Metric.ball (0 : Space Γ) 1) := by
  let : ContinuousAdd (BersWeighted.Automorphic Γ) :=
    (Submodule.isTopologicalAddGroup (BersWeighted.automorphicSubmodule Γ)).toContinuousAdd
  intro μ hμ
  exact (hasFDerivAt_automorphicProjection_nonzero R hp hg hgenus hΓ
    (⟨μ, hμ⟩ : Ball Γ)).continuousAt.continuousWithinAt

include R hg hgenus hp in
/-- Continuity uses the original essential norm and the original weighted supremum norm. -/
theorem continuous_automorphicProjectionBall :
    Continuous (fun μ : Ball Γ => BersWeighted.automorphicProjection hΓ μ.val) := by
  exact (continuousOn_automorphicProjection R hg hgenus hΓ hp).comp_continuous
    continuous_subtype_val (fun μ => μ.property)

/-- The actual original Bers embedding, in the faithful weighted function space. -/
def weightedBersEmbedding (a : TeichmullerSpace.{u, u} R) : BersWeighted.Automorphic Γ :=
  (W).symm (BC a)

/-- Every original normalized Schwarzian value is retained literally. -/
theorem weightedBersEmbedding_toSource (a : TeichmullerSpace.{u, u} R) :
    ((weightedBersEmbedding R hg hgenus hΓ hfree hp a).toSource : ℂ → ℂ) =
      LiZhongQC.bersMapGamma Γ (E a) := by
  have he : (weightedBersEmbedding R hg hgenus hΓ hfree hp a).toSource =
      (⟨LiZhongQC.bersMapGamma Γ (E a), (LiZhongQC.bersMapGamma_mem hΓ _).1⟩ :
        LiZhongQC.automorphicQD Γ) := by
    apply (linearBersCoordinates R hg hgenus hP hΓ hp).injective
    rw [← weightedLinearBersCoordinates_apply]
    exact (W).apply_symm_apply (BC a)
  exact congrArg (fun φ : LiZhongQC.automorphicQD Γ => (φ : ℂ → ℂ)) he

/-- The two genuine original projections commute with the literal Bers embedding. -/
theorem weightedBersEmbedding_coefficientProjectionBall (μ : Ball Γ) :
    weightedBersEmbedding R hg hgenus hΓ hfree hp (β μ) =
      BersWeighted.automorphicProjection hΓ μ.val := by
  apply (W).injective
  change W ((W).symm (BC (β μ))) = _
  rw [(W).apply_symm_apply]
  exact coefficientProjectionBall_coordinates R hg hgenus hP hΓ hfree hp μ

/-- Bers embedding continuity holds for the actual original QC metric topology. -/
theorem continuous_weightedBersEmbedding_fromQC :
    letI : MetricSpace (TeichmullerSpace.{u, u} R) := fromQCMetricSpace R hg hgenus hP
    Continuous (weightedBersEmbedding R hg hgenus hΓ hfree hp) := by
  let : MetricSpace (TeichmullerSpace.{u, u} R) := fromQCMetricSpace R hg hgenus hP
  exact (W).symm.continuous.comp
    (continuous_bersCoordinates_fromQC R hg hgenus hP hΓ hfree hp)

/-- The original full-ball marked-surface projection is continuous in the QC metric. -/
theorem continuous_coefficientProjectionBall_fromQC :
    letI : MetricSpace (TeichmullerSpace.{u, u} R) := fromQCMetricSpace R hg hgenus hP
    Continuous β := by
  let : MetricSpace (TeichmullerSpace.{u, u} R) := fromQCMetricSpace R hg hgenus hP
  let H := fromQCBersCoordinateHomeomorph R hg hgenus hP hΓ hfree hp
  let C : Ball Γ → range BC := fun μ => ⟨BC (β μ), mem_range_self (β μ)⟩
  have hBC : Continuous (fun μ : Ball Γ => BC (β μ)) := by
    have hc := (W).continuous.comp (continuous_automorphicProjectionBall R hg hgenus hΓ hp)
    apply hc.congr
    intro μ
    exact (coefficientProjectionBall_coordinates R hg hgenus hP hΓ hfree hp μ).symm
  have hC : Continuous C := hBC.subtype_mk (fun μ => mem_range_self (β μ))
  have he : (fun μ : Ball Γ => H.symm (C μ)) = β := by
    funext μ
    change H.symm (H (β μ)) = β μ
    exact H.symm_apply_apply (β μ)
  rw [← he]
  exact H.symm.continuous.comp hC

/-- Every original marked-surface class has a representative in the entire coefficient ball. -/
theorem coefficientProjectionBall_surjective : Function.Surjective β := by
  intro a
  let μ : LiZhongQC.BeltramiGamma Γ := Quotient.out (E a)
  let ν : Ball Γ := fromSourceGamma μ
  have hbers : LiZhongQC.bersMapGamma Γ (Quotient.mk _ (toSourceGamma ν)) =
      LiZhongQC.bersMapGamma Γ (E a) := by
    rw [LiZhongQC.bg_bersMapGamma_eq rfl,
      LiZhongQC.bg_bersMapGamma_eq (Quotient.out_eq (E a))]
    exact sourceBers_congr_ae (toSourceGamma ν) μ (toSourceGamma_fromSourceGamma_ae μ)
  have hq := (LiZhongQC.bersMapGamma_injective hΓ) hbers
  refine ⟨ν, ?_⟩
  change (E).symm (Quotient.mk _ (toSourceGamma ν)) = a
  rw [hq, (E).symm_apply_apply]

/-- The actual full-ball coefficient projection onto the group boundary model. -/
def gammaCoefficientProjectionBall (μ : Ball Γ) : LiZhongQC.TeichGamma Γ :=
  Quotient.mk _ (toSourceGamma μ)

/-- Its quotient relation is exactly equality of the original normalized lower maps. -/
theorem gammaCoefficientProjectionBall_eq_iff_lower (μ ν : Ball Γ) :
    gammaCoefficientProjectionBall (Γ := Γ) μ = gammaCoefficientProjectionBall ν ↔
      EqOn (LiZhongQC.normalizedSolution (toSourceGamma μ).val.val)
        (LiZhongQC.normalizedSolution (toSourceGamma ν).val.val) LiZhongQC.lowerHalf := by
  constructor
  · intro h
    exact (LiZhongQC.fMu_lower_model _ _).mpr
      (LiZhongQC.bg_l_forward (Quotient.exact h))
  · intro h
    exact Quotient.sound (LiZhongQC.bg_l_backward
      ((LiZhongQC.fMu_lower_model _ _).mp h))

/-- The genuine original QC metric transported through the actual normalized-lift equivalence. -/
@[instance_reducible] def gammaQCMetricSpace : MetricSpace (LiZhongQC.TeichGamma Γ) := by
  letI : MetricSpace (TeichmullerSpace.{u, u} R) := fromQCMetricSpace R hg hgenus hP
  exact MetricSpace.induced (E).symm (E).symm.injective inferInstance

/-- This explicit metric is exactly twice the book half-log distance, on every pair. -/
theorem gammaQCMetricSpace_dist (a b : LiZhongQC.TeichGamma Γ) :
    letI := gammaQCMetricSpace R hg hgenus hΓ hfree hp
    dist a b = 2 * LiZhongQC.teichDistanceGamma a b := by
  change fromQCDistance R ((E).symm a) ((E).symm b) = _
  rw [fromQCDistance_eq_two_mul_gamma R hg hgenus hP hΓ hfree hp,
    (E).apply_symm_apply, (E).apply_symm_apply]

/-- The full-ball boundary projection is continuous for the original book topology. -/
theorem continuous_gammaCoefficientProjectionBall :
    letI := gammaQCMetricSpace R hg hgenus hΓ hfree hp
    Continuous (gammaCoefficientProjectionBall (Γ := Γ)) := by
  let : MetricSpace (TeichmullerSpace.{u, u} R) := fromQCMetricSpace R hg hgenus hP
  let := gammaQCMetricSpace R hg hgenus hΓ hfree hp
  apply continuous_induced_rng.mpr
  exact continuous_coefficientProjectionBall_fromQC R hg hgenus hΓ hfree hp

include R hg hgenus hΓ hfree hp in
/-- Every actual boundary class is represented by an original compatible measurable coefficient. -/
theorem gammaCoefficientProjectionBall_surjective :
    Function.Surjective (gammaCoefficientProjectionBall (Γ := Γ)) := by
  intro a
  obtain ⟨μ, hμ⟩ := coefficientProjectionBall_surjective R hg hgenus hΓ hfree hp ((E).symm a)
  refine ⟨μ, ?_⟩
  have he := congrArg E hμ
  change E ((E).symm (gammaCoefficientProjectionBall μ)) = E ((E).symm a) at he
  simpa only [(E).apply_symm_apply] using he

/-- The full coefficient-to-boundary projection is a continuous surjection in the book topology. -/
theorem gammaCoefficientProjectionBall_continuous_surjective :
    letI := gammaQCMetricSpace R hg hgenus hΓ hfree hp
    Continuous (gammaCoefficientProjectionBall (Γ := Γ)) ∧
      Function.Surjective (gammaCoefficientProjectionBall (Γ := Γ)) := by
  exact ⟨continuous_gammaCoefficientProjectionBall R hg hgenus hΓ hfree hp,
    gammaCoefficientProjectionBall_surjective R hg hgenus hΓ hfree hp⟩

/-- Both the actual full-ball Bers projection and the original Bers embedding are continuous. -/
theorem bersProjection_embedding_continuous_fromQC :
    letI : MetricSpace (TeichmullerSpace.{u, u} R) := fromQCMetricSpace R hg hgenus hP
    Continuous (fun μ : Ball Γ => BersWeighted.automorphicProjection hΓ μ.val) ∧
      Continuous (weightedBersEmbedding R hg hgenus hΓ hfree hp) := by
  exact ⟨continuous_automorphicProjectionBall R hg hgenus hΓ hp,
    continuous_weightedBersEmbedding_fromQC R hg hgenus hΓ hfree hp⟩

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
