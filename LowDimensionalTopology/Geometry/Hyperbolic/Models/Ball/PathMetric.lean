/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.UnitBall.Invariants
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.DensityMetric
/-!
# The native ball density metric and actual Möbius isometries

The density is 2 / (1 - ‖x‖²) on the actual Euclidean open unit ball.
Its path metric uses the density length construction. The restricted
one-point homeomorphism of a ball-preserving GM transformation is genuinely
differentiable; weighted tangent covariance proves path-distance preservation.

The identification with transport of the upper-half-space metric by the
Cayley map is a separate result, not asserted by this density definition.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint Manifold Bundle ENNReal
open Filter EuclideanGeometry Set Bundle
namespace LowDimensionalTopology.Geometry.Hyperbolic
variable {n : ℕ}

def unitBallDomain (n : ℕ) : TopologicalSpace.Opens (Inversive.Euclidean n) :=
  ⟨Metric.ball 0 1,Metric.isOpen_ball⟩

theorem unitBallDomain_norm_lt (x : unitBallDomain n) : ‖x.val‖ < 1 := by
  simpa only [Metric.mem_ball,dist_zero_right] using
    (show x.val ∈ Metric.ball (0 : Inversive.Euclidean n) 1 from x.property)

def ballDensity (n : ℕ) : Auxiliary.Analysis.Density (unitBallDomain n) where
  toFun x := 2/(1-‖x.val‖^2)
  continuous := by
    apply continuous_const.div (continuous_const.sub (continuous_subtype_val.norm.pow 2))
    intro x
    exact (sub_pos.mpr ((sq_lt_one_iff₀ (norm_nonneg _)).mpr (unitBallDomain_norm_lt x))).ne'
  positive x := div_pos (by norm_num)
    (sub_pos.mpr ((sq_lt_one_iff₀ (norm_nonneg _)).mpr (unitBallDomain_norm_lt x)))

def ballExtendedHomeomorph (n : ℕ) : unitBallDomain n ≃ₜ (Inversive.extendedUnitBall : Set (Inversive.ExtendedEuclidean
  n)) :=
  OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage (unitBallDomain n : Set (Inversive.Euclidean n))

theorem ballExtendedHomeomorph_symm_apply (z : (Inversive.extendedUnitBall : Set (Inversive.ExtendedEuclidean n))) :
    (((ballExtendedHomeomorph n).symm z).val : Inversive.ExtendedEuclidean n) = z.val := by
  exact congrArg Subtype.val ((ballExtendedHomeomorph n).apply_symm_apply z)

def ballHomeomorph (f : Inversive.ExtendedHomeomorph n) (hB : Inversive.PreservesUnitBall f) :
    unitBallDomain n ≃ₜ unitBallDomain n :=
  (ballExtendedHomeomorph n).trans
    ((f.image Inversive.extendedUnitBall).trans
      ((Homeomorph.setCongr hB).trans (ballExtendedHomeomorph n).symm))

theorem ballHomeomorph_coe (f : Inversive.ExtendedHomeomorph n) (hB : Inversive.PreservesUnitBall f)
    (x : unitBallDomain n) : ((ballHomeomorph f hB x).val : Inversive.ExtendedEuclidean n) = f x.val := by
  exact ballExtendedHomeomorph_symm_apply _

theorem ballHomeomorph_val (f : Inversive.ExtendedHomeomorph n) (hB : Inversive.PreservesUnitBall f)
    (x : unitBallDomain n) : (ballHomeomorph f hB x).val = Inversive.finiteEuclideanPart f x.val := by
  have he := ballHomeomorph_coe f hB x
  rw [← Inversive.coe_finiteEuclideanPart f (hB.maps_ball x.val (unitBallDomain_norm_lt x)).1] at he
  exact OnePoint.coe_injective he

theorem ballHomeomorph_writtenInExtChart_eventuallyEq
    (f : Inversive.ExtendedHomeomorph n) (hB : Inversive.PreservesUnitBall f) (x : unitBallDomain n) :
    writtenInExtChartAt 𝓘(ℝ,Inversive.Euclidean n) 𝓘(ℝ,Inversive.Euclidean n) x (ballHomeomorph f hB) =ᶠ[𝓝 x.val]
      Inversive.finiteEuclideanPart f := by
  filter_upwards [(unitBallDomain n).isOpen.mem_nhds x.property] with z hz
  let y : unitBallDomain n := ⟨z,hz⟩
  have hy := Auxiliary.Analysis.openDomain_chart_symm_apply x y
  change (ballHomeomorph f hB ((chartAt (Inversive.Euclidean n) x).symm z)).val = Inversive.finiteEuclideanPart f z
  rw [hy,ballHomeomorph_val]

theorem ballHomeomorph_mdifferentiable [NeZero n] (f : Inversive.ExtendedHomeomorph n)
    (hf : f ∈ Inversive.generalMobiusGroup n) (hB : Inversive.PreservesUnitBall f) :
    MDifferentiable 𝓘(ℝ,Inversive.Euclidean n) 𝓘(ℝ,Inversive.Euclidean n) (ballHomeomorph f hB) := by
  intro x
  rw [mdifferentiableAt_iff]
  refine ⟨(ballHomeomorph f hB).continuous.continuousAt,?_⟩
  have he := ballHomeomorph_writtenInExtChart_eventuallyEq f hB x
  have hdiff := (Inversive.generalMobius_conformalAt hf
    (hB.maps_ball x.val (unitBallDomain_norm_lt x)).1).differentiableAt
  have hh := hdiff.congr_of_eventuallyEq he
  change DifferentiableWithinAt ℝ
    (writtenInExtChartAt 𝓘(ℝ,Inversive.Euclidean n) 𝓘(ℝ,Inversive.Euclidean n) x (ballHomeomorph f hB)) _ x.val
  exact hh.differentiableWithinAt
theorem ballHomeomorph_mfderiv_apply [NeZero n] (f : Inversive.ExtendedHomeomorph n)
    (hf : f ∈ Inversive.generalMobiusGroup n) (hB : Inversive.PreservesUnitBall f)
    (x : unitBallDomain n) (v : TangentSpace 𝓘(ℝ,Inversive.Euclidean n) x) :
    (tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean n) (ballHomeomorph f hB x))
      (mfderiv 𝓘(ℝ,Inversive.Euclidean n) 𝓘(ℝ,Inversive.Euclidean n) (ballHomeomorph f hB) x v) =
    fderiv ℝ (Inversive.finiteEuclideanPart f) x.val ((tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean n) x) v) := by
  have hmd := ballHomeomorph_mdifferentiable f hf hB x
  simp only [mfderiv,hmd,ite_true,ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.apply_symm_apply]
  simp only [mfld_simps]
  change fderivWithin ℝ
    (writtenInExtChartAt 𝓘(ℝ,Inversive.Euclidean n) 𝓘(ℝ,Inversive.Euclidean n) x (ballHomeomorph f hB))
    Set.univ x.val ((tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean n) x) v) =
      fderiv ℝ (Inversive.finiteEuclideanPart f) x.val ((tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean n) x) v)
  rw [fderivWithin_univ]
  exact congrArg (fun A : Inversive.Euclidean n →L[ℝ] Inversive.Euclidean n ↦
    A ((tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean n) x) v))
    (ballHomeomorph_writtenInExtChart_eventuallyEq f hB x).fderiv_eq

instance unitBallDomain_preconnected (n : ℕ) : PreconnectedSpace (unitBallDomain n) :=
  isPreconnected_iff_preconnectedSpace.mp (convex_ball (0 : Inversive.Euclidean n) 1).isPreconnected

theorem ballDensity_tangent_covariance [NeZero n] (f : Inversive.ExtendedHomeomorph n)
    (hf : f ∈ Inversive.generalMobiusGroup n) (hB : Inversive.PreservesUnitBall f)
    (x : unitBallDomain n) (v : TangentSpace 𝓘(ℝ,Inversive.Euclidean n) x) :
    ballDensity n (ballHomeomorph f hB x) *
      ‖(tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean n) (ballHomeomorph f hB x))
        (mfderiv 𝓘(ℝ,Inversive.Euclidean n) 𝓘(ℝ,Inversive.Euclidean n) (ballHomeomorph f hB) x v)‖ =
      ballDensity n x * ‖(tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean n) x) v‖ := by
  rw [ballHomeomorph_mfderiv_apply f hf hB]
  change 2/(1-‖(ballHomeomorph f hB x).val‖^2) *
    ‖fderiv ℝ (Inversive.finiteEuclideanPart f) x.val ((tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean n) x) v)‖ =
      2/(1-‖x.val‖^2)*‖(tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean n) x) v‖
  rw [ballHomeomorph_val]
  exact Inversive.generalMobius_ball_density_covariance f hf hB x.val (unitBallDomain_norm_lt x)
    ((tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean n) x) v)

theorem ballDensity_pathEDist_invariant [NeZero n] (f : Inversive.ExtendedHomeomorph n)
    (hf : f ∈ Inversive.generalMobiusGroup n) (hB : Inversive.PreservesUnitBall f) (x y : unitBallDomain n) :
    (ballDensity n).pathEDist (ballHomeomorph f hB x) (ballHomeomorph f hB y) =
      (ballDensity n).pathEDist x y :=
  Auxiliary.Analysis.Density.pathEDist_equiv (ballHomeomorph f hB).toEquiv
    (ballHomeomorph_mdifferentiable f hf hB) (ballDensity_tangent_covariance f hf hB) x y

theorem ballDensity_pathDist_invariant [NeZero n] (f : Inversive.ExtendedHomeomorph n)
    (hf : f ∈ Inversive.generalMobiusGroup n) (hB : Inversive.PreservesUnitBall f) (x y : unitBallDomain n) :
    (ballDensity n).pathDist (ballHomeomorph f hB x) (ballHomeomorph f hB y) =
      (ballDensity n).pathDist x y :=
  congrArg ENNReal.toReal (ballDensity_pathEDist_invariant f hf hB x y)

theorem ballDensity_isometry [NeZero n] (f : Inversive.ExtendedHomeomorph n)
    (hf : f ∈ Inversive.generalMobiusGroup n) (hB : Inversive.PreservesUnitBall f) :
    @Isometry (unitBallDomain n) (unitBallDomain n)
      (ballDensity n).eMetricSpace.toPseudoEMetricSpace
      (ballDensity n).eMetricSpace.toPseudoEMetricSpace (ballHomeomorph f hB) :=
  Auxiliary.Analysis.Density.isometry_equiv (ballHomeomorph f hB).toEquiv
    (ballHomeomorph_mdifferentiable f hf hB) (ballDensity_tangent_covariance f hf hB)

theorem ballDensity_tangent_norm (x : unitBallDomain n)
    (v : TangentSpace 𝓘(ℝ,Inversive.Euclidean n) x) :
    letI : RiemannianBundle (fun y : unitBallDomain n ↦ TangentSpace 𝓘(ℝ,Inversive.Euclidean n) y) :=
      ⟨(ballDensity n).riemannianMetric.toRiemannianMetric⟩
    ‖v‖ = (2/(1-‖x.val‖^2))*‖(tangentSpaceCastModel 𝓘(ℝ,Inversive.Euclidean n) x) v‖ :=
  Auxiliary.Analysis.Density.tangent_norm (ballDensity n) x v

@[instance_reducible] def ballMetricSpace (n : ℕ) : MetricSpace (unitBallDomain n) := (ballDensity n).metricSpace

theorem ballMetricSpace_dist (x y : unitBallDomain n) :
    @dist (unitBallDomain n) (ballMetricSpace n).toDist x y =
      (ballDensity n).pathDist x y :=
  ((ballDensity n).pathDist_eq_dist x y).symm

end LowDimensionalTopology.Geometry.Hyperbolic
