module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.TopologicalRiemannRoch
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S26_TeichmullerUniqueness
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Group.Uniform

/-!
# The book L1 norm on original-atlas quadratic differentials

The norm is twice the invariant Lebesgue integral of the absolute coefficient.
Chart independence, finiteness, positivity and homogeneity use Wu Xiaobin's
attributed LiZhongQC source.
The metric structures are explicit data; no competing global norm is installed.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.QuadraticL1
open Surfaces
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- The invariant integral of the actual quadratic coefficient density. -/
def coefficientIntegral (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) : ℝ≥0∞ :=
  let := R.toRiemannAtlas.toChartedSpace
  LiZhongQC.quadDiffNorm (q : X → ℂ → ℂ)

private theorem integral_facts (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    coefficientIntegral R q < ⊤ ∧ (coefficientIntegral R q = 0 ↔ q = 0) ∧
      ∀ c : ℂ, coefficientIntegral R (c • q) = ENNReal.ofReal ‖c‖ * coefficientIntegral R q := by
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨hf, hz, hs⟩ := LiZhongQC.quadDiffNorm_finite q.property
  exact ⟨hf, ⟨fun h => Subtype.ext (hz.mp h), fun h => hz.mpr (congrArg Subtype.val h)⟩, hs⟩

/-- Every genuine chart partition computes this same integral. -/
theorem coefficientIntegral_eq_partition
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    let := R.toRiemannAtlas.toChartedSpace
    ∀ {x : ℕ → X} {P : ℕ → Set X}, LiZhongQC.IsChartPartition X x P →
      coefficientIntegral R q =
        ∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖(q : X → ℂ → ℂ) (x i) z‖ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  dsimp only
  intro x P hP
  simpa only [coefficientIntegral, LiZhongQC.quadDiffNorm, one_mul] using
    LiZhongQC.s26v_surfaceIntegral_eq_tsum q.property (fun _ => (1 : ℝ≥0∞)) hP

private theorem integral_triangle (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    coefficientIntegral R (q + r) ≤ coefficientIntegral R q + coefficientIntegral R r := by
  let := R.compactSpace
  let := R.nonempty
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨x, P, hP⟩ := LiZhongQC.s26_exists_chartPartition' (S := X)
  have hmeas (i : ℕ) : AEMeasurable
      (fun z => ENNReal.ofReal ‖(q : X → ℂ → ℂ) (x i) z‖)
      (volume.restrict (chartAt ℂ (x i) '' P i)) := by
    have hsub : chartAt ℂ (x i) '' P i ⊆ (chartAt ℂ (x i)).target := by
      rintro _ ⟨p, hp, rfl⟩
      exact (chartAt ℂ (x i)).map_source ((hP.1 i).1 hp)
    have hhol : DifferentiableOn ℂ ((q : X → ℂ → ℂ) (x i)) (chartAt ℂ (x i)).target :=
      q.property.2 (x i)
    exact ENNReal.measurable_ofReal.comp_aemeasurable
      ((hhol.continuousOn.mono hsub).aemeasurable (hP.1 i).2).norm
  rw [coefficientIntegral_eq_partition R (q + r) hP,
    coefficientIntegral_eq_partition R q hP, coefficientIntegral_eq_partition R r hP,
    ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [← lintegral_add_left' (hmeas i)]
  refine lintegral_mono fun z => ?_
  change ENNReal.ofReal ‖(q : X → ℂ → ℂ) (x i) z + (r : X → ℂ → ℂ) (x i) z‖ ≤ _
  exact (ENNReal.ofReal_le_ofReal (norm_add_le _ _)).trans ENNReal.ofReal_add_le

/-- The book convention is exactly twice the invariant absolute-coefficient integral. -/
def bookNorm (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) : ℝ :=
  2 * (coefficientIntegral R q).toReal

/-- The norm can be evaluated using any actual measurable chart partition. -/
theorem bookNorm_eq_partition (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    let := R.toRiemannAtlas.toChartedSpace
    ∀ {x : ℕ → X} {P : ℕ → Set X}, LiZhongQC.IsChartPartition X x P →
      bookNorm R q = 2 *
        (∑' i, ∫⁻ z in chartAt ℂ (x i) '' P i, ENNReal.ofReal ‖(q : X → ℂ → ℂ) (x i) z‖).toReal := by
  let := R.toRiemannAtlas.toChartedSpace
  dsimp only
  intro x P hP
  rw [bookNorm, coefficientIntegral_eq_partition R q hP]

private theorem bookNorm_zero_iff (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    bookNorm R q = 0 ↔ q = 0 := by
  constructor
  · intro h
    have ht : (coefficientIntegral R q).toReal = 0 := by
      dsimp [bookNorm] at h
      linarith
    exact (integral_facts R q).2.1.mp
      (((ENNReal.toReal_eq_zero_iff _).mp ht).resolve_right (integral_facts R q).1.ne)
  · intro h
    rw [bookNorm, (integral_facts R q).2.1.mpr h, ENNReal.toReal_zero, mul_zero]

private theorem bookNorm_smul (c : ℂ) (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    bookNorm R (c • q) = ‖c‖ * bookNorm R q := by
  unfold bookNorm
  rw [(integral_facts R q).2.2 c, ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg _)]
  ring

private theorem bookNorm_triangle (q r : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    bookNorm R (q + r) ≤ bookNorm R q + bookNorm R r := by
  have hq := (integral_facts R q).1.ne
  have hr := (integral_facts R r).1.ne
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hq, hr⟩) (integral_triangle R q r)
  rw [ENNReal.toReal_add hq hr] at h
  dsimp [bookNorm]
  linarith

/-- All norm laws for the literal book L1 integral. -/
theorem normCore :
    let : Norm (HolomorphicQuadraticDifferential R.toRiemannAtlas) := ⟨bookNorm R⟩
    NormedSpace.Core ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) := by
  let : Norm (HolomorphicQuadraticDifferential R.toRiemannAtlas) := ⟨bookNorm R⟩
  exact { norm_nonneg := fun _ => mul_nonneg (by norm_num) ENNReal.toReal_nonneg
          norm_smul := bookNorm_smul R
          norm_triangle := bookNorm_triangle R
          norm_eq_zero_iff := bookNorm_zero_iff R }

/-- The actual original-atlas QD space, equipped with the book L1 metric. -/
@[instance_reducible]
def normedAddCommGroup : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) := by
  let : Norm (HolomorphicQuadraticDifferential R.toRiemannAtlas) := ⟨bookNorm R⟩
  exact NormedAddCommGroup.ofCore (normCore R)

/-- The constructed norm is the literal book integral. -/
theorem norm_eq_bookNorm (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) := normedAddCommGroup R
    ‖q‖ = bookNorm R q := rfl

/-- Complex scalar multiplication obeys the L1 norm law. -/
@[instance_reducible]
def normedSpace :
    let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) := normedAddCommGroup R
    NormedSpace ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) := by
  let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) := normedAddCommGroup R
  exact NormedSpace.ofCore (normCore R)

/-- Completeness follows for this precise norm from actual finite dimensionality. -/
theorem completeSpace :
    @CompleteSpace (HolomorphicQuadraticDifferential R.toRiemannAtlas)
      (normedAddCommGroup R).toMetricSpace.toUniformSpace := by
  let G := normedAddCommGroup R
  let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) := G
  let : MetricSpace (HolomorphicQuadraticDifferential R.toRiemannAtlas) := G.toMetricSpace
  let : UniformSpace (HolomorphicQuadraticDifferential R.toRiemannAtlas) := G.toMetricSpace.toUniformSpace
  let : TopologicalSpace (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    G.toMetricSpace.toUniformSpace.toTopologicalSpace
  let : IsUniformAddGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    G.toSeminormedAddCommGroup.to_isUniformAddGroup
  let : NormedSpace ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) := normedSpace R
  let : FiniteDimensional ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    R.finiteDimensional_holomorphicQuadraticDifferential
  exact FiniteDimensional.complete ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas)

/-- The book's parameter ball A2(R)₁, with its precise L1 metric. -/
def openUnitBall : Set (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
  @Metric.ball _ (normedAddCommGroup R).toMetricSpace.toPseudoMetricSpace 0 1

/-- The parameter subtype carries the metric induced by the actual book norm. -/
@[instance_reducible]
def unitBallMetricSpace : MetricSpace ↥(openUnitBall R) := by
  let : MetricSpace (HolomorphicQuadraticDifferential R.toRiemannAtlas) :=
    (normedAddCommGroup R).toMetricSpace
  infer_instance

/-- Membership is the strict book integral bound, with no basis-norm substitution. -/
theorem mem_openUnitBall (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    q ∈ openUnitBall R ↔ bookNorm R q < 1 := by
  let : NormedAddCommGroup (HolomorphicQuadraticDifferential R.toRiemannAtlas) := normedAddCommGroup R
  change dist q (0 : HolomorphicQuadraticDifferential R.toRiemannAtlas) < 1 ↔ _
  rw [dist_zero_right]
  rfl

/-- Equipping the actual QD space with L1 does not change its proved dimensions. -/
theorem finrank {g : ℕ} (hgenus : R.HasGenus g) (hg : 1 < g) :
    Module.finrank ℂ (HolomorphicQuadraticDifferential R.toRiemannAtlas) = 3 * g - 3 ∧
      Module.finrank ℝ (HolomorphicQuadraticDifferential R.toRiemannAtlas) = 6 * g - 6 :=
  R.holomorphicQuadraticDifferential_finrank hgenus hg

end LowDimensionalTopology.Geometry.Teichmuller.QuadraticL1
