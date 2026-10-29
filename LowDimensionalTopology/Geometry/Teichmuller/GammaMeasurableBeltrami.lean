module

public import LowDimensionalTopology.Geometry.Teichmuller.GammaLpOperators
public import LowDimensionalTopology.Geometry.Teichmuller.DomainMeasurableBeltrami
public import LowDimensionalTopology.Geometry.Teichmuller.SourceMarking
public import LowDimensionalTopology.External.LiZhongQC.Ch10.S33_BersEmbedding
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Tactic.FunProp

/-!
# The genuine measurable Beltrami Banach space in a uniformizing model

Coefficients are actual L-infinity almost-everywhere classes. The deck tensor
law cuts out a proved closed complex subspace using actual continuous linear
isometries. Hyperbolic and Euclidean area have the same null sets on the upper
half-plane. Subunit classes therefore feed the actual quasiconformal surface
construction and its preferred-chart almost-everywhere tensor law.
The all-original-chart linear isometric correspondence is a separate task.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal NNReal Manifold ContDiff UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami

open Surfaces

/-- Actual L-infinity classes satisfying every deck transformation equation. -/
def compatibleSubmodule (Γ : Subgroup Deck) : Submodule ℂ Ambient where
  carrier := {μ | ∀ γ ∈ Γ, pullback γ μ = μ}
  zero_mem' := by
    intro γ hγ
    exact map_zero _
  add_mem' := by
    intro μ ν hμ hν γ hγ
    rw [map_add, hμ γ hγ, hν γ hγ]
  smul_mem' := by
    intro a μ hμ γ hγ
    rw [map_smul, hμ γ hγ]

/-- Every compatibility equation is an equalizer of actual continuous maps. -/
theorem isClosed_compatibleSubmodule (Γ : Subgroup Deck) :
    IsClosed (compatibleSubmodule Γ : Set Ambient) := by
  change IsClosed {μ : Ambient | ∀ γ ∈ Γ, pullback γ μ = μ}
  simp_rw [ofPred_forall]
  exact isClosed_iInter fun γ => isClosed_iInter fun _ =>
    isClosed_eq (pullback γ).continuous continuous_id

/-- The closed complex subspace, carrying its genuine inherited L-infinity norm. -/
def compatibleClosedSubmodule (Γ : Subgroup Deck) : ClosedSubmodule ℂ Ambient :=
  ⟨compatibleSubmodule Γ, isClosed_compatibleSubmodule Γ⟩

abbrev Space (Γ : Subgroup Deck) := ↥(compatibleClosedSubmodule Γ)
abbrev Ball (Γ : Subgroup Deck) := ↥(Metric.ball (0 : Space Γ) 1)

theorem completeSpace (Γ : Subgroup Deck) : CompleteSpace (Space Γ) := inferInstance

/-- Closed-subspace membership is precisely the actual almost-everywhere tensor law. -/
theorem mem_compatibleSubmodule_iff {Γ : Subgroup Deck} (μ : Ambient) :
    μ ∈ compatibleSubmodule Γ ↔
      ∀ γ ∈ Γ, ∀ᵐ z : ℍ ∂volume, μ z = phase γ z * μ (γ • z) := by
  constructor
  · intro h γ hγ
    have hrep := pullback_coe_ae γ μ
    rw [h γ hγ] at hrep
    exact hrep
  · intro h γ hγ
    apply Lp.ext
    filter_upwards [pullback_coe_ae γ μ, h γ hγ] with z hpb hμ
    exact hpb.trans hμ.symm

/-- The unit ball uses the intrinsic class norm, equivalently a strict a.e. bound. -/
theorem norm_lt_one_iff {Γ : Subgroup Deck} (μ : Space Γ) :
    ‖μ‖ < 1 ↔ ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧ ∀ᵐ z : ℍ ∂volume, ‖μ.val z‖ ≤ k :=
  lpInfinity_norm_lt_one_iff μ.val

namespace Ball

variable {Γ : Subgroup Deck}

theorem norm_lt_one (μ : Ball Γ) : ‖μ.val‖ < 1 := by
  simpa only [Metric.mem_ball, dist_zero_right] using μ.property

end Ball

/-- Euclidean area on the actual upper half-plane. -/
abbrev flatMeasure : Measure ℍ := (volume : Measure ℂ).comap UpperHalfPlane.coe

/-- The positive density relating hyperbolic to Euclidean area. -/
def hyperbolicDensity (z : ℍ) : ℝ≥0∞ :=
  ↑((1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2)

theorem measurable_hyperbolicDensity : Measurable hyperbolicDensity := by
  unfold hyperbolicDensity
  fun_prop

theorem hyperbolicDensity_ne_zero (z : ℍ) : hyperbolicDensity z ≠ 0 := by
  have hz : NNReal.mk z.im z.im_pos.le ≠ 0 := NNReal.ne_iff.mp z.im_ne_zero
  exact ENNReal.coe_ne_zero.mpr (pow_ne_zero 2 (one_div_ne_zero hz))

/-- The two actual area measures have exactly the same almost-everywhere assertions. -/
theorem ae_hyperbolic_iff {P : ℍ → Prop} :
    (∀ᵐ z ∂(volume : Measure ℍ), P z) ↔ ∀ᵐ z ∂flatMeasure, P z := by
  change (∀ᵐ z ∂flatMeasure.withDensity hyperbolicDensity, P z) ↔ _
  constructor
  · intro h
    have hd := (ae_withDensity_iff measurable_hyperbolicDensity).1 h
    filter_upwards [hd] with z hz
    exact hz (hyperbolicDensity_ne_zero z)
  · intro h
    apply (ae_withDensity_iff measurable_hyperbolicDensity).2
    exact h.mono fun _ hz _ => hz

theorem flat_absolutelyContinuous_hyperbolic : flatMeasure ≪ (volume : Measure ℍ) :=
  withDensity_absolutelyContinuous' measurable_hyperbolicDensity.aemeasurable
    (Filter.Eventually.of_forall hyperbolicDensity_ne_zero)

/-- The actual inclusion sends Euclidean area to restricted planar area. -/
theorem map_flat_coe : Measure.map UpperHalfPlane.coe flatMeasure =
    (volume : Measure ℂ).restrict LiZhongQC.upperHalf := by
  change Measure.map UpperHalfPlane.coe
      ((volume : Measure ℂ).comap UpperHalfPlane.coe) =
    (volume : Measure ℂ).restrict UpperHalfPlane.upperHalfPlaneSet
  rw [UpperHalfPlane.measurableEmbedding_coe.map_comap, UpperHalfPlane.range_coe]

/-- Restricted planar area and hyperbolic area detect the same null assertions. -/
theorem ae_plane_iff {P : ℂ → Prop} :
    (∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf), P z) ↔
      ∀ᵐ z : ℍ ∂volume, P (z : ℂ) := by
  rw [← map_flat_coe, UpperHalfPlane.measurableEmbedding_coe.ae_map_iff]
  exact ae_hyperbolic_iff.symm

/-- Actual representative measurability is preserved in both directions. -/
theorem aestronglyMeasurable_plane_iff {f : ℂ → ℂ} :
    AEStronglyMeasurable f (volume.restrict LiZhongQC.upperHalf) ↔
      AEStronglyMeasurable (fun z : ℍ => f (z : ℂ)) volume := by
  rw [← map_flat_coe,
    UpperHalfPlane.measurableEmbedding_coe.aestronglyMeasurable_map_iff]
  exact ⟨fun h => h.mono_ac (withDensity_absolutelyContinuous flatMeasure hyperbolicDensity),
    fun h => h.mono_ac flat_absolutelyContinuous_hyperbolic⟩

/-- A chosen L-infinity representative extended by zero outside the half-plane. -/
def planeRepresentative (μ : Ambient) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ LiZhongQC.upperHalf then μ ⟨z, hz⟩ else 0

@[simp]
theorem planeRepresentative_coe (μ : Ambient) (z : ℍ) :
    planeRepresentative μ (z : ℂ) = μ z := by
  unfold planeRepresentative
  exact dite_eq_left (show (z : ℂ) ∈ LiZhongQC.upperHalf from z.im_pos)

theorem planeRepresentative_off (μ : Ambient) {z : ℂ}
    (hz : z ∉ LiZhongQC.upperHalf) : planeRepresentative μ z = 0 := by
  simp only [planeRepresentative, dite_eq_right hz]

/-- The class's own norm is an actual Euclidean a.e. bound on its planar representative. -/
theorem planeRepresentative_isBeltramiCoeff (μ : Ambient) :
    LiZhongQC.IsBeltramiCoeff (planeRepresentative μ) LiZhongQC.upperHalf ‖μ‖ := by
  have hmeas : AEStronglyMeasurable (μ : ℍ → ℂ) flatMeasure :=
    (Lp.aestronglyMeasurable μ).mono_ac flat_absolutelyContinuous_hyperbolic
  constructor
  · rw [← map_flat_coe, UpperHalfPlane.measurableEmbedding_coe.aestronglyMeasurable_map_iff]
    simpa only [Function.comp_def, planeRepresentative_coe] using hmeas
  · rw [← map_flat_coe, UpperHalfPlane.measurableEmbedding_coe.ae_map_iff]
    simpa only [planeRepresentative_coe] using
      (ae_hyperbolic_iff).1 (lpInfinity_norm_ae_le μ)

/-- Compatibility is the original phase-bearing planar deck law, not an added field. -/
theorem planeRepresentative_isGammaCompatible {Γ : Subgroup Deck} (μ : Space Γ) :
    LiZhongQC.IsGammaCompatible Γ (planeRepresentative μ.val) := by
  intro γ hγ
  rw [← map_flat_coe, UpperHalfPlane.measurableEmbedding_coe.ae_map_iff]
  have h := (ae_hyperbolic_iff).1 ((mem_compatibleSubmodule_iff μ.val).1 μ.property γ hγ)
  filter_upwards [h] with z hz
  rw [planeRepresentative_coe]
  have hmob := planeRepresentative_coe μ.val (γ • z)
  rw [LiZhongQC.h23l_b_coe_smul] at hmob
  rw [hmob]
  change μ.val z = μ.val (γ • z) * phase γ z
  simpa only [mul_comm] using hz

/-- Each compatible subunit class is an actual element of the planar coefficient ball. -/
def toDomainBall {Γ : Subgroup Deck} (μ : Ball Γ) :
    DomainMeasurableBeltramiBall LiZhongQC.upperHalf :=
  DomainMeasurableBeltramiBall.ofCoefficient (norm_nonneg μ.val.val) (Ball.norm_lt_one μ)
    (planeRepresentative_isBeltramiCoeff μ.val.val)

universe u

/-- The actual source-atlas coefficient family of a genuine QC marking. -/
def markingAtlasCoefficient {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    (m : LiZhongQC.MarkedRS X) : X → ℂ → ℂ :=
  fun x => (chartAt ℂ x).target.indicator fun z =>
    LiZhongQC.complexDilatation
      (fun w => chartAt ℂ (m.marking ((chartAt ℂ x).symm z))
        (m.marking ((chartAt ℂ x).symm w))) z

/-- Every subunit class has an actual marked surface with the same lifted
coefficient and a genuine measurable atlas tensor in the actual preferred reference charts. -/
theorem exists_marked_atlas_tensor {X : Type u} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (μ : Ball Γ) :
    let := R.toRiemannAtlas.toChartedSpace
    ∃ m : LiZhongQC.MarkedRS X,
      (LiZhongQC.s27u_liftCoeff p m.marking =ᵐ[volume.restrict LiZhongQC.upperHalf]
        planeRepresentative μ.val.val) ∧
      ∃ K : ℝ, LiZhongQC.IsKQCRS m.marking K ∧
        LiZhongQC.IsBeltramiDifferential (markingAtlasCoefficient m) ((K - 1) / (K + 1)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  obtain ⟨m, hm⟩ := LiZhongQC.s27v_exists_marked hp (norm_nonneg μ.val.val)
    (Ball.norm_lt_one μ) (planeRepresentative_isBeltramiCoeff μ.val.val)
    (planeRepresentative_isGammaCompatible μ.val)
  obtain ⟨K, hK⟩ := m.qc
  exact ⟨m, hm, K, hK, LiZhongQC.eq23_1_beltrami_differential hK⟩

end LowDimensionalTopology.Geometry.Teichmuller.GammaMeasurableBeltrami
