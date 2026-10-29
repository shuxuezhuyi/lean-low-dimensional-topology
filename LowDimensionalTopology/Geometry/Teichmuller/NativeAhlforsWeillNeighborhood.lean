module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersProjectionTopology
public import LowDimensionalTopology.Geometry.Teichmuller.NativeAhlforsWeillSection
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersBasePoint
public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The full half-unit Ahlfors-Weill neighborhood of the original boundary model

The section is the actual coefficient quotient projection of the literal
harmonic coefficient. Its image is an open neighborhood for the original QC
metric. Its genuine Bers coordinates are complex-linear on the ENTIRE ball
of radius one half, which proves holomorphy in the original Bers atlas.
No smaller inverse germ or coefficient-quotient topology premise is used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Topology MeasureTheory Complex
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces GammaMeasurableBeltrami

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    {Γ : Subgroup Deck} (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

local instance : Nonempty (LiZhongQC.TeichGamma Γ) := ⟨LiZhongQC.TeichGamma.origin Γ⟩

local notation "hP" => canonicalHandleGroupPresentation g
local notation "E" => gammaEquiv R hg hgenus hP hΓ hfree hp
local notation "BC" => bersCoordinates R hg hgenus hP hΓ hfree hp
local notation "W" => weightedLinearBersCoordinates R hg hgenus hP hΓ hp
local notation "mΓ" => gammaQCMetricSpace R hg hgenus hΓ hfree hp
local notation "A" => BersWeighted.Automorphic Γ
local notation "V" => Metric.ball (0 : A) (1 / 2 : ℝ)
local notation "Z" => Fin (3 * g - 3) → ℂ

/-- Actual Bers coordinates on the original group boundary quotient. -/
def gammaBersCoordinates (a : LiZhongQC.TeichGamma Γ) : Z := BC ((E).symm a)

local notation "G" => gammaBersCoordinates R hg hgenus hΓ hfree hp

/-- The normalized-lift equivalence is a homeomorphism for the proved original metrics. -/
def gammaQCBersHomeomorph :
    letI := mΓ
    LiZhongQC.TeichGamma Γ ≃ₜ range BC := by
  letI : MetricSpace (TeichmullerSpace.{u, u} R) := fromQCMetricSpace R hg hgenus hP
  letI := mΓ
  let H : LiZhongQC.TeichGamma Γ ≃ₜ TeichmullerSpace.{u, u} R :=
    { (E).symm with
      continuous_toFun := continuous_induced_dom
      continuous_invFun := by
        apply continuous_induced_rng.mpr
        change Continuous ((E).symm ∘ E)
        have he : (E).symm ∘ E = id := funext (E).symm_apply_apply
        rw [he]
        exact continuous_id }
  exact H.trans (fromQCBersCoordinateHomeomorph R hg hgenus hP hΓ hfree hp)

/-- The actual original group Bers coordinates form an open embedding. -/
theorem gammaBersCoordinates_isOpenEmbedding :
    letI := mΓ
    Topology.IsOpenEmbedding G := by
  let := mΓ
  let H := gammaQCBersHomeomorph R hg hgenus hΓ hfree hp
  have hi : Topology.IsEmbedding G := by
    change Topology.IsEmbedding (Subtype.val ∘ H)
    exact Topology.IsEmbedding.subtypeVal.comp H.isEmbedding
  have hr : range G = range BC := by
    ext z
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨(E).symm a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨E a, by simp only [gammaBersCoordinates, (E).symm_apply_apply]⟩
  refine ⟨hi, ?_⟩
  rw [hr]
  exact isOpen_range_bersCoordinates R hg hgenus hP hΓ hfree hp

/-- The book Bers complex atlas on the actual original boundary/QC metric topology. -/
@[instance_reducible] def gammaBersChartedSpace :
    letI := mΓ
    ChartedSpace Z (LiZhongQC.TeichGamma Γ) := by
  letI := mΓ
  exact (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp).singletonChartedSpace

theorem gammaBers_isManifold :
    letI := mΓ
    letI := gammaBersChartedSpace R hg hgenus hΓ hfree hp
    IsManifold 𝓘(ℂ, Z) ω (LiZhongQC.TeichGamma Γ) := by
  let := mΓ
  let := gammaBersChartedSpace R hg hgenus hΓ hfree hp
  exact (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp).isManifold_singleton

/-- Project the literal harmonic coefficient by the independently defined actual quotient map. -/
def gammaAhlforsWeillPsi (φ : A) : LiZhongQC.TeichGamma Γ :=
  E (coefficientProjection R hg hgenus hP hΓ hfree hp (BersWeighted.ahlforsWeill φ))

local notation "Ψ" => gammaAhlforsWeillPsi R hg hgenus hΓ hfree hp

/-- The coefficient is literally the book harmonic coefficient, as an actual L-infinity class. -/
theorem gammaAhlforsWeillCoefficient_ae (φ : A) :
    (BersWeighted.ahlforsWeill φ).val =ᵐ[(volume : Measure ℍ)]
      fun z : ℍ => -2 * (z.im : ℂ) ^ 2 * (φ.toSource : ℂ → ℂ) (conj (z : ℂ)) := by
  filter_upwards [BersWeighted.ahlforsWeill_coe_ae φ] with z hz
  rw [hz]
  norm_num [BersWeighted.ahlforsWeillCoefficient]

/-- On the FULL half-unit ball this is the actual coefficient-to-boundary projection. -/
theorem gammaAhlforsWeillPsi_eq_projection (φ : A) (hφ : φ ∈ V) :
    Ψ φ = gammaCoefficientProjectionBall
      (⟨BersWeighted.ahlforsWeill φ, by
        have hn := BersWeighted.norm_ahlforsWeill_le φ
        have hs := mem_ball_zero_iff.mp hφ
        simpa only [Metric.mem_ball, dist_zero_right] using (show
          ‖BersWeighted.ahlforsWeill φ‖ < 1 by linarith)⟩ : Ball Γ) := by
  have hs := mem_ball_zero_iff.mp hφ
  have hn : ‖BersWeighted.ahlforsWeill φ‖ < 1 :=
    (BersWeighted.norm_ahlforsWeill_le φ).trans_lt (by linarith)
  unfold gammaAhlforsWeillPsi coefficientProjection
  rw [dite_eq_left hn]
  exact (E).apply_symm_apply _

/-- The actual section coordinates are complex-linear throughout the full half-unit ball. -/
theorem gammaAhlforsWeillPsi_coordinates (φ : A) (hφ : φ ∈ V) : G (Ψ φ) = W φ := by
  change BC ((E).symm (E _)) = W φ
  rw [(E).symm_apply_apply,
    coefficientProjection_coordinates R hg hgenus hP hΓ hfree hp,
    BersWeighted.automorphicProjection_ahlforsWeill hΓ φ (mem_ball_zero_iff.mp hφ)]

/-- The literal original normalized Schwarzian gives the exact right-inverse equation. -/
theorem gammaAhlforsWeillPsi_bersMap (φ : A) (hφ : φ ∈ V) :
    LiZhongQC.bersMapGamma Γ (Ψ φ) = (φ.toSource : ℂ → ℂ) := by
  have he : weightedBersEmbedding R hg hgenus hΓ hfree hp ((E).symm (Ψ φ)) = φ := by
    apply (W).injective
    change W ((W).symm (G (Ψ φ))) = W φ
    rw [(W).apply_symm_apply]
    exact gammaAhlforsWeillPsi_coordinates R hg hgenus hΓ hfree hp φ hφ
  have hs := weightedBersEmbedding_toSource R hg hgenus hΓ hfree hp ((E).symm (Ψ φ))
  rw [(E).apply_symm_apply] at hs
  exact hs.symm.trans (congrArg (fun ψ : A => (ψ.toSource : ℂ → ℂ)) he)

/-- The zero parameter is exactly the original identity boundary class. -/
theorem gammaAhlforsWeillPsi_zero : Ψ 0 = LiZhongQC.TeichGamma.origin Γ := by
  unfold gammaAhlforsWeillPsi
  rw [map_zero, coefficientProjection_zero, gammaEquiv_basePoint]

/-- The actual image of the entire half-unit section domain. -/
def gammaAhlforsWeillImage : Set (LiZhongQC.TeichGamma Γ) := Ψ '' V

local notation "U" => gammaAhlforsWeillImage R hg hgenus hΓ hfree hp

/-- An exact image identity, not a smaller local neighborhood. -/
theorem gammaAhlforsWeillImage_eq : U = {a | ‖(W).symm (G a)‖ < 1 / 2} := by
  ext a
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    change ‖(W).symm (G (Ψ φ))‖ < 1 / 2
    rw [gammaAhlforsWeillPsi_coordinates R hg hgenus hΓ hfree hp φ hφ,
      (W).symm_apply_apply]
    exact mem_ball_zero_iff.mp hφ
  · intro ha
    let := mΓ
    have hφ : (W).symm (G a) ∈ V := mem_ball_zero_iff.mpr ha
    refine ⟨(W).symm (G a), hφ, ?_⟩
    apply (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp).injective
    rw [gammaAhlforsWeillPsi_coordinates R hg hgenus hΓ hfree hp _ hφ,
      (W).apply_symm_apply]

/-- The entire section image is an OPEN neighborhood of the original basepoint. -/
theorem gammaAhlforsWeillImage_open_base :
    letI := mΓ
    IsOpen U ∧ LiZhongQC.TeichGamma.origin Γ ∈ U := by
  let := mΓ
  constructor
  · rw [gammaAhlforsWeillImage_eq R hg hgenus hΓ hfree hp]
    exact isOpen_lt
      ((W).symm.continuous.comp
        (gammaBersCoordinates_isOpenEmbedding R hg hgenus hΓ hfree hp).continuous).norm
      continuous_const
  · exact ⟨0, Metric.mem_ball_self (by norm_num),
      gammaAhlforsWeillPsi_zero R hg hgenus hΓ hfree hp⟩

/-- A section point is recovered by the actual book chart inverse on the FULL domain. -/
theorem gammaAhlforsWeillPsi_eq_chartSymm (a : LiZhongQC.TeichGamma Γ) (φ : A) (hφ : φ ∈ V) :
    letI := mΓ
    letI := gammaBersChartedSpace R hg hgenus hΓ hfree hp
    Ψ φ = (chartAt Z a).symm (W φ) := by
  let := mΓ
  let := gammaBersChartedSpace R hg hgenus hΓ hfree hp
  rw [← gammaAhlforsWeillPsi_coordinates R hg hgenus hΓ hfree hp φ hφ]
  change Ψ φ = (chartAt Z a).symm ((chartAt Z a) (Ψ φ))
  exact ((chartAt Z a).left_inv (by change Ψ φ ∈ (univ : Set _); trivial)).symm

/-- The actual section is holomorphic on the ENTIRE original half-unit parameter ball. -/
theorem mdifferentiableOn_gammaAhlforsWeillPsi :
    letI := mΓ
    letI := gammaBersChartedSpace R hg hgenus hΓ hfree hp
    MDifferentiableOn 𝓘(ℂ, A) 𝓘(ℂ, Z) Ψ V := by
  let := mΓ
  let := gammaBersChartedSpace R hg hgenus hΓ hfree hp
  let : IsManifold 𝓘(ℂ, Z) ω (LiZhongQC.TeichGamma Γ) :=
    gammaBers_isManifold R hg hgenus hΓ hfree hp
  intro φ hφ
  let a := Ψ φ
  have hf : MDifferentiableAt 𝓘(ℂ, A) 𝓘(ℂ, Z) W φ :=
    (W).differentiableAt.mdifferentiableAt
  have hvalue : W φ = (chartAt Z a) a :=
    (gammaAhlforsWeillPsi_coordinates R hg hgenus hΓ hfree hp φ hφ).symm
  have hc := (mdifferentiable_chart (I := 𝓘(ℂ, Z)) a).symm.mdifferentiableAt
    ((chartAt Z a).map_source (mem_chart_source Z a))
  have hcomp := hc.comp_of_eq φ hf hvalue
  apply (hcomp.congr_of_eventuallyEq ?_).mdifferentiableWithinAt
  filter_upwards [Metric.isOpen_ball.mem_nhds hφ] with ψ hψ
  exact gammaAhlforsWeillPsi_eq_chartSymm R hg hgenus hΓ hfree hp a ψ hψ

/-- The map with its literal open-domain and actual-image codomain. -/
def gammaAhlforsWeillSection : V → U :=
  fun φ => ⟨Ψ φ.val, φ.val, φ.property, rfl⟩

/-- All conclusions of the full half-unit neighborhood theorem, in the original boundary model. -/
theorem gammaAhlforsWeillNeighborhood_full :
    letI := mΓ
    letI := gammaBersChartedSpace R hg hgenus hΓ hfree hp
    IsOpen U ∧ LiZhongQC.TeichGamma.origin Γ ∈ U ∧
      MDifferentiableOn 𝓘(ℂ, A) 𝓘(ℂ, Z) Ψ V ∧
      ∀ φ ∈ V, LiZhongQC.bersMapGamma Γ (Ψ φ) = (φ.toSource : ℂ → ℂ) := by
  let := mΓ
  let := gammaBersChartedSpace R hg hgenus hΓ hfree hp
  obtain ⟨hopen, hbase⟩ := gammaAhlforsWeillImage_open_base R hg hgenus hΓ hfree hp
  exact ⟨hopen, hbase, mdifferentiableOn_gammaAhlforsWeillPsi R hg hgenus hΓ hfree hp,
    gammaAhlforsWeillPsi_bersMap R hg hgenus hΓ hfree hp⟩

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
