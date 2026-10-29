module

public import LowDimensionalTopology.Geometry.Teichmuller.MeasurableAtlasTransitions
public import LowDimensionalTopology.Geometry.Teichmuller.DomainMeasurableBeltrami
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
public import Mathlib.Tactic.Ring

/-!
# The genuine Banach space of measurable Beltrami tensors on the full atlas

Each coordinate is an actual restricted-area L-infinity class. The ambient space
is the complete bounded product over every original chart. Genuine bounded
linear overlap maps impose the tensor equations as closed equalizers. Thus no
raw-function supremum seminorm or pointwise representative is declared a norm.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.AtlasMeasurableBeltrami

open Surfaces

universe u
variable {X : Type u} [TopologicalSpace X]

abbrev Chart (A : RiemannAtlas X) := {e : OpenPartialHomeomorph X ℂ // e ∈ A.charts}
abbrev Ambient (A : RiemannAtlas X) :=
  lp (fun e : Chart A => DomainMeasurableBeltramiSpace e.val.target) (⊤ : ℝ≥0∞)

/-- An actual L-infinity class remains L-infinity on a smaller planar set. -/
theorem restrictMemLp {D S : Set ℂ} (hDS : D ⊆ S)
    (μ : DomainMeasurableBeltramiSpace S) :
    MemLp μ (⊤ : ℝ≥0∞) (volume.restrict D) :=
  memLp_top_of_bound
    (AEStronglyMeasurable.mono_set hDS (Lp.aestronglyMeasurable μ)) ‖μ‖
    (ae_restrict_of_ae_restrict_of_subset hDS (lpInfinity_norm_ae_le μ))

/-- The genuine restriction class. -/
def restrictClass {D S : Set ℂ} (hDS : D ⊆ S)
    (μ : DomainMeasurableBeltramiSpace S) : DomainMeasurableBeltramiSpace D :=
  (restrictMemLp hDS μ).toLp μ

theorem restrictClass_coe_ae {D S : Set ℂ} (hDS : D ⊆ S)
    (μ : DomainMeasurableBeltramiSpace S) :
    restrictClass hDS μ =ᵐ[volume.restrict D] μ :=
  (restrictMemLp hDS μ).coeFn_toLp

theorem norm_restrictClass_le {D S : Set ℂ} (hDS : D ⊆ S)
    (μ : DomainMeasurableBeltramiSpace S) : ‖restrictClass hDS μ‖ ≤ ‖μ‖ := by
  apply lpInfinity_norm_le_of_ae_bound _ (norm_nonneg μ)
  filter_upwards [restrictClass_coe_ae hDS μ,
    ae_restrict_of_ae_restrict_of_subset hDS (lpInfinity_norm_ae_le μ)] with z hz hb
  rw [hz]
  exact hb

/-- Complex linearity of actual restricted L-infinity classes. -/
def restrictionLinear {D S : Set ℂ} (hDS : D ⊆ S) :
    DomainMeasurableBeltramiSpace S →ₗ[ℂ] DomainMeasurableBeltramiSpace D where
  toFun := restrictClass hDS
  map_add' μ ν := by
    apply Lp.ext
    filter_upwards [restrictClass_coe_ae hDS (μ + ν), restrictClass_coe_ae hDS μ,
      restrictClass_coe_ae hDS ν, Lp.coeFn_add (restrictClass hDS μ) (restrictClass hDS ν),
      ae_restrict_of_ae_restrict_of_subset hDS (Lp.coeFn_add μ ν)] with z hsum hμ hν hout hin
    change (μ + ν) z = μ z + ν z at hin
    change (restrictClass hDS μ + restrictClass hDS ν) z =
      restrictClass hDS μ z + restrictClass hDS ν z at hout
    rw [hsum, hout, hin, hμ, hν]
  map_smul' a μ := by
    apply Lp.ext
    filter_upwards [restrictClass_coe_ae hDS (a • μ), restrictClass_coe_ae hDS μ,
      Lp.coeFn_smul a (restrictClass hDS μ),
      ae_restrict_of_ae_restrict_of_subset hDS (Lp.coeFn_smul a μ)] with z hsmul hμ hout hin
    change (a • μ) z = a * μ z at hin
    change (a • restrictClass hDS μ) z = a * restrictClass hDS μ z at hout
    change restrictClass hDS (a • μ) z = (a • restrictClass hDS μ) z
    rw [hsmul, hout, hin, hμ]

/-- Restriction is an actual contraction. -/
def restriction {D S : Set ℂ} (hDS : D ⊆ S) :
    DomainMeasurableBeltramiSpace S →L[ℂ] DomainMeasurableBeltramiSpace D :=
  (restrictionLinear hDS).mkContinuous 1 fun μ => by
    change ‖restrictClass hDS μ‖ ≤ 1 * ‖μ‖
    simpa only [one_mul] using norm_restrictClass_le hDS μ

/-- The actual weighted overlap coefficient is a bounded measurable coefficient. -/
theorem changeMemLp {A : RiemannAtlas X} (e f : Chart A)
    (μ : DomainMeasurableBeltramiSpace f.val.target) :
    MemLp (fun z => μ ((e.val.symm.trans f.val) z) *
      RiemannAtlas.transitionBeltramiPhase e.val f.val z)
      (⊤ : ℝ≥0∞) (volume.restrict (e.val.symm.trans f.val).source) :=
  DomainMeasurableBeltramiBall.coefficientMemLp
    (A.transition_isBeltramiCoeff e.val f.val e.property f.property
      (DomainMeasurableBeltramiSpace.isBeltramiCoeff μ))

/-- The genuine overlap class with the actual Beltrami tensor factor. -/
def changeClass {A : RiemannAtlas X} (e f : Chart A)
    (μ : DomainMeasurableBeltramiSpace f.val.target) :
    DomainMeasurableBeltramiSpace (e.val.symm.trans f.val).source :=
  (changeMemLp e f μ).toLp (fun z => μ ((e.val.symm.trans f.val) z) *
    RiemannAtlas.transitionBeltramiPhase e.val f.val z)

theorem changeClass_coe_ae {A : RiemannAtlas X} (e f : Chart A)
    (μ : DomainMeasurableBeltramiSpace f.val.target) :
    changeClass e f μ =ᵐ[volume.restrict (e.val.symm.trans f.val).source]
      fun z => μ ((e.val.symm.trans f.val) z) *
        RiemannAtlas.transitionBeltramiPhase e.val f.val z :=
  (changeMemLp e f μ).coeFn_toLp

theorem norm_changeClass_le {A : RiemannAtlas X} (e f : Chart A)
    (μ : DomainMeasurableBeltramiSpace f.val.target) : ‖changeClass e f μ‖ ≤ ‖μ‖ := by
  apply lpInfinity_norm_le_of_ae_bound _ (norm_nonneg μ)
  have hb := (A.transition_isBeltramiCoeff e.val f.val e.property f.property
    (DomainMeasurableBeltramiSpace.isBeltramiCoeff μ)).2
  filter_upwards [changeClass_coe_ae e f μ, hb] with z hz hbz
  rw [hz]
  exact hbz

/-- Actual change of coordinates is complex linear on a.e. classes. -/
def changeLinear {A : RiemannAtlas X} (e f : Chart A) :
    DomainMeasurableBeltramiSpace f.val.target →ₗ[ℂ]
      DomainMeasurableBeltramiSpace (e.val.symm.trans f.val).source where
  toFun := changeClass e f
  map_add' μ ν := by
    apply Lp.ext
    filter_upwards [changeClass_coe_ae e f (μ + ν), changeClass_coe_ae e f μ,
      changeClass_coe_ae e f ν, Lp.coeFn_add (changeClass e f μ) (changeClass e f ν),
      A.transition_ae_pullback e.val f.val e.property f.property (Lp.coeFn_add μ ν)]
      with z hsum hμ hν hout hin
    change (μ + ν) ((e.val.symm.trans f.val) z) =
      μ ((e.val.symm.trans f.val) z) + ν ((e.val.symm.trans f.val) z) at hin
    change (changeClass e f μ + changeClass e f ν) z =
      changeClass e f μ z + changeClass e f ν z at hout
    rw [hsum, hout, hin, hμ, hν]
    exact add_mul _ _ _
  map_smul' a μ := by
    apply Lp.ext
    filter_upwards [changeClass_coe_ae e f (a • μ), changeClass_coe_ae e f μ,
      Lp.coeFn_smul a (changeClass e f μ),
      A.transition_ae_pullback e.val f.val e.property f.property (Lp.coeFn_smul a μ)]
      with z hsmul hμ hout hin
    change (a • μ) ((e.val.symm.trans f.val) z) =
      a * μ ((e.val.symm.trans f.val) z) at hin
    change (a • changeClass e f μ) z = a * changeClass e f μ z at hout
    change changeClass e f (a • μ) z = (a • changeClass e f μ) z
    rw [hsmul, hout, hin, hμ]
    ring

/-- Overlap coordinate change is an actual contraction of L-infinity spaces. -/
def change {A : RiemannAtlas X} (e f : Chart A) :
    DomainMeasurableBeltramiSpace f.val.target →L[ℂ]
      DomainMeasurableBeltramiSpace (e.val.symm.trans f.val).source :=
  (changeLinear e f).mkContinuous 1 fun μ => by
    change ‖changeClass e f μ‖ ≤ 1 * ‖μ‖
    simpa only [one_mul] using norm_changeClass_le e f μ

/-- Restrict the source coefficient of a bounded full-atlas family to the overlap. -/
def leftOverlap {A : RiemannAtlas X} (e f : Chart A) :
    Ambient A →L[ℂ] DomainMeasurableBeltramiSpace (e.val.symm.trans f.val).source :=
  (restriction (fun _ hz => hz.1)).comp
    (lp.evalCLM ℂ (fun g : Chart A => DomainMeasurableBeltramiSpace g.val.target) ⊤ e)

/-- Transport the other coefficient of the same family to that exact overlap. -/
def rightOverlap {A : RiemannAtlas X} (e f : Chart A) :
    Ambient A →L[ℂ] DomainMeasurableBeltramiSpace (e.val.symm.trans f.val).source :=
  (change e f).comp
    (lp.evalCLM ℂ (fun g : Chart A => DomainMeasurableBeltramiSpace g.val.target) ⊤ f)

/-- Full original-atlas almost-everywhere tensor compatibility. -/
def compatibleSubmodule (A : RiemannAtlas X) : Submodule ℂ (Ambient A) where
  carrier := {μ | ∀ e f : Chart A, leftOverlap e f μ = rightOverlap e f μ}
  zero_mem' := by
    intro e f
    rw [map_zero, map_zero]
  add_mem' := by
    intro μ ν hμ hν e f
    rw [map_add, map_add, hμ e f, hν e f]
  smul_mem' := by
    intro a μ hμ e f
    rw [map_smul, map_smul, hμ e f]

/-- Tensor compatibility is a family of closed continuous-linear equalizers. -/
theorem isClosed_compatibleSubmodule (A : RiemannAtlas X) :
    IsClosed (compatibleSubmodule A : Set (Ambient A)) := by
  change IsClosed {μ : Ambient A | ∀ e f : Chart A, leftOverlap e f μ = rightOverlap e f μ}
  simp_rw [ofPred_forall]
  exact isClosed_iInter fun e => isClosed_iInter fun f =>
    isClosed_eq (leftOverlap e f).continuous (rightOverlap e f).continuous

/-- The actual measurable full-atlas Beltrami Banach space. -/
def compatibleClosedSubmodule (A : RiemannAtlas X) : ClosedSubmodule ℂ (Ambient A) :=
  ⟨compatibleSubmodule A, isClosed_compatibleSubmodule A⟩

abbrev Space (A : RiemannAtlas X) := ↥(compatibleClosedSubmodule A)
abbrev Ball (A : RiemannAtlas X) := ↥(Metric.ball (0 : Space A) 1)

/-- Completeness follows from the actual complete bounded product and closedness. -/
theorem completeSpace (A : RiemannAtlas X) : CompleteSpace (Space A) := inferInstance

/-- The closed-space equations are exactly the genuine all-original-chart AE law. -/
theorem mem_compatibleSubmodule_iff {A : RiemannAtlas X} (μ : Ambient A) :
    μ ∈ compatibleSubmodule A ↔ ∀ e f : Chart A,
      ∀ᵐ z ∂(volume.restrict (e.val.symm.trans f.val).source),
        μ e z = μ f ((e.val.symm.trans f.val) z) *
          RiemannAtlas.transitionBeltramiPhase e.val f.val z := by
  constructor
  · intro h e f
    have hl := restrictClass_coe_ae
      (fun _ hz => hz.1 : (e.val.symm.trans f.val).source ⊆ e.val.target) (μ e)
    change leftOverlap e f μ =ᵐ[volume.restrict (e.val.symm.trans f.val).source] μ e at hl
    rw [h e f] at hl
    have hr := changeClass_coe_ae e f (μ f)
    change rightOverlap e f μ =ᵐ[volume.restrict (e.val.symm.trans f.val).source]
      (fun z => μ f ((e.val.symm.trans f.val) z) *
        RiemannAtlas.transitionBeltramiPhase e.val f.val z) at hr
    exact hl.symm.trans hr
  · intro h e f
    apply Lp.ext
    change restrictClass
      (fun _ hz => hz.1 : (e.val.symm.trans f.val).source ⊆ e.val.target) (μ e)
      =ᵐ[volume.restrict (e.val.symm.trans f.val).source] changeClass e f (μ f)
    have hlaw : (μ e : ℂ → ℂ) =ᵐ[volume.restrict (e.val.symm.trans f.val).source]
        fun z => μ f ((e.val.symm.trans f.val) z) *
          RiemannAtlas.transitionBeltramiPhase e.val f.val z := h e f
    exact (restrictClass_coe_ae
      (fun _ hz => hz.1 : (e.val.symm.trans f.val).source ⊆ e.val.target) (μ e)).trans
      (hlaw.trans (changeClass_coe_ae e f (μ f)).symm)

/-- Each actual original chart has a genuine restricted-area measurable coefficient class. -/
def coeff {A : RiemannAtlas X} (μ : Space A) (e : Chart A) :
    DomainMeasurableBeltramiSpace e.val.target := μ.val e

theorem compatible {A : RiemannAtlas X} (μ : Space A) (e f : Chart A) :
    ∀ᵐ z ∂(volume.restrict (e.val.symm.trans f.val).source),
      coeff μ e z = coeff μ f ((e.val.symm.trans f.val) z) *
        RiemannAtlas.transitionBeltramiPhase e.val f.val z :=
  (mem_compatibleSubmodule_iff μ.val).1 μ.property e f

/-- The intrinsic Banach norm is exactly the common essential bound in every original chart. -/
theorem norm_le_iff {A : RiemannAtlas X} (μ : Space A) {k : ℝ} (hk : 0 ≤ k) :
    ‖μ‖ ≤ k ↔ ∀ e : Chart A, ∀ᵐ z ∂(volume.restrict e.val.target), ‖coeff μ e z‖ ≤ k := by
  constructor
  · intro h e
    filter_upwards [lpInfinity_norm_ae_le (coeff μ e)] with z hz
    exact hz.trans ((lp.norm_apply_le_norm ENNReal.top_ne_zero μ.val e).trans h)
  · intro h
    apply lp.norm_le_of_forall_le hk
    intro e
    exact lpInfinity_norm_le_of_ae_bound (coeff μ e) hk (h e)

/-- The actual open unit ball is precisely one strict common AE coefficient bound. -/
theorem norm_lt_one_iff {A : RiemannAtlas X} (μ : Space A) :
    ‖μ‖ < 1 ↔ ∃ k : ℝ, 0 ≤ k ∧ k < 1 ∧
      ∀ e : Chart A, LiZhongQC.IsBeltramiCoeff (coeff μ e) e.val.target k := by
  constructor
  · intro h
    exact ⟨‖μ‖, norm_nonneg μ, h, fun e =>
      ⟨Lp.aestronglyMeasurable (coeff μ e), (norm_le_iff μ (norm_nonneg μ)).1 le_rfl e⟩⟩
  · rintro ⟨k, hk₀, hk, hμ⟩
    exact ((norm_le_iff μ hk₀).2 (fun e => (hμ e).2)).trans_lt hk

end LowDimensionalTopology.Geometry.Teichmuller.AtlasMeasurableBeltrami
