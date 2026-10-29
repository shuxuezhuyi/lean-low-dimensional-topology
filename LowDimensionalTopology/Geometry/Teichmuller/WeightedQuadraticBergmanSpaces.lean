module

public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.SeparableMeasure
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Full weighted holomorphic spaces on the disc and half-plane

The carriers contain all weighted square-integrable holomorphic functions,
represented in the actual weighted L² spaces. Holomorphic representatives agree
at every point of the original open domain. The norm and Hermitian pairing are
the literal weighted planar integrals. Completeness, separability and reproducing
formulas are separate theorems, and are not fields of these definitions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ComplexConjugate ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman

/-- The inverse square of the curvature -1 disc density. -/
def diskWeight (z : ℂ) : ℝ≥0 :=
  ⟨(1 - ‖z‖ ^ 2) ^ 2 / 4, div_nonneg (sq_nonneg _) (by norm_num)⟩

/-- The inverse square of the curvature -1 half-plane density. -/
def halfPlaneWeight (z : ℂ) : ℝ≥0 := ⟨z.im ^ 2, sq_nonneg _⟩

theorem diskWeight_measurable : Measurable diskWeight := by
  unfold diskWeight
  fun_prop

theorem halfPlaneWeight_measurable : Measurable halfPlaneWeight := by
  unfold halfPlaneWeight
  fun_prop

theorem diskWeight_pos {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    0 < diskWeight z := by
  have hnorm : ‖z‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  have hsq : ‖z‖ ^ 2 < 1 := by rwa [sq_lt_one_iff_abs_lt_one, abs_norm]
  change 0 < (1 - ‖z‖ ^ 2) ^ 2 / 4
  exact div_pos (sq_pos_of_pos (sub_pos.mpr hsq)) (by norm_num)

theorem halfPlaneWeight_pos {z : ℂ} (hz : 0 < z.im) : 0 < halfPlaneWeight z :=
  sq_pos_of_pos hz

/-- Planar area restricted to the actual domain, with its specified weight. -/
def weightedMeasure (Ω : Set ℂ) (w : ℂ → ℝ≥0) : Measure ℂ :=
  (volume.restrict Ω).withDensity (fun z => w z)

abbrev diskMeasure : Measure ℂ := weightedMeasure (Metric.ball 0 1) diskWeight
abbrev halfPlaneMeasure : Measure ℂ := weightedMeasure {z : ℂ | 0 < z.im} halfPlaneWeight

/-- Classes admitting an actual holomorphic representative on the given domain.
There is no boundedness, boundary regularity or closedness condition. -/
def holomorphicL2Submodule (Ω : Set ℂ) (μ : Measure ℂ) : Submodule ℂ (Lp ℂ 2 μ) where
  carrier := {q | ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Ω ∧ q =ᵐ[μ] φ}
  zero_mem' := ⟨0, differentiableOn_const 0, Lp.coeFn_zero ℂ 2 μ⟩
  add_mem' := by
    rintro q r ⟨φ, hφ, hq⟩ ⟨ψ, hψ, hr⟩
    refine ⟨φ + ψ, hφ.add hψ, ?_⟩
    filter_upwards [Lp.coeFn_add q r, hq, hr] with z hqr hzφ hzψ
    simpa only [Pi.add_apply, hzφ, hzψ] using hqr
  smul_mem' := by
    rintro a q ⟨φ, hφ, hq⟩
    refine ⟨a • φ, hφ.const_smul a, ?_⟩
    filter_upwards [Lp.coeFn_smul a q, hq] with z ha hz
    simpa only [Pi.smul_apply, hz] using ha

/-- All holomorphic weighted-square-integrable disc functions. -/
abbrev Disk := ↥(holomorphicL2Submodule (Metric.ball 0 1) diskMeasure)

/-- All holomorphic weighted-square-integrable half-plane functions. -/
abbrev HalfPlane := ↥(holomorphicL2Submodule {z : ℂ | 0 < z.im} halfPlaneMeasure)

/-- The actual disc space inherits second countability from its weighted L² ambient space. -/
instance instSecondCountableTopologyDisk : SecondCountableTopology Disk := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  let : SigmaFinite diskMeasure :=
    SigmaFinite.withDensity (μ := volume.restrict (Metric.ball (0 : ℂ) 1)) diskWeight
  let : MeasureTheory.IsSeparable diskMeasure := isSeparable_of_sigmaFinite diskMeasure
  let : SecondCountableTopology (Lp ℂ 2 diskMeasure) := Lp.SecondCountableTopology
  exact TopologicalSpace.Subtype.secondCountableTopology
    (holomorphicL2Submodule (Metric.ball 0 1) diskMeasure : Set (Lp ℂ 2 diskMeasure))

/-- The actual half-plane space inherits second countability from weighted L². -/
instance instSecondCountableTopologyHalfPlane : SecondCountableTopology HalfPlane := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨ENNReal.ofNat_ne_top⟩
  let : SigmaFinite halfPlaneMeasure :=
    SigmaFinite.withDensity (μ := volume.restrict {z : ℂ | 0 < z.im}) halfPlaneWeight
  let : MeasureTheory.IsSeparable halfPlaneMeasure := isSeparable_of_sigmaFinite halfPlaneMeasure
  let : SecondCountableTopology (Lp ℂ 2 halfPlaneMeasure) := Lp.SecondCountableTopology
  exact TopologicalSpace.Subtype.secondCountableTopology
    (holomorphicL2Submodule {z : ℂ | 0 < z.im} halfPlaneMeasure : Set (Lp ℂ 2 halfPlaneMeasure))

variable {Ω : Set ℂ} {μ : Measure ℂ}

/-- A total representative; only its values on the actual domain are intrinsic. -/
def coefficient (q : holomorphicL2Submodule Ω μ) : ℂ → ℂ := q.property.choose

theorem coefficient_holomorphic (q : holomorphicL2Submodule Ω μ) :
    DifferentiableOn ℂ (coefficient q) Ω := q.property.choose_spec.1

theorem coefficient_ae (q : holomorphicL2Submodule Ω μ) :
    (q.val : ℂ → ℂ) =ᵐ[μ] coefficient q := q.property.choose_spec.2

/-- Every original holomorphic function with the genuine finite L² norm is retained. -/
def ofFunction (φ : ℂ → ℂ) (hφ : DifferentiableOn ℂ φ Ω) (hφLp : MemLp φ 2 μ) :
    holomorphicL2Submodule Ω μ :=
  ⟨hφLp.toLp φ, φ, hφ, hφLp.coeFn_toLp⟩

/-- Holomorphy and the actual L² class prove membership of the chosen coefficient. -/
theorem coefficient_memLp (q : holomorphicL2Submodule Ω μ) :
    MemLp (coefficient q) 2 μ := MemLp.ae_eq (coefficient_ae q) (Lp.memLp q.val)

private theorem holomorphic_eqOn_of_ae (hΩ : IsOpen Ω) (w : ℂ → ℝ≥0)
    (hw : Measurable w) (hpos : ∀ z ∈ Ω, 0 < w z)
    {φ ψ : ℂ → ℂ} (hφ : DifferentiableOn ℂ φ Ω) (hψ : DifferentiableOn ℂ ψ Ω)
    (h : φ =ᵐ[weightedMeasure Ω w] ψ) : EqOn φ ψ Ω := by
  have hd : ∀ᵐ z ∂(volume.restrict Ω), (w z : ℝ≥0∞) ≠ 0 :=
    ae_restrict_of_forall_mem hΩ.measurableSet fun z hz => by
      exact_mod_cast (hpos z hz).ne'
  have he : φ =ᵐ[volume.restrict Ω] ψ :=
    (withDensity_ae_eq hw.coe_nnreal_ennreal.aemeasurable hd).mp h
  exact Measure.eqOn_open_of_ae_eq he hΩ hφ.continuousOn hψ.continuousOn

/-- The exact original coefficient is recovered at every point of the disc. -/
theorem disk_coefficient_eqOn (q : Disk) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ (Metric.ball 0 1)) (hq : q.val =ᵐ[diskMeasure] φ) :
    EqOn (coefficient q) φ (Metric.ball 0 1) :=
  holomorphic_eqOn_of_ae Metric.isOpen_ball diskWeight diskWeight_measurable
    (fun _ hz => diskWeight_pos hz) (coefficient_holomorphic q) hφ
    ((coefficient_ae q).symm.trans hq)

/-- The exact original coefficient is recovered at every point of the half-plane. -/
theorem halfPlane_coefficient_eqOn (q : HalfPlane) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ {z : ℂ | 0 < z.im}) (hq : q.val =ᵐ[halfPlaneMeasure] φ) :
    EqOn (coefficient q) φ {z : ℂ | 0 < z.im} :=
  holomorphic_eqOn_of_ae (isOpen_lt continuous_const Complex.continuous_im)
    halfPlaneWeight halfPlaneWeight_measurable (fun _ hz => halfPlaneWeight_pos hz)
    (coefficient_holomorphic q) hφ ((coefficient_ae q).symm.trans hq)

/-- The disc constructor retains every value of the original holomorphic function. -/
theorem disk_coefficient_ofFunction (φ : ℂ → ℂ)
    (hφ : DifferentiableOn ℂ φ (Metric.ball 0 1)) (hφLp : MemLp φ 2 diskMeasure) :
    EqOn (coefficient (ofFunction φ hφ hφLp)) φ (Metric.ball 0 1) :=
  disk_coefficient_eqOn (ofFunction φ hφ hφLp) hφ hφLp.coeFn_toLp

/-- The half-plane constructor retains every value of the original holomorphic function. -/
theorem halfPlane_coefficient_ofFunction (φ : ℂ → ℂ)
    (hφ : DifferentiableOn ℂ φ {z : ℂ | 0 < z.im}) (hφLp : MemLp φ 2 halfPlaneMeasure) :
    EqOn (coefficient (ofFunction φ hφ hφLp)) φ {z : ℂ | 0 < z.im} :=
  halfPlane_coefficient_eqOn (ofFunction φ hφ hφLp) hφ hφLp.coeFn_toLp

/-- The first-linear convention is the native inner product with exchanged slots. -/
def pairing (q r : holomorphicL2Submodule Ω μ) : ℂ := inner ℂ r q

private theorem pairing_integrable (q r : holomorphicL2Submodule Ω μ) :
    Integrable (fun z => coefficient q z * conj (coefficient r z)) μ := by
  refine (L2.integrable_inner (𝕜 := ℂ) r.val q.val).congr ?_
  filter_upwards [coefficient_ae q, coefficient_ae r] with z hq hr
  simp only [hq, hr, RCLike.inner_apply]

private theorem pairing_eq_integral (Ω : Set ℂ) (w : ℂ → ℝ≥0) (hw : Measurable w)
    (q r : holomorphicL2Submodule Ω (weightedMeasure Ω w)) :
    pairing q r = ∫ z in Ω, (w z : ℂ) * coefficient q z * conj (coefficient r z) := by
  change inner ℂ r.val q.val = _
  rw [L2.inner_def]
  calc
    (∫ z, inner ℂ (r.val z) (q.val z) ∂weightedMeasure Ω w) =
        ∫ z, coefficient q z * conj (coefficient r z) ∂weightedMeasure Ω w := by
      apply integral_congr_ae
      filter_upwards [coefficient_ae q, coefficient_ae r] with z hq hr
      simp only [hq, hr, RCLike.inner_apply]
    _ = _ := by
      unfold weightedMeasure
      rw [integral_withDensity_eq_integral_smul hw]
      simp only [NNReal.smul_def, Complex.real_smul, mul_assoc]

private theorem weighted_pairing_integrable (Ω : Set ℂ) (w : ℂ → ℝ≥0) (hw : Measurable w)
    (q r : holomorphicL2Submodule Ω (weightedMeasure Ω w)) :
    IntegrableOn (fun z => (w z : ℂ) * coefficient q z * conj (coefficient r z)) Ω := by
  have hi := (integrable_withDensity_iff_integrable_coe_smul hw).mp (pairing_integrable q r)
  simpa only [IntegrableOn, Complex.real_smul, mul_assoc] using hi

private theorem norm_sq_eq_integral (Ω : Set ℂ) (w : ℂ → ℝ≥0) (hw : Measurable w)
    (q : holomorphicL2Submodule Ω (weightedMeasure Ω w)) :
    ‖q‖ ^ 2 = ∫ z in Ω, (w z : ℝ) * ‖coefficient q z‖ ^ 2 := by
  have hs : pairing q q = ((∫ z in Ω, (w z : ℝ) * ‖coefficient q z‖ ^ 2 : ℝ) : ℂ) := by
    rw [pairing_eq_integral Ω w hw]
    calc
      (∫ z in Ω, (w z : ℂ) * coefficient q z * conj (coefficient q z)) =
          ∫ z in Ω, (((w z : ℝ) * ‖coefficient q z‖ ^ 2 : ℝ) : ℂ) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          simp only [mul_assoc, Complex.mul_conj', Complex.ofReal_mul, Complex.ofReal_pow]
      _ = _ := integral_ofReal
  have hn := norm_sq_eq_re_inner (𝕜 := ℂ) q
  change ‖q‖ ^ 2 = (pairing q q).re at hn
  rw [hs, Complex.ofReal_re] at hn
  exact hn

theorem disk_pairing_eq_integral (q r : Disk) :
    pairing q r = ∫ z in Metric.ball (0 : ℂ) 1,
      (diskWeight z : ℂ) * coefficient q z * conj (coefficient r z) :=
  pairing_eq_integral _ _ diskWeight_measurable q r

theorem halfPlane_pairing_eq_integral (q r : HalfPlane) :
    pairing q r = ∫ z in {z : ℂ | 0 < z.im},
      (halfPlaneWeight z : ℂ) * coefficient q z * conj (coefficient r z) :=
  pairing_eq_integral _ _ halfPlaneWeight_measurable q r

theorem disk_pairing_integrable (q r : Disk) :
    IntegrableOn (fun z => (diskWeight z : ℂ) * coefficient q z * conj (coefficient r z))
      (Metric.ball 0 1) :=
  weighted_pairing_integrable _ _ diskWeight_measurable q r

theorem halfPlane_pairing_integrable (q r : HalfPlane) :
    IntegrableOn (fun z => (halfPlaneWeight z : ℂ) * coefficient q z * conj (coefficient r z))
      {z : ℂ | 0 < z.im} :=
  weighted_pairing_integrable _ _ halfPlaneWeight_measurable q r

theorem disk_norm_sq_eq_integral (q : Disk) :
    ‖q‖ ^ 2 = ∫ z in Metric.ball (0 : ℂ) 1, (diskWeight z : ℝ) * ‖coefficient q z‖ ^ 2 :=
  norm_sq_eq_integral _ _ diskWeight_measurable q

theorem halfPlane_norm_sq_eq_integral (q : HalfPlane) :
    ‖q‖ ^ 2 = ∫ z in {z : ℂ | 0 < z.im}, (halfPlaneWeight z : ℝ) * ‖coefficient q z‖ ^ 2 :=
  norm_sq_eq_integral _ _ halfPlaneWeight_measurable q

end LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman
