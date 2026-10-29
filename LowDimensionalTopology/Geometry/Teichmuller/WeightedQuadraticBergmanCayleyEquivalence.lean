module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergmanCayleyTransport
public import LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergmanCompleteness
public import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The quadratic Cayley isometry between the full original spaces

The forward and inverse quadratic pullbacks retain every coefficient value on
their original domains. Their actual derivatives prove both inverse identities;
the genuine weighted L² membership and norms then give a complex linear isometry
equivalence. The book's first-linear pairing is preserved, and completeness of
the disc space follows from the proved half-plane completeness theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped ComplexConjugate ENNReal NNReal UpperHalfPlane Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman

open LowDimensionalTopology.Geometry.Hyperbolic

/-- Forward quadratic pullback uses the square of the actual Cayley derivative. -/
def cayleyPullback (φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  φ (cayleyFormula z) * cayleyDerivative z ^ 2

theorem cayley_mapsTo :
    MapsTo cayleyFormula {z : ℂ | 0 < z.im} (Metric.ball (0 : ℂ) 1) := by
  intro z hz
  exact mem_ball_zero_iff.mpr (cayley_mem_disc (UpperHalfPlane.mk z hz))

theorem cayley_inverseCayley {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    cayleyFormula (inverseCayleyFormula z) = z := by
  exact congrArg ((↑) : 𝔻 → ℂ) (halfPlaneToDisc_discToHalfPlane
    (Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz)))

theorem inverseCayley_cayley {z : ℂ} (hz : 0 < z.im) :
    inverseCayleyFormula (cayleyFormula z) = z := by
  exact congrArg ((↑) : ℍ → ℂ)
    (discToHalfPlane_halfPlaneToDisc (UpperHalfPlane.mk z hz))

/-- The actual derivatives of the inverse formulas have product one on the disc. -/
theorem cayleyDerivative_inverseCayley {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    cayleyDerivative (inverseCayleyFormula z) * inverseCayleyDerivative z = 1 := by
  have hn : 1 - z ≠ 0 := inverseCayley_denom_ne_zero
    (Complex.UnitDisc.mk z (mem_ball_zero_iff.mp hz))
  have hden : inverseCayleyFormula z + Complex.I = (2 * Complex.I) / (1 - z) := by
    unfold inverseCayleyFormula
    field_simp [hn]
    ring
  unfold cayleyDerivative inverseCayleyDerivative
  rw [hden, div_pow]
  field_simp [hn, Complex.I_ne_zero]

/-- The reverse derivative product is one at every original half-plane point. -/
theorem inverseCayleyDerivative_cayley {z : ℂ} (hz : 0 < z.im) :
    inverseCayleyDerivative (cayleyFormula z) * cayleyDerivative z = 1 := by
  have hn : z + Complex.I ≠ 0 := cayley_denom_ne_zero (UpperHalfPlane.mk z hz)
  have hden : 1 - cayleyFormula z = (2 * Complex.I) / (z + Complex.I) := by
    unfold cayleyFormula
    field_simp [hn]
    ring
  unfold inverseCayleyDerivative cayleyDerivative
  rw [hden, div_pow]
  field_simp [hn, Complex.I_ne_zero]

/-- Both squared derivative factors cancel at every original disc point. -/
theorem inverseCayleyPullback_cayleyPullback (φ : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    inverseCayleyPullback (cayleyPullback φ) z = φ z := by
  change (φ (cayleyFormula (inverseCayleyFormula z)) *
    cayleyDerivative (inverseCayleyFormula z) ^ 2) * inverseCayleyDerivative z ^ 2 = φ z
  rw [cayley_inverseCayley hz, mul_assoc, ← mul_pow,
    cayleyDerivative_inverseCayley hz, one_pow, mul_one]

/-- Both squared derivative factors cancel at every original half-plane point. -/
theorem cayleyPullback_inverseCayleyPullback (ψ : ℂ → ℂ) {z : ℂ} (hz : 0 < z.im) :
    cayleyPullback (inverseCayleyPullback ψ) z = ψ z := by
  change (ψ (inverseCayleyFormula (cayleyFormula z)) *
    inverseCayleyDerivative (cayleyFormula z) ^ 2) * cayleyDerivative z ^ 2 = ψ z
  rw [inverseCayley_cayley hz, mul_assoc, ← mul_pow,
    inverseCayleyDerivative_cayley hz, one_pow, mul_one]

theorem cayleyPullback_holomorphic {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1)) :
    DifferentiableOn ℂ (cayleyPullback φ) {z : ℂ | 0 < z.im} := by
  have hT : DifferentiableOn ℂ cayleyFormula {z : ℂ | 0 < z.im} := by
    intro z hz
    exact (hasDerivAt_cayleyFormula (UpperHalfPlane.mk z hz)).differentiableAt.differentiableWithinAt
  have hd : DifferentiableOn ℂ cayleyDerivative {z : ℂ | 0 < z.im} := by
    unfold cayleyDerivative
    refine (differentiableOn_const _).div
      ((differentiableOn_id.add (differentiableOn_const Complex.I)).pow 2) ?_
    intro z hz
    exact pow_ne_zero 2 (cayley_denom_ne_zero (UpperHalfPlane.mk z hz))
  exact (hφ.fun_comp hT cayley_mapsTo).mul (hd.pow 2)

/-- Genuine forward L² membership follows from the proved inverse change of variables. -/
theorem cayleyPullback_memLp {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ (Metric.ball (0 : ℂ) 1)) (hφLp : MemLp φ 2 diskMeasure) :
    MemLp (cayleyPullback φ) 2 halfPlaneMeasure := by
  have hpoint : EqOn (inverseCayleyPullback (cayleyPullback φ)) φ
      (Metric.ball (0 : ℂ) 1) := fun z hz => inverseCayleyPullback_cayleyPullback φ hz
  have he : inverseCayleyPullback (cayleyPullback φ) =ᵐ[diskMeasure] φ :=
    (withDensity_absolutelyContinuous (volume.restrict (Metric.ball (0 : ℂ) 1))
      (fun z => (diskWeight z : ℝ≥0∞))).ae_eq
        (hpoint.aeEq_restrict measurableSet_ball)
  exact (inverseCayleyPullback_memLp_iff (cayleyPullback_holomorphic hφ)).mpr
    (MemLp.ae_eq he.symm hφLp)

private theorem weighted_coefficient_ext {Ω : Set ℂ} {w : ℂ → ℝ≥0}
    (hΩ : MeasurableSet Ω) {q r : holomorphicL2Submodule Ω (weightedMeasure Ω w)}
    (h : EqOn (coefficient q) (coefficient r) Ω) : q = r := by
  apply Subtype.ext
  apply Lp.ext
  have he : coefficient q =ᵐ[weightedMeasure Ω w] coefficient r :=
    (withDensity_absolutelyContinuous (volume.restrict Ω) (fun z => (w z : ℝ≥0∞))).ae_eq
      (h.aeEq_restrict hΩ)
  exact (coefficient_ae q).trans (he.trans (coefficient_ae r).symm)

theorem disk_coefficient_ext {q r : Disk}
    (h : EqOn (coefficient q) (coefficient r) (Metric.ball (0 : ℂ) 1)) : q = r :=
  weighted_coefficient_ext measurableSet_ball h

theorem halfPlane_coefficient_ext {q r : HalfPlane}
    (h : EqOn (coefficient q) (coefficient r) {z : ℂ | 0 < z.im}) : q = r :=
  weighted_coefficient_ext (isOpen_lt continuous_const Complex.continuous_im).measurableSet h

private theorem disk_coefficient_linear (a b : ℂ) (q r : Disk) :
    EqOn (coefficient (a • q + b • r))
      (fun z => a * coefficient q z + b * coefficient r z) (Metric.ball (0 : ℂ) 1) := by
  refine disk_coefficient_eqOn (a • q + b • r)
    (((differentiableOn_const a).mul (coefficient_holomorphic q)).add
      ((differentiableOn_const b).mul (coefficient_holomorphic r))) ?_
  change ((a • q.val + b • r.val : Lp ℂ 2 diskMeasure) : ℂ → ℂ) =ᵐ[diskMeasure]
    fun z => a * coefficient q z + b * coefficient r z
  filter_upwards [Lp.coeFn_add (a • q.val) (b • r.val), Lp.coeFn_smul a q.val,
    Lp.coeFn_smul b r.val, coefficient_ae q, coefficient_ae r] with z hs ha hb hq hr
  simpa only [Pi.add_apply, ha, hb, Pi.smul_apply, smul_eq_mul, hq, hr] using hs

private theorem halfPlane_coefficient_linear (a b : ℂ) (q r : HalfPlane) :
    EqOn (coefficient (a • q + b • r))
      (fun z => a * coefficient q z + b * coefficient r z) {z : ℂ | 0 < z.im} := by
  refine halfPlane_coefficient_eqOn (a • q + b • r)
    (((differentiableOn_const a).mul (coefficient_holomorphic q)).add
      ((differentiableOn_const b).mul (coefficient_holomorphic r))) ?_
  change ((a • q.val + b • r.val : Lp ℂ 2 halfPlaneMeasure) : ℂ → ℂ) =ᵐ[halfPlaneMeasure]
    fun z => a * coefficient q z + b * coefficient r z
  filter_upwards [Lp.coeFn_add (a • q.val) (b • r.val), Lp.coeFn_smul a q.val,
    Lp.coeFn_smul b r.val, coefficient_ae q, coefficient_ae r] with z hs ha hb hq hr
  simpa only [Pi.add_apply, ha, hb, Pi.smul_apply, smul_eq_mul, hq, hr] using hs

/-- Every original disc element has a genuine original half-plane quadratic pullback. -/
def cayleyPullbackElement (q : Disk) : HalfPlane :=
  ofFunction (cayleyPullback (coefficient q))
    (cayleyPullback_holomorphic (coefficient_holomorphic q))
    (cayleyPullback_memLp (coefficient_holomorphic q) (coefficient_memLp q))

theorem cayleyPullbackElement_coefficient (q : Disk) :
    EqOn (coefficient (cayleyPullbackElement q))
      (cayleyPullback (coefficient q)) {z : ℂ | 0 < z.im} := by
  unfold cayleyPullbackElement
  exact halfPlane_coefficient_ofFunction _ _ _

/-- The inverse identity holds on the whole original disc carrier. -/
theorem inverseCayleyPullbackElement_cayleyPullbackElement (q : Disk) :
    inverseCayleyPullbackElement (cayleyPullbackElement q) = q := by
  apply disk_coefficient_ext
  intro z hz
  calc
    coefficient (inverseCayleyPullbackElement (cayleyPullbackElement q)) z =
        inverseCayleyPullback (coefficient (cayleyPullbackElement q)) z :=
      inverseCayleyPullbackElement_coefficient (cayleyPullbackElement q) hz
    _ = inverseCayleyPullback (cayleyPullback (coefficient q)) z := by
      change coefficient (cayleyPullbackElement q) (inverseCayleyFormula z) *
        inverseCayleyDerivative z ^ 2 =
        cayleyPullback (coefficient q) (inverseCayleyFormula z) * inverseCayleyDerivative z ^ 2
      rw [cayleyPullbackElement_coefficient q (inverseCayley_mapsTo hz)]
    _ = coefficient q z := inverseCayleyPullback_cayleyPullback (coefficient q) hz

/-- The reverse inverse identity holds on the whole original half-plane carrier. -/
theorem cayleyPullbackElement_inverseCayleyPullbackElement (q : HalfPlane) :
    cayleyPullbackElement (inverseCayleyPullbackElement q) = q := by
  apply halfPlane_coefficient_ext
  intro z hz
  calc
    coefficient (cayleyPullbackElement (inverseCayleyPullbackElement q)) z =
        cayleyPullback (coefficient (inverseCayleyPullbackElement q)) z :=
      cayleyPullbackElement_coefficient (inverseCayleyPullbackElement q) hz
    _ = cayleyPullback (inverseCayleyPullback (coefficient q)) z := by
      change coefficient (inverseCayleyPullbackElement q) (cayleyFormula z) *
        cayleyDerivative z ^ 2 =
        inverseCayleyPullback (coefficient q) (cayleyFormula z) * cayleyDerivative z ^ 2
      rw [inverseCayleyPullbackElement_coefficient q (cayley_mapsTo hz)]
    _ = coefficient q z := cayleyPullback_inverseCayleyPullback (coefficient q) hz

theorem cayleyPullbackElement_add (q r : Disk) :
    cayleyPullbackElement (q + r) = cayleyPullbackElement q + cayleyPullbackElement r := by
  apply halfPlane_coefficient_ext
  intro z hz
  have hD := disk_coefficient_linear 1 1 q r (cayley_mapsTo hz)
  have hH := halfPlane_coefficient_linear 1 1 (cayleyPullbackElement q) (cayleyPullbackElement r) hz
  simp only [one_smul, one_mul] at hD hH
  rw [cayleyPullbackElement_coefficient (q + r) hz, hH,
    cayleyPullbackElement_coefficient q hz, cayleyPullbackElement_coefficient r hz]
  simp only [cayleyPullback]
  rw [hD, add_mul]

theorem cayleyPullbackElement_smul (a : ℂ) (q : Disk) :
    cayleyPullbackElement (a • q) = a • cayleyPullbackElement q := by
  apply halfPlane_coefficient_ext
  intro z hz
  have hD := disk_coefficient_linear a 0 q q (cayley_mapsTo hz)
  have hH := halfPlane_coefficient_linear a 0 (cayleyPullbackElement q) (cayleyPullbackElement q) hz
  simp only [zero_smul, add_zero, zero_mul] at hD hH
  rw [cayleyPullbackElement_coefficient (a • q) hz, hH, cayleyPullbackElement_coefficient q hz]
  simp only [cayleyPullback]
  rw [hD, mul_assoc]

theorem cayleyPullbackElement_norm (q : Disk) : ‖cayleyPullbackElement q‖ = ‖q‖ := by
  calc
    ‖cayleyPullbackElement q‖ =
        ‖inverseCayleyPullbackElement (cayleyPullbackElement q)‖ :=
      (inverseCayleyPullbackElement_norm (cayleyPullbackElement q)).symm
    _ = ‖q‖ := congrArg norm (inverseCayleyPullbackElement_cayleyPullbackElement q)

/-- The actual quadratic pullbacks give a complex linear isometry of the full original spaces. -/
def cayleyLinearIsometryEquiv : Disk ≃ₗᵢ[ℂ] HalfPlane where
  toFun := cayleyPullbackElement
  invFun := inverseCayleyPullbackElement
  left_inv := inverseCayleyPullbackElement_cayleyPullbackElement
  right_inv := cayleyPullbackElement_inverseCayleyPullbackElement
  map_add' := cayleyPullbackElement_add
  map_smul' := cayleyPullbackElement_smul
  norm_map' := cayleyPullbackElement_norm

/-- The forward equivalence retains the quadratic coefficient at every original point. -/
theorem cayleyLinearIsometryEquiv_coefficient (q : Disk) {z : ℂ} (hz : 0 < z.im) :
    coefficient (cayleyLinearIsometryEquiv q) z =
      coefficient q (cayleyFormula z) * cayleyDerivative z ^ 2 := by
  change coefficient (cayleyPullbackElement q) z = _
  exact cayleyPullbackElement_coefficient q hz

/-- The inverse equivalence retains the quadratic coefficient at every original disc point. -/
theorem cayleyLinearIsometryEquiv_symm_coefficient (q : HalfPlane) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    coefficient (cayleyLinearIsometryEquiv.symm q) z =
      coefficient q (inverseCayleyFormula z) * inverseCayleyDerivative z ^ 2 := by
  change coefficient (inverseCayleyPullbackElement q) z = _
  exact inverseCayleyPullbackElement_coefficient q hz

/-- The first-linear book pairing is preserved with its original slot convention. -/
theorem cayleyLinearIsometryEquiv_pairing (q r : Disk) :
    pairing (cayleyLinearIsometryEquiv q) (cayleyLinearIsometryEquiv r) = pairing q r := by
  simpa only [pairing] using cayleyLinearIsometryEquiv.inner_map_map r q

/-- Completeness is transported from the proved full original half-plane space. -/
instance instCompleteSpaceDisk : CompleteSpace Disk :=
  cayleyLinearIsometryEquiv.toIsometryEquiv.completeSpace_iff.mpr instCompleteSpaceHalfPlane

end LowDimensionalTopology.Geometry.Teichmuller.WeightedQuadraticBergman
