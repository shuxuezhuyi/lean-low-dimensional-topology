module

public import LowDimensionalTopology.Geometry.Quasiconformal.CircularHilbertAngularEstimate
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.Normed.Operator.Extend

/-!
# The circular Hilbert estimate and its same-Lp extension

The directional average on smooth compact planar tests is complex linear
as an almost-everywhere class. Its established norm bound extends it along
the dense test inclusion using Mathlib's existing linear extension theorem.
The only analytic premise is the specified real-line Riesz estimate.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff

namespace LowDimensionalTopology.Geometry.Quasiconformal

open LowDimensionalTopology.Unproved.Quasiconformal

private theorem integrableOn_realHilbertKernel {ψ : ℝ → ℂ}
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    IntegrableOn (fun x : ℝ => ψ x / ((x - ξ : ℝ) : ℂ))
      {x : ℝ | ε < |x - ξ|} := by
  have hs : MeasurableSet {x : ℝ | ε < |x - ξ|} := by measurability
  have hi : IntegrableOn ψ {x : ℝ | ε < |x - ξ|} (volume : Measure ℝ) :=
    (hψ.integrable_of_hasCompactSupport hc).restrict
  simp only [div_eq_mul_inv]
  apply hi.mul_bdd (c := ε⁻¹)
  · apply Measurable.aestronglyMeasurable
    fun_prop
  · filter_upwards [ae_restrict_mem hs] with x hx
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
    exact (inv_le_inv₀ (hε.trans hx) hε).mpr hx.le

private theorem realHilbertTransform_add {A : ℝ → ℝ}
    (hA : RealHilbertEstimate A) {p : ℝ} (hp : 2 ≤ p) {ψ χ : ℝ → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hχ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) χ)
    (hcψ : HasCompactSupport ψ) (hcχ : HasCompactSupport χ) (ξ : ℝ) :
    realHilbertTransform (ψ + χ) ξ = realHilbertTransform ψ ξ + realHilbertTransform χ ξ := by
  have hψpv := (hA.2.2 p hp ψ hψ hcψ).1 ξ
  have hχpv := (hA.2.2 p hp χ hχ hcχ).1 ξ
  have hsumpv := (hA.2.2 p hp (ψ + χ) (hψ.add hχ) (hcψ.add hcχ)).1 ξ
  apply tendsto_nhds_unique hsumpv
  apply (hψpv.add hχpv).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hiψ := integrableOn_realHilbertKernel hψ.continuous hcψ ξ hε
  have hiχ := integrableOn_realHilbertKernel hχ.continuous hcχ ξ hε
  simp only [realHilbertTruncation, Pi.add_apply, add_div,
    integral_add hiψ hiχ, mul_add]

private theorem realHilbertTransform_smul {A : ℝ → ℝ}
    (hA : RealHilbertEstimate A) {p : ℝ} (hp : 2 ≤ p) {ψ : ℝ → ℂ}
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hcψ : HasCompactSupport ψ) (c : ℂ) (ξ : ℝ) :
    realHilbertTransform (c • ψ) ξ = c * realHilbertTransform ψ ξ := by
  have hψpv := (hA.2.2 p hp ψ hψ hcψ).1 ξ
  have hcpv := (hA.2.2 p hp (c • ψ) (contDiff_const.smul hψ) hcψ.smul_left).1 ξ
  apply tendsto_nhds_unique hcpv
  apply (tendsto_const_nhds.mul hψpv).congr'
  filter_upwards with ε
  simp only [realHilbertTruncation, Pi.smul_apply, smul_eq_mul, mul_div_assoc,
    integral_const_mul]
  ring

private theorem directionalHilbertTransform_add {A : ℝ → ℝ}
    (hA : RealHilbertEstimate A) {p : ℝ} (hp : 2 ≤ p) {φ ψ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hcφ : HasCompactSupport φ) (hcψ : HasCompactSupport ψ) (θ : ℝ) (ζ : ℂ) :
    directionalHilbertTransform (φ + ψ) θ ζ =
      directionalHilbertTransform φ θ ζ + directionalHilbertTransform ψ θ ζ :=
  realHilbertTransform_add hA hp (contDiff_affineLine hφ θ ζ)
    (contDiff_affineLine hψ θ ζ) (hasCompactSupport_affineLine hcφ θ ζ)
    (hasCompactSupport_affineLine hcψ θ ζ) 0

private theorem directionalHilbertTransform_smul {A : ℝ → ℝ}
    (hA : RealHilbertEstimate A) {p : ℝ} (hp : 2 ≤ p) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hcφ : HasCompactSupport φ) (c : ℂ) (θ : ℝ) (ζ : ℂ) :
    directionalHilbertTransform (c • φ) θ ζ = c * directionalHilbertTransform φ θ ζ :=
  realHilbertTransform_smul hA hp (contDiff_affineLine hφ θ ζ)
    (hasCompactSupport_affineLine hcφ θ ζ) c 0

/-- The literal circular average is additive on smooth compact tests as an
almost-everywhere identity on the original complex plane. -/
theorem circularHilbertTransform_add_ae {A : ℝ → ℝ}
    (hA : RealHilbertEstimate A) {p : ℝ} (hp : 2 ≤ p) {φ ψ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hcφ : HasCompactSupport φ) (hcψ : HasCompactSupport ψ) :
    circularHilbertTransform (φ + ψ) =ᵐ[volume]
      circularHilbertTransform φ + circularHilbertTransform ψ := by
  filter_upwards [ae_integrable_circularHilbertIntegrand hA hp hφ hcφ,
    ae_integrable_circularHilbertIntegrand hA hp hψ hcψ] with ζ hiφ hiψ
  simp only [circularHilbertTransform, intervalIntegral.integral_of_le Real.pi_pos.le,
    Pi.add_apply]
  simp_rw [directionalHilbertTransform_add hA hp hφ hψ hcφ hcψ, add_mul]
  rw [integral_add hiφ hiψ, mul_add]

/-- Complex scalar multiplication commutes with the same actual directional
average on every smooth compact planar test. -/
theorem circularHilbertTransform_smul {A : ℝ → ℝ}
    (hA : RealHilbertEstimate A) {p : ℝ} (hp : 2 ≤ p) {φ : ℂ → ℂ}
    (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ)
    (hcφ : HasCompactSupport φ) (c : ℂ) :
    circularHilbertTransform (c • φ) = c • circularHilbertTransform φ := by
  funext ζ
  simp only [circularHilbertTransform, intervalIntegral.integral_of_le Real.pi_pos.le,
    Pi.smul_apply, smul_eq_mul]
  simp_rw [directionalHilbertTransform_smul hA hp hφ hcφ, mul_assoc]
  rw [integral_const_mul]
  ring

private def circularTestSpace : Submodule ℂ (ℂ → ℂ) where
  carrier := {φ | ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧ HasCompactSupport φ}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' hφ hψ := ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩
  smul_mem' _c _φ hφ := ⟨contDiff_const.smul hφ.1, hφ.2.smul_left⟩

section Extension

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

private def circularTestToLp : circularTestSpace →ₗ[ℂ]
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) where
  toFun φ := (φ.property.1.continuous.memLp_of_hasCompactSupport φ.property.2).toLp φ
  map_add' _ _ := MemLp.toLp_add _ _
  map_smul' c _ := MemLp.toLp_const_smul c _

private theorem circularTestToLp_dense : DenseRange (circularTestToLp (p := p)) := by
  have hd := Lp.dense_hasCompactSupport_contDiff (E := ℂ) (F := ℂ)
    (μ := (volume : Measure ℂ)) (p := ENNReal.ofReal p) ENNReal.ofReal_ne_top
  have heq : Set.range (circularTestToLp (p := p)) =
      {f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) |
        ∃ g : ℂ → ℂ, f =ᵐ[volume] g ∧ HasCompactSupport g ∧ ContDiff ℝ ∞ g} := by
    ext f
    constructor
    · rintro ⟨φ, rfl⟩
      have hmφ : MemLp (φ : ℂ → ℂ) (ENNReal.ofReal p) (volume : Measure ℂ) :=
        φ.property.1.continuous.memLp_of_hasCompactSupport φ.property.2
      exact ⟨(φ : ℂ → ℂ), MemLp.coeFn_toLp hmφ, φ.property.2, φ.property.1⟩
    · rintro ⟨φ, hfφ, hcφ, hφ⟩
      refine ⟨⟨φ, hφ, hcφ⟩, ?_⟩
      apply Lp.ext
      have hmφ : MemLp φ (ENNReal.ofReal p) (volume : Measure ℂ) :=
        hφ.continuous.memLp_of_hasCompactSupport hcφ
      exact (MemLp.coeFn_toLp hmφ).trans hfφ.symm
  change Dense (Set.range (circularTestToLp (p := p)))
  rw [heq]
  exact hd

private def circularTestOperator {A : ℝ → ℝ} (hA : RealHilbertEstimate A) (hp : 2 ≤ p) :
    circularTestSpace →ₗ[ℂ] Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) where
  toFun φ := (circularHilbertTransform_test_bound hA hp φ.property.1 φ.property.2).1.toLp
    (circularHilbertTransform φ)
  map_add' φ ψ := by
    rw [← MemLp.toLp_add]
    apply (MemLp.toLp_eq_toLp_iff _ _).mpr
    exact circularHilbertTransform_add_ae hA hp φ.property.1 ψ.property.1
      φ.property.2 ψ.property.2
  map_smul' c φ := by
    rw [← MemLp.toLp_const_smul]
    apply (MemLp.toLp_eq_toLp_iff _ _).mpr
    apply Filter.Eventually.of_forall
    intro z
    simpa only [Submodule.coe_smul, RingHom.id_apply] using
      congrFun (circularHilbertTransform_smul hA hp φ.property.1 φ.property.2 c) z

omit [Fact (1 ≤ ENNReal.ofReal p)] in
private theorem circularTestOperator_bound {A : ℝ → ℝ} (hA : RealHilbertEstimate A)
    (hp : 2 ≤ p) (φ : circularTestSpace) :
    ‖circularTestOperator hA hp φ‖ ≤
      (Real.pi / 2 * A p) * ‖circularTestToLp (p := p) φ‖ := by
  change ‖(circularHilbertTransform_test_bound hA hp φ.property.1 φ.property.2).1.toLp
    (circularHilbertTransform φ)‖ ≤ _
  rw [Lp.norm_toLp]
  change _ ≤ (Real.pi / 2 * A p) *
    ‖(φ.property.1.continuous.memLp_of_hasCompactSupport φ.property.2).toLp (φ : ℂ → ℂ)‖
  rw [Lp.norm_toLp]
  exact (circularHilbertTransform_test_bound hA hp φ.property.1 φ.property.2).2

end Extension

/-- The circular directional average has the exact same-Lp continuous
complex-linear extension and bound, conditional on the specified real-line
Riesz assertion for its given family of constants. -/
theorem circularHilbertLpEstimate :
    LowDimensionalTopology.Unproved.Quasiconformal.CircularHilbertLpEstimate := by
  intro A hA p hp
  let : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (le_trans (by norm_num : (1 : ℝ) ≤ 2) hp)⟩
  let e := circularTestToLp (p := p)
  let f := circularTestOperator hA hp
  have hd : DenseRange e := circularTestToLp_dense
  have hb (φ : circularTestSpace) : ‖f φ‖ ≤ (Real.pi / 2 * A p) * ‖e φ‖ :=
    circularTestOperator_bound hA hp φ
  let S := f.extendOfNorm e
  refine ⟨S, ?_, ?_, ?_⟩
  · exact LinearMap.opNorm_extendOfNorm_le hd
      (mul_nonneg (by positivity) (RealHilbertEstimate.nonneg hA hp)) hb
  · intro φ hφ hcφ
    let ψ : circularTestSpace := ⟨φ, hφ, hcφ⟩
    have hext : S (e ψ) = f ψ := LinearMap.extendOfNorm_eq hd ⟨_, hb⟩ ψ
    change (S (e ψ) : ℂ → ℂ) =ᵐ[volume] circularHilbertTransform φ
    rw [hext]
    exact MemLp.coeFn_toLp
      (circularHilbertTransform_test_bound hA hp ψ.property.1 ψ.property.2).1
  · intro φ hφ hcφ
    exact circularHilbertTransform_test_bound hA hp hφ hcφ

/-- A genuine real-line Riesz family supplies the same constant family and
actual circular extensions at every stated exponent. Agreement here is with
the directional angular definition of the circular transform. -/
theorem exists_circularHilbertLp_of_realRiesz (hRiesz : RieszRealHilbertEstimate) :
    ∃ A : ℝ → ℝ, ContinuousOn A (Ici 2) ∧ A 2 = 1 ∧ RealHilbertEstimate A ∧
      ∀ (p : ℝ) (hp : 2 ≤ p),
        let : Fact (1 ≤ ENNReal.ofReal p) :=
          ⟨by
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal
              (le_trans (by norm_num : (1 : ℝ) ≤ 2) hp)⟩
        ∃ S : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) →L[ℂ]
            Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ),
          ‖S‖ ≤ Real.pi / 2 * A p ∧ IsCircularHilbertLpExtension p S ∧
          ∀ (φ : ℂ → ℂ),
            ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ →
              MemLp (circularHilbertTransform φ) (ENNReal.ofReal p)
                  (volume : Measure ℂ) ∧
                (eLpNorm (circularHilbertTransform φ) (ENNReal.ofReal p)
                  (volume : Measure ℂ)).toReal ≤
                  (Real.pi / 2 * A p) *
                    (eLpNorm φ (ENNReal.ofReal p) (volume : Measure ℂ)).toReal := by
  obtain ⟨A, hA⟩ := hRiesz
  refine ⟨A, hA.1, hA.2.1, hA, ?_⟩
  intro p hp
  exact circularHilbertLpEstimate A hA p hp

end LowDimensionalTopology.Geometry.Quasiconformal
