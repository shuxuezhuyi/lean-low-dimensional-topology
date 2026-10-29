module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.HolomorphicQuadraticDifferential
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedUniqueness
public import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FunProp

/-!
# Hyperbolic weighted Hermitian integrals

The first slot is complex linear and the second slot is conjugate linear.
Quadratic coefficients have density y^2 against dx dy. Beltrami coefficients
have density y^-2 against dx dy, the genuine upper-half-plane hyperbolic area.

The positivity theorem concerns actual global holomorphic quadratic differentials
pulled back by an actual holomorphic uniformizing covering. Compactness of the
integration set gives integrability; its nonempty interior gives strict positivity.
The module does not identify different fundamental domains or construct variation
of this form over a Teichmuller quotient.
-/

@[expose] public section
noncomputable section

open Set MeasureTheory Filter Topology
open scoped ComplexConjugate UpperHalfPlane Manifold ContDiff NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson

open Surfaces

section WeightedIntegral

variable {Z : Type*} [MeasurableSpace Z]

/-- An actual weighted integral, linear in the first slot. -/
def weightedPairing (m : Measure Z) (w : Z → ℝ) (f g : Z → ℂ) : ℂ :=
  ∫ z, (w z : ℂ) * f z * conj (g z) ∂m

/-- Conjugate symmetry holds even when the Bochner integral is undefined. -/
theorem weightedPairing_conj (m : Measure Z) (w : Z → ℝ) (f g : Z → ℂ) :
    conj (weightedPairing m w f g) = weightedPairing m w g f := by
  rw [weightedPairing, weightedPairing, ← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring

/-- Additivity has precisely the actual integrability premises. -/
theorem weightedPairing_add_left (m : Measure Z) (w : Z → ℝ) (f g h : Z → ℂ)
    (hf : Integrable (fun z => (w z : ℂ) * f z * conj (h z)) m)
    (hg : Integrable (fun z => (w z : ℂ) * g z * conj (h z)) m) :
    weightedPairing m w (f + g) h =
      weightedPairing m w f h + weightedPairing m w g h := by
  unfold weightedPairing
  simp only [Pi.add_apply, mul_add, add_mul]
  exact integral_add hf hg

/-- Additivity in the conjugate-linear slot. -/
theorem weightedPairing_add_right (m : Measure Z) (w : Z → ℝ) (f g h : Z → ℂ)
    (hg : Integrable (fun z => (w z : ℂ) * f z * conj (g z)) m)
    (hh : Integrable (fun z => (w z : ℂ) * f z * conj (h z)) m) :
    weightedPairing m w f (g + h) =
      weightedPairing m w f g + weightedPairing m w f h := by
  unfold weightedPairing
  simp only [Pi.add_apply, map_add, mul_add]
  exact integral_add hg hh

/-- The first slot is complex linear. -/
theorem weightedPairing_smul_left (m : Measure Z) (w : Z → ℝ)
    (a : ℂ) (f g : Z → ℂ) :
    weightedPairing m w (a • f) g = a * weightedPairing m w f g := by
  unfold weightedPairing
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (∫ z, (w z : ℂ) * (a * f z) * conj (g z) ∂m) =
        ∫ z, a * ((w z : ℂ) * f z * conj (g z)) ∂m := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    _ = _ := integral_const_mul a _

/-- The second slot is conjugate linear. -/
theorem weightedPairing_smul_right (m : Measure Z) (w : Z → ℝ)
    (a : ℂ) (f g : Z → ℂ) :
    weightedPairing m w f (a • g) = conj a * weightedPairing m w f g := by
  unfold weightedPairing
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  calc
    (∫ z, (w z : ℂ) * f z * (conj a * conj (g z)) ∂m) =
        ∫ z, conj a * ((w z : ℂ) * f z * conj (g z)) ∂m := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by ring
    _ = _ := integral_const_mul (conj a) _

/-- The diagonal is the real weighted square norm, with its actual integral. -/
theorem weightedPairing_self (m : Measure Z) (w : Z → ℝ) (f : Z → ℂ) :
    weightedPairing m w f f = (∫ z, w z * ‖f z‖ ^ 2 ∂m : ℝ) := by
  unfold weightedPairing
  calc
    (∫ z, (w z : ℂ) * f z * conj (f z) ∂m) =
        ∫ z, ((w z * ‖f z‖ ^ 2 : ℝ) : ℂ) ∂m := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        simp only [Complex.ofReal_mul, Complex.ofReal_pow, mul_assoc, Complex.mul_conj']
    _ = _ := integral_ofReal

@[simp]
theorem weightedPairing_self_im (m : Measure Z) (w : Z → ℝ) (f : Z → ℂ) :
    (weightedPairing m w f f).im = 0 := by
  rw [weightedPairing_self]
  exact Complex.ofReal_im _

theorem weightedPairing_self_nonneg (m : Measure Z) (w : Z → ℝ) (f : Z → ℂ)
    (hw : ∀ z, 0 ≤ w z) : 0 ≤ (weightedPairing m w f f).re := by
  rw [weightedPairing_self, Complex.ofReal_re]
  exact integral_nonneg fun z => mul_nonneg (hw z) (sq_nonneg _)

/-- A nonzero continuous coefficient on the interior forces positive mass.
The proof derives positivity from the measure and pointwise square norm. -/
theorem weightedPairing_self_pos_on [TopologicalSpace Z] [BorelSpace Z]
    (m : Measure Z) [m.IsOpenPosMeasure] (w : Z → ℝ) (f : Z → ℂ)
    (F : Set Z) (hw : Continuous w) (hf : Continuous f)
    (hwpos : ∀ z, 0 < w z)
    (hint : IntegrableOn (fun z => w z * ‖f z‖ ^ 2) F m)
    {z : Z} (hz : z ∈ interior F) (hfz : f z ≠ 0) :
    0 < (weightedPairing (m.restrict F) w f f).re := by
  rw [weightedPairing_self, Complex.ofReal_re]
  have hnonneg : ∀ z, 0 ≤ w z * ‖f z‖ ^ 2 :=
    fun z => mul_nonneg (hwpos z).le (sq_nonneg _)
  have hn : 0 ≤ ∫ z in F, w z * ‖f z‖ ^ 2 ∂m := integral_nonneg hnonneg
  have hne : (∫ z in F, w z * ‖f z‖ ^ 2 ∂m) ≠ 0 := by
    intro heq
    have hae : (fun z => w z * ‖f z‖ ^ 2) =ᵐ[m.restrict F] 0 :=
      (integral_eq_zero_iff_of_nonneg hnonneg hint).1 heq
    have hae' : (fun z => w z * ‖f z‖ ^ 2) =ᵐ[m.restrict (interior F)] 0 :=
      ae_restrict_of_ae_restrict_of_subset interior_subset hae
    have hzero := Measure.eqOn_open_of_ae_eq hae' isOpen_interior
      ((hw.mul (hf.norm.pow 2)).continuousOn) continuousOn_const
    have hp : 0 < w z * ‖f z‖ ^ 2 :=
      mul_pos (hwpos z) (sq_pos_of_pos (norm_pos_iff.mpr hfz))
    exact (ne_of_gt hp) (hzero hz)
  exact lt_iff_le_and_ne.mpr ⟨hn, Ne.symm hne⟩

end WeightedIntegral

/-- Euclidean area dx dy on the actual upper half-plane. -/
abbrev flatArea : Measure ℍ := (volume : Measure ℂ).comap UpperHalfPlane.coe

instance flatArea_isOpenPosMeasure : flatArea.IsOpenPosMeasure :=
  Measure.IsOpenPosMeasure.comap (volume : Measure ℂ) UpperHalfPlane.isOpenEmbedding_coe

/-- QD pairing for the curvature -1 density lambda_H = 1/y. -/
def quadraticPairing (F : Set ℍ) (φ ψ : ℍ → ℂ) : ℂ :=
  weightedPairing (flatArea.restrict F) (fun z => z.im ^ 2) φ ψ

/-- Beltrami pairing for the same density; the first slot stays linear. -/
def beltramiPairing (F : Set ℍ) (μ ν : ℍ → ℂ) : ℂ :=
  weightedPairing (flatArea.restrict F) (fun z => (z.im ^ 2)⁻¹) μ ν

theorem quadraticPairing_conj (F : Set ℍ) (φ ψ : ℍ → ℂ) :
    conj (quadraticPairing F φ ψ) = quadraticPairing F ψ φ :=
  weightedPairing_conj _ _ _ _

theorem beltramiPairing_conj (F : Set ℍ) (μ ν : ℍ → ℂ) :
    conj (beltramiPairing F μ ν) = beltramiPairing F ν μ :=
  weightedPairing_conj _ _ _ _

theorem quadraticPairing_self_nonneg (F : Set ℍ) (φ : ℍ → ℂ) :
    0 ≤ (quadraticPairing F φ φ).re :=
  weightedPairing_self_nonneg _ _ _ fun z => sq_nonneg z.im

theorem beltramiPairing_self_nonneg (F : Set ℍ) (μ : ℍ → ℂ) :
    0 ≤ (beltramiPairing F μ μ).re :=
  weightedPairing_self_nonneg _ _ _ fun z => inv_nonneg.mpr (sq_nonneg z.im)

/-- The Beltrami density integral is the genuine hyperbolic area integral. -/
theorem beltramiPairing_eq_hyperbolicIntegral (F : Set ℍ) (hF : MeasurableSet F)
    (μ ν : ℍ → ℂ) :
    beltramiPairing F μ ν = ∫ z in F, μ z * conj (ν z) ∂(volume : Measure ℍ) := by
  rw [UpperHalfPlane.volume_def,
    setIntegral_withDensity_eq_setIntegral_smul
      (by fun_prop : Measurable fun z : ℍ =>
        (1 / NNReal.mk z.im z.im_pos.le : ℝ≥0) ^ 2) _ hF]
  unfold beltramiPairing weightedPairing
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp only [NNReal.smul_def, Complex.real_smul, one_div, inv_pow]
    push_cast
    ring

/-- The harmonic Beltrami coefficient associated to a quadratic coefficient. -/
def harmonicBeltrami (φ : ℍ → ℂ) (z : ℍ) : ℂ := ((z.im ^ 2 : ℝ) : ℂ) * conj (φ z)

/-- The QD-to-Beltrami correspondence reverses the complex scalar. -/
theorem harmonicBeltrami_smul (a : ℂ) (φ : ℍ → ℂ) :
    harmonicBeltrami (a • φ) = conj a • harmonicBeltrami φ := by
  funext z
  simp only [harmonicBeltrami, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

/-- The antilinear QD-to-Beltrami correspondence reverses the two pairing slots. -/
theorem harmonicBeltrami_pairing (F : Set ℍ) (φ ψ : ℍ → ℂ) :
    beltramiPairing F (harmonicBeltrami φ) (harmonicBeltrami ψ) =
      quadraticPairing F ψ φ := by
  unfold beltramiPairing quadraticPairing weightedPairing harmonicBeltrami
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj, Complex.ofReal_inv]
    let t : ℂ := (z.im ^ 2 : ℝ)
    have ht : t ≠ 0 := Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 z.im_ne_zero)
    change t⁻¹ * (t * conj (φ z)) * (t * ψ z) = t * ψ z * conj (φ z)
    calc
      t⁻¹ * (t * conj (φ z)) * (t * ψ z) =
          (t⁻¹ * t) * (t * ψ z * conj (φ z)) := by ring
      _ = _ := by rw [inv_mul_cancel₀ ht, one_mul]

/-- The QD density y^2 dx dy is equivalently y^4 against hyperbolic area. -/
theorem quadraticPairing_eq_hyperbolicIntegral (F : Set ℍ) (hF : MeasurableSet F)
    (φ ψ : ℍ → ℂ) :
    quadraticPairing F φ ψ =
      ∫ z in F, ((z.im ^ 4 : ℝ) : ℂ) * φ z * conj (ψ z) ∂(volume : Measure ℍ) := by
  calc
    quadraticPairing F φ ψ =
        beltramiPairing F (harmonicBeltrami ψ) (harmonicBeltrami φ) :=
      (harmonicBeltrami_pairing F ψ φ).symm
    _ = ∫ z in F, harmonicBeltrami ψ z * conj (harmonicBeltrami φ z)
        ∂(volume : Measure ℍ) := beltramiPairing_eq_hyperbolicIntegral F hF _ _
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        simp only [harmonicBeltrami, map_mul, Complex.conj_ofReal, Complex.conj_conj]
        push_cast
        ring

/-- A global nonzero holomorphic coefficient cannot vanish on an open patch. -/
theorem exists_nonzero_on_open {U V : Set ℂ} {φ : ℂ → ℂ}
    (hU : IsOpen U) (hUc : IsPreconnected U) (hφ : DifferentiableOn ℂ φ U)
    (hφne : ∃ z ∈ U, φ z ≠ 0) (hV : IsOpen V) (hVU : V ⊆ U)
    (hVne : V.Nonempty) : ∃ z ∈ V, φ z ≠ 0 := by
  classical
  by_contra hn
  have hzero : ∀ z ∈ V, φ z = 0 := by
    intro z hz
    by_contra h
    exact hn ⟨z, hz, h⟩
  obtain ⟨z, hz⟩ := hVne
  have hevent : φ =ᶠ[nhds z] 0 :=
    Filter.eventuallyEq_of_mem (hV.mem_nhds hz) fun w hw => hzero w hw
  have hall := (hφ.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero
    hUc (hVU hz) hevent
  obtain ⟨w, hw, hwne⟩ := hφne
  exact hwne (hall hw)

/-- On every open upper-half-plane patch the actual coefficient is nonzero somewhere. -/
theorem exists_nonzero_on_halfPlane_open {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ LiZhongQC.upperHalf)
    (hφne : ∃ z ∈ LiZhongQC.upperHalf, φ z ≠ 0)
    {V : Set ℍ} (hV : IsOpen V) (hVne : V.Nonempty) :
    ∃ z ∈ V, φ (z : ℂ) ≠ 0 := by
  have hVo : IsOpen (UpperHalfPlane.coe '' V) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpen_iff_image_isOpen.mp hV
  have hVU : UpperHalfPlane.coe '' V ⊆ LiZhongQC.upperHalf := by
    rintro _ ⟨z, _, rfl⟩
    exact z.im_pos
  obtain ⟨_, ⟨z, hz, rfl⟩, hzne⟩ := exists_nonzero_on_open
    LiZhongQC.isOpen_upperHalf LiZhongQC.isConnected_upperHalf.isPreconnected hφ hφne
    hVo hVU (hVne.image UpperHalfPlane.coe)
  exact ⟨z, hz, hzne⟩

/-- Holomorphic nonvanishing proves strict positivity, rather than assuming it. -/
theorem quadraticPairing_self_pos_of_holomorphic {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ LiZhongQC.upperHalf)
    (hφne : ∃ z ∈ LiZhongQC.upperHalf, φ z ≠ 0)
    (F : Set ℍ) (hFne : (interior F).Nonempty)
    (hint : IntegrableOn (fun z : ℍ => z.im ^ 2 * ‖φ (z : ℂ)‖ ^ 2) F flatArea) :
    0 < (quadraticPairing F (fun z => φ (z : ℂ)) (fun z => φ (z : ℂ))).re := by
  have hc : Continuous (fun z : ℍ => φ (z : ℂ)) :=
    hφ.continuousOn.comp_continuous UpperHalfPlane.continuous_coe fun z => z.im_pos
  obtain ⟨z, hz, hzne⟩ := exists_nonzero_on_halfPlane_open hφ hφne isOpen_interior hFne
  exact weightedPairing_self_pos_on flatArea (fun z => z.im ^ 2)
    (fun z => φ (z : ℂ)) F (UpperHalfPlane.continuous_im.pow 2) hc
    (fun z => sq_pos_of_pos z.im_pos) hint hz hzne

/-- The actual mixed integrand is integrable on compact regions. -/
theorem quadratic_integrand_integrableOn_compact {φ ψ : ℍ → ℂ}
    (hφ : Continuous φ) (hψ : Continuous ψ) {F : Set ℍ} (hF : IsCompact F) :
    IntegrableOn (fun z : ℍ => ((z.im ^ 2 : ℝ) : ℂ) * φ z * conj (ψ z)) F flatArea := by
  exact (((Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.pow 2)).mul hφ).mul
    (Complex.continuous_conj.comp hψ)).continuousOn.integrableOn_compact hF

/-- Compact regions give the required weighted square-integrability automatically. -/
theorem quadratic_square_integrableOn_compact {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ LiZhongQC.upperHalf)
    {F : Set ℍ} (hF : IsCompact F) :
    IntegrableOn (fun z : ℍ => z.im ^ 2 * ‖φ (z : ℂ)‖ ^ 2) F flatArea := by
  have hc : Continuous (fun z : ℍ => φ (z : ℂ)) :=
    hφ.continuousOn.comp_continuous UpperHalfPlane.continuous_coe fun z => z.im_pos
  exact ((UpperHalfPlane.continuous_im.pow 2).mul (hc.norm.pow 2)).continuousOn.integrableOn_compact hF

section NativeDifferentials

universe u
variable {X : Type u} [TopologicalSpace X]

/-- The actual coefficient obtained by pulling back a global quadratic differential. -/
def liftQuadratic (A : RiemannAtlas X) (p : ℍ → X) :
    HolomorphicQuadraticDifferential A →ₗ[ℂ] (ℍ → ℂ) :=
  let := A.toChartedSpace
  { toFun := fun q z => LiZhongQC.utm_liftQD (q : X → ℂ → ℂ) p (z : ℂ)
    map_add' := by
      intro q r
      funext z
      simp only [LiZhongQC.utm_liftQD, Submodule.coe_add, Pi.add_apply]
      ring
    map_smul' := by
      intro a q
      funext z
      simp only [LiZhongQC.utm_liftQD, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
        RingHom.id_apply]
      ring }

/-- The explicit hyperbolic weighted integral of actual global quadratic differentials. -/
def nativeQuadraticPairing (A : RiemannAtlas X) (p : ℍ → X) (F : Set ℍ)
    (q r : HolomorphicQuadraticDifferential A) : ℂ :=
  quadraticPairing F (liftQuadratic A p q) (liftQuadratic A p r)

theorem nativeQuadraticPairing_conj (A : RiemannAtlas X) (p : ℍ → X) (F : Set ℍ)
    (q r : HolomorphicQuadraticDifferential A) :
    conj (nativeQuadraticPairing A p F q r) = nativeQuadraticPairing A p F r q :=
  quadraticPairing_conj _ _ _

theorem nativeQuadraticPairing_smul_left (A : RiemannAtlas X) (p : ℍ → X) (F : Set ℍ)
    (a : ℂ) (q r : HolomorphicQuadraticDifferential A) :
    nativeQuadraticPairing A p F (a • q) r = a * nativeQuadraticPairing A p F q r := by
  unfold nativeQuadraticPairing quadraticPairing
  rw [map_smul]
  exact weightedPairing_smul_left _ _ _ _ _

theorem nativeQuadraticPairing_smul_right (A : RiemannAtlas X) (p : ℍ → X) (F : Set ℍ)
    (a : ℂ) (q r : HolomorphicQuadraticDifferential A) :
    nativeQuadraticPairing A p F q (a • r) = conj a * nativeQuadraticPairing A p F q r := by
  unfold nativeQuadraticPairing quadraticPairing
  rw [map_smul]
  exact weightedPairing_smul_right _ _ _ _ _

/-- Pullback by the actual covering has continuous coefficients on the whole half-plane. -/
theorem liftQuadratic_continuous (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    Continuous (liftQuadratic R.toRiemannAtlas p q) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  have hhol : LiZhongQC.IsHolQuadDiff (q : X → ℂ → ℂ) := q.property
  exact (LiZhongQC.utm_liftQD_differentiableOn hhol hp).continuousOn.comp_continuous
    UpperHalfPlane.continuous_coe fun z => z.im_pos

/-- Additivity for actual global differentials; compactness proves integrability. -/
theorem nativeQuadraticPairing_add_left (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : IsCompact F)
    (q r s : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    nativeQuadraticPairing R.toRiemannAtlas p F (q + r) s =
      nativeQuadraticPairing R.toRiemannAtlas p F q s +
        nativeQuadraticPairing R.toRiemannAtlas p F r s := by
  unfold nativeQuadraticPairing quadraticPairing
  rw [map_add]
  exact weightedPairing_add_left _ _ _ _ _
    (quadratic_integrand_integrableOn_compact
      (liftQuadratic_continuous R p hp q) (liftQuadratic_continuous R p hp s) hF)
    (quadratic_integrand_integrableOn_compact
      (liftQuadratic_continuous R p hp r) (liftQuadratic_continuous R p hp s) hF)

/-- Additivity in the second slot for the same actual global differentials. -/
theorem nativeQuadraticPairing_add_right (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : IsCompact F)
    (q r s : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    nativeQuadraticPairing R.toRiemannAtlas p F q (r + s) =
      nativeQuadraticPairing R.toRiemannAtlas p F q r +
        nativeQuadraticPairing R.toRiemannAtlas p F q s := by
  unfold nativeQuadraticPairing quadraticPairing
  rw [map_add]
  exact weightedPairing_add_right _ _ _ _ _
    (quadratic_integrand_integrableOn_compact
      (liftQuadratic_continuous R p hp q) (liftQuadratic_continuous R p hp r) hF)
    (quadratic_integrand_integrableOn_compact
      (liftQuadratic_continuous R p hp q) (liftQuadratic_continuous R p hp s) hF)

/-- Positive definiteness follows from the actual nonzero holomorphic lift.
The covering, compact set, and its interior are concrete geometric inputs. -/
theorem nativeQuadraticPairing_self_pos (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : IsCompact F) (hFne : (interior F).Nonempty)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0) :
    0 < (nativeQuadraticPairing R.toRiemannAtlas p F q q).re := by
  let := R.t2Space
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  have hhol : LiZhongQC.IsHolQuadDiff (q : X → ℂ → ℂ) := q.property
  have hne : (q : X → ℂ → ℂ) ≠ 0 := by
    intro heq
    exact hq (Subtype.ext heq)
  have hd := LiZhongQC.utm_liftQD_differentiableOn hhol hp
  have hn := LiZhongQC.utm_liftQD_ne hhol hne hp
  exact quadraticPairing_self_pos_of_holomorphic hd hn F hFne
    (quadratic_square_integrableOn_compact hd hF)

/-- The actual positive diagonal detects precisely the zero global differential. -/
theorem nativeQuadraticPairing_self_eq_zero_iff (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : IsCompact F) (hFne : (interior F).Nonempty)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    nativeQuadraticPairing R.toRiemannAtlas p F q q = 0 ↔ q = 0 := by
  classical
  constructor
  · intro heq
    by_contra hq
    have hpos := nativeQuadraticPairing_self_pos R p hp F hF hFne q hq
    rw [heq] at hpos
    exact (lt_irrefl 0) hpos
  · rintro rfl
    simp [nativeQuadraticPairing, quadraticPairing, weightedPairing]

end NativeDifferentials

end LowDimensionalTopology.Geometry.Teichmuller.WeilPetersson
