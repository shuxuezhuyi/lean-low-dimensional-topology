module

public import LowDimensionalTopology.Geometry.Teichmuller.WeightedAutomorphicBergmanProjection
public import LowDimensionalTopology.Geometry.Teichmuller.HarmonicHermitianCompatibility
public import LowDimensionalTopology.Geometry.Teichmuller.SourceFundamentalIntegrability
public import LowDimensionalTopology.Geometry.Teichmuller.CompatibleFundamentalZero

/-!
# The Petersson integral on all weighted automorphic coefficients

The first slot is linear. Both original rough slots are absolutely integrable
on the same given fundamental region, without compactness of that region.
The inherited essential-supremum norm is retained.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter MeasureTheory
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.WeightedAutomorphicCoefficient

open Surfaces GammaMeasurableBeltrami WeilPetersson
variable {Γ : Subgroup Deck} (F : Set ℍ)

/-- The actual Petersson integral, with the two antilinear slots reversed. -/
def peterssonPairing (g h : Space Γ) : ℂ :=
  beltramiPairing F (toBeltrami h).val (toBeltrami g).val

private theorem pairing_integrand_ae (g h : Space Γ) :
    (fun z : ℍ => (((z.im ^ 2)⁻¹ : ℝ) : ℂ) * (toBeltrami h).val z *
      conj ((toBeltrami g).val z)) =ᵐ[flatArea.restrict F]
    fun z => (((z.im ^ 2)⁻¹ : ℝ) : ℂ) * g.val z * conj (h.val z) := by
  filter_upwards [ae_restrict_of_ae (ae_hyperbolic_iff.mp (Lp.coeFn_star h.val)),
    ae_restrict_of_ae (ae_hyperbolic_iff.mp (Lp.coeFn_star g.val))] with z hh hg
  change (((z.im ^ 2)⁻¹ : ℝ) : ℂ) * (star h.val : Ambient) z *
    conj ((star g.val : Ambient) z) = _
  rw [hh, hg]
  change (((z.im ^ 2)⁻¹ : ℝ) : ℂ) * conj (h.val z) * conj (conj (g.val z)) = _
  rw [Complex.conj_conj]
  ring

/-- In the original weighted classes this is the literal inverse-height integral. -/
theorem peterssonPairing_eq_weightedPairing (g h : Space Γ) :
    peterssonPairing F g h =
      weightedPairing (flatArea.restrict F) (fun z => (z.im ^ 2)⁻¹) g.val h.val :=
  integral_congr_ae (pairing_integrand_ae F g h)

variable {X : Type*} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius)) (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

include hp hF in
private theorem coefficient_integrand_integrable (g h : Space Γ) :
    IntegrableOn (fun z : ℍ => (((z.im ^ 2)⁻¹ : ℝ) : ℂ) *
      g.val z * conj (h.val z)) F flatArea := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  have hΓ : LiZhongQC.IsFuchsian Γ := LiZhongQC.utm_x_isFuchsian hp
  let k : ℂ → ℂ := fun z => ((z.im ^ 2 : ℝ) : ℂ)⁻¹ *
    planeRepresentative g.val z * conj (planeRepresentative h.val z)
  have hg := planeRepresentative_isBeltramiCoeff g.val
  have hh := planeRepresentative_isBeltramiCoeff h.val
  have hk : AEStronglyMeasurable k (volume.restrict LiZhongQC.upperHalf) :=
    ((Measurable.aestronglyMeasurable
      (by fun_prop : Measurable fun z : ℂ => ((z.im ^ 2 : ℝ) : ℂ)⁻¹)).mul hg.1).mul hh.1.star
  have hb : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf),
      ‖k z‖ * z.im ^ 2 ≤ M := by
    refine ⟨‖g.val‖ * ‖h.val‖, ?_⟩
    filter_upwards [hg.2, hh.2,
      ae_restrict_mem LiZhongQC.isOpen_upperHalf.measurableSet] with z hzg hzh hz
    dsimp only [k]
    rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg z.im), Complex.norm_conj]
    calc
      _ = ‖planeRepresentative g.val z‖ * ‖planeRepresentative h.val z‖ := by
        calc
          _ = ((z.im ^ 2)⁻¹ * z.im ^ 2) *
              (‖planeRepresentative g.val z‖ * ‖planeRepresentative h.val z‖) := by ring
          _ = _ := by rw [inv_mul_cancel₀ (pow_ne_zero 2
            (ne_of_gt (show 0 < z.im from hz))), one_mul]
      _ ≤ _ := mul_le_mul hzg hzh (norm_nonneg _) (norm_nonneg _)
  have hi := sourceFundamentalDomainH_integrable_of_weighted_bound R hΓ hp
    (Fuchsian.closedPlanarRegion_isFundamentalDomainH P hF) hk hb
  have ho := (Fuchsian.integrableOn_openPlanarRegion_iff_closedPlanarRegion
    hF.1 hF.2.2.2 k).mpr hi
  have he := (UpperHalfPlane.measurableEmbedding_coe.integrableOn_iff_comap
    (image_subset_range UpperHalfPlane.coe F)).mp ho
  simpa only [k, UpperHalfPlane.coe_injective.preimage_image, Function.comp_def,
    flatArea, planeRepresentative_coe, UpperHalfPlane.coe_im, Complex.ofReal_inv] using he

include hp hF in
/-- Both original rough slots give a genuine absolutely integrable defining integrand. -/
theorem peterssonPairing_integrable (g h : Space Γ) :
    IntegrableOn (fun z : ℍ => (((z.im ^ 2)⁻¹ : ℝ) : ℂ) *
      (toBeltrami h).val z * conj ((toBeltrami g).val z)) F flatArea :=
  (coefficient_integrand_integrable F R P p hp hF g h).congr_fun_ae
    (pairing_integrand_ae F g h).symm

/-- The full coefficient space has the same conjugate symmetry. -/
theorem peterssonPairing_conj (g h : Space Γ) :
    conj (peterssonPairing F g h) = peterssonPairing F h g := beltramiPairing_conj _ _ _

/-- The diagonal is nonnegative in the original Petersson integral. -/
theorem peterssonPairing_self_nonneg (g : Space Γ) :
    0 ≤ (peterssonPairing F g g).re := beltramiPairing_self_nonneg _ _

include hp hF in
/-- Additivity in the first slot uses genuine integrability of both summands. -/
theorem peterssonPairing_add_left (g h k : Space Γ) :
    peterssonPairing F (g + h) k = peterssonPairing F g k + peterssonPairing F h k := by
  simp only [peterssonPairing_eq_weightedPairing]
  calc
    _ = weightedPairing (flatArea.restrict F) (fun z => (z.im ^ 2)⁻¹)
        ((g.val : ℍ → ℂ) + h.val) k.val := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (ae_hyperbolic_iff.mp
        (Lp.coeFn_add g.val h.val))] with z hz
      exact congrArg (fun v : ℂ => (((z.im ^ 2)⁻¹ : ℝ) : ℂ) * v * conj (k.val z)) hz
    _ = _ := weightedPairing_add_left _ _ _ _ _
      (coefficient_integrand_integrable F R P p hp hF g k)
      (coefficient_integrand_integrable F R P p hp hF h k)

include hp hF in
theorem peterssonPairing_add_right (g h k : Space Γ) :
    peterssonPairing F g (h + k) = peterssonPairing F g h + peterssonPairing F g k := by
  simpa only [map_add, peterssonPairing_conj] using
    congrArg conj (peterssonPairing_add_left F R P p hp hF h k g)

/-- Scalars retain the book's complex-linear first slot. -/
theorem peterssonPairing_smul_left (a : ℂ) (g h : Space Γ) :
    peterssonPairing F (a • g) h = a * peterssonPairing F g h := by
  simp only [peterssonPairing_eq_weightedPairing]
  calc
    _ = weightedPairing (flatArea.restrict F) (fun z => (z.im ^ 2)⁻¹)
        (a • (g.val : ℍ → ℂ)) h.val := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae (ae_hyperbolic_iff.mp
        (Lp.coeFn_smul a g.val))] with z hz
      exact congrArg (fun v : ℂ => (((z.im ^ 2)⁻¹ : ℝ) : ℂ) * v * conj (h.val z)) hz
    _ = _ := weightedPairing_smul_left _ _ _ _ _

theorem peterssonPairing_smul_right (a : ℂ) (g h : Space Γ) :
    peterssonPairing F g (a • h) = conj a * peterssonPairing F g h := by
  simpa only [map_mul, peterssonPairing_conj] using
    congrArg conj (peterssonPairing_smul_left F a h g)

/-- On both original raw inputs the form is the literal quadratic Petersson integral. -/
theorem peterssonPairing_ofRaw (f g : ℍ → ℂ)
    (hf : AEStronglyMeasurable f flatMeasure) (hg : AEStronglyMeasurable g flatMeasure)
    (ha : ∀ A ∈ Γ, ∀ z : ℍ, f (A • z) / denominator A z ^ 4 = f z)
    (hga : ∀ A ∈ Γ, ∀ z : ℍ, g (A • z) / denominator A z ^ 4 = g z)
    (hb : ∃ M : ℝ, ∀ᵐ z ∂flatMeasure, ‖f z‖ * z.im ^ 2 ≤ M)
    (hgb : ∃ M : ℝ, ∀ᵐ z ∂flatMeasure, ‖g z‖ * z.im ^ 2 ≤ M) :
    peterssonPairing F (ofRaw f hf ha hb) (ofRaw g hg hga hgb) = quadraticPairing F f g := by
  rw [peterssonPairing_eq_weightedPairing]
  unfold quadraticPairing weightedPairing
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae (ofRaw_coe_ae_flat f hf ha hb),
    ae_restrict_of_ae (ofRaw_coe_ae_flat g hg hga hgb)] with z hzf hzg
  rw [hzf, hzg]
  simp only [MeasurableQuadratic.weightedValue, map_mul, map_pow,
    Complex.conj_ofReal, Complex.ofReal_inv, Complex.ofReal_pow]
  have hy : (z.im : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr z.im_ne_zero)
  calc
    _ = (((z.im : ℂ) ^ 2)⁻¹ * (z.im : ℂ) ^ 2) *
        ((z.im : ℂ) ^ 2 * f z * conj (g z)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hy, one_mul]

/-- The actual Bergman projection is self-adjoint for this extended integral. -/
theorem peterssonPairing_bergmanProjection (g h : Space Γ) :
    peterssonPairing F (bergmanProjection R P p hp F hF g) h =
      peterssonPairing F g (bergmanProjection R P p hp F hF h) := by
  let s := beltramiEquiv Γ
  let H := NativePetersson.harmonicProjection R P p hp F hF
  change beltramiPairing F (s h).val (s (s.symm (H (s g)))).val =
    beltramiPairing F (s (s.symm (H (s h)))).val (s g).val
  rw [s.apply_symm_apply, s.apply_symm_apply]
  have he := NativePetersson.harmonicProjection_hermitian_compatibility
    R P p hp F hF (s h) (s g)
  exact he.2.1.symm.trans he.1

include hp hF in
/-- The extended Petersson diagonal vanishes precisely on the zero original class. -/
theorem peterssonPairing_self_eq_zero_iff (g : Space Γ) :
    peterssonPairing F g g = 0 ↔ g = 0 := by
  constructor
  · intro heq
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isManifold
    let := R.t2Space
    let := R.connectedSpace
    let := R.compactSpace
    have hΓ : LiZhongQC.IsFuchsian Γ := LiZhongQC.utm_x_isFuchsian hp
    let μ := toBeltrami g
    have hi : IntegrableOn (fun z : ℍ => (z.im ^ 2)⁻¹ * ‖μ.val z‖ ^ 2) F flatArea := by
      apply Integrable.congr (peterssonPairing_integrable F R P p hp hF g g).norm
      exact Filter.Eventually.of_forall fun z => by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr (sq_nonneg z.im)), Complex.norm_conj]
        ring
    have hI : (∫ z in F, (z.im ^ 2)⁻¹ * ‖μ.val z‖ ^ 2 ∂flatArea) = 0 := by
      have he := congrArg Complex.re heq
      simpa only [peterssonPairing, beltramiPairing, weightedPairing_self,
        Complex.ofReal_re, Complex.zero_re] using he
    have hzero : ∀ᵐ z ∂(flatArea.restrict F), μ.val z = 0 := by
      have hz0 := (integral_eq_zero_iff_of_nonneg
        (fun z : ℍ => mul_nonneg (inv_nonneg.mpr (sq_nonneg z.im))
          (sq_nonneg ‖μ.val z‖)) hi).mp hI
      filter_upwards [hz0] with z hz
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp ((mul_eq_zero.mp hz).resolve_left
        (ne_of_gt (inv_pos.mpr (sq_pos_of_pos z.im_pos)))))
    apply (beltramiEquiv Γ).injective
    exact (GammaMeasurableBeltrami.eq_zero_of_ae_zero_fundamentalRegion hΓ P hF μ hzero).trans
      (map_zero (beltramiEquiv Γ)).symm
  · rintro rfl
    simpa only [zero_smul, zero_mul] using
      (peterssonPairing_smul_left F (0 : ℂ) (0 : Space Γ) (0 : Space Γ))

end LowDimensionalTopology.Geometry.Teichmuller.WeightedAutomorphicCoefficient
