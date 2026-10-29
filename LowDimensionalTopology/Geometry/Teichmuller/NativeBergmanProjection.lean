module

public import LowDimensionalTopology.Geometry.Teichmuller.MeasurableQuadraticTransport
public import LowDimensionalTopology.Geometry.Teichmuller.HarmonicHermitianCompatibility
public import LowDimensionalTopology.Geometry.Teichmuller.HalfPlaneQuadraticReproduction

/-!
# The literal Bergman integral on every measurable automorphic coefficient

The input retains its original almost-everywhere weighted bound. The actual
conjugate-height transport connects the kernel integral to the full native
Petersson vector. Both slots of the original first-linear integral are kept.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter MeasureTheory
open scoped ENNReal UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.MeasurableQuadratic

open Surfaces QuadraticBergman GammaMeasurableBeltrami WeilPetersson

variable {Γ : Subgroup Deck} (f : ℂ → ℂ)

/-- The original full-half-plane kernel integral, with the original slot order. -/
def bergman (z : ℂ) : ℂ :=
  ∫ ζ in LiZhongQC.upperHalf,
    (ζ.im : ℂ) ^ 2 * f ζ * conj (halfPlaneQuadraticKernel z ζ)

private theorem restriction_measurable
    (hf : AEStronglyMeasurable f (volume.restrict LiZhongQC.upperHalf)) :
    AEStronglyMeasurable (fun z : ℍ => f z) flatMeasure :=
  (aestronglyMeasurable_plane_iff.mp hf).mono_ac flat_absolutelyContinuous_hyperbolic

private theorem restriction_automorphic
    (ha : ∀ A ∈ Γ, ∀ z ∈ LiZhongQC.upperHalf,
      f (LiZhongQC.h36p_m A z) / ((A 1 0 : ℂ) * z + A 1 1) ^ 4 = f z) :
    ∀ A ∈ Γ, ∀ z : ℍ, f (A • z : ℍ) / denominator A z ^ 4 = f z := by
  intro A hA z
  simpa only [LiZhongQC.h36p_m_coe, denominator] using ha A hA (z : ℂ) z.im_pos

private theorem restriction_bound
    (hb : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf),
      ‖f z‖ * z.im ^ 2 ≤ M) :
    ∃ M : ℝ, ∀ᵐ z : ℍ ∂flatMeasure, ‖f z‖ * z.im ^ 2 ≤ M := by
  obtain ⟨M, hM⟩ := hb
  exact ⟨M, ae_hyperbolic_iff.mp (ae_plane_iff.mp hM)⟩

private theorem kernel_integrand_eq (z ζ : ℂ) :
    (ζ.im : ℂ) ^ 2 * f ζ * conj (halfPlaneQuadraticKernel z ζ) =
      (12 / Real.pi : ℂ) * LiZhongQC.h36p_c_K f ζ z := by
  unfold halfPlaneQuadraticKernel
  simp only [map_div₀, map_pow, map_sub, Complex.conj_conj, map_ofNat, Complex.conj_ofReal]
  have hp : (z - conj ζ) ^ 4 = (conj ζ - z) ^ 4 := by ring
  rw [hp]
  unfold LiZhongQC.h36p_c_K
  ring

variable (hf : AEStronglyMeasurable f (volume.restrict LiZhongQC.upperHalf))
    (ha : ∀ A ∈ Γ, ∀ z ∈ LiZhongQC.upperHalf,
      f (LiZhongQC.h36p_m A z) / ((A 1 0 : ℂ) * z + A 1 1) ^ 4 = f z)
    (hb : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf),
      ‖f z‖ * z.im ^ 2 ≤ M)

include hf ha hb

/-- The actual compatible class of every original measurable automorphic form. -/
def bergmanInput : Space Γ := by
  refine toBeltrami (fun z : ℍ => f z) ?_ ?_ ?_
  · exact (aestronglyMeasurable_plane_iff.mp hf).mono_ac
      flat_absolutelyContinuous_hyperbolic
  · intro A hA z
    simpa only [LiZhongQC.h36p_m_coe, denominator] using ha A hA (z : ℂ) z.im_pos
  · obtain ⟨M, hM⟩ := hb
    exact ⟨M, ae_hyperbolic_iff.mp (ae_plane_iff.mp hM)⟩

theorem norm_bergmanInput :
    ‖bergmanInput f hf ha hb‖ = weightedEssNorm (fun z : ℍ => f z) :=
  norm_toBeltrami _ _ _ _

theorem bergmanInput_plane_ae :
    planeRepresentative (bergmanInput f hf ha hb).val =ᵐ[volume.restrict LiZhongQC.upperHalf]
      fun z => (z.im : ℂ) ^ 2 * conj (f z) := by
  apply ae_plane_iff.mpr
  filter_upwards [toBeltrami_coe_ae (fun z : ℍ => f z)
    (restriction_measurable f hf) (restriction_automorphic f ha)
    (restriction_bound f hb)] with z hz
  change (bergmanInput f hf ha hb).val z = beltramiValue (fun w : ℍ => f w) z at hz
  rw [planeRepresentative_coe, hz, beltramiValue_apply, UpperHalfPlane.coe_im]

private theorem conjugate_input_kernel_ae (z : ℂ) :
    (fun ζ => conj (planeRepresentative (bergmanInput f hf ha hb).val ζ /
      (ζ - conj z) ^ 4)) =ᵐ[volume.restrict LiZhongQC.upperHalf]
      fun ζ => LiZhongQC.h36p_c_K f ζ z := by
  filter_upwards [bergmanInput_plane_ae f hf ha hb] with ζ hζ
  rw [hζ]
  simp only [map_div₀, map_mul, map_pow, map_sub, Complex.conj_ofReal, Complex.conj_conj]
  rfl

/-- The original kernel integrand is absolutely integrable at every original point. -/
theorem bergman_integrable {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    IntegrableOn (fun ζ => (ζ.im : ℂ) ^ 2 * f ζ *
      conj (halfPlaneQuadraticKernel z ζ)) LiZhongQC.upperHalf := by
  have hz' : conj z ∈ LiZhongQC.lowerHalf := by
    change (conj z).im < 0
    rw [Complex.conj_im]
    exact neg_lt_zero.mpr hz
  have hi := BersWeighted.fourthKernel_mul_integrable
    (planeRepresentative_isBeltramiCoeff (bergmanInput f hf ha hb).val).1
    (planeRepresentative_isBeltramiCoeff (bergmanInput f hf ha hb).val).2 hz'
  have hic : IntegrableOn (fun ζ => conj
      (planeRepresentative (bergmanInput f hf ha hb).val ζ / (ζ - conj z) ^ 4))
      LiZhongQC.upperHalf := (Complex.conjCLE.integrable_comp_iff).mpr hi
  have hn := hic.congr_fun_ae (conjugate_input_kernel_ae f hf ha hb z)
  apply IntegrableOn.congr_fun_ae (hn.const_mul (12 / Real.pi : ℂ))
  exact Eventually.of_forall fun ζ => (kernel_integrand_eq f z ζ).symm

/-- The literal integral is precisely the reflected bounded Bers integral. -/
theorem bergman_eq_bers (z : ℂ) :
    bergman f z = -2 * conj (LiZhongQC.bersDerivative
      (planeRepresentative (bergmanInput f hf ha hb).val) (conj z)) := by
  have hc : conj (∫ ζ in LiZhongQC.upperHalf,
      planeRepresentative (bergmanInput f hf ha hb).val ζ / (ζ - conj z) ^ 4) =
      ∫ ζ in LiZhongQC.upperHalf, LiZhongQC.h36p_c_K f ζ z := by
    rw [← integral_conj]
    exact integral_congr_ae (conjugate_input_kernel_ae f hf ha hb z)
  have he : bergman f z = (12 / Real.pi : ℂ) *
      ∫ ζ in LiZhongQC.upperHalf, LiZhongQC.h36p_c_K f ζ z := by
    unfold bergman
    simp_rw [kernel_integrand_eq]
    exact integral_const_mul _ _
  rw [he]
  unfold LiZhongQC.bersDerivative
  simp only [map_mul, map_neg, map_div₀, map_ofNat, Complex.conj_ofReal]
  rw [hc]
  ring

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

include hp hF

/-- The full native Petersson vector has exactly the original Bergman coefficient. -/
theorem bergman_eq_uniformized {z : ℂ} (hz : z ∈ LiZhongQC.upperHalf) :
    bergman f z = uniformizedQuadratic R p
      (NativePetersson.toQuadratic R P p hp F hF
        (NativePetersson.rieszQuadratic R P p hp F hF (bergmanInput f hf ha hb))) z := by
  exact (bergman_eq_bers f hf ha hb z).trans
    (NativePetersson.uniformized_rieszQuadratic_eq_bersDerivative R P p hp F hF
      (bergmanInput f hf ha hb) hz).symm

private theorem bergman_lift_eq :
    (fun z : ℍ => bergman f z) = NativePetersson.lift R P p hp F hF
      (NativePetersson.rieszQuadratic R P p hp F hF (bergmanInput f hf ha hb)) := by
  funext z
  exact bergman_eq_uniformized f hf ha hb R P p hp F hF z.im_pos

private theorem mixed_integrand_ae (q : NativePetersson.Space R P p hp F hF) :
    (fun z : ℍ => (z.im : ℂ) ^ 2 * NativePetersson.lift R P p hp F hF q z *
      conj (f z)) =ᵐ[flatArea.restrict F]
      fun z => (bergmanInput f hf ha hb).val z * NativePetersson.lift R P p hp F hF q z := by
  have he := ae_hyperbolic_iff.mp (toBeltrami_coe_ae (fun z : ℍ => f z)
    (restriction_measurable f hf) (restriction_automorphic f ha) (restriction_bound f hb))
  filter_upwards [ae_restrict_of_ae he] with z hz
  change (bergmanInput f hf ha hb).val z = beltramiValue (fun w : ℍ => f w) z at hz
  rw [hz, beltramiValue_apply]
  ring

private theorem pairing_eq_quadratic (q : NativePetersson.Space R P p hp F hF) :
    NativePetersson.pairing R P p hp F hF (bergmanInput f hf ha hb) q =
      quadraticPairing F (NativePetersson.lift R P p hp F hF q) (fun z : ℍ => f z) := by
  unfold NativePetersson.pairing quadraticPairing weightedPairing
  simpa only [Complex.ofReal_pow] using
    integral_congr_ae (mixed_integrand_ae f hf ha hb R P p hp F hF q).symm

/-- Both original mixed Petersson integrals converge absolutely for all
original bounded measurable automorphic inputs. -/
theorem bergman_mixed_integrable (g : ℂ → ℂ)
    (hg : AEStronglyMeasurable g (volume.restrict LiZhongQC.upperHalf))
    (hga : ∀ A ∈ Γ, ∀ z ∈ LiZhongQC.upperHalf,
      g (LiZhongQC.h36p_m A z) / ((A 1 0 : ℂ) * z + A 1 1) ^ 4 = g z)
    (hgb : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf),
      ‖g z‖ * z.im ^ 2 ≤ M) :
    IntegrableOn (fun z : ℍ => (z.im : ℂ) ^ 2 * bergman f z * conj (g z)) F flatArea ∧
      IntegrableOn (fun z : ℍ => (z.im : ℂ) ^ 2 * f z * conj (bergman g z)) F flatArea := by
  let μ := bergmanInput f hf ha hb
  let ν := bergmanInput g hg hga hgb
  let qf := NativePetersson.rieszQuadratic R P p hp F hF μ
  let qg := NativePetersson.rieszQuadratic R P p hp F hF ν
  have hif := (NativePetersson.pairing_integrable R P p hp F hF ν qf).congr_fun_ae
    (mixed_integrand_ae g hg hga hgb R P p hp F hF qf).symm
  have hig := (NativePetersson.pairing_integrable R P p hp F hF μ qg).congr_fun_ae
    (mixed_integrand_ae f hf ha hb R P p hp F hF qg).symm
  have hl : IntegrableOn (fun z : ℍ =>
      (z.im : ℂ) ^ 2 * bergman f z * conj (g z)) F flatArea :=
    hif.congr_fun_ae (Eventually.of_forall fun z => by
      dsimp only
      rw [congrFun (bergman_lift_eq f hf ha hb R P p hp F hF) z])
  have hr : IntegrableOn (fun z : ℍ =>
      (z.im : ℂ) ^ 2 * bergman g z * conj (f z)) F flatArea :=
    hig.congr_fun_ae (Eventually.of_forall fun z => by
      dsimp only
      rw [congrFun (bergman_lift_eq g hg hga hgb R P p hp F hF) z])
  refine ⟨hl, ?_⟩
  have hc : IntegrableOn (fun z : ℍ =>
      conj ((z.im : ℂ) ^ 2 * bergman g z * conj (f z))) F flatArea :=
    (Complex.conjCLE.integrable_comp_iff).mpr hr
  apply hc.congr_fun_ae
  exact Eventually.of_forall fun z => by
    simp only [map_mul, map_pow, Complex.conj_ofReal, Complex.conj_conj]
    ring

omit hf ha hb in
private theorem projected_pairing_conj (μ ν : Space Γ) :
    NativePetersson.pairing R P p hp F hF μ
        (NativePetersson.rieszQuadratic R P p hp F hF ν) =
      conj (NativePetersson.pairing R P p hp F hF ν
        (NativePetersson.rieszQuadratic R P p hp F hF μ)) := by
  let H := NativePetersson.harmonicProjection R P p hp F hF
  have h := (NativePetersson.harmonicProjection_hermitian_compatibility
    R P p hp F hF μ ν).2.2.2
  have h' := (NativePetersson.harmonicProjection_hermitian_compatibility
    R P p hp F hF ν μ).2.2.2
  calc
    _ = beltramiPairing F (H μ).val (H ν).val := h.symm
    _ = conj (beltramiPairing F (H ν).val (H μ).val) :=
      (beltramiPairing_conj F (H ν).val (H μ).val).symm
    _ = _ := congrArg conj h'

/-- Self-adjointness uses the original first-linear Petersson integral and
all original measurable weighted-bounded automorphic inputs in both slots. -/
theorem bergman_selfAdjoint (g : ℂ → ℂ)
    (hg : AEStronglyMeasurable g (volume.restrict LiZhongQC.upperHalf))
    (hga : ∀ A ∈ Γ, ∀ z ∈ LiZhongQC.upperHalf,
      g (LiZhongQC.h36p_m A z) / ((A 1 0 : ℂ) * z + A 1 1) ^ 4 = g z)
    (hgb : ∃ M : ℝ, ∀ᵐ z ∂(volume.restrict LiZhongQC.upperHalf),
      ‖g z‖ * z.im ^ 2 ≤ M) :
    (∫ z in F, (z.im : ℂ) ^ 2 * bergman f z * conj (g z) ∂flatArea) =
      ∫ z in F, (z.im : ℂ) ^ 2 * f z * conj (bergman g z) ∂flatArea := by
  let μ := bergmanInput f hf ha hb
  let ν := bergmanInput g hg hga hgb
  let qf := NativePetersson.rieszQuadratic R P p hp F hF μ
  let qg := NativePetersson.rieszQuadratic R P p hp F hF ν
  have hef : (fun z : ℍ => bergman f z) = NativePetersson.lift R P p hp F hF qf :=
    bergman_lift_eq f hf ha hb R P p hp F hF
  have heg : (fun z : ℍ => bergman g z) = NativePetersson.lift R P p hp F hF qg :=
    bergman_lift_eq g hg hga hgb R P p hp F hF
  simp only [← Complex.ofReal_pow]
  change quadraticPairing F (fun z : ℍ => bergman f z) (fun z : ℍ => g z) =
    quadraticPairing F (fun z : ℍ => f z) (fun z : ℍ => bergman g z)
  rw [hef, heg]
  calc
    _ = NativePetersson.pairing R P p hp F hF ν qf :=
      (pairing_eq_quadratic g hg hga hgb R P p hp F hF qf).symm
    _ = conj (NativePetersson.pairing R P p hp F hF μ qg) :=
      projected_pairing_conj R P p hp F hF ν μ
    _ = conj (quadraticPairing F (NativePetersson.lift R P p hp F hF qg)
        (fun z : ℍ => f z)) := congrArg conj
      (pairing_eq_quadratic f hf ha hb R P p hp F hF qg)
    _ = _ := quadraticPairing_conj F (NativePetersson.lift R P p hp F hF qg)
      (fun z : ℍ => f z)

end LowDimensionalTopology.Geometry.Teichmuller.MeasurableQuadratic
