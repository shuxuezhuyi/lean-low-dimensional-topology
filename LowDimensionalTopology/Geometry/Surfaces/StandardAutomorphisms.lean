module

public import LowDimensionalTopology.Geometry.Surfaces.Covering.SphereUniversalDeck
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.DiscAnalyticAutomorphisms
public import LowDimensionalTopology.Geometry.Mobius.Trace.MobiusInvariants
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.HyperbolicExamples
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S22_RiemannSurfaces
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.DiscAutomorphism
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Explicit forms of analytic automorphisms of the standard complex domains

The sphere formula includes its pole and its value at infinity. The disc formulas
retain both complex conjugates. The half-plane statement starts with an actual
holomorphic homeomorphism, rather than a previously supplied fractional linear map.
-/

@[expose] public section
noncomputable section

open Set Metric
open scoped OnePoint ComplexConjugate UpperHalfPlane Manifold

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Geometry

/-- A sphere automorphism has a determinant-one representative, including the
exceptional values in its fractional linear coordinate formula. -/
theorem sphere_analytic_automorphism_det_one_form
    (H : Mobius.ExtendedComplex ≃ₜ Mobius.ExtendedComplex)
    (hH : RiemannAnalyticMap sphereRiemannAtlas sphereRiemannAtlas H) :
    ∃ A : Auxiliary.Algebra.SpecialLinear2,
      A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 ∧
      (∀ z : ℂ, H (z : Mobius.ExtendedComplex) =
        if A 1 0 * z + A 1 1 = 0 then ∞
        else (((A 0 0 * z + A 0 1) / (A 1 0 * z + A 1 1) : ℂ) :
          Mobius.ExtendedComplex)) ∧
      H ∞ = if A 1 0 = 0 then ∞
        else ((A 0 0 / A 1 0 : ℂ) : Mobius.ExtendedComplex) := by
  obtain ⟨M, hM, _⟩ := sphere_analytic_automorphism_existsUnique_mobius H hH
  obtain ⟨A, hA⟩ := Mobius.mobiusSpecialLinearProjection_surjective M
  have hAf (z : Mobius.ExtendedComplex) :
      Mobius.fractionalLinear (Matrix.SpecialLinearGroup.toGL A) z = H z := by
    rw [← Mobius.mobiusMatrixProjection_apply]
    change (Mobius.mobiusSpecialLinearProjection A).val z = H z
    rw [hA]
    exact hM z
  refine ⟨A, ?_, ?_, ?_⟩
  · simpa only [Matrix.det_fin_two] using A.det_coe
  · intro z
    rw [← hAf (z : Mobius.ExtendedComplex)]
    exact Mobius.fractionalLinear_coe (Matrix.SpecialLinearGroup.toGL A) z
  · rw [← hAf ∞]
    exact Mobius.fractionalLinear_infty (Matrix.SpecialLinearGroup.toGL A)

/-- A whole-plane analytic homeomorphism is affine, with nonzero linear part. -/
theorem plane_analytic_automorphism_explicit_form (H : ℂ ≃ₜ ℂ)
    (hH : AnalyticOnNhd ℂ H univ) :
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z : ℂ, H z = a * z + b :=
  plane_analytic_automorphism_affine H hH

/-- Analyticity and the actual inverse laws provide the conformal-bijection
contract needed by the disc classification. -/
theorem analytic_openPartialHomeomorph_isConformalOnto
    (e : OpenPartialHomeomorph ℂ ℂ) (he : AnalyticOnNhd ℂ e e.source) :
    LiZhongQC.IsConformalOnto e e.source e.target := by
  refine ⟨he.differentiableOn, ?_, e.image_source_eq_target⟩
  intro z hz w hw hzw
  calc
    z = e.symm (e z) := (e.left_inv hz).symm
    _ = e.symm (e w) := congrArg e.symm hzw
    _ = w := e.left_inv hw

/-- The rotation-Blaschke expression for an actual analytic disc homeomorphism. -/
theorem disc_analytic_automorphism_phase_form (e : OpenPartialHomeomorph ℂ ℂ)
    (hs : e.source = ball 0 1) (ht : e.target = ball 0 1)
    (he : AnalyticOnNhd ℂ e e.source) :
    ∃ θ : ℝ, ∃ α : ℂ, ‖α‖ < 1 ∧ ∀ z ∈ ball (0 : ℂ) 1,
      e z = Complex.exp ((θ : ℂ) * Complex.I) *
        ((z - α) / (1 - conj α * z)) := by
  have hc : LiZhongQC.IsConformalOnto e LiZhongQC.unitDisc LiZhongQC.unitDisc := by
    simpa only [hs, ht, LiZhongQC.unitDisc] using
      analytic_openPartialHomeomorph_isConformalOnto e he
  obtain ⟨c, α, hc, hα, heq⟩ :=
    LiZhongQC.exists_rotation_blaschke_of_isConformalOnto_unitDisc hc
  have hphase : Complex.exp ((Complex.arg c : ℂ) * Complex.I) = c := by
    simpa only [hc, Complex.ofReal_one, one_mul] using Complex.norm_mul_exp_arg_mul_I c
  refine ⟨Complex.arg c, α, hα, ?_⟩
  intro z hz
  rw [hphase]
  exact heq hz

/-- The determinant-one disc form for the actual inherited Riemann surface. -/
theorem discRiemannSurface_automorphism_normalized_form
    (H : Hyperbolic.extendedUnitDisc ≃ₜ Hyperbolic.extendedUnitDisc)
    (hH : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas
      discRiemannSurface.toRiemannAtlas H) :
    ∃ a b : ℂ, ‖a‖ ^ 2 - ‖b‖ ^ 2 = 1 ∧
      ∀ z : Hyperbolic.extendedUnitDisc,
        (H z).val =
          (((a * discFiniteChart z + b) /
            (conj b * discFiniteChart z + conj a) : ℂ) : Mobius.ExtendedComplex) := by
  obtain ⟨M, hM, heq⟩ := discRiemannSurface_automorphism_exists_mobius H hH
  obtain ⟨a, c, hdet, hnorm⟩ := Hyperbolic.complexMobius_disc_normal_form M hM
  refine ⟨a, conj c, ?_, ?_⟩
  · simpa only [Complex.norm_conj, ← Complex.normSq_eq_norm_sq] using hdet
  · intro z
    have hzs : z ∈ discFiniteChart.source := by
      rw [discFiniteChart_source]
      exact mem_univ z
    have hz : ‖discFiniteChart z‖ ≤ 1 :=
      (mem_ball_zero_iff.mp (discFiniteChart_target ▸ discFiniteChart.map_source hzs)).le
    calc
      (H z).val = M.val z.val := (heq z).symm
      _ = Hyperbolic.normalizedDiscTransformation a c hdet
          (discFiniteChart z : Mobius.ExtendedComplex) := by
        rw [← discFiniteChart_coe z]
        exact Equiv.congr_fun hnorm _
      _ = (Auxiliary.Analysis.discFractionalMap a c (discFiniteChart z) :
          Mobius.ExtendedComplex) :=
        Hyperbolic.normalizedDiscTransformation_of_closedDisc a c _ hdet hz
      _ = _ := by
        simp only [Auxiliary.Analysis.discFractionalMap,
          Auxiliary.Analysis.fractionalLinearMap, starRingEnd_self_apply]

/-- The phase form also holds in the actual inherited disc surface structure. -/
theorem discRiemannSurface_automorphism_phase_form
    (H : Hyperbolic.extendedUnitDisc ≃ₜ Hyperbolic.extendedUnitDisc)
    (hH : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas
      discRiemannSurface.toRiemannAtlas H) :
    ∃ θ : ℝ, ∃ α : ℂ, ‖α‖ < 1 ∧ ∀ z : Hyperbolic.extendedUnitDisc,
      discFiniteChart (H z) = Complex.exp ((θ : ℂ) * Complex.I) *
        ((discFiniteChart z - α) / (1 - conj α * discFiniteChart z)) := by
  let F := riemannHomeomorphChart discFiniteChart H discFiniteChart
  have hs : F.source = ball (0 : ℂ) 1 := by
    rw [riemannHomeomorphChart_source]
    simp [riemannChartMapDomain, discFiniteChart_source, discFiniteChart_target]
  have ht : F.target = ball (0 : ℂ) 1 := by
    rw [riemannHomeomorphChart_target]
    simp [riemannChartMapDomain, discFiniteChart_source, discFiniteChart_target]
  have hF : AnalyticOnNhd ℂ F F.source := by
    rw [show F.source = riemannChartMapDomain discFiniteChart H discFiniteChart from
      riemannHomeomorphChart_source _ _ _]
    exact hH.2 discFiniteChart discFiniteChart_mem discFiniteChart discFiniteChart_mem
  obtain ⟨θ, α, hα, heq⟩ := disc_analytic_automorphism_phase_form F hs ht hF
  refine ⟨θ, α, hα, ?_⟩
  intro z
  have hzs : z ∈ discFiniteChart.source := by
    rw [discFiniteChart_source]
    exact mem_univ z
  have hz := discFiniteChart_target ▸ discFiniteChart.map_source hzs
  have h := heq (discFiniteChart z) hz
  change discFiniteChart (H (discFiniteChart.symm (discFiniteChart z))) = _ at h
  rwa [discFiniteChart.left_inv hzs] at h

/-- An arbitrary holomorphic homeomorphism of the actual upper half-plane has
real determinant-one coefficients and no pole anywhere in the domain. -/
theorem upperHalfPlane_analytic_automorphism_real_form (H : ℍ ≃ₜ ℍ)
    (hH : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) H) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 ∧
      ∀ z : ℍ, (A 1 0 : ℂ) * z + A 1 1 ≠ 0 ∧
        (H z : ℂ) =
          ((A 0 0 : ℂ) * z + A 0 1) / ((A 1 0 : ℂ) * z + A 1 1) := by
  obtain ⟨A, hA⟩ := LiZhongQC.k22c5_eq_smul_of_mdifferentiable H hH
  refine ⟨A, LiZhongQC.k24_det_realR A, ?_⟩
  intro z
  refine ⟨LiZhongQC.h36t_den_ne A z, ?_⟩
  rw [hA z]
  exact LiZhongQC.h36t_coe_smul A z

end LowDimensionalTopology.Geometry.Surfaces
