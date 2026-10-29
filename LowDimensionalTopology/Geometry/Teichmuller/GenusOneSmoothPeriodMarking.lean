module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalGenusOneParameterSupport
public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneWeilPeterssonParameter
public import LowDimensionalTopology.Geometry.Teichmuller.AnalyticCoverDescent
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.LowGenusQC

/-!
# The actual smooth oriented period marking

The actual real period change descends through the genuine torus coverings.
Its smoothness and positive orientation use the same original surface atlases.
The selected markings satisfy the exact covering law and the cocycle identity.
Their values on both ordered projected period segments preserve the marking.
These maps define marked compact surfaces and points of the original quotient.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Module
open scoped UpperHalfPlane ComplexConjugate Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces

private theorem periodChange_explicit (τ σ : ℍ) (z : ℂ) :
    periodChange τ σ z =
      ((z.re - z.im / τ.im * τ.re : ℝ) : ℂ) +
        ((z.im / τ.im : ℝ) : ℂ) * (σ : ℂ) := by
  have hc : (normalizedTorusBasis τ).equivFun z =
      ![z.re - z.im / τ.im * τ.re, z.im / τ.im] := by
    ext i
    fin_cases i <;>
      simp [normalizedTorusBasis]
  change (normalizedTorusBasis σ).equivFun.symm
    ((normalizedTorusBasis τ).equivFun z) = _
  rw [hc, Basis.equivFun_symm_apply, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    normalizedTorusBasis_zero, normalizedTorusBasis_one, Complex.real_smul, mul_one]

/-- The basis-linear marking lift is precisely the literal affine
deformation with parameter difference σ−τ, including its conjugate term. -/
theorem periodChange_eq_affineLift (τ σ : ℍ) (z : ℂ) :
    periodChange τ σ z = affineLift τ ((σ : ℂ) - (τ : ℂ)) z := by
  rw [periodChange_explicit, affineLift, periodGap_eq]
  apply Complex.ext <;>
    simp [Complex.div_re, Complex.div_im, Complex.normSq,
      Complex.mul_re, Complex.mul_im]
  all_goals
    field_simp [τ.im_ne_zero]
    ring

private theorem periodChange_det (τ σ : ℍ) :
    LinearMap.det (periodChange τ σ).toLinearMap = σ.im / τ.im := by
  rw [LiZhongQC.s24q_lg_det_eq]
  simp [periodChange_explicit, Complex.mul_re, Complex.mul_im]
  ring

private theorem planeLinear_smooth (L : ℂ ≃L[ℝ] ℂ) :
    letI := complexPlaneRiemannSurface.toRiemannAtlas.toChartedSpace
    ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ L := by
  apply realContMDiff_of_chartMaps complexPlaneRiemannSurface.toRiemannAtlas
    complexPlaneRiemannSurface.toRiemannAtlas L L.continuous
  intro e he g hg
  have he' : e = OpenPartialHomeomorph.refl ℂ := he
  have hg' : g = OpenPartialHomeomorph.refl ℂ := hg
  subst e
  subst g
  simpa [riemannChartMap] using L.contDiff.contDiffOn

private def periodPlaneEquiv (τ σ : ℍ) :
    SmoothSurfaceEquiv complexPlaneRiemannSurface complexPlaneRiemannSurface := by
  let := complexPlaneRiemannSurface.toRiemannAtlas.toChartedSpace
  exact
    { toEquiv := (periodChange τ σ).toLinearEquiv.toEquiv
      contMDiff_toFun := planeLinear_smooth (periodChange τ σ)
      contMDiff_invFun := planeLinear_smooth (periodChange τ σ).symm }

private theorem periodPlaneEquiv_coe (τ σ : ℍ) :
    ((periodPlaneEquiv τ σ).toHomeomorph : ℂ → ℂ) = periodChange τ σ := rfl

private theorem periodPlaneEquiv_orientation (τ σ : ℍ) :
    PreservesComplexOrientation complexPlaneRiemannSurface.toRiemannAtlas
      complexPlaneRiemannSurface.toRiemannAtlas (periodPlaneEquiv τ σ).toHomeomorph := by
  intro e he g hg z _hz
  have he' : e = OpenPartialHomeomorph.refl ℂ := he
  have hg' : g = OpenPartialHomeomorph.refl ℂ := hg
  subst e
  subst g
  rw [periodPlaneEquiv_coe]
  change 0 < realJacobian (periodChange τ σ) z
  unfold realJacobian
  rw [ContinuousLinearEquiv.fderiv (periodChange τ σ)]
  change 0 < LinearMap.det (periodChange τ σ).toLinearMap
  rw [periodChange_det]
  exact div_pos σ.im_pos τ.im_pos

/-- The real-affine period change descends to a genuine smooth oriented map
of the two existing actual torus surfaces, with its exact covering law. -/
theorem exists_periodMarking (τ σ : ℍ) :
    ∃ f : SmoothSurfaceEquiv (normalizedTorusModel τ).surface
        (normalizedTorusModel σ).surface,
      PreservesComplexOrientation (normalizedTorusModel τ).surface.toRiemannAtlas
        (normalizedTorusModel σ).surface.toRiemannAtlas f.toHomeomorph ∧
      ∀ z : ℂ, f.toHomeomorph ((normalizedTorusModel τ).projection z) =
        (normalizedTorusModel σ).projection (periodChange τ σ z) := by
  obtain ⟨f, hf⟩ := exists_periodChange_homeomorph τ σ
  obtain ⟨F, hF, hpos⟩ := analyticCovering_smooth_descent
    complexPlaneRiemannSurface complexPlaneRiemannSurface
    (normalizedTorusModel τ).surface (normalizedTorusModel σ).surface
    (normalizedTorusModel τ).covering (normalizedTorusModel σ).covering
    (normalizedTorusModel τ).analytic_projection (normalizedTorusModel σ).analytic_projection
    (normalizedTorusModel τ).surjective (normalizedTorusModel σ).surjective
    (periodPlaneEquiv τ σ) (periodPlaneEquiv_orientation τ σ) f (fun z => by
      simpa only [periodPlaneEquiv_coe] using (hf z).symm)
  refine ⟨F, hpos, ?_⟩
  intro z
  rw [hF]
  exact hf z

/-- The actual smooth marking, selected only after its existence was proved. -/
def periodMarking (τ σ : ℍ) :
    SmoothSurfaceEquiv (normalizedTorusModel τ).surface (normalizedTorusModel σ).surface :=
  Classical.choose (exists_periodMarking τ σ)

/-- Actual orientation and the exact original-cover equation for the selected
marking, with the affine lift given by periodChange_eq_affineLift. -/
theorem periodMarking_spec (τ σ : ℍ) :
    PreservesComplexOrientation (normalizedTorusModel τ).surface.toRiemannAtlas
        (normalizedTorusModel σ).surface.toRiemannAtlas (periodMarking τ σ).toHomeomorph ∧
      ∀ z : ℂ, (periodMarking τ σ).toHomeomorph ((normalizedTorusModel τ).projection z) =
        (normalizedTorusModel σ).projection (periodChange τ σ z) :=
  Classical.choose_spec (exists_periodMarking τ σ)

/-- The selected actual maps satisfy the cocycle pointwise. No compatibility
of arbitrary choices is assumed; surjectivity of the original cover proves it. -/
theorem periodMarking_cocycle (τ σ ρ : ℍ) (x : ComplexTorusCarrier) :
    (periodMarking σ ρ).toHomeomorph ((periodMarking τ σ).toHomeomorph x) =
      (periodMarking τ ρ).toHomeomorph x := by
  obtain ⟨z, rfl⟩ := (normalizedTorusModel τ).surjective x
  rw [(periodMarking_spec τ σ).2, (periodMarking_spec σ ρ).2,
    (periodMarking_spec τ ρ).2]
  congr 1
  apply (normalizedTorusBasis ρ).equivFun.injective
  rw [periodChange_coordinates, periodChange_coordinates, periodChange_coordinates]

/-- Literal pointwise equality of both ordered projected period segments.
This includes the basepoint equation; path packaging must retain that endpoint
cast rather than pretend the two original basepoints are definitionally equal. -/
theorem periodMarking_markedSegments (τ σ : ℍ) (i : Fin 2) (s : unitInterval) :
    (periodMarking τ σ).toHomeomorph (normalizedTorusMarkingLoop τ i s) =
      normalizedTorusMarkingLoop σ i s := by
  change (periodMarking τ σ).toHomeomorph
    ((normalizedTorusModel τ).projection (s.val • normalizedTorusBasis τ i)) =
      (normalizedTorusModel σ).projection (s.val • normalizedTorusBasis σ i)
  rw [(periodMarking_spec τ σ).2, map_smul]
  have hb : periodChange τ σ (normalizedTorusBasis τ i) = normalizedTorusBasis σ i := by
    apply (normalizedTorusBasis σ).equivFun.injective
    rw [periodChange_coordinates]
    ext j
    simp only [Basis.equivFun_self]
  rw [hb]

/-- A family of genuine original marked compact surfaces, on the fixed actual
reference τ₀ and the existing target carrier, topology and complex atlas. -/
def normalizedMarkedFamily (τ₀ τ : ℍ) :
    MarkedRiemannSurface.{0, 0} (normalizedClosedTorus τ₀) :=
  markedNormalizedTorus (normalizedClosedTorus τ₀) τ
    (periodMarking τ₀ τ) (periodMarking_spec τ₀ τ).1

/-- The actual family in the original marked-surface quotient, using the fixed
reference torus and the relative marking maps from the cocycle. -/
def normalizedFamilyPoint (τ₀ τ : ℍ) : TeichmullerSpace.{0, 0} (normalizedClosedTorus τ₀) :=
  TeichmullerSpace.mk (normalizedMarkedFamily τ₀ τ)

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
