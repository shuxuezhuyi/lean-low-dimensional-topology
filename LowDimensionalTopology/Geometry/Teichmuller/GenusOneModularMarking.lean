module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOneSmoothPeriodMarking
public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.TorusAffineDescent
public import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
public import Mathlib.Tactic.LinearCombination

/-!
# The modular change of an actual smooth torus marking

The two basis-vector identities prove
`hτ ∘ fγτ = fτ ∘ hτ₀ ∘ fγτ₀`. All maps descend through the original analytic
torus covers, and the final equality is in the actual marked-surface quotient.

Matrices use Mathlib's `SL(2, ℤ)` action on the upper half-plane. No arbitrary
surface classification, canonical-cut realization, or new moduli carrier is
used.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Module
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne

open Surfaces

/-- The literal scalar `cτ+d` in the source's holomorphic torus map. -/
def modularDenominator (M : SL(2, ℤ)) (τ : ℍ) : ℂ :=
  (M 1 0 : ℂ) * (τ : ℂ) + (M 1 1 : ℂ)

private theorem modular_det (M : SL(2, ℤ)) :
    M 0 0 * M 1 1 - M 0 1 * M 1 0 = (1 : ℤ) := by
  simpa only [Matrix.det_fin_two] using M.property

theorem modularDenominator_ne_zero (M : SL(2, ℤ)) (τ : ℍ) :
    modularDenominator M τ ≠ 0 := by
  intro hzero
  have hcR : (M 1 0 : ℝ) * τ.im = 0 := by
    simpa only [modularDenominator, Complex.add_im, Complex.mul_im,
      Complex.intCast_re, Complex.intCast_im, UpperHalfPlane.coe_im,
      zero_mul, add_zero, Complex.zero_im] using congrArg Complex.im hzero
  have hc : M 1 0 = 0 := by
    exact_mod_cast (mul_eq_zero.mp hcR).resolve_right τ.im_ne_zero
  have hd : M 1 1 = 0 := by
    have hdC : (M 1 1 : ℂ) = 0 := by simpa [modularDenominator, hc] using hzero
    exact_mod_cast hdC
  have hdet := modular_det M
  simp only [hc, hd, mul_zero, sub_self] at hdet
  exact zero_ne_one hdet

theorem modularDenominator_mul_parameter (M : SL(2, ℤ)) (τ : ℍ) :
    modularDenominator M τ * ((M • τ : ℍ) : ℂ) =
      (M 0 0 : ℂ) * (τ : ℂ) + (M 0 1 : ℂ) := by
  have haction : ((M • τ : ℍ) : ℂ) =
      ((M 0 0 : ℂ) * (τ : ℂ) + (M 0 1 : ℂ)) / modularDenominator M τ := by
    simpa [modularDenominator] using UpperHalfPlane.coe_specialLinearGroup_apply M τ
  rw [mul_comm, haction, div_mul_cancel₀ _ (modularDenominator_ne_zero M τ)]

private theorem modularDenominator_lattice_iff (M : SL(2, ℤ)) (τ : ℍ) (z : ℂ) :
    z ∈ normalizedPeriodLattice (M • τ) ↔
      modularDenominator M τ * z ∈ normalizedPeriodLattice τ := by
  let a : ℤ := M 0 0
  let b : ℤ := M 0 1
  let c : ℤ := M 1 0
  let d : ℤ := M 1 1
  have hdetC : (a : ℂ) * (d : ℂ) - (b : ℂ) * (c : ℂ) = 1 := by
    exact_mod_cast modular_det M
  have hcross := modularDenominator_mul_parameter M τ
  constructor
  · intro hz
    obtain ⟨m, n, hmn⟩ := (mem_normalizedPeriodLattice (M • τ) z).mp hz
    apply (mem_normalizedPeriodLattice τ _).mpr
    refine ⟨m * d + n * b, m * c + n * a, ?_⟩
    rw [← hmn, mul_add, mul_left_comm (modularDenominator M τ) (n : ℂ), hcross]
    dsimp only [modularDenominator, a, b, c, d]
    push_cast
    ring
  · intro hz
    obtain ⟨m, n, hmn⟩ := (mem_normalizedPeriodLattice τ _).mp hz
    apply (mem_normalizedPeriodLattice (M • τ) z).mpr
    refine ⟨a * m - b * n, -c * m + d * n, ?_⟩
    apply mul_left_cancel₀ (modularDenominator_ne_zero M τ)
    calc
      modularDenominator M τ *
          (((a * m - b * n : ℤ) : ℂ) +
            ((-c * m + d * n : ℤ) : ℂ) * ((M • τ : ℍ) : ℂ)) =
          ((a : ℂ) * (d : ℂ) - (b : ℂ) * (c : ℂ)) *
            ((m : ℂ) + (n : ℂ) * (τ : ℂ)) := by
        rw [mul_add, mul_left_comm (modularDenominator M τ)
          ((-c * m + d * n : ℤ) : ℂ), hcross]
        dsimp only [modularDenominator, a, b, c, d]
        push_cast
        ring
      _ = modularDenominator M τ * z := by rw [hdetC, one_mul, hmn]

/-- The source's exact complex-linear map descends to an actual biholomorphism. -/
theorem exists_modularBiholomorph (M : SL(2, ℤ)) (τ : ℍ) :
    ∃ h : ComplexTorusCarrier ≃ₜ ComplexTorusCarrier,
      RiemannAnalyticMap (normalizedTorusModel (M • τ)).surface.toRiemannAtlas
        (normalizedTorusModel τ).surface.toRiemannAtlas h ∧
      ∀ z : ℂ, h ((normalizedTorusModel (M • τ)).projection z) =
        (normalizedTorusModel τ).projection (modularDenominator M τ * z) := by
  obtain ⟨h, hh, _hhi, hcomm⟩ :=
    (normalizedTorusModel (M • τ)).affine_descends_to_analytic_homeomorph
      (normalizedTorusModel τ) (modularDenominator M τ) 0
      (modularDenominator_ne_zero M τ) (fun z => by
        rw [normalizedTorusBasis_span, normalizedTorusBasis_span]
        exact modularDenominator_lattice_iff M τ z)
  exact ⟨h, hh, fun z => by simpa only [add_zero] using hcomm z⟩

/-- The actual biholomorphism with the specified covering-plane scalar. -/
def modularBiholomorph (M : SL(2, ℤ)) (τ : ℍ) :
    ComplexTorusCarrier ≃ₜ ComplexTorusCarrier :=
  (exists_modularBiholomorph M τ).choose

theorem modularBiholomorph_analytic (M : SL(2, ℤ)) (τ : ℍ) :
    RiemannAnalyticMap (normalizedTorusModel (M • τ)).surface.toRiemannAtlas
      (normalizedTorusModel τ).surface.toRiemannAtlas (modularBiholomorph M τ) :=
  (exists_modularBiholomorph M τ).choose_spec.1

theorem modularBiholomorph_projection (M : SL(2, ℤ)) (τ : ℍ) (z : ℂ) :
    modularBiholomorph M τ ((normalizedTorusModel (M • τ)).projection z) =
      (normalizedTorusModel τ).projection (modularDenominator M τ * z) :=
  (exists_modularBiholomorph M τ).choose_spec.2 z

private theorem periodChange_basis (τ σ : ℍ) (i : Fin 2) :
    periodChange τ σ (normalizedTorusBasis τ i) = normalizedTorusBasis σ i := by
  apply (normalizedTorusBasis σ).equivFun.injective
  rw [periodChange_coordinates]
  funext j
  simp only [Basis.equivFun_self]

private theorem periodChange_one (τ σ : ℍ) : periodChange τ σ 1 = 1 := by
  simpa only [normalizedTorusBasis_zero] using periodChange_basis τ σ 0

private theorem periodChange_parameter (τ σ : ℍ) :
    periodChange τ σ (τ : ℂ) = (σ : ℂ) := by
  simpa only [normalizedTorusBasis_one] using periodChange_basis τ σ 1

private theorem periodChange_int_combination (τ σ : ℍ) (m n : ℤ) :
    periodChange τ σ ((m : ℂ) * (τ : ℂ) + (n : ℂ)) =
      (m : ℂ) * (σ : ℂ) + (n : ℂ) := by
  have h := map_add (periodChange τ σ) (m • (τ : ℂ)) (n • (1 : ℂ))
  rw [map_zsmul, map_zsmul, periodChange_parameter, periodChange_one] at h
  simpa only [zsmul_eq_mul, mul_one] using h

private def modularScaleLinear (M : SL(2, ℤ)) (τ : ℍ) : ℂ →ₗ[ℝ] ℂ where
  toFun z := modularDenominator M τ * z
  map_add' := mul_add _
  map_smul' := by
    intro r z
    simp only [RingHom.id_apply, Complex.real_smul]
    ring

/-- The two period identities in the notes determine the entire real-linear
lift, hence the exact equality needed for the marking action. -/
theorem modular_periodChange (τ₀ τ : ℍ) (M : SL(2, ℤ)) (z : ℂ) :
    modularDenominator M τ * periodChange τ₀ (M • τ) z =
      periodChange τ₀ τ
        (modularDenominator M τ₀ * periodChange τ₀ (M • τ₀) z) := by
  let L : ℂ →ₗ[ℝ] ℂ :=
    (modularScaleLinear M τ).comp (periodChange τ₀ (M • τ)).toLinearMap
  let K : ℂ →ₗ[ℝ] ℂ :=
    (periodChange τ₀ τ).toLinearMap.comp
      ((modularScaleLinear M τ₀).comp (periodChange τ₀ (M • τ₀)).toLinearMap)
  have hLK : L = K := by
    apply (normalizedTorusBasis τ₀).ext
    intro i
    fin_cases i
    · change modularDenominator M τ *
          periodChange τ₀ (M • τ) (normalizedTorusBasis τ₀ 0) =
        periodChange τ₀ τ (modularDenominator M τ₀ *
          periodChange τ₀ (M • τ₀) (normalizedTorusBasis τ₀ 0))
      rw [periodChange_basis, periodChange_basis, normalizedTorusBasis_zero,
        normalizedTorusBasis_zero, mul_one, mul_one]
      exact (periodChange_int_combination τ₀ τ (M 1 0) (M 1 1)).symm
    · change modularDenominator M τ *
          periodChange τ₀ (M • τ) (normalizedTorusBasis τ₀ 1) =
        periodChange τ₀ τ (modularDenominator M τ₀ *
          periodChange τ₀ (M • τ₀) (normalizedTorusBasis τ₀ 1))
      rw [periodChange_basis, periodChange_basis, normalizedTorusBasis_one,
        normalizedTorusBasis_one, modularDenominator_mul_parameter,
        modularDenominator_mul_parameter]
      exact (periodChange_int_combination τ₀ τ (M 0 0) (M 0 1)).symm
  exact LinearMap.congr_fun hLK z

/-- The inverse of the notes' `ωγ`: first deform to `γτ₀`, then apply `hτ₀`.
Both smoothness and orientation follow from the genuine maps already proved. -/
def modularReferenceChange (τ₀ : ℍ) (M : SL(2, ℤ)) :
    OrientedSurfaceAut (normalizedClosedTorus τ₀) where
  smooth := SmoothSurfaceEquiv.trans (periodMarking τ₀ (M • τ₀))
    (SmoothSurfaceEquiv.ofConformalHomeomorph
      (normalizedTorusModel (M • τ₀)).surface (normalizedTorusModel τ₀).surface
      (modularBiholomorph M τ₀) (modularBiholomorph_analytic M τ₀))
  orientation_preserving :=
    (analyticHomeomorph_preservesComplexOrientation
      (modularBiholomorph M τ₀) (modularBiholomorph_analytic M τ₀)).comp
        (periodMarking_spec τ₀ (M • τ₀)).1
        (periodMarking τ₀ (M • τ₀)).toHomeomorph.continuous

/-- The actual positive smooth reference diffeomorphism `ωγ`. -/
def modularReferenceAut (τ₀ : ℍ) (M : SL(2, ℤ)) :
    OrientedSurfaceAut (normalizedClosedTorus τ₀) :=
  (modularReferenceChange τ₀ M)⁻¹

/-- Descent of the proved lift identity through the unchanged original cover. -/
theorem modularBiholomorph_periodMarking (τ₀ τ : ℍ) (M : SL(2, ℤ))
    (x : ComplexTorusCarrier) :
    modularBiholomorph M τ ((periodMarking τ₀ (M • τ)).toHomeomorph x) =
      (periodMarking τ₀ τ).toHomeomorph ((modularReferenceChange τ₀ M).toHomeomorph x) := by
  change modularBiholomorph M τ ((periodMarking τ₀ (M • τ)).toHomeomorph x) =
    (periodMarking τ₀ τ).toHomeomorph
      (modularBiholomorph M τ₀ ((periodMarking τ₀ (M • τ₀)).toHomeomorph x))
  obtain ⟨z, rfl⟩ := (normalizedTorusModel τ₀).surjective x
  rw [(periodMarking_spec τ₀ (M • τ)).2, modularBiholomorph_projection,
    (periodMarking_spec τ₀ (M • τ₀)).2, modularBiholomorph_projection,
    (periodMarking_spec τ₀ τ).2, modular_periodChange]

/-- The fractional modular parameter change is precisely inverse
precomposition by the source's actual reference diffeomorphism. -/
theorem modularReferenceAut_smul_normalizedFamilyPoint
    (τ₀ τ : ℍ) (M : SL(2, ℤ)) :
    MappingClassGroup.mk (modularReferenceAut τ₀ M) • normalizedFamilyPoint τ₀ τ =
      normalizedFamilyPoint τ₀ (M • τ) := by
  rw [MappingClassGroup.mk_smul]
  simp only [modularReferenceAut, inv_inv]
  change TeichmullerSpace.mk
      (MarkedRiemannSurface.precompose (modularReferenceChange τ₀ M).smooth
        (modularReferenceChange τ₀ M).orientation_preserving (normalizedMarkedFamily τ₀ τ)) =
    TeichmullerSpace.mk (normalizedMarkedFamily τ₀ (M • τ))
  apply (TeichmullerSpace.mk_eq_mk_iff _ _).mpr
  apply MarkedRiemannSurface.equivalent_symm
  refine ⟨modularBiholomorph M τ, modularBiholomorph_analytic M τ, ?_⟩
  change ContinuousMap.Homotopic
    ((_root_.toContinuousMap (modularBiholomorph M τ)).comp
      (_root_.toContinuousMap (periodMarking τ₀ (M • τ)).toHomeomorph))
    ((_root_.toContinuousMap (periodMarking τ₀ τ).toHomeomorph).comp
      (_root_.toContinuousMap (modularReferenceChange τ₀ M).toHomeomorph))
  have hmark :
      (_root_.toContinuousMap (modularBiholomorph M τ)).comp
          (_root_.toContinuousMap (periodMarking τ₀ (M • τ)).toHomeomorph) =
        (_root_.toContinuousMap (periodMarking τ₀ τ).toHomeomorph).comp
          (_root_.toContinuousMap (modularReferenceChange τ₀ M).toHomeomorph) := by
    apply ContinuousMap.ext
    intro x
    exact modularBiholomorph_periodMarking τ₀ τ M x
  rw [hmark]

/-- The two matrix representatives of a projective modular transformation
give the same action on every normalized marked torus. -/
theorem modularReferenceAut_neg_smul_normalizedFamilyPoint
    (τ₀ τ : ℍ) (M : SL(2, ℤ)) :
    MappingClassGroup.mk (modularReferenceAut τ₀ (-M)) • normalizedFamilyPoint τ₀ τ =
      MappingClassGroup.mk (modularReferenceAut τ₀ M) • normalizedFamilyPoint τ₀ τ := by
  rw [modularReferenceAut_smul_normalizedFamilyPoint,
    modularReferenceAut_smul_normalizedFamilyPoint, ModularGroup.SL_neg_smul]

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
