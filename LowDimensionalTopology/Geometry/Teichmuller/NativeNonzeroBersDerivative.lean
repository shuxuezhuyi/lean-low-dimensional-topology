module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeInverseBersDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersTranslationLocalInverse
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Genuine nonzero Bers derivatives in the original native Banach spaces

The actual coordinate translation is continuous at the original Bers point
and has the proved normalized pullback as a local left inverse. The genuine
invertible derivative of that pullback therefore gives the true derivative
of the actual coordinate translation.

For original coefficients near the given nonzero coefficient, the translated
Bers composite is continuous by its proved Frechet derivative. Its smallness
and the actual image left-inverse equation express the original Bers map as
the actual inverse germ composed with that translated composite. This proves
its genuine Frechet derivative in every original coefficient direction,
without assuming continuity of the original map at the nonzero point.
The actual derivatives obey the literal deformed Bers integral transport
identity, in the unchanged coefficient and weighted automorphic norms.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Surfaces

variable {Γ : Subgroup Deck}

/-- Nearby original coefficient values are represented by the actual inverse germ and composite. -/
theorem automorphicProjection_eq_inverseBersGerm_translated_eventually
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    ∀ᶠ μ : Space Γ in 𝓝 ν.val,
      BersWeighted.automorphicProjection hΓ μ =
        inverseBersGerm hΓ ν (translatedBersProjection hΓ ν μ) := by
  have ht := hasFDerivAt_translatedBersProjection hΓ ν
  have htarget : Metric.ball
      (0 : BersWeighted.Automorphic (deformedGroup hΓ ν)) (1 / 2) ∈
      𝓝 (translatedBersProjection hΓ ν ν.val) := by
    rw [translatedBersProjection_base]
    exact Metric.ball_mem_nhds _ (by norm_num)
  have hsmall : ∀ᶠ μ : Space Γ in 𝓝 ν.val,
      ‖translatedBersProjection hΓ ν μ‖ < 1 / 2 := by
    let : ContinuousAdd (BersWeighted.Automorphic (deformedGroup hΓ ν)) :=
      (Submodule.isTopologicalAddGroup
        (BersWeighted.automorphicSubmodule (deformedGroup hΓ ν))).toContinuousAdd
    filter_upwards [ht.continuousAt.preimage_mem_nhds htarget] with μ hμ
    exact mem_ball_zero_iff.mp hμ
  have hball : Metric.ball (0 : Space Γ) 1 ∈ 𝓝 ν.val :=
    Metric.isOpen_ball.mem_nhds ν.property
  filter_upwards [hball, hsmall] with μ hμ hsmallμ
  let μB : Ball Γ := ⟨μ, hμ⟩
  have hμn : ‖μ‖ < 1 := mem_ball_zero_iff.mp hμ
  have himage : BersWeighted.automorphicProjection hΓ μ ∈ nativeUniversalBersImage Γ := by
    refine ⟨(toSourceGamma μB).val, ?_⟩
    change LiZhongQC.bersFunction (planeRepresentative μ.val) =
      ((BersWeighted.automorphicProjection hΓ μ).toSource : ℂ → ℂ)
    exact (BersWeighted.automorphicProjection_toSource_eq hΓ μ hμn).symm
  have hcomm : bersTranslation hΓ ν (BersWeighted.automorphicProjection hΓ μ) =
      translatedBersProjection hΓ ν μ :=
    bersTranslation_automorphicProjection hΓ ν μB
  have hleft := inverseBersGerm_bersTranslation_of_image hΓ ν
    (BersWeighted.automorphicProjection hΓ μ) himage (by rw [hcomm]; exact hsmallμ)
  rw [hcomm] at hleft
  exact hleft.symm

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)

/-- The actual transported integral, followed by the genuine inverse-coordinate derivative. -/
def nonzeroBersDerivative (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    Space Γ →L[ℂ] BersWeighted.Automorphic Γ :=
  (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).toContinuousLinearMap.comp
    ((BersWeighted.automorphicIntegralOperator (deformedGroup_spec hΓ ν).1).comp
      (gammaDerivative hΓ ν))

/-- The original coordinate translation has the inverse of the actual inverse-germ derivative. -/
theorem hasFDerivAt_bersTranslation (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    HasFDerivAt (bersTranslation hΓ ν)
      (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm.toContinuousLinearMap
      (baseBersValue hΓ ν) := by
  have hf : HasFDerivAt (inverseBersGerm hΓ ν)
      (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).toContinuousLinearMap
      (bersTranslation hΓ ν (baseBersValue hΓ ν)) := by
    simpa only [bersTranslation_base] using
      hasFDerivAt_inverseBersGerm_equiv R hp hg hgenus hΓ ν
  exact HasFDerivAt.of_local_left_inverse (continuousAt_bersTranslation_base hΓ ν)
    hf (inverseBersGerm_bersTranslation_eventually hΓ ν)

/-- The original nonzero Bers projection is genuinely Frechet differentiable in all native directions. -/
theorem hasFDerivAt_automorphicProjection_nonzero (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    HasFDerivAt (BersWeighted.automorphicProjection hΓ)
      (nonzeroBersDerivative R hp hg hgenus hΓ ν) ν.val := by
  have hE : HasFDerivAt (inverseBersGerm hΓ ν)
      (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).toContinuousLinearMap
      (translatedBersProjection hΓ ν ν.val) := by
    simpa only [translatedBersProjection_base] using
      hasFDerivAt_inverseBersGerm_equiv R hp hg hgenus hΓ ν
  have hcomp := hE.comp ν.val (hasFDerivAt_translatedBersProjection hΓ ν)
  exact hcomp.congr_of_eventuallyEq
    (automorphicProjection_eq_inverseBersGerm_translated_eventually hΓ ν)

/-- The public derivative equality retains the actual coordinate map and original base point. -/
theorem fderiv_bersTranslation (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    fderiv ℂ (bersTranslation hΓ ν) (baseBersValue hΓ ν) =
      (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm.toContinuousLinearMap :=
  (hasFDerivAt_bersTranslation R hp hg hgenus hΓ ν).fderiv

/-- The public derivative equality retains the actual original projection at the actual coefficient. -/
theorem fderiv_automorphicProjection_nonzero (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    fderiv ℂ (BersWeighted.automorphicProjection hΓ) ν.val =
      nonzeroBersDerivative R hp hg hgenus hΓ ν :=
  (hasFDerivAt_automorphicProjection_nonzero R hp hg hgenus hΓ ν).fderiv

/-- The actual coordinate derivative cancels the actual inverse-coordinate derivative. -/
theorem nonzeroBersDerivative_commutation (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm.toContinuousLinearMap.comp
        (nonzeroBersDerivative R hp hg hgenus hΓ ν) =
      (BersWeighted.automorphicIntegralOperator (deformedGroup_spec hΓ ν).1).comp
        (gammaDerivative hΓ ν) := by
  apply ContinuousLinearMap.ext
  intro μ
  change (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm
      ((inverseBersDerivativeEquiv R hp hg hgenus hΓ ν)
        (((BersWeighted.automorphicIntegralOperator (deformedGroup_spec hΓ ν).1).comp
          (gammaDerivative hΓ ν)) μ)) = _
  exact (inverseBersDerivativeEquiv R hp hg hgenus hΓ ν).symm_apply_apply _

include R hp hg hgenus in
/-- Genuine Frechet derivatives of the actual maps satisfy the literal transported-integral identity. -/
theorem fderiv_bersTranslation_comp_fderiv_automorphicProjection
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    (fderiv ℂ (bersTranslation hΓ ν) (baseBersValue hΓ ν)).comp
        (fderiv ℂ (BersWeighted.automorphicProjection hΓ) ν.val) =
      (BersWeighted.automorphicIntegralOperator (deformedGroup_spec hΓ ν).1).comp
        (gammaDerivative hΓ ν) := by
  rw [fderiv_bersTranslation R hp hg hgenus hΓ ν,
    fderiv_automorphicProjection_nonzero R hp hg hgenus hΓ ν]
  exact nonzeroBersDerivative_commutation R hp hg hgenus hΓ ν

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
