module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeDeformedCoefficientMap
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# The actual bounded coefficient transport on compatible Banach spaces

The literal ambient derivative and its actual inverse preserve the native
compatible closed subspaces. This follows from the genuine nonlinear maps
and their proved Fréchet derivatives, by closedness and directional limits.
Their restrictions are a continuous complex linear equivalence in the
unchanged original essential norms. The actual nonlinear compatible maps
have precisely these derivatives.

This supporting result does not assert nonzero Bers derivative conjugacy or
independence under changing the Teichmüller point's representative.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped ENNReal UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami

variable {Γ : Subgroup Deck}

/-- Differentiate the actual compatible translation and use its genuinely closed image. -/
theorem ambientDerivative_mem_compatible (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (μ : Space Γ) : ambientDerivative ν μ.val ∈ compatibleSubmodule (deformedGroup hΓ ν) := by
  have hlim := (hasFDerivAt_translation ν).lim μ.val
    (tendsto_norm_cobounded_atTop (E := ℂ))
  apply (isClosed_compatibleSubmodule (deformedGroup hΓ ν)).mem_of_tendsto hlim
  apply Eventually.of_forall
  intro c
  exact (compatibleSubmodule (deformedGroup hΓ ν)).smul_mem c
    ((compatibleSubmodule (deformedGroup hΓ ν)).sub_mem
      (translation_mem_compatible hΓ ν (ν.val + c⁻¹ • μ))
      (translation_mem_compatible hΓ ν ν.val))

/-- Differentiate the actual inverse compositions, rather than assuming inverse range. -/
theorem ambientInverse_mem_compatible (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (κ : Space (deformedGroup hΓ ν)) : ambientInverse ν κ.val ∈ compatibleSubmodule Γ := by
  have hlim := (hasFDerivAt_pullback ν).lim κ.val
    (tendsto_norm_cobounded_atTop (E := ℂ))
  change Tendsto (fun c : ℂ => c • (pullback ν (0 + c⁻¹ • κ.val) - pullback ν 0))
    (Bornology.cobounded ℂ) (𝓝 (ambientInverse ν κ.val)) at hlim
  apply (isClosed_compatibleSubmodule Γ).mem_of_tendsto hlim
  apply Eventually.of_forall
  intro c
  exact (compatibleSubmodule Γ).smul_mem c ((compatibleSubmodule Γ).sub_mem
    (pullback_mem_compatible hΓ ν (0 + c⁻¹ • κ)) (pullback_mem_compatible hΓ ν 0))

/-- The genuine literal bounded derivative with its proved compatible codomain. -/
def gammaDerivative (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    Space Γ →L[ℂ] Space (deformedGroup hΓ ν) :=
  ((ambientDerivative ν).domRestrict (compatibleSubmodule Γ)).codRestrict
    (compatibleSubmodule (deformedGroup hΓ ν)) (ambientDerivative_mem_compatible hΓ ν)

@[simp] theorem gammaDerivative_val (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (μ : Space Γ) : (gammaDerivative hΓ ν μ).val = ambientDerivative ν μ.val := rfl

/-- The genuine inverse bounded derivative with its proved original codomain. -/
def gammaInverse (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    Space (deformedGroup hΓ ν) →L[ℂ] Space Γ :=
  ((ambientInverse ν).domRestrict (compatibleSubmodule (deformedGroup hΓ ν))).codRestrict
    (compatibleSubmodule Γ) (ambientInverse_mem_compatible hΓ ν)

@[simp] theorem gammaInverse_val (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (κ : Space (deformedGroup hΓ ν)) : (gammaInverse hΓ ν κ).val = ambientInverse ν κ.val := rfl

theorem gammaInverse_gammaDerivative (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (μ : Space Γ) : gammaInverse hΓ ν (gammaDerivative hΓ ν μ) = μ := by
  apply Subtype.ext
  exact ambientInverse_ambientDerivative ν μ.val

theorem gammaDerivative_gammaInverse (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (κ : Space (deformedGroup hΓ ν)) : gammaDerivative hΓ ν (gammaInverse hΓ ν κ) = κ := by
  apply Subtype.ext
  exact ambientDerivative_ambientInverse ν κ.val

/-- The actual all-coefficient complex transport equivalence in the native infinity norms. -/
def gammaEquiv (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    Space Γ ≃L[ℂ] Space (deformedGroup hΓ ν) where
  toLinearEquiv :=
    { (gammaDerivative hΓ ν).toLinearMap with
      invFun := gammaInverse hΓ ν
      left_inv := gammaInverse_gammaDerivative hΓ ν
      right_inv := gammaDerivative_gammaInverse hΓ ν }
  continuous_toFun := (gammaDerivative hΓ ν).continuous
  continuous_invFun := (gammaInverse hΓ ν).continuous

@[simp] theorem gammaEquiv_val (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (μ : Space Γ) : (gammaEquiv hΓ ν μ).val = ambientDerivative ν μ.val := rfl

@[simp] theorem gammaEquiv_symm_val (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    (κ : Space (deformedGroup hΓ ν)) : ((gammaEquiv hΓ ν).symm κ).val =
      ambientInverse ν κ.val := rfl

/-- The literal compatible translation has its genuine Banach derivative at the base. -/
theorem hasFDerivAt_gammaTranslation (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    HasFDerivAt (gammaTranslation hΓ ν) (gammaDerivative hΓ ν) ν.val := by
  have hd := (hasFDerivAt_translation ν).comp ν.val
    ((compatibleSubmodule Γ).subtypeL.hasFDerivAt)
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  have he := Asymptotics.isLittleO_iff.mp
    (hasFDerivAt_iff_isLittleO_nhds_zero.mp hd) hε
  filter_upwards [he] with μ hμ
  change ‖translation ν ((ν.val + μ).val) - translation ν ν.val.val -
    ambientDerivative ν μ.val‖ ≤ ε * ‖μ‖
  exact hμ

/-- The actual compatible inverse map has the inverse genuine Banach derivative at zero. -/
theorem hasFDerivAt_gammaPullback (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    HasFDerivAt (gammaPullback hΓ ν) (gammaInverse hΓ ν) 0 := by
  have hd := (hasFDerivAt_pullback ν).comp (0 : Space (deformedGroup hΓ ν))
    ((compatibleSubmodule (deformedGroup hΓ ν)).subtypeL.hasFDerivAt)
  apply hasFDerivAt_iff_isLittleO_nhds_zero.mpr
  apply Asymptotics.isLittleO_iff.mpr
  intro ε hε
  have he := Asymptotics.isLittleO_iff.mp
    (hasFDerivAt_iff_isLittleO_nhds_zero.mp hd) hε
  filter_upwards [he] with κ hκ
  change ‖pullback ν ((0 + κ).val) - pullback ν 0 - ambientInverse ν κ.val‖ ≤ ε * ‖κ‖
  exact hκ

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
