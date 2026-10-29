module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeHarmonicAhlforsWeill
public import LowDimensionalTopology.Geometry.Teichmuller.NativeDeformedBersNaturality
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedNativeTarget

/-!
# Same-point harmonic identification is the identity on actual coefficient classes

The existing harmonic derivative identifies each original harmonic space
with its full weighted automorphic space. The previously proved same-point
weighted identification is the identity isometry on actual vectors.
The literal Ahlfors-Weill description of the harmonic inverse proves that
the resulting harmonic identification is precisely the existing coefficient
class identity, in the unchanged inherited L-infinity norm.

The actual compact targets and their original harmonic spaces are retained.
No equality of matrix-lift subgroups or chosen surface carriers is asserted.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Surfaces

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup Deck} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    (ν ν' : Ball Γ)
    (hpoint : TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν =
      TeichmullerSpace.coefficientProjectionBall R hg hgenus
        (canonicalHandleGroupPresentation g) hΓ hfree hp ν')

/-- The literal section commutes with the genuine same-point identity identifications. -/
theorem nativePointDeformedCoefficientEquiv_ahlforsWeill
    (φ : BersWeighted.Automorphic (deformedGroup hΓ ν)) :
    nativePointDeformedCoefficientEquiv R hp hg hgenus hΓ hfree ν ν' hpoint
        (BersWeighted.ahlforsWeill φ) =
      BersWeighted.ahlforsWeill
        (nativePointDeformedBersEquiv R hp hg hgenus hΓ hfree ν ν' hpoint φ) := by
  have hs : ((nativePointDeformedBersEquiv R hp hg hgenus hΓ hfree ν ν' hpoint φ).toSource :
      ℂ → ℂ) = (φ.toSource : ℂ → ℂ) := by
    change BersWeighted.decode
        (nativePointDeformedBersEquiv R hp hg hgenus hΓ hfree ν ν' hpoint φ).val =
      BersWeighted.decode φ.val
    rw [nativePointDeformedBersEquiv_val]
  apply Subtype.ext
  rw [nativePointDeformedCoefficientEquiv_val]
  apply Lp.ext
  filter_upwards [BersWeighted.ahlforsWeill_coe_ae φ,
    BersWeighted.ahlforsWeill_coe_ae
      (nativePointDeformedBersEquiv R hp hg hgenus hΓ hfree ν ν' hpoint φ)]
    with z hz hz'
  rw [hz, hz', BersWeighted.ahlforsWeillCoefficient,
    BersWeighted.ahlforsWeillCoefficient, hs]

variable
    (P : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν).map Hyperbolic.realSLMobius))
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)
    (P' : Fuchsian.HalfPlaneFuchsianGroup ((deformedGroup hΓ ν').map Hyperbolic.realSLMobius))
    (F' : Set ℍ) (hF' : Fuchsian.IsHalfPlaneFundamentalRegion P' F')

local notation "RY" => deformedNativeSurface R hgenus hΓ hp ν
local notation "pY" => deformedTargetCover R hgenus hΓ hp ν
local notation "hpY" => deformedNativeSurface_uniformization R hgenus hΓ hp ν
local notation "RY'" => deformedNativeSurface R hgenus hΓ hp ν'
local notation "pY'" => deformedTargetCover R hgenus hΓ hp ν'
local notation "hpY'" => deformedNativeSurface_uniformization R hgenus hΓ hp ν'

/-- The actual same-point harmonic identification is supplied by the original restricted integral. -/
def nativePointDeformedHarmonicEquiv :
    NativePetersson.Harmonic RY P pY hpY F hF ≃L[ℂ]
      NativePetersson.Harmonic RY' P' pY' hpY' F' hF' :=
  ((NativePetersson.harmonicDerivativeEquiv RY P pY hpY F hF (deformedGroup_spec hΓ ν).1).trans
    (nativePointDeformedBersEquiv R hp hg hgenus hΓ hfree ν ν' hpoint)).trans
      (NativePetersson.harmonicDerivativeEquiv RY' P' pY' hpY' F' hF'
        (deformedGroup_spec hΓ ν').1).symm

/-- This harmonic identification is exactly the existing identity of original coefficient classes. -/
theorem nativePointDeformedHarmonicEquiv_val
    (μ : NativePetersson.Harmonic RY P pY hpY F hF) :
    (nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint
      P F hF P' F' hF' μ).val =
        nativePointDeformedCoefficientEquiv R hp hg hgenus hΓ hfree ν ν' hpoint μ.val := by
  let e := NativePetersson.harmonicDerivativeEquiv RY P pY hpY F hF (deformedGroup_spec hΓ ν).1
  have hμ : μ.val = BersWeighted.ahlforsWeill (e μ) :=
    (congrArg Subtype.val (e.symm_apply_apply μ)).symm.trans
      (NativePetersson.harmonicDerivativeEquiv_symm_val_eq_ahlforsWeill
        RY P pY hpY F hF (deformedGroup_spec hΓ ν).1 (e μ))
  change ((NativePetersson.harmonicDerivativeEquiv RY' P' pY' hpY' F' hF'
    (deformedGroup_spec hΓ ν').1).symm
      (nativePointDeformedBersEquiv R hp hg hgenus hΓ hfree ν ν' hpoint (e μ))).val = _
  rw [NativePetersson.harmonicDerivativeEquiv_symm_val_eq_ahlforsWeill, hμ]
  exact (nativePointDeformedCoefficientEquiv_ahlforsWeill
    R hp hg hgenus hΓ hfree ν ν' hpoint (e μ)).symm

/-- The harmonic same-point identification preserves the entire inherited original infinity norm. -/
theorem norm_nativePointDeformedHarmonicEquiv
    (μ : NativePetersson.Harmonic RY P pY hpY F hF) :
    ‖nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint
      P F hF P' F' hF' μ‖ = ‖μ‖ := by
  change ‖(nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint
    P F hF P' F' hF' μ).val‖ = ‖μ.val‖
  rw [nativePointDeformedHarmonicEquiv_val]
  exact norm_nativePointDeformedCoefficientEquiv R hp hg hgenus hΓ hfree ν ν' hpoint μ.val

/-- The actual harmonic identification is an isometry, not merely an abstract vector isomorphism. -/
theorem isometry_nativePointDeformedHarmonicEquiv :
    Isometry (nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint
      P F hF P' F' hF') :=
  AddMonoidHomClass.isometry_of_norm _
    (norm_nativePointDeformedHarmonicEquiv R hp hg hgenus hΓ hfree ν ν' hpoint P F hF P' F' hF')

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
