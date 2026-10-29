module

public import LowDimensionalTopology.Geometry.Teichmuller.GenusOnePeriodBeltramiDerivative
public import LowDimensionalTopology.Geometry.Teichmuller.ComplexBeltramiMetricContinuity

/-!
# The actual relative tensors of the fixed-reference marked-torus family

The existing relative smooth map of the original marked surfaces is precisely
the actual period marking. Its tensor curve is therefore the same original
source-atlas Banach curve, with its already constructed infinitesimal tensor.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GenusOne
open Surfaces

/-- The fixed-reference marked family's actual relative map is the period
marking between its two original target tori. -/
theorem relativeSmooth_normalizedMarkedFamily (τ₀ τ σ : ℍ) :
    MarkedRiemannSurface.relativeSmooth
      (normalizedMarkedFamily τ₀ τ) (normalizedMarkedFamily τ₀ σ) =
        periodMarking τ σ := by
  change SmoothSurfaceEquiv.trans (SmoothSurfaceEquiv.symm (periodMarking τ₀ τ))
    (periodMarking τ₀ σ) = periodMarking τ σ
  apply DFunLike.ext _ (periodMarking τ σ)
  intro x
  change (periodMarking τ₀ σ).toHomeomorph
      ((periodMarking τ₀ τ).toHomeomorph.symm x) =
    (periodMarking τ σ).toHomeomorph x
  have h := periodMarking_cocycle τ₀ τ σ
    ((periodMarking τ₀ τ).toHomeomorph.symm x)
  rw [(periodMarking τ₀ τ).toHomeomorph.apply_symm_apply] at h
  exact h.symm

/-- The genuine relative Beltrami tensors of the fixed-reference marked family,
all on the actual original atlas of its target torus at the base period. -/
def nativeRelativePeriodBeltramiCurve (τ₀ τ : ℍ) (t : ℂ) :
    BeltramiDifferential.BanachSpace
      (normalizedTorusModel τ).surface.toRiemannAtlas :=
  BeltramiDifferential.ofTensor
    ((MarkedRiemannSurface.relativeSmooth
      (normalizedMarkedFamily τ₀ τ)
      (normalizedMarkedFamily τ₀ (nearbyPeriod τ t))).beltrami
        (MarkedRiemannSurface.relativeSmooth_orientation
          (normalizedMarkedFamily τ₀ τ)
          (normalizedMarkedFamily τ₀ (nearbyPeriod τ t))))

/-- The original marked-family relative tensor curve is the actual period
tensor curve, with the finite map equality proved from the cocycle. -/
theorem nativeRelativePeriodBeltramiCurve_eq_periodBeltramiCurve (τ₀ τ : ℍ) :
    nativeRelativePeriodBeltramiCurve τ₀ τ = periodBeltramiCurve τ := by
  funext t
  let f : SmoothSurfaceEquiv (normalizedTorusModel τ).surface
      (normalizedTorusModel (nearbyPeriod τ t)).surface :=
    MarkedRiemannSurface.relativeSmooth
      (normalizedMarkedFamily τ₀ τ) (normalizedMarkedFamily τ₀ (nearbyPeriod τ t))
  have hf : PreservesComplexOrientation (normalizedTorusModel τ).surface.toRiemannAtlas
      (normalizedTorusModel (nearbyPeriod τ t)).surface.toRiemannAtlas f.toHomeomorph :=
    MarkedRiemannSurface.relativeSmooth_orientation
      (normalizedMarkedFamily τ₀ τ) (normalizedMarkedFamily τ₀ (nearbyPeriod τ t))
  have hcongr
      (f g : SmoothSurfaceEquiv (normalizedTorusModel τ).surface
        (normalizedTorusModel (nearbyPeriod τ t)).surface)
      (hfg : f = g)
      (hf : PreservesComplexOrientation (normalizedTorusModel τ).surface.toRiemannAtlas
        (normalizedTorusModel (nearbyPeriod τ t)).surface.toRiemannAtlas f.toHomeomorph)
      (hg : PreservesComplexOrientation (normalizedTorusModel τ).surface.toRiemannAtlas
        (normalizedTorusModel (nearbyPeriod τ t)).surface.toRiemannAtlas g.toHomeomorph) :
      BeltramiDifferential.ofTensor (f.beltrami hf) =
        BeltramiDifferential.ofTensor (g.beltrami hg) := by
    cases hfg
    rfl
  exact hcongr f _ (relativeSmooth_normalizedMarkedFamily τ₀ τ (nearbyPeriod τ t)) hf _

/-- The actual fixed-reference marked family's relative tensor derivative is
the original infinitesimal period-marking tensor. -/
theorem hasDerivAt_nativeRelativePeriodBeltramiCurve_zero (τ₀ τ : ℍ) :
    HasDerivAt (nativeRelativePeriodBeltramiCurve τ₀ τ)
      (periodTangentBeltrami τ) 0 := by
  rw [nativeRelativePeriodBeltramiCurve_eq_periodBeltramiCurve]
  exact hasDerivAt_periodBeltramiCurve_zero τ

end LowDimensionalTopology.Geometry.Teichmuller.GenusOne
