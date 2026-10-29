module

public import LowDimensionalTopology.Geometry.Teichmuller.HarmonicHermitianCompatibility

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NativePetersson
open Surfaces WeilPetersson
universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius)) (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

/-- The actual two-slot harmonic integral is the genuine Petersson Riesz inner product. -/
theorem harmonicPairing_eq_riesz_inner (μ ν : Harmonic R P p hp F hF) :
    beltramiPairing F μ.val.val ν.val.val =
      inner ℂ (rieszQuadratic R P p hp F hF μ.val)
        (rieszQuadratic R P p hp F hF ν.val) := by
  have hν := (mem_harmonicSubmodule_iff R P p hp F hF ν.val).mp ν.property
  have h := beltramiPairing_harmonicProjection_right R P p hp F hF μ.val ν.val
  rw [hν] at h
  apply h.trans
  change pairingMap R P p hp F hF μ.val (rieszQuadratic R P p hp F hF ν.val) =
    inner ℂ ((InnerProductSpace.toDual ℂ (Space R P p hp F hF)).symm
      (pairingMap R P p hp F hF μ.val)) (rieszQuadratic R P p hp F hF ν.val)
  exact InnerProductSpace.toDual_symm_apply.symm

end LowDimensionalTopology.Geometry.Teichmuller.NativePetersson
