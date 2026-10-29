module

public import LowDimensionalTopology.Geometry.Teichmuller.HarmonicPeterssonCompatibility

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.NativePetersson
open Surfaces WeilPetersson

/-- Pullback of a Hermitian form along a continuous linear equivalence. -/
@[instance_reducible]
def pullbackHermitianCore {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [TopologicalSpace V] [AddCommGroup W] [Module ℂ W] [TopologicalSpace W]
    (c : InnerProductSpace.Core ℂ W) (e : V ≃L[ℂ] W) : InnerProductSpace.Core ℂ V where
  inner v w := c.inner (e v) (e w)
  conj_inner_symm v w := c.conj_inner_symm (e v) (e w)
  re_inner_nonneg v := c.re_inner_nonneg (e v)
  add_left v w z := by rw [map_add, c.add_left]
  smul_left v w a := by rw [map_smul, c.smul_left]
  definite v hv := e.injective ((c.definite (e v) hv).trans (map_zero e).symm)

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup GammaMeasurableBeltrami.Deck}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius)) (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

/-- The Hermitian form of the harmonic Petersson integral, using the
conjugate-first convention for its two arguments. -/
@[instance_reducible]
def harmonicHermitianCore : InnerProductSpace.Core ℂ (Harmonic R P p hp F hF) where
  inner μ ν := inner ℂ (rieszQuadratic R P p hp F hF ν.val)
    (rieszQuadratic R P p hp F hF μ.val)
  conj_inner_symm μ ν := inner_conj_symm _ _
  re_inner_nonneg μ := inner_self_nonneg
  add_left μ ν ξ := by
    change inner ℂ (rieszQuadratic R P p hp F hF ξ.val)
      (rieszQuadratic R P p hp F hF (μ.val + ν.val)) = _
    rw [rieszQuadratic_add]
    exact _root_.inner_add_right (𝕜 := ℂ)
      (rieszQuadratic R P p hp F hF ξ.val)
      (rieszQuadratic R P p hp F hF μ.val) (rieszQuadratic R P p hp F hF ν.val)
  smul_left μ ν a := by
    change inner ℂ (rieszQuadratic R P p hp F hF ν.val)
      (rieszQuadratic R P p hp F hF (a • μ.val)) = _
    rw [rieszQuadratic_smul]
    exact _root_.inner_smul_right (𝕜 := ℂ)
      (rieszQuadratic R P p hp F hF ν.val)
      (rieszQuadratic R P p hp F hF μ.val) ((starRingEnd ℂ) a)
  definite μ hμ := by
    have hρ : rieszQuadratic R P p hp F hF μ.val = 0 := inner_self_eq_zero.mp hμ
    have hpair : pairingMap R P p hp F hF μ.val = 0 := by
      have ht := (InnerProductSpace.toDual ℂ (Space R P p hp F hF)).apply_symm_apply
        (pairingMap R P p hp F hF μ.val)
      change (InnerProductSpace.toDual ℂ (Space R P p hp F hF))
        (rieszQuadratic R P p hp F hF μ.val) = _ at ht
      rw [hρ, map_zero] at ht
      exact ht.symm
    have hm : μ.val ∈ (harmonicProjection R P p hp F hF).ker := by
      rw [harmonicProjection_ker, ← pairingMap_ker R P p hp F hF]
      exact hpair
    apply Subtype.ext
    exact ((mem_harmonicSubmodule_iff R P p hp F hF μ.val).mp μ.property).symm.trans hm

/-- Reversing the slots recovers the first-linear harmonic integral. -/
theorem harmonicHermitianCore_inner (μ ν : Harmonic R P p hp F hF) :
    (harmonicHermitianCore R P p hp F hF).inner ν μ =
      beltramiPairing F μ.val.val ν.val.val :=
  (harmonicPairing_eq_riesz_inner R P p hp F hF μ ν).symm

end LowDimensionalTopology.Geometry.Teichmuller.NativePetersson
