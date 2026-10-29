module

public import LowDimensionalTopology.Geometry.Teichmuller.FundamentalPetersson

/-!
# The full original quadratic space with its canonical Petersson Hilbert norm

This normed model retains precisely the original global quadratic differentials.
The actual region is an index because it determines the integral norm. The
identity source equivalence exposes every original vector, and descent proves
that the uniformizing coefficients cover all holomorphic automorphic forms.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NativePetersson

open Surfaces WeilPetersson

universe u

/-- All original-atlas quadratic differentials, carrying the full-region
Petersson norm supplied by the instances below. No vector is added or removed. -/
def Space {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (_P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (_p : ℍ → X)
    (_hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ _p)
    (_F : Set ℍ) (_hF : Fuchsian.IsHalfPlaneFundamentalRegion _P _F) : Type u :=
  HolomorphicQuadraticDifferential R.toRiemannAtlas

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (P : Fuchsian.HalfPlaneFuchsianGroup (Γ.map Hyperbolic.realSLMobius))
    (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    (F : Set ℍ) (hF : Fuchsian.IsHalfPlaneFundamentalRegion P F)

instance : NormedAddCommGroup (Space R P p hp F hF) :=
  fundamentalQuadraticNormedAddCommGroup R P p hp hF

/-- Addition is uniform for the existing full Petersson norm and its actual topology. -/
instance : IsUniformAddGroup (Space R P p hp F hF) :=
  (fundamentalQuadraticNormedAddCommGroup R P p hp hF).toSeminormedAddCommGroup.to_isUniformAddGroup

instance : InnerProductSpace ℂ (Space R P p hp F hF) :=
  fundamentalQuadraticInnerProductSpace R P p hp hF

/-- Register exactly the normed-space projection of the existing Petersson inner product. -/
instance instNormedSpace : NormedSpace ℂ (Space R P p hp F hF) :=
  (fundamentalQuadraticInnerProductSpace R P p hp hF).toNormedSpace

/-- The original scalar action is continuous in the existing full Petersson topology. -/
instance : ContinuousSMul ℂ (Space R P p hp F hF) := by
  let : NormedSpace ℂ (Space R P p hp F hF) :=
    (fundamentalQuadraticInnerProductSpace R P p hp hF).toNormedSpace
  let : IsBoundedSMul ℂ (Space R P p hp F hF) := NormedSpace.toIsBoundedSMul
  exact IsBoundedSMul.continuousSMul

instance : FiniteDimensional ℂ (Space R P p hp F hF) :=
  R.finiteDimensional_holomorphicQuadraticDifferential

instance : CompleteSpace (Space R P p hp F hF) :=
  fundamentalQuadratic_completeSpace R P p hp hF

/-- The underlying original-atlas vector is unchanged. -/
def toQuadratic : Space R P p hp F hF ≃ₗ[ℂ]
    HolomorphicQuadraticDifferential R.toRiemannAtlas :=
  LinearEquiv.refl ℂ _

/-- The literal uniformizing coefficient as a complex linear map. -/
def lift : Space R P p hp F hF →ₗ[ℂ] (ℍ → ℂ) :=
  (liftQuadratic R.toRiemannAtlas p).comp (toQuadratic R P p hp F hF).toLinearMap

/-- The native norm is the exact Petersson norm in the book's curvature -1 convention. -/
theorem norm_eq_sqrt_integral (q : Space R P p hp F hF) :
    ‖q‖ = Real.sqrt (∫ z in F, z.im ^ 2 * ‖lift R P p hp F hF q z‖ ^ 2 ∂flatArea) :=
  fundamentalQuadraticNorm_eq_sqrt R P p hp hF q

/-- The genuine Hilbert inner product is the literal full-region Petersson pairing. -/
theorem inner_eq_integral (q r : Space R P p hp F hF) :
    inner ℂ q r = ∫ z in F, ((z.im ^ 2 : ℝ) : ℂ) *
      lift R P p hp F hF r z * star (lift R P p hp F hF q z) ∂flatArea := rfl

/-- The original lift is faithful on all native global differentials. -/
theorem lift_injective : Function.Injective (lift R P p hp F hF) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  intro q r he
  apply sub_eq_zero.mp
  by_contra hn
  have hn' : (toQuadratic R P p hp F hF (q - r) : X → ℂ → ℂ) ≠ 0 := by
    intro hz
    exact hn (Subtype.ext hz)
  obtain ⟨z, hz, hne⟩ := LiZhongQC.utm_liftQD_ne
    (toQuadratic R P p hp F hF (q - r)).property hn' hp
  have hzero : lift R P p hp F hF (q - r) ⟨z, hz⟩ = 0 := by
    rw [map_sub]
    change lift R P p hp F hF q ⟨z, hz⟩ - lift R P p hp F hF r ⟨z, hz⟩ = 0
    rw [congrFun he ⟨z, hz⟩, sub_self]
  exact hne hzero

/-- Every actual holomorphic automorphic coefficient is the lift of an
original-atlas differential. Off-half-plane values are irrelevant explicitly. -/
theorem exists_lift_of_automorphic {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ LiZhongQC.upperHalf)
    (hφΓ : ∀ γ ∈ Γ, ∀ z ∈ LiZhongQC.upperHalf,
      φ (((γ 0 0 : ℂ) * z + γ 0 1) / ((γ 1 0 : ℂ) * z + γ 1 1)) /
        ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z) :
    ∃ q : Space R P p hp F hF, ∀ z : ℍ, lift R P p hp F hF q z = φ z := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨q, hq, he⟩ := LiZhongQC.utm_x_descent hp hφ hφΓ
  exact ⟨⟨q, hq⟩, fun z => he (z : ℂ) z.im_pos⟩

end LowDimensionalTopology.Geometry.Teichmuller.NativePetersson
