module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticBergmanKernel

/-!
# Reproduction of every original automorphic quadratic coefficient

Actual descent through the given uniformization identifies every holomorphic
automorphic coefficient with an original-atlas quadratic differential. The
existing compact-surface reproducing theorem therefore applies to the entire
coefficient space, with absolute convergence and the literal upper-half-plane
kernel. The Poincare density here is `1 / Im z`, so its inverse square is `y²`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory
open scoped Manifold ContDiff UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.QuadraticBergman

open Surfaces LiZhongQC

/-- The actual weight-four reproducing kernel on the original upper half-plane. -/
def halfPlaneQuadraticKernel (z ζ : ℂ) : ℂ :=
  (12 / Real.pi : ℂ) / (conj z - ζ) ^ 4

private theorem kernel_integrand_eq (φ : ℂ → ℂ) (z ζ : ℂ) :
    (ζ.im : ℂ) ^ 2 * φ ζ * conj (halfPlaneQuadraticKernel z ζ) =
      (12 / Real.pi : ℂ) * ((ζ.im : ℂ) ^ 2 * φ ζ / (conj ζ - z) ^ 4) := by
  have hpow : (z - conj ζ) ^ 4 = (conj ζ - z) ^ 4 := by ring
  simp only [halfPlaneQuadraticKernel, map_div₀, map_ofNat, Complex.conj_ofReal,
    map_pow, map_sub, Complex.conj_conj]
  rw [hpow]
  ring

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (p : ℍ → X)
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)

include R p hp in
/-- Every actual holomorphic weight-four automorphic coefficient is reproduced
on the same upper half-plane, without an extra weighted bound or integral premise. -/
theorem automorphicQuadratic_reproducing (φ : ℂ → ℂ)
    (hφ : DifferentiableOn ℂ φ upperHalf)
    (hφΓ : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      φ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) /
        ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z) :
    ∀ z ∈ upperHalf,
      IntegrableOn (fun ζ => (ζ.im : ℂ) ^ 2 * φ ζ / (conj ζ - z) ^ 4) upperHalf ∧
      φ z = (12 / Real.pi : ℂ) *
        ∫ ζ in upperHalf, (ζ.im : ℂ) ^ 2 * φ ζ / (conj ζ - z) ^ 4 := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨q, hq, hqφ⟩ := utm_x_descent hp hφ hφΓ
  let Q : HolomorphicQuadraticDifferential R.toRiemannAtlas := ⟨q, hq⟩
  have hQ (ζ : ℂ) (hζ : ζ ∈ upperHalf) : uniformizedQuadratic R p Q ζ = φ ζ :=
    hqφ ζ hζ
  intro z hz
  have hr := uniformizedQuadratic_reproducing R p hp Q z hz
  have hi : IntegrableOn
      (fun ζ => (ζ.im : ℂ) ^ 2 * φ ζ / (conj ζ - z) ^ 4) upperHalf :=
    hr.1.congr_fun (fun ζ hζ => by
      dsimp only
      rw [hQ ζ hζ]) isOpen_upperHalf.measurableSet
  refine ⟨hi, ?_⟩
  rw [hQ z hz] at hr
  exact hr.2.trans (congrArg (fun w : ℂ => (12 / Real.pi : ℂ) * w)
    (setIntegral_congr_fun isOpen_upperHalf.measurableSet fun ζ hζ => by
      rw [hQ ζ hζ]))

include R p hp in
/-- The exact kernel and inverse-density-square version on the original H.
Both its absolute convergence and all original coefficient values are retained. -/
theorem automorphicQuadratic_reproducing_kernel (φ : ℂ → ℂ)
    (hφ : DifferentiableOn ℂ φ upperHalf)
    (hφΓ : ∀ γ ∈ Γ, ∀ z ∈ upperHalf,
      φ ((γ 0 0 * z + γ 0 1) / (γ 1 0 * z + γ 1 1)) /
        ((γ 1 0 : ℂ) * z + γ 1 1) ^ 4 = φ z) :
    ∀ z ∈ upperHalf,
      IntegrableOn (fun ζ => (ζ.im : ℂ) ^ 2 * φ ζ *
        conj (halfPlaneQuadraticKernel z ζ)) upperHalf ∧
      φ z = ∫ ζ in upperHalf,
        (ζ.im : ℂ) ^ 2 * φ ζ * conj (halfPlaneQuadraticKernel z ζ) := by
  intro z hz
  obtain ⟨hi, he⟩ := automorphicQuadratic_reproducing R p hp φ hφ hφΓ z hz
  have hfun : (fun ζ => (ζ.im : ℂ) ^ 2 * φ ζ * conj (halfPlaneQuadraticKernel z ζ)) =
      fun ζ => (12 / Real.pi : ℂ) * ((ζ.im : ℂ) ^ 2 * φ ζ / (conj ζ - z) ^ 4) :=
    funext (kernel_integrand_eq φ z)
  rw [hfun]
  exact ⟨hi.const_mul _, by rw [integral_const_mul]; exact he⟩

end LowDimensionalTopology.Geometry.Teichmuller.QuadraticBergman
