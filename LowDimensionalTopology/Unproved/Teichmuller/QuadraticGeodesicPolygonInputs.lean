module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticUpperHalfDistance

/-!
# Deferred finite geometry of actual local quadratic geodesics

The two inputs are separate: extraction of a genuine finite simple polygon
from a repeated nonconstant local-geodesic trace, and the local corner-angle
bound. The original path and its actual adjacent side traces remain explicit.
Neither input states a loop exclusion or an angle-sum identity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Real ENNReal NNReal

namespace LowDimensionalTopology.Unproved.Teichmuller
open Geometry.Surfaces Geometry.Teichmuller LiZhongQC

/-- The two actual one-sided traces of the original path follow the adjacent
sides of the supplied polygon, with either traversal orientation. -/
def FollowsActualPolygonCorner {a b : UpperHalfPlane} (δ : Path a b)
    (l v : ℝ) (c : ℂ) (r : ℝ) {φ : ℂ → ℂ} {n : ℕ} [NeZero n]
    (P : PhiPolygon φ n) (j : Fin n) : Prop :=
  let f : ℝ → ℂ := fun u => (δ.extend u : ℂ)
  let A : ℂ → ℂ := fun w => c + (r : ℂ) * w
  ∃ s u t ε η : ℝ,
    0 ≤ s ∧ l ≤ s ∧ s < u ∧ u < t ∧ t ≤ v ∧ t ≤ 1 ∧
    0 < ε ∧ ε < 1 ∧ 0 < η ∧ η < 1 ∧ f u = A (P.vert j) ∧
    ((f '' Icc s u = A '' (P.side (j - 1) '' Icc (1 - ε) 1) ∧
      f '' Icc u t = A '' (P.side j '' Icc 0 η)) ∨
     (f '' Icc s u = A '' (P.side j '' Icc 0 η) ∧
      f '' Icc u t = A '' (P.side (j - 1) '' Icc (1 - ε) 1)))

/-- A repeated nonconstant actual local-geodesic trace supplies a genuine
finite simple polygon. At most two joining vertices lack an actual corner
trace from the original geodesic. All polygon regularity remains explicit. -/
def QuadraticGeodesicFinitePolygonExtraction
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (_hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  letI := R.toRiemannAtlas.isManifold
  ∀ hp : IsUniformization Γ p,
    let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
    let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
    letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
    ∀ {a b : UpperHalfPlane} (δ : Path a b),
      IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) δ →
      ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ 1 → δ.extend s = δ.extend t →
      (∃ u ∈ Icc s t, δ.extend u ≠ δ.extend s) →
      ∃ (c : ℂ) (r : ℝ), 0 < r ∧
        MapsTo (fun w : ℂ => c + (r : ℂ) * w) unitDisc upperHalf ∧
        ∃ (n : ℕ) (hn : NeZero n),
          letI := hn
          ∃ (P : PhiPolygon (fun w => (r : ℂ) ^ 2 * ψ (c + (r : ℂ) * w)) n)
            (E : Finset (Fin n)),
            (fun w : ℂ => c + (r : ℂ) * w) '' frontier P.dom ⊆
              (fun u : ℝ => (δ.extend u : ℂ)) '' Icc s t ∧
            E.card ≤ 2 ∧
            ∀ j ∉ E, FollowsActualPolygonCorner δ s t c r P j

/-- At a polygon corner genuinely followed by the original local geodesic,
the actual interior angle has the zero-order lower bound. The coefficient is
the explicit affine pullback of the same original lifted differential. -/
def QuadraticGeodesicLocalAngleBound
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (_hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  letI := R.toRiemannAtlas.isManifold
  ∀ hp : IsUniformization Γ p,
    let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
    let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
    letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
    ∀ {a b : UpperHalfPlane} (δ : Path a b),
      IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) δ →
      ∀ (c : ℂ) (r : ℝ), 0 < r →
        MapsTo (fun w : ℂ => c + (r : ℂ) * w) unitDisc upperHalf →
        ∀ (n : ℕ) [NeZero n]
          (P : PhiPolygon (fun w => (r : ℂ) ^ 2 * ψ (c + (r : ℂ) * w)) n)
          (j : Fin n) (l v : ℝ),
          FollowsActualPolygonCorner δ l v c r P j →
          ∀ m : ℕ,
            meromorphicOrderAt (fun w => (r : ℂ) ^ 2 * ψ (c + (r : ℂ) * w))
              (P.vert j) = (m : ℤ) →
            2 * π / ((m : ℝ) + 2) ≤ P.angle j

end LowDimensionalTopology.Unproved.Teichmuller
