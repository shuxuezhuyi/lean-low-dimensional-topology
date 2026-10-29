module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeQuadraticSegments
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticGlobalMinimizer
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticUpperHalfDistance
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticL1Norm

/-!
# Deferred quadratic-flat statements

The original differential and its actual lifted coefficient are retained.
Local geodesics and global smooth minimizers are separate predicates. A
projected segment is represented by its actual lift, so projected point
distances are never substituted for fixed-lift distances.

The segment-shortening proof is unfinished, and the mean-stretch foliation
argument needs the graphical/branched-cover prerequisites.
These definitions state obligations; they assert no proofs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Teichmuller LiZhongQC

universe u

/-- One constant bounds shortening of every actual projected quadratic
segment. The source segment is retained in the universal cover;
its projection may meet itself. Both lengths are measured up to genuine
monotone reparametrization, admitting infinite image length. -/
def QuadraticSegmentBoundedShortening : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (R : ClosedRiemannSurface X) (g : ℕ),
    2 ≤ g → R.HasGenus g →
    ∀ q : HolomorphicQuadraticDifferential R.toRiemannAtlas, q ≠ 0 →
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ h : X ≃ₜ X, IsQCRS h →
      ContinuousMap.Homotopic (h : C(X, X)) (ContinuousMap.id X) →
      ∃ M : ℝ, 0 < M ∧
        ∀ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ))
          (p : UpperHalfPlane → X) (hp : IsUniformization Γ p),
          let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
            (utm_liftQD_differentiableOn q.property hp)
          ∀ (a b : X) (z₁ z₂ : UpperHalfPlane) (α : Path a b) (L : Path z₁ z₂),
            (∀ t, p (L t) = α t) →
            IsQuadraticSegment upperHalfNativeSurface qH (L : C(unitInterval, UpperHalfPlane)) →
            phiLengthPathInv (q : X → ℂ → ℂ) α ≤
              phiLengthPathInv (q : X → ℂ → ℂ) (α.map h.continuous) + ENNReal.ofReal M

/-- The actual area integral of horizontal stretch is at least the actual
quadratic area. `coefficientIntegral` is the single area integral, while
the separate book norm remains twice this integral. No global choice of
horizontal orientation is assumed. -/
def QuadraticMeanHorizontalStretch : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] (R : ClosedRiemannSurface X) (g : ℕ),
    2 ≤ g → R.HasGenus g →
    ∀ q : HolomorphicQuadraticDifferential R.toRiemannAtlas, q ≠ 0 →
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ h : X ≃ₜ X, IsQCRS h →
      ContinuousMap.Homotopic (h : C(X, X)) (ContinuousMap.id X) →
      QuadraticL1.coefficientIntegral R q ≤
        surfaceIntegral (q : X → ℂ → ℂ) fun x z =>
          ENNReal.ofReal (lambdaStretch (q : X → ℂ → ℂ) (q : X → ℂ → ℂ) h x z)

end LowDimensionalTopology.Unproved.Teichmuller
