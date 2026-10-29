module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCanonicalCoefficientCurve
public import LowDimensionalTopology.Unproved.Teichmuller.OriginalFNTwistPhaseAnalytic
public import LowDimensionalTopology.External.LiZhongQC.Ch08.S30_ModularGroupDiscontinuity

/-!
# The actual left intrinsic copy in book-oriented original FN coordinates

The geometric input records which of the two prescribed original seam germs
lies to the left of the positively oriented cuff axis, and preserves that
label through the actual marked pants correspondence. The cuff, its full
period, each normalization, and the original seam parameter are retained.
No angle branch, real FN equation, tangent, metric or WP assertion is included.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set
open scoped unitInterval UpperHalfPlane Topology

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

/-- The literal inward original seam germ is on the left precisely for the
specified intrinsic copy. Normalization is by the SAME oriented full cuff. -/
def OriginalFNCopyLeftGerm
    {Y : Type} [TopologicalSpace Y] {S : ClosedRiemannSurface Y}
    {N : HyperbolicSurfaceModel S.toRiemannSurface} {g : ℕ}
    {inc : OriginalFNCuffIncidence g} (D : OriginalFNRealization N inc)
    (j : Fin (3 * g - 3)) (left : Fin 2) : Prop :=
  let := S.toRiemannAtlas.toChartedSpace
  ∀ (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)),
    LiZhongQC.IsUniformization Γ N.halfPlaneCover →
    ∀ (A Q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (s : ℝ),
      0 < s → A ∈ Γ →
      LiZhongQC.Covers N.halfPlaneCover A (D.cuff j).toLoop →
      Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
        Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s) →
      ∀ (c : Fin 2) (v : C(I, ℍ)),
        (∀ u : I, LiZhongQC.adjustProjection N.halfPlaneCover Q (v u) =
          (D.pants (inc.copy (j, c)).1).projection ((D.seam (j, c)).curve u)) →
        (v 0 : ℂ).re = 0 →
        ((∃ ε : ℝ, 0 < ε ∧
          ∀ u : I, 0 < (u : ℝ) → (u : ℝ) < ε → (v u : ℂ).re < 0) ↔ c = left)

end LowDimensionalTopology.Geometry.Teichmuller

namespace LowDimensionalTopology.Unproved.Teichmuller

open Geometry.Surfaces Geometry.Surfaces.HandlePresentation Geometry.Teichmuller

/-- The source's fixed left/right cuff-copy convention, coherent under the
actual marked transport. Only the actual negative-real inward seam germ is
asserted. This is the explicit figure/gluing prerequisite for book FN order. -/
def OriginalFNBookLeftCopyTransport
    {X : Type} [TopologicalSpace X] {R : ClosedRiemannSurface X} {g : ℕ}
    {M : HyperbolicSurfaceModel R.toRiemannSurface}
    {inc : OriginalFNCuffIncidence g} (D₀ : OriginalFNRealization M inc) : Prop :=
  ∃ left : Fin (3 * g - 3) → Fin 2,
    (∀ j, OriginalFNCopyLeftGerm D₀ j (left j)) ∧
    ∀ (m : MarkedRiemannSurface.{0, 0} R)
      (N : HyperbolicSurfaceModel m.surface.toRiemannSurface)
      (D : OriginalFNRealization N inc),
      OriginalFNMarkedTransport D₀ m D →
      ∀ j, OriginalFNCopyLeftGerm D j (left j)

end LowDimensionalTopology.Unproved.Teichmuller
