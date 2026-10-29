module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Closed
public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.LinearAlgebra.Complex.Determinant

/-!
# Smooth oriented markings of closed Riemann surfaces

The smooth maps below use the real smooth structures induced by the actual
complex atlases. Positivity of the real Jacobian in complex coordinates records
preservation of the complex orientations.
-/

@[expose] public section

noncomputable section

open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

universe u v

/-- A real smooth diffeomorphism for the smooth structures of two complex atlases. -/
abbrev SmoothSurfaceEquiv {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (A : RiemannSurface X) (B : RiemannSurface Y) :=
  letI := A.toRiemannAtlas.toChartedSpace
  letI := B.toRiemannAtlas.toChartedSpace
  X ≃ₘ⟮𝓘(ℝ, ℂ), 𝓘(ℝ, ℂ)⟯ Y

namespace SmoothSurfaceEquiv

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
variable {A : RiemannSurface X} {B : RiemannSurface Y}

/-- Forget differentiability while keeping the original topologies. -/
def toHomeomorph (f : SmoothSurfaceEquiv A B) : X ≃ₜ Y := by
  letI := A.toRiemannAtlas.toChartedSpace
  letI := B.toRiemannAtlas.toChartedSpace
  exact Diffeomorph.toHomeomorph f

/-- The identity is a real smooth diffeomorphism of a surface. -/
def refl (A : RiemannSurface X) : SmoothSurfaceEquiv A A := by
  letI := A.toRiemannAtlas.toChartedSpace
  exact Diffeomorph.refl 𝓘(ℝ, ℂ) X ∞

@[simp]
theorem refl_toHomeomorph (A : RiemannSurface X) :
    (refl A).toHomeomorph = Homeomorph.refl X := rfl

end SmoothSurfaceEquiv

/-- The determinant of the real derivative of a complex-coordinate map. -/
def realJacobian (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  (fderiv ℝ f z).toLinearMap.det

/-- A holomorphic coordinate map has the familiar squared-norm real Jacobian. -/
theorem realJacobian_eq_norm_deriv_sq {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : realJacobian f z = ‖deriv f z‖ ^ 2 := by
  have hreal : HasFDerivAt f
      ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).restrictScalars ℝ) z :=
    hf.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  unfold realJacobian
  rw [hreal.fderiv]
  change ((ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)).restrictScalars ℝ).det = _
  simp only [ContinuousLinearMap.det, ContinuousLinearMap.coe_restrictScalars,
    LinearMap.det_restrictScalars, ContinuousLinearMap.det_toSpanSingleton,
    Algebra.norm_complex_eq]
  exact Complex.normSq_eq_norm_sq _

/-- Orientation preservation, tested on every actual complex chart expression. -/
def PreservesComplexOrientation {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A : RiemannAtlas X) (B : RiemannAtlas Y) (f : X → Y) : Prop :=
  ∀ e ∈ A.charts, ∀ g ∈ B.charts, ∀ z ∈ riemannChartMapDomain e f g,
    0 < realJacobian (riemannChartMap e f g) z

/-- Analytic coordinate changes give the complex surface its consistent orientation. -/
theorem preservesComplexOrientation_id {X : Type u} [TopologicalSpace X]
    (A : RiemannAtlas X) : PreservesComplexOrientation A A (id : X → X) := by
  intro e he g hg z hz
  change 0 < realJacobian (e.symm.trans g) z
  have hz' : z ∈ (e.symm.trans g).source := hz
  rw [realJacobian_eq_norm_deriv_sq (A.compatible e he g hg z hz').differentiableAt]
  exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (A.transition_deriv_ne_zero e g he hg z hz'))

/-- A closed Riemann surface together with an orientation-preserving smooth marking
from a fixed closed reference surface. The target carrier is not fixed in advance. -/
structure MarkedRiemannSurface {X : Type u} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) where
  carrier : Type v
  topology : TopologicalSpace carrier
  surface : @ClosedRiemannSurface carrier topology
  marking :
    letI := topology
    SmoothSurfaceEquiv R.toRiemannSurface surface.toRiemannSurface
  orientation_preserving :
    letI := topology
    PreservesComplexOrientation R.toRiemannAtlas surface.toRiemannAtlas marking.toHomeomorph

attribute [instance] MarkedRiemannSurface.topology

namespace MarkedRiemannSurface

variable {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}

/-- The marking as a continuous map between the original topological surfaces. -/
def markingMap (M : MarkedRiemannSurface.{u, v} R) : C(X, M.carrier) :=
  ⟨M.marking.toHomeomorph, M.marking.toHomeomorph.continuous⟩

/-- A reference surface carries its identity marking. -/
def refl (R : ClosedRiemannSurface X) : MarkedRiemannSurface.{u, u} R where
  carrier := X
  topology := inferInstance
  surface := R
  marking := SmoothSurfaceEquiv.refl R.toRiemannSurface
  orientation_preserving := preservesComplexOrientation_id R.toRiemannAtlas

end MarkedRiemannSurface

end LowDimensionalTopology.Geometry.Teichmuller
