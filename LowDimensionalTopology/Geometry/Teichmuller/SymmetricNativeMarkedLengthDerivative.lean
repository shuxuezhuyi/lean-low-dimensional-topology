module

public import LowDimensionalTopology.Geometry.Teichmuller.SymmetricNativeLogVariation
public import LowDimensionalTopology.Geometry.Teichmuller.SymmetricNativeMarkedLengthValue

/-!
# The actual marked-length derivative in the same mirrored direction

The genuine logarithmic derivative is transported along the equality of the
same native marked-length curve and the same symmetric logarithmic curve.
The original covering element and its full period are retained.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
variable (hPresentation : Unproved.HandleGroupPresentation g)
variable {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
variable (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
variable {p : ℍ → X}
variable (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
variable (α : LiZhongQC.Loop X)
variable (A0 : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA0 : A0 ∈ Γ)
variable (hcov : LiZhongQC.Covers p A0 α) (s : ℝ) (hs : 0 < s)
variable (hproj : Hyperbolic.realSLMobius A0 =
  Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s))

include hA0 hcov hs hproj in
/-- The same genuine mirrored direction differentiates the actual native
marked-length scalar curve, retaining the original covering period. -/
theorem exists_marked_length_derivative_same_symmetric_direction
    (μ : GammaMeasurableBeltrami.Space Γ) :
    ∃ η : MeasurableBeltramiSpace,
      (η : ℂ → ℂ) =ᵐ[volume]
        LiZhongQC.s27u_symExt (GammaMeasurableBeltrami.planeRepresentative μ.val) ∧
      ‖η‖ ≤ ‖μ‖ ∧
      HasDerivAt
        (fun t : ℝ => markedGeodesicLength R (Nat.succ_le_of_lt hg) hgenus α
          (TeichmullerSpace.coefficientProjection R hg hgenus hPresentation hΓ hfree hp
            ((t : ℂ) • μ)))
        ((Quasiconformal.firstVariation η (Real.exp (2 * s) : ℂ)).re /
          Real.exp (2 * s)) 0 := by
  obtain ⟨η, hη, hbound, _, _, hlog⟩ := exists_symmetric_native_real_log_derivative μ s hs
  have hvalue := marked_length_coefficient_curve_eventually_eq_symmetric_log
    (R := R) (hg := hg) (hgenus := hgenus) (hPresentation := hPresentation)
    (hΓ := hΓ) (hfree := hfree) (hp := hp) (α := α)
    (A0 := A0) (hA0 := hA0) (hcov := hcov) (s := s) (hs := hs) (hproj := hproj) μ
  exact ⟨η, hη, hbound, hlog.congr_of_eventuallyEq hvalue⟩

end LowDimensionalTopology.Geometry.Teichmuller
