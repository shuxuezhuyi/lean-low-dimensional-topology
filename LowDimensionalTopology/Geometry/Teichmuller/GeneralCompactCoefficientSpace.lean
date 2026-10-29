/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

Uses Wu Xiaobin's credited LiZhongQC APIs, Apache-2.0, pinned upstream
1c0d5473c020b66ed5106331a38a61536760b9b2; see THIRD_PARTY_NOTICES.md.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralReducedCoefficientSpace
public import LowDimensionalTopology.Geometry.Teichmuller.CompactReducedBoundary

/-!
# The original compact-reference coefficient model with independent targets

The natural forward map keeps the actual original marking's literal lifted
coefficient. The reduced/full-boundary identification uses only the original
reference's compactness. Every target universe is retained through the proved
actual retargeting construction; no universe inequality is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Manifold ContDiff UpperHalfPlane OnePoint

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open Surfaces LiZhongQC
universe u v
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (hfixed : ∀ ξ ∈ ({((0 : ℂ) : ExtPlane), ((1 : ℂ) : ExtPlane), extInf} : Set ExtPlane),
      ∃ γ ∈ Γ, Hyperbolic.realSLMobius γ ≠ 1 ∧ mobiusSL (slRealToComplex γ) ξ = ξ)

/-- The original independently sized marked quotient identifies naturally with
T(Γ), through the same-coefficient reduced and full-boundary quotient maps. -/
def closedGammaEquivGeneral :
    Space.{u, v} (Surface.ofRiemannSurface R.toRiemannSurface) ≃ TeichGamma Γ :=
  ((reducedCoefficientEquivGeneral (Surface.ofRiemannSurface R.toRiemannSurface) hp hfixed).trans
    (ReducedCoefficient.boundaryEquiv R hp)).trans (ReducedCoefficient.boundarySourceEquiv Γ)

/-- The explicit forward law uses the original actual marking's coefficient. -/
theorem closedGammaEquivGeneral_mk
    (m : Marked.{u, v} (Surface.ofRiemannSurface R.toRiemannSurface)) :
    closedGammaEquivGeneral R hp hfixed (mk m) =
      (Quotient.mk _ (ReducedCoefficient.toSourceCoefficient
        (markedCoefficientGeneral (Surface.ofRiemannSurface R.toRiemannSurface) hp m)) :
          TeichGamma Γ) := rfl

/-- This actual source class has a representative whose raw function is
literally the lifted coefficient of the unchanged original marking, even when
its actual target is in a universe independent of the reference's universe. -/
theorem closedGammaEquivGeneral_original_coefficient
    (m : Marked.{u, v} (Surface.ofRiemannSurface R.toRiemannSurface)) :
    let := R.toRiemannAtlas.toChartedSpace
    ∃ ρ : BeltramiGamma Γ,
      ρ.val.val = s27u_liftCoeff p m.marking ∧
      closedGammaEquivGeneral R hp hfixed (mk m) = Quotient.mk _ ρ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨B, hB, hΓ⟩ := s27u_liftCoeff_beltramiH hp m.sourceCarrierRepresentative.qc
  let ρ : BeltramiGamma Γ := ⟨B, hΓ⟩
  have hraw : ρ.val.val = s27u_liftCoeff p m.marking :=
    hB.trans (sourceCarrierRepresentative_liftCoeff
      (Surface.ofRiemannSurface R.toRiemannSurface) hp m)
  refine ⟨ρ, hraw, ?_⟩
  rw [closedGammaEquivGeneral_mk]
  apply ReducedCoefficient.toSourceCoefficient_class_eq_of_ae
  exact Eventually.of_forall fun z => congrFun hraw.symm z

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
