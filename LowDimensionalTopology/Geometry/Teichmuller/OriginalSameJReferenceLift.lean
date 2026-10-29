module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalMirrorUpperUniformization

/-!
# Lift the same supplied inverse reference map through the two actual covers

The mirror covering is the original projection composed with the same chosen
minus-conjugation. Its lift of the supplied J inverse uses the actual target
cover's surjectivity and the existing covering lift theorem.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex
open scoped Manifold ContDiff ComplexConjugate UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open Surfaces LiZhongQC

/-- The same J inverse has an actual lift from the actual mirror cover to the original cover. -/
theorem originalMirror_referenceLift {X : Type} [TopologicalSpace X]
    (R : ClosedRiemannSurface X) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} (hΓ : IsFuchsian Γ)
    {p : UpperHalfPlane → X}
    (hp : letI := R.toRiemannAtlas.toChartedSpace; IsUniformization Γ p)
    (J : X ≃ₜ X) :
    letI := R.toRiemannAtlas.toChartedSpace
    let E := bsu24_mirror_group hΓ (s27g_actsFreely hp)
    let Eσ := Classical.choose_spec E
    let σ := Classical.choose Eσ
    ∃ wJ : UpperHalfPlane ≃ₜ UpperHalfPlane,
      IsLift (fun τ => p (σ τ)) p J.symm wJ := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let E := bsu24_mirror_group hΓ (s27g_actsFreely hp)
  let Γσ := Classical.choose E
  let Eσ := Classical.choose_spec E
  let σ := Classical.choose Eσ
  let hs := Classical.choose_spec Eσ
  let RStar := originalMirrorNative R.toSourceClosedRS
  let hpSigma := originalMirrorUpperCover_isUniformization
    R.toSourceClosedRS p hp σ hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2
  change ∃ wJ : UpperHalfPlane ≃ₜ UpperHalfPlane,
    IsLift (fun τ => p (σ τ)) p J.symm wJ
  obtain ⟨τ1, hτ1⟩ := hp.2.2.1 (J.symm (p (σ UpperHalfPlane.I)))
  obtain ⟨wJ, hwJ, -⟩ :=
    @exists_lift X inferInstance RStar.toRiemannAtlas.toChartedSpace
      X inferInstance R.toRiemannAtlas.toChartedSpace
      RStar.t2Space RStar.connectedSpace R.t2Space R.connectedSpace
      Γσ Γ (fun τ => p (σ τ)) p hpSigma hp J.symm UpperHalfPlane.I τ1 hτ1
  exact ⟨wJ, hwJ⟩

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
