module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedSpectrumClosureAction

/-!
# The same closure action on the literal native Fricke image

This interface retains the entire literal native Fricke image and its
actual complete marked-length spectra. Its spectrum image is exactly the
image of the original native marked quotient, by the existing native Fricke
homeomorphism; taking the closure therefore does not change any ray.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Surfaces.HandlePresentation

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)
variable {e : X ≃ₜ PolygonQuotient g}
variable (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable R
  (Nat.lt_of_succ_le hg) e)
variable (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} R,
  Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m))

/-- The full original marked-length ray at the original literal Fricke point,
in the nonnegative projective space with the zero spectrum deleted. -/
def frickeProjectiveMarkedLengthSpectrum (a₀ : EssentialSimpleFreeClass X)
    (t : nativeFrickeImage hA) : ProjectiveNonnegativeSpectrum X :=
  letI := nativeFrickeTopology hA
  projectiveMarkedLengthSpectrum R hg hgenus a₀ ((nativeFrickeHomeomorph hA hAlt).symm t)

/-- The full original Fricke image and full original marked quotient have
exactly the same projective marked-length rays. -/
theorem range_frickeProjectiveMarkedLengthSpectrum (a₀ : EssentialSimpleFreeClass X) :
    Set.range (frickeProjectiveMarkedLengthSpectrum R hg hgenus hA hAlt a₀) =
      Set.range (projectiveMarkedLengthSpectrum R hg hgenus a₀) := by
  let := nativeFrickeTopology hA
  apply Set.Subset.antisymm
  · rintro p ⟨t, rfl⟩
    exact ⟨(nativeFrickeHomeomorph hA hAlt).symm t, rfl⟩
  · rintro p ⟨t, rfl⟩
    refine ⟨nativeFrickeHomeomorph hA hAlt t, ?_⟩
    simp only [frickeProjectiveMarkedLengthSpectrum, Homeomorph.symm_apply_apply]

/-- The closure of the entire original Fricke marked-length image in the
literal projective nonnegative spectrum space. -/
def frickeMarkedLengthSpectrumProjectiveClosure (a₀ : EssentialSimpleFreeClass X) :
    Set (ProjectiveNonnegativeSpectrum X) :=
  closure (Set.range (frickeProjectiveMarkedLengthSpectrum R hg hgenus hA hAlt a₀))

/-- The two descriptions use exactly the same subset of the same projective
spectrum space; no model replacement or new compactification is introduced. -/
theorem frickeMarkedLengthSpectrumProjectiveClosure_eq (a₀ : EssentialSimpleFreeClass X) :
    frickeMarkedLengthSpectrumProjectiveClosure R hg hgenus hA hAlt a₀ =
      markedLengthSpectrumProjectiveClosure R hg hgenus a₀ := by
  unfold frickeMarkedLengthSpectrumProjectiveClosure markedLengthSpectrumProjectiveClosure
  rw [range_frickeProjectiveMarkedLengthSpectrum R hg hgenus hA hAlt a₀]

/-- The same original topological homeomorphism acts on the closure of the
complete marked-length image of the entire literal native Fricke space.
The source's topological orientation condition, old native-model/axis
premises and old quantitative smoothing premise are all explicit. -/
def frickeMarkedLengthSpectrumProjectiveClosureHomeomorph
    (a₀ : EssentialSimpleFreeClass X) (h : X ≃ₜ X)
    (hOri : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsOrientationPreservingRS h)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0}) :
    frickeMarkedLengthSpectrumProjectiveClosure R hg hgenus hA hAlt a₀ ≃ₜ
      frickeMarkedLengthSpectrumProjectiveClosure R hg hgenus hA hAlt a₀ :=
  (Homeomorph.setCongr
      (frickeMarkedLengthSpectrumProjectiveClosure_eq R hg hgenus hA hAlt a₀)).trans
    ((markedLengthSpectrumProjectiveClosureHomeomorph R hg hgenus a₀ h
      (hasPositiveSmoothRepresentative_of_orientationPreserving R hgenus h hOri hsmooth)).trans
      (Homeomorph.setCongr
        (frickeMarkedLengthSpectrumProjectiveClosure_eq R hg hgenus hA hAlt a₀).symm))

/-- The native Fricke closure action is still the literal ambient reindexing
of all original essential simple free classes. -/
theorem frickeMarkedLengthSpectrumProjectiveClosureHomeomorph_apply
    (a₀ : EssentialSimpleFreeClass X) (h : X ≃ₜ X)
    (hOri : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsOrientationPreservingRS h)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0})
    (p : frickeMarkedLengthSpectrumProjectiveClosure R hg hgenus hA hAlt a₀) :
    (frickeMarkedLengthSpectrumProjectiveClosureHomeomorph
      R hg hgenus hA hAlt a₀ h hOri hsmooth p : ProjectiveNonnegativeSpectrum X) =
      projectiveSpectrumHomeomorph h p.val := rfl

end LowDimensionalTopology.Geometry.Teichmuller
