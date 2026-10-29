module

public import LowDimensionalTopology.Geometry.Teichmuller.MarkedSpectrumReindexing
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge
public import LowDimensionalTopology.External.LiZhongQC.Ch06.S24_QuasiFuchsian
public import LowDimensionalTopology.Unproved.Teichmuller.QuasiconformalSmoothing
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The original homeomorphism action on the projective marked-spectrum closure

The ambient action is the actual reindexing of original classes.
Marked-image invariance is derived from the existing positive smooth
action. The existing quasiconformal representative theorem and the old
explicit quantitative smoothing premise supply the positive smooth
representative for a given orientation-preserving homeomorphism.
Continuity and the actual inverse then restrict to the literal closure.

No compactness, foliation classification, sphere, ball, or manifold assertion
is proved or assumed here. Those earlier reference-only conclusions remain
separate from this action on the same original spectrum closure.

The proved quasiconformal representative API is reused from Wu Xiaobin's
Li-Zhong-QC-formalization, fixed commit
`1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0); see the existing
`THIRD_PARTY_NOTICES.md`. Its proof is not copied or reconstructed here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
variable {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)

/-- Ordinary existence of a positive smooth representative of the given
original homeomorphism. This is not an additional Unproved obligation: the
next theorem derives it from the existing quantitative smoothing premise
for each genuinely orientation-preserving original homeomorphism. -/
def HasPositiveSmoothRepresentative (h : X ≃ₜ X) : Prop :=
  ∃ F : OrientedSurfaceAut R,
    ContinuousMap.Homotopic F.continuousMap (_root_.toContinuousMap h)

/-- Reuse the proved quasiconformal representative theorem and the old
quantitative quasiconformal-smoothing premise. No topological smoothing or
surface-classification theorem is reconstructed. The quasiconformal
representative theorem is from the credited Li-Zhong-QC implementation. -/
theorem hasPositiveSmoothRepresentative_of_orientationPreserving
    (hgenus : R.HasGenus g) (h : X ≃ₜ X)
    (hOri : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsOrientationPreservingRS h)
    (hsmooth : Unproved.Teichmuller.QuasiconformalSmoothing.{0}) :
    HasPositiveSmoothRepresentative R h := by
  let := R.t2Space
  let := R.compactSpace
  let := R.connectedSpace
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  obtain ⟨q, hQC, hq⟩ := LiZhongQC.exists_qc_in_homotopy_class
    (R.hasSourceGenus hgenus) (R.hasSourceGenus hgenus) h hOri
  obtain ⟨K, hK⟩ := hQC
  obtain ⟨F, hF, hFq, _hNorm⟩ := hsmooth R R q K hK.1 hK 1 zero_lt_one
  exact ⟨⟨F, hF⟩, hFq.trans hq.symm⟩

/-- The literal closure of all original projective marked-length spectra in
the existing projective nonnegative product. The original class witnesses
nonvanishing only; every spectrum still has all original class coordinates. -/
def markedLengthSpectrumProjectiveClosure (a₀ : EssentialSimpleFreeClass X) :
    Set (ProjectiveNonnegativeSpectrum X) :=
  closure (Set.range (projectiveMarkedLengthSpectrum R hg hgenus a₀))

/-- The given original topological homeomorphism preserves the full projective
marked-length image when its independent positive smooth representative is
provided. Image invariance is a conclusion, not the supplied premise. -/
theorem projectiveSpectrumHomeomorph_image_markedLengthSpectrum_of_smoothRepresentative
    (a₀ : EssentialSimpleFreeClass X) (h : X ≃ₜ X)
    (hSmooth : HasPositiveSmoothRepresentative R h) :
    projectiveSpectrumHomeomorph h ''
        Set.range (projectiveMarkedLengthSpectrum R hg hgenus a₀) =
      Set.range (projectiveMarkedLengthSpectrum R hg hgenus a₀) := by
  obtain ⟨F, hF⟩ := hSmooth
  have hclasses : essentialSimpleFreeClassEquiv F.toHomeomorph =
      essentialSimpleFreeClassEquiv h :=
    essentialSimpleFreeClassEquiv_eq_of_homotopic F.toHomeomorph h hF
  have haction : projectiveSpectrumHomeomorph F.toHomeomorph =
      projectiveSpectrumHomeomorph h := by
    unfold projectiveSpectrumHomeomorph
    rw [hclasses]
  rw [← haction]
  exact projectiveSpectrumHomeomorph_image_markedLengthSpectrum R hg hgenus a₀ F

/-- Ambient reindexing preserves the literal closure of the full original
marked-spectrum image. No identification of the boundary is needed. -/
theorem projectiveSpectrumHomeomorph_image_markedLengthSpectrumProjectiveClosure
    (a₀ : EssentialSimpleFreeClass X) (h : X ≃ₜ X)
    (hSmooth : HasPositiveSmoothRepresentative R h) :
    projectiveSpectrumHomeomorph h '' markedLengthSpectrumProjectiveClosure R hg hgenus a₀ =
      markedLengthSpectrumProjectiveClosure R hg hgenus a₀ := by
  unfold markedLengthSpectrumProjectiveClosure
  rw [(projectiveSpectrumHomeomorph h).image_closure,
    projectiveSpectrumHomeomorph_image_markedLengthSpectrum_of_smoothRepresentative
      R hg hgenus a₀ h hSmooth]

/-- The full original projective marked-spectrum closure has the exact
homeomorphism induced by the given original topological self-homeomorphism,
conditional only on its separate positive smooth representative. -/
def markedLengthSpectrumProjectiveClosureHomeomorph
    (a₀ : EssentialSimpleFreeClass X) (h : X ≃ₜ X)
    (hSmooth : HasPositiveSmoothRepresentative R h) :
    markedLengthSpectrumProjectiveClosure R hg hgenus a₀ ≃ₜ
      markedLengthSpectrumProjectiveClosure R hg hgenus a₀ :=
  ((projectiveSpectrumHomeomorph h).image
      (markedLengthSpectrumProjectiveClosure R hg hgenus a₀)).trans
    (Homeomorph.setCongr
      (projectiveSpectrumHomeomorph_image_markedLengthSpectrumProjectiveClosure
        R hg hgenus a₀ h hSmooth))

/-- Restriction retains the original ambient action on each actual ray. -/
theorem markedLengthSpectrumProjectiveClosureHomeomorph_apply
    (a₀ : EssentialSimpleFreeClass X) (h : X ≃ₜ X)
    (hSmooth : HasPositiveSmoothRepresentative R h)
    (p : markedLengthSpectrumProjectiveClosure R hg hgenus a₀) :
    (markedLengthSpectrumProjectiveClosureHomeomorph R hg hgenus a₀ h hSmooth p :
      ProjectiveNonnegativeSpectrum X) = projectiveSpectrumHomeomorph h p.val := rfl

end LowDimensionalTopology.Geometry.Teichmuller
