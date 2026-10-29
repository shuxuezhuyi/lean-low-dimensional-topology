module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalCanonicalFrickeCoordinates
public import LowDimensionalTopology.Geometry.Teichmuller.NativeFrickeOpenEmbedding

/-!
# Direct original QC and canonical-coordinate topology comparisons

The original QC identity is checked on the same actual native targets and
markings before using the existing source equivalences to exhaust the QC
classes. The canonical quotient carries the topology induced by its actual
Fricke map, and the native comparison is a homeomorphism for that topology.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Topology

variable {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g)
  (D : OriginalOrientedCanonicalCut B.surface g
    (lt_trans Nat.zero_lt_one hg) B.point)
  (hD : D.family = B.classes)
  (hGeom : Unproved.Teichmuller.OriginalCanonicalCutQCPositiveTransport
    B.surface hg B.point D)
  (hRealize : Unproved.Teichmuller.OriginalGeneratorPrescribedPositiveSmoothRealization hg B)
  (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable B.surface hg D.polygon)

/-- The literal original QC coordinate value agrees with the existing native
value through the actual source equivalences, without an axis hypothesis. -/
theorem originalQCFrickeCoordinates_eq_native (z : GeneralQC.ClosedSpace B.surface) :
    originalCanonicalFrickeCoordinates hg B D hD hGeom hRealize hA
        (originalQCGeneratorComparison hg B D hD hGeom z) =
      finiteFrickeCoordinates hA
        ((TeichmullerSpace.qcEquiv B.surface hg B.genus).symm
          (GeneralQC.closedSourceEquiv B.surface z)) := by
  let E := GeneralQC.closedSourceEquiv B.surface
  let Q := TeichmullerSpace.qcEquiv B.surface hg B.genus
  have hrep : ∀ t : TeichmullerSpace.{0, 0} B.surface, Q t = E z →
      originalCanonicalFrickeCoordinates hg B D hD hGeom hRealize hA
        (originalQCGeneratorComparison hg B D hD hGeom z) = finiteFrickeCoordinates hA t := by
    intro t
    induction t using Quotient.inductionOn with
    | _ m =>
      intro ht
      let zₘ : GeneralQC.ClosedMarked B.surface :=
        { target := GeneralQC.Surface.ofRiemannSurface m.surface.toRiemannSurface
          marking := m.marking.toHomeomorph
          qc := by
            let := B.surface.compactSpace
            exact m.marking.isQCRS_of_compact m.orientation_preserving }
      have hsource : E (GeneralQC.mk zₘ) = Q (TeichmullerSpace.mk m) := by
        rfl
      have hz : z = GeneralQC.mk zₘ := E.injective (ht.symm.trans hsource.symm)
      have hPhi : originalQCGeneratorComparison hg B D hD hGeom (GeneralQC.mk zₘ) =
          originalGeneratorComparison hg B
            (originalCanonicalFamilyMarkingTransport_of_qcCutPositiveTransport hg B D hD hGeom)
            (TeichmullerSpace.mk m) := by
        rfl
      rw [hz, hPhi]
      exact originalCanonicalFrickeCoordinates_comparison hg B D hD hGeom hRealize hA _
  exact hrep (Q.symm (E z)) (Q.apply_symm_apply _)

/-- For the original coordinate-induced topology, the same native comparison
is a homeomorphism under the existing pointwise canonical-axis obligations. -/
theorem originalGeneratorComparison_fricke_isHomeomorph
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} B.surface,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m)) :
    let mT : MetricSpace (TeichmullerSpace.{0, 0} B.surface) :=
      TeichmullerSpace.qcMetricSpace B.surface hg B.genus
    letI : TopologicalSpace (TeichmullerSpace.{0, 0} B.surface) :=
      mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI : TopologicalSpace (OriginalGeneratorTeichmullerSpace g) :=
      TopologicalSpace.induced
        (originalCanonicalFrickeCoordinates hg B D hD hGeom hRealize hA) inferInstance
    IsHomeomorph
      (originalGeneratorComparison hg B
        (originalCanonicalFamilyMarkingTransport_of_qcCutPositiveTransport hg B D hD hGeom)) := by
  let mT : MetricSpace (TeichmullerSpace.{0, 0} B.surface) :=
    TeichmullerSpace.qcMetricSpace B.surface hg B.genus
  let : TopologicalSpace (TeichmullerSpace.{0, 0} B.surface) :=
    mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let F := originalCanonicalFrickeCoordinates hg B D hD hGeom hRealize hA
  let : TopologicalSpace (OriginalGeneratorTeichmullerSpace g) :=
    TopologicalSpace.induced F inferInstance
  let hTransport := originalCanonicalFamilyMarkingTransport_of_qcCutPositiveTransport
    hg B D hD hGeom
  let C := originalGeneratorComparison hg B hTransport
  have hF : Function.Injective F := by
    intro p q hpq
    apply (originalCanonicalFrickeMap_bijective hg B D hD hGeom hRealize hA hAlt).1
    exact Subtype.ext hpq
  have hFe : IsEmbedding F := IsEmbedding.induced hF
  have hcomm : F ∘ C = finiteFrickeCoordinates hA := by
    funext t
    exact originalCanonicalFrickeCoordinates_comparison hg B D hD hGeom hRealize hA t
  have hCF : IsEmbedding (F ∘ C) := by
    rw [hcomm]
    exact (finiteFrickeCoordinates_qc_isOpenEmbedding B.surface hg B.genus hA hAlt).isEmbedding
  have hCe : IsEmbedding C := hFe.of_comp_iff.mp hCF
  have hCs : Function.Surjective C :=
    (originalGeneratorComparison_bijective hg B hTransport hRealize).2
  exact isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hCe, hCs⟩

end LowDimensionalTopology.Geometry.Teichmuller
