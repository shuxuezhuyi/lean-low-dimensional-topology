module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalCanonicalFrickeTopologyJoin
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCDistanceTopology
public import LowDimensionalTopology.Geometry.Teichmuller.NativeFrickeDomain
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The six original marked models

The raw quotient keeps its actual full-log distance topology. The native
comparison and the original Fricke map keep their actual underlying functions;
the original geometric quotient has the topology induced by that genuine map.
The book's Tg is the same fixed-reference T(R), up to its existing reference
changes. No additional moduli carrier or transported-Phi topology is introduced.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces Topology

/-- The actual maps connect the original QC, native smooth, original geometric,
intrinsic Fricke and real coordinate spaces. The book's Tg names the first
space up to the existing reference comparison. -/
theorem original_marked_six_models_homeomorphic
    {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g)
    (D : OriginalOrientedCanonicalCut B.surface g
      (lt_trans Nat.zero_lt_one hg) B.point)
    (hD : D.family = B.classes)
    (hGeom : Unproved.Teichmuller.OriginalCanonicalCutQCPositiveTransport
      B.surface hg B.point D)
    (hRealize : Unproved.Teichmuller.OriginalGeneratorPrescribedPositiveSmoothRealization hg B)
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable B.surface hg D.polygon)
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} B.surface,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m)) :
    let mQ : PseudoMetricSpace (GeneralQC.ClosedSpace B.surface) :=
      GeneralQC.pseudoMetricSpace
        (GeneralQC.Surface.ofRiemannSurface B.surface.toRiemannSurface)
    letI : TopologicalSpace (GeneralQC.ClosedSpace B.surface) :=
      mQ.toUniformSpace.toTopologicalSpace
    let mT : MetricSpace (TeichmullerSpace.{0, 0} B.surface) :=
      TeichmullerSpace.qcMetricSpace B.surface hg B.genus
    letI : TopologicalSpace (TeichmullerSpace.{0, 0} B.surface) :=
      mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
    letI : TopologicalSpace (OriginalGeneratorTeichmullerSpace g) :=
      TopologicalSpace.induced
        (originalCanonicalFrickeCoordinates hg B D hD hGeom hRealize hA) inferInstance
    let I :=
      (GeneralQC.closedSourceEquiv B.surface).trans
        (TeichmullerSpace.qcEquiv B.surface hg B.genus).symm
    let C := originalGeneratorComparison hg B
      (originalCanonicalFamilyMarkingTransport_of_qcCutPositiveTransport hg B D hD hGeom)
    let Phi := originalQCGeneratorComparison hg B D hD hGeom
    let F := originalCanonicalFrickeMap hg B D hD hGeom hRealize hA
    ∃ (Hqn : GeneralQC.ClosedSpace B.surface ≃ₜ TeichmullerSpace.{0, 0} B.surface)
      (Hno : TeichmullerSpace.{0, 0} B.surface ≃ₜ OriginalGeneratorTeichmullerSpace g)
      (Hof : OriginalGeneratorTeichmullerSpace g ≃ₜ originalCanonicalFrickeImage hg),
      (∀ z, Hqn z = I z) ∧
      (∀ t, Hno t = C t) ∧
      (∀ q, Hof q = F q) ∧
      (∀ z, Hno (Hqn z) = Phi z) ∧
      Nonempty (originalCanonicalFrickeImage hg ≃ₜ (Fin (6 * g - 6) → ℝ)) := by
  let := B.surface.toRiemannAtlas.toChartedSpace
  let mQ : PseudoMetricSpace (GeneralQC.ClosedSpace B.surface) :=
    GeneralQC.pseudoMetricSpace
      (GeneralQC.Surface.ofRiemannSurface B.surface.toRiemannSurface)
  let : PseudoMetricSpace (GeneralQC.ClosedSpace B.surface) := mQ
  let mT : MetricSpace (TeichmullerSpace.{0, 0} B.surface) :=
    TeichmullerSpace.qcMetricSpace B.surface hg B.genus
  let : MetricSpace (TeichmullerSpace.{0, 0} B.surface) := mT
  let : TopologicalSpace (TeichmullerSpace.{0, 0} B.surface) :=
    mT.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let f := originalCanonicalFrickeCoordinates hg B D hD hGeom hRealize hA
  let : TopologicalSpace (OriginalGeneratorTeichmullerSpace g) :=
    TopologicalSpace.induced f inferInstance
  let E := GeneralQC.closedSourceEquiv B.surface
  let Q := TeichmullerSpace.qcEquiv B.surface hg B.genus
  let I := E.trans Q.symm
  let hTransport := originalCanonicalFamilyMarkingTransport_of_qcCutPositiveTransport
    hg B D hD hGeom
  let C := originalGeneratorComparison hg B hTransport
  let Phi := originalQCGeneratorComparison hg B D hD hGeom
  let F := originalCanonicalFrickeMap hg B D hD hGeom hRealize hA
  change ∃ (Hqn : GeneralQC.ClosedSpace B.surface ≃ₜ TeichmullerSpace.{0, 0} B.surface)
      (Hno : TeichmullerSpace.{0, 0} B.surface ≃ₜ OriginalGeneratorTeichmullerSpace g)
      (Hof : OriginalGeneratorTeichmullerSpace g ≃ₜ originalCanonicalFrickeImage hg),
      (∀ z, Hqn z = I z) ∧ (∀ t, Hno t = C t) ∧ (∀ q, Hof q = F q) ∧
      (∀ z, Hno (Hqn z) = Phi z) ∧
      Nonempty (originalCanonicalFrickeImage hg ≃ₜ (Fin (6 * g - 6) → ℝ))
  have hI : Isometry I := by
    apply Isometry.of_dist_eq
    intro x y
    change TeichmullerSpace.fromQCDistance B.surface (Q.symm (E x)) (Q.symm (E y)) =
      GeneralQC.distance x y
    rw [GeneralQC.distance_eq_source_bookDistance]
    change QCBookMetric.bookDistance (Q (Q.symm (E x))) (Q (Q.symm (E y))) =
      QCBookMetric.bookDistance (E x) (E y)
    rw [Q.apply_symm_apply, Q.apply_symm_apply]
  let J : GeneralQC.ClosedSpace B.surface ≃ᵢ TeichmullerSpace.{0, 0} B.surface :=
    { toEquiv := I
      isometry_toFun := hI }
  let Hqn := J.toHomeomorph
  have hC : IsHomeomorph C :=
    originalGeneratorComparison_fricke_isHomeomorph hg B D hD hGeom hRealize hA hAlt
  let Hno := IsHomeomorph.homeomorph C hC
  have hFb : Function.Bijective F :=
    originalCanonicalFrickeMap_bijective hg B D hD hGeom hRealize hA hAlt
  have hfi : Function.Injective f := by
    intro p q hpq
    apply hFb.1
    exact Subtype.ext hpq
  have hcomp : IsEmbedding
      ((Subtype.val : originalCanonicalFrickeImage hg → (Fin (6 * g - 6) → ℝ)) ∘ F) := by
    change IsEmbedding f
    exact IsEmbedding.induced hfi
  have hFe : IsEmbedding F := (IsEmbedding.subtypeVal.of_comp_iff).mp hcomp
  have hF : IsHomeomorph F :=
    isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hFe, hFb.2⟩
  let Hof := IsHomeomorph.homeomorph F hF
  have hPhi (z : GeneralQC.ClosedSpace B.surface) : C (I z) = Phi z := by
    apply hfi
    calc
      f (C (I z)) = finiteFrickeCoordinates hA (I z) :=
        originalCanonicalFrickeCoordinates_comparison hg B D hD hGeom hRealize hA (I z)
      _ = f (Phi z) :=
        (originalQCFrickeCoordinates_eq_native hg B D hD hGeom hRealize hA z).symm
  refine ⟨Hqn, Hno, Hof, fun _ => rfl, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro z
    change C (I z) = Phi z
    exact hPhi z
  · obtain ⟨H⟩ := (nativeFrickeImage_domain B.surface hg B.genus hA hAlt).2.2.2
    have hImage : originalCanonicalFrickeImage hg = nativeFrickeImage hA :=
      originalCanonicalFrickeImage_eq_nativeFrickeImage hg B D hD hGeom hRealize hA
    exact ⟨(Homeomorph.setCongr hImage).trans H⟩

end LowDimensionalTopology.Geometry.Teichmuller
