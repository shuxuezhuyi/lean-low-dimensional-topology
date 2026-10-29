module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalCanonicalCutQCTransport
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalGeneratorComparison
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCClosedCompatibility
public import LowDimensionalTopology.Geometry.Teichmuller.CanonicalQCMetric

/-!
# The original quasiconformal marking and its ordered canonical family

Every given quasiconformal representative keeps its target carrier, original
complex atlas, image basepoint and all induced ordered classes. One actual
homotopy trace makes the comparison descend to the original QC quotient.
The genuine smooth inclusion identifies this map with the earlier canonical
comparison, so its prescribed realization premise gives a bijection.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

variable {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g)
  (D : OriginalOrientedCanonicalCut B.surface g
    (lt_trans Nat.zero_lt_one hg) B.point)
  (hD : D.family = B.classes)
  (hGeom : Unproved.Teichmuller.OriginalCanonicalCutQCPositiveTransport
    B.surface hg B.point D)

/-- Only compactness is added to the actual target's unchanged Riemann surface. -/
def originalQCClosedTarget (m : GeneralQC.ClosedMarked B.surface) :
    ClosedRiemannSurface m.target.carrier where
  toRiemannSurface := m.target.riemann
  compactSpace := GeneralQC.closed_target_compact B.surface m

/-- The given QC marking sends the same point and every original ordered
class to the unchanged target with its original complex atlas. -/
def originalQCGeneratorMarkedTarget (m : GeneralQC.ClosedMarked B.surface) :
    OriginalGeneratorMarkedSurface g where
  carrier := m.target.carrier
  topology := m.target.topology
  surface := originalQCClosedTarget B m
  genus := by
    obtain ⟨e⟩ := B.genus
    exact ⟨m.marking.symm.trans e⟩
  point := m.marking B.point
  classes := fun i =>
    FundamentalGroup.map (⟨m.marking, m.marking.continuous⟩ : C(B.carrier, m.target.carrier))
      B.point (B.classes i)
  canonical := originalCanonicalFamily_of_qcCutPositiveTransport hg B D hD hGeom
    (originalQCClosedTarget B m) m.marking m.qc

theorem originalQCGeneratorMarkedTarget_equivalent
    {m n : GeneralQC.ClosedMarked B.surface} (hmn : m.Equivalent n) :
    (originalQCGeneratorMarkedTarget hg B D hD hGeom m).Equivalent
      (originalQCGeneratorMarkedTarget hg B D hD hGeom n) := by
  obtain ⟨k, hk, hh⟩ := (GeneralQC.marked_equivalent_iff_analytic m n).mp hmn
  change ContinuousMap.Homotopic
    ((⟨k, k.continuous⟩ : C(m.target.carrier, n.target.carrier)).comp
      (⟨m.marking, m.marking.continuous⟩ : C(B.carrier, m.target.carrier)))
    (⟨n.marking, n.marking.continuous⟩ : C(B.carrier, n.target.carrier)) at hh
  obtain ⟨H⟩ := hh
  apply OriginalGeneratorMarkedSurface.equivalent_symm
  dsimp only [OriginalGeneratorMarkedSurface.Equivalent, originalQCGeneratorMarkedTarget,
    originalQCClosedTarget]
  refine ⟨k, hk, H.evalAt B.point, ?_⟩
  intro i
  change FundamentalGroup.fundamentalGroupMulEquivOfPath (H.evalAt B.point)
    (FundamentalGroup.map
      (⟨k, k.continuous⟩ : C(m.target.carrier, n.target.carrier))
      ((⟨m.marking, m.marking.continuous⟩ : C(B.carrier, m.target.carrier)) B.point)
      (FundamentalGroup.map
        (⟨m.marking, m.marking.continuous⟩ : C(B.carrier, m.target.carrier))
        B.point (B.classes i))) =
    FundamentalGroup.map
      (⟨n.marking, n.marking.continuous⟩ : C(B.carrier, n.target.carrier))
      B.point (B.classes i)
  simpa only [FundamentalGroup.map_comp, MonoidHom.comp_apply, ContinuousMap.coe_mk] using
    (homotopy_basedLoop_transport
      ((⟨k, k.continuous⟩ : C(m.target.carrier, n.target.carrier)).comp
        (⟨m.marking, m.marking.continuous⟩ : C(B.carrier, m.target.carrier)))
      (⟨n.marking, n.marking.continuous⟩ : C(B.carrier, n.target.carrier))
      H B.point (B.classes i))

/-- The literal original-QC comparison with the independent geometric
canonical-marking quotient. Its target is not defined as its own image. -/
def originalQCGeneratorComparison :
    GeneralQC.ClosedSpace B.surface → OriginalGeneratorTeichmullerSpace g :=
  Quotient.lift
    (fun m => OriginalGeneratorTeichmullerSpace.mk
      (originalQCGeneratorMarkedTarget hg B D hD hGeom m))
    (fun _ _ h => Quotient.sound
      (originalQCGeneratorMarkedTarget_equivalent hg B D hD hGeom h))

/-- Every original QC representative retains its actual target, image point
and all induced ordered classes in the comparison. -/
theorem originalQCGeneratorComparison_mk (m : GeneralQC.ClosedMarked B.surface) :
    originalQCGeneratorComparison hg B D hD hGeom (GeneralQC.mk m) =
      OriginalGeneratorTeichmullerSpace.mk
        (originalQCGeneratorMarkedTarget hg B D hD hGeom m) := rfl

/-- The actual smooth marking is included without changing its target atlas. -/
private def smoothOriginalQCMarked (m : MarkedRiemannSurface.{0, 0} B.surface) :
    GeneralQC.ClosedMarked B.surface where
  target := GeneralQC.Surface.ofRiemannSurface m.surface.toRiemannSurface
  marking := m.marking.toHomeomorph
  qc := by
    let := B.surface.compactSpace
    exact m.marking.isQCRS_of_compact m.orientation_preserving

private theorem smoothOriginalQCMarked_equivalent
    {m n : MarkedRiemannSurface.{0, 0} B.surface}
    (hmn : MarkedRiemannSurface.Equivalent m n) :
    (smoothOriginalQCMarked B m).Equivalent (smoothOriginalQCMarked B n) := by
  obtain ⟨k, hk, hh⟩ := hmn
  apply (GeneralQC.marked_equivalent_iff_analytic
    (smoothOriginalQCMarked B m) (smoothOriginalQCMarked B n)).mpr
  exact ⟨k, hk, hh⟩

private def smoothOriginalQCClass :
    TeichmullerSpace.{0, 0} B.surface → GeneralQC.ClosedSpace B.surface :=
  Quotient.lift (fun m => GeneralQC.mk (smoothOriginalQCMarked B m))
    (fun _ _ h => Quotient.sound (smoothOriginalQCMarked_equivalent B h))

private theorem smoothOriginalQCClass_source (t : TeichmullerSpace.{0, 0} B.surface) :
    GeneralQC.closedSourceEquiv B.surface (smoothOriginalQCClass B t) =
      TeichmullerSpace.qcEquiv B.surface hg B.genus t := by
  refine Quotient.inductionOn t ?_
  intro m
  rfl

private theorem smoothOriginalQCClass_bijective
    {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g) :
    Function.Bijective (smoothOriginalQCClass B) := by
  constructor
  · intro t u htu
    apply (TeichmullerSpace.qcEquiv B.surface hg B.genus).injective
    rw [← smoothOriginalQCClass_source hg B t,
      ← smoothOriginalQCClass_source hg B u, htu]
  · intro q
    refine ⟨(TeichmullerSpace.qcEquiv B.surface hg B.genus).symm
      (GeneralQC.closedSourceEquiv B.surface q), ?_⟩
    apply (GeneralQC.closedSourceEquiv B.surface).injective
    rw [smoothOriginalQCClass_source hg B]
    exact (TeichmullerSpace.qcEquiv B.surface hg B.genus).apply_symm_apply _

private theorem originalQCGeneratorComparison_smooth
    (t : TeichmullerSpace.{0, 0} B.surface) :
    originalQCGeneratorComparison hg B D hD hGeom (smoothOriginalQCClass B t) =
      originalGeneratorComparison hg B
        (originalCanonicalFamilyMarkingTransport_of_qcCutPositiveTransport
          hg B D hD hGeom) t := by
  refine Quotient.inductionOn t ?_
  intro m
  rfl

/-- The original QC comparison is bijective under the same single cut
geometry premise and the existing prescribed positive-smooth realization.
The weaker smooth transport premise is derived, not independently assumed. -/
theorem originalQCGeneratorComparison_bijective
    (hRealize : Unproved.Teichmuller.OriginalGeneratorPrescribedPositiveSmoothRealization
      hg B) :
    Function.Bijective (originalQCGeneratorComparison hg B D hD hGeom) := by
  let hTransport : Unproved.Teichmuller.OriginalCanonicalFamilyMarkingTransport hg B :=
    originalCanonicalFamilyMarkingTransport_of_qcCutPositiveTransport hg B D hD hGeom
  have hC : Function.Bijective (originalGeneratorComparison hg B hTransport) :=
    originalGeneratorComparison_bijective hg B hTransport hRealize
  have hJ := smoothOriginalQCClass_bijective hg B
  constructor
  · intro q r hqr
    obtain ⟨t, rfl⟩ := hJ.2 q
    obtain ⟨u, rfl⟩ := hJ.2 r
    have htu : originalGeneratorComparison hg B hTransport t =
        originalGeneratorComparison hg B hTransport u := by
      rw [← originalQCGeneratorComparison_smooth hg B D hD hGeom t,
        ← originalQCGeneratorComparison_smooth hg B D hD hGeom u]
      exact hqr
    exact congrArg (smoothOriginalQCClass B) (hC.1 htu)
  · intro c
    obtain ⟨t, ht⟩ := hC.2 c
    refine ⟨smoothOriginalQCClass B t, ?_⟩
    rw [originalQCGeneratorComparison_smooth hg B D hD hGeom]
    exact ht

end LowDimensionalTopology.Geometry.Teichmuller
