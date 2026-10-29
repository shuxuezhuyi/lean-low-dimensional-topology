module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalCanonicalFrickeVector
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalQCGeneratorComparison

/-!
# Literal coordinates on the original canonical-marked quotient

The map chooses the unique actual canonical-model vector of each original
surface and descends that vector through the original equivalence relation.
Its representative formula holds for every supplied original cut and model.
The native commuting identity retains the actual transported polygon and
all matrices; coordinate injectivity uses only the stated axis obligations.
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
  (hRealize : Unproved.Teichmuller.OriginalGeneratorPrescribedPositiveSmoothRealization hg B)
  (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable B.surface hg D.polygon)

include B D hD hRealize hA in
/-- Existence is the existential part of the proved unique actual vector. -/
theorem originalCanonicalFrickeVector_exists (N : OriginalGeneratorMarkedSurface g) :
    ∃ v : Fin (6 * g - 6) → ℝ, IsOriginalCanonicalFrickeVector hg N v := by
  obtain ⟨v, hv, _⟩ := existsUnique_originalCanonicalFrickeVector hg B D hD hRealize hA N
  exact ⟨v, hv⟩

/-- Choose the unique vector of an actual original geometrically marked surface. -/
def originalCanonicalFrickeVector (N : OriginalGeneratorMarkedSurface g) : Fin (6 * g - 6) → ℝ :=
  Classical.choose (originalCanonicalFrickeVector_exists hg B D hD hRealize hA N)

/-- The chosen vector is the literal vector of an actual original identity model. -/
theorem originalCanonicalFrickeVector_spec (N : OriginalGeneratorMarkedSurface g) :
    IsOriginalCanonicalFrickeVector hg N
      (originalCanonicalFrickeVector hg B D hD hRealize hA N) :=
  Classical.choose_spec (originalCanonicalFrickeVector_exists hg B D hD hRealize hA N)

/-- Every supplied cut and identity model gives the same chosen vector. -/
theorem originalCanonicalFrickeVector_eq_model (N : OriginalGeneratorMarkedSurface g)
    (E : OriginalOrientedCanonicalCut N.surface g
      (lt_trans Nat.zero_lt_one hg) N.point)
    (hE : E.family = N.classes)
    (P : NormalizedCanonicalFuchsianModel hg E.polygon (MarkedRiemannSurface.refl N.surface)) :
    originalCanonicalFrickeVector hg B D hD hRealize hA N =
      flattenFirstBookData P.firstBookCoordinates := by
  obtain ⟨_u, _hu, hUnique⟩ := existsUnique_originalCanonicalFrickeVector hg B D hD hRealize hA N
  exact (hUnique _ (originalCanonicalFrickeVector_spec hg B D hD hRealize hA N)).trans
    (hUnique _ ⟨E, hE, P, rfl⟩).symm

include hGeom in
/-- Original equivalence preserves the actual chosen canonical-model vector. -/
theorem originalCanonicalFrickeVector_equivalent {M N : OriginalGeneratorMarkedSurface g}
    (hMN : M.Equivalent N) :
    originalCanonicalFrickeVector hg B D hD hRealize hA M =
      originalCanonicalFrickeVector hg B D hD hRealize hA N := by
  exact originalCanonicalFrickeVector_eq_of_equivalent hg B D hD hGeom hRealize hA hMN
    (originalCanonicalFrickeVector_spec hg B D hD hRealize hA M)
    (originalCanonicalFrickeVector_spec hg B D hD hRealize hA N)

/-- Descend the unique actual vector to the independent original quotient. -/
def originalCanonicalFrickeCoordinates :
    OriginalGeneratorTeichmullerSpace g → (Fin (6 * g - 6) → ℝ) :=
  Quotient.lift (originalCanonicalFrickeVector hg B D hD hRealize hA)
    (fun _ _ h => originalCanonicalFrickeVector_equivalent hg B D hD hGeom hRealize hA h)

/-- The quotient map reads every supplied original model literally. -/
theorem originalCanonicalFrickeCoordinates_mk_eq_model
    (N : OriginalGeneratorMarkedSurface g)
    (E : OriginalOrientedCanonicalCut N.surface g
      (lt_trans Nat.zero_lt_one hg) N.point)
    (hE : E.family = N.classes)
    (P : NormalizedCanonicalFuchsianModel hg E.polygon (MarkedRiemannSurface.refl N.surface)) :
    originalCanonicalFrickeCoordinates hg B D hD hGeom hRealize hA
        (OriginalGeneratorTeichmullerSpace.mk N) =
      flattenFirstBookData P.firstBookCoordinates :=
  originalCanonicalFrickeVector_eq_model hg B D hD hRealize hA N E hE P

/-- The same native marking gives the same literal finite coordinate vector. -/
theorem originalCanonicalFrickeCoordinates_comparison
    (t : TeichmullerSpace.{0, 0} B.surface) :
    originalCanonicalFrickeCoordinates hg B D hD hGeom hRealize hA
        (originalGeneratorComparison hg B
          (originalCanonicalFamilyMarkingTransport_of_qcCutPositiveTransport hg B D hD hGeom) t) =
      finiteFrickeCoordinates hA t := by
  induction t using Quotient.inductionOn with
  | _ m =>
    let hTransport := originalCanonicalFamilyMarkingTransport_of_qcCutPositiveTransport
      hg B D hD hGeom
    let N := originalGeneratorMarkedTarget hg B hTransport m
    let := B.surface.compactSpace
    have hqc :
        letI := B.surface.toRiemannAtlas.toChartedSpace
        letI := m.surface.toRiemannAtlas.toChartedSpace
        LiZhongQC.IsQCRS m.marking.toHomeomorph :=
      m.marking.isQCRS_of_compact m.orientation_preserving
    let E := D.mapQC (hg := hg) hGeom m.surface m.marking.toHomeomorph hqc
    have hE : E.family = N.classes := by
      funext i
      change E.family i =
        FundamentalGroup.map
          (⟨m.marking.toHomeomorph, m.marking.toHomeomorph.continuous⟩ :
            C(B.carrier, m.carrier)) B.point (B.classes i)
      simpa only [hD] using
        (D.mapQC_family (hg := hg) hGeom m.surface m.marking.toHomeomorph hqc i)
    let P := chosenCanonicalModel hA m
    let Q : NormalizedCanonicalFuchsianModel hg E.polygon
        (MarkedRiemannSurface.refl N.surface) :=
      { model := P.model
        liftBase := P.liftBase
        liftBase_proj := P.liftBase_proj
        matrices := P.matrices
        represents := P.represents
        alpha_attracting := P.alpha_attracting
        beta_attracting_repelling := P.beta_attracting_repelling }
    change originalCanonicalFrickeCoordinates hg B D hD hGeom hRealize hA
      (OriginalGeneratorTeichmullerSpace.mk N) = _
    rw [originalCanonicalFrickeCoordinates_mk_eq_model hg B D hD hGeom hRealize hA N E hE Q]
    change flattenFirstBookData P.firstBookCoordinates =
      finiteFrickeCoordinates hA (TeichmullerSpace.mk m)
    exact (finiteFrickeCoordinates_eq_model hA P).symm

/-- The actual coordinate value lies in the independently defined original image. -/
theorem originalCanonicalFrickeCoordinates_mem_image (q : OriginalGeneratorTeichmullerSpace g) :
    originalCanonicalFrickeCoordinates hg B D hD hGeom hRealize hA q ∈
      originalCanonicalFrickeImage hg := by
  induction q using Quotient.inductionOn with
  | _ N =>
    exact ⟨N, originalCanonicalFrickeVector_spec hg B D hD hRealize hA N⟩

/-- The genuine coordinate map with its independently defined image as codomain. -/
def originalCanonicalFrickeMap :
    OriginalGeneratorTeichmullerSpace g → originalCanonicalFrickeImage hg :=
  fun q => ⟨originalCanonicalFrickeCoordinates hg B D hD hGeom hRealize hA q,
    originalCanonicalFrickeCoordinates_mem_image hg B D hD hGeom hRealize hA q⟩

/-- Original canonical coordinates are bijective under the existing pointwise
axis obligations, with no additional model or compatibility premise. -/
theorem originalCanonicalFrickeMap_bijective
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} B.surface,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m)) :
    Function.Bijective (originalCanonicalFrickeMap hg B D hD hGeom hRealize hA) := by
  let hTransport := originalCanonicalFamilyMarkingTransport_of_qcCutPositiveTransport
    hg B D hD hGeom
  have hC := originalGeneratorComparison_bijective hg B hTransport hRealize
  constructor
  · intro p q hpq
    obtain ⟨x, rfl⟩ := hC.2 p
    obtain ⟨y, rfl⟩ := hC.2 q
    have hcoords := congrArg Subtype.val hpq
    change originalCanonicalFrickeCoordinates hg B D hD hGeom hRealize hA
        (originalGeneratorComparison hg B hTransport x) =
      originalCanonicalFrickeCoordinates hg B D hD hGeom hRealize hA
        (originalGeneratorComparison hg B hTransport y) at hcoords
    rw [originalCanonicalFrickeCoordinates_comparison hg B D hD hGeom hRealize hA,
      originalCanonicalFrickeCoordinates_comparison hg B D hD hGeom hRealize hA] at hcoords
    exact congrArg (originalGeneratorComparison hg B hTransport)
      (finiteFrickeCoordinates_injective hA hAlt hcoords)
  · intro v
    obtain ⟨N, E, hE, P, hP⟩ := v.property
    refine ⟨OriginalGeneratorTeichmullerSpace.mk N, ?_⟩
    apply Subtype.ext
    exact (originalCanonicalFrickeCoordinates_mk_eq_model hg B D hD hGeom hRealize hA
      N E hE P).trans hP

/-- The literal original QC comparison followed by the genuine coordinates is bijective. -/
theorem originalCanonicalFrickeMap_comp_qc_bijective
    (hAlt : ∀ m : MarkedRiemannSurface.{0, 0} B.surface,
      Unproved.Teichmuller.CanonicalLastPairAxisAlternation (chosenCanonicalModel hA m)) :
    Function.Bijective
      (originalCanonicalFrickeMap hg B D hD hGeom hRealize hA ∘
        originalQCGeneratorComparison hg B D hD hGeom) :=
  (originalCanonicalFrickeMap_bijective hg B D hD hGeom hRealize hA hAlt).comp
    (originalQCGeneratorComparison_bijective hg B D hD hGeom hRealize)

end LowDimensionalTopology.Geometry.Teichmuller
