module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalCanonicalModelPathTransport
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalCanonicalCutQCTransport
public import LowDimensionalTopology.Geometry.Teichmuller.OriginalGeneratorComparison
public import LowDimensionalTopology.Geometry.Teichmuller.AmbientFirstBookMatrices
public import LowDimensionalTopology.Geometry.Teichmuller.NativeFrickeImageTopology

/-!
# The literal image of original geometrically marked canonical models

The image is defined independently by all original marked surfaces and the
literal coordinates of their identity-marking models. Its comparison with
the native image transports actual cuts and a supplied model through one
common path, preserving every matrix used by the coordinates.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces

/-- A literal coordinate vector of an actual identity-marking model of the
same original surface, point and entire geometrically canonical family. -/
def IsOriginalCanonicalFrickeVector {g : ℕ} (hg : 1 < g)
    (N : OriginalGeneratorMarkedSurface g) (v : Fin (6 * g - 6) → ℝ) : Prop :=
  ∃ E : OriginalOrientedCanonicalCut N.surface g
      (lt_trans Nat.zero_lt_one hg) N.point,
    E.family = N.classes ∧
      ∃ P : NormalizedCanonicalFuchsianModel hg E.polygon
          (MarkedRiemannSurface.refl N.surface),
        flattenFirstBookData P.firstBookCoordinates = v

/-- The independently defined image of all original geometrically marked
surfaces through their actual normalized identity-marking models. -/
def originalCanonicalFrickeImage {g : ℕ} (hg : 1 < g) :
    Set (Fin (6 * g - 6) → ℝ) :=
  {v | ∃ N : OriginalGeneratorMarkedSurface g,
    IsOriginalCanonicalFrickeVector hg N v}

/-- The original canonical image agrees with the actual native image under
the same geometric transport, prescribed realization and model inputs. -/
theorem originalCanonicalFrickeImage_eq_nativeFrickeImage
    {g : ℕ} (hg : 1 < g) (B : OriginalGeneratorMarkedSurface g)
    (D : OriginalOrientedCanonicalCut B.surface g
      (lt_trans Nat.zero_lt_one hg) B.point)
    (hD : D.family = B.classes)
    (hGeom : Unproved.Teichmuller.OriginalCanonicalCutQCPositiveTransport
      B.surface hg B.point D)
    (hRealize : Unproved.Teichmuller.OriginalGeneratorPrescribedPositiveSmoothRealization
      hg B)
    (hA : Unproved.Teichmuller.CanonicalNormalizedModelsAvailable
      B.surface hg D.polygon) :
    originalCanonicalFrickeImage hg = nativeFrickeImage hA := by
  classical
  let hTransport := originalCanonicalFamilyMarkingTransport_of_qcCutPositiveTransport
    hg B D hD hGeom
  ext v
  constructor
  · rintro ⟨N, E, hE, P, hPv⟩
    obtain ⟨F, hF, c, hc⟩ := hRealize N
    let mF : MarkedRiemannSurface.{0, 0} B.surface :=
      { carrier := N.carrier
        topology := N.topology
        surface := N.surface
        marking := F
        orientation_preserving := hF }
    let P₀ := chosenCanonicalModel hA mF
    obtain ⟨_L, Q, _hL, _hL₀, _hL₁, _hModel, hMatrices⟩ :=
      NormalizedCanonicalFuchsianModel.exists_transportOriginalCanonicalPath
        hg B N D hD E hE F hF c hc P₀
    have hData : Q.firstBookCoordinates = P₀.firstBookCoordinates := by
      exact congrArg (fun A : Fin g × Fin 2 → RealSL => fun i : Fin (g - 1) =>
        let positiveLift := fun b : Fin 2 =>
          let M := A (NormalizedCanonicalFuchsianModel.firstBookIndex i, b)
          if 0 < M 1 0 then M else -M
        (bookMatrixCoordinates (positiveLift 0), bookMatrixCoordinates (positiveLift 1))) hMatrices
    have hQP : Q.firstBookCoordinates = P.firstBookCoordinates :=
      Q.firstBookCoordinates_eq_of_equivalent P
        (MarkedRiemannSurface.equivalent_refl (MarkedRiemannSurface.refl N.surface))
    apply (mem_nativeFrickeImage_iff hA v).mpr
    refine ⟨TeichmullerSpace.mk mF, ?_⟩
    calc
      finiteFrickeCoordinates hA (TeichmullerSpace.mk mF) =
          flattenFirstBookData P₀.firstBookCoordinates := finiteFrickeCoordinates_eq_model hA P₀
      _ = flattenFirstBookData Q.firstBookCoordinates := congrArg flattenFirstBookData hData.symm
      _ = flattenFirstBookData P.firstBookCoordinates := congrArg flattenFirstBookData hQP
      _ = v := hPv
  · intro hv
    obtain ⟨t, rfl⟩ := (mem_nativeFrickeImage_iff hA v).mp hv
    induction t using Quotient.inductionOn with
    | _ m =>
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
      refine ⟨N, E, hE, Q, ?_⟩
      change flattenFirstBookData P.firstBookCoordinates =
        finiteFrickeCoordinates hA (TeichmullerSpace.mk m)
      exact (finiteFrickeCoordinates_eq_model hA P).symm

end LowDimensionalTopology.Geometry.Teichmuller
