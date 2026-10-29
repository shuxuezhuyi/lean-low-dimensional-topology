module

public import LowDimensionalTopology.Geometry.Teichmuller.OriginalReflectedClosedSurface
public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCClosedCompatibility

/-!
# Reflection of the original QC-marked quotient

The given involution, the original target, its topology and the actual QC
marking are retained. The target complex charts are conjugated. No existence
of the involution, Teichmüller complex-coordinate assertion, or metric
reflection identity is assumed or established here.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Topology
open scoped Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open Surfaces

variable {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)

/-- Reflect the same original QC-marked target using the given base involution. -/
def originalReflectedClosedMarked (J : X ≃ₜ X)
    (hJ : @LiZhongQC.IsAnticonformalInvolution X inferInstance
      R.toRiemannAtlas.toChartedSpace J) (m : ClosedMarked R) : ClosedMarked R := by
  let A := R.toSourceClosedRS
  let S := closedTarget R m
  refine
    { target := Surface.ofRiemannSurface (originalMirrorNative S).toRiemannSurface
      marking := J.trans m.marking
      qc := ?_ }
  have hmirror : @LiZhongQC.IsQCRS X inferInstance (originalMirrorChartedSpace A)
      S.carrier S.topologicalSpace (originalMirrorChartedSpace S) m.marking :=
    originalMirror_isQCRS A S m.marking m.qc
  have hJqc : @LiZhongQC.IsQCRS X inferInstance A.chartedSpace
      X inferInstance (originalMirrorChartedSpace A) J :=
    ⟨1, originalInvolution_isKQCRS_toMirror A J hJ⟩
  have hqc : @LiZhongQC.IsQCRS X inferInstance A.chartedSpace
      S.carrier S.topologicalSpace (originalMirrorChartedSpace S)
      (J.trans m.marking) :=
    @LiZhongQC.s28q_isQCRS_trans X X S.carrier
      inferInstance A.chartedSpace A.isManifold
      inferInstance (originalMirrorChartedSpace A) (originalMirror_isManifold A)
      S.topologicalSpace (originalMirrorChartedSpace S)
        (originalMirror_isManifold S) J m.marking hJqc hmirror
  exact (@qc_target_toNative X inferInstance A.chartedSpace A.isManifold
    (originalMirrorClosedRS S) (J.trans m.marking) hqc).1

/-- The reflected target is the literal mirror atlas of the actual original target. -/
theorem originalReflectedClosedMarked_target (J : X ≃ₜ X)
    (hJ : @LiZhongQC.IsAnticonformalInvolution X inferInstance
      R.toRiemannAtlas.toChartedSpace J) (m : ClosedMarked R) :
    (originalReflectedClosedMarked R J hJ m).target =
      Surface.ofRiemannSurface
        (originalMirrorNative (closedTarget R m)).toRiemannSurface := rfl

/-- The raw marking is precisely the source composition with the same J. -/
theorem originalReflectedClosedMarked_marking_apply (J : X ≃ₜ X)
    (hJ : @LiZhongQC.IsAnticonformalInvolution X inferInstance
      R.toRiemannAtlas.toChartedSpace J) (m : ClosedMarked R) (x : X) :
    (originalReflectedClosedMarked R J hJ m).marking x =
      originalMirrorCanonicalMap (closedTarget R m) (m.marking (J x)) := rfl

/-- The same actual conformal witness and marking homotopy descend to the mirrors. -/
theorem originalReflectedClosedMarked_equivalent (J : X ≃ₜ X)
    (hJ : @LiZhongQC.IsAnticonformalInvolution X inferInstance
      R.toRiemannAtlas.toChartedSpace J) (m n : ClosedMarked R)
    (h : m.Equivalent n) :
    (originalReflectedClosedMarked R J hJ m).Equivalent
      (originalReflectedClosedMarked R J hJ n) := by
  obtain ⟨c, hc, H⟩ := h
  let S := closedTarget R m
  let T := closedTarget R n
  have hcmirror := originalMirror_isBiholomorphic S T c hc
  have hcnative := biholomorphic_closed_toNative
    (originalMirrorClosedRS S) (originalMirrorClosedRS T) c hcmirror
  change ∃ d : m.target.carrier ≃ₜ n.target.carrier,
    (@LiZhongQC.IsBiholomorphic S.carrier S.topologicalSpace
      (originalMirrorNative S).toRiemannAtlas.toChartedSpace
      T.carrier T.topologicalSpace (originalMirrorNative T).toRiemannAtlas.toChartedSpace d) ∧
    ContinuousMap.Homotopic
      (⟨fun x => d (m.marking (J x)),
        (d.continuous.comp m.marking.continuous).comp J.continuous⟩ : C(X, n.target.carrier))
      (⟨fun x => n.marking (J x), n.marking.continuous.comp J.continuous⟩ :
        C(X, n.target.carrier))
  refine ⟨c, hcnative, ?_⟩
  have hpre := H.comp
    (ContinuousMap.Homotopic.refl (⟨J, J.continuous⟩ : C(X, X)))
  exact hpre

/-- The literal reflected representative defines a map on the original QC quotient. -/
def originalTeichmullerReflection (J : X ≃ₜ X)
    (hJ : @LiZhongQC.IsAnticonformalInvolution X inferInstance
      R.toRiemannAtlas.toChartedSpace J) : ClosedSpace R → ClosedSpace R :=
  Quotient.lift (fun m => mk (originalReflectedClosedMarked R J hJ m))
    (fun m n h => Quotient.sound (originalReflectedClosedMarked_equivalent R J hJ m n h))

/-- The original class formula retains the same target and raw marking. -/
theorem originalTeichmullerReflection_mk (J : X ≃ₜ X)
    (hJ : @LiZhongQC.IsAnticonformalInvolution X inferInstance
      R.toRiemannAtlas.toChartedSpace J) (m : ClosedMarked R) :
    originalTeichmullerReflection R J hJ (mk m) =
      mk (originalReflectedClosedMarked R J hJ m) := rfl

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
