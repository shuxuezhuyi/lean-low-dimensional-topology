/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicFaceExtension
public import LowDimensionalTopology.External.LeanPool.ClassificationOfSurfaces.FiniteCyclicCanonicalRealization
/-!
# Geometry of boundary-word occurrences

The unique stored face is the marked polygon cell, and its occurrences retain
the original finite indices and signed darts. Compatible side pairings reverse
parameters and have exactly the original involution as their partner map.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- The actual unique face stored by the genuine original pairing word. -/
def originalCyclicFaceZero {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) : (originalCyclicPresentation J e).presentation.Face :=
  ⟨0,by simp [originalCyclicPresentation,_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.freeInvolutionPresentation,ofOneFaceWord]⟩

/-- The actual stored one-face pre-realization is exactly the same genuine marked disk. -/
def originalCyclicPreFaceHomeomorph {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) :
    (originalCyclicPresentation J e).presentation.PolygonalPreRealization≃ₜPolygonCell J.n where
  toFun x:=⟨x.2.val,x.2.property⟩
  invFun x:=⟨originalCyclicFaceZero J e,⟨x.val,x.property⟩⟩
  left_inv := by
    rintro ⟨f,x⟩
    have hf : f=originalCyclicFaceZero J e := by
      apply Fin.ext
      have hlen:(originalCyclicPresentation J e).presentation.faces.length=1:=rfl
      have hlt:f.val<1:=f.isLt.trans_le hlen.le
      change f.val=0
      omega
    subst f
    rfl
  right_inv x:=rfl
  continuous_toFun := by
    apply continuous_sigma_iff.mpr
    intro f
    exact continuous_induced_rng.mpr PolygonCell.continuous_val
  continuous_invFun := continuous_sigmaMk.comp
    (continuous_induced_rng.mpr PolygonCell.continuous_val)

/-- No actual disk coordinate is changed by unpacking the stored unique original face. -/
theorem originalCyclicPreFaceHomeomorph_coe {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD)
    (x:(originalCyclicPresentation J e).presentation.PolygonalPreRealization) :
    (originalCyclicPreFaceHomeomorph J e x:ℂ)=(x.2:ℂ) := rfl

/-- Every stored original face has precisely the actual boundary occurrence count. -/
theorem originalCyclicFaceBoundary_length {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) (f:(originalCyclicPresentation J e).presentation.Face) :
    ((originalCyclicPresentation J e).presentation.boundary f).length=J.n :=
  (ofOneFaceWord_boundary_length (originalCyclicWord J e) f).trans
    (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.freeInvolutionWord_length _ _ _)

/-- The literal occurrence index retained by the stored actual one-face word. -/
def originalCyclicOccurrenceIndex {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) :
    (originalCyclicPresentation J e).presentation.BoundaryOccurrence≃Fin J.n where
  toFun o:=Fin.cast (originalCyclicFaceBoundary_length J e o.1) o.2
  invFun i:=⟨originalCyclicFaceZero J e,Fin.cast (originalCyclicFaceBoundary_length J e _).symm i⟩
  left_inv := by
    rintro ⟨f,i⟩
    have hf:f=originalCyclicFaceZero J e:=by
      apply Fin.ext
      have hlen:(originalCyclicPresentation J e).presentation.faces.length=1:=rfl
      have hlt:f.val<1:=f.isLt.trans_le hlen.le
      change f.val=0
      omega
    subst f
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Fin.ext
    rfl
  right_inv i:=Fin.ext rfl

theorem originalCyclicOccurrenceIndex_val {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD)
    (o:(originalCyclicPresentation J e).presentation.BoundaryOccurrence) :
    (originalCyclicOccurrenceIndex J e o).val=o.2.val := rfl

/-- The stored enumerated signed dart is exactly the same original geometric signed occurrence, with only the finite edge-name enumeration changed. -/
theorem originalCyclicOccurrenceIndex_dart {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD)
    (o:(originalCyclicPresentation J e).presentation.BoundaryOccurrence) :
    o.dart=SignedDart.mapEquiv (Fintype.equivFin
      (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.InvolutionPositive (originalCyclicFinPair J e)))
      (originalCyclicDart J e (originalCyclicOccurrenceIndex J e o)) := by
  refine (ofOneFaceWordMapOccurrence_dart (originalCyclicWord J e) o).symm.trans ?_
  congr 1
  change (originalCyclicWord J e).get _=originalCyclicDart J e _
  simp only [originalCyclicWord_eq_ofFn,List.get_ofFn]
  congr 1
end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- Every genuine stored signed occurrence is distinct: no repeated same-sign word occurrence is silently identified. -/
theorem originalCyclicOccurrence_dart_injective {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD) :
    Function.Injective (@FiniteCyclicPresentation.BoundaryOccurrence.dart
      (originalCyclicPresentation J e).presentation) := by
  intro x y he
  rw [originalCyclicOccurrenceIndex_dart J e x,originalCyclicOccurrenceIndex_dart J e y] at he
  apply (originalCyclicOccurrenceIndex J e).injective
  apply (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.freeInvolutionDartEquiv (originalCyclicFinPair J
    e)
    (originalCyclicFinPair_involutive J e) (originalCyclicFinPair_ne_self J e)).injective
  exact (SignedDart.mapEquiv (Fintype.equivFin
    (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.InvolutionPositive (originalCyclicFinPair J
    e)))).injective he

/-- Every actual compatible pairing stored by this original word reverses parameters; same-direction gluings are excluded by literal signed-occurrence injectivity. -/
theorem originalCyclicBoundaryPairing_direction {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD)
    (pairing:(originalCyclicPresentation J e).presentation.BoundaryPairing) :
    pairing.direction=PolygonGluing.ParameterDirection.opposite := by
  cases hd:pairing.direction with
  | same =>
    have hc:pairing.target.dart=pairing.source.dart:=by
      simpa only [hd] using pairing.compatible
    exact False.elim (pairing.source_ne_target ((originalCyclicOccurrence_dart_injective J e hc).symm))
  | opposite => rfl

/-- The actual stored partner is exactly the original geometric finite-index involution, rather than an additional supplied pairing correspondence. -/
theorem originalCyclicBoundaryPairing_target_index {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} {hD:IsConvexFuchsianPolygon P D} (J:PolygonalCircle)
    (e:ZMod J.n≃OriginalRefinedSide hD)
    (pairing:(originalCyclicPresentation J e).presentation.BoundaryPairing) :
    originalCyclicOccurrenceIndex J e pairing.target=
      originalCyclicFinPair J e (originalCyclicOccurrenceIndex J e pairing.source) := by
  have hc:pairing.target.dart=pairing.source.dart.flip:=by
    simpa only [originalCyclicBoundaryPairing_direction J e pairing] using pairing.compatible
  let E:=Fintype.equivFin (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.InvolutionPositive
    (originalCyclicFinPair J e))
  have hm : SignedDart.mapEquiv E (originalCyclicDart J e (originalCyclicOccurrenceIndex J e pairing.target))=
      (SignedDart.mapEquiv E (originalCyclicDart J e (originalCyclicOccurrenceIndex J e pairing.source))).flip :=
    (originalCyclicOccurrenceIndex_dart J e pairing.target).symm.trans
      (hc.trans (congrArg SignedDart.flip (originalCyclicOccurrenceIndex_dart J e pairing.source)))
  have hh:originalCyclicDart J e (originalCyclicOccurrenceIndex J e pairing.target)=
      (originalCyclicDart J e (originalCyclicOccurrenceIndex J e pairing.source)).flip:=
    (SignedDart.mapEquiv E).injective
      (hm.trans (SignedDart.mapEquiv_flip E
        (originalCyclicDart J e (originalCyclicOccurrenceIndex J e pairing.source))).symm)
  apply (_root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.freeInvolutionDartEquiv (originalCyclicFinPair J
    e)
    (originalCyclicFinPair_involutive J e) (originalCyclicFinPair_ne_self J e)).injective
  exact hh.trans (originalCyclicDart_pair J e (originalCyclicOccurrenceIndex J e pairing.source)).symm
end LowDimensionalTopology.Geometry.Fuchsian
