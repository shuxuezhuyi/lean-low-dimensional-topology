/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicOldCompletion
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalWordIdealPoints
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.FinitePunctureContinuousExtension
/-!
# The word realization and cusp completion

The completion map identifies its old and ideal parts exactly. The old-part
homeomorphism extends across the finite ideal sets using connected punctured
neighborhoods, giving the full homeomorphism and genus identity.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
open Set Filter Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LeanEval.Topology.ClassificationOfSurfaces.Moise
section IdealWordMap
variable {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D₀:FuchsianDisc H)
    {L:Set (geometricDiscData D₀).domain.carrier}
    (hL:IsConvexFuchsianPolygon (geometricDiscData D₀) L) (ha:(geometricDiscData D₀).area L≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hL,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hL)
    (e:ZMod J.n≃OriginalRefinedSide hL) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    {n:ℕ} (S:_root_.LowDimensionalTopology.Geometry.Polygon.CyclicDiscPolygonSupportData n)
    (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein (geometricDiscData D₀) L)
    (hpar:∀u:Circle,(u:ℂ)∈fuchsianPolygonIdealBoundary (geometricDiscData D₀) L→
      ∃f:geometricDiscGroup D₀,f≠1∧_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val∧
        f.val.val ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))

/-- The actual old quotient consists precisely of original points strictly inside the closed disc model. -/
theorem originalCyclicPreCompletionMap_old_iff_norm
    (a:(originalCyclicPresentation J e).presentation.PolygonalPreRealization) :
    originalCyclicPreCompletionMap D₀ hL ha J hc hv e hs S hr hpar a∈
        range (fuchsianCuspCompletionOld D₀)↔
      ‖((originalCyclicPreClosedModelHomeomorph hL ha J hc hv e hs a).val:ℂ)‖<1 := by
  rw [originalCyclicPreCompletionMap_mem_old_iff]
  let P:=geometricDiscData D₀
  let B:=originalCyclicPreClosedModelHomeomorph hL ha J hc hv e hs
  constructor
  · rintro ⟨x,rfl⟩
    rw [originalFinitePrePoint_coe]
    exact (P.finiteCoordinate x.val).norm_lt_one
  · intro hn
    let x:P.domain.carrier:=P.finiteCoordinate.symm (Complex.UnitDisc.mk ((B a).val:ℂ) hn)
    have hB:(B a).val=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel (P.finiteCoordinate x):=by
      apply Subtype.ext
      change ((B a).val:ℂ)=(P.finiteCoordinate x:ℂ)
      simp only [x,P.finiteCoordinate.apply_symm_apply,Complex.UnitDisc.coe_mk]
    have hx:x∈closure L:=(originalFiniteClosedModel_mem_iff x).mp (hB ▸ (B a).property)
    refine ⟨⟨x,hx⟩,B.injective (Subtype.ext ?_)⟩
    exact hB.trans (originalFinitePrePoint_coe hL ha J hc hv e hs ⟨x,hx⟩).symm

/-- Exactly the actual original ideal face points map into the added cusp part of the unique completion. -/
theorem originalCyclicPreCompletionMap_not_old_iff_ideal
    (a:(originalCyclicPresentation J e).presentation.PolygonalPreRealization) :
    originalCyclicPreCompletionMap D₀ hL ha J hc hv e hs S hr hpar a∉
        range (fuchsianCuspCompletionOld D₀)↔
      a∈originalCyclicPreIdealPoints hL ha J hc hv e hs := by
  rw [originalCyclicPreCompletionMap_old_iff_norm]
  exact ⟨fun h=>le_antisymm
    (originalCyclicPreClosedModelHomeomorph hL ha J hc hv e hs a).val.norm_le_one (not_lt.mp h),
    fun h=>not_lt.mpr h.ge⟩
/-- The inverse image of the actual added cusp part consists exactly of the literal ideal word points. -/
theorem originalCyclicCompletionMap_preimage_new :
    (originalCyclicCompletionMap D₀ hL ha J hc hv e hs S hr hpar) ⁻¹'
      (range (fuchsianCuspCompletionOld D₀))ᶜ=
      originalCyclicWordIdealPoints hL ha J hc hv e hs := by
  ext x
  induction x using Quotient.inductionOn with
  | h a=>
      constructor
      · intro hx
        exact ⟨a,(originalCyclicPreCompletionMap_not_old_iff_ideal D₀ hL ha J hc hv e hs S hr hpar a).mp hx,rfl⟩
      · rintro ⟨b,hb,he⟩
        have hh:originalCyclicCompletionMap D₀ hL ha J hc hv e hs S hr hpar
            ((originalCyclicPresentation J e).presentation.polygonalMk (originalCyclicPresentation J e).valid b)∉
            range (fuchsianCuspCompletionOld D₀):=
          (originalCyclicPreCompletionMap_not_old_iff_ideal D₀ hL ha J hc hv e hs S hr hpar b).mpr hb
        rwa [he] at hh

/-- The actual continuous finite-area original side-word map is a homeomorphism onto the unique original cusp completion. Actual ideal fibers are identified using connected punctured neighborhoods of the genuine target surface. -/
theorem originalCyclicCompletionMap_isHomeomorph :
    IsHomeomorph (originalCyclicCompletionMap D₀ hL ha J hc hv e hs S hr hpar) := by
  let W:=(originalCyclicPresentation J e).presentation.PolygonalRealization (originalCyclicPresentation J e).valid
  let F:W→FuchsianCuspCompletion D₀:=originalCyclicCompletionMap D₀ hL ha J hc hv e hs S hr hpar
  let Q:=(originalCyclicPresentation J e).presentation.polygonalMk (originalCyclicPresentation J e).valid
  let A:=originalCyclicWordIdealPoints hL ha J hc hv e hs
  let B:Set (FuchsianCuspCompletion D₀):=(range (fuchsianCuspCompletionOld D₀))ᶜ
  let O:=range (fuchsianCuspCompletionOld D₀)
  let:=originalCyclicPresentation_t2Space J e
  let:=originalCyclicPresentation_compactSpace J e
  let:Nonempty W:=⟨Q ((originalCyclicPreFaceHomeomorph J e).symm ⟨0,by simp⟩)⟩
  let R:=fuchsianCuspCompletionRiemannSurface D₀
  let:=R.t2Space
  let:=R.toRiemannAtlas.toChartedSpace
  have :LocallyCompactSpace (FuchsianCuspCompletion D₀):=
    ChartedSpace.locallyCompactSpace ℂ (FuchsianCuspCompletion D₀)
  have hF:Continuous F:=continuous_originalCyclicCompletionMap D₀ hL ha J hc hv e hs S hr hpar
  have hsur:Function.Surjective F:=originalCyclicCompletionMap_surjective D₀ hL ha J hc hv e hs S hr hpar
  have hA:A.Finite:=originalCyclicWordIdealPoints_finite hL ha J hc hv e hs
  have hPre:F ⁻¹' B=A:=originalCyclicCompletionMap_preimage_new D₀ hL ha J hc hv e hs S hr hpar
  have hNew:∀x∈A,F x∈B:=by
    intro x hx
    have hh:x∈F ⁻¹' B:=hPre.symm ▸ hx
    exact hh
  have hB:B.Finite:=(hA.image F).subset (by
    intro y hy
    obtain ⟨x,rfl⟩:=hsur y
    exact ⟨x,hPre ▸ hy,rfl⟩)
  have hDenseA:Dense (Aᶜ):=by
    intro x
    obtain ⟨a,rfl⟩:=(isQuotientMap_polygonalMk
      (originalCyclicPresentation J e).presentation (originalCyclicPresentation J e).valid).surjective x
    have hsub:Q '' (originalCyclicPreIdealPoints hL ha J hc hv e hs)ᶜ⊆Aᶜ:=by
      rintro _ ⟨b,hb,rfl⟩ hba
      have hnew:=hNew (Q b) hba
      exact hb ((originalCyclicPreCompletionMap_not_old_iff_ideal D₀ hL ha J hc hv e hs S hr hpar b).mp hnew)
    apply closure_mono hsub
    exact image_closure_subset_closure_image
      (continuous_polygonalMk (originalCyclicPresentation J e).presentation (originalCyclicPresentation J e).valid)
      ⟨a,originalCyclicPreIdealPoints_compl_dense hL ha J hc hv e hs a,rfl⟩
  have hOld:∀x∈Aᶜ,F x∈Bᶜ:=by
    intro x hx hFx
    exact hx (hPre ▸ hFx)
  have hDenseB:Dense Bᶜ:=by
    intro y
    obtain ⟨x,rfl⟩:=hsur y
    apply closure_mono (show F '' Aᶜ⊆Bᶜ from by rintro _ ⟨z,hz,rfl⟩;exact hOld z hz)
    exact image_closure_subset_closure_image hF ⟨x,hDenseA x,rfl⟩
  have hAo:Aᶜ=F ⁻¹' O:=by
    rw [←hPre,←preimage_compl]
    exact congrArg (preimage F) (compl_compl O)
  have hBo:O=Bᶜ:=(compl_compl O).symm
  let E:↥(Aᶜ)≃ₜ↥(Bᶜ):=(Homeomorph.setCongr hAo).trans
    ((originalCyclicCompletionOldHomeomorph D₀ hL ha J hc hv e hs S hr hpar).trans
      (Homeomorph.setCongr hBo))
  have hE:∀x:↥(Aᶜ),F x=(E x).val:=by intro x;rfl
  apply _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.finite_puncture_continuous_map_isHomeomorph A hA B hB hDenseB E F hE hF hNew
    (_root_.LowDimensionalTopology.Geometry.Surfaces.chartedComplex_connectedPuncturedNeighborhoods
      (FuchsianCuspCompletion D₀))
  intro a _ha
  have:NeBot (𝓝[Aᶜ] a):=mem_closure_iff_nhdsWithin_neBot.mp (hDenseA a)
  exact (hF.continuousAt.mono_left nhdsWithin_le_nhds).mapClusterPt

/-- The genuine homeomorphism from the unchanged original pairing-word realization onto the single actual all-cusp completion. -/
def originalCyclicCompletionHomeomorph :
    (originalCyclicPresentation J e).presentation.PolygonalRealization
      (originalCyclicPresentation J e).valid≃ₜFuchsianCuspCompletion D₀ :=
  (Equiv.ofBijective (originalCyclicCompletionMap D₀ hL ha J hc hv e hs S hr hpar)
    (originalCyclicCompletionMap_isHomeomorph D₀ hL ha J hc hv e hs S hr hpar).bijective).toHomeomorphOfContinuousClosed
      (continuous_originalCyclicCompletionMap D₀ hL ha J hc hv e hs S hr hpar)
      (originalCyclicCompletionMap_isHomeomorph D₀ hL ha J hc hv e hs S hr hpar).isClosedMap

include ha hc hv hs S hr hpar in
/-- The actual original completion has the same genuine topological genus and literal Euler characteristic as the unchanged original side word. -/
theorem originalCyclicCompletion_genus_euler :
    ∃g,_root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus (FuchsianCuspCompletion D₀) g∧
      _root_.LowDimensionalTopology.Geometry.Surfaces.CyclicSurface.eulerCharacteristic (originalCyclicPresentation J e).presentation=2-2*(g:ℤ) := by
  obtain ⟨g,⟨G⟩,hχ⟩:=originalCyclicPresentation_genus J e
  exact ⟨g,⟨(originalCyclicCompletionHomeomorph D₀ hL ha J hc hv e hs S hr hpar).symm.trans G⟩,hχ⟩

end IdealWordMap
end LowDimensionalTopology.Geometry.Fuchsian
