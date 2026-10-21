/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicSideParameters
public import LowDimensionalTopology.Geometry.Polygon.Topology.PolygonCellSideCollision
public import LowDimensionalTopology.Geometry.Polygon.Topology.PolygonCellBoundaryCover
/-!
# Parameterizing the compact polygon boundary

The side intervals cover the refined boundary with exactly the standard
circle identifications. Their continuous descended map is bijective and
therefore gives a homeomorphism from the circle onto the full boundary.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped Complex.UnitDisc
set_option maxHeartbeats 600000


namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LeanEval.Topology.ClassificationOfSurfaces.Moise

/-- The literal disjoint family of all genuinely parameterized original sides, with its image in the whole actual original compact boundary. -/
def originalCyclicBoundaryCover {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (x:Σ _:Fin J.n,unitInterval) : ↥(⋃v:OriginalRefinedSide hD,v.carrier):=
  ⟨originalCyclicSideParam hD J hv e x.1 x.2,mem_iUnion.mpr
    ⟨e (originalCyclicFinIndex J x.1),
      (range_originalCyclicSideParam hD J hv e hs x.1) ▸ mem_range_self x.2⟩⟩

theorem continuous_originalCyclicBoundaryCover {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier) :
    Continuous (originalCyclicBoundaryCover hD J hv e hs) := by
  apply continuous_sigma_iff.mpr
  intro i
  exact (continuous_originalCyclicSideParam hD J hv e i).subtype_mk _

theorem originalCyclicBoundaryCover_surjective {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier) :
    Function.Surjective (originalCyclicBoundaryCover hD J hv e hs) := by
  rintro ⟨x,hx⟩
  obtain ⟨v,hv'⟩:=mem_iUnion.mp hx
  let i:Fin J.n:=(originalCyclicFinIndex J).symm (e.symm v)
  have hi:e (originalCyclicFinIndex J i)=v:=by simp only [i,Equiv.apply_symm_apply]
  have hx':x∈range (originalCyclicSideParam hD J hv e i):=by
    rw [range_originalCyclicSideParam hD J hv e hs i,hi]
    exact hv'
  obtain ⟨t,ht⟩:=hx'
  exact ⟨⟨i,t⟩,Subtype.ext ht⟩

/-- Equality in the actual compact boundary introduces no extra identifications of the genuine marked boundary circle. -/
theorem originalCyclicBoundaryCover_eq_implies_circle_eq
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (x y:Σ _:Fin J.n,unitInterval)
    (he:originalCyclicBoundaryCover hD J hv e hs x=originalCyclicBoundaryCover hD J hv e hs y) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover J.n x=_root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover J.n y := by
  rcases x with ⟨i,t⟩
  rcases y with ⟨j,u⟩
  have heq:originalCyclicSideParam hD J hv e i t=originalCyclicSideParam hD J hv e j u:=
    congrArg Subtype.val he
  by_cases hij : i=j
  · subst j
    have htu: t=u:=originalCyclicSideParam_injective hD J hv e i heq
    subst u
    rfl
  have hvij : e (originalCyclicFinIndex J i)≠e (originalCyclicFinIndex J j):=by
    intro h
    exact hij ((originalCyclicFinIndex J).injective (e.injective h))
  have hxi:originalCyclicSideParam hD J hv e i t∈(e (originalCyclicFinIndex J i)).carrier:=
    (range_originalCyclicSideParam hD J hv e hs i) ▸ mem_range_self t
  have hxj:originalCyclicSideParam hD J hv e i t∈(e (originalCyclicFinIndex J j)).carrier:=
    heq.symm ▸ ((range_originalCyclicSideParam hD J hv e hs j) ▸ mem_range_self u)
  have hends:=(e (originalCyclicFinIndex J i)).inter_subset_endpoints
    (e (originalCyclicFinIndex J j)) hvij
    (originalCyclicVertex hD J hv (originalCyclicFinIndex J i))
    (originalCyclicVertex hD J hv (originalCyclicFinIndex J i+1))
    (originalCyclicVertex hD J hv (originalCyclicFinIndex J j))
    (originalCyclicVertex hD J hv (originalCyclicFinIndex J j+1))
    (originalCyclicVertex_side_segment hD J hv e hs _).symm
    (originalCyclicVertex_side_segment hD J hv e hs _).symm ⟨hxi,hxj⟩
  have hg0 := originalCyclicSideParam_zero hD ha J hc hv e hs
  have hg1 := originalCyclicSideParam_one hD ha J hc hv e hs
  have ht : t=0∨t=1 := by
    rcases hends.1 with h|h
    · exact Or.inl (originalCyclicSideParam_injective hD J hv e i (h.trans (hg0 i).symm))
    · exact Or.inr (originalCyclicSideParam_injective hD J hv e i (h.trans (hg1 i).symm))
  have hu : u=0∨u=1 := by
    have huends:=heq ▸ hends.2
    rcases huends with h|h
    · exact Or.inl (originalCyclicSideParam_injective hD J hv e j (h.trans (hg0 j).symm))
    · exact Or.inr (originalCyclicSideParam_injective hD J hv e j (h.trans (hg1 j).symm))
  rcases ht with rfl|rfl <;> rcases hu with rfl|rfl
  · rw [hg0,hg0] at heq
    have hi : i=j := (originalCyclicFinIndex J).injective
      (originalCyclicVertex_injective hD J hv heq)
    subst j
    rfl
  · rw [hg0,hg1] at heq
    have hi : i=finRotate J.n j := by
      apply (originalCyclicFinIndex J).injective
      rw [originalCyclicFinIndex_rotate]
      exact originalCyclicVertex_injective hD J hv heq
    subst i
    exact (_root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover_endpoint_rotate j).symm
  · rw [hg1,hg0] at heq
    have hj : j=finRotate J.n i := by
      apply (originalCyclicFinIndex J).injective
      rw [originalCyclicFinIndex_rotate]
      exact (originalCyclicVertex_injective hD J hv heq).symm
    subst j
    exact _root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover_endpoint_rotate i
  · rw [hg1,hg1] at heq
    have hi : i=j := (originalCyclicFinIndex J).injective
      (add_right_cancel (originalCyclicVertex_injective hD J hv heq))
    subst j
    rfl

/-- Shared points of the standard circular arcs give precisely the same true original boundary point. -/
theorem originalCyclicBoundaryCover_eq_of_circle_eq
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (x y:Σ _:Fin J.n,unitInterval)
    (he:_root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover J.n
      x=_root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover J.n y) :
    originalCyclicBoundaryCover hD J hv e hs x=originalCyclicBoundaryCover hD J hv e hs y := by
  rcases x with ⟨i,t⟩
  rcases y with ⟨j,u⟩
  have he' : LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side i t=
      LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.side j u := by
    apply LeanEval.Topology.ClassificationOfSurfaces.PolygonCell.ext
    exact congrArg Subtype.val he
  rcases (_root_.LowDimensionalTopology.Geometry.Surfaces.PolygonCellCollision.side_eq_iff i j t u).mp he' with
    ⟨rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  · rfl
  · apply Subtype.ext
    change originalCyclicSideParam hD J hv e i 1=
      originalCyclicSideParam hD J hv e (finRotate J.n i) 0
    rw [originalCyclicSideParam_one hD ha J hc hv e hs,
      originalCyclicSideParam_zero hD ha J hc hv e hs,originalCyclicFinIndex_rotate]
  · apply Subtype.ext
    change originalCyclicSideParam hD J hv e (finRotate J.n j) 0=
      originalCyclicSideParam hD J hv e j 1
    rw [originalCyclicSideParam_one hD ha J hc hv e hs,
      originalCyclicSideParam_zero hD ha J hc hv e hs,originalCyclicFinIndex_rotate]

/-- The whole actual original boundary map descended from its genuine finitely many interval parameters. -/
def originalCyclicBoundaryMap {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (J:PolygonalCircle)
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (z:Circle) : ↥(⋃v:OriginalRefinedSide hD,v.carrier) :=
  originalCyclicBoundaryCover hD J hv e hs
    (Classical.choose (_root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover_surjective J.n (by have h:=J.three_le;omega) z))

theorem originalCyclicBoundaryMap_cover
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (x:Σ _:Fin J.n,unitInterval) :
    originalCyclicBoundaryMap hD J hv e hs (_root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover J.n
      x)=
      originalCyclicBoundaryCover hD J hv e hs x := by
  apply originalCyclicBoundaryCover_eq_of_circle_eq hD ha J hc hv e hs
  exact Classical.choose_spec (_root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover_surjective J.n (by have h:=J.three_le;omega)
    (_root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover J.n x))

theorem continuous_originalCyclicBoundaryMap
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier) :
    Continuous (originalCyclicBoundaryMap hD J hv e hs) := by
  apply (_root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover_isQuotientMap J.n (by have h:=J.three_le;omega)).continuous_iff.mpr
  have he : originalCyclicBoundaryMap hD J hv e hs ∘ _root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover J.n=
      originalCyclicBoundaryCover hD J hv e hs :=
    funext (originalCyclicBoundaryMap_cover hD ha J hc hv e hs)
  rw [he]
  exact continuous_originalCyclicBoundaryCover hD J hv e hs

theorem originalCyclicBoundaryMap_bijective
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier) :
    Function.Bijective (originalCyclicBoundaryMap hD J hv e hs) := by
  constructor
  · intro z w he
    obtain ⟨x,rfl⟩:=_root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover_surjective J.n (by have h:=J.three_le;omega) z
    obtain ⟨y,rfl⟩:=_root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover_surjective J.n (by have h:=J.three_le;omega) w
    rw [originalCyclicBoundaryMap_cover hD ha J hc hv e hs,
      originalCyclicBoundaryMap_cover hD ha J hc hv e hs] at he
    exact originalCyclicBoundaryCover_eq_implies_circle_eq hD ha J hc hv e hs x y he
  · intro z
    obtain ⟨x,hx⟩:=originalCyclicBoundaryCover_surjective hD J hv e hs z
    exact ⟨_root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover J.n x,(originalCyclicBoundaryMap_cover
      hD ha J hc hv e hs x).trans hx⟩

/-- The genuine whole compact original boundary is a true circle, with exactly the parameters required by its actual original side pairings. -/
def originalCyclicBoundaryHomeomorph
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier) :
    Circle≃ₜ↥(⋃v:OriginalRefinedSide hD,v.carrier) := by
  let :T2Space 𝕔𝔻:=Complex.UnitClosedDisc.isEmbedding_coe.t2Space
  let E:=Equiv.ofBijective _ (originalCyclicBoundaryMap_bijective hD ha J hc hv e hs)
  have hcont:=continuous_originalCyclicBoundaryMap hD ha J hc hv e hs
  exact E.toHomeomorphOfContinuousClosed hcont hcont.isClosedMap

theorem originalCyclicBoundaryHomeomorph_cover
    {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)
    (x:Σ _:Fin J.n,unitInterval) :
    originalCyclicBoundaryHomeomorph hD ha J hc hv e hs (_root_.LowDimensionalTopology.Geometry.Surfaces.polygonSideCircleCover J.n x)=
      originalCyclicBoundaryCover hD J hv e hs x :=
  originalCyclicBoundaryMap_cover hD ha J hc hv e hs x
end LowDimensionalTopology.Geometry.Fuchsian
