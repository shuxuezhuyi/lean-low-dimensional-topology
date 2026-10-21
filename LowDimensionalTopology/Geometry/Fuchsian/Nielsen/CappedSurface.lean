module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.FiniteHull
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.Separation
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.BoundaryCensusArea
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Analysis.Convex.Combination
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalCuspOldPoints
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicPreCompletion
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalFinitePointWordGluing
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.CuspConjugacyPaths
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.FinitePunctureContinuousExtension
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalWordIdealPoints
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Data.Set.UnionLift
public import Mathlib.Topology.Homeomorph.Defs
/-!
# Geometric realization of the capped Nielsen surface

Compatible side parameters realize the cyclic Nielsen presentation as a
compact surface. The construction relates its original face and cap boundary
circles to the cusp completion of the Fuchsian quotient.

The completed Nielsen core embeds in this surface, with each boundary cycle
represented by its cap clock. The final area identity uses the genus of this
geometrically constructed surface.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter MeasureTheory
open scoped UpperHalfPlane Complex.UnitDisc OnePoint RealInnerProductSpace Pointwise


namespace LowDimensionalTopology.Geometry.Fuchsian
attribute [local instance] nielsenInteriorSphereMeasurableSpace nielsenInteriorSphereBorelSpace

section NielsenCyclicSideParameters
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "index" => originalCyclicFinIndex J
local notation "pairIndex" => nielsenCyclicPairIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "tag" => nielsenCyclicSideTag hD hNE hFG hfin w hwD hwN J hc hv
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv
local notation "edge" => nielsenCyclicEdge hD hNE hFG J hv

def nielsenCyclicFinPair (i:Fin J.n) : Fin J.n := (index).symm (pairIndex ((index) i))
local notation "finPair" => nielsenCyclicFinPair hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCyclicFinPair_index (i:Fin J.n) : (index) ((finPair) i)=pairIndex ((index) i) :=
  (index).apply_symm_apply _

theorem nielsenCyclicFinPair_involutive : Function.Involutive (finPair) := by
  intro i
  apply (index).injective
  rw [nielsenCyclicFinPair_index,nielsenCyclicFinPair_index,nielsenCyclicPairIndex_involutive]

def nielsenCyclicEdgeAction (i:Fin J.n) : 𝕔𝔻≃ₜ𝕔𝔻 :=
  match tag ((index) i) with
  | Sum.inl v => (P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap
  | Sum.inr _ => Homeomorph.refl _
local notation "edgeAction" => nielsenCyclicEdgeAction hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCyclicEdgeAction_pair_apply (i:Fin J.n) (x:𝕔𝔻) :
    edgeAction ((finPair) i) (edgeAction i x)=x := by
  cases hi:tag ((index) i) with
  | inl v =>
    have hpair:=(nielsenCyclicPairIndex_paired hD hNE hFG hfin w hwD hwN J hc hv ((index) i) v hi).2.1
    have hp:tag ((index) ((finPair) i))=Sum.inl v.pair:=by rw [nielsenCyclicFinPair_index];exact hpair
    simp only [nielsenCyclicEdgeAction,hi,hp]
    have he:fuchsianSideElement hD v.pair.val.val.1=(fuchsianSideElement hD v.val.val.1)⁻¹:=v.val.pair_element
    rw [he,inv_inv]
    rw [←nielsen_compactifiedAction_mul,mul_inv_cancel,nielsen_compactifiedAction_one]
  | inr v =>
    have hp:(finPair) i=i:=by
      apply (index).injective
      rw [nielsenCyclicFinPair_index]
      exact nielsenCyclicPairIndex_unpaired hD hNE hFG hfin w hwD hwN J hc hv ((index) i) v hi
    simp only [hp,nielsenCyclicEdgeAction,hi,Homeomorph.refl_apply,id_eq]

theorem nielsenCyclicEdgeAction_image (i:Fin J.n) :
    edgeAction i '' edge ((index) i)=edge ((index) ((finPair) i)) := by
  cases hi:tag ((index) i) with
  | inl v =>
    simpa only [nielsenCyclicEdgeAction,hi,nielsenCyclicFinPair_index] using
      (nielsenCyclicPairIndex_paired hD hNE hFG hfin w hwD hwN J hc hv ((index) i) v hi).2.2
  | inr v =>
    have hp:=nielsenCyclicPairIndex_unpaired hD hNE hFG hfin w hwD hwN J hc hv ((index) i) v hi
    simp only [nielsenCyclicEdgeAction,hi,nielsenCyclicFinPair_index,hp,Homeomorph.refl_apply,id_eq,Set.image_id']

def nielsenCyclicSideBaseParam (i:Fin J.n) (t:unitInterval) : 𝕔𝔻 :=
  Hyperbolic.closedModelSegmentParam (vertex ((index) i)) (vertex ((index) i+1)) t
local notation "baseParam" => nielsenCyclicSideBaseParam hD hNE hFG J hv

def nielsenCyclicSideParam (i:Fin J.n) (t:unitInterval) : 𝕔𝔻 :=
  if i≤(finPair) i then baseParam i t
  else edgeAction ((finPair) i) (baseParam ((finPair) i) (unitInterval.symm t))
local notation "sideParam" => nielsenCyclicSideParam hD hNE hFG hfin w hwD hwN J hc hv

/-- The actual partial pairing maps real side parameters to exactly their reverse partner parameters. -/
theorem nielsenCyclicSideParam_pair (i:Fin J.n) (hi:(finPair) i≠i) (t:unitInterval) :
    edgeAction i (sideParam i t)=sideParam ((finPair) i) (unitInterval.symm t) := by
  have hpp:=nielsenCyclicFinPair_involutive hD hNE hFG hfin w hwD hwN J hc hv i
  by_cases hle:i≤(finPair) i
  · have hp:¬((finPair) i≤ i):=not_le.mpr (lt_of_le_of_ne hle (Ne.symm hi))
    simp only [nielsenCyclicSideParam,hpp,ite_eq_left hle,ite_eq_right hp,unitInterval.symm_symm]
  · have hp:(finPair) i≤ i:=(lt_of_not_ge hle).le
    simp only [nielsenCyclicSideParam,hpp,ite_eq_right hle,ite_eq_left hp]
    simpa only [hpp] using nielsenCyclicEdgeAction_pair_apply hD hNE hFG hfin w hwD hwN J hc hv
      ((finPair) i) (baseParam ((finPair) i) (unitInterval.symm t))

theorem continuous_nielsenCyclicSideBaseParam (i:Fin J.n) : Continuous (baseParam i) :=
  Hyperbolic.continuous_closedModelSegmentParam _ _

theorem nielsenCyclicSideBaseParam_injective (i:Fin J.n) : Function.Injective (baseParam i) :=
  Hyperbolic.closedModelSegmentParam_injective _ _ (nielsenCyclicVertex_adjacent_ne hD hNE hFG J hv ((index) i))

theorem continuous_nielsenCyclicSideParam (i:Fin J.n) : Continuous (sideParam i) := by
  unfold nielsenCyclicSideParam
  split_ifs
  · exact continuous_nielsenCyclicSideBaseParam hD hNE hFG J hv i
  · exact (edgeAction ((finPair) i)).continuous.comp
      ((continuous_nielsenCyclicSideBaseParam hD hNE hFG J hv _).comp unitInterval.continuous_symm)

theorem nielsenCyclicSideParam_injective (i:Fin J.n) : Function.Injective (sideParam i) := by
  unfold nielsenCyclicSideParam
  split_ifs
  · exact nielsenCyclicSideBaseParam_injective hD hNE hFG J hv i
  · exact (edgeAction ((finPair) i)).injective.comp
      ((nielsenCyclicSideBaseParam_injective hD hNE hFG J hv _).comp unitInterval.symm_bijective.injective)



theorem nielsenCyclicFinPair_nonfixed_tag (i:Fin J.n) (hi:(finPair) i≠i) :
    ∃v:NielsenRefinedSide hD hNE,tag ((index) i)=Sum.inl v := by
  cases ht:tag ((index) i) with
  | inl v => exact ⟨v,rfl⟩
  | inr v =>
    have hp:=nielsenCyclicPairIndex_unpaired hD hNE hFG hfin w hwD hwN J hc hv ((index) i) v ht
    exact False.elim (hi ((index).injective ((nielsenCyclicFinPair_index hD hNE hFG hfin w hwD hwN J hc hv i).trans
      hp)))

theorem nielsenCyclicEdgeAction_endpoint_reverse (i:Fin J.n) (hi:(finPair) i≠i) :
    edgeAction i (vertex ((index) i))=vertex ((index) ((finPair) i)+1) ∧
      edgeAction i (vertex ((index) i+1))=vertex ((index) ((finPair) i)) := by
  obtain ⟨v,hv'⟩:=nielsenCyclicFinPair_nonfixed_tag hD hNE hFG hfin w hwD hwN J hc hv i hi
  simpa only [nielsenCyclicEdgeAction,hv',nielsenCyclicFinPair_index] using
    nielsenCyclicPairIndex_endpoint_reverse hD hNE hFG hfin w hwD hwN J hc hv ((index) i) v hv'

theorem nielsenCyclicSideParam_zero (i:Fin J.n) : sideParam i 0=vertex ((index) i) := by
  by_cases hi:i≤(finPair) i
  · simp only [nielsenCyclicSideParam,ite_eq_left hi,nielsenCyclicSideBaseParam,Hyperbolic.closedModelSegmentParam_zero]
  · have hp:(finPair) ((finPair) i)=i:=nielsenCyclicFinPair_involutive hD hNE hFG hfin w hwD hwN J hc hv i
    have hn:(finPair) ((finPair) i)≠(finPair) i:=by rw [hp];exact (lt_of_not_ge hi).ne.symm
    simp only [nielsenCyclicSideParam,ite_eq_right
      hi,nielsenCyclicSideBaseParam,unitInterval.symm_zero,Hyperbolic.closedModelSegmentParam_one]
    have hr:=(nielsenCyclicEdgeAction_endpoint_reverse hD hNE hFG hfin w hwD hwN J hc hv ((finPair) i) hn).2
    rwa [hp] at hr

theorem nielsenCyclicSideParam_one (i:Fin J.n) : sideParam i 1=vertex ((index) i+1) := by
  by_cases hi:i≤(finPair) i
  · simp only [nielsenCyclicSideParam,ite_eq_left hi,nielsenCyclicSideBaseParam,Hyperbolic.closedModelSegmentParam_one]
  · have hp:(finPair) ((finPair) i)=i:=nielsenCyclicFinPair_involutive hD hNE hFG hfin w hwD hwN J hc hv i
    have hn:(finPair) ((finPair) i)≠(finPair) i:=by rw [hp];exact (lt_of_not_ge hi).ne.symm
    simp only [nielsenCyclicSideParam,ite_eq_right
      hi,nielsenCyclicSideBaseParam,unitInterval.symm_one,Hyperbolic.closedModelSegmentParam_zero]
    have hr:=(nielsenCyclicEdgeAction_endpoint_reverse hD hNE hFG hfin w hwD hwN J hc hv ((finPair) i) hn).1
    rwa [hp] at hr

theorem range_nielsenCyclicSideBaseParam (i:Fin J.n) : range (baseParam i)=edge ((index) i) :=
  Hyperbolic.range_closedModelSegmentParam _ _

theorem range_nielsenCyclicSideParam (i:Fin J.n) : range (sideParam i)=edge ((index) i) := by
  unfold nielsenCyclicSideParam
  split_ifs
  · exact range_nielsenCyclicSideBaseParam hD hNE hFG J hv i
  · change range (edgeAction ((finPair) i) ∘ baseParam ((finPair) i) ∘ unitInterval.symm)=_
    rw [Set.range_comp,Set.range_comp,unitInterval.symm_bijective.surjective.range_eq,image_univ,
      range_nielsenCyclicSideBaseParam,nielsenCyclicEdgeAction_image,nielsenCyclicFinPair_involutive]

end NielsenCyclicSideParameters



section NielsenCyclicBoundaryParameters
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open LeanEval.Topology.ClassificationOfSurfaces
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Q" => nielsenCyclicDiscPolygon hD hNE hFG hfin w hwD hwN J hc hv
local notation "γ" => nielsenCyclicSideParam hD hNE hFG hfin w hwD hwN J hc hv
local notation "index" => originalCyclicFinIndex J
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv

theorem range_nielsenCyclicSideParam_discEdge (i:Fin J.n) :
    range ((γ) i)=Polygon.discPolygonEdge (Q).vertices i := by
  rw [range_nielsenCyclicSideParam]
  change Hyperbolic.closedModelDiscHSegment (vertex ((index) i)) (vertex ((index) i+1))=
    Hyperbolic.closedModelDiscHSegment (vertex ((index) i)) (vertex ((index) (finRotate J.n i)))
  rw [originalCyclicFinIndex_rotate]

def nielsenCyclicBoundaryCover (x:Σ _:Fin J.n,unitInterval) : ↥(Q).boundary :=
  ⟨(γ) x.1 x.2,mem_iUnion.mpr ⟨x.1,
    (range_nielsenCyclicSideParam_discEdge hD hNE hFG hfin w hwD hwN J hc hv x.1) ▸ mem_range_self x.2⟩⟩
local notation "cover" => nielsenCyclicBoundaryCover hD hNE hFG hfin w hwD hwN J hc hv

theorem continuous_nielsenCyclicBoundaryCover : Continuous (cover) := by
  apply continuous_sigma_iff.mpr
  intro i
  exact (continuous_nielsenCyclicSideParam hD hNE hFG hfin w hwD hwN J hc hv i).subtype_mk _

theorem nielsenCyclicBoundaryCover_surjective : Function.Surjective (cover) := by
  rintro ⟨x,hx⟩
  obtain ⟨i,hi⟩:=mem_iUnion.mp hx
  rw [←range_nielsenCyclicSideParam_discEdge hD hNE hFG hfin w hwD hwN J hc hv i] at hi
  obtain ⟨t,ht⟩:=hi
  exact ⟨⟨i,t⟩,Subtype.ext ht⟩

theorem nielsenCyclicBoundaryCover_eq_implies_circle_eq
    (x y:Σ _:Fin J.n,unitInterval) (he:(cover) x=(cover) y) :
    Surfaces.polygonSideCircleCover J.n x=Surfaces.polygonSideCircleCover J.n y := by
  rcases x with ⟨i,t⟩
  rcases y with ⟨j,u⟩
  have heq:(γ) i t=(γ) j u:=congrArg Subtype.val he
  by_cases hij:i=j
  · subst j
    have htu:=nielsenCyclicSideParam_injective hD hNE hFG hfin w hwD hwN J hc hv i heq
    subst u
    rfl
  have hi:(γ) i t∈Polygon.discPolygonEdge (Q).vertices i:=
    (range_nielsenCyclicSideParam_discEdge hD hNE hFG hfin w hwD hwN J hc hv i) ▸ mem_range_self t
  have hj:(γ) i t∈Polygon.discPolygonEdge (Q).vertices j:=heq.symm ▸
    ((range_nielsenCyclicSideParam_discEdge hD hNE hFG hfin w hwD hwN J hc hv j) ▸ mem_range_self u)
  have hends:=(Q).simple_edges i j hij ⟨hi,hj⟩
  have hz:=nielsenCyclicSideParam_zero hD hNE hFG hfin w hwD hwN J hc hv
  have ho:=nielsenCyclicSideParam_one hD hNE hFG hfin w hwD hwN J hc hv
  have ht:t=0∨t=1:=by
    rcases hends.1 with h|h
    · exact Or.inl (nielsenCyclicSideParam_injective hD hNE hFG hfin w hwD hwN J hc hv i (h.trans (hz i).symm))
    · have h':(γ) i t=vertex ((index) i+1):=by simpa only [nielsenCyclicDiscPolygon,nielsenCyclicNativeVertices,originalCyclicFinIndex_rotate,Set.mem_singleton_iff] using h
      exact Or.inr (nielsenCyclicSideParam_injective hD hNE hFG hfin w hwD hwN J hc hv i (h'.trans (ho i).symm))
  have hu:u=0∨u=1:=by
    have hends':=heq ▸ hends.2
    rcases hends' with h|h
    · exact Or.inl (nielsenCyclicSideParam_injective hD hNE hFG hfin w hwD hwN J hc hv j (h.trans (hz j).symm))
    · have h':(γ) j u=vertex ((index) j+1):=by simpa only [nielsenCyclicDiscPolygon,nielsenCyclicNativeVertices,originalCyclicFinIndex_rotate,Set.mem_singleton_iff] using h
      exact Or.inr (nielsenCyclicSideParam_injective hD hNE hFG hfin w hwD hwN J hc hv j (h'.trans (ho j).symm))
  rcases ht with rfl|rfl <;> rcases hu with rfl|rfl
  · rw [hz,hz] at heq
    have hji:i=j:=(index).injective (nielsenCyclicVertex_injective hD hNE hFG J hv heq)
    subst j
    rfl
  · rw [hz,ho] at heq
    have hir:i=finRotate J.n j:=by
      apply (index).injective
      rw [originalCyclicFinIndex_rotate]
      exact nielsenCyclicVertex_injective hD hNE hFG J hv heq
    subst i
    exact (Surfaces.polygonSideCircleCover_endpoint_rotate j).symm
  · rw [ho,hz] at heq
    have hjr:j=finRotate J.n i:=by
      apply (index).injective
      rw [originalCyclicFinIndex_rotate]
      exact (nielsenCyclicVertex_injective hD hNE hFG J hv heq).symm
    subst j
    exact Surfaces.polygonSideCircleCover_endpoint_rotate i
  · rw [ho,ho] at heq
    have hji:i=j:=(index).injective (add_right_cancel (nielsenCyclicVertex_injective hD hNE hFG J hv heq))
    subst j
    rfl

theorem nielsenCyclicBoundaryCover_eq_of_circle_eq
    (x y:Σ _:Fin J.n,unitInterval) (he:Surfaces.polygonSideCircleCover J.n x=Surfaces.polygonSideCircleCover J.n y) :
    (cover) x=(cover) y := by
  rcases x with ⟨i,t⟩
  rcases y with ⟨j,u⟩
  have he':PolygonCell.side i t=PolygonCell.side j u:=by
    apply PolygonCell.ext
    exact congrArg Subtype.val he
  rcases (Surfaces.PolygonCellCollision.side_eq_iff i j t u).mp he' with
    ⟨rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  · rfl
  · apply Subtype.ext
    change (γ) i 1=(γ) (finRotate J.n i) 0
    rw [nielsenCyclicSideParam_one,nielsenCyclicSideParam_zero,originalCyclicFinIndex_rotate]
  · apply Subtype.ext
    change (γ) (finRotate J.n j) 0=(γ) j 1
    rw [nielsenCyclicSideParam_one,nielsenCyclicSideParam_zero,originalCyclicFinIndex_rotate]

def nielsenCyclicBoundaryMap (z:Circle) : ↥(Q).boundary :=
  (cover) (Classical.choose (Surfaces.polygonSideCircleCover_surjective J.n (by have h:=J.three_le;omega) z))
local notation "boundaryMap" => nielsenCyclicBoundaryMap hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCyclicBoundaryMap_cover (x:Σ _:Fin J.n,unitInterval) :
    (boundaryMap) (Surfaces.polygonSideCircleCover J.n x)=(cover) x := by
  apply nielsenCyclicBoundaryCover_eq_of_circle_eq hD hNE hFG hfin w hwD hwN J hc hv
  exact Classical.choose_spec (Surfaces.polygonSideCircleCover_surjective J.n (by have h:=J.three_le;omega)
    (Surfaces.polygonSideCircleCover J.n x))

theorem continuous_nielsenCyclicBoundaryMap : Continuous (boundaryMap) := by
  apply (Surfaces.polygonSideCircleCover_isQuotientMap J.n (by have h:=J.three_le;omega)).continuous_iff.mpr
  have he:(boundaryMap) ∘ Surfaces.polygonSideCircleCover J.n=(cover):=
    funext (nielsenCyclicBoundaryMap_cover hD hNE hFG hfin w hwD hwN J hc hv)
  rw [he]
  exact continuous_nielsenCyclicBoundaryCover hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCyclicBoundaryMap_bijective : Function.Bijective (boundaryMap) := by
  constructor
  · intro z v he
    obtain ⟨x,rfl⟩:=Surfaces.polygonSideCircleCover_surjective J.n (by have h:=J.three_le;omega) z
    obtain ⟨y,rfl⟩:=Surfaces.polygonSideCircleCover_surjective J.n (by have h:=J.three_le;omega) v
    rw [nielsenCyclicBoundaryMap_cover,nielsenCyclicBoundaryMap_cover] at he
    exact nielsenCyclicBoundaryCover_eq_implies_circle_eq hD hNE hFG hfin w hwD hwN J hc hv x y he
  · intro x
    obtain ⟨y,rfl⟩:=nielsenCyclicBoundaryCover_surjective hD hNE hFG hfin w hwD hwN J hc hv x
    exact ⟨Surfaces.polygonSideCircleCover J.n y,nielsenCyclicBoundaryMap_cover hD hNE hFG hfin w hwD hwN J hc hv y⟩

/-- The actual original partial-pairing parameters give a homeomorphism onto the true clipped first-face boundary. -/
def nielsenCyclicBoundaryHomeomorph : Circle≃ₜ↥(Q).boundary := by
  let :T2Space 𝕔𝔻:=Complex.UnitClosedDisc.isEmbedding_coe.t2Space
  let E:=Equiv.ofBijective (boundaryMap) (nielsenCyclicBoundaryMap_bijective hD hNE hFG hfin w hwD hwN J hc hv)
  have hcont:=continuous_nielsenCyclicBoundaryMap hD hNE hFG hfin w hwD hwN J hc hv
  exact E.toHomeomorphOfContinuousClosed hcont hcont.isClosedMap

theorem nielsenCyclicBoundaryHomeomorph_cover (x:Σ _:Fin J.n,unitInterval) :
    nielsenCyclicBoundaryHomeomorph hD hNE hFG hfin w hwD hwN J hc hv (Surfaces.polygonSideCircleCover J.n
      x)=(cover) x :=
  nielsenCyclicBoundaryMap_cover hD hNE hFG hfin w hwD hwN J hc hv x

end NielsenCyclicBoundaryParameters



section NielsenCyclicFaceExtension
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open LeanEval.Topology.ClassificationOfSurfaces
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Q" => nielsenCyclicDiscPolygon hD hNE hFG hfin w hwD hwN J hc hv
local notation "γ" => nielsenCyclicSideParam hD hNE hFG hfin w hwD hwN J hc hv
local notation "K" => fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE)

def nielsenCorePolygonGaugeData (w₀:P.domain.carrier) (hwD₀:w₀∈D) (hwN₀:w₀∈fuchsianNielsenCore P hNE) :
    {f:ℂ≃ₜℂ // f '' interior K=Metric.ball 0 1 ∧
      f '' K=Metric.closedBall 0 1 ∧f '' frontier K=Metric.sphere 0 1} := by
  have hex:∃f:ℂ≃ₜℂ,f '' interior K=Metric.ball 0 1 ∧
      f '' K=Metric.closedBall 0 1 ∧f '' frontier K=Metric.sphere 0 1:=by
    have hconv:Convex ℝ (P.kleinCoordinate '' (D∩fuchsianNielsenCore P hNE)):=by
      have h:=(Hyperbolic.discHConvex_iff_klein_convex _).mp (nielsenCore_inter_native_convex hD hNE)
      simpa only [image_image,UnitDiscFuchsianGroup.kleinCoordinate] using h
    have hint:(interior K).Nonempty:=by
      rw [nielsenCore_klein_interior hD hNE w₀ hwD₀ hwN₀]
      exact ⟨P.kleinCoordinate w₀,w₀,⟨hwD₀,hwN₀⟩,rfl⟩
    obtain ⟨f,hi,hcl,hfront⟩:=exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      hconv.closure hint (fuchsianPolygonCompactKlein_compact P (D∩fuchsianNielsenCore P hNE)).isBounded
    refine ⟨f,hi,?_,hfront⟩
    change f '' closure (P.kleinCoordinate '' (D∩fuchsianNielsenCore P hNE))=_
    simpa only [closure_closure] using hcl
  exact ⟨Classical.choose hex,Classical.choose_spec hex⟩
local notation "gauge" => nielsenCorePolygonGaugeData hD hNE w hwD hwN

def nielsenCyclicBoundaryKleinHomeomorph : ↥(Q).boundary≃ₜ↥(frontier K) :=
  (Hyperbolic.isClosedEmbedding_closedKleinCoordinate.isEmbedding.homeomorphImage (Q).boundary).trans
    (Homeomorph.setCongr (nielsenCyclicNativeVertices_boundary_klein hD hNE hFG hfin w hwD hwN J hc hv))

def nielsenCoreGaugeCellHomeomorph (n:ℕ) : PolygonCell n≃ₜ↥K :=
  (PolygonCell.closedUnitDiscHomeomorph n).trans
    ((((gauge).val.image K).trans (Homeomorph.setCongr (gauge).property.2.1)).symm)

theorem nielsenCoreGaugeCellHomeomorph_coe (n:ℕ) (x:PolygonCell n) :
    (nielsenCoreGaugeCellHomeomorph hD hNE w hwD hwN n x:ℂ)=(gauge).val.symm (x:ℂ) := rfl

def nielsenCyclicGaugeBoundaryHomeomorph : Circle≃ₜCircle :=
  ((nielsenCyclicBoundaryHomeomorph hD hNE hFG hfin w hwD hwN J hc hv).trans
    (nielsenCyclicBoundaryKleinHomeomorph hD hNE hFG hfin w hwD hwN J hc hv)).trans
      (((gauge).val.image (frontier K)).trans (Homeomorph.setCongr (gauge).property.2.2))

/-- The actual clipped first face is filled with its true original partial-pairing boundary parameters, without treating the Nielsen intersection as a whole-plane fundamental domain. -/
def nielsenCyclicFaceHomeomorph : PolygonCell J.n≃ₜ↥K :=
  (PolygonCell.radialHomeomorph (n:=J.n) (m:=J.n)
    (nielsenCyclicGaugeBoundaryHomeomorph hD hNE hFG hfin w hwD hwN J hc hv)).trans
      (nielsenCoreGaugeCellHomeomorph hD hNE w hwD hwN J.n)

theorem nielsenCyclicFaceHomeomorph_ofCircle (z:Circle) :
    (nielsenCyclicFaceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv (PolygonCell.ofCircle J.n z):ℂ)=
      Hyperbolic.closedKleinCoordinate (nielsenCyclicBoundaryHomeomorph hD hNE hFG hfin w hwD hwN J hc hv z).val := by
  change (nielsenCoreGaugeCellHomeomorph hD hNE w hwD hwN J.n
    (PolygonCell.radialHomeomorph (n:=J.n) (m:=J.n)
      (nielsenCyclicGaugeBoundaryHomeomorph hD hNE hFG hfin w hwD hwN J hc hv) (PolygonCell.ofCircle J.n z)):ℂ)=_
  rw [PolygonCell.radialHomeomorph_ofCircle,nielsenCoreGaugeCellHomeomorph_coe]
  change (gauge).val.symm ((gauge).val
    (Hyperbolic.closedKleinCoordinate (nielsenCyclicBoundaryHomeomorph hD hNE hFG hfin w hwD hwN J hc hv z).val))=_
  exact (gauge).val.symm_apply_apply _

theorem nielsenCyclicFaceHomeomorph_side (i:Fin J.n) (t:unitInterval) :
    (nielsenCyclicFaceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv (PolygonCell.side i t):ℂ)=
      Hyperbolic.closedKleinCoordinate ((γ) i t) := by
  change (nielsenCyclicFaceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv
    (PolygonCell.ofCircle J.n (Surfaces.polygonSideCircleCover J.n ⟨i,t⟩)):ℂ)=_
  rw [nielsenCyclicFaceHomeomorph_ofCircle,nielsenCyclicBoundaryHomeomorph_cover]
  rfl

/-- This actual first-face homeomorphism takes values in the true compactified clipped Nielsen polygon, retaining all original finite and ideal points. -/
def nielsenCyclicClosedModelFaceHomeomorph :
    PolygonCell J.n≃ₜ↥(Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE))) :=
  (nielsenCyclicFaceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv).trans
    (originalPolygonClosedModelKleinHomeomorph P (D∩fuchsianNielsenCore P hNE)).symm

theorem nielsenCyclicClosedModelFaceHomeomorph_side (i:Fin J.n) (t:unitInterval) :
    (nielsenCyclicClosedModelFaceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv (PolygonCell.side i t)).val=(γ) i t := by
  apply Hyperbolic.closedKleinCoordinate_injective
  exact (originalPolygonClosedModelKleinHomeomorph_symm_coe P _
    (nielsenCyclicFaceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv (PolygonCell.side i t))).trans
      (nielsenCyclicFaceHomeomorph_side hD hNE hFG hfin w hwD hwN J hc hv i t)

end NielsenCyclicFaceExtension



def nielsenCoreFiniteSidePointStep
    {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier}
    (hD:IsConvexFuchsianPolygon P D)
    (hNE:DiscreteGroups.IsNonElementary H)
    (x y:P.domain.carrier) : Prop :=
  ∃v:NielsenRefinedSide hD hNE,Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈v.carrier ∧
    (fuchsianSideElement hD v.val.val.1)⁻¹•x=y

section NielsenCoreFinitePointKernel
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
local notation "step" => nielsenCoreFiniteSidePointStep hD hNE

include hFG hfin w hwD hwN in
theorem nielsenCore_positive_incident_pair_pointChain
    (x:P.domain.carrier) (a b:H)
    (haa:x∈fuchsianDomainTile P (D∩fuchsianNielsenCore P hNE) a)
    (hbb:x∈fuchsianDomainTile P (D∩fuchsianNielsenCore P hNE) b)
    (hab:(fuchsianDomainTile P (D∩fuchsianNielsenCore P hNE) a∩
      fuchsianDomainTile P (D∩fuchsianNielsenCore P hNE) b).Nontrivial) :
    Relation.EqvGen step (a⁻¹•x) (b⁻¹•x) := by
  classical
  by_cases he:a=b
  · subst b
    exact Relation.EqvGen.refl _
  let Q:=D∩fuchsianNielsenCore P hNE
  let g:=a⁻¹*b
  have hgne:g≠1:=fun hh=>he (inv_mul_eq_one.mp hh)
  have hT:(closure Q∩fuchsianDomainTile P Q g).Nontrivial:=by
    have hh:=hab.image (MulAction.injective a⁻¹)
    change (a⁻¹•(a•closure Q∩b•closure Q)).Nontrivial at hh
    rw [smul_set_inter,inv_smul_smul,←mul_smul] at hh
    exact hh
  have hsub:∀k:H,fuchsianDomainTile P Q k⊆fuchsianDomainTile P D k:=by
    intro k z hz
    rw [nielsenCore_closed_tile_inter hD hNE w hwD hwN] at hz
    exact hz.1
  have hSide: (closure D∩fuchsianDomainTile P D g).Nontrivial:=by
    apply hT.mono
    intro z hz
    exact ⟨closure_mono inter_subset_left hz.1,hsub g hz.2⟩
  let s:FuchsianPolygonSides P D:=⟨closure D∩fuchsianDomainTile P D g,
    hD.side_of_nontrivial_intersection hgne hSide⟩
  have hsel:fuchsianSideElement hD s=g:=
    (hD.existsUnique_side_element s.property).unique (fuchsianSideElement_spec hD s) ⟨hgne,rfl⟩
  let F:=fun z:P.domain.carrier=>Hyperbolic.discToClosedModel (P.finiteCoordinate z)
  have hFinj:Function.Injective F:=Hyperbolic.isEmbedding_discToClosedModel.injective.comp P.finiteCoordinate.injective
  have hCore:∀z∈closure (fuchsianNielsenCore P hNE),F z∈nielsenClosedCore P hNE:=by
    intro z hz
    apply mem_closure_image Hyperbolic.isEmbedding_discToClosedModel.continuous.continuousAt
    rw [←P.finiteCoordinate.image_closure]
    exact ⟨z,hz,rfl⟩
  have hST:∀z∈closure Q∩fuchsianDomainTile P Q g,
      F z∈fuchsianSideClosedModel s∩nielsenClosedCore P hNE:=by
    intro z hz
    exact ⟨(mem_fuchsianSideClosedModel_finite s z).mpr
      ⟨closure_mono inter_subset_left hz.1,hsub g hz.2⟩,
      hCore z (closure_mono inter_subset_right hz.1)⟩
  have hnt:(fuchsianSideClosedModel s∩nielsenClosedCore P hNE).Nontrivial:=
    (hT.image hFinj).mono (by rintro _ ⟨z,hz,rfl⟩;exact hST z hz)
  have hpa:a⁻¹•x∈closure Q:=by
    simpa only [fuchsianDomainTile,mem_smul_set_iff_inv_smul_mem] using haa
  have hpb:b⁻¹•x∈closure Q:=by
    simpa only [fuchsianDomainTile,mem_smul_set_iff_inv_smul_mem] using hbb
  have hpg:a⁻¹•x∈fuchsianDomainTile P Q g:=
    ⟨b⁻¹•x,hpb,by simp only [g,mul_smul,smul_inv_smul]⟩
  obtain ⟨v,hvs,hpv⟩:=nielsen_original_positive_clip_refined_at_point hD hNE hFG hfin s hnt
    (F (a⁻¹•x)) (hST _ ⟨hpa,hpg⟩)
  apply Relation.EqvGen.rel
  refine ⟨v,hpv,?_⟩
  rw [hvs,hsel]
  simp only [g,mul_inv_rev,inv_inv,mul_smul,smul_inv_smul]

include hFG hfin w hwD hwN in
/-- Every finite original orbit identification in the actual clipped core closure is generated by genuine positive clipped original side maps. -/
theorem nielsenCore_finite_orbit_pointChain
    (x y:P.domain.carrier)
    (hx:x∈closure (D∩fuchsianNielsenCore P hNE))
    (hy:y∈closure (D∩fuchsianNielsenCore P hNE))
    (horbit:∃g:H,g•x=y) : Relation.EqvGen step x y := by
  let Q:=D∩fuchsianNielsenCore P hNE
  let R:=fun a b:H=>x∈fuchsianDomainTile P Q a∧x∈fuchsianDomainTile P Q b∧
    (fuchsianDomainTile P Q a∩fuchsianDomainTile P Q b).Nontrivial
  obtain ⟨g,hg⟩:=horbit
  have h1:x∈fuchsianDomainTile P D (1:H):=by
    simpa only [fuchsianDomainTile,one_smul] using closure_mono inter_subset_left hx
  have hgI:x∈fuchsianDomainTile P D g⁻¹:=by
    refine ⟨y,closure_mono inter_subset_left hy,?_⟩
    change g⁻¹•y=x
    rw [←hg,inv_smul_smul]
  have hchain:Relation.EqvGen R (1:H) g⁻¹:=by
    by_cases hxN:x∈fuchsianNielsenCore P hNE
    · have hc:=hD.incident_tile_nontrivial_chains x 1 g⁻¹ h1 hgI
      have hcut (a:H) (ha:x∈fuchsianDomainTile P D a):x∈fuchsianDomainTile P Q a:=by
        rw [nielsenCore_closed_tile_inter hD hNE w hwD hwN]
        exact ⟨ha,subset_closure hxN⟩
      have lift {a b:H} (hab:Relation.EqvGen (fun c d:H=>x∈fuchsianDomainTile P D c ∧
          x∈fuchsianDomainTile P D d ∧(fuchsianDomainTile P D c∩fuchsianDomainTile P D d).Nontrivial) a b) :
          Relation.EqvGen R a b:=by
        induction hab with
        | rel a b hab =>
          exact Relation.EqvGen.rel _ _ ⟨hcut a hab.1,hcut b hab.2.1,
            nielsenCore_interior_incident_positive_inter hD hNE w hwD hwN x hxN a b hab.1 hab.2.1 hab.2.2⟩
        | refl => exact Relation.EqvGen.refl _
        | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
        | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
      exact lift hc
    · have hxF:x∈frontier (fuchsianNielsenCore P hNE):=by
        rw [(fuchsianNielsenCore_isOpen P hNE).frontier_eq]
        exact ⟨closure_mono inter_subset_right hx,hxN⟩
      exact IsConvexFuchsianPolygon.nielsenCore_incident_tile_nontrivial_chains hD hNE w hwD hwN x hxF 1 g⁻¹ h1 hgI
  have hmap {a b:H} (hab:Relation.EqvGen R a b):Relation.EqvGen step (a⁻¹•x) (b⁻¹•x):=by
    induction hab with
    | rel a b hab =>
      exact nielsenCore_positive_incident_pair_pointChain hD hNE hFG hfin w hwD hwN x a b hab.1 hab.2.1 hab.2.2
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  simpa only [inv_one,one_smul,inv_inv,hg] using hmap hchain

theorem nielsenCore_finite_pointChain_orbit (x y:P.domain.carrier)
    (hxy:Relation.EqvGen step x y) : ∃g:H,g•x=y := by
  induction hxy with
  | rel a b h =>
    obtain ⟨v,_hv,hv'⟩:=h
    exact ⟨(fuchsianSideElement hD v.val.val.1)⁻¹,hv'⟩
  | refl => exact ⟨1,one_smul _ _⟩
  | symm _ _ _ ih =>
    obtain ⟨g,hg⟩:=ih
    exact ⟨g⁻¹,by rw [←hg,inv_smul_smul]⟩
  | trans _ _ _ _ _ ih₁ ih₂ =>
    obtain ⟨g,hg⟩:=ih₁
    obtain ⟨k,hk⟩:=ih₂
    exact ⟨k*g,by rw [mul_smul,hg,hk]⟩

include hFG hfin w hwD hwN in
theorem nielsenCore_finite_pointChain_iff_orbit (x y:P.domain.carrier)
    (hx:x∈closure (D∩fuchsianNielsenCore P hNE))
    (hy:y∈closure (D∩fuchsianNielsenCore P hNE)) :
    Relation.EqvGen step x y↔∃g:H,g•x=y :=
  ⟨nielsenCore_finite_pointChain_orbit hD hNE x y,
    nielsenCore_finite_orbit_pointChain hD hNE hFG hfin w hwD hwN x y hx hy⟩

end NielsenCoreFinitePointKernel



section NielsenCoreFiniteQuotient
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "π" => Surfaces.mobiusDomainProjection P.domain
local notation "coreImage" => (π) '' closure (fuchsianNielsenCore P hNE)

def nielsenCoreClosedProjection (x:closure Q) : ↥coreImage :=
  ⟨(π) x.val,⟨x.val,closure_mono inter_subset_right x.property,rfl⟩⟩
local notation "F" => nielsenCoreClosedProjection (P:=P) (D:=D) hNE

theorem continuous_nielsenCoreClosedProjection : Continuous (F) :=
  ((Surfaces.mobiusDomainProjection_continuous P.domain).comp continuous_subtype_val).subtype_mk _

include hD in
theorem nielsenCoreClosedProjection_isClosedMap : IsClosedMap (F) := by
  have hclosed:IsClosedMap (fun x:closure Q=>(π) x.val):=by
    intro C hC
    let S:Set P.domain.carrier:=(Subtype.val:closure Q→P.domain.carrier) '' C
    have hS:IsClosed S:=isClosed_closure.isClosedEmbedding_subtypeVal.isClosedMap _ hC
    have hSD:S⊆closure D:=by
      rintro _ ⟨z,_hz,rfl⟩
      exact closure_mono inter_subset_left z.property
    have hLF:LocallyFinite (fun g:H=>g•S):=
      hD.locallyFinite.locallyFinite.subset (fun _=>Set.smul_set_mono hSD)
    have hU:IsClosed (⋃g:H,g•S):=hLF.isClosed_iUnion (fun g=>(Homeomorph.smul g).isClosedMap S hS)
    have he:(π) ⁻¹' ((fun x:closure Q=>(π) x.val) '' C)=⋃g:H,g•S:=by
      ext x
      constructor
      · rintro ⟨z,hz,hzx⟩
        have horb:=Quotient.exact hzx
        change z.val∈MulAction.orbit H x at horb
        obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp horb
        exact mem_iUnion.mpr ⟨g⁻¹,z.val,⟨z,hz,rfl⟩,by
          change g⁻¹•z.val=x
          rw [←hg,inv_smul_smul]⟩
      · intro hx
        obtain ⟨g,z,⟨a,ha,rfl⟩,hgz⟩:=mem_iUnion.mp hx
        refine ⟨a,ha,?_⟩
        rw [←hgz,Surfaces.mobiusDomainProjection_smul]
    apply (isQuotientMap_quotient_mk' (s:=MulAction.orbitRel H P.domain.carrier)).isClosed_preimage.mp
    change IsClosed ((π) ⁻¹' _)
    rw [he]
    exact hU
  exact hclosed.codRestrict _

include hD w hwD hwN in
theorem nielsenCoreClosedProjection_surjective : Function.Surjective (F) := by
  rintro ⟨p,x,hx,rfl⟩
  have hcover:=hD.locallyFinite.fundamental.closure_cover
  have hxcover:x∈⋃g:H,fuchsianDomainTile P D g:=by
    change x∈⋃g:H,(fun y:P.domain.carrier=>g•y) '' closure D
    rw [hcover]
    trivial
  obtain ⟨g,y,hy,hgy⟩:=mem_iUnion.mp hxcover
  have hyN:y∈closure (fuchsianNielsenCore P hNE):=by
    have ht:g⁻¹•x∈g⁻¹•closure (fuchsianNielsenCore P hNE):=mem_smul_set.mpr ⟨x,hx,rfl⟩
    rw [fuchsianNielsenCore_smul_closure,←hgy,inv_smul_smul] at ht
    exact ht
  have hyQ:y∈closure Q:=by
    rw [nielsenCore_inter_closure_eq hD hNE w hwD hwN]
    exact ⟨hy,hyN⟩
  refine ⟨⟨y,hyQ⟩,Subtype.ext ?_⟩
  change (π) y=(π) x
  rw [←hgy,Surfaces.mobiusDomainProjection_smul]

include hD w hwD hwN in
theorem nielsenCoreClosedProjection_isQuotientMap : IsQuotientMap (F) :=
  (nielsenCoreClosedProjection_isClosedMap hD hNE).isQuotientMap
    (continuous_nielsenCoreClosedProjection hNE) (nielsenCoreClosedProjection_surjective hD hNE w hwD hwN)

def nielsenCoreFiniteSidePointSetoid : Setoid (closure Q) :=
  (Relation.EqvGen.setoid (nielsenCoreFiniteSidePointStep hD hNE)).comap Subtype.val

include hFG hfin w hwD hwN in
theorem nielsenCoreFiniteSidePointSetoid_iff_projection (x y:closure Q) :
    nielsenCoreFiniteSidePointSetoid hD hNE x y↔(F) x=(F) y := by
  change Relation.EqvGen (nielsenCoreFiniteSidePointStep hD hNE) x.val y.val↔(F) x=(F) y
  rw [nielsenCore_finite_pointChain_iff_orbit hD hNE hFG hfin w hwD hwN x.val y.val x.property y.property]
  constructor
  · rintro ⟨g,hg⟩
    apply Subtype.ext
    change (π) x.val=(π) y.val
    rw [←hg,Surfaces.mobiusDomainProjection_smul]
  · intro he
    have hπ:(π) x.val=(π) y.val:=congrArg Subtype.val he
    have horb:=Quotient.exact hπ
    change x.val∈MulAction.orbit H y.val at horb
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp horb
    exact ⟨g⁻¹,by rw [←hg,inv_smul_smul]⟩

/-- The genuine partial positive-side quotient of the true finite core closure is naturally homeomorphic to its unchanged original whole-group quotient image. -/
def nielsenCoreFiniteSidePointQuotientHomeomorph :
    Quotient (nielsenCoreFiniteSidePointSetoid hD hNE)≃ₜ↥coreImage :=
  (Homeomorph.Quotient.congrRight
    (nielsenCoreFiniteSidePointSetoid_iff_projection hD hNE hFG hfin w hwD hwN)).trans
      (Topology.IsQuotientMap.homeomorph
        (f:=⟨(F),continuous_nielsenCoreClosedProjection hNE⟩)
        (nielsenCoreClosedProjection_isQuotientMap hD hNE w hwD hwN))

end NielsenCoreFiniteQuotient



section NielsenCappedCornerRealization
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "rawSetoid" => nielsenCoreRawCornerSetoid hD hNE hFG hfin w hwD hwN J hc hv
local notation "rawStep" => nielsenCoreRawCornerStep hD hNE hFG hfin w hwD hwN J hc hv
local notation "pairIndex" => nielsenCyclicPairIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "partner" => nielsenCappedOccurrencePartner hD hNE hFG hfin w hwD hwN J hc hv
local notation "label" => nielsenCappedOccurrenceRawLabel hD hNE hFG hfin w hwD hwN J hc hv
local notation "oldCorner" => nielsenCappedOriginalCorner hD hNE hFG hfin w hwD hwN J hc hv
local notation "mk" => FiniteCyclicPresentation.polygonalMk (Pcap) (valid)

theorem nielsenCappedBoundaryPairing_direction (p:(Pcap).BoundaryPairing) :
    p.direction=PolygonGluing.ParameterDirection.opposite := by
  cases hd:p.direction with
  | same =>
    have he:=p.compatible
    rw [hd] at he
    exact False.elim (p.source_ne_target
      ((nielsenCappedOccurrence_dart_injective hD hNE hFG hfin w hwD hwN J hc hv) he).symm)
  | opposite => rfl

theorem nielsenCappedBoundaryPairing_target (p:(Pcap).BoundaryPairing) : p.target=(partner) p.source := by
  apply nielsenCappedOccurrence_dart_injective hD hNE hFG hfin w hwD hwN J hc hv
  have he:=p.compatible
  rw [nielsenCappedBoundaryPairing_direction hD hNE hFG hfin w hwD hwN J hc hv] at he
  exact he.trans (nielsenCappedOccurrencePartner_dart hD hNE hFG hfin w hwD hwN J hc hv p.source).symm

/-- Literal corners of every stored core or cap face carry their genuine raw endpoint classes; all other cell points are unmarked. -/
def nielsenCappedCornerPreLabel (z:(Pcap).PolygonalPreRealization) : Option V :=
  if hz:∃i:Fin ((Pcap).boundary z.1).length,PolygonCell.side i 0=z.2 then
    some ((label) ⟨z.1,Classical.choose hz⟩)
  else none
local notation "preLabel" => nielsenCappedCornerPreLabel hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedCornerPreLabel_zero (o:(Pcap).BoundaryOccurrence) :
    preLabel (((Pcap).occurrenceSide o).point 0)=some ((label) o) := by
  have hz:∃i:Fin ((Pcap).boundary o.1).length,PolygonCell.side i 0=PolygonCell.side o.2 0:=⟨o.2,rfl⟩
  dsimp only [nielsenCappedCornerPreLabel,FiniteCyclicPresentation.occurrenceSide,PolygonGluing.Side.point]
  rw [dite_eq_left hz]
  rw [Surfaces.PolygonCellCollision.side_zero_injective (Classical.choose_spec hz)]

theorem nielsenCappedCornerPreLabel_side (o:(Pcap).BoundaryOccurrence) (t:unitInterval) :
    preLabel (((Pcap).occurrenceSide o).point t)=
      if t=0 then some ((label) o) else if t=1 then some ((label) (Surfaces.CyclicSurface.cornerNext (Pcap) o)) else none := by
  by_cases h0:t=0
  · rw [h0,ite_eq_left rfl,nielsenCappedCornerPreLabel_zero]
  rw [ite_eq_right h0]
  by_cases h1:t=1
  · rw [h1,ite_eq_left rfl]
    have he:((Pcap).occurrenceSide o).point 1=((Pcap).occurrenceSide (Surfaces.CyclicSurface.cornerNext (Pcap) o)).point 0:=by
      rcases o with ⟨f,i⟩
      exact congrArg (fun x:PolygonCell ((Pcap).boundary f).length=>
        (⟨f,x⟩:(Pcap).PolygonalPreRealization)) (PolygonCell.side_one_eq_rotate_zero i)
    rw [he,nielsenCappedCornerPreLabel_zero]
  rw [ite_eq_right h1,nielsenCappedCornerPreLabel,dite_eq_right]
  rintro ⟨j,hj⟩
  rcases (Surfaces.PolygonCellCollision.side_eq_iff o.2 j t 0).mp hj.symm with h|h|h
  · exact h0 h.2
  · exact h1 h.1
  · exact h0 h.1

theorem nielsenCappedCornerPreLabel_pairing (p:(Pcap).BoundaryPairing) (t:unitInterval) :
    preLabel (p.identification.source.point t)=preLabel (p.identification.target.point (p.identification.parameter t)) := by
  have hd:=nielsenCappedBoundaryPairing_direction hD hNE hFG hfin w hwD hwN J hc hv p
  have ht:p.identification.parameter t=unitInterval.symm t:=by
    change p.direction.homeomorph t=unitInterval.symm t
    rw [hd]
    rfl
  rw [ht]
  change preLabel (((Pcap).occurrenceSide p.source).point t)=
    preLabel (((Pcap).occurrenceSide p.target).point (unitInterval.symm t))
  rw [nielsenCappedCornerPreLabel_side,nielsenCappedCornerPreLabel_side,
    nielsenCappedBoundaryPairing_target hD hNE hFG hfin w hwD hwN J hc hv p]
  by_cases h0:t=0
  · subst t
    simp only [unitInterval.symm_zero,ite_true,one_ne_zero,ite_false]
    exact congrArg some (nielsenCappedOccurrenceRawLabel_paired_left hD hNE hFG hfin w hwD hwN J hc hv p.source)
  by_cases h1:t=1
  · subst t
    simp only [unitInterval.symm_one,one_ne_zero,ite_false,ite_true]
    exact congrArg some (nielsenCappedOccurrenceRawLabel_paired_right hD hNE hFG hfin w hwD hwN J hc hv p.source)
  have h01:unitInterval.symm t≠0:=by intro he;exact h1 (unitInterval.symm_involutive.injective (he.trans unitInterval.symm_one.symm))
  have h10:unitInterval.symm t≠1:=by intro he;exact h0 (unitInterval.symm_involutive.injective (he.trans unitInterval.symm_zero.symm))
  simp only [ite_eq_right h0,ite_eq_right h1,ite_eq_right h01,ite_eq_right h10]

def nielsenCappedCornerWordLabel : (Pcap).PolygonalRealization (valid)→Option V :=
  Quotient.lift (preLabel) (by
    intro a b h
    change Relation.EqvGen (PolygonGluing.Generator ((Pcap).polygonalIdentifications (valid))) a b at h
    induction h with
    | rel a b h =>
      cases h with
      | glue identification hi t =>
        obtain ⟨p,rfl⟩:=hi
        exact nielsenCappedCornerPreLabel_pairing hD hNE hFG hfin w hwD hwN J hc hv p t
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

/-- The unchanged faithful realization contains this genuine stored original corner. -/
def nielsenCappedRawIndexPoint (i:ZMod J.n) : (Pcap).PolygonalRealization (valid) :=
  (mk) (((Pcap).occurrenceSide ((oldCorner) i)).point 0)
local notation "indexPoint" => nielsenCappedRawIndexPoint hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedCornerWordLabel_indexPoint (i:ZMod J.n) :
    nielsenCappedCornerWordLabel hD hNE hFG hfin w hwD hwN J hc hv ((indexPoint) i)=some (Quotient.mk (rawSetoid) i) := by
  change preLabel (((Pcap).occurrenceSide ((oldCorner) i)).point 0)=_
  rw [nielsenCappedCornerPreLabel_zero]
  congr 1
  unfold nielsenCappedOccurrenceRawLabel nielsenCappedOriginalCorner
  rw [Equiv.apply_symm_apply]
  rfl



theorem nielsenCappedRawIndexPoint_next (i:ZMod J.n) :
    (mk) (((Pcap).occurrenceSide ((oldCorner) i)).point 1)=(indexPoint) (i+1) := by
  change (mk) (((Pcap).occurrenceSide ((oldCorner) i)).point 1)=
    (mk) (((Pcap).occurrenceSide ((oldCorner) (i+1))).point 0)
  rw [←nielsenCappedOriginalCorner_next]
  apply congrArg (mk)
  rcases he:(oldCorner) i with ⟨f,k⟩
  exact congrArg (fun z:PolygonCell ((Pcap).boundary f).length=>
    (⟨f,z⟩:(Pcap).PolygonalPreRealization)) (PolygonCell.side_one_eq_rotate_zero k)

theorem nielsenCappedRawIndexPoint_step {i j:ZMod J.n} (hij:rawStep i j) :
    (indexPoint) i=(indexPoint) j := by
  obtain ⟨hi,rfl⟩:=hij
  have hnot:¬(Pcap).IsBoundaryEdge ((oldCorner) i).edge:=by
    intro he
    have htwo:=nielsenCappedPresentation_closed hD hNE hFG hfin w hwD hwN J hc hv ((oldCorner) i).edge
    change (Pcap).edgeMultiplicity ((oldCorner) i).edge=1 at he
    omega
  obtain ⟨p,hp⟩:=(valid).exists_pairing_source ((oldCorner) i) hnot
  have htarget:p.target=(oldCorner) (pairIndex i):=by
    rw [nielsenCappedBoundaryPairing_target hD hNE hFG hfin w hwD hwN J hc hv p,hp,
      nielsenCappedOriginalCorner_partner hD hNE hFG hfin w hwD hwN J hc hv i hi]
  have hpar:p.identification.parameter 0=1:=by
    change p.direction.homeomorph 0=1
    rw [nielsenCappedBoundaryPairing_direction hD hNE hFG hfin w hwD hwN J hc hv p]
    exact unitInterval.symm_zero
  have h:=(Pcap).polygonalMk_pairing_eq (valid) p 0
  change (mk) (((Pcap).occurrenceSide p.source).point 0)=
    (mk) (((Pcap).occurrenceSide p.target).point (p.identification.parameter 0)) at h
  rw [hp,htarget,hpar,nielsenCappedRawIndexPoint_next] at h
  exact h

theorem nielsenCappedRawIndexPoint_rawChain {i j:ZMod J.n} (hij:Relation.EqvGen rawStep i j) :
    (indexPoint) i=(indexPoint) j := by
  induction hij with
  | rel i j h => exact nielsenCappedRawIndexPoint_step hD hNE hFG hfin w hwD hwN J hc hv h
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The actual raw corner quotient embeds by its unchanged stored corners in the faithful multiface capped realization. -/
def nielsenCappedRawCornerPoint : V→(Pcap).PolygonalRealization (valid) :=
  Quotient.lift (indexPoint) (fun _ _ h=>nielsenCappedRawIndexPoint_rawChain hD hNE hFG hfin w hwD hwN J hc hv h)
local notation "cornerPoint" => nielsenCappedRawCornerPoint hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedRawCornerPoint_mk (i:ZMod J.n) : (cornerPoint) (Quotient.mk (rawSetoid) i)=(indexPoint) i := rfl

theorem nielsenCappedRawCornerPoint_label (q:V) :
    nielsenCappedCornerWordLabel hD hNE hFG hfin w hwD hwN J hc hv ((cornerPoint) q)=some q := by
  induction q using Quotient.inductionOn with
  | h i => exact nielsenCappedCornerWordLabel_indexPoint hD hNE hFG hfin w hwD hwN J hc hv i

theorem nielsenCappedRawCornerPoint_injective : Function.Injective (cornerPoint) := by
  intro q r hqr
  have h:=congrArg (nielsenCappedCornerWordLabel hD hNE hFG hfin w hwD hwN J hc hv) hqr
  rw [nielsenCappedRawCornerPoint_label,nielsenCappedRawCornerPoint_label] at h
  exact Option.some.inj h

/-- The complete kernel of genuine old corner images in the faithful cap realization is exactly the original partial-side raw chain. -/
theorem nielsenCappedRawIndexPoint_eq_iff (i j:ZMod J.n) :
    (indexPoint) i=(indexPoint) j↔Relation.EqvGen rawStep i j := by
  constructor
  · intro he
    have hq:Quotient.mk (rawSetoid) i=Quotient.mk (rawSetoid) j:=
      nielsenCappedRawCornerPoint_injective hD hNE hFG hfin w hwD hwN J hc hv he
    exact Quotient.exact hq
  · exact nielsenCappedRawIndexPoint_rawChain hD hNE hFG hfin w hwD hwN J hc hv

end NielsenCappedCornerRealization



section NielsenCappedOriginalFace
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "index" => originalCyclicFinIndex J
local notation "occIndex" => nielsenCappedOccurrenceIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "dart" => nielsenCapFiniteDartEquiv hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedOriginalFace_length : ((Pcap).boundary (f₀)).length=J.n := by
  rw [nielsenCappedPresentation_original_boundary,List.length_map,nielsenCapOriginalOccurrences,List.length_ofFn]
local notation "hlen" => nielsenCappedOriginalFace_length hD hNE hFG hfin w hwD hwN J hc hv

def nielsenCappedOriginalOccurrence (i:Fin J.n) : (Pcap).BoundaryOccurrence :=
  ⟨f₀,Fin.cast (hlen).symm i⟩
local notation "oldOccurrence" => nielsenCappedOriginalOccurrence hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedOriginalOccurrence_index (i:Fin J.n) :
    (occIndex) ((oldOccurrence) i)=Sum.inl ((index) i) := by
  apply (dart).injective
  rw [nielsenCappedOccurrenceIndex_dart]
  change ((Pcap).boundary (f₀)).get (Fin.cast (hlen).symm i)=(dart) (Sum.inl ((index) i))
  simp only [nielsenCappedPresentation_original_boundary,List.get_eq_getElem,List.getElem_map,
    nielsenCapOriginalOccurrences,List.getElem_ofFn,Fin.val_cast,originalCyclicFinIndex]
  rfl

theorem nielsenCappedOriginalOccurrence_eq_corner (i:Fin J.n) :
    (oldOccurrence) i=nielsenCappedOriginalCorner hD hNE hFG hfin w hwD hwN J hc hv ((index) i) := by
  apply (occIndex).injective
  rw [nielsenCappedOriginalOccurrence_index]
  exact ((occIndex).apply_symm_apply _).symm

/-- The first stored face of the unchanged capped word is the actual compactified clipped Nielsen polygon, with its actual face topology. -/
def nielsenCappedOriginalFaceHomeomorph :
    PolygonCell ((Pcap).boundary (f₀)).length≃ₜ
      ↥(Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' (D∩fuchsianNielsenCore P hNE))) :=
  (PolygonCell.castHomeomorph (hlen)).trans
    (nielsenCyclicClosedModelFaceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv)

theorem nielsenCappedOriginalFaceHomeomorph_side (i:Fin J.n) (t:unitInterval) :
    (nielsenCappedOriginalFaceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv
      (PolygonCell.side (Fin.cast (hlen).symm i) t)).val=
      nielsenCyclicSideParam hD hNE hFG hfin w hwD hwN J hc hv i t := by
  change (nielsenCyclicClosedModelFaceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv
    (PolygonCell.castHomeomorph (hlen) (PolygonCell.side (Fin.cast (hlen).symm i) t))).val=_
  rw [PolygonCell.castHomeomorph_side]
  have hi:Fin.cast (hlen) (Fin.cast (hlen).symm i)=i:=Fin.ext rfl
  rw [hi,nielsenCyclicClosedModelFaceHomeomorph_side]

end NielsenCappedOriginalFace



section NielsenCappedBoundaryOrbit
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv
local notation "index" => originalCyclicFinIndex J
local notation "occIndex" => nielsenCappedOccurrenceIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "rawLabel" => nielsenCappedOccurrenceRawLabel hD hNE hFG hfin w hwD hwN J hc hv
local notation "γ" => nielsenCyclicSideParam hD hNE hFG hfin w hwD hwN J hc hv
local notation "πs" => DiscreteGroups.Action.orbitProjection H Mobius.ExtendedComplex

def nielsenRawCornerSphereClass : V → DiscreteGroups.Action.orbitQuotient H Mobius.ExtendedComplex :=
  Quotient.lift (fun i=>(πs) (Hyperbolic.closedDiscToExtended (vertex i))) (by
    intro i j hij
    obtain ⟨g,hg⟩:=nielsenCoreRawCornerChain_sphereOrbit hD hNE hFG hfin w hwD hwN J hc hv hij
    apply Quotient.sound
    refine ⟨g⁻¹,?_⟩
    change g.val.val.symm (Hyperbolic.closedDiscToExtended (vertex j))=Hyperbolic.closedDiscToExtended (vertex i)
    rw [←hg,g.val.val.symm_apply_apply])
local notation "sphereClass" => nielsenRawCornerSphereClass hD hNE hFG hfin w hwD hwN J hc hv

/-- Actual sphere coordinates on every genuine old or cap boundary occurrence, with the cap traversal reversed. -/
def nielsenCappedSphereBoundaryPoint
    (o:(Pcap).BoundaryOccurrence)
    (t:unitInterval) : Mobius.ExtendedComplex :=
  match (occIndex) o with
  | Sum.inl i => Hyperbolic.closedDiscToExtended ((γ) ((index).symm i) t)
  | Sum.inr b => Hyperbolic.closedDiscToExtended ((γ) ((index).symm b.val) (unitInterval.symm t))
local notation "boundaryPoint" => nielsenCappedSphereBoundaryPoint hD hNE hFG hfin w hwD hwN J hc hv

def nielsenCappedSphereBoundaryClass (o:(Pcap).BoundaryOccurrence) (t:unitInterval) : DiscreteGroups.Action.orbitQuotient H Mobius.ExtendedComplex :=
  (πs) ((boundaryPoint) o t)
local notation "boundaryClass" => nielsenCappedSphereBoundaryClass hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedSphereBoundaryClass_zero (o:(Pcap).BoundaryOccurrence) :
    (boundaryClass) o 0=(sphereClass) ((rawLabel) o) := by
  cases he:(occIndex) o with
  | inl i =>
    simp only [nielsenCappedSphereBoundaryClass,nielsenCappedSphereBoundaryPoint,he,
      nielsenCyclicSideParam_zero,Equiv.apply_symm_apply]
    unfold nielsenCappedOccurrenceRawLabel
    rw [he]
    rfl
  | inr b =>
    simp only [nielsenCappedSphereBoundaryClass,nielsenCappedSphereBoundaryPoint,he,
      unitInterval.symm_zero,nielsenCyclicSideParam_one,Equiv.apply_symm_apply]
    unfold nielsenCappedOccurrenceRawLabel
    rw [he]
    rfl

theorem nielsenCappedSphereBoundaryClass_one (o:(Pcap).BoundaryOccurrence) :
    (boundaryClass) o 1=(sphereClass)
    ((rawLabel)
    (Surfaces.CyclicSurface.cornerNext (Pcap) o)) := by
  rw [nielsenCappedOccurrenceRawLabel_next]
  cases he:(occIndex) o with
  | inl i =>
    simp only [nielsenCappedSphereBoundaryClass,nielsenCappedSphereBoundaryPoint,he,
      nielsenCyclicSideParam_one,Equiv.apply_symm_apply]
    rfl
  | inr b =>
    simp only [nielsenCappedSphereBoundaryClass,nielsenCappedSphereBoundaryPoint,he,
      unitInterval.symm_one,nielsenCyclicSideParam_zero,Equiv.apply_symm_apply]
    rfl

/-- The real circular boundary clock of every stored face has exactly consistent original orbit values at all adjacent endpoints. -/
theorem nielsenCappedSphereBoundaryClass_face_collision
    (f:(Pcap).Face) (i j:Fin ((Pcap).boundary f).length) (t u:unitInterval)
    (he:PolygonCell.side i t=PolygonCell.side j u) :
    (boundaryClass) ⟨f,i⟩ t=(boundaryClass) ⟨f,j⟩ u := by
  rcases (Surfaces.PolygonCellCollision.side_eq_iff i j t u).mp he with
    ⟨rfl,rfl⟩|⟨rfl,rfl,rfl⟩|⟨rfl,rfl,rfl⟩
  · rfl
  · rw [nielsenCappedSphereBoundaryClass_one,nielsenCappedSphereBoundaryClass_zero]
    rfl
  · rw [nielsenCappedSphereBoundaryClass_zero,nielsenCappedSphereBoundaryClass_one]
    rfl


theorem nielsenCyclicSideParam_pair_sphereClass (i:Fin J.n)
    (hi:nielsenCyclicFinPair hD hNE hFG hfin w hwD hwN J hc hv i≠i) (t:unitInterval) :
    (πs) (Hyperbolic.closedDiscToExtended ((γ) i t))=
      (πs)
      (Hyperbolic.closedDiscToExtended ((γ)
      (nielsenCyclicFinPair hD hNE hFG hfin w hwD hwN J hc hv i)
      (unitInterval.symm t))) := by
  obtain ⟨v,hv'⟩:=nielsenCyclicFinPair_nonfixed_tag hD hNE hFG hfin w hwD hwN J hc hv i hi
  have he:=nielsenCyclicSideParam_pair hD hNE hFG hfin w hwD hwN J hc hv i hi t
  have hs:Hyperbolic.closedDiscToExtended ((γ) (nielsenCyclicFinPair hD hNE hFG hfin w hwD hwN J hc hv i)
    (unitInterval.symm t))=
      (fuchsianSideElement hD v.val.val.1).val.val.symm (Hyperbolic.closedDiscToExtended ((γ) i t)) := by
    rw [←he]
    rw [nielsenCyclicEdgeAction,hv']
    change Hyperbolic.closedDiscToExtended ((P.compactifiedAction (fuchsianSideElement hD v.val.val.1)⁻¹).closedMap ((γ)
      i t))=_
    exact P.compactifiedAction_sphere _ _
  apply Quotient.sound
  refine ⟨fuchsianSideElement hD v.val.val.1,?_⟩
  change (fuchsianSideElement hD v.val.val.1).val.val
    (Hyperbolic.closedDiscToExtended ((γ) (nielsenCyclicFinPair hD hNE hFG hfin w hwD hwN J hc hv i) (unitInterval.symm
      t)))=_
  rw [hs]
  exact Equiv.apply_symm_apply _ _

theorem nielsenCappedSphereBoundaryClass_partner (o:(Pcap).BoundaryOccurrence) (t:unitInterval) :
    (boundaryClass) o t=(boundaryClass)
      (nielsenCappedOccurrencePartner hD hNE hFG hfin w hwD hwN J hc hv o) (unitInterval.symm t) := by
  have hp:(occIndex) (nielsenCappedOccurrencePartner hD hNE hFG hfin w hwD hwN J hc hv o)=
      nielsenCapOccurrencePair hD hNE hFG hfin w hwD hwN J hc hv ((occIndex) o) := by
    exact (occIndex).apply_symm_apply _
  cases he:(occIndex) o with
  | inl i =>
    by_cases hi:nielsenCyclicPairIndex hD hNE hFG hfin w hwD hwN J hc hv i=i
    · simp only [he,nielsenCapOccurrencePair,dite_eq_left hi] at hp
      simp only [nielsenCappedSphereBoundaryClass,nielsenCappedSphereBoundaryPoint,he,hp,unitInterval.symm_symm]
    · simp only [he,nielsenCapOccurrencePair,dite_eq_right hi] at hp
      simp only [nielsenCappedSphereBoundaryClass,nielsenCappedSphereBoundaryPoint,he,hp]
      have hn:nielsenCyclicFinPair hD hNE hFG hfin w hwD hwN J hc hv ((index).symm i)≠(index).symm i := by
        intro h
        apply hi
        have hh:=congrArg (index) h
        simpa only [nielsenCyclicFinPair_index,Equiv.apply_symm_apply] using hh
      simpa only [nielsenCyclicFinPair,Equiv.apply_symm_apply] using
        nielsenCyclicSideParam_pair_sphereClass hD hNE hFG hfin w hwD hwN J hc hv ((index).symm i) hn t
  | inr b =>
    simp only [he,nielsenCapOccurrencePair] at hp
    simp only [nielsenCappedSphereBoundaryClass,nielsenCappedSphereBoundaryPoint,he,hp]

theorem nielsenCappedSphereBoundaryClass_pairing (p:(Pcap).BoundaryPairing) (t:unitInterval) :
    (boundaryClass) p.source t=(boundaryClass) p.target (p.identification.parameter t) := by
  have ht:p.identification.parameter t=unitInterval.symm t := by
    change p.direction.homeomorph t=unitInterval.symm t
    rw [nielsenCappedBoundaryPairing_direction hD hNE hFG hfin w hwD hwN J hc hv p]
    rfl
  rw [ht,nielsenCappedBoundaryPairing_target hD hNE hFG hfin w hwD hwN J hc hv p]
  exact nielsenCappedSphereBoundaryClass_partner hD hNE hFG hfin w hwD hwN J hc hv p.source t


/-- The actual sphere-orbit boundary map on each genuine stored face. -/
def nielsenCappedFaceBoundarySphereClass (f:(Pcap).Face) (z:Circle) : DiscreteGroups.Action.orbitQuotient H Mobius.ExtendedComplex :=
  let hn:0<((Pcap).boundary f).length:=List.length_pos_iff.mpr
    (nielsenCappedPresentation_boundary_ne_nil hD hNE hFG hfin w hwD hwN J hc hv f)
  let x:=Classical.choose (Surfaces.polygonSideCircleCover_surjective ((Pcap).boundary f).length hn z)
  (boundaryClass) ⟨f,x.1⟩ x.2
local notation "faceClass" => nielsenCappedFaceBoundarySphereClass hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedFaceBoundarySphereClass_cover (f:(Pcap).Face)
    (x:Σ _:Fin ((Pcap).boundary f).length,unitInterval) :
    (faceClass) f (Surfaces.polygonSideCircleCover ((Pcap).boundary f).length x)=(boundaryClass) ⟨f,x.1⟩ x.2 := by
  let hn:0<((Pcap).boundary f).length:=List.length_pos_iff.mpr
    (nielsenCappedPresentation_boundary_ne_nil hD hNE hFG hfin w hwD hwN J hc hv f)
  let y:=Classical.choose (Surfaces.polygonSideCircleCover_surjective ((Pcap).boundary f).length hn
    (Surfaces.polygonSideCircleCover ((Pcap).boundary f).length x))
  have hy:=Classical.choose_spec (Surfaces.polygonSideCircleCover_surjective ((Pcap).boundary f).length hn
    (Surfaces.polygonSideCircleCover ((Pcap).boundary f).length x))
  change (boundaryClass) ⟨f,y.1⟩ y.2=(boundaryClass) ⟨f,x.1⟩ x.2
  apply nielsenCappedSphereBoundaryClass_face_collision hD hNE hFG hfin w hwD hwN J hc hv
  apply PolygonCell.ext
  exact congrArg Subtype.val hy

end NielsenCappedBoundaryOrbit



section NielsenCappedSphereLabel
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "hlen" => nielsenCappedOriginalFace_length hD hNE hFG hfin w hwD hwN J hc hv
local notation "E" => nielsenCappedOriginalFaceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv
local notation "πs" => DiscreteGroups.Action.orbitProjection H Mobius.ExtendedComplex
local notation "boundaryClass" => nielsenCappedSphereBoundaryClass hD hNE hFG hfin w hwD hwN J hc hv
local notation "faceClass" => nielsenCappedFaceBoundarySphereClass hD hNE hFG hfin w hwD hwN J hc hv
local notation "mk" => FiniteCyclicPresentation.polygonalMk (Pcap) (valid)

theorem nielsenCappedSphereBoundaryClass_original_occurrence (i:Fin J.n) (t:unitInterval) :
    (boundaryClass) (nielsenCappedOriginalOccurrence hD hNE hFG hfin w hwD hwN J hc hv i) t=
      (πs) (Hyperbolic.closedDiscToExtended (nielsenCyclicSideParam hD hNE hFG hfin w hwD hwN J hc hv i t)) := by
  simp only [nielsenCappedSphereBoundaryClass,nielsenCappedSphereBoundaryPoint,
    nielsenCappedOriginalOccurrence_index,Equiv.symm_apply_apply]

/-- The actual original sphere point of a point in the true clipped first face. -/
def nielsenCappedOriginalSpherePoint
    (z:(Pcap).PolygonalPreRealization)
    (hf:z.1=f₀) : Mobius.ExtendedComplex :=
  Hyperbolic.closedDiscToExtended ((E) (hf ▸ z.2)).val

/-- Genuine old points and cap boundaries carry their original sphere-orbit class; cap interiors carry no original point. -/
def nielsenCappedSpherePreLabel (z:(Pcap).PolygonalPreRealization) : Option (DiscreteGroups.Action.orbitQuotient H
  Mobius.ExtendedComplex) :=
  if hf:z.1=f₀ then some ((πs) (nielsenCappedOriginalSpherePoint hD hNE hFG hfin w hwD hwN J hc hv z hf))
  else if hz:‖z.2.val‖=1 then some ((faceClass) z.1 ⟨z.2.val,mem_sphere_zero_iff_norm.mpr hz⟩) else none
local notation "preLabel" => nielsenCappedSpherePreLabel hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedSpherePreLabel_original (x:PolygonCell ((Pcap).boundary (f₀)).length) :
    (preLabel) ⟨f₀,x⟩=some ((πs)
    (Hyperbolic.closedDiscToExtended ((E) x).val)) := by
  rw [nielsenCappedSpherePreLabel,dite_eq_left rfl]
  rfl

theorem nielsenCappedSpherePreLabel_side (o:(Pcap).BoundaryOccurrence) (t:unitInterval) :
    (preLabel) (((Pcap).occurrenceSide o).point t)=some ((boundaryClass) o t) := by
  rcases o with ⟨f,i⟩
  by_cases hf:f=f₀
  · subst f
    change (preLabel) ⟨f₀,PolygonCell.side i t⟩=_
    rw [nielsenCappedSpherePreLabel_original]
    let k:Fin J.n:=Fin.cast (hlen) i
    have hk:Fin.cast (hlen).symm k=i:=Fin.ext rfl
    have he:=nielsenCappedOriginalFaceHomeomorph_side hD hNE hFG hfin w hwD hwN J hc hv k t
    rw [hk] at he
    change some ((πs) (Hyperbolic.closedDiscToExtended ((E) (PolygonCell.side i t)).val))=_
    rw [he]
    have ho:nielsenCappedOriginalOccurrence hD hNE hFG hfin w hwD hwN J hc hv k=⟨f₀,i⟩:=by
      apply Sigma.ext rfl
      exact heq_of_eq hk
    rw [←ho,nielsenCappedSphereBoundaryClass_original_occurrence]
  · have hn:‖(PolygonCell.side i t).val‖=1:=by
      change ‖((Circle.exp (PolygonCell.sideAngle i t):Circle):ℂ)‖=1
      exact Circle.norm_coe _
    change (if h:f=f₀ then _ else if h:‖(PolygonCell.side i t).val‖=1 then _ else _)=_
    rw [dite_eq_right hf,dite_eq_left hn]
    exact congrArg some (nielsenCappedFaceBoundarySphereClass_cover hD hNE hFG hfin w hwD hwN J hc hv f ⟨i,t⟩)

theorem nielsenCappedSpherePreLabel_pairing (p:(Pcap).BoundaryPairing) (t:unitInterval) :
    (preLabel) (p.identification.source.point t)=
      (preLabel) (p.identification.target.point (p.identification.parameter t)) := by
  change (preLabel) (((Pcap).occurrenceSide p.source).point t)=
    (preLabel) (((Pcap).occurrenceSide p.target).point (p.identification.parameter t))
  rw [nielsenCappedSpherePreLabel_side,nielsenCappedSpherePreLabel_side]
  exact congrArg some (nielsenCappedSphereBoundaryClass_pairing hD hNE hFG hfin w hwD hwN J hc hv p t)

/-- A label on the unchanged faithful cap realization, obtained from actual original sphere orbits on every original point. -/
def nielsenCappedSphereWordLabel : (Pcap).PolygonalRealization (valid) → Option (DiscreteGroups.Action.orbitQuotient H
  Mobius.ExtendedComplex) :=
  Quotient.lift (preLabel) (by
    intro a b h
    change Relation.EqvGen (PolygonGluing.Generator ((Pcap).polygonalIdentifications (valid))) a b at h
    induction h with
    | rel a b h =>
      cases h with
      | glue identification hi t =>
        obtain ⟨p,rfl⟩:=hi
        exact nielsenCappedSpherePreLabel_pairing hD hNE hFG hfin w hwD hwN J hc hv p t
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂)

/-- Equality of actual first-face images in the capped word forces equality of their true original sphere-orbit classes. -/
theorem nielsenCappedOriginalFace_eq_implies_sphereOrbit
    (x y:PolygonCell ((Pcap).boundary (f₀)).length)
    (he:(mk) ⟨f₀,x⟩=(mk) ⟨f₀,y⟩) :
    (πs)
    (Hyperbolic.closedDiscToExtended ((E) x).val)=(πs)
    (Hyperbolic.closedDiscToExtended ((E) y).val) := by
  have h:=congrArg (nielsenCappedSphereWordLabel hD hNE hFG hfin w hwD hwN J hc hv) he
  change (preLabel) ⟨f₀,x⟩=(preLabel) ⟨f₀,y⟩ at h
  rw [nielsenCappedSpherePreLabel_original,nielsenCappedSpherePreLabel_original] at h
  exact Option.some.inj h

end NielsenCappedSphereLabel



section NielsenCappedFiniteWordKernel
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "hlen" => nielsenCappedOriginalFace_length hD hNE hFG hfin w hwD hwN J hc hv
local notation "E" => nielsenCappedOriginalFaceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv
local notation "γ" => nielsenCyclicSideParam hD hNE hFG hfin w hwD hwN J hc hv
local notation "index" => originalCyclicFinIndex J
local notation "finPair" => nielsenCyclicFinPair hD hNE hFG hfin w hwD hwN J hc hv
local notation "pairIndex" => nielsenCyclicPairIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "mk" => FiniteCyclicPresentation.polygonalMk (Pcap) (valid)
local notation "step" => nielsenCoreFiniteSidePointStep hD hNE

def nielsenCappedOriginalModelPoint (p:K) : (Pcap).PolygonalRealization (valid) :=
  (mk) ⟨f₀,(E).symm p⟩
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv

theorem continuous_nielsenCappedOriginalModelPoint : Continuous (modelPoint) :=
  ((Pcap).continuous_polygonalMk (valid)).comp (continuous_sigmaMk.comp (E).symm.continuous)

theorem nielsenCappedOriginalModelPoint_side (p:K) (i:Fin J.n) (t:unitInterval)
    (hp:p.val=(γ) i t) :
    (modelPoint) p=(mk) (((Pcap).occurrenceSide
      (nielsenCappedOriginalOccurrence hD hNE hFG hfin w hwD hwN J hc hv i)).point t) := by
  apply congrArg (mk)
  change (⟨f₀,(E).symm p⟩:(Pcap).PolygonalPreRealization)=⟨f₀,PolygonCell.side (Fin.cast (hlen).symm i) t⟩
  apply congrArg (fun z:PolygonCell ((Pcap).boundary (f₀)).length=>(⟨f₀,z⟩:(Pcap).PolygonalPreRealization))
  apply (E).injective
  rw [Homeomorph.apply_symm_apply]
  apply Subtype.ext
  exact hp.trans (nielsenCappedOriginalFaceHomeomorph_side hD hNE hFG hfin w hwD hwN J hc hv i t).symm

/-- The unchanged stored first-face point corresponding to a genuine finite point of the clipped core closure. -/
def nielsenCappedOriginalFinitePoint (x:closure Q) : (Pcap).PolygonalRealization (valid) :=
  (modelPoint) ⟨Hyperbolic.discToClosedModel (P.finiteCoordinate x.val),(originalFiniteClosedModel_mem_iff x.val).mpr
    x.property⟩
local notation "finitePoint" => nielsenCappedOriginalFinitePoint hD hNE hFG hfin w hwD hwN J hc hv

theorem continuous_nielsenCappedOriginalFinitePoint : Continuous (finitePoint) := by
  apply (continuous_nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv).comp
  exact ((Hyperbolic.isEmbedding_discToClosedModel.continuous.comp P.finiteCoordinate.continuous).comp
    continuous_subtype_val).subtype_mk _

theorem nielsenCappedFiniteSideStep_word_eq (x y:closure Q) (hxy:step x.val y.val) :
    (finitePoint) x=(finitePoint) y := by
  obtain ⟨v,hx,hxy⟩:=hxy
  obtain ⟨k,hk,hxk⟩:=nielsenBoundarySide_point_mem_tagged_cyclic_edge hD hNE hFG hfin w hwD hwN J hc hv
    (Sum.inl v) (Hyperbolic.discToClosedModel (P.finiteCoordinate x.val)) hx
  let i:Fin J.n:=(index).symm k
  have hik:(index) i=k:=(index).apply_symm_apply _
  have hxγ:Hyperbolic.discToClosedModel (P.finiteCoordinate x.val)∈range ((γ) i):=by
    rw [range_nielsenCyclicSideParam,hik]
    exact hxk
  obtain ⟨t,ht⟩:=hxγ
  have hn:(finPair) i≠i:=by
    intro he
    have hne:pairIndex k≠k:=(nielsenCyclicPairIndex_paired hD hNE hFG hfin w hwD hwN J hc hv k v hk).1
    apply hne
    have hh:=congrArg (index) he
    simpa only [nielsenCyclicFinPair_index,hik] using hh
  have hyγ:Hyperbolic.discToClosedModel (P.finiteCoordinate y.val)=(γ) ((finPair) i) (unitInterval.symm t):=by
    rw [←nielsenCyclicSideParam_pair hD hNE hFG hfin w hwD hwN J hc hv i hn t]
    unfold nielsenCyclicEdgeAction
    rw [hik,hk,ht,P.compactifiedAction_finite,hxy]
  let o:=nielsenCappedOriginalOccurrence hD hNE hFG hfin w hwD hwN J hc hv i
  have hclosed:=nielsenCappedPresentation_closed hD hNE hFG hfin w hwD hwN J hc hv o.edge
  have hb:¬(Pcap).IsBoundaryEdge o.edge:=by
    change (Pcap).edgeMultiplicity o.edge≠1
    omega
  obtain ⟨p,hp⟩:=(valid).exists_pairing_source o hb
  have htarget:p.target=nielsenCappedOriginalOccurrence hD hNE hFG hfin w hwD hwN J hc hv ((finPair) i):=by
    rw [nielsenCappedBoundaryPairing_target hD hNE hFG hfin w hwD hwN J hc hv p,hp]
    dsimp only [o]
    rw [nielsenCappedOriginalOccurrence_eq_corner,
      nielsenCappedOriginalCorner_partner hD hNE hFG hfin w hwD hwN J hc hv ((index) i)
        (by intro he;apply hn;apply (index).injective;rw [nielsenCyclicFinPair_index,he]),
      nielsenCappedOriginalOccurrence_eq_corner,nielsenCyclicFinPair_index]
  have hpar:p.identification.parameter t=unitInterval.symm t:=by
    change p.direction.homeomorph t=unitInterval.symm t
    rw [nielsenCappedBoundaryPairing_direction hD hNE hFG hfin w hwD hwN J hc hv p]
    rfl
  change (modelPoint) _=(modelPoint) _
  rw [nielsenCappedOriginalModelPoint_side hD hNE hFG hfin w hwD hwN J hc hv _ i t ht.symm,
    nielsenCappedOriginalModelPoint_side hD hNE hFG hfin w hwD hwN J hc hv _ ((finPair) i) (unitInterval.symm t) hyγ]
  have he:=(Pcap).polygonalMk_pairing_eq (valid) p t
  change (mk) (((Pcap).occurrenceSide p.source).point t)=
    (mk) (((Pcap).occurrenceSide p.target).point (p.identification.parameter t)) at he
  rwa [hp,htarget,hpar] at he

/-- Full finite original orbits, including all true frontier points, are exactly identified in the actual cap word. -/
theorem nielsenCappedFiniteOrbit_word_eq (x y:closure Q) (horbit:∃g:H,g•x.val=y.val) :
    (finitePoint) x=(finitePoint) y := by
  have hc':=nielsenCore_finite_orbit_pointChain hD hNE hFG hfin w hwD hwN x.val y.val x.property y.property horbit
  have hLift {a b:P.domain.carrier} (hab:Relation.EqvGen step a b) :
      Relation.EqvGen (fuchsianSidePointStep hD) a b := by
    induction hab with
    | rel a b h =>
      obtain ⟨v,hv',rfl⟩:=h
      exact Relation.EqvGen.rel _ _ ⟨v.val.val.1,
        (mem_fuchsianSideClosedModel_finite _ a).mp (v.val.carrier_subset_original hv'.1),rfl⟩
    | refl => exact Relation.EqvGen.refl _
    | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans _ _ _ _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂
  have hmodel {a b:P.domain.carrier} (hab:Relation.EqvGen step a b) :
      ∀ha:a∈closure Q,∀hb:b∈closure Q,(finitePoint) ⟨a,ha⟩=(finitePoint) ⟨b,hb⟩:=by
    induction hab with
    | rel a b hab =>
      intro ha hb
      exact nielsenCappedFiniteSideStep_word_eq hD hNE hFG hfin w hwD hwN J hc hv ⟨a,ha⟩ ⟨b,hb⟩ hab
    | refl a => intro ha hb;rfl
    | symm a b _ ih => intro ha hb;exact (ih hb ha).symm
    | trans a b c hab _ ih ih' =>
      intro ha hc''
      have hb:b∈closure Q:=by
        have hOrb:=nielsenCore_finite_pointChain_orbit hD hNE a b hab
        obtain ⟨g,hg⟩:=hOrb
        have hbc:b∈closure D:=
          (originalFiniteSidePointChain_closure hD (hLift hab)).mp (closure_mono inter_subset_left ha)
        have hbn:b∈closure (fuchsianNielsenCore P hNE):=by
          rw [←hg,←fuchsianNielsenCore_smul_closure P hNE g]
          exact mem_smul_set.mpr ⟨a,closure_mono inter_subset_right ha,rfl⟩
        rw [nielsenCore_inter_closure_eq hD hNE w hwD hwN]
        exact ⟨hbc,hbn⟩
      exact (ih ha hb).trans (ih' hb hc'')
  exact hmodel hc' x.property y.property


/-- The complete finite first-face kernel in the genuine multiface cap realization is the actual original group orbit relation. -/
theorem nielsenCappedFinitePoint_eq_iff_orbit (x y:closure Q) :
    (finitePoint) x=(finitePoint) y↔∃g:H,g•x.val=y.val := by
  constructor
  · intro he
    have hs:=nielsenCappedOriginalFace_eq_implies_sphereOrbit hD hNE hFG hfin w hwD hwN J hc hv _ _ he
    rw [Homeomorph.apply_symm_apply,Homeomorph.apply_symm_apply] at hs
    have horb:=Quotient.exact hs
    change Hyperbolic.closedDiscToExtended (Hyperbolic.discToClosedModel (P.finiteCoordinate x.val))∈
      MulAction.orbit H (Hyperbolic.closedDiscToExtended (Hyperbolic.discToClosedModel (P.finiteCoordinate
        y.val))) at horb
    rw [originalFinitePoint_closedModel_sphere,originalFinitePoint_closedModel_sphere] at horb
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp horb
    have hxy:g•y.val=x.val:=Subtype.ext hg
    exact ⟨g⁻¹,by rw [←hxy,inv_smul_smul]⟩
  · exact nielsenCappedFiniteOrbit_word_eq hD hNE hFG hfin w hwD hwN J hc hv x y

end NielsenCappedFiniteWordKernel



section NielsenCappedFirstFaceTopology
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "E" => nielsenCappedOriginalFaceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "finitePoint" => nielsenCappedOriginalFinitePoint hD hNE hFG hfin w hwD hwN J hc hv

local instance nielsenCappedFirstFaceWordT2 : T2Space ((Pcap).PolygonalRealization (valid)) := by
  obtain ⟨g,hg,_⟩:=nielsenCappedPresentation_genus hD hNE hFG hfin w hwD hwN J hc hv
  exact Surfaces.HandleSeparation.hasTopologicalGenus_t2Space hg

local instance nielsenCappedFirstFaceModelCompact : CompactSpace K :=
  isCompact_iff_compactSpace.mp (Hyperbolic.isCompact_discClosedModelClosure _)

theorem nielsenCappedOriginalModelPoint_eq_compactifiedOrbit (p q:K)
    (he:(modelPoint) p=(modelPoint) q) :
    ∃g:H,(P.compactifiedAction g).closedMap p.val=q.val := by
  have hs:=nielsenCappedOriginalFace_eq_implies_sphereOrbit hD hNE hFG hfin w hwD hwN J hc hv _ _ he
  rw [Homeomorph.apply_symm_apply,Homeomorph.apply_symm_apply] at hs
  have horb:=Quotient.exact hs
  change Hyperbolic.closedDiscToExtended p.val∈MulAction.orbit H (Hyperbolic.closedDiscToExtended q.val) at horb
  obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp horb
  change g.val.val (Hyperbolic.closedDiscToExtended q.val)=Hyperbolic.closedDiscToExtended p.val at hg
  refine ⟨g⁻¹,?_⟩
  apply Hyperbolic.isEmbedding_closedDiscToExtended.injective
  rw [P.compactifiedAction_sphere]
  change g.val.val.symm (Hyperbolic.closedDiscToExtended p.val)=Hyperbolic.closedDiscToExtended q.val
  rw [←hg,g.val.val.symm_apply_apply]

theorem nielsenCappedOriginalModelPoint_mem_finite_range_iff (p:K) :
    (modelPoint) p∈range (finitePoint)↔‖(p.val:ℂ)‖<1 := by
  constructor
  · rintro ⟨x,hx⟩
    obtain ⟨g,hg⟩:=nielsenCappedOriginalModelPoint_eq_compactifiedOrbit hD hNE hFG hfin w hwD hwN J hc hv
      ⟨Hyperbolic.discToClosedModel (P.finiteCoordinate x.val),(originalFiniteClosedModel_mem_iff x.val).mpr
        x.property⟩ p hx
    rw [←hg]
    exact ((P.compactifiedAction g).finite_iff _).mpr (P.finiteCoordinate x.val).norm_lt_one
  · intro hp
    let z:𝔻:=Hyperbolic.closedDiscFinitePoint p.val hp
    let x:=P.finiteCoordinate.symm z
    have hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=p.val:=by
      rw [P.finiteCoordinate.apply_symm_apply]
      exact Hyperbolic.closedDiscFinitePoint_spec p.val hp
    have hxc:x∈closure Q:=(originalFiniteClosedModel_mem_iff x).mp (hx.symm ▸ p.property)
    refine ⟨⟨x,hxc⟩,?_⟩
    apply congrArg (modelPoint)
    exact Subtype.ext hx

def nielsenCappedFirstFaceIdealSet : Set K := {p | ‖(p.val:ℂ)‖=1}
local notation "I" => nielsenCappedFirstFaceIdealSet (P:=P) hNE (D:=D)

include hD hFG in
theorem nielsenCappedFirstFaceIdealSet_finite : (I).Finite := by
  have ha:=finitelyGenerated_nielsenCoreArea_ne_top P hNE hFG hD.locallyFinite.fundamental
  apply ((finite_nielsenCore_idealBoundary hD hNE ha).preimage
    (Complex.UnitClosedDisc.isEmbedding_coe.injective.comp Subtype.val_injective).injOn).subset
  intro p hp
  apply (mem_fuchsianPolygonIdealBoundary P Q (p.val:ℂ)).mpr
  refine ⟨?_,hp⟩
  have hm:=mem_closure_image Complex.UnitClosedDisc.continuous_coe.continuousAt p.property
  simp only [Hyperbolic.discClosedModelClosure,image_image] at hm
  exact hm

/-- The first-face image in the unchanged faithful cap realization. -/
def nielsenCappedFirstFaceImageMap (p:K) : ↥(range (modelPoint)) := ⟨(modelPoint) p,mem_range_self p⟩
local notation "firstMap" => nielsenCappedFirstFaceImageMap hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedFirstFaceImageMap_isQuotientMap : IsQuotientMap (firstMap) := by
  have hcont:Continuous (firstMap):=(continuous_nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc
    hv).subtype_mk _
  have hsur:Function.Surjective (firstMap):=by
    rintro ⟨_,p,rfl⟩
    exact ⟨p,rfl⟩
  exact hcont.isClosedMap.isQuotientMap hcont hsur

def nielsenCappedFirstFaceOldSet : Set ↥(range (modelPoint)) := {z | z.val∈range (finitePoint)}
local notation "O" => nielsenCappedFirstFaceOldSet hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedFirstFaceOldSet_isOpen : IsOpen (O) := by
  have hf:((modelPoint) '' I).Finite:=(nielsenCappedFirstFaceIdealSet_finite hD hNE hFG).image _
  have he:O=(Subtype.val:↥(range (modelPoint)) → (Pcap).PolygonalRealization (valid)) ⁻¹' ((modelPoint) '' I)ᶜ:=by
    ext z
    obtain ⟨p,hp⟩:=z.property
    change z.val∈range (finitePoint)↔z.val∉(modelPoint) '' I
    rw [←hp]
    constructor
    · intro hOld
      rintro ⟨q,hq,he⟩
      have hOldq: (modelPoint) q∈range (finitePoint):=he.symm ▸ hOld
      have hqn:‖(q.val:ℂ)‖<1:=(nielsenCappedOriginalModelPoint_mem_finite_range_iff hD hNE hFG hfin w hwD hwN J hc hv
        q).mp hOldq
      exact (ne_of_lt hqn) hq
    · intro hn
      apply (nielsenCappedOriginalModelPoint_mem_finite_range_iff hD hNE hFG hfin w hwD hwN J hc hv p).mpr
      by_contra hnot
      have hI:p∈I:=le_antisymm p.val.norm_le_one (le_of_not_gt hnot)
      exact hn ⟨p,hI,rfl⟩
  rw [he]
  exact hf.isClosed.isOpen_compl.preimage continuous_subtype_val


def nielsenCappedFiniteModelPoint (x:closure Q) : K :=
  ⟨Hyperbolic.discToClosedModel (P.finiteCoordinate x.val),(originalFiniteClosedModel_mem_iff x.val).mpr x.property⟩
local notation "finiteModel" => nielsenCappedFiniteModelPoint (P:=P) hNE (D:=D)

theorem nielsenCappedFiniteModelPoint_isEmbedding : Topology.IsEmbedding (finiteModel) := by
  have he:= (Hyperbolic.isEmbedding_discToClosedModel.comp P.finiteCoordinate.isEmbedding).comp
    (Topology.IsEmbedding.subtypeVal (p:=fun x:P.domain.carrier=>x∈closure Q))
  exact he.codRestrict K (fun x=>(originalFiniteClosedModel_mem_iff x.val).mpr x.property)

def nielsenCappedFirstFaceOldSourceMap (x:closure Q) : ↥((firstMap) ⁻¹' O) :=
  ⟨(finiteModel) x,⟨x,rfl⟩⟩
local notation "oldSource" => nielsenCappedFirstFaceOldSourceMap hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedFirstFaceOldSourceMap_isEmbedding : Topology.IsEmbedding (oldSource) :=
  (nielsenCappedFiniteModelPoint_isEmbedding (P:=P) (D:=D) hNE).codRestrict
    ((firstMap) ⁻¹' O) (fun x=>⟨x,rfl⟩)

theorem nielsenCappedFirstFaceOldSourceMap_surjective : Function.Surjective (oldSource) := by
  intro z
  have hn:‖(z.val.val:ℂ)‖<1:=
    (nielsenCappedOriginalModelPoint_mem_finite_range_iff hD hNE hFG hfin w hwD hwN J hc hv z.val).mp z.property
  let u:𝔻:=Hyperbolic.closedDiscFinitePoint z.val.val hn
  let x:=P.finiteCoordinate.symm u
  have hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=z.val.val:=by
    rw [P.finiteCoordinate.apply_symm_apply]
    exact Hyperbolic.closedDiscFinitePoint_spec z.val.val hn
  have hxc:x∈closure Q:=(originalFiniteClosedModel_mem_iff x).mp (hx.symm ▸ z.val.property)
  refine ⟨⟨x,hxc⟩,?_⟩
  apply Subtype.ext
  exact Subtype.ext hx

def nielsenCappedFirstFaceOldSourceHomeomorph : closure Q≃ₜ↥((firstMap) ⁻¹' O) :=
  (nielsenCappedFirstFaceOldSourceMap_isEmbedding hD hNE hFG hfin w hwD hwN J hc hv).toHomeomorphOfSurjective
    (nielsenCappedFirstFaceOldSourceMap_surjective hD hNE hFG hfin w hwD hwN J hc hv)

def nielsenCappedFirstFaceOldTargetHomeomorph : ↥O≃ₜ↥(range (finitePoint)) := by
  have hs:range (finitePoint)⊆range (Subtype.val:↥(range (modelPoint)) → (Pcap).PolygonalRealization (valid)):=by
    rintro z ⟨x,rfl⟩
    exact ⟨⟨(finitePoint) x,⟨(finiteModel) x,rfl⟩⟩,rfl⟩
  exact Topology.IsEmbedding.subtypeVal.homeomorphOfSubsetRange hs

/-- The original finite-point image with its genuine subspace topology inside the faithful capped word. -/
def nielsenCappedFiniteImageMap (x:closure Q) : ↥(range (finitePoint)) := ⟨(finitePoint) x,mem_range_self x⟩
local notation "oldMap" => nielsenCappedFiniteImageMap hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedFiniteImageMap_isQuotientMap : IsQuotientMap (oldMap) := by
  have hcomp: (oldMap)=
      nielsenCappedFirstFaceOldTargetHomeomorph hD hNE hFG hfin w hwD hwN J hc hv ∘
      (O).restrictPreimage (firstMap) ∘
      nielsenCappedFirstFaceOldSourceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv :=rfl
  rw [hcomp]
  exact (nielsenCappedFirstFaceOldTargetHomeomorph hD hNE hFG hfin w hwD hwN J hc hv).isQuotientMap.comp
    (((nielsenCappedFirstFaceImageMap_isQuotientMap hD hNE hFG hfin w hwD hwN J hc hv).restrictPreimage_isOpen
      (nielsenCappedFirstFaceOldSet_isOpen hD hNE hFG hfin w hwD hwN J hc hv)).comp
        (nielsenCappedFirstFaceOldSourceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv).isQuotientMap)

theorem nielsenCappedFiniteImageMap_kernel (x y:closure Q) :
    nielsenCoreFiniteSidePointSetoid hD hNE x y↔(oldMap) x=(oldMap) y := by
  change Relation.EqvGen (nielsenCoreFiniteSidePointStep hD hNE) x.val y.val↔(oldMap) x=(oldMap) y
  rw [nielsenCore_finite_pointChain_iff_orbit hD hNE hFG hfin w hwD hwN x.val y.val x.property y.property]
  constructor
  · intro h
    exact Subtype.ext (nielsenCappedFiniteOrbit_word_eq hD hNE hFG hfin w hwD hwN J hc hv x y h)
  · intro h
    exact (nielsenCappedFinitePoint_eq_iff_orbit hD hNE hFG hfin w hwD hwN J hc hv x y).mp (congrArg Subtype.val h)

/-- The finite part of the literal first-face image is naturally homeomorphic to the unchanged whole-group image of the true closed Nielsen region. -/
def nielsenCappedFirstFaceFiniteOrbitHomeomorph :
    ↥(range (finitePoint))≃ₜ↥((Surfaces.mobiusDomainProjection P.domain) '' closure (fuchsianNielsenCore P hNE)) :=
  ((Homeomorph.Quotient.congrRight
    (nielsenCappedFiniteImageMap_kernel hD hNE hFG hfin w hwD hwN J hc hv)).trans
      (Topology.IsQuotientMap.homeomorph
        (f:=⟨(oldMap),(continuous_nielsenCappedOriginalFinitePoint hD hNE hFG hfin w hwD hwN J hc hv).subtype_mk _⟩)
        (nielsenCappedFiniteImageMap_isQuotientMap hD hNE hFG hfin w hwD hwN J hc hv))).symm.trans
    (nielsenCoreFiniteSidePointQuotientHomeomorph hD hNE hFG hfin w hwD hwN)

end NielsenCappedFirstFaceTopology



section NielsenCappedCoreCompletion
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "firstMap" => nielsenCappedFirstFaceImageMap hD hNE hFG hfin w hwD hwN J hc hv

include hD hFG in
/-- Every ideal point of the actual compact clipped core is a genuine original cusp; this is derived from finite generation and the actual Dirichlet-polygon approximation theorem. -/
theorem nielsenCoreClosedModel_cusp_admissible (p:K) :
    Hyperbolic.closedDiscToExtended p.val∈P.asFuchsianDisc.carrier∨
      ∃(c:FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic)(g:H),
        g.val.val (fuchsianParabolicPointRepresentative P.asFuchsianDisc c).val=Hyperbolic.closedDiscToExtended p.val := by
  by_cases hp:‖(p.val:ℂ)‖<1
  · exact Or.inl ⟨(p.val:ℂ),hp,rfl⟩
  · have hn:‖(p.val:ℂ)‖=1:=le_antisymm p.val.norm_le_one (le_of_not_gt hp)
    have hξQ:(p.val:ℂ)∈fuchsianPolygonIdealBoundary P Q:=by
      apply (mem_fuchsianPolygonIdealBoundary P Q _).mpr
      refine ⟨?_,hn⟩
      have hm:=mem_closure_image Complex.UnitClosedDisc.continuous_coe.continuousAt p.property
      simp only [Hyperbolic.discClosedModelClosure,image_image] at hm
      exact hm
    have hξD:(p.val:ℂ)∈fuchsianPolygonIdealBoundary P D:=
      inter_subset_inter_left _ (closure_mono (image_mono inter_subset_left)) hξQ
    have hΛ:=nielsenCore_inter_idealBoundary_subset_limit P hNE D (p.val:ℂ) hξQ
    have hcl:=((mem_fuchsianPolygonIdealBoundary_iff_extendedClosure P D (p.val:ℂ)).mp hξD).2
    obtain ⟨f,hf,hfix⟩:=finitelyGenerated_polygon_ideal_limit_parabolic P hFG hD
      ((p.val:ℂ):Mobius.ExtendedComplex) hcl hΛ hNE
    let x:fuchsianCyclicFixedPoints P.asFuchsianDisc .parabolic:=⟨Hyperbolic.closedDiscToExtended p.val,by
      constructor
      · intro he
        cases he
      · exact ⟨f.val,f.property,hf,hfix⟩⟩
    exact Or.inr (fuchsianParabolicPointRepresentative_orbit_cover P.asFuchsianDisc x)

variable {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "hull" => originalFiniteClosedHull 1 S.vertices
local notation "sphereE" => originalPolygonClosedModelSphereHomeomorph P Q 1 S hr

include hD hNE hFG hr in
theorem nielsenCoreActualHull_cusp_admissible :
    ∀z∈hull,z∈P.asFuchsianDisc.carrier∨
      ∃(c:FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic)(g:H),
        g.val.val (fuchsianParabolicPointRepresentative P.asFuchsianDisc c).val=z := by
  rintro z ⟨p,hp,rfl⟩
  have hpK:p∈K:=by
    rw [←finite_cyclic_hull_eq_polygon_closedModel P Q S hr]
    exact hp
  exact nielsenCoreClosedModel_cusp_admissible hD hNE hFG ⟨p,hpK⟩
local notation "hullAdmissible" => nielsenCoreActualHull_cusp_admissible hD hNE hFG S hr

/-- The unchanged compact clipped polygon maps into the original group's unique genuine cusp completion. -/
def nielsenCoreClosedModelCompletionMap : K → FuchsianCuspCompletion P.asFuchsianDisc :=
  fuchsianCuspSubsetProjection P.asFuchsianDisc hull (hullAdmissible) ∘ sphereE
local notation "projection" => nielsenCoreClosedModelCompletionMap hD hNE hFG S hr

theorem continuous_nielsenCoreClosedModelCompletionMap : Continuous (projection) := by
  apply (fuchsianCuspSubsetProjection_continuous P.asFuchsianDisc hull (hullAdmissible) _).comp (sphereE).continuous
  exact originalFiniteClosedHull_cusp_bounds P.asFuchsianDisc 1 (by
    change (fun z:Mobius.ExtendedComplex=>z) '' Hyperbolic.extendedUnitDisc=Hyperbolic.extendedUnitDisc
    exact image_id' Hyperbolic.extendedUnitDisc) S.vertices

theorem nielsenCoreClosedModelCompletionMap_compactified_orbit (p q:K)
    (g:H) (hg:(P.compactifiedAction g).closedMap p.val=q.val) :
    (projection) p=(projection) q := by
  apply Eq.symm
  apply (fuchsianCuspSubsetProjection_eq_iff P.asFuchsianDisc hull (hullAdmissible) ((sphereE) q) ((sphereE) p)).mpr
  refine ⟨g,?_⟩
  change g.val.val (Hyperbolic.closedDiscToExtended p.val)=Hyperbolic.closedDiscToExtended q.val
  rw [←P.compactifiedAction_sphere,hg]

/-- The actual original completion projection respects the complete kernel of the unchanged first-face quotient. -/
theorem nielsenCoreClosedModelCompletionMap_word_fiber (p q:K) (he:(modelPoint) p=(modelPoint) q) :
    (projection) p=(projection) q := by
  obtain ⟨g,hg⟩:=nielsenCappedOriginalModelPoint_eq_compactifiedOrbit hD hNE hFG hfin w hwD hwN J hc hv p q he
  exact nielsenCoreClosedModelCompletionMap_compactified_orbit hD hNE hFG S hr p q g hg

/-- The actual first-face image, retaining its original topology, maps continuously into the same original group's cusp completion. -/
def nielsenCappedFirstFaceCompletionMap (z:↥(range (modelPoint))) : FuchsianCuspCompletion P.asFuchsianDisc :=
  (projection) (Classical.choose z.property)
local notation "completionMap" => nielsenCappedFirstFaceCompletionMap hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenCappedFirstFaceCompletionMap_cover (p:K) :
    (completionMap) ((firstMap) p)=(projection) p := by
  exact nielsenCoreClosedModelCompletionMap_word_fiber hD hNE hFG hfin w hwD hwN J hc hv S hr
    (Classical.choose ((firstMap) p).property) p (Classical.choose_spec ((firstMap) p).property)

theorem continuous_nielsenCappedFirstFaceCompletionMap : Continuous (completionMap) := by
  apply (nielsenCappedFirstFaceImageMap_isQuotientMap hD hNE hFG hfin w hwD hwN J hc hv).continuous_iff.mpr
  have he:(completionMap) ∘ (firstMap)=(projection):=
    funext (nielsenCappedFirstFaceCompletionMap_cover hD hNE hFG hfin w hwD hwN J hc hv S hr)
  rw [he]
  exact continuous_nielsenCoreClosedModelCompletionMap hD hNE hFG S hr


/-- Old finite original representatives are unchanged by the actual clipped-core completion projection. -/
theorem nielsenCoreClosedModelCompletionMap_finite (x:closure Q) :
    (projection) (nielsenCappedFiniteModelPoint hNE x)=
      fuchsianCuspCompletionOld P.asFuchsianDisc (Surfaces.mobiusDomainProjection P.domain x.val) := by
  apply congrArg (Quotient.mk _)
  apply Subtype.ext
  exact originalFinitePoint_closedModel_sphere P x.val

/-- The actual completion projection introduces no finite-versus-ideal ambiguity. -/
theorem nielsenCoreClosedModelCompletionMap_mem_old_iff (p:K) :
    (projection) p∈range (fuchsianCuspCompletionOld P.asFuchsianDisc)↔‖(p.val:ℂ)‖<1 := by
  change fuchsianCuspSubsetProjection P.asFuchsianDisc hull (hullAdmissible) ((sphereE) p)∈
    range (fuchsianCuspCompletionOld P.asFuchsianDisc)↔_
  rw [originalCuspSubsetProjection_mem_old_iff]
  exact Hyperbolic.coe_mem_extendedUnitDisc _

/-- The genuine first-face completion map takes precisely its genuine finite part into the unchanged original quotient. -/
theorem nielsenCappedFirstFaceCompletionMap_mem_old_iff (z:↥(range (modelPoint))) :
    (completionMap) z∈range (fuchsianCuspCompletionOld P.asFuchsianDisc)↔
      z.val∈range (nielsenCappedOriginalFinitePoint hD hNE hFG hfin w hwD hwN J hc hv) := by
  obtain ⟨p,hp⟩:=z.property
  have he:z=(firstMap) p:=Subtype.ext hp.symm
  rw [he,nielsenCappedFirstFaceCompletionMap_cover,nielsenCoreClosedModelCompletionMap_mem_old_iff]
  exact (nielsenCappedOriginalModelPoint_mem_finite_range_iff hD hNE hFG hfin w hwD hwN J hc hv p).symm

end NielsenCappedCoreCompletion


/-- Every genuine bounded ordinary gap has width at most the absolute
translation period of the actual original limit set. -/
theorem nielsen_bounded_gap_width_le_translation
    (K : Subgroup Mobius.complexMobiusGroup) (t : ℝ) (ht : t≠0)
    (hT : DiscreteGroups.mobiusTranslation (t:ℂ)∈K)
    (hinf : (∞:Mobius.ExtendedComplex)∈DiscreteGroups.mobiusLimitSet K)
    (a b : ℝ) (hab : a<b)
    (hG : (Hyperbolic.NielsenHalfPlaneGap.bounded a b hab).carrier∈
      Auxiliary.Topology.nielsenRealGapFamily (Hyperbolic.nielsenHalfPlaneRealSet (DiscreteGroups.mobiusLimitSet K))) :
    b-a≤|t| :=by
  have hpos : DiscreteGroups.mobiusTranslation ((|t|:ℝ):ℂ)∈K:=by
    by_cases hp : 0≤t
    · simpa only [abs_of_nonneg hp] using hT
    · have hn : t<0:=lt_of_not_ge hp
      simpa only [abs_of_neg hn,Complex.ofReal_neg,DiscreteGroups.mobiusTranslation_neg] using K.inv_mem hT
  have hGArc : Hyperbolic.nielsenRealBoundaryPoint '' (Hyperbolic.NielsenHalfPlaneGap.bounded a b hab).carrier∈
      Hyperbolic.nielsenHalfPlaneArcFamily (DiscreteGroups.mobiusLimitSet K):=by
    rw [Hyperbolic.nielsenHalfPlaneArcFamily_eq_realGapImage _ hinf]
    exact ⟨_,hG,rfl⟩
  have hend:=nielsen_gap_idealEndpoints_limit_subset _ hinf
    (Hyperbolic.NielsenHalfPlaneGap.bounded a b hab) hGArc
  have ha : Hyperbolic.nielsenRealBoundaryPoint a∈DiscreteGroups.mobiusLimitSet K:=by
    apply hend
    rw [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints]
    exact mem_insert _ _
  have hbp:=DiscreteGroups.mobiusLimitSet_invariant K ⟨DiscreteGroups.mobiusTranslation ((|t|:ℝ):ℂ),hpos⟩ ha
  have hbad : a+|t|∈Hyperbolic.nielsenHalfPlaneRealSet (DiscreteGroups.mobiusLimitSet K):=by
    change Hyperbolic.nielsenRealBoundaryPoint (a+|t|)∈DiscreteGroups.mobiusLimitSet K
    convert hbp using 1
    change (((a+|t|:ℝ):ℂ):Mobius.ExtendedComplex)=
      (DiscreteGroups.mobiusTranslation ((|t|:ℝ):ℂ)).val ((a:ℂ):Mobius.ExtendedComplex)
    rw [DiscreteGroups.mobiusTranslation_coe]
    congr 1
    push_cast
    ring
  have hsub : (Hyperbolic.NielsenHalfPlaneGap.bounded a b hab).carrier⊆
      (Hyperbolic.nielsenHalfPlaneRealSet (DiscreteGroups.mobiusLimitSet K))ᶜ:=by
    obtain ⟨x,_hx,hxG⟩:=hG
    rw [hxG]
    exact connectedComponentIn_subset _ _
  by_contra hwidth
  have hw : |t|<b-a:=lt_of_not_ge hwidth
  exact hsub (show a+|t|∈Ioo a b from
    ⟨by linarith only [abs_pos.mpr ht],by linarith only [hw]⟩) hbad

/-- A true nonzero parabolic translation puts the entire corresponding high
half-plane inside the original Nielsen region. The estimate is derived from
the actual whole limit set and all its actual complementary gaps. -/
theorem nielsenRealArcRegion_contains_translation_tail
    (K : Subgroup Mobius.complexMobiusGroup) (t : ℝ) (ht : t≠0)
    (hT : DiscreteGroups.mobiusTranslation (t:ℂ)∈K)
    (hinf : (∞:Mobius.ExtendedComplex)∈DiscreteGroups.mobiusLimitSet K)
    (z : ℍ) (hz : |t|/2<z.im) :
    z∈Hyperbolic.nielsenRealArcRegion (Hyperbolic.nielsenHalfPlaneRealSet (DiscreteGroups.mobiusLimitSet K)) :=by
  intro G hG
  have hNo:=nielsen_gap_infty_not_endpoint_of_translation K t ht hT hinf G hG
  cases G with
  | bounded a b hab =>
    have hw:=nielsen_bounded_gap_width_le_translation K t ht hT hinf a b hab hG
    have hws : (b-a)^2≤|t|^2:=
      (sq_le_sq₀ (sub_pos.mpr hab).le (abs_nonneg t)).mpr hw
    have hheight : |t|^2<(2*z.im)^2:=
      (sq_lt_sq₀ (abs_nonneg t) (by positivity)).mpr (by linarith only [hz])
    have hprod : 4*(z.re-a)*(b-z.re)≤(b-a)^2:=by
      nlinarith only [sq_nonneg (2*z.re-a-b)]
    change (z.re-a)*(b-z.re)<z.im^2
    nlinarith only [hws,hheight,hprod]
  | left b =>
    exact (hNo (by simp [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints])).elim
  | right a =>
    exact (hNo (by simp [Hyperbolic.NielsenHalfPlaneGap.idealEndpoints])).elim



/-- Every real translation tail in a genuine original whole-disc parabolic chart lies in the source-defined Nielsen region. -/
theorem nielsenRegion_contains_normalized_translation_tail
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (q:Mobius.complexMobiusGroup)
    (hq:q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (t:ℝ) (ht:t≠0) (hT:DiscreteGroups.mobiusTranslation (t:ℂ)∈DiscreteGroups.Action.Actions.subgroupConjugate q H) :
    nielsenModelSet q {z:ℍ | |t|/2<z.im}⊆D.nielsenRegion hNE := by
  let K:=DiscreteGroups.Action.Actions.subgroupConjugate q H
  have hp:Mobius.MobiusParabolic (DiscreteGroups.mobiusTranslation (t:ℂ)):=
    (DiscreteGroups.mobiusTranslation_parabolic_iff _).mpr (by exact_mod_cast ht)
  have hinf:(∞:Mobius.ExtendedComplex)∈DiscreteGroups.mobiusLimitSet K:=
    DiscreteGroups.mobius_parabolic_fixed_mem_limitSet K (hNE.conjugation q) ⟨DiscreteGroups.mobiusTranslation
      (t:ℂ),hT⟩ hp ∞ (DiscreteGroups.mobiusTranslation_infty _)
  have hreg:D.nielsenRegion hNE=nielsenRegionInChart H q:=
    D.nielsenRegionInChart_independent (D.nielsenArcNormalizer hNE) q
      (D.nielsenArcNormalizer_image hNE) hq hNE (D.nielsenArcNormalizer_limit hNE) hinf
  rw [hreg,nielsenRegionInChart,Hyperbolic.nielsenHalfPlaneArcRegion_eq_realArcRegion _ hinf]
  rintro x ⟨p,⟨z,hz,rfl⟩,rfl⟩
  exact ⟨Hyperbolic.extendedHalfPlanePoint z,⟨z,nielsenRealArcRegion_contains_translation_tail K t ht hT hinf z
    hz,rfl⟩,rfl⟩

/-- An unchanged genuine cusp normalization has a high horocyclic tail inside the actual original Nielsen region, even for second-kind groups and elliptic ambient groups. -/
theorem cuspNormalization_original_nielsen_tail
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H)
    (hNE:DiscreteGroups.IsNonElementary H)
    {S:Surfaces.MobiusStableSubset D.domain}
    {p:Mobius.ExtendedComplex}
    (C:Surfaces.MobiusCuspNormalization S p) :
    ∃r:ℝ,∀z:ℂ,r<z.im→C.normalizer.val.symm (z:Mobius.ExtendedComplex)∈D.nielsenRegion hNE := by
  obtain ⟨h,hD,_hh⟩:=cuspNormalization_original_domain_upper D C
  let shift:=DiscreteGroups.mobiusTranslation (-(h:ℂ)*Complex.I)
  let q:=shift*C.normalizer
  have hq:q.val '' D.carrier=Hyperbolic.openHalfPlaneSet:=by
    change ((fun z=>shift.val (C.normalizer.val z)) '' D.carrier)=_
    rw [←image_image,hD]
    exact vertical_cusp_shift_image h
  have hT:DiscreteGroups.mobiusTranslation (1:ℂ)∈DiscreteGroups.Action.Actions.subgroupConjugate q H:=by
    obtain ⟨f,hf,hCf⟩:=(DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff C.normalizer H
      _).mp C.normalized_translation_mem
    apply (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr
    refine ⟨f,hf,?_⟩
    calc
      q*f*q⁻¹=shift*(C.normalizer*f*C.normalizer⁻¹)*shift⁻¹:=by dsimp only [q];group
      _=shift*DiscreteGroups.mobiusTranslation 1*shift⁻¹:=by rw [hCf]
      _=DiscreteGroups.mobiusTranslation 1:=by
        dsimp only [shift]
        rw [←DiscreteGroups.mobiusTranslation_neg,←DiscreteGroups.mobiusTranslation_add,←DiscreteGroups.mobiusTranslation_add]
        congr 1
        ring
  have htail:=nielsenRegion_contains_normalized_translation_tail D hNE q hq 1 one_ne_zero hT
  refine ⟨h+1/2,?_⟩
  intro z hz
  have hIm:(z-(h:ℂ)*Complex.I).im=z.im-h:=by simp
  let w:ℍ:=⟨z-(h:ℂ)*Complex.I,by rw [hIm];linarith⟩
  have hw:(1:ℝ)/2<w.im:=by change 1/2<(z-(h:ℂ)*Complex.I).im;rw [hIm];linarith
  have hwp:w∈{w:ℍ | |(1:ℝ)|/2<w.im}:=by
    change |(1:ℝ)|/2<w.im
    simpa only [abs_one] using hw
  apply htail
  refine ⟨Hyperbolic.extendedHalfPlanePoint w,⟨w,hwp,rfl⟩,?_⟩
  apply q.val.injective
  change q.val (q.val.symm (Hyperbolic.extendedHalfPlanePoint w))=_
  rw [q.val.apply_symm_apply]
  change Hyperbolic.extendedHalfPlanePoint w=(DiscreteGroups.mobiusTranslation (-(h:ℂ)*Complex.I)).val
    (C.normalizer.val (C.normalizer.val.symm (z:Mobius.ExtendedComplex)))
  rw [C.normalizer.val.apply_symm_apply,DiscreteGroups.mobiusTranslation_coe]
  change ((z-(h:ℂ)*Complex.I:ℂ):Mobius.ExtendedComplex)=((z+(-(h:ℂ)*Complex.I):ℂ):Mobius.ExtendedComplex)
  congr 1
  ring



/-- The original closed Nielsen quotient, with exactly the original actual parabolic cusp points adjoined inside the unchanged completion. -/
def nielsenCompletedCoreSet
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H) : Set (FuchsianCuspCompletion P.asFuchsianDisc) :=
  (fuchsianCuspCompletionOld P.asFuchsianDisc) ''
    ((Surfaces.mobiusDomainProjection P.domain) '' closure (fuchsianNielsenCore P hNE)) ∪
      range (fuchsianCuspCompletionPoint P.asFuchsianDisc)

/-- Each original actual cusp has a genuine ambient completion neighborhood entirely inside the actual completed Nielsen core. -/
theorem nielsenCompletedCoreSet_cusp_mem_interior
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (c:FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) :
    fuchsianCuspCompletionPoint P.asFuchsianDisc c∈interior (nielsenCompletedCoreSet P hNE) := by
  let D₀:=P.asFuchsianDisc
  let C:=fuchsianCuspChartNormalization D₀
  obtain ⟨r,hr⟩:=cuspNormalization_original_nielsen_tail D₀ hNE (C c)
  let t:=max r (C c).height+1
  have ht:(C c).height<t:=lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  have hrt:r<t:=lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  let U:Set (FuchsianCuspCompletion D₀):=
    (Quotient.mk (MulAction.orbitRel H (Surfaces.MultipleCuspAugmentedDomain C))) ''
      (Surfaces.multipleCuspAugmentedPiece C c '' Surfaces.mobiusCuspAugmentedHeightTail (C c) 1 t)
  have hU:IsOpen U:=by
    apply (MulAction.isOpenQuotientMap_quotientMk (Γ:=H) (T:=Surfaces.MultipleCuspAugmentedDomain C)).isOpenMap
    apply (Surfaces.multipleCuspAugmentedPiece_isOpenEmbedding C D₀.discontinuous
      (fuchsianParabolicPointRepresentative_orbits_distinct D₀) c).isOpenMap
    rw [Surfaces.mobiusCuspAugmentedHeightTail_eq_image (C c) 1 t ht]
    exact ((C c).cusp_isOpenEmbedding D₀.discontinuous (fuchsianCuspChart_full_stabilizer D₀ c) 1).isOpenMap _
      (Surfaces.stableCuspCompletionTail_isOpen _ _)
  have hc:fuchsianCuspCompletionPoint D₀ c∈U:=by
    refine ⟨Surfaces.multipleCuspAugmentedPiece C c
      (Surfaces.mobiusCuspAugmentedCusp (C c) 1 (Surfaces.stableCuspCompletionInfinity (C c).height)),?_,?_⟩
    · exact ⟨_,Or.inl rfl,rfl⟩
    · exact Surfaces.multipleCuspNewPoint_projection C c 1
  apply mem_interior.mpr
  refine ⟨U,?_,hU,hc⟩
  rintro z ⟨_,⟨a,ha,rfl⟩,rfl⟩
  rcases (C c).heightTail_one_cases t a ha with hai|hai
  · right
    have he:a=Surfaces.mobiusCuspAugmentedCusp (C c) 1 (Surfaces.stableCuspCompletionInfinity (C c).height):=by
      apply Subtype.ext
      exact hai
    rw [he,Surfaces.multipleCuspNewPoint_projection]
    exact mem_range_self c
  · have haD:a.val∈D₀.carrier:=(C c).finiteTail_subset_domain t ht.le hai
    obtain ⟨v,hv,hva⟩:=hai
    have he:(C c).normalizer.val.symm (v:Mobius.ExtendedComplex)=a.val:=by
      rw [hva,Equiv.symm_apply_apply]
    have hN:a.val∈D₀.nielsenRegion hNE:=he ▸ hr v (hrt.trans hv)
    let x:P.domain.carrier:=⟨a.val,haD⟩
    left
    refine ⟨Surfaces.mobiusDomainProjection P.domain x,⟨x,subset_closure hN,rfl⟩,?_⟩
    apply congrArg (Quotient.mk _)
    apply Subtype.ext
    rfl





section NielsenCompletedCoreRange
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
local notation "Q" => D∩fuchsianNielsenCore P hNE
variable {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "projection" => nielsenCoreClosedModelCompletionMap hD hNE hFG S hr
local notation "finiteModel" => nielsenCappedFiniteModelPoint (P:=P) (D:=D) hNE
local notation "old" => fuchsianCuspCompletionOld P.asFuchsianDisc
local notation "oldCore" => (old) '' ((Surfaces.mobiusDomainProjection P.domain) '' closure (fuchsianNielsenCore P hNE))

local instance nielsenCompletedCoreRangeT2 : T2Space (FuchsianCuspCompletion P.asFuchsianDisc) :=
  fuchsianCuspCompletion_t2Space P.asFuchsianDisc
local instance nielsenCompletedCoreRangeModelCompact : CompactSpace K :=
  isCompact_iff_compactSpace.mp (Hyperbolic.isCompact_discClosedModelClosure _)

include hD in
theorem nielsenCoreClosedModelCompletionMap_finite_range
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) :
    range ((projection) ∘ (finiteModel))=oldCore := by
  apply subset_antisymm
  · rintro _ ⟨x,rfl⟩
    exact ⟨Surfaces.mobiusDomainProjection P.domain x.val,
      ⟨x.val,closure_mono inter_subset_right x.property,rfl⟩,
      (nielsenCoreClosedModelCompletionMap_finite hD hNE hFG S hr x).symm⟩
  · rintro _ ⟨y,hy,rfl⟩
    obtain ⟨x,hx⟩:=nielsenCoreClosedProjection_surjective hD hNE w hwD hwN ⟨y,hy⟩
    refine ⟨x,?_⟩
    rw [Function.comp_apply,nielsenCoreClosedModelCompletionMap_finite]
    exact congrArg (old) (congrArg Subtype.val hx)

theorem nielsenCoreClosedModelCompletionMap_range_isClosed : IsClosed (range (projection)) :=
  (isCompact_range (continuous_nielsenCoreClosedModelCompletionMap hD hNE hFG S hr)).isClosed

include hD in
theorem nielsenCoreClosedModelCompletionMap_oldCore_subset
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) :
    oldCore⊆range (projection) := by
  rw [←nielsenCoreClosedModelCompletionMap_finite_range hD hNE hFG S hr w hwD hwN]
  exact range_comp_subset_range _ _

include hD in
/-- Every actual original cusp belongs to the completion image of the true clipped core, by a genuine high-height path inside that core. -/
theorem nielsenCoreClosedModelCompletionMap_cusp_mem_range
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
    (c:FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) :
    fuchsianCuspCompletionPoint P.asFuchsianDisc c∈range (projection) := by
  let D₀:=P.asFuchsianDisc
  let C:=fuchsianCuspChartNormalization D₀ c
  let z:ℕ→ℂ:=fun k=>⟨0,C.height+1+(k:ℝ)⟩
  have hz:∀k,C.height<(z k).im:=by
    intro k
    change C.height<C.height+1+(k:ℝ)
    have hk:(0:ℝ)≤(k:ℝ):=Nat.cast_nonneg k
    linarith
  let p:ℕ→P.domain.carrier:=fun k=>⟨C.normalizer.val.symm (z k:Mobius.ExtendedComplex),
    C.finiteTail_subset_domain C.height le_rfl ⟨z k,hz k,by
      change (z k:Mobius.ExtendedComplex)=C.normalizer.val (C.normalizer.val.symm (z k:Mobius.ExtendedComplex))
      exact (C.normalizer.val.apply_symm_apply _).symm⟩⟩
  have hcoord:∀k,C.normalizer.val ((1:H).val.val.symm (p k).val)=(z k:Mobius.ExtendedComplex):=by
    intro k
    change C.normalizer.val (C.normalizer.val.symm (z k:Mobius.ExtendedComplex))=(z k:Mobius.ExtendedComplex)
    exact C.normalizer.val.apply_symm_apply _
  have hzim:Tendsto (fun k=>(z k).im) atTop atTop:=by
    change Tendsto (fun k:ℕ=>C.height+1+(k:ℝ)) atTop atTop
    exact tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hlim:=fuchsianCuspCompletionOld_tendsto_of_height D₀ c 1 p z hcoord hzim
  obtain ⟨r,htail⟩:=cuspNormalization_original_nielsen_tail D₀ hNE C
  have hevent:∀ᶠk in atTop,(old) (Surfaces.mobiusDomainProjection P.domain (p k))∈range (projection):=by
    filter_upwards [hzim.eventually_gt_atTop r] with k hk
    have hN:(p k).val∈D₀.nielsenRegion hNE:=htail (z k) hk
    apply nielsenCoreClosedModelCompletionMap_oldCore_subset hD hNE hFG S hr w hwD hwN
    exact ⟨Surfaces.mobiusDomainProjection P.domain (p k),⟨p k,subset_closure hN,rfl⟩,rfl⟩
  exact (nielsenCoreClosedModelCompletionMap_range_isClosed hD hNE hFG S hr).mem_of_tendsto hlim hevent

include hD in
/-- The true compact clipped polygon projects onto exactly the original closed Nielsen quotient with the actual original cusps adjoined. -/
theorem nielsenCoreClosedModelCompletionMap_range
    (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE) :
    range (projection)=nielsenCompletedCoreSet P hNE := by
  apply subset_antisymm
  · rintro y ⟨p,rfl⟩
    by_cases hp:‖(p.val:ℂ)‖<1
    · left
      let z:𝔻:=Hyperbolic.closedDiscFinitePoint p.val hp
      let x:=P.finiteCoordinate.symm z
      have hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=p.val:=by
        rw [P.finiteCoordinate.apply_symm_apply]
        exact Hyperbolic.closedDiscFinitePoint_spec p.val hp
      have hxc:x∈closure Q:=(originalFiniteClosedModel_mem_iff x).mp (hx.symm ▸ p.property)
      have hpf:(finiteModel) ⟨x,hxc⟩=p:=Subtype.ext hx
      rw [←hpf,←nielsenCoreClosedModelCompletionMap_finite_range hD hNE hFG S hr w hwD hwN]
      exact ⟨⟨x,hxc⟩,rfl⟩
    · have hn:(projection) p∉range (old):=by
        rwa [nielsenCoreClosedModelCompletionMap_mem_old_iff]
      exact Or.inr ((fuchsianCuspCompletion_old_or_cusp P.asFuchsianDisc ((projection) p)).resolve_left hn |>.imp
        (fun c hc=>hc.symm))
  · rintro y (hOld|⟨c,rfl⟩)
    · exact nielsenCoreClosedModelCompletionMap_oldCore_subset hD hNE hFG S hr w hwD hwN hOld
    · exact nielsenCoreClosedModelCompletionMap_cusp_mem_range hD hNE hFG S hr w hwD hwN c

end NielsenCompletedCoreRange



section NielsenCompletedCoreOldHomeomorph
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "firstMap" => nielsenCappedFirstFaceImageMap hD hNE hFG hfin w hwD hwN J hc hv
local notation "finitePoint" => nielsenCappedOriginalFinitePoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "finiteModel" => nielsenCappedFiniteModelPoint (P:=P) (D:=D) hNE
local notation "oldMap" => nielsenCappedFiniteImageMap hD hNE hFG hfin w hwD hwN J hc hv
local notation "O" => nielsenCappedFirstFaceOldSet hD hNE hFG hfin w hwD hwN J hc hv
local notation "old" => fuchsianCuspCompletionOld P.asFuchsianDisc
local notation "coreImage" => (Surfaces.mobiusDomainProjection P.domain) '' closure (fuchsianNielsenCore P hNE)
local notation "oldCore" => (old) '' coreImage
local notation "Y" => {y:FuchsianCuspCompletion P.asFuchsianDisc // y∈nielsenCompletedCoreSet P hNE}

/-- The finite first-face homeomorphism retains each literal original representative. -/
theorem nielsenCappedFirstFaceFiniteOrbitHomeomorph_projection (x:closure Q) :
    nielsenCappedFirstFaceFiniteOrbitHomeomorph hD hNE hFG hfin w hwD hwN J hc hv ((oldMap) x)=
      nielsenCoreClosedProjection hNE x := by
  let A:Quotient (nielsenCoreFiniteSidePointSetoid hD hNE)≃ₜ↥(range (finitePoint)):=
    (Homeomorph.Quotient.congrRight
      (nielsenCappedFiniteImageMap_kernel hD hNE hFG hfin w hwD hwN J hc hv)).trans
        (Topology.IsQuotientMap.homeomorph
          (f:=⟨(oldMap),(continuous_nielsenCappedOriginalFinitePoint hD hNE hFG hfin w hwD hwN J hc hv).subtype_mk _⟩)
          (nielsenCappedFiniteImageMap_isQuotientMap hD hNE hFG hfin w hwD hwN J hc hv))
  have hA:A (Quotient.mk _ x)=(oldMap) x:=rfl
  change nielsenCoreFiniteSidePointQuotientHomeomorph hD hNE hFG hfin w hwD hwN (A.symm ((oldMap) x))=_
  rw [←hA,A.symm_apply_apply]
  rfl

/-- The true old part of the completed Nielsen core, as an actual subspace of the unchanged completion. -/
def nielsenCompletedCoreOldSet : Set Y := {y | y.val∈range (old)}
local notation "T" => nielsenCompletedCoreOldSet (P:=P) hNE

theorem nielsenCompletedCore_old_iff (y:FuchsianCuspCompletion P.asFuchsianDisc) :
    y∈nielsenCompletedCoreSet P hNE ∧y∈range (old)↔y∈oldCore := by
  constructor
  · rintro ⟨h,hOld⟩
    rcases h with h|⟨c,rfl⟩
    · exact h
    · exact False.elim (fuchsianCuspCompletionPoint_not_mem_old P.asFuchsianDisc c hOld)
  · intro h
    refine ⟨Or.inl h,?_⟩
    obtain ⟨z,_hz,rfl⟩:=h
    exact mem_range_self z

/-- The natural old-part inclusion has the original subspace topology; no new quotient topology is assigned. -/
def nielsenCompletedCoreOldForgetHomeomorph : ↥T≃ₜ↥oldCore := by
  have hEmb:Topology.IsEmbedding (fun y:↥T=>y.val.val):=
    Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
  have hrange:range (fun y:↥T=>y.val.val)=oldCore:=by
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      exact (nielsenCompletedCore_old_iff hNE z.val.val).mp ⟨z.val.property,z.property⟩
    · intro hy
      have h:=(nielsenCompletedCore_old_iff hNE y).mpr hy
      exact ⟨⟨⟨y,h.1⟩,h.2⟩,rfl⟩
  exact hEmb.toHomeomorph.trans (Homeomorph.setCongr hrange)

theorem nielsenCompletedCoreOldForgetHomeomorph_symm_coe (z:oldCore) :
    ((nielsenCompletedCoreOldForgetHomeomorph hNE).symm z).val.val=z.val := by
  exact congrArg Subtype.val ((nielsenCompletedCoreOldForgetHomeomorph hNE).apply_symm_apply z)

/-- The genuine finite part of the faithful first-face image is homeomorphic to the genuine old part of the original completed Nielsen quotient. -/
def nielsenCappedFirstFaceOldCoreHomeomorph : ↥O≃ₜ↥T :=
  (nielsenCappedFirstFaceOldTargetHomeomorph hD hNE hFG hfin w hwD hwN J hc hv).trans
    ((nielsenCappedFirstFaceFiniteOrbitHomeomorph hD hNE hFG hfin w hwD hwN J hc hv).trans
      (((fuchsianCuspCompletionOld_isOpenEmbedding P.asFuchsianDisc).isEmbedding.homeomorphImage coreImage).trans
        (nielsenCompletedCoreOldForgetHomeomorph hNE).symm))

variable {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "projection" => nielsenCoreClosedModelCompletionMap hD hNE hFG S hr
local notation "completionMap" => nielsenCappedFirstFaceCompletionMap hD hNE hFG hfin w hwD hwN J hc hv S hr

/-- The unchanged first-face completion map, now with its proved canonical original completed-core image. -/
def nielsenCappedFirstFaceCompletedCoreMap (x:↥(range (modelPoint))) : Y :=
  ⟨(completionMap) x,by
    rw [←nielsenCoreClosedModelCompletionMap_range hD hNE hFG S hr w hwD hwN]
    exact ⟨Classical.choose x.property,rfl⟩⟩
local notation "F" => nielsenCappedFirstFaceCompletedCoreMap hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem continuous_nielsenCappedFirstFaceCompletedCoreMap : Continuous (F) :=
  (continuous_nielsenCappedFirstFaceCompletionMap hD hNE hFG hfin w hwD hwN J hc hv S hr).subtype_mk _

theorem nielsenCappedFirstFaceCompletedCoreMap_surjective : Function.Surjective (F) := by
  intro y
  have hy:y.val∈range (projection):=(nielsenCoreClosedModelCompletionMap_range hD hNE hFG S hr w hwD
    hwN).symm ▸ y.property
  obtain ⟨p,hp⟩:=hy
  refine ⟨(firstMap) p,Subtype.ext ?_⟩
  change (completionMap) ((firstMap) p)=y.val
  rw [nielsenCappedFirstFaceCompletionMap_cover,hp]

/-- The old-part homeomorphism and the actual continuous completed-core map are the same literal map. -/
theorem nielsenCappedFirstFaceCompletedCoreMap_old_compat (x:↥O) :
    (F) x.val=(nielsenCappedFirstFaceOldCoreHomeomorph hD hNE hFG hfin w hwD hwN J hc hv x).val := by
  obtain ⟨a,ha⟩:=x.property
  let e:=nielsenCappedFirstFaceOldTargetHomeomorph hD hNE hFG hfin w hwD hwN J hc hv
  have he:e x=(oldMap) a:=Subtype.ext ha.symm
  have hx:x=e.symm ((oldMap) a):=e.injective (by rw [e.apply_symm_apply];exact he)
  apply Subtype.ext
  change (completionMap) x.val=_
  have hx':x.val=(firstMap) ((finiteModel) a):=by
    apply Subtype.ext
    exact ha.symm
  rw [hx',nielsenCappedFirstFaceCompletionMap_cover,nielsenCoreClosedModelCompletionMap_finite]
  unfold nielsenCappedFirstFaceOldCoreHomeomorph
  change (old) (Surfaces.mobiusDomainProjection P.domain a.val)=
    ((nielsenCompletedCoreOldForgetHomeomorph hNE).symm
      (((fuchsianCuspCompletionOld_isOpenEmbedding P.asFuchsianDisc).isEmbedding.homeomorphImage coreImage)
        (nielsenCappedFirstFaceFiniteOrbitHomeomorph hD hNE hFG hfin w hwD hwN J hc hv (e x)))).val.val
  rw [he,nielsenCappedFirstFaceFiniteOrbitHomeomorph_projection,nielsenCompletedCoreOldForgetHomeomorph_symm_coe]
  rfl

end NielsenCompletedCoreOldHomeomorph



private theorem nielsenCore_puncture_tendsto_at {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (A:Set X) (hA:A.Finite) (B:Set Y) (hB:B.Finite)
    (e:↥(Aᶜ) ≃ₜ ↥(Bᶜ)) (F:X→Y) (he:∀x:↥(Aᶜ),F x=(e x).val)
    (a:X) (ha:a∈A) (b:Y)
    (hOne:∀s:Set X,s∈𝓝 a→∃t:Set X,t∈𝓝 a ∧t⊆s ∧IsPreconnected (t\{a}))
    (hcluster:MapClusterPt b (𝓝[Aᶜ] a) F) : Tendsto F (𝓝[Aᶜ] a) (𝓝 b) := by
  have hf:ContinuousOn F Aᶜ:=by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp e.continuous).congr (fun x=>(he x).symm)
  apply tendsto_def.mpr
  intro s hs
  obtain ⟨V,hVo,hbV,hVs,hVcomp,hVB⟩:=Surfaces.finite_punctures_compact_frontier_neighborhood B hB b s hs
  let K:=Aᶜ∩F ⁻¹' frontier V
  have hK:IsCompact K:=Surfaces.puncture_homeomorph_compact_preimage A B e F he _ hVcomp hVB
  have haK:a∉K:=by intro h;exact h.1 ha
  have hKa:Kᶜ∈𝓝 a:=hK.isClosed.isOpen_compl.mem_nhds haK
  have hother:(A\{a})ᶜ∈𝓝 a:=hA.sdiff.isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨U,hUa,hUsub,hUconn⟩:=hOne (Kᶜ∩(A\{a})ᶜ) (inter_mem hKa hother)
  have hUold:U\{a}⊆Aᶜ:=by
    intro x hx hxA
    exact (hUsub hx.1).2 ⟨hxA,hx.2⟩
  have hne:∀x∈Aᶜ,x≠a:=by intro x hx h;subst x;exact hx ha
  have himconn:IsPreconnected (F '' (U\{a})):=hUconn.image F (hf.mono hUold)
  have hfreq:=hcluster.frequently (hVo.mem_nhds hbV)
  have hUevent:∀ᶠx in 𝓝[Aᶜ] a,x∈U ∧x∈Aᶜ:=by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hUa,self_mem_nhdsWithin] with x hx hxA
    exact ⟨hx,hxA⟩
  obtain ⟨x,hxV,hxU,hxA⟩:=(hfreq.and_eventually hUevent).exists
  have hinter:(F '' (U\{a})∩V).Nonempty:=⟨F x,⟨x,⟨hxU,by simpa only [mem_singleton_iff] using hne x hxA⟩,rfl⟩,hxV⟩
  have himsub:F '' (U\{a})⊆V:=by
    apply himconn.subset_of_closure_inter_subset hVo hinter
    rintro y ⟨hyCl,z,hz,rfl⟩
    by_contra hyV
    have hyFront:F z∈frontier V:=by
      rw [frontier,hVo.interior_eq]
      exact ⟨hyCl,hyV⟩
    exact (hUsub hz.1).1 ⟨hUold hz,hyFront⟩
  filter_upwards [hUevent] with x hx
  exact hVs (himsub ⟨x,⟨hx.1,by simpa only [mem_singleton_iff] using hne x hx.2⟩,rfl⟩)


private theorem nielsenCore_finite_puncture_continuous_isHomeomorph {X Y:Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (A:Set X) (hA:A.Finite) (B:Set Y) (hB:B.Finite) (hDenseB:Dense Bᶜ)
    (e:↥(Aᶜ)≃ₜ↥(Bᶜ)) (F:X→Y) (he:∀x:↥(Aᶜ),F x=(e x).val)
    (hf:Continuous F) (hNew:∀a∈A,F a∈B)
    (hOneY:∀b∈B,∀s:Set Y,s∈𝓝 b→∃t:Set Y,t∈𝓝 b ∧t⊆s ∧IsPreconnected (t\{b}))
    (hcluster:∀a∈A,MapClusterPt (F a) (𝓝[Aᶜ] a) F) : IsHomeomorph F := by
  classical
  let G:Y→X:=fun y=>if hy:y∈B then Classical.choice (inferInstance:Nonempty X) else (e.symm ⟨y,hy⟩).val
  have hG:∀y:↥(Bᶜ),G y=(e.symm y).val:=by intro y;simp only [G,dite_eq_right y.property]
  have hOld:∀x∉A,F x∉B:=by intro x hx;rw [he ⟨x,hx⟩];exact (e ⟨x,hx⟩).property
  have hinj:Function.Injective F:=by
    intro x x' hxx
    by_cases hx:x∈A
    · have hx':x'∈A:=by
        by_contra hn
        exact hOld x' hn (hxx ▸ hNew x hx)
      let b:=F x
      have hb:b∈B:=hNew x hx
      have hCx:MapClusterPt x (𝓝[Bᶜ] b) G:=Surfaces.puncture_mapClusterPt_symm A B e F G he hG x b (hcluster x hx)
      have hCx':MapClusterPt x' (𝓝[Bᶜ] b) G:=by
        have h:=Surfaces.puncture_mapClusterPt_symm A B e F G he hG x' (F x') (hcluster x' hx')
        simpa only [←hxx] using h
      have ht:=nielsenCore_puncture_tendsto_at B hB A hA e.symm G hG b hb x (hOneY b hb) hCx
      have ht':=nielsenCore_puncture_tendsto_at B hB A hA e.symm G hG b hb x' (hOneY b hb) hCx'
      have : NeBot (𝓝[Bᶜ] b):=mem_closure_iff_nhdsWithin_neBot.mp (hDenseB b)
      exact tendsto_nhds_unique ht ht'
    · have hx':x'∉A:=by intro hx';exact hOld x hx (hxx.symm ▸ hNew x' hx')
      have h:e ⟨x,hx⟩=e ⟨x',hx'⟩:=Subtype.ext ((he ⟨x,hx⟩).symm.trans (hxx.trans (he ⟨x',hx'⟩)))
      exact congrArg Subtype.val (e.injective h)
  have hsur:Function.Surjective F:=by
    intro y
    have hOldRange:Bᶜ⊆range F:=by
      intro z hz
      refine ⟨(e.symm ⟨z,hz⟩).val,?_⟩
      rw [he,e.apply_symm_apply]
    exact closure_minimal hOldRange (isCompact_range hf).isClosed (hDenseB y)
  exact isHomeomorph_iff_continuous_bijective.mpr ⟨hf,hinj,hsur⟩



/-- At a genuine cusp the completed Nielsen core agrees locally with its original Riemann-surface completion. -/
private theorem nielsenCore_cuspSubspace_punctured
    {H:Subgroup Mobius.complexMobiusGroup} (D₀:FuchsianDisc H)
    (S:Set (FuchsianCuspCompletion D₀)) (x:S) (hx:x.val∈interior S) :
    ∀U:Set S,U∈𝓝 x→∃T:Set S,T∈𝓝 x ∧T⊆U ∧IsPreconnected (T\{x}) := by
  let R:=fuchsianCuspCompletionRiemannSurface D₀
  let:=R.toRiemannAtlas.toChartedSpace
  intro U hU
  obtain ⟨V,hV,hVU⟩:=(mem_nhds_subtype S x U).mp hU
  obtain ⟨T,hT,hsub,hconn⟩:=Surfaces.chartedComplex_connectedPuncturedNeighborhoods
    (FuchsianCuspCompletion D₀) x.val (V∩interior S) (inter_mem hV (isOpen_interior.mem_nhds hx))
  have hTS:T⊆S:=fun _ hp=>interior_subset (hsub hp).2
  refine ⟨Subtype.val ⁻¹' T,(continuous_subtype_val.tendsto x) hT,fun y hy=>hVU (hsub hy).1,?_⟩
  apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
  have he: (Subtype.val:S → FuchsianCuspCompletion D₀) '' ((Subtype.val ⁻¹' T)\{x})=T\{x.val}:=by
    ext p
    constructor
    · rintro ⟨y,⟨hy,hne⟩,rfl⟩
      refine ⟨hy,?_⟩
      intro hp
      apply hne
      exact Subtype.ext hp
    · rintro ⟨hp,hne⟩
      refine ⟨⟨p,hTS hp⟩,⟨hp,?_⟩,rfl⟩
      intro he
      exact hne (congrArg Subtype.val he)
  rw [he]
  exact hconn



section NielsenCompletedCoreFaceHomeomorph
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
  {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "firstMap" => nielsenCappedFirstFaceImageMap hD hNE hFG hfin w hwD hwN J hc hv
local notation "finitePoint" => nielsenCappedOriginalFinitePoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "finiteModel" => nielsenCappedFiniteModelPoint (P:=P) (D:=D) hNE
local notation "projection" => nielsenCoreClosedModelCompletionMap hD hNE hFG S hr
local notation "completionMap" => nielsenCappedFirstFaceCompletionMap hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "F" => nielsenCappedFirstFaceCompletedCoreMap hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "O" => nielsenCappedFirstFaceOldSet hD hNE hFG hfin w hwD hwN J hc hv
local notation "T" => nielsenCompletedCoreOldSet (P:=P) hNE

/-- The actual first-face image is homeomorphic to the unchanged original completed Nielsen quotient. Only the finitely many actual ideal points are extended, using the proved genuine original cusp neighborhoods. -/
theorem nielsenCappedFirstFaceCompletedCoreMap_isHomeomorph : IsHomeomorph (F) := by
  let W:=(Pcap).PolygonalRealization (valid)
  let X:=↥(range (modelPoint))
  let Y:=↥(nielsenCompletedCoreSet P hNE)
  obtain ⟨g,hg,_⟩:=nielsenCappedPresentation_genus hD hNE hFG hfin w hwD hwN J hc hv
  let:T2Space W:=Surfaces.HandleSeparation.hasTopologicalGenus_t2Space hg
  let:CompactSpace K:=isCompact_iff_compactSpace.mp (Hyperbolic.isCompact_discClosedModelClosure _)
  let:CompactSpace X:=isCompact_iff_compactSpace.mp
    (isCompact_range (continuous_nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv))
  let R:=fuchsianCuspCompletionRiemannSurface P.asFuchsianDisc
  let:=R.t2Space
  let:CompactSpace Y:=isCompact_iff_compactSpace.mp (by
    rw [←nielsenCoreClosedModelCompletionMap_range hD hNE hFG S hr w hwD hwN]
    exact isCompact_range (continuous_nielsenCoreClosedModelCompletionMap hD hNE hFG S hr))
  let a:closure Q:=⟨w,subset_closure ⟨hwD,hwN⟩⟩
  let:Nonempty X:=⟨(firstMap) ((finiteModel) a)⟩
  let A:Set X:=(O)ᶜ
  let B:Set Y:=(T)ᶜ
  have hF:Continuous (F):=continuous_nielsenCappedFirstFaceCompletedCoreMap hD hNE hFG hfin w hwD hwN J hc hv S hr
  have hsur:Function.Surjective (F):=nielsenCappedFirstFaceCompletedCoreMap_surjective hD hNE hFG hfin w hwD hwN J hc hv S hr
  have hA:A.Finite:=by
    apply ((nielsenCappedFirstFaceIdealSet_finite hD hNE hFG).image (firstMap)).subset
    intro x hx
    obtain ⟨p,hp⟩:=x.property
    have hpOld:(modelPoint) p∉range (finitePoint):=by
      change x.val∉range (finitePoint) at hx
      rwa [hp]
    have hnorm:¬‖(p.val:ℂ)‖<1:=by
      rwa [←nielsenCappedOriginalModelPoint_mem_finite_range_iff hD hNE hFG hfin w hwD hwN J hc hv]
    exact ⟨p,le_antisymm p.val.norm_le_one (le_of_not_gt hnorm),Subtype.ext hp⟩
  have hPre:(F) ⁻¹' B=A:=by
    ext x
    exact not_congr (nielsenCappedFirstFaceCompletionMap_mem_old_iff hD hNE hFG hfin w hwD hwN J hc hv S hr x)
  have hNew:∀x∈A,(F) x∈B:=by
    intro x hx
    change x∈(F) ⁻¹' B
    rw [hPre]
    exact hx
  have hB:B.Finite:=(hA.image (F)).subset (by
    intro y hy
    obtain ⟨x,rfl⟩:=hsur y
    exact ⟨x,hPre ▸ hy,rfl⟩)
  have hDenseO:Dense (O):=by
    intro x
    obtain ⟨p,hp⟩:=x.property
    have he:(firstMap) p=x:=Subtype.ext hp
    rw [←he]
    have hsub:(firstMap) '' {p:K | ‖(p.val:ℂ)‖<1}⊆O:=by
      rintro _ ⟨q,hq,rfl⟩
      exact (nielsenCappedOriginalModelPoint_mem_finite_range_iff hD hNE hFG hfin w hwD hwN J hc hv q).mpr hq
    apply closure_mono hsub
    exact image_closure_subset_closure_image
      ((continuous_nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv).subtype_mk _)
      ⟨p,originalClosedModel_finitePart_dense (P:=P) (D:=Q) p,rfl⟩
  have hDenseA:Dense Aᶜ:=by simpa only [A,compl_compl] using hDenseO
  have hOld:∀x∈Aᶜ,(F) x∈Bᶜ:=by intro x hx hFx;exact hx (hPre ▸ hFx)
  have hDenseB:Dense Bᶜ:=by
    intro y
    obtain ⟨x,rfl⟩:=hsur y
    apply closure_mono (show (F) '' Aᶜ⊆Bᶜ from by rintro _ ⟨z,hz,rfl⟩;exact hOld z hz)
    exact image_closure_subset_closure_image hF ⟨x,hDenseA x,rfl⟩
  let e:↥(Aᶜ)≃ₜ↥(Bᶜ):=(Homeomorph.setCongr (compl_compl (O))).trans
    ((nielsenCappedFirstFaceOldCoreHomeomorph hD hNE hFG hfin w hwD hwN J hc hv).trans
      (Homeomorph.setCongr (compl_compl (T)).symm))
  have hE:∀x:↥(Aᶜ),(F) x=(e x).val:=by
    intro x
    exact nielsenCappedFirstFaceCompletedCoreMap_old_compat hD hNE hFG hfin w hwD hwN J hc hv S hr
      ⟨x.val,by simpa only [A,compl_compl] using x.property⟩
  apply nielsenCore_finite_puncture_continuous_isHomeomorph A hA B hB hDenseB e (F) hE hF hNew
  · intro b hb
    have hbOld:b.val∉range (fuchsianCuspCompletionOld P.asFuchsianDisc):=hb
    obtain ⟨c,hc'⟩:=(fuchsianCuspCompletion_old_or_cusp P.asFuchsianDisc b.val).resolve_left hbOld
    apply nielsenCore_cuspSubspace_punctured P.asFuchsianDisc (nielsenCompletedCoreSet P hNE) b
    rw [hc']
    exact nielsenCompletedCoreSet_cusp_mem_interior P hNE c
  · intro x _hx
    have:NeBot (𝓝[Aᶜ] x):=mem_closure_iff_nhdsWithin_neBot.mp (hDenseA x)
    exact (hF.continuousAt.mono_left nhdsWithin_le_nhds).mapClusterPt

/-- The actual first-face compactification retains precisely the same original finite quotient and original cusp topology. -/
def nielsenCappedFirstFaceCompletedCoreHomeomorph :
    ↥(range (modelPoint))≃ₜ↥(nielsenCompletedCoreSet P hNE) :=
  (Equiv.ofBijective (F) (nielsenCappedFirstFaceCompletedCoreMap_isHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S
    hr).bijective).toHomeomorphOfContinuousClosed
    (continuous_nielsenCappedFirstFaceCompletedCoreMap hD hNE hFG hfin w hwD hwN J hc hv S hr)
    (nielsenCappedFirstFaceCompletedCoreMap_isHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr).isClosedMap

end NielsenCompletedCoreFaceHomeomorph



section NielsenCappedFaceInteriors
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "mk" => FiniteCyclicPresentation.polygonalMk (Pcap) (valid)

/-- Every genuine stored gluing acts only on the real boundary circles; it never changes an interior point. -/
theorem nielsenCappedWord_eq_or_boundary
    {a b:(Pcap).PolygonalPreRealization} (he:(mk) a=(mk) b) :
    a=b ∨ (‖a.2.val‖=1 ∧‖b.2.val‖=1) := by
  have hr:=Quotient.exact he
  change Relation.EqvGen (PolygonGluing.Generator ((Pcap).polygonalIdentifications (valid))) a b at hr
  clear he
  induction hr with
  | rel a b h =>
    right
    cases h with
    | glue identification _hi t =>
      constructor <;> exact Circle.norm_coe _
  | refl a => exact Or.inl rfl
  | symm a b _ ih =>
    rcases ih with he|hb
    · exact Or.inl he.symm
    · exact Or.inr ⟨hb.2,hb.1⟩
  | trans a b c _ _ ih ih' =>
    rcases ih with he|hb
    · subst b
      exact ih'
    · rcases ih' with he'|hc'
      · subst c
        exact Or.inr hb
      · exact Or.inr ⟨hb.1,hc'.2⟩

private theorem nielsenCapped_discToClosedModel_isOpenEmbedding : Topology.IsOpenEmbedding Hyperbolic.discToClosedModel := by
  refine ⟨Hyperbolic.isEmbedding_discToClosedModel,?_⟩
  have he:range Hyperbolic.discToClosedModel={p:𝕔𝔻 | ‖(p:ℂ)‖<1}:=by
    ext p
    constructor
    · rintro ⟨z,rfl⟩
      exact z.norm_lt_one
    · intro hp
      exact ⟨Hyperbolic.closedDiscFinitePoint p hp,Hyperbolic.closedDiscFinitePoint_spec p hp⟩
  rw [he]
  exact isOpen_lt (continuous_norm.comp Complex.UnitClosedDisc.continuous_coe) continuous_const

/-- The literal open disc of each genuine stored face, included before the faithful quotient. -/
def nielsenCappedFaceInteriorPre (f:(Pcap).Face) (z:𝔻) : (Pcap).PolygonalPreRealization :=
  ⟨f,(PolygonCell.closedUnitDiscHomeomorph ((Pcap).boundary f).length).symm (Hyperbolic.discToClosedModel z)⟩
local notation "pre" => nielsenCappedFaceInteriorPre hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedFaceInteriorPre_isOpenEmbedding (f:(Pcap).Face) : Topology.IsOpenEmbedding ((pre) f) :=
  Topology.IsOpenEmbedding.sigmaMk.comp
    ((PolygonCell.closedUnitDiscHomeomorph ((Pcap).boundary f).length).symm.isOpenEmbedding.comp
      nielsenCapped_discToClosedModel_isOpenEmbedding)

def nielsenCappedFaceInterior (f:(Pcap).Face) : 𝔻 → (Pcap).PolygonalRealization (valid) := (mk) ∘ (pre) f
local notation "faceInterior" => nielsenCappedFaceInterior hD hNE hFG hfin w hwD hwN J hc hv

/-- Every actual stored open face is a genuine open embedded disc in the unchanged faithful cap surface. -/
theorem nielsenCappedFaceInterior_isOpenEmbedding (f:(Pcap).Face) : Topology.IsOpenEmbedding ((faceInterior) f) := by
  have hpre:=nielsenCappedFaceInteriorPre_isOpenEmbedding hD hNE hFG hfin w hwD hwN J hc hv f
  have hnorm:∀z:𝔻,‖((pre) f z).2.val‖<1:=fun z=>z.norm_lt_one
  have hinj:Function.Injective ((faceInterior) f):=by
    intro z u he
    rcases nielsenCappedWord_eq_or_boundary hD hNE hFG hfin w hwD hwN J hc hv he with he'|hb
    · exact hpre.injective he'
    · exact False.elim ((ne_of_lt (hnorm z)) hb.1)
  have hopen:IsOpenMap ((faceInterior) f):=by
    intro U hU
    have hS:IsOpen (((pre) f) '' U):=hpre.isOpenMap U hU
    have hsat:(mk) ⁻¹' ((mk) '' (((pre) f) '' U))=(((pre) f) '' U):=by
      apply subset_antisymm
      · rintro b ⟨a,⟨z,hz,rfl⟩,he⟩
        rcases nielsenCappedWord_eq_or_boundary hD hNE hFG hfin w hwD hwN J hc hv he with hab|hb
        · exact hab ▸ mem_image_of_mem _ hz
        · exact False.elim ((ne_of_lt (hnorm z)) hb.1)
      · exact subset_preimage_image _ _
    change IsOpen (((mk) ∘ (pre) f) '' U)
    have he:((mk) ∘ (pre) f) '' U=(mk) '' (((pre) f) '' U):=by
      simpa only [Function.comp_def] using (image_image (mk) ((pre) f) U).symm
    rw [he]
    apply (isQuotientMap_polygonalMk (Pcap) (valid)).isOpen_preimage.mp
    rw [hsat]
    exact hS
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    (((Pcap).continuous_polygonalMk (valid)).comp hpre.continuous) hinj hopen

/-- Distinct genuine face interiors stay disjoint in the faithful closed surface. -/
theorem nielsenCappedFaceInterior_pairwise_disjoint :
    Pairwise (fun f g:(Pcap).Face=>Disjoint (range ((faceInterior) f)) (range ((faceInterior) g))) := by
  intro f g hfg
  apply Set.disjoint_left.mpr
  rintro _ ⟨z,rfl⟩ ⟨u,he⟩
  rcases nielsenCappedWord_eq_or_boundary hD hNE hFG hfin w hwD hwN J hc hv he with h|h
  · exact hfg (congrArg Sigma.fst h).symm
  · exact (ne_of_lt u.norm_lt_one) h.1

end NielsenCappedFaceInteriors



section NielsenCappedComplement
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "E" => nielsenCappedOriginalFaceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv
local notation "mk" => FiniteCyclicPresentation.polygonalMk (Pcap) (valid)
local notation "index" => originalCyclicFinIndex J
local notation "occIndex" => nielsenCappedOccurrenceIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "partner" => nielsenCappedOccurrencePartner hD hNE hFG hfin w hwD hwN J hc hv
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "pre" => nielsenCappedFaceInteriorPre hD hNE hFG hfin w hwD hwN J hc hv
local notation "faceInterior" => nielsenCappedFaceInterior hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedOccurrence_old_face (o:(Pcap).BoundaryOccurrence)
    (i:ZMod J.n) (hi:(occIndex) o=Sum.inl i) : o.1=f₀ := by
  have he:o=nielsenCappedOriginalOccurrence hD hNE hFG hfin w hwD hwN J hc hv ((index).symm i):=by
    apply (occIndex).injective
    rw [hi,nielsenCappedOriginalOccurrence_index,Equiv.apply_symm_apply]
  exact congrArg Sigma.fst he

theorem nielsenCappedOccurrence_cap_partner_face (o:(Pcap).BoundaryOccurrence)
    (hf:o.1≠f₀) : ((partner) o).1=f₀ := by
  cases hi:(occIndex) o with
  | inl i => exact False.elim (hf (nielsenCappedOccurrence_old_face hD hNE hFG hfin w hwD hwN J hc hv o i hi))
  | inr b =>
    apply nielsenCappedOccurrence_old_face hD hNE hFG hfin w hwD hwN J hc hv ((partner) o) b.val
    simp only [nielsenCappedOccurrencePartner,Equiv.apply_symm_apply,hi,nielsenCapOccurrencePair]

/-- Every literal cap-side point is glued into the actual first-face image, by its own stored original pairing. -/
theorem nielsenCappedCapSide_mem_firstFace (o:(Pcap).BoundaryOccurrence)
    (hf:o.1≠f₀) (t:unitInterval) :
    (mk) (((Pcap).occurrenceSide o).point t)∈range (modelPoint) := by
  have hclosed:=nielsenCappedPresentation_closed hD hNE hFG hfin w hwD hwN J hc hv o.edge
  have hb:¬(Pcap).IsBoundaryEdge o.edge:=by
    change (Pcap).edgeMultiplicity o.edge≠1
    omega
  obtain ⟨p,hp⟩:=(valid).exists_pairing_source o hb
  have ht:p.target.1=f₀:=by
    rw [nielsenCappedBoundaryPairing_target hD hNE hFG hfin w hwD hwN J hc hv p,hp]
    exact nielsenCappedOccurrence_cap_partner_face hD hNE hFG hfin w hwD hwN J hc hv o hf
  have he:=(Pcap).polygonalMk_pairing_eq (valid) p t
  change (mk) (((Pcap).occurrenceSide p.source).point t)=
    (mk) (((Pcap).occurrenceSide p.target).point (p.identification.parameter t)) at he
  rw [hp] at he
  rw [he]
  generalize ho:p.target=o at ht ⊢
  rcases o with ⟨f,i⟩
  change f=f₀ at ht
  subst f
  refine ⟨(E) (PolygonCell.side i (p.identification.parameter t)),?_⟩
  change (mk) ⟨f₀,(E).symm ((E) _)⟩=_
  rw [Homeomorph.symm_apply_apply]
  rfl

/-- A full genuine cap boundary, rather than only its marked corners, lies in the original completed core image. -/
theorem nielsenCappedCapBoundary_mem_firstFace (f:(Pcap).Face) (hf:f≠f₀)
    (z:PolygonCell ((Pcap).boundary f).length) (hz:‖z.val‖=1) :
    (mk) ⟨f,z⟩∈range (modelPoint) := by
  have hlen:0<((Pcap).boundary f).length:=List.length_pos_iff.mpr
    (nielsenCappedPresentation_boundary_ne_nil hD hNE hFG hfin w hwD hwN J hc hv f)
  obtain ⟨i,t,rfl⟩:=PolygonCell.exists_side_eq_of_mem_sphere hlen z (by simpa only [Metric.mem_sphere,dist_zero_right] using hz)
  exact nielsenCappedCapSide_mem_firstFace hD hNE hFG hfin w hwD hwN J hc hv ⟨f,i⟩ hf t

/-- A cap interior cannot be identified with any point of the original face. -/
theorem nielsenCappedCapInterior_not_mem_firstFace (f:(Pcap).Face) (hf:f≠f₀) (z:𝔻) :
    (faceInterior) f z∉range (modelPoint) := by
  rintro ⟨p,hp⟩
  rcases nielsenCappedWord_eq_or_boundary hD hNE hFG hfin w hwD hwN J hc hv hp with he|hb
  · exact hf (congrArg Sigma.fst he).symm
  · exact (ne_of_lt z.norm_lt_one) hb.2

/-- The complement of the unchanged completed core is exactly the disjoint union of the actual stored open cap discs. -/
theorem nielsenCappedFirstFace_complement_eq :
    (range (modelPoint))ᶜ=⋃f: {f:(Pcap).Face // f≠f₀},range ((faceInterior) f.val) := by
  ext y
  constructor
  · intro hy
    obtain ⟨⟨f,z⟩,rfl⟩:=(isQuotientMap_polygonalMk (Pcap) (valid)).surjective y
    have hf:f≠f₀:=by
      intro he
      subst f
      apply hy
      exact ⟨(E) z,by change (mk) ⟨f₀,(E).symm ((E) z)⟩=_;rw [Homeomorph.symm_apply_apply]⟩
    have hz:‖z.val‖<1:=by
      apply lt_of_le_of_ne (mem_closedBall_zero_iff.mp z.property)
      intro he
      exact hy (nielsenCappedCapBoundary_mem_firstFace hD hNE hFG hfin w hwD hwN J hc hv f hf z he)
    apply mem_iUnion.mpr
    refine ⟨⟨f,hf⟩,⟨Complex.UnitDisc.mk z.val hz,?_⟩⟩
    apply congrArg (mk)
    apply congrArg (fun a:PolygonCell ((Pcap).boundary f).length=>(⟨f,a⟩:(Pcap).PolygonalPreRealization))
    apply (PolygonCell.closedUnitDiscHomeomorph ((Pcap).boundary f).length).injective
    rw [Homeomorph.apply_symm_apply]
    rfl
  · intro hy
    obtain ⟨⟨f,hf⟩,z,rfl⟩:=mem_iUnion.mp hy
    exact nielsenCappedCapInterior_not_mem_firstFace hD hNE hFG hfin w hwD hwN J hc hv f hf z

end NielsenCappedComplement



section NielsenCappedCapBoundaryKernel
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "mk" => FiniteCyclicPresentation.polygonalMk (Pcap) (valid)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "ρ" => nielsenCyclicBoundaryEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "index" => originalCyclicFinIndex J
local notation "occIndex" => nielsenCappedOccurrenceIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "label" => nielsenCappedOccurrenceRawLabel hD hNE hFG hfin w hwD hwN J hc hv
local notation "γ" => nielsenCyclicSideParam hD hNE hFG hfin w hwD hwN J hc hv
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv
local notation "edge" => nielsenCyclicEdge hD hNE hFG J hv
local notation "point" => nielsenCyclicBoundaryNativePoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "rightPoint" => nielsenCyclicBoundaryNativeRightPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "nativeEdge" => nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv
local notation "preCornerLabel" => nielsenCappedCornerPreLabel hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedOccurrence_cap_index (o:(Pcap).BoundaryOccurrence) (hf:o.1≠f₀) :
    ∃b:B,(occIndex) o=Sum.inr b := by
  cases hi:(occIndex) o with
  | inl i => exact False.elim (hf (nielsenCappedOccurrence_old_face hD hNE hFG hfin w hwD hwN J hc hv o i hi))
  | inr b => exact ⟨b,rfl⟩

/-- No two genuine cap corners are identified: each is the unique corresponding outgoing original boundary vertex. -/
theorem nielsenCappedCapCornerLabel_injective
    (o p:(Pcap).BoundaryOccurrence) (ho:o.1≠f₀) (hp:p.1≠f₀)
    (he:(label) o=(label) p) : o=p := by
  obtain ⟨b,hb⟩:=nielsenCappedOccurrence_cap_index hD hNE hFG hfin w hwD hwN J hc hv o ho
  obtain ⟨c,hc'⟩:=nielsenCappedOccurrence_cap_index hD hNE hFG hfin w hwD hwN J hc hv p hp
  have hb':(Quotient.mk _ (b.val+1):V)=Quotient.mk _ ((ρ) b).val:=
    Quotient.sound (nielsenCyclicBoundaryNext_corner_chain hD hNE hFG hfin w hwD hwN J hc hv b)
  have hc'':(Quotient.mk _ (c.val+1):V)=Quotient.mk _ ((ρ) c).val:=
    Quotient.sound (nielsenCyclicBoundaryNext_corner_chain hD hNE hFG hfin w hwD hwN J hc hv c)
  change nielsenCapRawVertexLabel hD hNE hFG hfin w hwD hwN J hc hv ((occIndex) o)=
    nielsenCapRawVertexLabel hD hNE hFG hfin w hwD hwN J hc hv ((occIndex) p) at he
  simp only [hb,hc',nielsenCapRawVertexLabel] at he
  rw [hb',hc''] at he
  have hbc:b=c:=(ρ).injective
    (nielsenRawBoundaryVertex_injective hD hNE hFG hfin w hwD hwN J hc hv he)
  exact (occIndex).injective (hb.trans ((congrArg Sum.inr hbc).trans hc'.symm))

theorem nielsenCappedCapCorner_word_injective
    (o p:(Pcap).BoundaryOccurrence) (ho:o.1≠f₀) (hp:p.1≠f₀)
    (he:(mk) (((Pcap).occurrenceSide o).point 0)=(mk) (((Pcap).occurrenceSide p).point 0)) : o=p := by
  have h:=congrArg (nielsenCappedCornerWordLabel hD hNE hFG hfin w hwD hwN J hc hv) he
  change (preCornerLabel) (((Pcap).occurrenceSide o).point 0)=(preCornerLabel) (((Pcap).occurrenceSide p).point 0) at h
  rw [nielsenCappedCornerPreLabel_zero,nielsenCappedCornerPreLabel_zero] at h
  exact nielsenCappedCapCornerLabel_injective hD hNE hFG hfin w hwD hwN J hc hv o p ho hp (Option.some.inj h)

/-- The original whole-group quotient is faithful on an actual open free edge; hence no two cap side interiors are merged. -/
theorem nielsenCappedCapSideInterior_word_injective
    (o p:(Pcap).BoundaryOccurrence) (ho:o.1≠f₀) (hp:p.1≠f₀)
    (t u:unitInterval) (ht0:t≠0) (ht1:t≠1)
    (he:(mk) (((Pcap).occurrenceSide o).point t)=(mk) (((Pcap).occurrenceSide p).point u)) : o=p ∧ t=u := by
  obtain ⟨b,hb⟩:=nielsenCappedOccurrence_cap_index hD hNE hFG hfin w hwD hwN J hc hv o ho
  obtain ⟨c,hc'⟩:=nielsenCappedOccurrence_cap_index hD hNE hFG hfin w hwD hwN J hc hv p hp
  have hxb:(γ) ((index).symm b.val) (unitInterval.symm t)∈edge b.val:=by
    have hm:=range_nielsenCyclicSideParam hD hNE hFG hfin w hwD hwN J hc hv ((index).symm b.val)
    rw [Equiv.apply_symm_apply] at hm
    exact hm ▸ mem_range_self (unitInterval.symm t)
  have hyc:(γ) ((index).symm c.val) (unitInterval.symm u)∈edge c.val:=by
    have hm:=range_nielsenCyclicSideParam hD hNE hFG hfin w hwD hwN J hc hv ((index).symm c.val)
    rw [Equiv.apply_symm_apply] at hm
    exact hm ▸ mem_range_self (unitInterval.symm u)
  obtain ⟨x,hx⟩:=nielsenCyclicBoundaryEdge_finite hD hNE hFG hfin w hwD hwN J hc hv b _ hxb
  obtain ⟨y,hy⟩:=nielsenCyclicBoundaryEdge_finite hD hNE hFG hfin w hwD hwN J hc hv c _ hyc
  have hxE:x∈nativeEdge b:=(mem_nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv b x).mpr (hx.symm ▸
    hxb)
  have hyE:y∈nativeEdge c:=(mem_nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv c y).mpr (hy.symm ▸
    hyc)
  have hxL:x≠point b:=by
    intro h
    have hγ:(γ) ((index).symm b.val) (unitInterval.symm t)=(γ) ((index).symm b.val) 0:=by
      rw [nielsenCyclicSideParam_zero,Equiv.apply_symm_apply,←hx,h]
      exact (nielsenCyclicBoundaryNativePoint_spec hD hNE hFG hfin w hwD hwN J hc hv b).1
    have ht:=nielsenCyclicSideParam_injective hD hNE hFG hfin w hwD hwN J hc hv _ hγ
    exact ht1 (unitInterval.symm_involutive.injective (ht.trans unitInterval.symm_one.symm))
  have hxR:x≠rightPoint b:=by
    intro h
    have hγ:(γ) ((index).symm b.val) (unitInterval.symm t)=(γ) ((index).symm b.val) 1:=by
      rw [nielsenCyclicSideParam_one,Equiv.apply_symm_apply,←hx,h]
      exact nielsenCyclicBoundaryNativeRightPoint_spec hD hNE hFG hfin w hwD hwN J hc hv b
    have ht:=nielsenCyclicSideParam_injective hD hNE hFG hfin w hwD hwN J hc hv _ hγ
    exact ht0 (unitInterval.symm_involutive.injective (ht.trans unitInterval.symm_zero.symm))
  have hclass:=congrArg (nielsenCappedSphereWordLabel hD hNE hFG hfin w hwD hwN J hc hv) he
  change nielsenCappedSpherePreLabel hD hNE hFG hfin w hwD hwN J hc hv _=
    nielsenCappedSpherePreLabel hD hNE hFG hfin w hwD hwN J hc hv _ at hclass
  rw [nielsenCappedSpherePreLabel_side,nielsenCappedSpherePreLabel_side] at hclass
  have hs:=Option.some.inj hclass
  simp only [nielsenCappedSphereBoundaryClass,nielsenCappedSphereBoundaryPoint,hb,hc'] at hs
  rw [←hx,←hy,originalFinitePoint_closedModel_sphere,originalFinitePoint_closedModel_sphere] at hs
  have hπ:Surfaces.mobiusDomainProjection P.domain x=Surfaces.mobiusDomainProjection P.domain y:=by
    have horb:=Quotient.exact hs
    change x.val∈MulAction.orbit H y.val at horb
    obtain ⟨g,hg⟩:=MulAction.mem_orbit_iff.mp horb
    apply Quotient.sound
    change x∈MulAction.orbit H y
    exact MulAction.mem_orbit_iff.mpr ⟨g,Subtype.ext hg⟩
  obtain ⟨hbc,hxy⟩:=nielsenCyclicBoundaryNativeEdge_projection_interior hD hNE hFG hfin w hwD hwN J hc hv b c x y hxE hyE hxL hxR hπ
  refine ⟨(occIndex).injective (hb.trans ((congrArg Sum.inr hbc).trans hc'.symm)),?_⟩
  subst c
  have hγ:(γ) ((index).symm b.val) (unitInterval.symm t)=(γ) ((index).symm b.val) (unitInterval.symm
    u):=hx.symm.trans ((congrArg (fun a:P.domain.carrier=>Hyperbolic.discToClosedModel (P.finiteCoordinate a))
    hxy).trans hy)
  exact unitInterval.symm_involutive.injective (nielsenCyclicSideParam_injective hD hNE hFG hfin w hwD hwN J hc hv _ hγ)

end NielsenCappedCapBoundaryKernel



section NielsenCappedCapDiscs
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "mk" => FiniteCyclicPresentation.polygonalMk (Pcap) (valid)
local notation "cornerLabel" => nielsenCappedCornerWordLabel hD hNE hFG hfin w hwD hwN J hc hv
local notation "preCornerLabel" => nielsenCappedCornerPreLabel hD hNE hFG hfin w hwD hwN J hc hv
local notation "label" => nielsenCappedOccurrenceRawLabel hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedCapSide_zero_kernel
    (o p:(Pcap).BoundaryOccurrence) (ho:o.1≠f₀) (hp:p.1≠f₀)
    (u:unitInterval)
    (he:(mk) (((Pcap).occurrenceSide o).point 0)=(mk) (((Pcap).occurrenceSide p).point u)) :
    ((Pcap).occurrenceSide o).point 0=((Pcap).occurrenceSide p).point u := by
  by_cases hu0:u=0
  · subst u
    rw [nielsenCappedCapCorner_word_injective hD hNE hFG hfin w hwD hwN J hc hv o p ho hp he]
  by_cases hu1:u=1
  · subst u
    have hnext:((Pcap).occurrenceSide p).point 1=((Pcap).occurrenceSide (Surfaces.CyclicSurface.cornerNext (Pcap) p)).point 0:=by
      rcases p with ⟨f,i⟩
      exact congrArg (fun x:PolygonCell ((Pcap).boundary f).length=>(⟨f,x⟩:(Pcap).PolygonalPreRealization))
        (PolygonCell.side_one_eq_rotate_zero i)
    rw [hnext] at he ⊢
    have heo:o=Surfaces.CyclicSurface.cornerNext (Pcap) p:=nielsenCappedCapCorner_word_injective hD hNE hFG hfin w hwD hwN J hc hv o (Surfaces.CyclicSurface.cornerNext (Pcap) p) ho hp he
    rw [heo]
  have h:=congrArg (cornerLabel) he
  change (preCornerLabel) (((Pcap).occurrenceSide o).point 0)=(preCornerLabel) (((Pcap).occurrenceSide p).point u) at h
  rw [nielsenCappedCornerPreLabel_zero,nielsenCappedCornerPreLabel_side,ite_eq_right hu0,ite_eq_right hu1] at h
  exact False.elim (Option.some_ne_none _ h)

/-- The actual stored quotient is faithful on every cap boundary, including its full side intervals and all corners. -/
theorem nielsenCappedCapSide_word_kernel
    (o p:(Pcap).BoundaryOccurrence) (ho:o.1≠f₀) (hp:p.1≠f₀)
    (t u:unitInterval)
    (he:(mk) (((Pcap).occurrenceSide o).point t)=(mk) (((Pcap).occurrenceSide p).point u)) :
    ((Pcap).occurrenceSide o).point t=((Pcap).occurrenceSide p).point u := by
  by_cases ht0:t=0
  · subst t
    exact nielsenCappedCapSide_zero_kernel hD hNE hFG hfin w hwD hwN J hc hv o p ho hp u he
  by_cases ht1:t=1
  · subst t
    have hnext:((Pcap).occurrenceSide o).point 1=((Pcap).occurrenceSide (Surfaces.CyclicSurface.cornerNext (Pcap) o)).point 0:=by
      rcases o with ⟨f,i⟩
      exact congrArg (fun x:PolygonCell ((Pcap).boundary f).length=>(⟨f,x⟩:(Pcap).PolygonalPreRealization))
        (PolygonCell.side_one_eq_rotate_zero i)
    rw [hnext] at he ⊢
    exact nielsenCappedCapSide_zero_kernel hD hNE hFG hfin w hwD hwN J hc hv (Surfaces.CyclicSurface.cornerNext (Pcap)
      o) p ho hp u he
  obtain ⟨hop,htu⟩:=nielsenCappedCapSideInterior_word_injective hD hNE hFG hfin w hwD hwN J hc hv o p ho hp t u ht0 ht1 he
  rw [hop,htu]

theorem nielsenCappedCapPre_word_kernel
    (a b:(Pcap).PolygonalPreRealization) (ha:a.1≠f₀) (hb:b.1≠f₀)
    (he:(mk) a=(mk) b) : a=b := by
  rcases nielsenCappedWord_eq_or_boundary hD hNE hFG hfin w hwD hwN J hc hv he with he'|hboundary
  · exact he'
  rcases a with ⟨f,z⟩
  rcases b with ⟨g,v⟩
  have hlenf:0<((Pcap).boundary f).length:=List.length_pos_iff.mpr
    (nielsenCappedPresentation_boundary_ne_nil hD hNE hFG hfin w hwD hwN J hc hv f)
  have hleng:0<((Pcap).boundary g).length:=List.length_pos_iff.mpr
    (nielsenCappedPresentation_boundary_ne_nil hD hNE hFG hfin w hwD hwN J hc hv g)
  obtain ⟨i,t,rfl⟩:=PolygonCell.exists_side_eq_of_mem_sphere hlenf z (mem_sphere_zero_iff_norm.mpr hboundary.1)
  obtain ⟨j,u,rfl⟩:=PolygonCell.exists_side_eq_of_mem_sphere hleng v (mem_sphere_zero_iff_norm.mpr hboundary.2)
  exact nielsenCappedCapSide_word_kernel hD hNE hFG hfin w hwD hwN J hc hv ⟨f,i⟩ ⟨g,j⟩ ha hb t u he

/-- The literal closed cap disc, with its own unchanged stored cell. -/
def nielsenCappedClosedCap
    (f:(Pcap).Face) : PolygonCell ((Pcap).boundary f).length → (Pcap).PolygonalRealization (valid) :=
  fun z=>(mk) ⟨f,z⟩
local notation "closedCap" => nielsenCappedClosedCap hD hNE hFG hfin w hwD hwN J hc hv

theorem continuous_nielsenCappedClosedCap (f:(Pcap).Face) : Continuous ((closedCap) f) :=
  ((Pcap).continuous_polygonalMk (valid)).comp continuous_sigmaMk

/-- Each cap is a genuine embedded closed disc; no endpoint or interior identifications are hidden by the word realization. -/
theorem nielsenCappedClosedCap_isClosedEmbedding (f:(Pcap).Face) (hf:f≠f₀) :
    Topology.IsClosedEmbedding ((closedCap) f) := by
  obtain ⟨g,hg,_⟩:=nielsenCappedPresentation_genus hD hNE hFG hfin w hwD hwN J hc hv
  let:T2Space ((Pcap).PolygonalRealization (valid)):=Surfaces.HandleSeparation.hasTopologicalGenus_t2Space hg
  let:CompactSpace (PolygonCell ((Pcap).boundary f).length):=
    (PolygonCell.closedUnitDiscHomeomorph ((Pcap).boundary f).length).symm.compactSpace
  apply (continuous_nielsenCappedClosedCap hD hNE hFG hfin w hwD hwN J hc hv f).isClosedEmbedding
  intro z v he
  exact eq_of_heq (Sigma.mk.inj_iff.mp (nielsenCappedCapPre_word_kernel hD hNE hFG hfin w hwD hwN J hc hv ⟨f,z⟩ ⟨f,v⟩ hf
    hf he)).2

/-- Distinct actual caps are disjoint even on their real boundary clocks. -/
theorem nielsenCappedClosedCap_pairwise_disjoint :
    Pairwise (fun f g:{f:(Pcap).Face // f≠f₀}=>Disjoint (range ((closedCap) f.val)) (range ((closedCap) g.val))) := by
  intro f g hfg
  apply Set.disjoint_left.mpr
  rintro _ ⟨z,rfl⟩ ⟨v,he⟩
  have he':=nielsenCappedCapPre_word_kernel hD hNE hFG hfin w hwD hwN J hc hv ⟨g.val,v⟩ ⟨f.val,z⟩ g.property f.property he
  exact hfg (Subtype.ext (congrArg Sigma.fst he').symm)

end NielsenCappedCapDiscs



section NielsenCappedCapClocks
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "mk" => FiniteCyclicPresentation.polygonalMk (Pcap) (valid)
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "closedCap" => nielsenCappedClosedCap hD hNE hFG hfin w hwD hwN J hc hv

/-- The genuine unit-circle clock of a cap in the very same faithful closed surface. -/
def nielsenCappedCapClock (f:(Pcap).Face) : Circle → (Pcap).PolygonalRealization (valid) :=
  (closedCap) f ∘ (PolygonCell.ofCircle ((Pcap).boundary f).length)
local notation "clock" => nielsenCappedCapClock hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedCapClock_isClosedEmbedding (f:(Pcap).Face) (hf:f≠f₀) :
    Topology.IsClosedEmbedding ((clock) f) := by
  have he:=nielsenCappedClosedCap_isClosedEmbedding hD hNE hFG hfin w hwD hwN J hc hv f hf
  have hi:Topology.IsClosedEmbedding (PolygonCell.ofCircle ((Pcap).boundary f).length):=by
    let:T2Space (PolygonCell ((Pcap).boundary f).length):=(PolygonCell.closedUnitDiscHomeomorph _).symm.t2Space
    apply (PolygonCell.ofCircle ((Pcap).boundary f).length).continuous.isClosedEmbedding
    intro z v h
    exact Subtype.ext (congrArg PolygonCell.val h)
  exact he.comp hi

theorem nielsenCappedClosedCap_mem_firstFace_iff (f:(Pcap).Face) (hf:f≠f₀)
    (z:PolygonCell ((Pcap).boundary f).length) :
    (closedCap) f z∈range (modelPoint) ↔ ‖z.val‖=1 := by
  constructor
  · rintro ⟨p,hp⟩
    rcases nielsenCappedWord_eq_or_boundary hD hNE hFG hfin w hwD hwN J hc hv hp with he|hb
    · exact False.elim (hf (congrArg Sigma.fst he).symm)
    · exact hb.2
  · exact nielsenCappedCapBoundary_mem_firstFace hD hNE hFG hfin w hwD hwN J hc hv f hf z

theorem nielsenCappedCapClock_range (f:(Pcap).Face) (hf:f≠f₀) :
    range ((clock) f)=range ((closedCap) f)∩range (modelPoint) := by
  ext y
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨⟨_,rfl⟩,(nielsenCappedClosedCap_mem_firstFace_iff hD hNE hFG hfin w hwD hwN J hc hv f hf _).mpr
      (Circle.norm_coe z)⟩
  · rintro ⟨⟨z,rfl⟩,hz⟩
    have hn:‖z.val‖=1:=(nielsenCappedClosedCap_mem_firstFace_iff hD hNE hFG hfin w hwD hwN J hc hv f hf z).mp hz
    refine ⟨⟨z.val,mem_sphere_zero_iff_norm.mpr hn⟩,?_⟩
    apply congrArg ((closedCap) f)
    exact PolygonCell.ext rfl

/-- The actual number of open complementary caps is the original maximal boundary-hyperbolic conjugacy-class count. -/
theorem nielsenCappedCapFaceCount_eq :
    Nat.card {f:(Pcap).Face // f≠f₀}=
      Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc) := by
  rw [←nielsenBoundaryCycleClassCount_eq hD hNE hFG hfin w hwD hwN J hc hv,
    Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Fintype.card_subtype_compl (fun f:(Pcap).Face=>f=f₀),
    Fintype.card_subtype_eq]
  have hcard:Fintype.card (Pcap).Face=(Pcap).faces.length:=by
    calc
      _=Fintype.card (Fin (Pcap).faces.length):=Fintype.card_congr (Equiv.refl _)
      _=_:=Fintype.card_fin _
  rw [hcard,nielsenCappedPresentation_faces_length]
  omega

end NielsenCappedCapClocks



section NielsenCappedIdealCorners
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "L" => fuchsianPolygonCompactKlein P Q
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "index" => originalCyclicFinIndex J
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "cornerPoint" => nielsenCappedRawCornerPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "weight" => nielsenRawCornerClassWeight hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCyclicVertex_mem_closedModel (i:ZMod J.n) : vertex i∈K := by
  have hB:Hyperbolic.closedKleinCoordinate (vertex i)∈frontier L:=
    nielsenBoundaryMarkSaturation_subset_boundary P hNE D (nielsenBoundarySeedMarks hD hNE hFG)
      ⟨vertex i,nielsenCyclicVertex_marked hD hNE hFG J hv i,rfl⟩
  have hL:Hyperbolic.closedKleinCoordinate (vertex i)∈L:=by
    simpa only [fuchsianPolygonCompactKlein,closure_closure] using frontier_subset_closure hB
  have him:Hyperbolic.closedKleinCoordinate '' K=L:=by
    rw [Hyperbolic.discClosedModelClosure,Hyperbolic.closedKlein_image_discClosedModelClosure,image_image]
    rfl
  exact Hyperbolic.closedKleinCoordinate_injective.mem_set_image.mp (him.symm ▸ hL)

include hfin w hwD hwN in
/-- Every genuine ideal point of the actual clipped polygon is among its derived stored cyclic corners. -/
theorem nielsenCoreClosedModel_ideal_is_cyclicVertex (p:K) (hp:‖(p.val:ℂ)‖=1) :
    ∃i:ZMod J.n,vertex i=p.val := by
  have him:Hyperbolic.closedKleinCoordinate '' K=L:=by
    rw [Hyperbolic.discClosedModelClosure,Hyperbolic.closedKlein_image_discClosedModelClosure,image_image]
    rfl
  have hpL:Hyperbolic.closedKleinCoordinate p.val∈L:=him ▸ mem_image_of_mem _ p.property
  have hsub:L⊆Metric.closedBall (0:ℂ) 1:=by
    apply closure_minimal _ Metric.isClosed_closedBall
    rintro y ⟨x,_hx,rfl⟩
    exact Metric.ball_subset_closedBall (P.kleinCoordinate_range ▸ mem_range_self x)
  have hExtreme:Hyperbolic.closedKleinCoordinate p.val∈(Metric.closedBall (0:ℂ) 1).extremePoints ℝ:=by
    apply StrictConvexSpace.sphere_subset_extremePoints_closedBall (0:ℂ) one_ne_zero
    exact mem_sphere_zero_iff_norm.mpr ((Polygon.norm_closedKleinCoordinate_eq_one_iff p.val).mpr hp)
  have hext:Hyperbolic.closedKleinCoordinate p.val∈(L).extremePoints ℝ:=
    inter_extremePoints_subset_extremePoints_of_subset hsub ⟨hpL,hExtreme⟩
  have hB:Hyperbolic.closedKleinCoordinate p.val∈frontier L:=by
    rw [frontier,(show IsClosed L from isClosed_closure).closure_eq]
    exact ⟨hpL,fun h=>disjoint_left.mp (disjoint_interior_extremePoints L) h hext⟩
  obtain ⟨s,hs⟩:=nielsenBoundarySide_covers_frontier hD hNE hFG hfin w hwD hwN p.val hB
  have hseed:p.val∈nielsenBoundarySeedMarks hD hNE hFG:=
    NielsenBoundarySide.extreme_mem_seed hD hNE hFG w hwD hwN s p.val hs hext
  have hmark:p.val∈nielsenCanonicalBoundaryMarks hD hNE hFG:=
    nielsenBoundaryMarkSaturation_contains P hNE D _
      (nielsenBoundarySeedMarks_subset_frontier hD hNE hFG w hwD hwN) hseed
  obtain ⟨i,hi⟩:=(hv _).mpr ⟨p.val,hmark,rfl⟩
  refine ⟨i,Polygon.discPolygonKleinPlane_injective ?_⟩
  exact (nielsenCyclicVertex_plane hD hNE hFG J hv i).trans hi

theorem nielsenCappedOriginalModelPoint_vertex (i:ZMod J.n) :
    (modelPoint) ⟨vertex i,nielsenCyclicVertex_mem_closedModel hD hNE hFG J hv i⟩=
      (cornerPoint) (Quotient.mk _ i) := by
  rw [nielsenCappedOriginalModelPoint_side hD hNE hFG hfin w hwD hwN J hc hv _ ((index).symm i) 0
    (by rw [nielsenCyclicSideParam_zero,Equiv.apply_symm_apply])]
  rw [nielsenCappedOriginalOccurrence_eq_corner,Equiv.apply_symm_apply]
  rfl

/-- The natural map uses unchanged faithful word corner points, not assigned cusp labels. -/
def nielsenCappedRawCornerFirstFace (q:V) : ↥(range (modelPoint)) :=
  ⟨(cornerPoint) q,by
    refine Quotient.inductionOn q ?_
    intro i
    exact ⟨_,nielsenCappedOriginalModelPoint_vertex hD hNE hFG hfin w hwD hwN J hc hv i⟩⟩
local notation "rawFirst" => nielsenCappedRawCornerFirstFace hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedRawCornerFirstFace_injective : Function.Injective (rawFirst) := by
  intro q r he
  exact nielsenCappedRawCornerPoint_injective hD hNE hFG hfin w hwD hwN J hc hv (congrArg Subtype.val he)

theorem nielsenRawCornerWeight_zero_iff_ideal (i:ZMod J.n) :
    nielsenRawCornerWeight hD hNE hFG J hv i=0 ↔ ‖(vertex i:ℂ)‖=1 := by
  by_cases hn:‖(vertex i:ℂ)‖<1
  · rw [nielsenRawCornerWeight,dite_eq_left hn]
    have hpos:0<(fuchsianPointOrder P (P.finiteCoordinate.symm (Hyperbolic.closedDiscFinitePoint (vertex i) hn)):ℝ):=by
      exact_mod_cast P.pointOrder_pos _
    constructor
    · intro h
      dsimp only at h
      split_ifs at h
      · exact False.elim ((one_div_pos.mpr hpos).ne' h)
      · norm_num at h
    · intro he
      exact False.elim ((ne_of_lt hn) he)
  · rw [nielsenRawCornerWeight,dite_eq_right hn]
    exact ⟨fun _=>le_antisymm (vertex i).norm_le_one (le_of_not_gt hn),fun _=>rfl⟩

end NielsenCappedIdealCorners



section NielsenCappedActualCusps
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
  {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "vertex" => nielsenCyclicVertex hD hNE hFG J hv
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "firstMap" => nielsenCappedFirstFaceImageMap hD hNE hFG hfin w hwD hwN J hc hv
local notation "rawFirst" => nielsenCappedRawCornerFirstFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "weight" => nielsenRawCornerClassWeight hD hNE hFG hfin w hwD hwN J hc hv
local notation "projection" => nielsenCoreClosedModelCompletionMap hD hNE hFG S hr
local notation "completionMap" => nielsenCappedFirstFaceCompletionMap hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "F" => nielsenCappedFirstFaceCompletedCoreMap hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "old" => fuchsianCuspCompletionOld P.asFuchsianDisc
local notation "cusp" => fuchsianCuspCompletionPoint P.asFuchsianDisc

theorem nielsenCappedRawCornerFirstFace_mk (i:ZMod J.n) :
    (rawFirst) (Quotient.mk _ i)=(firstMap) ⟨vertex i,nielsenCyclicVertex_mem_closedModel hD hNE hFG J hv i⟩ := by
  apply Subtype.ext
  exact (nielsenCappedOriginalModelPoint_vertex hD hNE hFG hfin w hwD hwN J hc hv i).symm

/-- Zero weight means an actual original cusp point in the unchanged completion, rather than a formally assigned ideal label. -/
theorem nielsenCappedRawCornerCompletion_not_old_iff (q:V) :
    (completionMap) ((rawFirst) q)∉range (old) ↔ (weight) q=0 := by
  refine Quotient.inductionOn q ?_
  intro i
  rw [nielsenCappedRawCornerFirstFace_mk,nielsenCappedFirstFaceCompletionMap_cover,
    nielsenCoreClosedModelCompletionMap_mem_old_iff,nielsenRawCornerClassWeight_mk,
    nielsenRawCornerWeight_zero_iff_ideal]
  exact ⟨fun h=>le_antisymm (vertex i).norm_le_one (le_of_not_gt h),fun h hn=>(ne_of_lt hn) h⟩

def nielsenRawIdealCuspMap (q:{q:V // (weight) q=0}) :
    FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic :=
  Classical.choose ((fuchsianCuspCompletion_old_or_cusp P.asFuchsianDisc
    ((completionMap) ((rawFirst) q.val))).resolve_left
      ((nielsenCappedRawCornerCompletion_not_old_iff hD hNE hFG hfin w hwD hwN J hc hv S hr q.val).mpr q.property))
local notation "cuspMap" => nielsenRawIdealCuspMap hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenRawIdealCuspMap_spec (q:{q:V // (weight) q=0}) :
    (completionMap) ((rawFirst) q.val)=(cusp) ((cuspMap) q) :=
  Classical.choose_spec ((fuchsianCuspCompletion_old_or_cusp P.asFuchsianDisc
    ((completionMap) ((rawFirst) q.val))).resolve_left
      ((nielsenCappedRawCornerCompletion_not_old_iff hD hNE hFG hfin w hwD hwN J hc hv S hr q.val).mpr q.property))

theorem nielsenRawIdealCuspMap_injective : Function.Injective (cuspMap) := by
  intro q r he
  have hp:(completionMap) ((rawFirst) q.val)=(completionMap) ((rawFirst) r.val):=
    (nielsenRawIdealCuspMap_spec hD hNE hFG hfin w hwD hwN J hc hv S hr q).trans
      ((congrArg (cusp) he).trans (nielsenRawIdealCuspMap_spec hD hNE hFG hfin w hwD hwN J hc hv S hr r).symm)
  have hF:(F) ((rawFirst) q.val)=(F) ((rawFirst) r.val):=Subtype.ext hp
  apply Subtype.ext
  exact nielsenCappedRawCornerFirstFace_injective hD hNE hFG hfin w hwD hwN J hc hv
    ((nielsenCappedFirstFaceCompletedCoreMap_isHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr).injective hF)

theorem nielsenRawIdealCuspMap_surjective : Function.Surjective (cuspMap) := by
  intro c
  obtain ⟨p,hp⟩:=nielsenCoreClosedModelCompletionMap_cusp_mem_range hD hNE hFG S hr w hwD hwN c
  have hn:¬‖(p.val:ℂ)‖<1:=by
    intro hn
    exact fuchsianCuspCompletionPoint_not_mem_old P.asFuchsianDisc c
      (hp ▸ (nielsenCoreClosedModelCompletionMap_mem_old_iff hD hNE hFG S hr p).mpr hn)
  have hideal:‖(p.val:ℂ)‖=1:=le_antisymm p.val.norm_le_one (le_of_not_gt hn)
  obtain ⟨i,hi⟩:=nielsenCoreClosedModel_ideal_is_cyclicVertex hD hNE hFG hfin w hwD hwN J hv p hideal
  have hq:(weight) (Quotient.mk _ i)=0:=by
    rw [nielsenRawCornerClassWeight_mk,nielsenRawCornerWeight_zero_iff_ideal,hi]
    exact hideal
  let q:{q:V // (weight) q=0}:=⟨Quotient.mk _ i,hq⟩
  refine ⟨q,(fuchsianCuspCompletionPoint_injective P.asFuchsianDisc) ?_⟩
  rw [←nielsenRawIdealCuspMap_spec]
  change (completionMap) ((rawFirst) (Quotient.mk _ i))=(cusp) c
  rw [nielsenCappedRawCornerFirstFace_mk,nielsenCappedFirstFaceCompletionMap_cover]
  have he:(⟨vertex i,nielsenCyclicVertex_mem_closedModel hD hNE hFG J hv i⟩:K)=p:=Subtype.ext hi
  rw [he]
  exact hp

/-- Genuine zero-weight raw classes are exactly all original maximal parabolic conjugacy classes. -/
def nielsenRawIdealCuspEquiv : {q:V // (weight) q=0}≃
    FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic :=
  Equiv.ofBijective (cuspMap) ⟨nielsenRawIdealCuspMap_injective hD hNE hFG hfin w hwD hwN J hc hv S hr,
    nielsenRawIdealCuspMap_surjective hD hNE hFG hfin w hwD hwN J hc hv S hr⟩

include S hr in
theorem nielsenRawIdealClassCount_eq_actualCusps :
    nielsenRawIdealClassCount hD hNE hFG hfin w hwD hwN J hc hv=
      Nat.card (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) := by
  have he:=Nat.card_congr (nielsenRawIdealCuspEquiv hD hNE hFG hfin w hwD hwN J hc hv S hr)
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype] at he
  exact he

end NielsenCappedActualCusps



section NielsenCappedClockOriginal
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "mk" => FiniteCyclicPresentation.polygonalMk (Pcap) (valid)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "ρ" => nielsenCyclicBoundaryEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "index" => originalCyclicFinIndex J
local notation "occIndex" => nielsenCappedOccurrenceIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "dart" => nielsenCapFiniteDartEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "capFace" => nielsenCapBoundaryOccurrences hD hNE hFG hfin w hwD hwN J hc hv
local notation "capList" => nielsenBoundaryCapList hD hNE hFG hfin w hwD hwN J hc hv
local notation "γ" => nielsenCyclicSideParam hD hNE hFG hfin w hwD hwN J hc hv
local notation "E" => nielsenCappedOriginalFaceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv
local notation "hlen" => nielsenCappedOriginalFace_length hD hNE hFG hfin w hwD hwN J hc hv
local notation "oldOccurrence" => nielsenCappedOriginalOccurrence hD hNE hFG hfin w hwD hwN J hc hv

def nielsenCappedCapCycle (f:(Pcap).Face) (hf:f≠f₀) : C :=
  Classical.choose (nielsenCappedPresentation_other_boundary hD hNE hFG hfin w hwD hwN J hc hv f hf)
local notation "capCycle" => nielsenCappedCapCycle hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedCapCycle_spec (f:(Pcap).Face) (hf:f≠f₀) :
    (Pcap).boundary f=(capFace ((capCycle) f hf)).map (dart) :=
  Classical.choose_spec (nielsenCappedPresentation_other_boundary hD hNE hFG hfin w hwD hwN J hc hv f hf)

theorem nielsenCappedCapOccurrence_cycle (o:(Pcap).BoundaryOccurrence) (hf:o.1≠f₀) :
    ∃b:B,(occIndex) o=Sum.inr b ∧ (Quotient.mk (Equiv.Perm.SameCycle.setoid (ρ)) b:C)=(capCycle) o.1 hf := by
  have hd:o.dart∈(Pcap).boundary o.1:=List.get_mem _ o.2
  rw [nielsenCappedCapCycle_spec hD hNE hFG hfin w hwD hwN J hc hv o.1 hf] at hd
  obtain ⟨x,hx,hxd⟩:=List.mem_map.mp hd
  have hix:x=(occIndex) o:=(dart).injective (hxd.trans (nielsenCappedOccurrenceIndex_dart hD hNE hFG hfin w hwD hwN J hc
    hv o).symm)
  rw [hix] at hx
  obtain ⟨b,hb,hmem⟩:=(nielsenCapBoundaryOccurrences_mem hD hNE hFG hfin w hwD hwN J hc hv _ _).mp hx
  exact ⟨b,hb,(nielsenBoundaryCapList_mem_iff hD hNE hFG hfin w hwD hwN J hc hv _ b).mp hmem⟩

theorem nielsenCappedCapCycle_occurrence (f:(Pcap).Face) (hf:f≠f₀) (b:B)
    (hb:(Quotient.mk (Equiv.Perm.SameCycle.setoid (ρ)) b:C)=(capCycle) f hf) :
    ∃i:Fin ((Pcap).boundary f).length,(occIndex) ⟨f,i⟩=Sum.inr b := by
  have hm:(dart) (Sum.inr b)∈(Pcap).boundary f:=by
    rw [nielsenCappedCapCycle_spec hD hNE hFG hfin w hwD hwN J hc hv f hf]
    apply List.mem_map.mpr
    refine ⟨Sum.inr b,?_,rfl⟩
    exact (nielsenCapBoundaryOccurrences_mem hD hNE hFG hfin w hwD hwN J hc hv _ _).mpr
      ⟨b,rfl,(nielsenBoundaryCapList_mem_iff hD hNE hFG hfin w hwD hwN J hc hv _ b).mpr hb⟩
  obtain ⟨i,hi⟩:=List.mem_iff_get.mp hm
  refine ⟨i,(dart).injective ?_⟩
  rw [nielsenCappedOccurrenceIndex_dart]
  exact hi

/-- The actual cap-side traversal is identified with the reverse traversal of its own original free side at every parameter. -/
theorem nielsenCappedCapSide_eq_original (o:(Pcap).BoundaryOccurrence) (b:B)
    (hb:(occIndex) o=Sum.inr b) (t:unitInterval) :
    (mk) (((Pcap).occurrenceSide o).point t)=
      (mk) (((Pcap).occurrenceSide ((oldOccurrence) ((index).symm b.val))).point (unitInterval.symm t)) := by
  have hclosed:=nielsenCappedPresentation_closed hD hNE hFG hfin w hwD hwN J hc hv o.edge
  have hnot:¬(Pcap).IsBoundaryEdge o.edge:=by change (Pcap).edgeMultiplicity o.edge≠1;omega
  obtain ⟨p,hp⟩:=(valid).exists_pairing_source o hnot
  have ht:p.target=(oldOccurrence) ((index).symm b.val):=by
    rw [nielsenCappedBoundaryPairing_target hD hNE hFG hfin w hwD hwN J hc hv p,hp]
    apply (occIndex).injective
    simp only [nielsenCappedOccurrencePartner,Equiv.apply_symm_apply,hb,nielsenCapOccurrencePair,
      nielsenCappedOriginalOccurrence_index]
  have hparam:p.identification.parameter t=unitInterval.symm t:=by
    change p.direction.homeomorph t=unitInterval.symm t
    rw [nielsenCappedBoundaryPairing_direction hD hNE hFG hfin w hwD hwN J hc hv p]
    rfl
  have he:=(Pcap).polygonalMk_pairing_eq (valid) p t
  change (mk) (((Pcap).occurrenceSide p.source).point t)=
    (mk) (((Pcap).occurrenceSide p.target).point (p.identification.parameter t)) at he
  rwa [hp,ht,hparam] at he

variable {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "firstMap" => nielsenCappedFirstFaceImageMap hD hNE hFG hfin w hwD hwN J hc hv
local notation "completionMap" => nielsenCappedFirstFaceCompletionMap hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "old" => fuchsianCuspCompletionOld P.asFuchsianDisc
local notation "π" => Surfaces.mobiusDomainProjection P.domain

/-- The natural first-face completion homeomorphism sends each literal cap boundary parameter to its unchanged original quotient representative. -/
theorem nielsenCappedCapSide_completion_projection (o:(Pcap).BoundaryOccurrence) (ho:o.1≠f₀)
    (b:B) (hb:(occIndex) o=Sum.inr b) (t:unitInterval)
    (x:P.domain.carrier)
    (hx:Hyperbolic.discToClosedModel (P.finiteCoordinate x)=(γ)
    ((index).symm b.val)
    (unitInterval.symm t)) :
    (completionMap) ⟨(mk) (((Pcap).occurrenceSide o).point t),
      nielsenCappedCapSide_mem_firstFace hD hNE hFG hfin w hwD hwN J hc hv o ho t⟩=(old) ((π) x) := by
  let i:Fin J.n:=(index).symm b.val
  let p:K:=(E) (PolygonCell.side (Fin.cast (hlen).symm i) (unitInterval.symm t))
  have hp:p.val=(γ) i (unitInterval.symm t):=
    nielsenCappedOriginalFaceHomeomorph_side hD hNE hFG hfin w hwD hwN J hc hv i (unitInterval.symm t)
  have hxK:Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈K:=hx.symm ▸ (hp ▸ p.property)
  let a:closure Q:=⟨x,(originalFiniteClosedModel_mem_iff x).mp hxK⟩
  have hpfin:p=nielsenCappedFiniteModelPoint hNE a:=Subtype.ext (hp.trans hx.symm)
  have hword:(mk) (((Pcap).occurrenceSide o).point t)=(modelPoint) p:=by
    rw [nielsenCappedCapSide_eq_original hD hNE hFG hfin w hwD hwN J hc hv o b hb t]
    exact (nielsenCappedOriginalModelPoint_side hD hNE hFG hfin w hwD hwN J hc hv p i (unitInterval.symm t) hp).symm
  have he:(⟨(mk) (((Pcap).occurrenceSide o).point t),
      nielsenCappedCapSide_mem_firstFace hD hNE hFG hfin w hwD hwN J hc hv o ho t⟩:↥(range
        (modelPoint)))=(firstMap) p:=Subtype.ext hword
  rw [he,nielsenCappedFirstFaceCompletionMap_cover,hpfin,nielsenCoreClosedModelCompletionMap_finite]

end NielsenCappedClockOriginal



section NielsenCappedClockCycles
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
  {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "mk" => FiniteCyclicPresentation.polygonalMk (Pcap) (valid)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "ρ" => nielsenCyclicBoundaryEquiv hD hNE hFG hfin w hwD hwN J hc hv
local notation "index" => originalCyclicFinIndex J
local notation "occIndex" => nielsenCappedOccurrenceIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "γ" => nielsenCyclicSideParam hD hNE hFG hfin w hwD hwN J hc hv
local notation "edge" => nielsenCyclicEdge hD hNE hFG J hv
local notation "nativeEdge" => nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "capCycle" => nielsenCappedCapCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "completionMap" => nielsenCappedFirstFaceCompletionMap hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "old" => fuchsianCuspCompletionOld P.asFuchsianDisc
local notation "π" => Surfaces.mobiusDomainProjection P.domain
local notation "clock" => nielsenCappedCapClock hD hNE hFG hfin w hwD hwN J hc hv

/-- The real cap clock transported through the actual first-face map into the original completion. -/
def nielsenCappedOriginalCapClock (f:(Pcap).Face) (hf:f≠f₀) : Circle → FuchsianCuspCompletion P.asFuchsianDisc :=
  fun z=>(completionMap) ⟨(clock) f z,by
    have hz:(clock) f z∈range ((clock) f):=mem_range_self z
    exact ((nielsenCappedCapClock_range hD hNE hFG hfin w hwD hwN J hc hv f hf) ▸ hz).2⟩
local notation "originalClock" => nielsenCappedOriginalCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr

/-- The transported clock has precisely its unchanged original whole-group projected boundary cycle as range. -/
theorem nielsenCappedOriginalCapClock_range (f:(Pcap).Face) (hf:f≠f₀) :
    range ((originalClock) f hf)=(old) '' (cycleCarrier ((capCycle) f hf)) := by
  ext y
  constructor
  · rintro ⟨z,rfl⟩
    have hlen:0<((Pcap).boundary f).length:=List.length_pos_iff.mpr
      (nielsenCappedPresentation_boundary_ne_nil hD hNE hFG hfin w hwD hwN J hc hv f)
    obtain ⟨i,t,hit⟩:=PolygonCell.exists_side_eq_of_mem_sphere hlen
      (PolygonCell.ofCircle ((Pcap).boundary f).length z) z.property
    let o:(Pcap).BoundaryOccurrence:=⟨f,i⟩
    obtain ⟨b,hb,hbc⟩:=nielsenCappedCapOccurrence_cycle hD hNE hFG hfin w hwD hwN J hc hv o hf
    have hγ:(γ) ((index).symm b.val) (unitInterval.symm t)∈edge b.val:=by
      have hm:=range_nielsenCyclicSideParam hD hNE hFG hfin w hwD hwN J hc hv ((index).symm b.val)
      rw [Equiv.apply_symm_apply] at hm
      exact hm ▸ mem_range_self (unitInterval.symm t)
    obtain ⟨x,hx⟩:=nielsenCyclicBoundaryEdge_finite hD hNE hFG hfin w hwD hwN J hc hv b _ hγ
    have hxE:x∈nativeEdge b:=(mem_nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv b x).mpr (hx.symm ▸
      hγ)
    have he:(originalClock) f hf z=(old) ((π) x):=by
      let zX:↥(range (modelPoint)):=⟨(clock) f z,by
        have hz:(clock) f z∈range ((clock) f):=mem_range_self z
        exact ((nielsenCappedCapClock_range hD hNE hFG hfin w hwD hwN J hc hv f hf) ▸ hz).2⟩
      let aX:↥(range (modelPoint)):=⟨(mk) (((Pcap).occurrenceSide o).point t),
        nielsenCappedCapSide_mem_firstFace hD hNE hFG hfin w hwD hwN J hc hv o hf t⟩
      have hpoint:zX=aX:=by
        apply Subtype.ext
        exact congrArg (fun a:PolygonCell ((Pcap).boundary f).length=>(mk) ⟨f,a⟩) hit.symm
      change (completionMap) zX=_
      rw [hpoint]
      exact nielsenCappedCapSide_completion_projection hD hNE hFG hfin w hwD hwN J hc hv S hr o hf b hb t x hx
    exact ⟨(π) x,mem_iUnion.mpr ⟨⟨b,hbc⟩,x,hxE,rfl⟩,he.symm⟩
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨b,x,hx,rfl⟩:=mem_iUnion.mp hq
    have hxE:Hyperbolic.discToClosedModel (P.finiteCoordinate x)∈edge b.val.val:=
      (mem_nielsenCyclicBoundaryNativeEdge hD hNE hFG hfin w hwD hwN J hc hv b.val x).mp hx
    have hm:=range_nielsenCyclicSideParam hD hNE hFG hfin w hwD hwN J hc hv ((index).symm b.val.val)
    rw [Equiv.apply_symm_apply] at hm
    obtain ⟨u,hu⟩:=hm.symm ▸ hxE
    obtain ⟨i,hi⟩:=nielsenCappedCapCycle_occurrence hD hNE hFG hfin w hwD hwN J hc hv f hf b.val b.property
    refine ⟨Surfaces.polygonSideCircleCover ((Pcap).boundary f).length ⟨i,unitInterval.symm u⟩,?_⟩
    change (completionMap) ⟨(mk) (((Pcap).occurrenceSide ⟨f,i⟩).point (unitInterval.symm u)),_⟩=_
    apply nielsenCappedCapSide_completion_projection hD hNE hFG hfin w hwD hwN J hc hv S hr ⟨f,i⟩ hf b.val hi (unitInterval.symm u) x
    rw [unitInterval.symm_symm]
    exact hu.symm

end NielsenCappedClockCycles



section NielsenCompletedCoreGeometricCaps
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
  {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "W" => FiniteCyclicPresentation.PolygonalRealization
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv)
  (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)
local notation "A" => {f:FiniteCyclicPresentation.Face
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv) //
  f≠nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv}
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "coreHomeo" => nielsenCappedFirstFaceCompletedCoreHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "F" => nielsenCappedFirstFaceCompletedCoreMap hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "openCap" => nielsenCappedFaceInterior hD hNE hFG hfin w hwD hwN J hc hv
local notation "closedCap" => nielsenCappedClosedCap hD hNE hFG hfin w hwD hwN J hc hv
local notation "clock" => nielsenCappedCapClock hD hNE hFG hfin w hwD hwN J hc hv
local notation "originalClock" => nielsenCappedOriginalCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "capCycle" => nielsenCappedCapCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv

/-- The unchanged actual completed Nielsen quotient is embedded as the actual first-face image of the same faithful capped surface. -/
def nielsenCompletedCoreCappedEmbedding : ↥(nielsenCompletedCoreSet P hNE) → W :=
  Subtype.val ∘ (coreHomeo).symm
local notation "coreEmbedding" => nielsenCompletedCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenCompletedCoreCappedEmbedding_range : range (coreEmbedding)=range (modelPoint) := by
  ext y
  constructor
  · rintro ⟨z,rfl⟩
    exact ((coreHomeo).symm z).property
  · intro hy
    refine ⟨(coreHomeo) ⟨y,hy⟩,?_⟩
    change ((coreHomeo).symm ((coreHomeo) ⟨y,hy⟩)).val=y
    rw [Homeomorph.symm_apply_apply]

theorem nielsenCompletedCoreCappedEmbedding_isClosedEmbedding : Topology.IsClosedEmbedding (coreEmbedding) := by
  obtain ⟨g,hg,_⟩:=nielsenCappedPresentation_genus hD hNE hFG hfin w hwD hwN J hc hv
  let:T2Space W:=Surfaces.HandleSeparation.hasTopologicalGenus_t2Space hg
  let:CompactSpace K:=isCompact_iff_compactSpace.mp (Hyperbolic.isCompact_discClosedModelClosure _)
  have hclosed:IsClosed (range (modelPoint)):=
    (isCompact_range (continuous_nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv)).isClosed
  exact hclosed.isClosedEmbedding_subtypeVal.comp (coreHomeo).symm.isClosedEmbedding

/-- The actual boundary clock in the original quotient, viewed as a point of the unchanged completed core. -/
def nielsenCompletedCoreCapClock (f:A) (z:Circle) : ↥(nielsenCompletedCoreSet P hNE) :=
  (F) ⟨(clock) f.val z,by
    have hz:(clock) f.val z∈range ((clock) f.val):=mem_range_self z
    exact ((nielsenCappedCapClock_range hD hNE hFG hfin w hwD hwN J hc hv f.val f.property) ▸ hz).2⟩
local notation "coreClock" => nielsenCompletedCoreCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenCompletedCoreCapClock_original (f:A) (z:Circle) :
    ((coreClock) f z).val=(originalClock) f.val f.property z := rfl

theorem nielsenCompletedCoreCapClock_filling (f:A) (z:Circle) :
    (coreEmbedding) ((coreClock) f z)=(clock) f.val z := by
  change ((coreHomeo).symm ((coreHomeo) _)).val=_
  rw [Homeomorph.symm_apply_apply]

/-- actual original elliptic orders, actual cusp classes and actual boundary classes appear in the area identity of the same genuine geometrically capped Nielsen quotient. -/
theorem nielsenCompletedCore_geometric_caps_area :
    let _nielsenGeometricCapsEllipticFinite : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
      finite_sided_polygon_elliptic_classes_finite hD hfin
    ∃g,Surfaces.HasTopologicalGenus W g ∧
      Topology.IsClosedEmbedding (coreEmbedding) ∧
      (range (coreEmbedding))ᶜ=⋃f:A,range ((openCap) f.val) ∧
      (∀f:A,Topology.IsOpenEmbedding ((openCap) f.val)) ∧
      (∀f:A,Topology.IsClosedEmbedding ((closedCap) f.val)) ∧
      Pairwise (fun f k:A=>Disjoint (range ((closedCap) f.val)) (range ((closedCap) k.val))) ∧
      (∀f:A,Topology.IsClosedEmbedding ((clock) f.val)) ∧
      (∀f:A,range ((originalClock) f.val f.property)=
        (fuchsianCuspCompletionOld P.asFuchsianDisc) '' (cycleCarrier ((capCycle) f.val f.property))) ∧
      (∀f:A,∀z:Circle,(coreEmbedding) ((coreClock) f z)=(clock) f.val z) ∧
      Nat.card A=Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc) ∧
      (fuchsianNielsenCoreArea P hNE D).toReal=2*Real.pi*
        (2*(g:ℝ)-2+Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc)+
          Nat.card (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic)+
          ((fuchsianEllipticOrderList P.asFuchsianDisc).map (fun m:ℕ=>1-1/(m:ℝ))).sum) := by
  let _nielsenGeometricCapsEllipticFinite : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    finite_sided_polygon_elliptic_classes_finite hD hfin
  obtain ⟨g,hg,ha⟩:=nielsenCappedWord_genus_actualBoundaryElliptic_area hD hNE hFG hfin w hwD hwN J hc hv
  rw [nielsenRawIdealClassCount_eq_actualCusps hD hNE hFG hfin w hwD hwN J hc hv S hr] at ha
  refine ⟨g,hg,nielsenCompletedCoreCappedEmbedding_isClosedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr,?_,
    (fun f=>nielsenCappedFaceInterior_isOpenEmbedding hD hNE hFG hfin w hwD hwN J hc hv f.val),
    (fun f=>nielsenCappedClosedCap_isClosedEmbedding hD hNE hFG hfin w hwD hwN J hc hv f.val f.property),
    nielsenCappedClosedCap_pairwise_disjoint hD hNE hFG hfin w hwD hwN J hc hv,
    (fun f=>nielsenCappedCapClock_isClosedEmbedding hD hNE hFG hfin w hwD hwN J hc hv f.val f.property),
    (fun f=>nielsenCappedOriginalCapClock_range hD hNE hFG hfin w hwD hwN J hc hv S hr f.val f.property),
    nielsenCompletedCoreCapClock_filling hD hNE hFG hfin w hwD hwN J hc hv S hr,
    nielsenCappedCapFaceCount_eq hD hNE hFG hfin w hwD hwN J hc hv,ha⟩
  rw [nielsenCompletedCoreCappedEmbedding_range]
  exact nielsenCappedFirstFace_complement_eq hD hNE hFG hfin w hwD hwN J hc hv

end NielsenCompletedCoreGeometricCaps

end LowDimensionalTopology.Geometry.Fuchsian
