/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalIdealRawVertices
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalRawCornerRealization
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CornerCycle.OriginalRawParabolicProfiles
/-!
# Zero-weight classes as ideal word points

A zero-weight raw corner class determines an ideal point of the word
realization. Faithful corner labels and completeness of the marked ideal
vertices make this correspondence a bijection.
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
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
section RawIdealPoints
variable {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
    {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
    (J:PolygonalCircle)
    (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
      hD,v.carrier))
    (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
      originalRefinedEndpointSet hD)
    (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)

/-- Every actual zero-weight raw corner class gives its genuine ideal point of the unchanged word realization. -/
def originalRawIdealWordPoint
    (q:{q:Quotient (originalRawCornerSetoid J e)//originalRawCornerClassWeight hD ha J hc hv e hs q=0}) :
    ↥(originalCyclicWordIdealPoints hD ha J hc hv e hs) := by
  let i:=q.val.out
  have hqi:Quotient.mk (originalRawCornerSetoid J e) i=q.val:=Quotient.out_eq _
  have hni:‖(originalCyclicVertex hD J hv i:ℂ)‖=1:=
    (originalRawCornerClassWeight_zero_iff_ideal hD ha J hc hv e hs q.val).mp q.property
  let a:=((originalCyclicPresentation J e).presentation.occurrenceSide
    ((originalCyclicCornerIndex J e).symm i)).point 0
  have ha':a∈originalCyclicPreIdealPoints hD ha J hc hv e hs:=by
    change ‖((originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs a).val:ℂ)‖=1
    rw [originalCyclicPreClosedModelHomeomorph_corner]
    exact hni
  refine ⟨originalCyclicRawCornerPoint J e q.val,a,ha',?_⟩
  rw [←hqi,originalCyclicRawCornerPoint_mk]

theorem originalRawIdealWordPoint_injective : Function.Injective
    (originalRawIdealWordPoint hD ha J hc hv e hs) := by
  intro q r hqr
  apply Subtype.ext
  exact originalCyclicRawCornerPoint_injective J e (congrArg Subtype.val hqr)

/-- The actual marked corners contain every genuine ideal point of the word surface. -/
theorem originalRawIdealWordPoint_surjective : Function.Surjective
    (originalRawIdealWordPoint hD ha J hc hv e hs) := by
  intro x
  obtain ⟨a,ha',he⟩:=x.property
  obtain ⟨i,hai,hni⟩:=originalCyclicPreIdealPoint_is_rawCorner hD ha J hc hv e hs a ha'
  let q:{q:Quotient (originalRawCornerSetoid J e)//originalRawCornerClassWeight hD ha J hc hv e hs q=0}:=
    ⟨Quotient.mk _ i,originalRawCornerClassWeight_ideal hD ha J hc hv e hs i hni⟩
  refine ⟨q,Subtype.ext ?_⟩
  change originalCyclicRawCornerPoint J e (Quotient.mk _ i)=x.val
  rw [originalCyclicRawCornerPoint_mk,←hai]
  exact he

/-- Zero-weight raw classes and actual ideal word points are genuinely the same finite data. -/
def originalRawIdealWordEquiv :
    {q:Quotient (originalRawCornerSetoid J e)//originalRawCornerClassWeight hD ha J hc hv e hs q=0}≃
      ↥(originalCyclicWordIdealPoints hD ha J hc hv e hs) :=
  Equiv.ofBijective (originalRawIdealWordPoint hD ha J hc hv e hs)
    ⟨originalRawIdealWordPoint_injective hD ha J hc hv e hs,
      originalRawIdealWordPoint_surjective hD ha J hc hv e hs⟩
end RawIdealPoints
end LowDimensionalTopology.Geometry.Fuchsian
