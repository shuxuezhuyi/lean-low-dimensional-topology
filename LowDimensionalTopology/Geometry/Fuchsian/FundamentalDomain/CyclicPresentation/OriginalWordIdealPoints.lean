/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.CyclicPresentation.OriginalCyclicPreGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaPolygonBoundary
/-!
# Ideal points of the polygon word

The closed disc-model coordinates define the ideal preface points and their
images in the word realization. These sets are finite, and the finite part
is dense because the compactified polygon is the closure of its original points.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Topology
open scoped Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open LeanEval.Topology.ClassificationOfSurfaces.Moise

variable {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D) (ha:P.area D≠⊤)
  (J:PolygonalCircle)
  (hc:J.carrier=_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane '' (⋃v:OriginalRefinedSide
    hD,v.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈_root_.LowDimensionalTopology.Geometry.Polygon.discPolygonKleinPlane ''
    originalRefinedEndpointSet hD)
  (e:ZMod J.n≃OriginalRefinedSide hD) (hs:∀i,J.edgeSegment i=(e i).planeCarrier)

/-- The actual ideal points of the stored original word face, using its proved
homeomorphism to the unchanged original compact polygon closure. -/
def originalCyclicPreIdealPoints :
    Set (originalCyclicPresentation J e).presentation.PolygonalPreRealization :=
  {a|‖((originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs a).val:ℂ)‖=1}

/-- The finitely many literal ideal points of the original stored word quotient. -/
def originalCyclicWordIdealPoints :
    Set ((originalCyclicPresentation J e).presentation.PolygonalRealization
      (originalCyclicPresentation J e).valid) :=
  (originalCyclicPresentation J e).presentation.polygonalMk (originalCyclicPresentation J e).valid ''
    originalCyclicPreIdealPoints hD ha J hc hv e hs

theorem originalCyclicPreIdealPoints_finite :
    (originalCyclicPreIdealPoints hD ha J hc hv e hs).Finite := by
  let B:=originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs
  let f:(originalCyclicPresentation J e).presentation.PolygonalPreRealization→ℂ:=
    fun a=>(B a).val
  have hf:Function.Injective f:=by
    intro a b hab
    apply B.injective
    apply Subtype.ext
    exact Subtype.ext hab
  apply ((finite_area_polygon_idealBoundary_finite hD ha).preimage hf.injOn).subset
  intro a hai
  apply (mem_fuchsianPolygonIdealBoundary P D (f a)).mpr
  refine ⟨?_,hai⟩
  have hz:(B a).val∈closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel '' (P.finiteCoordinate
    '' D)):=(B a).property
  have hm:=mem_closure_image (Complex.UnitClosedDisc.continuous_coe.continuousAt) hz
  simpa only [image_image,Function.comp_def,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel,Complex.UnitClosedDisc.coe_mk] using hm

/-- Actual finite polygon points are dense in its actual compactified model closure;
this uses the defining closure and imposes no extra puncture-density assumption. -/
theorem originalClosedModel_finitePart_dense :
    Dense {z:↥(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))|‖(z.val:ℂ)‖<1} := by
  apply Subtype.dense_iff.mpr
  intro z hz
  apply closure_mono (t:=Subtype.val ''
    {z:↥(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate ''
      D))|‖(z.val:ℂ)‖<1}) ?_ hz
  rintro _ ⟨w,hw,rfl⟩
  exact ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel w,subset_closure (mem_image_of_mem
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel hw)⟩,
    w.norm_lt_one,rfl⟩

/-- Deleting precisely the true ideal face points leaves a dense actual finite part. -/
theorem originalCyclicPreIdealPoints_compl_dense :
    Dense (originalCyclicPreIdealPoints hD ha J hc hv e hs)ᶜ := by
  let B:=originalCyclicPreClosedModelHomeomorph hD ha J hc hv e hs
  have he:(originalCyclicPreIdealPoints hD ha J hc hv e hs)ᶜ=
      B⁻¹'{z:↥(_root_.LowDimensionalTopology.Geometry.Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' D))|‖(z.val:ℂ)‖<1}:=by
    ext a
    change (¬‖((B a).val:ℂ)‖=1)↔‖((B a).val:ℂ)‖<1
    exact ⟨fun h=>lt_of_le_of_ne (B a).val.norm_le_one h,fun h=>ne_of_lt h⟩
  rw [he]
  exact (originalClosedModel_finitePart_dense (P:=P) (D:=D)).preimage B.isOpenMap

theorem originalCyclicWordIdealPoints_finite :
    (originalCyclicWordIdealPoints hD ha J hc hv e hs).Finite :=
  (originalCyclicPreIdealPoints_finite hD ha J hc hv e hs).image _

end LowDimensionalTopology.Geometry.Fuchsian
