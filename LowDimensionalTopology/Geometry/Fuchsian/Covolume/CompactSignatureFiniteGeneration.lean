/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.CompactCuspArea
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Boundary.FiniteAreaPolygonSides
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Topology
open scoped OnePoint UpperHalfPlane Pointwise ENNReal
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance compactSignatureFiniteGenerationSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance compactSignatureFiniteGenerationSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-- Finite generation follows from the actual compact signature, through a constructed genuine original fundamental domain and its proved finite area. -/
theorem HasCofiniteFuchsianSignature.finitelyGenerated {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {g p : ℕ} {orders : List ℕ}
    (hSig : HasCofiniteFuchsianSignature D g orders p) : H.FG := by
  let _compactSignatureFGCompletion : CompactSpace (FuchsianCuspCompletion D):=hSig.compact
  let _compactSignatureFGCusps : Finite (FuchsianCyclicConjugacyClasses D .parabolic):=hSig.parabolicClassesFinite
  obtain ⟨w,hw⟩:=finite_area_exists_dirichlet_center (geometricDiscData D)
  have hL:=dirichletDomain_isConvexFuchsianPolygon (geometricDiscData D) w hw
  have hF:=geometricModel_fundamentalDomain_of_disc D hL.locallyFinite.fundamental
  exact finite_area_group_finitelyGenerated D _ hF (compact_cuspCompletion_geometricArea_ne_top D _ hF)

end LowDimensionalTopology.Geometry.Fuchsian
