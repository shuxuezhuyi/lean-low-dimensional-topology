/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.LowGenusUniqueness
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Area.OriginalActualSignatureArea
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
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open scoped Classical
local instance lowGenusSignatureAreaSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance lowGenusSignatureAreaSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=⟨rfl⟩

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 1000000 in
/-- A given genuine original signature of genus zero or one determines the original actual finite quotient area. No uniqueness for higher genus is asserted. -/
theorem cofinite_signature_area_of_genus_le_one {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D₀ : FuchsianDisc H) (F : Set (fuchsianGeometricDomain D₀).carrier)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain
      D₀).carrier (geometricModelArea D₀) F)
    (harea : geometricModelArea D₀ F≠⊤) (g p : ℕ) (orders : List ℕ)
    (hSig : HasCofiniteFuchsianSignature D₀ g orders p) (hg : g≤1) :
    (geometricModelArea D₀ F).toReal=2*Real.pi*(2*(g : ℝ)-2+(p : ℝ)+
      (orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum) := by
  let _lowGenusSignatureOriginalFinite : Finite (FuchsianCyclicConjugacyClasses D₀ .elliptic):=
    hSig.ellipticClassesFinite
  obtain ⟨g',hg',hA⟩:=finite_area_original_actual_signature_area D₀ F hF harea
  have he : g=g':=_root_.LowDimensionalTopology.Geometry.Surfaces.hasTopologicalGenus_unique_of_le_one hSig.topologicalGenus hg' hg
  have hp : (orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum=
      ((fuchsianEllipticOrderList D₀).map (fun m : ℕ=>1-1/(m : ℝ))).sum:=
    (hSig.ellipticOrders.map (fun m : ℕ=>1-1/(m : ℝ))).sum_eq
  rwa [←he,←hSig.cuspCount,←hp] at hA

end LowDimensionalTopology.Geometry.Fuchsian
