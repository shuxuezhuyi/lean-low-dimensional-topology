/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CanonicalHandleEuler
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.OriginalFirstKindArea
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Area.OriginalActualSignatureArea
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
local instance originalSignatureAreaSphereMeasurable : MeasurableSpace Mobius.ExtendedComplex:=borel Mobius.ExtendedComplex
local instance originalSignatureAreaSphereBorel : BorelSpace Mobius.ExtendedComplex:=⟨rfl⟩

/-- The genuine signature of the original finitely generated first-kind group determines every actual original fundamental-domain area. -/
theorem cofinite_area_eq_two_pi_mul_signatureDeficit
    {H : Subgroup Mobius.complexMobiusGroup}
    (D₀ : FuchsianDisc H) (hfirst : D₀.IsFirstKind) (hFG : H.FG)
    (F : Set (fuchsianGeometricDomain D₀).carrier)
    (hF : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain H (fuchsianGeometricDomain D₀).carrier (geometricModelArea D₀) F)
    (g p : ℕ) (orders : List ℕ) (hSig : HasCofiniteFuchsianSignature D₀ g orders p) :
    (geometricModelArea D₀ F).toReal=2*Real.pi*(2*(g : ℝ)-2+(p : ℝ)+
      (orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum) := by
  let _originalSignatureOriginalFinite : Finite (FuchsianCyclicConjugacyClasses D₀ .elliptic):=
    hSig.ellipticClassesFinite
  obtain ⟨g',hg',hA⟩:=finite_area_original_actual_signature_area D₀ F hF
    (firstKind_finitelyGenerated_geometricArea_ne_top D₀ hfirst hFG F hF)
  have he : g=g':=_root_.LowDimensionalTopology.Geometry.Surfaces.hasTopologicalGenus_unique hSig.topologicalGenus hg'
  have hp : (orders.map (fun m : ℕ=>1-1/(m : ℝ))).sum=
      ((fuchsianEllipticOrderList D₀).map (fun m : ℕ=>1-1/(m : ℝ))).sum:=
    (hSig.ellipticOrders.map (fun m : ℕ=>1-1/(m : ℝ))).sum_eq
  rwa [←he,←hSig.cuspCount,←hp] at hA

end LowDimensionalTopology.Geometry.Fuchsian
