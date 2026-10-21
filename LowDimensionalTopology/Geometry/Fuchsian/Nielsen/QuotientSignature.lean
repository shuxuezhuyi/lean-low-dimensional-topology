module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.FiniteHull
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.Separation
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.QuotientSurface
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Analysis.Convex.Combination
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Data
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Data.Set.UnionLift
public import Mathlib.Topology.Homeomorph.Defs
/-!
# Geometric signatures of finitely generated Fuchsian groups

A Nielsen signature records the genus of the capped quotient surface, the
elliptic orders, and the numbers of cusps and boundary-hyperbolic ends. The
surface in this definition is built from the original group and its Nielsen
core; its genus and end counts are not extra area assumptions.

This module constructs the signature, identifies the whole quotient surface,
and proves the real and extended-real area formulas and uniqueness of genus.
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

open LeanEval.Topology.ClassificationOfSurfaces
/-- A signature of the original group uses the genus of its genuine geometrically
filled Nielsen surface. The theorem below identifies the original whole orbit
surface with this very surface minus its actual cusp and boundary-end points;
no area or genus budget is part of the signature data. -/
def HasNielsenFuchsianSignature {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
    (g:ℕ) (orders:List ℕ) (cusps boundaryEnds:ℕ) : Prop :=
  ∃w:P.domain.carrier,∃hw:IsDirichletCenter P w,∃hwN:w∈fuchsianNielsenCore P hNE,
    let D:=dirichletDomain P w
    let hD:=dirichletDomain_isConvexFuchsianPolygon P w hw
    let hfin:=finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw
    let hwD:=dirichletDomain_center_mem P w hw
    ∃J:Moise.PolygonalCircle,
    ∃hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier),
    ∃hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG,
    ∃n:ℕ,∃S:Polygon.CyclicDiscPolygonSupportData n,
    ∃_hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE),
    let _nielsenOriginalSignatureEllipticFinite:Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
      finite_sided_polygon_elliptic_classes_finite hD hfin
    Surfaces.HasTopologicalGenus
      ((nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv).PolygonalRealization
        (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)) g ∧
      orders.Perm (fuchsianEllipticOrderList P.asFuchsianDisc) ∧
      cusps=Nat.card (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) ∧
      boundaryEnds=Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc)

/-- The group signature is actually constructed; its filled surface is an actual
compactification of the original whole quotient by precisely the genuine ends. -/
theorem finitelyGenerated_hasNielsenFuchsianSignature
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (hFG:H.FG) :
    ∃g orders cusps boundaryEnds,HasNielsenFuchsianSignature P hNE hFG g orders cusps boundaryEnds := by
  obtain ⟨w,hw,hwN,n,S,hr,_⟩:=finitelyGenerated_nielsenCore_polygon P hNE hFG
  let hD:=dirichletDomain_isConvexFuchsianPolygon P w hw
  let hfin:=finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw
  let hwD:=dirichletDomain_center_mem P w hw
  obtain ⟨J,hc,hv⟩:=nielsenCore_actual_marked_cyclic_boundary hD hNE hFG hfin w hwD hwN
  let _nielsenOriginalSignatureEllipticFinite:Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    finite_sided_polygon_elliptic_classes_finite hD hfin
  obtain ⟨g,hg,_⟩:=nielsenCappedWord_genus_actualBoundaryElliptic_area hD hNE hFG hfin w hwD hwN J hc hv
  exact ⟨g,fuchsianEllipticOrderList P.asFuchsianDisc,
    Nat.card (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic),
    Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc),
    w,hw,hwN,J,hc,hv,n,S,hr,hg,List.Perm.refl _,rfl,rfl⟩

/--
For any original fundamental domain: the genus in the
signature is the actual same filled whole-quotient genus, and every order and
end in the formula counts an actual original-group conjugacy class.
-/
theorem HasNielsenFuchsianSignature.area {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {hNE:DiscreteGroups.IsNonElementary H} {hFG:H.FG}
    {g:ℕ} {orders:List ℕ} {cusps boundaryEnds:ℕ}
    (h:HasNielsenFuchsianSignature P hNE hFG g orders cusps boundaryEnds)
    {D:Set P.domain.carrier} (hD:IsFuchsianFundamentalDomain P D) :
    (fuchsianNielsenCoreArea P hNE D).toReal=2*Real.pi*
      (2*(g:ℝ)-2+boundaryEnds+cusps+((orders.map (fun m:ℕ=>1-1/(m:ℝ))).sum)) := by
  obtain ⟨w,hw,hwN,J,hc,hv,n,S,hr,hg,ho,hp,ht⟩:=h
  let hE:=dirichletDomain_isConvexFuchsianPolygon P w hw
  let hfin:=finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw
  let hwD:=dirichletDomain_center_mem P w hw
  have ha:=nielsenCore_area_of_same_capped_surface_genus hE hNE hFG hfin w hwD hwN J hc hv S hr g hg
  rw [fuchsianNielsenCoreArea_independent P hNE hD hE.locallyFinite.fundamental]
  rw [hp,ht]
  rw [signature_elliptic_sum_perm ho]
  exact ha

/-- The exact nonnegative extended-real area formula is equivalent to the real
formula because true finite generation has already proved actual core area finite. -/
theorem HasNielsenFuchsianSignature.area_ennreal
    {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {hNE:DiscreteGroups.IsNonElementary H} {hFG:H.FG}
    {g:ℕ} {orders:List ℕ} {cusps boundaryEnds:ℕ}
    (h:HasNielsenFuchsianSignature P hNE hFG g orders cusps boundaryEnds)
    {D:Set P.domain.carrier} (hD:IsFuchsianFundamentalDomain P D) :
    fuchsianNielsenCoreArea P hNE D=ENNReal.ofReal (2*Real.pi*
      (2*(g:ℝ)-2+boundaryEnds+cusps+((orders.map (fun m:ℕ=>1-1/(m:ℝ))).sum))) := by
  rw [←h.area hD]
  exact (ENNReal.ofReal_toReal (finitelyGenerated_nielsenCoreArea_ne_top P hNE hFG hD)).symm

/-- The signature genus is witnessed by an actual compactification of the
original whole quotient, and the deleted points are the actual cusp/boundary ends. -/
theorem HasNielsenFuchsianSignature.whole_quotient_surface
    {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {hNE:DiscreteGroups.IsNonElementary H} {hFG:H.FG}
    {g:ℕ} {orders:List ℕ} {cusps boundaryEnds:ℕ}
    (h:HasNielsenFuchsianSignature P hNE hFG g orders cusps boundaryEnds) :
    ∃X:Type,∃tX:TopologicalSpace X,∃A:Set X,
      letI:TopologicalSpace X:=tX
      Surfaces.HasTopologicalGenus X g ∧ A.Finite ∧
      Nat.card ↥A=cusps+boundaryEnds ∧
      Nonempty (Surfaces.MobiusDomainQuotient P.domain≃ₜ↥(Aᶜ)) := by
  obtain ⟨w,hw,hwN,J,hc,hv,n,S,hr,hg,_ho,hp,ht⟩:=h
  let hD:=dirichletDomain_isConvexFuchsianPolygon P w hw
  let hfin:=finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw
  let hwD:=dirichletDomain_center_mem P w hw
  let W:=(nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv).PolygonalRealization
    (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)
  let A:=nielsenCappedEndMarks hD hNE hFG hfin w hwD hwN J hc hv S hr
  obtain ⟨E,_⟩:=nielsenWholeQuotient_same_capped_surface hD hNE hFG hfin w hwD hwN J hc hv S hr
  refine ⟨W,inferInstance,A,hg,nielsenCappedEndMarks_finite hD hNE hFG hfin w hwD hwN J hc hv S hr,?_,⟨E⟩⟩
  rw [hp,ht]
  exact nielsenCappedEndMarks_card hD hNE hFG hfin w hwD hwN J hc hv S hr

/-- The finite entries of the actual signature are genuine elliptic orders. -/
theorem HasNielsenFuchsianSignature.orders_two_le
    {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {hNE:DiscreteGroups.IsNonElementary H} {hFG:H.FG}
    {g:ℕ} {orders:List ℕ} {cusps boundaryEnds:ℕ}
    (h:HasNielsenFuchsianSignature P hNE hFG g orders cusps boundaryEnds) : ∀m∈orders,2≤m := by
  obtain ⟨w,hw,_hwN,_J,_hc,_hv,_n,_S,_hr,_hg,ho,_hp,_ht⟩:=h
  let:Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    finite_sided_polygon_elliptic_classes_finite (dirichletDomain_isConvexFuchsianPolygon P w hw)
      (finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw)
  intro m hm
  exact fuchsianEllipticOrderList_two_le P.asFuchsianDisc m (ho.mem_iff.mp hm)

/-- Different actual Dirichlet models and cappings of the same original group
have the same genus; the true invariant Nielsen area removes all model choices. -/
theorem HasNielsenFuchsianSignature.genus_unique
    {H:Subgroup Mobius.complexMobiusGroup}
    {P:UnitDiscFuchsianGroup H} {hNE:DiscreteGroups.IsNonElementary H} {hFG:H.FG}
    {g k:ℕ} {orders orders':List ℕ} {cusps boundaryEnds cusps' boundaryEnds':ℕ}
    (h:HasNielsenFuchsianSignature P hNE hFG g orders cusps boundaryEnds)
    (h':HasNielsenFuchsianSignature P hNE hFG k orders' cusps' boundaryEnds') : g=k := by
  have hSave:=h
  have hSave' :=h'
  obtain ⟨w,hw,_hwN,_J,_hc,_hv,_n,_S,_hr,_hg,ho,hp,ht⟩:=h
  obtain ⟨w',hw',_hwN',_J',_hc',_hv',_n',_S',_hr',_hg',ho',hp',ht'⟩:=h'
  let:Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    finite_sided_polygon_elliptic_classes_finite (dirichletDomain_isConvexFuchsianPolygon P w hw)
      (finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw)
  have hsum:(orders.map (fun m:ℕ=>1-1/(m:ℝ))).sum=(orders'.map (fun m:ℕ=>1-1/(m:ℝ))).sum:=
    signature_elliptic_sum_perm (ho.trans ho'.symm)
  have ha:=hSave.area (dirichletDomain_fundamental P w hw)
  have hb:=hSave'.area (dirichletDomain_fundamental P w hw)
  rw [hp,ht,hsum] at ha
  rw [hp',ht'] at hb
  have hreal:(g:ℝ)=(k:ℝ):=by nlinarith [Real.pi_pos]
  exact_mod_cast hreal


end LowDimensionalTopology.Geometry.Fuchsian
