/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Cusp.FuchsianCuspCompletion
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.FuchsianSignatureOrders
public import LowDimensionalTopology.Geometry.Surfaces.Topology.HandleModels
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped OnePoint UpperHalfPlane MatrixGroups
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

/-- The literal sphere points used by the completion are precisely the original domain and the actual parabolic fixed points of the whole original group. -/
theorem fuchsianCuspCompletion_augmented_carrier_iff
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (p : Mobius.ExtendedComplex) :
    (p∈D.carrier∨∃(c : FuchsianCyclicConjugacyClasses D .parabolic)(g : H),
      g.val.val (fuchsianParabolicPointRepresentative D c).val=p) ↔
      p∈D.carrier∨∃f∈H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f∧f.val p=p := by
  constructor
  · rintro (hp|⟨c,g,rfl⟩)
    · exact Or.inl hp
    · obtain ⟨f,hfH,hf,hfix⟩:=(fuchsianParabolicPointRepresentative D c).property.2
      refine Or.inr ⟨g.val*f*g.val⁻¹,H.mul_mem (H.mul_mem g.property hfH) (H.inv_mem g.property),
        _root_.LowDimensionalTopology.Geometry.Fuchsian.MobiusCyclicType.conjugate hf g.val,?_⟩
      exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_conjugate_fixedpoint f g.val _ hfix
  · rintro (hp|⟨f,hfH,hf,hfix⟩)
    · exact Or.inl hp
    · let z : fuchsianCyclicFixedPoints D .parabolic:=⟨p,(by intro he;cases he),f,hfH,hf,hfix⟩
      obtain ⟨c,g,hg⟩:=fuchsianParabolicPointRepresentative_orbit_cover D z
      exact Or.inr ⟨c,g,hg⟩

/-- The unchanged original quotient embeds analytically, with its genuine original Riemann surface, in the actual simultaneous all-cusp completion. -/
theorem fuchsianCuspCompletionOld_analytic
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) :
    _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap (_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas
      (fuchsianCuspCompletionRiemannSurface D).toRiemannAtlas (fuchsianCuspCompletionOld D) :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspQuotientOld_analytic (fuchsianCuspChartNormalization D) D.discontinuous
    (fuchsianParabolicPointRepresentative_orbits_distinct D) (fuchsianCuspChart_full_stabilizer D)

/-- The genuine normalized exponential chart at a labelled actual cusp of the full original group. -/
def fuchsianCuspCompletionChart {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (c : FuchsianCyclicConjugacyClasses D .parabolic) :
    OpenPartialHomeomorph (FuchsianCuspCompletion D) ℂ :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspNewChart (fuchsianCuspChartNormalization D) D.discontinuous
    (fuchsianParabolicPointRepresentative_orbits_distinct D) c

/-- The actual cusp lies in its actual chart source. -/
theorem fuchsianCuspCompletionPoint_mem_chart
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (c : FuchsianCyclicConjugacyClasses D .parabolic) :
    fuchsianCuspCompletionPoint D c∈(fuchsianCuspCompletionChart D c).source :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspNewChart_newPoint_source (fuchsianCuspChartNormalization D) D.discontinuous
    (fuchsianParabolicPointRepresentative_orbits_distinct D) c

/-- The actual cusp has coordinate zero, not a separate abstract end label. -/
theorem fuchsianCuspCompletionChart_point
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (c : FuchsianCyclicConjugacyClasses D .parabolic) :
    fuchsianCuspCompletionChart D c (fuchsianCuspCompletionPoint D c)=0 :=
  _root_.LowDimensionalTopology.Geometry.Surfaces.multipleCuspNewChart_newPoint (fuchsianCuspChartNormalization D) D.discontinuous
    (fuchsianParabolicPointRepresentative_orbits_distinct D) c

/-- An actual cofinite signature uses the genuine all-cusp filled quotient topology, actual maximal elliptic subgroup orders, and actual maximal parabolic subgroup classes. Area and its signature formula are not fields. This predicate is intended for the cofinite case, not for general second-kind signatures. -/
structure HasCofiniteFuchsianSignature {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (genus : ℕ) (orders : List ℕ) (cusps : ℕ) : Prop where
  ellipticClassesFinite : Finite (FuchsianCyclicConjugacyClasses D .elliptic)
  parabolicClassesFinite : Finite (FuchsianCyclicConjugacyClasses D .parabolic)
  compact : CompactSpace (FuchsianCuspCompletion D)
  topologicalGenus : _root_.LowDimensionalTopology.Geometry.Surfaces.HasTopologicalGenus (FuchsianCuspCompletion D) genus
  ellipticOrders : letI:=ellipticClassesFinite;orders.Perm (fuchsianEllipticOrderList D)
  cuspCount : cusps=Nat.card (FuchsianCyclicConjugacyClasses D .parabolic)

/-- The elliptic entries of a genuine signature count actual conjugacy classes, retaining repeated orders. -/
theorem HasCofiniteFuchsianSignature.orders_length
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {g p : ℕ} {orders : List ℕ}
    (h : HasCofiniteFuchsianSignature D g orders p) :
    orders.length=Nat.card (FuchsianCyclicConjugacyClasses D .elliptic) := by
  let :=h.ellipticClassesFinite
  exact h.ellipticOrders.length_eq.trans (fuchsianEllipticOrderList_length D)

/-- Every elliptic signature entry is exactly the order of a genuine maximal elliptic subgroup class. -/
theorem HasCofiniteFuchsianSignature.mem_orders
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {g p m : ℕ} {orders : List ℕ}
    (h : HasCofiniteFuchsianSignature D g orders p) :
    m∈orders↔∃c : FuchsianCyclicConjugacyClasses D .elliptic,fuchsianEllipticClassOrder D c=m := by
  let :=h.ellipticClassesFinite
  exact h.ellipticOrders.mem_iff.trans (mem_fuchsianEllipticOrderList D m)

/-- Every actual elliptic order in the signature is at least two. -/
theorem HasCofiniteFuchsianSignature.orders_two_le
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {g p m : ℕ} {orders : List ℕ}
    (h : HasCofiniteFuchsianSignature D g orders p) (hm : m∈orders) : 2≤m := by
  obtain ⟨c,hc⟩:=h.mem_orders.mp hm
  rw [←hc]
  exact fuchsianEllipticClassOrder_two_le D c

/-- The cusp count is the number of actual new points of the genuine quotient completion. -/
theorem HasCofiniteFuchsianSignature.cusp_complement_card
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {g p : ℕ} {orders : List ℕ}
    (h : HasCofiniteFuchsianSignature D g orders p) :
    p=Nat.card {x : FuchsianCuspCompletion D // x∉range (fuchsianCuspCompletionOld D)} :=
  h.cuspCount.trans (Nat.card_congr (fuchsianCuspCompletionComplementEquiv D))

/-- Ordering the actual elliptic class entries differently does not change a genuine cofinite signature. -/
theorem HasCofiniteFuchsianSignature.perm_orders
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H} {g p : ℕ} {orders orders' : List ℕ}
    (h : HasCofiniteFuchsianSignature D g orders p) (hp : orders'.Perm orders) :
    HasCofiniteFuchsianSignature D g orders' p :=
  {h with ellipticOrders:=hp.trans h.ellipticOrders}

end LowDimensionalTopology.Geometry.Fuchsian
