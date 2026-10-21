module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.CofiniteSignatures
public import Mathlib.Data.List.Count
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.CyclicClassRepresentatives
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped OnePoint
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
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The short first-kind convention records each genuine cusp with infinite
order, after the finite elliptic orders; list permutation carries the usual
freedom to reorder signature entries. -/
def fuchsianShortSignatureOrders (orders : List ℕ) (cusps : ℕ) : List (WithTop ℕ) :=
  orders.map (fun m => (m : WithTop ℕ)) ++ List.replicate cusps ⊤

theorem fuchsianShortSignatureOrders_length (orders : List ℕ) (cusps : ℕ) :
    (fuchsianShortSignatureOrders orders cusps).length=orders.length+cusps := by
  simp [fuchsianShortSignatureOrders]

theorem fuchsianShortSignatureOrders_count_top (orders : List ℕ) (cusps : ℕ) :
    (fuchsianShortSignatureOrders orders cusps).count ⊤=cusps := by
  have hn : (⊤ : WithTop ℕ)∉orders.map (fun m => (m : WithTop ℕ)) := by simp
  rw [fuchsianShortSignatureOrders,List.count_append,List.count_eq_zero.mpr hn]
  simp

theorem fuchsianShortSignatureOrders_mem_coe (orders : List ℕ) (cusps m : ℕ) :
    (m : WithTop ℕ)∈fuchsianShortSignatureOrders orders cusps ↔ m∈orders := by
  simp [fuchsianShortSignatureOrders]

theorem fuchsianShortSignatureOrders_eq_nil_iff (orders : List ℕ) (cusps : ℕ) :
    fuchsianShortSignatureOrders orders cusps=[] ↔ orders=[] ∧ cusps=0 := by
  rw [←List.length_eq_zero_iff,fuchsianShortSignatureOrders_length,Nat.add_eq_zero_iff]
  rw [List.length_eq_zero_iff]

/--
The short signature has no boundary-hyperbolic parameter. Its empty
order list is the geometric notation `(g: 0)`, with zero as an empty-family
convention rather than the order of an elliptic transformation.
-/
structure FuchsianShortSignature where
  genus : ℕ
  orders : List (WithTop ℕ)

/-- The short notation is tied to the genuine completed quotient, actual
elliptic subgroup orders and actual cusp classes of an original geometric
disc through the existing cofinite signature. This is a notation predicate,
not a geometric signature-existence assumption or theorem. -/
def HasFuchsianShortSignature
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (s : FuchsianShortSignature) : Prop :=
  ∃ (orders : List ℕ) (cusps : ℕ), HasCofiniteFuchsianSignature D s.genus orders cusps ∧
    s.orders.Perm (fuchsianShortSignatureOrders orders cusps)

/-- Any genuine original cofinite signature has its exact short notation. -/
theorem HasCofiniteFuchsianSignature.shortSignature
    {H : Subgroup Mobius.complexMobiusGroup} {D : FuchsianDisc H}
    {g c : ℕ} {orders : List ℕ} (h : HasCofiniteFuchsianSignature D g orders c) :
    HasFuchsianShortSignature D ⟨g,fuchsianShortSignatureOrders orders c⟩ :=
  ⟨orders,c,h,List.Perm.refl _⟩

/-- The short length counts the original elliptic and parabolic conjugacy
classes, with their actual multiplicities. -/
theorem HasFuchsianShortSignature.length
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {s : FuchsianShortSignature}
    (h : HasFuchsianShortSignature D s) :
    s.orders.length=Nat.card (FuchsianCyclicConjugacyClasses D .elliptic)+
      Nat.card (FuchsianCyclicConjugacyClasses D .parabolic) := by
  obtain ⟨orders,c,hc,hperm⟩ := h
  exact hperm.length_eq.trans ((fuchsianShortSignatureOrders_length orders c).trans
    (congrArg₂ (·+·) hc.orders_length hc.cuspCount))

/-- Infinite order entries count exactly the original genuine cusp classes. -/
theorem HasFuchsianShortSignature.count_top
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {s : FuchsianShortSignature}
    (h : HasFuchsianShortSignature D s) :
    s.orders.count ⊤=Nat.card (FuchsianCyclicConjugacyClasses D .parabolic) := by
  obtain ⟨orders,c,hc,hperm⟩ := h
  exact (hperm.count_eq ⊤).trans ((fuchsianShortSignatureOrders_count_top orders c).trans hc.cuspCount)

/-- Every finite short entry is precisely an order of an actual maximal
elliptic cyclic subgroup class in the original geometric disc. -/
theorem HasFuchsianShortSignature.mem_coe
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {s : FuchsianShortSignature}
    (h : HasFuchsianShortSignature D s) (m : ℕ) :
    (m : WithTop ℕ)∈s.orders ↔
      ∃ c : FuchsianCyclicConjugacyClasses D .elliptic, fuchsianEllipticClassOrder D c=m := by
  obtain ⟨orders,n,hc,hperm⟩ := h
  exact hperm.mem_iff.trans ((fuchsianShortSignatureOrders_mem_coe orders n m).trans hc.mem_orders)

/--
The geometric `(g: 0)` case means that both actual typed class families
are empty; no transformation of order zero is inserted.
-/
theorem HasFuchsianShortSignature.orders_eq_nil_iff
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {s : FuchsianShortSignature}
    (h : HasFuchsianShortSignature D s) :
    s.orders=[] ↔ Nat.card (FuchsianCyclicConjugacyClasses D .elliptic)=0 ∧
      Nat.card (FuchsianCyclicConjugacyClasses D .parabolic)=0 := by
  rw [←List.length_eq_zero_iff,h.length,Nat.add_eq_zero_iff]

/-- A zero finite order never occurs in the genuine short signature. -/
theorem HasFuchsianShortSignature.zero_not_mem
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {s : FuchsianShortSignature}
    (h : HasFuchsianShortSignature D s) : (0 : WithTop ℕ)∉s.orders := by
  intro hm
  obtain ⟨c,hc⟩ := (h.mem_coe 0).mp hm
  have hb := fuchsianEllipticClassOrder_two_le D c
  rw [hc] at hb
  omega

/-- The genuine typed maximal cyclic class space is empty exactly when the
original whole group has no element of that geometric type. -/
theorem fuchsianCyclicConjugacyClasses_isEmpty_iff
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (kind : FuchsianCyclicKind) :
    IsEmpty (FuchsianCyclicConjugacyClasses D kind) ↔
      ∀ f ∈ H, ¬MobiusCyclicType kind f := by
  constructor
  · intro he f hf hft
    let : IsEmpty (FuchsianCyclicConjugacyClasses D kind) := he
    obtain ⟨r,_hr,_hu⟩ := fuchsianCyclicRepresentativeMembers_unique_conjugate D kind ⟨f,hf⟩ hft
    exact isEmptyElim r.1
  · intro hno
    refine ⟨fun c => ?_⟩
    obtain ⟨f,hf,hft⟩ := c.out.property.2
    exact hno f (c.out.property.1.1 hf) hft

/-- The empty short order list means exactly that the original whole group
has neither genuine elliptic nor genuine parabolic transformations. -/
theorem HasFuchsianShortSignature.orders_eq_nil_iff_no_elements
    {H : Subgroup Mobius.complexMobiusGroup}
    {D : FuchsianDisc H}
    {s : FuchsianShortSignature}
    (h : HasFuchsianShortSignature D s) :
    s.orders=[] ↔ (∀ f ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) ∧ (∀ f ∈ H, ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f) := by
  have hzero := h.orders_eq_nil_iff
  obtain ⟨orders,c,hc,_hperm⟩ := h
  let := hc.ellipticClassesFinite
  let := hc.parabolicClassesFinite
  simp only [hzero,Nat.card_eq_zero,hc.ellipticClassesFinite.not_infinite,hc.parabolicClassesFinite.not_infinite,or_false,
    fuchsianCyclicConjugacyClasses_isEmpty_iff D .elliptic,
    fuchsianCyclicConjugacyClasses_isEmpty_iff D .parabolic]
  rfl

end LowDimensionalTopology.Geometry.Fuchsian
