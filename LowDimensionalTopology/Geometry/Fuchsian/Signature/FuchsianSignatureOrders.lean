/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.FiniteIndexConjugacy
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.OfFn
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- An actual maximal elliptic cyclic subgroup is finite: it is the genuine stabilizer
of its unique interior fixed point for the original discontinuous disc action. -/
theorem fuchsianMaximalElliptic_finite {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : fuchsianMaximalCyclicSubgroups H .elliptic) :
    Finite K.val := by
  obtain ⟨hK,f,hfK,hf⟩:=K.property
  obtain ⟨p,hp,_⟩:=elliptic_disc_existsUnique_fixed f hf D.isDisc
    (D.image_eq ⟨f,hK.1 hfK⟩)
  have he:=maximal_elliptic_cyclic_eq_stabilizer D hK f hfK hf p hp
  rw [he]
  exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer_finite H D.discontinuous p.val p.property).to_subtype

/-- The order of every actual elliptic maximal cyclic subgroup is at least two. -/
theorem fuchsianMaximalElliptic_card_two_le
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : fuchsianMaximalCyclicSubgroups H .elliptic) :
    2≤Nat.card K.val := by
  have : Finite K.val:=fuchsianMaximalElliptic_finite D K
  obtain ⟨_,f,hfK,hf⟩:=K.property
  have hne : (⟨f,hfK⟩:K.val)≠1:=fun he=>hf.1 (congrArg Subtype.val he)
  have : Nontrivial K.val:=⟨⟨⟨f,hfK⟩,1,hne⟩⟩
  exact Finite.one_lt_card

/-- Literal conjugation preserves the order of an actual subgroup, without a finiteness assumption. -/
theorem subgroupConjugate_natCard
    (q : Mobius.complexMobiusGroup)
    (K : Subgroup Mobius.complexMobiusGroup) :
    Nat.card (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K)=Nat.card K :=
  Nat.card_congr (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q K).symm.toEquiv

/-- The actual elliptic order is constant on the actual subgroup conjugacy relation. -/
theorem fuchsianEllipticOrder_conjugacy {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K L : fuchsianMaximalCyclicSubgroups H .elliptic)
    (h : (fuchsianMaximalCyclicConjugacySetoid D .elliptic).r K L) :
    Nat.card K.val=Nat.card L.val := by
  obtain ⟨q,hq⟩:=(fuchsianMaximalCyclicConjugacySetoid_iff D .elliptic K L).mp h
  rw [←hq]
  exact (subgroupConjugate_natCard q.val K.val).symm

/-- Each true conjugacy class of maximal elliptic cyclic subgroups has a well-defined
order, computed from the actual finite subgroup and independent of its representative. -/
def fuchsianEllipticClassOrder {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : FuchsianCyclicConjugacyClasses D .elliptic→ℕ :=
  Quotient.lift (fun K=>Nat.card K.val) (fuchsianEllipticOrder_conjugacy D)

theorem fuchsianEllipticClassOrder_mk {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : fuchsianMaximalCyclicSubgroups H .elliptic) :
    fuchsianEllipticClassOrder D (Quotient.mk _ K)=Nat.card K.val := rfl

theorem fuchsianEllipticClassOrder_two_le
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (c : FuchsianCyclicConjugacyClasses D .elliptic) :
    2≤fuchsianEllipticClassOrder D c := by
  induction c using Quotient.inductionOn with
  | _ K=>exact fuchsianMaximalElliptic_card_two_le D K

/-- Once finiteness of the actual conjugacy-class space is available, the signature
orders enumerate precisely those classes, with repeated orders retained. Finiteness is
explicit here; the finite-generation implication is not assumed by this construction. -/
def fuchsianEllipticOrderList {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) [Finite (FuchsianCyclicConjugacyClasses D .elliptic)] : List ℕ :=
  letI := Fintype.ofFinite (FuchsianCyclicConjugacyClasses D .elliptic)
  List.ofFn (fun i=>fuchsianEllipticClassOrder D
    ((Fintype.equivFin (FuchsianCyclicConjugacyClasses D .elliptic)).symm i))

/-- The length counts the actual conjugacy classes, rather than just distinct orders. -/
theorem fuchsianEllipticOrderList_length {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) [Finite (FuchsianCyclicConjugacyClasses D .elliptic)] :
    (fuchsianEllipticOrderList D).length=Nat.card (FuchsianCyclicConjugacyClasses D .elliptic) := by
  classical
  let := Fintype.ofFinite (FuchsianCyclicConjugacyClasses D .elliptic)
  simp only [fuchsianEllipticOrderList,List.length_ofFn,Nat.card_eq_fintype_card]

/-- Membership in the order list is exactly the order of an actual elliptic conjugacy class. -/
theorem mem_fuchsianEllipticOrderList {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) [Finite (FuchsianCyclicConjugacyClasses D .elliptic)] (m : ℕ) :
    m∈fuchsianEllipticOrderList D ↔
      ∃c : FuchsianCyclicConjugacyClasses D .elliptic,fuchsianEllipticClassOrder D c=m := by
  classical
  let := Fintype.ofFinite (FuchsianCyclicConjugacyClasses D .elliptic)
  simp only [fuchsianEllipticOrderList,List.mem_ofFn]
  constructor
  · rintro ⟨i,hi⟩
    exact ⟨_,hi⟩
  · rintro ⟨c,hc⟩
    exact ⟨Fintype.equivFin _ c,by simpa only [Equiv.symm_apply_apply] using hc⟩

/-- Every listed order is the order of a genuine nontrivial finite elliptic subgroup. -/
theorem fuchsianEllipticOrderList_two_le {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) [Finite (FuchsianCyclicConjugacyClasses D .elliptic)] :
    ∀m∈fuchsianEllipticOrderList D,2≤m := by
  intro m hm
  obtain ⟨c,rfl⟩:=(mem_fuchsianEllipticOrderList D m).mp hm
  exact fuchsianEllipticClassOrder_two_le D c

/-- Vanishing of the actual elliptic class space is equivalent to absence of elliptics. -/
theorem fuchsianEllipticClass_isEmpty_iff
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) :
    IsEmpty (FuchsianCyclicConjugacyClasses D .elliptic) ↔ ∀f∈H,¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f := by
  classical
  constructor
  · intro he f hfH hf
    obtain ⟨p,hp,_⟩:=elliptic_disc_existsUnique_fixed f hf D.isDisc (D.image_eq ⟨f,hfH⟩)
    let K : fuchsianMaximalCyclicSubgroups H .elliptic:=
      ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H p.val,
        elliptic_stabilizer_isMaximalCyclic D f hfH hf p hp,
        f,(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p.val f).mpr ⟨hfH,hp⟩,hf⟩
    exact he.false (Quotient.mk _ K)
  · intro h
    refine ⟨?_⟩
    intro c
    induction c using Quotient.inductionOn with
    | _ K=>
      obtain ⟨hK,f,hfK,hf⟩:=K.property
      exact h f (hK.1 hfK) hf

/-- The empty elliptic list has the precise geometric meaning used by the source's
zero-elliptic shorthand, including elementary groups where appropriate. -/
theorem fuchsianEllipticOrderList_eq_nil_iff
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) [Finite (FuchsianCyclicConjugacyClasses D .elliptic)] :
    fuchsianEllipticOrderList D=[] ↔ ∀f∈H,¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f := by
  rw [←fuchsianEllipticClass_isEmpty_iff D]
  rw [←List.length_eq_zero_iff,fuchsianEllipticOrderList_length,Nat.card_eq_zero]
  constructor
  · rintro (h|h)
    · exact h
    · exact False.elim (not_finite_iff_infinite.mpr h inferInstance)
  · exact Or.inl

/-- Changing the genuine invariant disc leaves the actual maximal-elliptic subgroup
conjugacy classes unchanged: the defining relation is literal conjugacy in H. -/
def fuchsianEllipticClassDiscEquiv {H : Subgroup Mobius.complexMobiusGroup}
    (D E : FuchsianDisc H) :
    FuchsianCyclicConjugacyClasses D .elliptic ≃ FuchsianCyclicConjugacyClasses E .elliptic :=
  Quotient.congr (Equiv.refl _) (fun K L=>
    (fuchsianMaximalCyclicConjugacySetoid_iff D .elliptic K L).trans
      (fuchsianMaximalCyclicConjugacySetoid_iff E .elliptic K L).symm)

/-- The actual finite elliptic order is independent of the chosen invariant disc. -/
theorem fuchsianEllipticClassDiscEquiv_order
    {H : Subgroup Mobius.complexMobiusGroup}
    (D E : FuchsianDisc H) (c : FuchsianCyclicConjugacyClasses D .elliptic) :
    fuchsianEllipticClassOrder E (fuchsianEllipticClassDiscEquiv D E c)=
      fuchsianEllipticClassOrder D c := by
  induction c using Quotient.inductionOn with
  | _ K=>rfl

theorem fuchsianEllipticClassDiscEquiv_natCard
    {H : Subgroup Mobius.complexMobiusGroup}
    (D E : FuchsianDisc H) :
    Nat.card (FuchsianCyclicConjugacyClasses D .elliptic)=
      Nat.card (FuchsianCyclicConjugacyClasses E .elliptic) :=
  Nat.card_congr (fuchsianEllipticClassDiscEquiv D E)

/-- Equivalent finite enumerations with equal values produce genuinely permuted lists. -/
theorem signature_orderList_perm_of_equiv {m n : ℕ} (e : Fin m≃Fin n)
    (f : Fin m→ℕ) (g : Fin n→ℕ) (h : ∀i,g (e i)=f i) :
    (List.ofFn f).Perm (List.ofFn g) := by
  have hmn : m=n:=by simpa using Fintype.card_congr e
  subst n
  have he : f=g∘e:=funext (fun i=>(h i).symm)
  rw [he]
  exact (show Equiv.Perm (Fin m) from e).ofFn_comp_perm g

/-- The entire multiset of actual elliptic class orders, including multiplicities,
is independent of the invariant disc. -/
theorem fuchsianEllipticOrderList_disc_perm
    {H : Subgroup Mobius.complexMobiusGroup}
    (D E : FuchsianDisc H) [Finite (FuchsianCyclicConjugacyClasses D .elliptic)]
    [Finite (FuchsianCyclicConjugacyClasses E .elliptic)] :
    (fuchsianEllipticOrderList D).Perm (fuchsianEllipticOrderList E) := by
  classical
  let := Fintype.ofFinite (FuchsianCyclicConjugacyClasses D .elliptic)
  let := Fintype.ofFinite (FuchsianCyclicConjugacyClasses E .elliptic)
  let e:=(Fintype.equivFin (FuchsianCyclicConjugacyClasses D .elliptic)).symm |>.trans
    ((fuchsianEllipticClassDiscEquiv D E).trans
      (Fintype.equivFin (FuchsianCyclicConjugacyClasses E .elliptic)))
  apply signature_orderList_perm_of_equiv e
  intro i
  simp only [e,Equiv.trans_apply,Equiv.symm_apply_apply]
  exact fuchsianEllipticClassDiscEquiv_order D E _

end LowDimensionalTopology.Geometry.Fuchsian
