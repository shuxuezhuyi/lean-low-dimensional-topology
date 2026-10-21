/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import Mathlib.GroupTheory.CoprodI
public import Mathlib.Topology.Algebra.Group.Subgroup
public import Mathlib.Topology.Algebra.MulAction
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.WanderingDomain
@[expose] public section
set_option autoImplicit false
open Set
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.DiscreteGroups
universe u v w

theorem pingPong_word_gap
    {ι : Type u} {H : ι→Type v} [∀i,Group (H i)]
    {G : Type w} [Group G] {X : Type*} [MulAction G X]
    (f : ∀i,H i→*G) (A : ι→Set X) (U : Set X)
    (hpp : Pairwise fun i j=>∀h : H i,h≠1→f i h • A j⊆A i)
    (hstart : ∀i (h : H i),h≠1→f i h • U⊆A i)
    {i j : ι} (word : Monoid.CoprodI.NeWord H i j) :
    Monoid.CoprodI.lift f word.prod • U⊆A i := by
  induction word with
  | singleton h hh => simpa using hstart _ h hh
  | @append i j k l a hjk b ha hb =>
    rw [Monoid.CoprodI.NeWord.append_prod,map_mul,mul_smul]
    exact (smul_set_subset_smul_set_iff.mpr hb).trans
      (Monoid.CoprodI.lift_word_ping_pong f A hpp a hjk)

theorem pingPong_range_wandering
    {ι : Type u} {H : ι→Type v} [∀i,Group (H i)]
    {G : Type w} [Group G] {X : Type*} [MulAction G X]
    (f : ∀i,H i→*G) (A : ι→Set X) (U : Set X)
    (hpp : Pairwise fun i j=>∀h : H i,h≠1→f i h • A j⊆A i)
    (hstart : ∀i (h : H i),h≠1→f i h • U⊆A i)
    (hgap : ∀i,Disjoint (A i) U)
    (g : G) (hg : g∈(Monoid.CoprodI.lift f).range) (hne : g≠1) :
    Disjoint (g • U) U := by
  classical
  obtain ⟨a,rfl⟩:=hg
  let word:=Monoid.CoprodI.Word.equiv (M:=H) a
  have hp : word.prod=a:=(Monoid.CoprodI.Word.equiv (M:=H)).symm_apply_apply a
  have hw : word≠Monoid.CoprodI.Word.empty:=by
    intro he
    have ha : a=1:=by rw [←hp,he,Monoid.CoprodI.Word.prod_empty]
    exact hne (by rw [ha,map_one])
  obtain ⟨i,j,v,hv⟩:=Monoid.CoprodI.NeWord.of_word word hw
  have hvp : v.prod=a:=by
    change v.toWord.prod=a
    rw [hv,hp]
  rw [←hvp]
  exact (hgap i).mono_left (pingPong_word_gap f A U hpp hstart v)

theorem discreteTopology_range_of_pingPong_gap
    {ι : Type u} {H : ι→Type v} [∀i,Group (H i)]
    {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {X : Type*} [TopologicalSpace X] [MulAction G X] [ContinuousSMul G X]
    (f : ∀i,H i→*G) (A : ι→Set X) (U : Set X)
    (hU : IsOpen U) (hUn : U.Nonempty)
    (hpp : Pairwise fun i j=>∀h : H i,h≠1→f i h • A j⊆A i)
    (hstart : ∀i (h : H i),h≠1→f i h • U⊆A i)
    (hgap : ∀i,Disjoint (A i) U) :
    DiscreteTopology (Monoid.CoprodI.lift f).range := by
  apply discreteTopology_of_wandering_open U hU hUn
  intro g hg
  have hne : (g:G)≠1:=by
    intro he
    exact hg (Subtype.ext he)
  exact pingPong_range_wandering f A U hpp hstart hgap g g.property hne

end LowDimensionalTopology.Geometry.DiscreteGroups
