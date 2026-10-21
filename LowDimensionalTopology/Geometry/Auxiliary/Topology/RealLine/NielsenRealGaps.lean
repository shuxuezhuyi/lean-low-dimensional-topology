/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.Topology.Connected.LocallyConnected
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Topology.Bases
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Analysis.Normed.Module.Convex
@[expose] public section
open Set Filter
open scoped Topology
namespace LowDimensionalTopology.Geometry.Auxiliary.Topology
noncomputable section

theorem nielsen_realOpen_exists_lt {S : Set ℝ} (hS : IsOpen S) {a : ℝ} (ha : a∈S) :
    ∃b∈S,b<a := by
  obtain ⟨ε,hε,hball⟩:=Metric.isOpen_iff.mp hS a ha
  refine ⟨a-ε/2,hball ?_,by linarith⟩
  rw [Metric.mem_ball,Real.dist_eq]
  have hEq : a-ε/2-a=-(ε/2):=by ring
  rw [hEq,abs_neg,abs_of_pos (half_pos hε)]
  linarith

theorem nielsen_realOpen_exists_gt {S : Set ℝ} (hS : IsOpen S) {a : ℝ} (ha : a∈S) :
    ∃b∈S,a<b := by
  obtain ⟨ε,hε,hball⟩:=Metric.isOpen_iff.mp hS a ha
  refine ⟨a+ε/2,hball ?_,by linarith⟩
  rw [Metric.mem_ball,Real.dist_eq,add_sub_cancel_left,abs_of_pos (half_pos hε)]
  linarith

/-- Every nonempty open connected real set is exactly one of the genuine open intervals. -/
theorem nielsen_realOpen_preconnected_interval {S : Set ℝ} (hS : IsOpen S)
    (hpre : IsPreconnected S) (hne : S.Nonempty) :
    (∃a b : ℝ,a<b ∧ S=Ioo a b) ∨ (∃b : ℝ,S=Iio b) ∨
      (∃a : ℝ,S=Ioi a) ∨ S=univ := by
  have hlo (hb : BddBelow S) (x : ℝ) (hx : x∈S) : sInf S<x:=by
    obtain ⟨y,hy,hyx⟩:=nielsen_realOpen_exists_lt hS hx
    exact (csInf_le hb hy).trans_lt hyx
  have hhi (hb : BddAbove S) (x : ℝ) (hx : x∈S) : x<sSup S:=by
    obtain ⟨y,hy,hxy⟩:=nielsen_realOpen_exists_gt hS hx
    exact hxy.trans_le (le_csSup hb hy)
  by_cases hb : BddBelow S <;> by_cases ha : BddAbove S
  · have he : S=Ioo (sInf S) (sSup S):=subset_antisymm
      (fun x hx=>⟨hlo hb x hx,hhi ha x hx⟩)
      ((show IsConnected S from ⟨hne,hpre⟩).Ioo_csInf_csSup_subset hb ha)
    refine Or.inl ⟨sInf S,sSup S,?_,he⟩
    have hh:=hne
    rw [he] at hh
    exact nonempty_Ioo.mp hh
  · exact Or.inr (Or.inr (Or.inl ⟨sInf S,subset_antisymm
      (fun x hx=>hlo hb x hx) (hpre.Ioi_csInf_subset hb ha)⟩))
  · exact Or.inr (Or.inl ⟨sSup S,subset_antisymm
      (fun x hx=>hhi ha x hx) (hpre.Iio_csSup_subset hb ha)⟩)
  · exact Or.inr (Or.inr (Or.inr (hpre.eq_univ_of_unbounded hb ha)))

/-- Connected components are genuinely closed relative to the ambient subset. -/
theorem nielsen_connectedComponentIn_closure_inter_subset {X : Type*} [TopologicalSpace X]
    (F : Set X) {x : X} (hx : x∈F) :
    closure (connectedComponentIn F x)∩F⊆connectedComponentIn F x := by
  have hsub : connectedComponentIn F x⊆closure (connectedComponentIn F x)∩F:=
    fun y hy=>⟨subset_closure hy,connectedComponentIn_subset F x hy⟩
  have hpre:=isPreconnected_connectedComponentIn.subset_closure hsub inter_subset_left
  exact hpre.subset_connectedComponentIn (hsub (mem_connectedComponentIn hx)) inter_subset_right

/-- An excluded endpoint of a complementary component lies in the original closed set. -/
theorem nielsen_realGap_endpoint_mem {A : Set ℝ} {x b : ℝ} (hx : x∉A)
    (hbcl : b∈closure (connectedComponentIn Aᶜ x)) (hbnot : b∉connectedComponentIn Aᶜ x) : b∈A := by
  by_contra hb
  exact hbnot (nielsen_connectedComponentIn_closure_inter_subset Aᶜ hx ⟨hbcl,hb⟩)

/-- The actual complementary components of a nonempty closed real set are intervals with true endpoints in that set. -/
theorem nielsen_realGap_classification {A : Set ℝ} (hA : IsClosed A) (hneA : A.Nonempty)
    {x : ℝ} (hx : x∉A) :
    (∃a b : ℝ,a∈A ∧ b∈A ∧ a<b ∧ connectedComponentIn Aᶜ x=Ioo a b) ∨
      (∃b : ℝ,b∈A ∧ connectedComponentIn Aᶜ x=Iio b) ∨
      (∃a : ℝ,a∈A ∧ connectedComponentIn Aᶜ x=Ioi a) := by
  have hne : (connectedComponentIn Aᶜ x).Nonempty:=⟨x,mem_connectedComponentIn hx⟩
  rcases nielsen_realOpen_preconnected_interval hA.isOpen_compl.connectedComponentIn
    isPreconnected_connectedComponentIn hne with ⟨a,b,hab,he⟩ | ⟨b,he⟩ | ⟨a,he⟩ | he
  · have haA : a∈A:=nielsen_realGap_endpoint_mem hx (by
      rw [he,closure_Ioo hab.ne];exact left_mem_Icc.mpr hab.le) (by rw [he];exact fun h=>lt_irrefl a h.1)
    have hbA : b∈A:=nielsen_realGap_endpoint_mem hx (by
      rw [he,closure_Ioo hab.ne];exact right_mem_Icc.mpr hab.le) (by rw [he];exact fun h=>lt_irrefl b h.2)
    exact Or.inl ⟨a,b,haA,hbA,hab,he⟩
  · have hbA : b∈A:=nielsen_realGap_endpoint_mem hx (by rw [he,closure_Iio];exact le_refl b)
      (by rw [he];exact lt_irrefl b)
    exact Or.inr (Or.inl ⟨b,hbA,he⟩)
  · have haA : a∈A:=nielsen_realGap_endpoint_mem hx (by rw [he,closure_Ioi];exact le_refl a)
      (by rw [he];exact lt_irrefl a)
    exact Or.inr (Or.inr ⟨a,haA,he⟩)
  · obtain ⟨a,ha⟩:=hneA
    have hm : a∈connectedComponentIn Aᶜ x:=he.symm ▸ mem_univ a
    exact (connectedComponentIn_subset Aᶜ x hm ha).elim


/-- The actual family of complementary components, with repeated point indices removed. -/
def nielsenRealGapFamily (A : Set ℝ) : Set (Set ℝ):=
  {S | ∃x : ℝ,x∉A ∧ S=connectedComponentIn Aᶜ x}

theorem nielsenRealGapFamily_nonempty (A : Set ℝ) {S : Set ℝ} (hS : S∈nielsenRealGapFamily A) : S.Nonempty := by
  obtain ⟨x,hx,rfl⟩:=hS
  exact ⟨x,mem_connectedComponentIn hx⟩

theorem nielsenRealGapFamily_isOpen {A : Set ℝ} (hA : IsClosed A) {S : Set ℝ}
    (hS : S∈nielsenRealGapFamily A) : IsOpen S := by
  obtain ⟨x,_,rfl⟩:=hS
  exact hA.isOpen_compl.connectedComponentIn

theorem nielsenRealGapFamily_pairwiseDisjoint (A : Set ℝ) : (nielsenRealGapFamily A).PairwiseDisjoint id := by
  intro S hS T hT hne
  apply Set.disjoint_left.mpr
  intro z hzS hzT
  obtain ⟨x,_,rfl⟩:=hS
  obtain ⟨y,_,rfl⟩:=hT
  exact hne ((connectedComponentIn_eq hzS).trans (connectedComponentIn_eq hzT).symm)

theorem nielsenRealGapFamily_countable {A : Set ℝ} (hA : IsClosed A) : (nielsenRealGapFamily A).Countable :=
  (nielsenRealGapFamily_pairwiseDisjoint A).countable_of_isOpen
    (fun _ hS=>nielsenRealGapFamily_isOpen hA hS) (fun _ hS=>nielsenRealGapFamily_nonempty A hS)

theorem nielsenRealGapFamily_sUnion (A : Set ℝ) : ⋃₀ nielsenRealGapFamily A=Aᶜ := by
  ext x
  constructor
  · rintro ⟨S,⟨y,_,rfl⟩,hx⟩
    exact connectedComponentIn_subset Aᶜ y hx
  · intro hx
    exact ⟨connectedComponentIn Aᶜ x,⟨x,hx,rfl⟩,mem_connectedComponentIn hx⟩

end
end LowDimensionalTopology.Geometry.Auxiliary.Topology
