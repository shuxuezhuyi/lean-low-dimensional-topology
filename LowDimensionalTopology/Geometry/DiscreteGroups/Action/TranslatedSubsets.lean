module
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Translated subsets under group actions.

Continuity and compactness control how translates of a set meet neighborhoods. These
lemmas isolate the underlying action and set arguments from geometric applications.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Pointwise

namespace LowDimensionalTopology.Geometry.DiscreteGroups.Action

/-- Distinct actual translated subsets, rather than group labels repeated by a stabilizer. -/
def translatedSubsetFamily {G X : Type*} [Group G] [MulAction G X] (S : Set X) : Set (Set X) :=
  {T | ∃ g : G, T = (g • ·) '' S}

/-- A compact core under a set-preserving subgroup makes distinct translates compact-locally finite. -/
theorem finite_translated_subsets_meeting_compact {G X : Type*} [Group G]
    [TopologicalSpace X] [MulAction G X] [ProperlyDiscontinuousSMul G X]
    (S C B : Set X) (K : Subgroup G) (hC : IsCompact C) (hB : IsCompact B)
    (hstable : ∀ k : K, ((k.val) • ·) '' S = S)
    (hcover : ∀ x ∈ S, ∃ k : K, ∃ c ∈ C, k.val • c = x) :
    {T | T ∈ translatedSubsetFamily (G := G) S ∧ (T ∩ B).Nonempty}.Finite := by
  let J := {g : G | ((g • ·) '' C ∩ B).Nonempty}
  have hJ : J.Finite := finite_disjoint_inter_image hC hB
  apply (hJ.image (fun g : G => (g • ·) '' S)).subset
  rintro T ⟨⟨g,rfl⟩,y,⟨x,hx,rfl⟩,hyB⟩
  obtain ⟨k,c,hc,hcx⟩ := hcover x hx
  refine ⟨g*k.val,?_,?_⟩
  · refine ⟨g • x,⟨c,hc,?_⟩,hyB⟩
    change (g*k.val) • c = g • x
    rw [mul_smul,hcx]
  · change (fun z => (g*k.val) • z) '' S = (g • ·) '' S
    calc
      (fun z : X => (g*k.val) • z) '' S = (g • ·) '' ((k.val • ·) '' S) := by
        rw [image_image]
        congr 1
        funext z
        exact mul_smul g k.val z
      _ = (g • ·) '' S := congrArg (Set.image (g • ·)) (hstable k)

/-- In a proper metric space the translated sets at bounded distance are a finite family. -/
theorem finite_translated_subsets_distance_le {G X : Type*} [Group G]
    [MetricSpace X] [ProperSpace X] [MulAction G X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X] (S C : Set X) (K : Subgroup G)
    (hS : IsClosed S) (hne : S.Nonempty) (hC : IsCompact C)
    (hstable : ∀ k : K, (k.val • ·) '' S = S)
    (hcover : ∀ x ∈ S, ∃ k : K, ∃ c ∈ C, k.val • c = x) (x : X) (R : ℝ) :
    {T | T ∈ translatedSubsetFamily (G := G) S ∧ Metric.infDist x T ≤ R}.Finite := by
  apply (finite_translated_subsets_meeting_compact S C (Metric.closedBall x R) K
    hC (isCompact_closedBall x R) hstable hcover).subset
  rintro T ⟨⟨g,rfl⟩,hd⟩
  refine ⟨⟨g,rfl⟩,?_⟩
  obtain ⟨y,hy,he⟩ := (isClosedMap_smul g S hS).exists_infDist_eq_dist (hne.image _) x
  exact ⟨y,hy,by rw [Metric.mem_closedBall,dist_comm,←he];exact hd⟩

/-- A closest actual translate exists; no finite stabilizer or torsion exclusion is needed. -/
theorem exists_closest_translated_subset {G X : Type*} [Group G]
    [MetricSpace X] [ProperSpace X] [MulAction G X] [ContinuousConstSMul G X]
    [ProperlyDiscontinuousSMul G X] (S C : Set X) (K : Subgroup G)
    (hS : IsClosed S) (hne : S.Nonempty) (hC : IsCompact C)
    (hstable : ∀ k : K, (k.val • ·) '' S = S)
    (hcover : ∀ x ∈ S, ∃ k : K, ∃ c ∈ C, k.val • c = x) (x : X) :
    ∃ T ∈ translatedSubsetFamily (G := G) S,
      ∀ U ∈ translatedSubsetFamily (G := G) S, Metric.infDist x T ≤ Metric.infDist x U := by
  let J := {T | T ∈ translatedSubsetFamily (G := G) S ∧ Metric.infDist x T ≤ Metric.infDist x S}
  have hfin : J.Finite := finite_translated_subsets_distance_le S C K hS hne hC hstable hcover x _
  have hJS : S ∈ J := ⟨⟨1,by simp⟩,le_rfl⟩
  obtain ⟨T,hT,hmin⟩ := Set.exists_min_image J (Metric.infDist x) hfin ⟨S,hJS⟩
  refine ⟨T,hT.1,fun U hU => ?_⟩
  by_cases hd : Metric.infDist x U ≤ Metric.infDist x S
  · exact hmin U ⟨hU,hd⟩
  · exact hT.2.trans (le_of_lt (lt_of_not_ge hd))

end LowDimensionalTopology.Geometry.DiscreteGroups.Action
