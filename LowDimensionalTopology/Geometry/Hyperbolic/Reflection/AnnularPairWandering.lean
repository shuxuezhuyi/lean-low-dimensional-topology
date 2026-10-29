module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularPairReflectionGroup
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularFourCapZPowers
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.PingPong

@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane Pointwise

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- The complement of the four full closed caps wanders under the original
two-product subgroup, with its original native action. -/
theorem annularPairReflectionGroup_wandering (E r x : ℝ)
    (hE : 1 < E) (hr : 0 < r) (hinner : 1 + r < x) (houter : x + r < E) :
    let σ0 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one)
    let O := {z : ℍ | E ≤ ‖(z : ℂ)‖}
    let B := {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ ≤ r}
    let V := ((σ0 '' O ∪ O) ∪ (B ∪ σ0 '' B))ᶜ
    ∀ g : annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr,
      g ≠ 1 → Disjoint ((g : ℍ ≃ᵢ ℍ) '' V) V := by
  let σ0 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle 0 1 zero_lt_one)
  let σ1 := halfPlaneLineReflectionIsometry
    (HalfPlaneLine.circle 0 E (zero_lt_one.trans hE))
  let σ2 := halfPlaneLineReflectionIsometry (HalfPlaneLine.circle x r hr)
  let a : Fin 2 → (ℍ ≃ᵢ ℍ) := ![σ0 * σ1, σ2 * σ0]
  let O := {z : ℍ | E ≤ ‖(z : ℂ)‖}
  let B := {z : ℍ | ‖(z : ℂ) - (x : ℂ)‖ ≤ r}
  let A : Fin 2 → Set ℍ := ![σ0 '' O ∪ O, B ∪ σ0 '' B]
  let V := (A 0 ∪ A 1)ᶜ
  let K := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
  let H : Fin 2 → Subgroup (ℍ ≃ᵢ ℍ) := fun i => Subgroup.zpowers (a i)
  let f : ∀ i, H i →* (ℍ ≃ᵢ ℍ) := fun i => (H i).subtype
  change ∀ g : K, g ≠ 1 → Disjoint ((g : ℍ ≃ᵢ ℍ) '' V) V
  have hd : Disjoint (σ0 '' O) O ∧ Disjoint (σ0 '' O) B ∧
      Disjoint (σ0 '' O) (σ0 '' B) ∧ Disjoint O B ∧
      Disjoint O (σ0 '' B) ∧ Disjoint B (σ0 '' B) :=
    annular_four_closed_caps_disjoint E r x hE hr hinner houter
  rcases hd with ⟨_, hXX, h01, h10, hYY, _⟩
  have hA01 : Disjoint (A 0) (A 1) :=
    (hXX.union_right h01).union_left (h10.union_right hYY)
  have hA : Pairwise fun i j => Disjoint (A i) (A j) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact (hij rfl).elim
      | exact hA01
      | exact hA01.symm
  have hpow : ∀ i (n : ℤ), n ≠ 0 → a i ^ n • (A i)ᶜ ⊆ A i :=
    annular_four_closed_caps_zpow_gap E r x hE hr hinner houter
  have hVA (i : Fin 2) : V ⊆ (A i)ᶜ := by
    fin_cases i
    · exact compl_subset_compl.mpr subset_union_left
    · exact compl_subset_compl.mpr subset_union_right
  have hfactor (i : Fin 2) (h : H i) (hh : h ≠ 1) :
      f i h • (A i)ᶜ ⊆ A i := by
    have hm : (h : ℍ ≃ᵢ ℍ) ∈ Subgroup.zpowers (a i) := h.property
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hm
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hh (Subtype.ext (by simpa using hn.symm))
    have he : f i h = a i ^ n := hn.symm
    rw [he]
    exact hpow i n hn0
  have hpp : Pairwise fun i j => ∀ h : H i, h ≠ 1 → f i h • A j ⊆ A i := by
    intro i j hij h hh
    exact (smul_set_mono (hA hij).symm.subset_compl_right).trans (hfactor i h hh)
  have hstart : ∀ i (h : H i), h ≠ 1 → f i h • V ⊆ A i := by
    intro i h hh
    exact (smul_set_mono (hVA i)).trans (hfactor i h hh)
  have hgap : ∀ i, Disjoint (A i) V :=
    fun i => disjoint_left.mpr fun _ hz hv => (hVA i hv) hz
  have hrange : (Monoid.CoprodI.lift f).range = K := by
    rw [Monoid.CoprodI.range_eq_iSup]
    simp only [f, Subgroup.range_subtype]
    apply le_antisymm
    · apply iSup_le
      intro i
      change Subgroup.zpowers (a i) ≤ K
      apply Subgroup.zpowers_le.mpr
      change a i ∈ Subgroup.closure ({σ0 * σ1, σ2 * σ0} : Set (ℍ ≃ᵢ ℍ))
      apply Subgroup.subset_closure
      fin_cases i <;> simp [a]
    · change Subgroup.closure ({σ0 * σ1, σ2 * σ0} : Set (ℍ ≃ᵢ ℍ)) ≤
        ⨆ i : Fin 2, H i
      apply (Subgroup.closure_le _).mpr
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · exact (le_iSup H 0) (Subgroup.mem_zpowers (a 0))
      · exact (le_iSup H 1) (Subgroup.mem_zpowers (a 1))
  intro g hg
  have hmem : (g : ℍ ≃ᵢ ℍ) ∈ (Monoid.CoprodI.lift f).range := by
    rw [hrange]
    exact g.property
  have hne : (g : ℍ ≃ᵢ ℍ) ≠ 1 := fun he => hg (Subtype.ext he)
  change Disjoint ((g : ℍ ≃ᵢ ℍ) • V) V
  exact DiscreteGroups.pingPong_range_wandering f A V hpp hstart hgap
    (g : ℍ ≃ᵢ ℍ) hmem hne

end LowDimensionalTopology.Geometry.Hyperbolic
