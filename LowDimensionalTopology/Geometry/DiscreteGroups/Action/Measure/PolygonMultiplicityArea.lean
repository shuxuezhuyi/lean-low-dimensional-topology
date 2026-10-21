module
public import Mathlib.MeasureTheory.Group.FundamentalDomain
public import Mathlib.Topology.LocallyFinite
@[expose] public section
noncomputable section
open Set Filter Topology MeasureTheory
open scoped Pointwise ENNReal
namespace LowDimensionalTopology.Geometry.DiscreteGroups.Action
universe u v
variable {X : Type u} {G : Type v} [Group G] [MulAction G X]

/-- The genuine number of original translates containing a point, counted with their
original group labels and expressed as a nonnegative extended sum. -/
def orbitalCoverMultiplicity (G : Type v) [Group G] [MulAction G X]
    (P : Set X) (x : X) : ℝ≥0∞ :=
  ∑' g : G, P.indicator (fun _ : X => (1 : ℝ≥0∞)) (g⁻¹ • x)

theorem orbitalCoverMultiplicity_smul (P : Set X) (h : G) (x : X) :
    orbitalCoverMultiplicity G P (h • x)=orbitalCoverMultiplicity G P x := by
  unfold orbitalCoverMultiplicity
  calc
    (∑' g : G, P.indicator (fun _ : X => (1 : ℝ≥0∞)) (g⁻¹ • (h • x))) =
      ∑' k : G, P.indicator (fun _ : X => (1 : ℝ≥0∞)) ((h*k)⁻¹ • (h • x)) :=
        ((Equiv.mulLeft h).tsum_eq _).symm
    _ = _ := tsum_congr (fun k => by simp [mul_smul])

theorem orbitalCoverMultiplicity_eq_card (P : Set X) (x : X)
    (hf : {g : G | g⁻¹ • x ∈ P}.Finite) :
    orbitalCoverMultiplicity G P x=(hf.toFinset.card : ℝ≥0∞) := by
  classical
  unfold orbitalCoverMultiplicity
  rw [tsum_eq_sum (s:=hf.toFinset)]
  · have hi : ∀g∈hf.toFinset,
        P.indicator (fun _ : X => (1 : ℝ≥0∞)) (g⁻¹ • x)=1 := by
      intro g hg
      have hm : g⁻¹ • x∈P:=hf.mem_toFinset.mp hg
      exact Set.indicator_of_mem hm _
    rw [Finset.sum_congr rfl hi]
    simp
  · intro g hg
    exact Set.indicator_of_notMem (by simpa only [Set.Finite.mem_toFinset,mem_ofPred_eq] using hg) _

section Measurable
variable [MeasurableSpace X] [MeasurableConstSMul G X] [Countable G]

/-- The literal translate count is measurable for every original measurable polygon. -/
theorem measurable_orbitalCoverMultiplicity {P : Set X} (hP : MeasurableSet P) :
    Measurable (orbitalCoverMultiplicity G P) := by
  apply Measurable.tsum
  intro g
  exact (measurable_const.indicator hP).comp (measurable_const_smul g⁻¹)

/-- Integrating the genuine translate count on an actual fundamental domain gives
exactly the measure of the original polygon, without assuming constant multiplicity. -/
theorem measure_eq_lintegral_orbitalCoverMultiplicity (μ : Measure X)
    [SMulInvariantMeasure G X μ] {Q P : Set X}
    (hQ : MeasureTheory.IsFundamentalDomain G Q μ) (hP : MeasurableSet P) :
    μ P=∫⁻ x in Q, orbitalCoverMultiplicity G P x ∂μ := by
  rw [←lintegral_indicator_one hP,hQ.lintegral_eq_tsum']
  unfold orbitalCoverMultiplicity
  exact (lintegral_tsum (fun g =>
    ((measurable_const.indicator hP).comp (measurable_const_smul g⁻¹)).aemeasurable)).symm

/-- An almost-everywhere constant integer overlap count scales the fundamental-domain measure. -/
theorem measure_eq_mul_of_ae_orbitalCoverMultiplicity (μ : Measure X)
    [SMulInvariantMeasure G X μ] {Q P : Set X}
    (hQ : MeasureTheory.IsFundamentalDomain G Q μ) (hP : MeasurableSet P)
    (k : ℕ) (hk : ∀ᵐ x ∂μ.restrict Q, orbitalCoverMultiplicity G P x=k) :
    μ P=(k : ℝ≥0∞)*μ Q := by
  rw [measure_eq_lintegral_orbitalCoverMultiplicity μ hQ hP,
    lintegral_congr_ae hk,setLIntegral_const]

end Measurable

/-- Local finiteness and avoidance of every actual boundary imply simultaneous
stability of all original tile memberships, including the infinitely many absent tiles. -/
theorem locallyFinite_membership_germ [TopologicalSpace X]
    {ι : Type*} {U : ι → Set X} (hU : LocallyFinite U) (x : X)
    (hx : ∀i,x∉frontier (U i)) :
    ∀ᶠ y in 𝓝 x,∀i,y∈U i ↔ x∈U i := by
  obtain ⟨N,hN,hf⟩:=hU x
  have stable (i : ι) : ∀ᶠ y in 𝓝 x,y∈U i ↔x∈U i := by
    have hh : x∈interior (U i) ∪ interior (U i)ᶜ := by
      rw [←compl_frontier_eq_union_interior]
      exact hx i
    rcases hh with hi | hi
    · have hxI:=interior_subset hi
      filter_upwards [isOpen_interior.mem_nhds hi] with y hy
      exact iff_of_true (interior_subset hy) hxI
    · have hxI:=interior_subset hi
      filter_upwards [isOpen_interior.mem_nhds hi] with y hy
      exact iff_of_false (interior_subset hy) hxI
  filter_upwards [hN,hf.eventually_all.mpr (fun i _ =>stable i)] with y hy hstable i
  by_cases hi : i∈{j | (U j∩N).Nonempty}
  · exact hstable i hi
  · have hx0 : x∉U i:=fun hm=>hi ⟨x,hm,mem_of_mem_nhds hN⟩
    have hy0 : y∉U i:=fun hm=>hi ⟨y,hm,hy⟩
    exact iff_of_false hy0 hx0

/-- The actual integer translate multiplicity is locally constant off the actual union
of translated polygon boundaries; no packing or fundamental-domain assumption is used. -/
theorem orbitalCoverMultiplicity_locally_constant_off_boundaries [TopologicalSpace X]
    (P : Set X) (hLF : LocallyFinite (fun g : G=>g • P)) (x : X)
    (hx : ∀g : G,x∉frontier (g • P)) :
    ∀ᶠ y in 𝓝 x,orbitalCoverMultiplicity G P y=orbitalCoverMultiplicity G P x := by
  classical
  filter_upwards [locallyFinite_membership_germ hLF x hx] with y hy
  apply tsum_congr
  intro g
  have he : g⁻¹ • y∈P ↔g⁻¹ • x∈P:=by
    simpa only [mem_smul_set_iff_inv_smul_mem] using hy g
  by_cases hm : g⁻¹ • y∈P
  · rw [indicator_of_mem hm,indicator_of_mem (he.mp hm)]
  · rw [indicator_of_notMem hm,indicator_of_notMem (fun h=>hm (he.mpr h))]

end LowDimensionalTopology.Geometry.DiscreteGroups.Action
