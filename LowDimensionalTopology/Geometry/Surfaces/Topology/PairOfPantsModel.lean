module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Tauto

/-!
# The standard planar region with three circular boundary curves

The open region and its closed carrier are concrete subsets of the complex
plane. The three labelled circles are proved to be disjoint and to form the
whole frontier. No assertion about connected components is built into the data.
-/

public section
noncomputable section
open Set Metric

namespace LowDimensionalTopology.Geometry.Surfaces

/-- The open radius-two disk with two closed radius-one-half disks removed. -/
@[expose] def pantsPlanarRegion : Set ℂ :=
  {z | ‖z‖ < 2 ∧ (1 : ℝ) / 2 < ‖z + 1‖ ∧ (1 : ℝ) / 2 < ‖z - 1‖}

/-- The closed radius-two disk with the interiors of the two smaller disks
removed; every boundary circle is retained. -/
@[expose] def pantsClosedPlanarRegion : Set ℂ :=
  {z | ‖z‖ ≤ 2 ∧ (1 : ℝ) / 2 ≤ ‖z + 1‖ ∧ (1 : ℝ) / 2 ≤ ‖z - 1‖}

/-- The outer, left inner, and right inner boundary circles, in that order. -/
@[expose] def pantsModelBoundaryCircle (i : Fin 3) : Set ℂ :=
  if i = 0 then {z | ‖z‖ = 2}
  else if i = 1 then {z | ‖z + 1‖ = (1 : ℝ) / 2}
  else {z | ‖z - 1‖ = (1 : ℝ) / 2}

/-- The standard open region is open in the original complex plane. -/
theorem isOpen_pantsPlanarRegion : IsOpen pantsPlanarRegion := by
  unfold pantsPlanarRegion
  have hp : Continuous (fun z : ℂ => ‖z + 1‖) := by fun_prop
  have hm : Continuous (fun z : ℂ => ‖z - 1‖) := by fun_prop
  exact (isOpen_lt continuous_norm (continuous_const : Continuous (fun _ : ℂ => (2 : ℝ)))).inter
    ((isOpen_lt (continuous_const : Continuous (fun _ : ℂ => (1 : ℝ) / 2)) hp).inter
      (isOpen_lt (continuous_const : Continuous (fun _ : ℂ => (1 : ℝ) / 2)) hm))

/-- The carrier with the boundary retained is closed. -/
theorem isClosed_pantsClosedPlanarRegion : IsClosed pantsClosedPlanarRegion := by
  unfold pantsClosedPlanarRegion
  have hp : Continuous (fun z : ℂ => ‖z + 1‖) := by fun_prop
  have hm : Continuous (fun z : ℂ => ‖z - 1‖) := by fun_prop
  exact (isClosed_le continuous_norm (continuous_const : Continuous (fun _ : ℂ => (2 : ℝ)))).inter
    ((isClosed_le (continuous_const : Continuous (fun _ : ℂ => (1 : ℝ) / 2)) hp).inter
      (isClosed_le (continuous_const : Continuous (fun _ : ℂ => (1 : ℝ) / 2)) hm))

/-- The open region is contained in the carrier retaining its boundary. -/
theorem pantsPlanarRegion_subset_closed : pantsPlanarRegion ⊆ pantsClosedPlanarRegion :=
  fun _ hz => ⟨hz.1.le, hz.2.1.le, hz.2.2.le⟩

/-- Compactness follows from closedness inside the actual radius-two ball. -/
theorem isCompact_pantsClosedPlanarRegion : IsCompact pantsClosedPlanarRegion := by
  apply (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset
    isClosed_pantsClosedPlanarRegion
  intro z hz
  simpa only [mem_closedBall, dist_zero_right] using hz.1

/-- The origin belongs to the open region. -/
theorem pantsPlanarRegion_nonempty : pantsPlanarRegion.Nonempty :=
  ⟨0, by norm_num [pantsPlanarRegion]⟩

/-- The closed carrier is nonempty. -/
theorem pantsClosedPlanarRegion_nonempty : pantsClosedPlanarRegion.Nonempty :=
  pantsPlanarRegion_nonempty.mono pantsPlanarRegion_subset_closed

@[simp] theorem pantsModelBoundaryCircle_zero :
    pantsModelBoundaryCircle 0 = sphere (0 : ℂ) 2 := by
  ext z
  simp [pantsModelBoundaryCircle]

@[simp] theorem pantsModelBoundaryCircle_one :
    pantsModelBoundaryCircle 1 = sphere (-1 : ℂ) ((1 : ℝ) / 2) := by
  ext z
  simp [pantsModelBoundaryCircle, sub_neg_eq_add]

@[simp] theorem pantsModelBoundaryCircle_two :
    pantsModelBoundaryCircle 2 = sphere (1 : ℂ) ((1 : ℝ) / 2) := by
  ext z
  simp [pantsModelBoundaryCircle]

/-- Every labelled boundary set is a genuine nonempty Euclidean circle. -/
theorem pantsModelBoundaryCircle_nonempty (i : Fin 3) :
    (pantsModelBoundaryCircle i).Nonempty := by
  fin_cases i
  · change (pantsModelBoundaryCircle (0 : Fin 3)).Nonempty
    rw [pantsModelBoundaryCircle_zero]
    exact (NormedSpace.sphere_nonempty (x := (0 : ℂ)) (r := (2 : ℝ))).mpr (by norm_num)
  · change (pantsModelBoundaryCircle (1 : Fin 3)).Nonempty
    rw [pantsModelBoundaryCircle_one]
    exact (NormedSpace.sphere_nonempty (x := (-1 : ℂ)) (r := (1 : ℝ) / 2)).mpr (by norm_num)
  · change (pantsModelBoundaryCircle (2 : Fin 3)).Nonempty
    rw [pantsModelBoundaryCircle_two]
    exact (NormedSpace.sphere_nonempty (x := (1 : ℂ)) (r := (1 : ℝ) / 2)).mpr (by norm_num)

/-- Each labelled circle is compact in the ambient complex plane. -/
theorem isCompact_pantsModelBoundaryCircle (i : Fin 3) :
    IsCompact (pantsModelBoundaryCircle i) := by
  fin_cases i
  · change IsCompact (pantsModelBoundaryCircle (0 : Fin 3))
    rw [pantsModelBoundaryCircle_zero]
    exact isCompact_sphere (0 : ℂ) (2 : ℝ)
  · change IsCompact (pantsModelBoundaryCircle (1 : Fin 3))
    rw [pantsModelBoundaryCircle_one]
    exact isCompact_sphere (-1 : ℂ) ((1 : ℝ) / 2)
  · change IsCompact (pantsModelBoundaryCircle (2 : Fin 3))
    rw [pantsModelBoundaryCircle_two]
    exact isCompact_sphere (1 : ℂ) ((1 : ℝ) / 2)

/-- The three distance inequalities separating the circles. -/
theorem pantsModel_norm_separation (z : ℂ) :
    ‖z‖ ≤ ‖z + 1‖ + 1 ∧ ‖z‖ ≤ ‖z - 1‖ + 1 ∧
      2 ≤ ‖z + 1‖ + ‖z - 1‖ := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [add_sub_cancel_right, norm_one] using norm_sub_le (z + 1) (1 : ℂ)
  · simpa only [sub_add_cancel, norm_one] using norm_add_le (z - 1) (1 : ℂ)
  · have heq : (z + 1) - (z - 1) = (2 : ℂ) := by ring
    simpa [heq] using norm_sub_le (z + 1) (z - 1)

/-- All three actual circles lie in the carrier retaining the boundary. -/
theorem pantsModelBoundaryCircle_subset_closed (i : Fin 3) :
    pantsModelBoundaryCircle i ⊆ pantsClosedPlanarRegion := by
  intro z hz
  obtain ⟨h₀, h₁, h₂⟩ := pantsModel_norm_separation z
  fin_cases i <;> norm_num [pantsModelBoundaryCircle, pantsClosedPlanarRegion] at hz ⊢
  all_goals exact ⟨by linarith, by linarith, by linarith⟩

/-- The three labelled circles are pairwise disjoint as actual subsets. -/
theorem pantsModelBoundaryCircle_pairwise_disjoint :
    Pairwise fun i j : Fin 3 => Disjoint (pantsModelBoundaryCircle i)
      (pantsModelBoundaryCircle j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  obtain ⟨h₀, h₁, h₂⟩ := pantsModel_norm_separation z
  fin_cases i <;> fin_cases j
  all_goals try exact (hij rfl).elim
  all_goals norm_num [pantsModelBoundaryCircle] at hzi hzj
  all_goals linarith

/-- The difference between the closed and open models is precisely the
union of the three labelled circles. -/
theorem pantsClosedPlanarRegion_sdiff_open :
    pantsClosedPlanarRegion \ pantsPlanarRegion =
      ⋃ i : Fin 3, pantsModelBoundaryCircle i := by
  ext z
  simp only [mem_sdiff, mem_iUnion]
  constructor
  · rintro ⟨hz, hn⟩
    by_cases h₀ : ‖z‖ = 2
    · exact ⟨0, by simpa [pantsModelBoundaryCircle] using h₀⟩
    by_cases h₁ : ‖z + 1‖ = (1 : ℝ) / 2
    · exact ⟨1, by simpa [pantsModelBoundaryCircle] using h₁⟩
    refine ⟨2, ?_⟩
    have h₂ : ‖z - 1‖ = (1 : ℝ) / 2 := by
      by_contra h₂
      exact hn ⟨lt_of_le_of_ne hz.1 h₀,
        lt_of_le_of_ne hz.2.1 (Ne.symm h₁), lt_of_le_of_ne hz.2.2 (Ne.symm h₂)⟩
    simpa [pantsModelBoundaryCircle] using h₂
  · rintro ⟨i, hi⟩
    refine ⟨pantsModelBoundaryCircle_subset_closed i hi, ?_⟩
    rintro ⟨h₀, h₁, h₂⟩
    fin_cases i <;> norm_num [pantsModelBoundaryCircle] at hi
    all_goals linarith

/-- Every point of every labelled circle is a limit of the actual open
region; the other two inequalities remain strict near that circle. -/
theorem pantsModelBoundaryCircle_subset_closure (i : Fin 3) :
    pantsModelBoundaryCircle i ⊆ closure pantsPlanarRegion := by
  intro z hz
  obtain ⟨h₀, h₁, h₂⟩ := pantsModel_norm_separation z
  fin_cases i
  · have hz' : ‖z‖ = 2 := by simpa [pantsModelBoundaryCircle] using hz
    let U : Set ℂ := {w | (1 : ℝ) / 2 < ‖w + 1‖ ∧ (1 : ℝ) / 2 < ‖w - 1‖}
    have hp : Continuous (fun w : ℂ => ‖w + 1‖) := by fun_prop
    have hm : Continuous (fun w : ℂ => ‖w - 1‖) := by fun_prop
    have hU : IsOpen U := by
      change IsOpen ({w : ℂ | (1 : ℝ) / 2 < ‖w + 1‖} ∩
        {w : ℂ | (1 : ℝ) / 2 < ‖w - 1‖})
      exact (isOpen_lt (continuous_const : Continuous (fun _ : ℂ => (1 : ℝ) / 2)) hp).inter
        (isOpen_lt (continuous_const : Continuous (fun _ : ℂ => (1 : ℝ) / 2)) hm)
    have hzU : z ∈ U := ⟨by linarith, by linarith⟩
    have hzB : z ∈ closure (ball (0 : ℂ) 2) := by
      rw [closure_ball (0 : ℂ) (by norm_num : (2 : ℝ) ≠ 0)]
      simpa only [mem_closedBall, dist_zero_right] using hz'.le
    have heq : U ∩ ball (0 : ℂ) 2 = pantsPlanarRegion := by
      ext w
      simp only [U, pantsPlanarRegion, mem_inter_iff, mem_ofPred_eq,
        mem_ball, dist_zero_right]
      tauto
    rw [← heq]
    exact hU.inter_closure ⟨hzU, hzB⟩
  · have hz' : ‖z + 1‖ = (1 : ℝ) / 2 := by
      simpa [pantsModelBoundaryCircle] using hz
    let U : Set ℂ := {w | ‖w‖ < 2 ∧ (1 : ℝ) / 2 < ‖w - 1‖}
    have hm : Continuous (fun w : ℂ => ‖w - 1‖) := by fun_prop
    have hU : IsOpen U := by
      change IsOpen ({w : ℂ | ‖w‖ < 2} ∩ {w : ℂ | (1 : ℝ) / 2 < ‖w - 1‖})
      exact (isOpen_lt continuous_norm (continuous_const : Continuous (fun _ : ℂ => (2 : ℝ)))).inter
        (isOpen_lt (continuous_const : Continuous (fun _ : ℂ => (1 : ℝ) / 2)) hm)
    have hzU : z ∈ U := ⟨by linarith, by linarith⟩
    have hzB : z ∈ closure ((closedBall (-1 : ℂ) ((1 : ℝ) / 2))ᶜ) := by
      rw [closure_compl, interior_closedBall (-1 : ℂ) (by norm_num : (1 : ℝ) / 2 ≠ 0)]
      simpa only [mem_compl_iff, mem_ball, dist_eq_norm, sub_neg_eq_add, not_lt] using hz'.ge
    have heq : U ∩ (closedBall (-1 : ℂ) ((1 : ℝ) / 2))ᶜ = pantsPlanarRegion := by
      ext w
      simp only [U, pantsPlanarRegion, mem_inter_iff, mem_ofPred_eq,
        mem_compl_iff, mem_closedBall, dist_eq_norm, sub_neg_eq_add, not_le]
      tauto
    rw [← heq]
    exact hU.inter_closure ⟨hzU, hzB⟩
  · have hz' : ‖z - 1‖ = (1 : ℝ) / 2 := by
      simpa [pantsModelBoundaryCircle] using hz
    let U : Set ℂ := {w | ‖w‖ < 2 ∧ (1 : ℝ) / 2 < ‖w + 1‖}
    have hp : Continuous (fun w : ℂ => ‖w + 1‖) := by fun_prop
    have hU : IsOpen U := by
      change IsOpen ({w : ℂ | ‖w‖ < 2} ∩ {w : ℂ | (1 : ℝ) / 2 < ‖w + 1‖})
      exact (isOpen_lt continuous_norm (continuous_const : Continuous (fun _ : ℂ => (2 : ℝ)))).inter
        (isOpen_lt (continuous_const : Continuous (fun _ : ℂ => (1 : ℝ) / 2)) hp)
    have hzU : z ∈ U := ⟨by linarith, by linarith⟩
    have hzB : z ∈ closure ((closedBall (1 : ℂ) ((1 : ℝ) / 2))ᶜ) := by
      rw [closure_compl, interior_closedBall (1 : ℂ) (by norm_num : (1 : ℝ) / 2 ≠ 0)]
      simpa only [mem_compl_iff, mem_ball, dist_eq_norm, not_lt] using hz'.ge
    have heq : U ∩ (closedBall (1 : ℂ) ((1 : ℝ) / 2))ᶜ = pantsPlanarRegion := by
      ext w
      simp only [U, pantsPlanarRegion, mem_inter_iff, mem_ofPred_eq,
        mem_compl_iff, mem_closedBall, dist_eq_norm, not_le]
      tauto
    rw [← heq]
    exact hU.inter_closure ⟨hzU, hzB⟩

/-- The closed carrier is the actual ambient closure of the original open
region, rather than an assumed compactification. -/
theorem closure_pantsPlanarRegion :
    closure pantsPlanarRegion = pantsClosedPlanarRegion := by
  apply Subset.antisymm
  · exact isClosed_pantsClosedPlanarRegion.closure_subset_iff.mpr
      pantsPlanarRegion_subset_closed
  · intro z hz
    by_cases ho : z ∈ pantsPlanarRegion
    · exact subset_closure ho
    have hb : z ∈ ⋃ i : Fin 3, pantsModelBoundaryCircle i := by
      rw [← pantsClosedPlanarRegion_sdiff_open]
      exact ⟨hz, ho⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp hb
    exact pantsModelBoundaryCircle_subset_closure i hi

/-- The interior of the closed carrier is the original open region. -/
theorem interior_pantsClosedPlanarRegion :
    interior pantsClosedPlanarRegion = pantsPlanarRegion := by
  have heq : pantsClosedPlanarRegion = closedBall (0 : ℂ) 2 ∩
      ((ball (-1 : ℂ) ((1 : ℝ) / 2))ᶜ ∩ (ball (1 : ℂ) ((1 : ℝ) / 2))ᶜ) := by
    ext z
    simp only [pantsClosedPlanarRegion, mem_ofPred_eq, mem_inter_iff,
      mem_closedBall, mem_ball, mem_compl_iff, dist_eq_norm, sub_zero,
      sub_neg_eq_add, not_lt]
  rw [heq, interior_inter, interior_inter, interior_compl, interior_compl,
    interior_closedBall (0 : ℂ) (by norm_num : (2 : ℝ) ≠ 0),
    closure_ball (-1 : ℂ) (by norm_num : (1 : ℝ) / 2 ≠ 0),
    closure_ball (1 : ℂ) (by norm_num : (1 : ℝ) / 2 ≠ 0)]
  ext z
  simp only [pantsPlanarRegion, mem_ofPred_eq, mem_inter_iff, mem_ball,
    mem_closedBall, mem_compl_iff, dist_eq_norm, sub_zero, sub_neg_eq_add, not_le]

/-- The whole ambient frontier is exactly the union of the three labelled
nonempty disjoint circles. This does not assume a component classification. -/
theorem frontier_pantsPlanarRegion :
    frontier pantsPlanarRegion = ⋃ i : Fin 3, pantsModelBoundaryCircle i := by
  rw [isOpen_pantsPlanarRegion.frontier_eq, closure_pantsPlanarRegion,
    pantsClosedPlanarRegion_sdiff_open]

/-- The closed model has the same exact union of three circles as frontier. -/
theorem frontier_pantsClosedPlanarRegion :
    frontier pantsClosedPlanarRegion = ⋃ i : Fin 3, pantsModelBoundaryCircle i := by
  rw [isClosed_pantsClosedPlanarRegion.frontier_eq, interior_pantsClosedPlanarRegion,
    pantsClosedPlanarRegion_sdiff_open]

/-- The actual closure of the open region is compact. -/
theorem isCompact_closure_pantsPlanarRegion : IsCompact (closure pantsPlanarRegion) := by
  rw [closure_pantsPlanarRegion]
  exact isCompact_pantsClosedPlanarRegion

end LowDimensionalTopology.Geometry.Surfaces
