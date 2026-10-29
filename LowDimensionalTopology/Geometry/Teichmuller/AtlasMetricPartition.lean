module

public import LowDimensionalTopology.Geometry.Teichmuller.AtlasMetricLocalSections
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.RiemannManifold
public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# A smooth positive metric from the original complex chart cover

The original surface supplies Hausdorffness and, by Rado's theorem, second
countability. Local compactness then gives sigma compactness, so Mathlib's
smooth partition of unity applies without a compactness hypothesis. Weighted
original chart forms give a genuine metric on the unchanged tangent bundle.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Bundle Set Filter Topology Bornology
open scoped Manifold ContDiff InnerProductSpace

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
namespace AtlasMetricConstruction

universe u
variable {X : Type u} [TopologicalSpace X] (R : RiemannSurface X)

/-- Smooth weights on the original carrier and its real smooth structure. -/
abbrev Partition :=
  let := R.toRiemannAtlas.toChartedSpace
  SmoothPartitionOfUnity X 𝓘(ℝ, ℂ) X univ

/-- The partition is subordinate to the actual sources of the chosen original charts. -/
def Subordinate (ρ : Partition R) : Prop :=
  ∀ j : X, tsupport (ρ j) ⊆ (chosenChart R j).val.source

theorem exists_partition : ∃ ρ : Partition R, Subordinate R ρ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  let := R.t2Space
  let := R.secondCountableTopology
  let : LocallyCompactSpace X := ChartedSpace.locallyCompactSpace ℂ X
  let : SigmaCompactSpace X := sigmaCompactSpace_of_locallyCompact_secondCountable
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate_chartAt_source 𝓘(ℝ, ℂ) X
  exact ⟨ρ, hρ⟩

/-- A finite sum at each point, with the partition's actual nonzero support. -/
def partitionForm (ρ : Partition R) (x : X) : TangentForm R x := by
  let := R.toRiemannAtlas.toChartedSpace
  exact ∑ j ∈ ρ.finsupport x, ρ j x • localForm R j x

@[simp]
theorem partitionForm_apply (ρ : Partition R) (x : X)
    (v w : RealSurfaceTangent R x) :
    let := R.toRiemannAtlas.toChartedSpace
    partitionForm R ρ x v w =
      ∑ j ∈ ρ.finsupport x, ρ j x * localForm R j x v w := by
  let := R.toRiemannAtlas.toChartedSpace
  simp [partitionForm]

private theorem source_of_weight_ne_zero (ρ : Partition R) (hρ : Subordinate R ρ)
    (j x : X) (hj : ρ j x ≠ 0) : x ∈ (chosenChart R j).val.source :=
  hρ j (subset_tsupport _ hj)

private theorem weighted_self_nonneg (ρ : Partition R) (hρ : Subordinate R ρ)
    (j x : X) (v : RealSurfaceTangent R x) :
    0 ≤ ρ j x * localForm R j x v v := by
  let := R.toRiemannAtlas.toChartedSpace
  by_cases hj : ρ j x = 0
  · simp [hj]
  · rw [localForm_eq_chartForm R j x (source_of_weight_ne_zero R ρ hρ j x hj)]
    exact mul_nonneg (ρ.nonneg j x) (chartForm_self_nonneg R _ x v)

theorem partitionForm_symm (ρ : Partition R) (hρ : Subordinate R ρ) (x : X)
    (v w : RealSurfaceTangent R x) :
    partitionForm R ρ x v w = partitionForm R ρ x w v := by
  let := R.toRiemannAtlas.toChartedSpace
  rw [partitionForm_apply, partitionForm_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : ρ j x ≠ 0 := by simpa only [ρ.mem_finsupport, Function.mem_support] using hj
  rw [localForm_eq_chartForm R j x (source_of_weight_ne_zero R ρ hρ j x hj')]
  rw [chartForm_symm]

/-- A single positive weight gives a genuine quantitative chart lower bound. -/
theorem partitionForm_self_lower (ρ : Partition R) (hρ : Subordinate R ρ)
    (j x : X) (hj : 0 < ρ j x) (v : RealSurfaceTangent R x) :
    ρ j x * chartForm R (chosenChart R j) x v v ≤ partitionForm R ρ x v v := by
  let := R.toRiemannAtlas.toChartedSpace
  have hjmem : j ∈ ρ.finsupport x := by
    simpa only [ρ.mem_finsupport, Function.mem_support] using hj.ne'
  rw [partitionForm_apply]
  have hle := Finset.single_le_sum
    (fun k (_ : k ∈ ρ.finsupport x) => weighted_self_nonneg R ρ hρ k x v) hjmem
  rw [localForm_eq_chartForm R j x (source_of_weight_ne_zero R ρ hρ j x hj.ne')] at hle
  exact hle

theorem partitionForm_self_pos (ρ : Partition R) (hρ : Subordinate R ρ)
    (x : X) (v : RealSurfaceTangent R x) (hv : v ≠ 0) :
    0 < partitionForm R ρ x v v := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨j, hj⟩ := ρ.exists_pos_of_mem (mem_univ x)
  have hsource := source_of_weight_ne_zero R ρ hρ j x hj.ne'
  exact (mul_pos hj (chartForm_self_pos R _ x hsource v hv)).trans_le
    (partitionForm_self_lower R ρ hρ j x hj v)

private theorem isVonNBounded_sublevel_of_coordinate_lower_bound
    {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
    (D : V ≃L[ℝ] ℂ) {a : ℝ} (ha : 0 < a) (q : V → ℝ)
    (hbound : ∀ v : V, a * ‖D v‖ ^ 2 ≤ q v) :
    IsVonNBounded ℝ {v : V | q v < 1} := by
  have hball : IsVonNBounded ℝ
      (D.symm.toContinuousLinearMap '' Metric.ball (0 : ℂ) (Real.sqrt (1 / a))) :=
    (NormedSpace.isVonNBounded_ball ℝ ℂ (Real.sqrt (1 / a))).image
      D.symm.toContinuousLinearMap
  apply hball.subset
  intro v hv
  refine ⟨D v, ?_, D.symm_apply_apply v⟩
  rw [Metric.mem_ball, dist_zero_right, Real.lt_sqrt (norm_nonneg (D v))]
  apply (lt_div_iff₀ ha).mpr
  have hv' : q v < 1 := hv
  nlinarith [hbound v]

/-- Boundedness is in the original tangent topology, without adding a fiber norm. -/
theorem partitionForm_isVonNBounded (ρ : Partition R) (hρ : Subordinate R ρ) (x : X) :
    IsVonNBounded ℝ {v : RealSurfaceTangent R x | partitionForm R ρ x v v < 1} := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨j, hj⟩ := ρ.exists_pos_of_mem (mem_univ x)
  have hsource := source_of_weight_ne_zero R ρ hρ j x hj.ne'
  let D := SmoothSurfaceEquiv.originalChartDifferentialEquiv (chosenChart R j) x hsource
  apply isVonNBounded_sublevel_of_coordinate_lower_bound D hj
    (fun v => partitionForm R ρ x v v)
  intro v
  simpa only [D, SmoothSurfaceEquiv.originalChartDifferentialEquiv_apply,
    chartForm_apply, real_inner_self_eq_norm_sq] using
    partitionForm_self_lower R ρ hρ j x hj v

/-- Smoothness comes from the local sections and their actual locally finite supports. -/
theorem partitionForm_contMDiff (ρ : Partition R) (hρ : Subordinate R ρ) :
    let := R.toRiemannAtlas.toChartedSpace
    let := R.toRiemannAtlas.isRealManifold
    ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, FormModel)) ∞
      (fun x => TotalSpace.mk' (E := fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ]
        TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) FormModel x (partitionForm R ρ x)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  change ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, FormModel)) ∞
    (fun x => TotalSpace.mk' (E := fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ]
        TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) FormModel x (partitionForm R ρ x))
  have hs (j : X) : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, FormModel)) ∞
      (fun x => TotalSpace.mk' (E := fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ]
        TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) FormModel x (ρ j x • localForm R j x)) :=
    ContMDiffOn.smul_section_of_tsupport (ρ j).contMDiff.contMDiffOn
      (chosenChart R j).val.open_source (hρ j) (localForm_contMDiffOn R j)
  have hf : LocallyFinite (fun j => {x : X | ρ j x • localForm R j x ≠ 0}) := by
    apply ρ.locallyFinite.subset
    intro j x hx
    change ρ j x • localForm R j x ≠ 0 at hx
    change ρ j x ≠ 0
    intro hz
    apply hx
    ext v w
    simp only [smul_apply, hz, smul_eq_mul, zero_mul,
      zero_apply]
  have hsum : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, FormModel)) ∞
      (fun x => TotalSpace.mk' (E := fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ]
        TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) FormModel x
          (∑ᶠ j, ρ j x • localForm R j x)) :=
    ContMDiff.finsum_section_of_locallyFinite (F := FormModel)
      (V := fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ]
        TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) hf hs
  have hEq (x : X) : partitionForm R ρ x = ∑ᶠ j, ρ j x • localForm R j x :=
    ρ.sum_finsupport_smul_eq_finsum x (fun j _ => localForm R j x)
  apply hsum.congr
  intro x
  exact congrArg (TotalSpace.mk' (E := fun y : X => TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ]
        TangentSpace 𝓘(ℝ, ℂ) y →L[ℝ] ℝ) FormModel x) (hEq x)

/-- The partition defines actual smooth metric data on the unchanged tangent bundle. -/
def metricOfPartition (ρ : Partition R) (hρ : Subordinate R ρ) : SmoothSurfaceMetric R := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isRealManifold
  exact
    { inner := partitionForm R ρ
      symm := partitionForm_symm R ρ hρ
      pos := partitionForm_self_pos R ρ hρ
      isVonNBounded := partitionForm_isVonNBounded R ρ hρ
      contMDiff := partitionForm_contMDiff R ρ hρ }

end AtlasMetricConstruction

end LowDimensionalTopology.Geometry.Teichmuller
