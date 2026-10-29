module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchySeriesIntegral
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchyKernelTail
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.InfiniteSum.Ring
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Local uniform convergence of the same actual angular Cauchy series

The true norm-integral summability bounds every absolute integral tail by
the positive kernel tail already proved to converge uniformly on compacts.
The same actual HasSum then controls signed partial sums. The original
closed-geodesic consumer supplies its own one-support and countability.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

open LowDimensionalTopology.Geometry.Surfaces

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

private theorem rightCoset_integral_tail_le_kernel_tail
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ) [Countable Γ]
    (hsep : ∀ ζ : ℂ,
      ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
        rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0 →
        rightCosetInfinitesimalZeroExtension θ Γ s v ζ ≠ 0 → u = v)
    (F : Finset (Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)))) (z : ℂ) :
    (show ℝ from by
      classical
      exact ∑' u : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
        if u ∈ F then 0 else ‖rightCosetCauchyTerm θ Γ s u z‖) ≤
    (1 / Real.pi) * ∫ ζ : ℂ,
      (show ℝ from by
        classical
        exact ∑' u : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
          if u ∈ F then 0 else ‖rightCosetInfinitesimalZeroExtension θ Γ s u ζ‖) *
          ‖Quasiconformal.firstVariationKernel z ζ‖ := by
  classical
  let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
  let D := {u : C // u ∉ F}
  let f : D → ℂ → ℝ := fun u ζ => ‖rightCosetInfinitesimalZeroExtension θ Γ s u.val ζ *
    Quasiconformal.firstVariationKernel z ζ‖
  let k : ℝ := 1 / Real.pi
  have hf (u : D) : Integrable (f u) (volume : Measure ℂ) :=
    (integrable_rightCosetInfinitesimalZeroExtension_mul_firstVariationKernel θ Γ s u.val z).norm
  have hs : Summable (fun u : D => ∫ ζ : ℂ, f u ζ) :=
    (summable_integral_norm_rightCoset_kernel θ Γ s hsep z).subtype (fun u => u ∉ F)
  have hsn : Summable (fun u : D => ∫ ζ : ℂ, ‖f u ζ‖) := by
    simpa only [f, norm_norm] using hs
  have hπ : ‖-(1 / (Real.pi : ℂ))‖ = k := by
    rw [norm_neg, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hterm (u : D) : ‖rightCosetCauchyTerm θ Γ s u.val z‖ ≤ k * ∫ ζ : ℂ, f u ζ := by
    change ‖(-(1 / (Real.pi : ℂ))) * ∫ ζ : ℂ,
      rightCosetInfinitesimalZeroExtension θ Γ s u.val ζ *
        Quasiconformal.firstVariationKernel z ζ‖ ≤ _
    rw [norm_mul, hπ]
    exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
      (one_div_nonneg.mpr Real.pi_pos.le)
  have habs : Summable (fun u : D => ‖rightCosetCauchyTerm θ Γ s u.val z‖) :=
    ((rightCosetCauchySeries_hasSum θ Γ s hsep).2.2 z).2.1.subtype (fun u => u ∉ F)
  have heq : (fun ζ : ℂ => ∑' u : D, f u ζ) =
      (fun ζ => (∑' u : C, if u ∈ F then 0 else
        ‖rightCosetInfinitesimalZeroExtension θ Γ s u ζ‖) *
          ‖Quasiconformal.firstVariationKernel z ζ‖) := by
    funext ζ
    simp only [f, norm_mul]
    rw [tsum_mul_right]
    congr 1
    change (∑' u : {u : C | u ∉ F},
      ‖rightCosetInfinitesimalZeroExtension θ Γ s u.val ζ‖) = _
    rw [tsum_subtype {u : C | u ∉ F}
      (fun u => ‖rightCosetInfinitesimalZeroExtension θ Γ s u ζ‖)]
    apply tsum_congr
    intro u
    by_cases hu : u ∈ F
    · simp [Set.indicator, hu]
    · simp [Set.indicator, hu]
  have ht : (∑' u : D, ‖rightCosetCauchyTerm θ Γ s u.val z‖) =
      ∑' u : C, if u ∈ F then 0 else ‖rightCosetCauchyTerm θ Γ s u z‖ := by
    change (∑' u : {u : C | u ∉ F}, ‖rightCosetCauchyTerm θ Γ s u.val z‖) = _
    rw [tsum_subtype {u : C | u ∉ F}
      (fun u => ‖rightCosetCauchyTerm θ Γ s u z‖)]
    apply tsum_congr
    intro u
    by_cases hu : u ∈ F
    · simp [Set.indicator, hu]
    · simp [Set.indicator, hu]
  rw [← ht]
  calc
    _ ≤ ∑' u : D, k * ∫ ζ : ℂ, f u ζ := Summable.tsum_le_tsum hterm habs (hs.mul_left k)
    _ = k * ∫ ζ : ℂ, ∑' u : D, f u ζ := by
      rw [tsum_mul_left, integral_tsum_of_summable_integral_norm hf hsn]
    _ = _ := by rw [heq]

/-- The same actual angular integral series has locally uniform signed sums
and uniformly vanishing absolute tails on each compact set. -/
theorem rightCosetCauchySeries_tendstoLocallyUniformlyOn
    (θ : Width) (Γ : Subgroup Deck) (s : ℝ) [Countable Γ]
    (hsep : ∀ ζ : ℂ,
      ∀ u v : Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s)),
        rightCosetInfinitesimalZeroExtension θ Γ s u ζ ≠ 0 →
        rightCosetInfinitesimalZeroExtension θ Γ s v ζ ≠ 0 → u = v) :
    let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
    let ν : ℂ → ℂ := fun ζ => ∑' u : C, rightCosetInfinitesimalZeroExtension θ Γ s u ζ
    let Tail : Finset C → ℂ → ℝ := fun F z => by
      classical
      exact ∑' u : C, if u ∈ F then 0 else ‖rightCosetCauchyTerm θ Γ s u z‖
    (∀ K : Set ℂ, IsCompact K →
      TendstoUniformlyOn Tail (fun _ => 0) (atTop : Filter (Finset C)) K) ∧
      TendstoLocallyUniformlyOn
        (fun (F : Finset C) (z : ℂ) => ∑ u ∈ F, rightCosetCauchyTerm θ Γ s u z)
        (LiZhongQC.ahVar ν) (atTop : Filter (Finset C)) Set.univ := by
  classical
  let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup Γ s))
  let ν : ℂ → ℂ := fun ζ => ∑' u : C, rightCosetInfinitesimalZeroExtension θ Γ s u ζ
  let Tail : Finset C → ℂ → ℝ := fun F z =>
    ∑' u : C, if u ∈ F then 0 else ‖rightCosetCauchyTerm θ Γ s u z‖
  let E : Finset C → ℂ → ℝ := fun F z => ∫ ζ : ℂ,
    (∑' u : C, if u ∈ F then 0 else ‖rightCosetInfinitesimalZeroExtension θ Γ s u ζ‖) *
      ‖Quasiconformal.firstVariationKernel z ζ‖
  let k : ℝ := 1 / Real.pi
  have hk : 0 < k := one_div_pos.mpr Real.pi_pos
  have hE := (rightCoset_kernelTail_tendstoUniformlyOn θ Γ s hsep).2
  have hT0 (F : Finset C) (z : ℂ) : 0 ≤ Tail F z := by
    apply tsum_nonneg
    intro u
    by_cases hu : u ∈ F
    · simp only [ite_eq_left hu, le_refl]
    · simpa only [ite_eq_right hu] using norm_nonneg (rightCosetCauchyTerm θ Γ s u z)
  have hT : ∀ K : Set ℂ, IsCompact K →
      TendstoUniformlyOn Tail (fun _ => 0) (atTop : Filter (Finset C)) K := by
    intro K hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have he := (Metric.tendstoUniformlyOn_iff.mp (hE K hK)) (ε / k) (div_pos hε hk)
    filter_upwards [he] with F hF z hz
    have hnear : |E F z| < ε / k := by
      simpa only [Real.dist_eq, zero_sub, abs_neg] using hF z hz
    have hsmall : Tail F z < ε := by
      calc
        _ ≤ k * E F z := rightCoset_integral_tail_le_kernel_tail θ Γ s hsep F z
        _ ≤ k * |E F z| := mul_le_mul_of_nonneg_left (le_abs_self _) hk.le
        _ < k * (ε / k) := mul_lt_mul_of_pos_left hnear hk
        _ = ε := by rw [mul_comm k, div_mul_cancel₀ _ (ne_of_gt hk)]
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hT0 F z)] using hsmall
  refine ⟨hT, ?_⟩
  apply (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_univ).mpr
  intro K _hK hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp (hT K hK)) ε hε] with F hF z hz
  let D := {u : C // u ∉ F}
  have hdata := (rightCosetCauchySeries_hasSum θ Γ s hsep).2.2 z
  have hs : HasSum (fun u : C => rightCosetCauchyTerm θ Γ s u z) (LiZhongQC.ahVar ν z) := hdata.2.2
  have he := hs.summable.sum_add_tsum_subtype_compl F
  rw [hs.tsum_eq] at he
  have hsub : LiZhongQC.ahVar ν z - ∑ u ∈ F, rightCosetCauchyTerm θ Γ s u z =
      ∑' u : D, rightCosetCauchyTerm θ Γ s u.val z := by
    apply sub_eq_iff_eq_add.mpr
    simpa only [add_comm] using he.symm
  have ht : (∑' u : D, ‖rightCosetCauchyTerm θ Γ s u.val z‖) =
      ∑' u : C, if u ∈ F then 0 else ‖rightCosetCauchyTerm θ Γ s u z‖ := by
    change (∑' u : {u : C | u ∉ F}, ‖rightCosetCauchyTerm θ Γ s u.val z‖) = _
    rw [tsum_subtype {u : C | u ∉ F}
      (fun u => ‖rightCosetCauchyTerm θ Γ s u z‖)]
    apply tsum_congr
    intro u
    by_cases hu : u ∈ F
    · simp [Set.indicator, hu]
    · simp [Set.indicator, hu]
  have hbound : dist (LiZhongQC.ahVar ν z) (∑ u ∈ F, rightCosetCauchyTerm θ Γ s u z) ≤ Tail F z := by
    rw [dist_eq_norm, hsub]
    dsimp only [Tail]
    rw [← ht]
    exact norm_tsum_le_tsum_norm (hdata.2.1.subtype (fun u => u ∉ F))
  have hsmall : Tail F z < ε := by
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg (hT0 F z)] using hF z hz
  exact hbound.trans_lt hsmall

/-- The original closed geodesic produces a normalized coordinate in which its
same actual integral series has locally uniform sums and uniform absolute tails. -/
theorem originalClosedGeodesic_exists_normalized_angular_locallyUniform_series
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M) {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (hcircle : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) :
    ∃ (A Q : Deck) (s : ℝ) (hs : 0 < s), A ∈ Γ ∧
      LiZhongQC.Covers M.halfPlaneCover A q.toLoop ∧
      Hyperbolic.realSLMobius (Q * A * Q⁻¹) =
        Hyperbolic.realSLMobius (Fuchsian.hLogDilationSL s) ∧
      let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
      let θ := canonicalBandWidth s hs
      let C := Quotient (QuotientGroup.rightRel (projectiveDilationSubgroup ΓQ s))
      let ν : ℂ → ℂ := fun ζ => ∑' u : C, rightCosetInfinitesimalZeroExtension θ ΓQ s u ζ
      let Tail : Finset C → ℂ → ℝ := fun F z => by
        classical
        exact ∑' u : C, if u ∈ F then 0 else ‖rightCosetCauchyTerm θ ΓQ s u z‖
      (∀ K : Set ℂ, IsCompact K →
        TendstoUniformlyOn Tail (fun _ => 0) (atTop : Filter (Finset C)) K) ∧
        TendstoLocallyUniformlyOn
          (fun (F : Finset C) (z : ℂ) => ∑ u ∈ F, rightCosetCauchyTerm θ ΓQ s u z)
          (LiZhongQC.ahVar ν) (atTop : Filter (Finset C)) Set.univ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.t2Space
  obtain ⟨A, Q, s, hs, hA, hcov, hQA, hsep⟩ :=
    originalClosedGeodesic_exists_normalized_angular_one_support q hp hcircle
  refine ⟨A, Q, s, hs, hA, hcov, hQA, ?_⟩
  let ΓQ := Γ.map (MulAut.conj Q).toMonoidHom
  have hcount : (ΓQ : Set Deck).Countable := by
    rw [Subgroup.coe_map]
    exact (LiZhongQC.h36p_countable (LiZhongQC.utm_x2_isFuchsian hp)).image _
  let : Countable ΓQ := hcount.to_subtype
  exact rightCosetCauchySeries_tendstoLocallyUniformlyOn (canonicalBandWidth s hs) ΓQ s hsep

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
