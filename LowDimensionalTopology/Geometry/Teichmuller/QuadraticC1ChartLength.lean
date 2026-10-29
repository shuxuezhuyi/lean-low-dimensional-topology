module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.HolomorphicQuadraticDifferential
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedUniqueness
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Quadratic length on a finite C1 chart subdivision

The curve and quadratic coefficient family remain the original ones. Compact
closed parameter intervals turn actual C1 chart pieces into admissible Lipschitz
pieces. Chart invariance then identifies the existing path length with their
literal finite sum of integrals, including pieces through zeros.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal NNReal Topology Manifold ContDiff UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

universe u
variable {S : Type u} [TopologicalSpace S] [ChartedSpace ℂ S]

/-- A given finite C1 subdivision meets the actual existing length definition's
Lipschitz-partition predicate, with the same times, charts and curve. -/
theorem c1_chartSubdivision_admissible {a b : S} (γ : Path a b)
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (x : Fin n → S)
    (h0 : τ 0 = 0) (hn : τ (Fin.last n) = 1) (hτ : Monotone τ)
    (hsrc : ∀ i : Fin n,
      γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source)
    (hC1 : ∀ i : Fin n, ContDiffOn ℝ 1 (fun v : ℝ => chartAt ℂ (x i) (γ.extend v))
      (Icc (τ i.castSucc) (τ i.succ))) :
    τ 0 = 0 ∧ τ (Fin.last n) = 1 ∧ Monotone τ ∧
      ∀ i : Fin n,
        γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source ∧
          ∃ K : ℝ≥0, LipschitzOnWith K (fun v : ℝ => chartAt ℂ (x i) (γ.extend v))
            (Icc (τ i.castSucc) (τ i.succ)) := by
  refine ⟨h0, hn, hτ, fun i => ⟨hsrc i, ?_⟩⟩
  exact (hC1 i).exists_lipschitzOnWith one_ne_zero (convex_Icc _ _) isCompact_Icc

private theorem chart_partition_integral_eq [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) {a b : S} (γ : Path a b)
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (x : Fin n → S) (hτ : Monotone τ)
    (hsrc : ∀ i : Fin n,
      γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source) :
    (∑ i : Fin n, ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ),
      phiDensity (q (x i)) (chartAt ℂ (x i) (γ.extend u)) *
        ‖deriv (fun v : ℝ => chartAt ℂ (x i) (γ.extend v)) u‖ₑ) =
      ∫⁻ u in Ioo (τ 0) (τ (Fin.last n)),
        phiDensity (q (γ.extend u)) (chartAt ℂ (γ.extend u) (γ.extend u)) *
          ‖deriv (fun v : ℝ => chartAt ℂ (γ.extend u) (γ.extend v)) u‖ₑ := by
  rw [← utm_a_lintegral_sum_eq _ n τ hτ]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  exact s26n_density_speed_chart hq (x i) (γ.extend u) γ.continuous_extend.continuousAt
    (hsrc i ⟨u, Ioo_subset_Icc_self hu, rfl⟩) (mem_chart_source ℂ (γ.extend u))

/-- The existing intrinsic path length is the literal finite C1 chart-integral
sum. No nonvanishing, distance or minimizing-path assumption is used. -/
theorem phiLengthPath_eq_c1_chartSubdivision [IsManifold 𝓘(ℂ) ω S]
    {q : S → ℂ → ℂ} (hq : IsHolQuadDiff q) {a b : S} (γ : Path a b)
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (x : Fin n → S)
    (h0 : τ 0 = 0) (hn : τ (Fin.last n) = 1) (hτ : Monotone τ)
    (hsrc : ∀ i : Fin n,
      γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source)
    (hC1 : ∀ i : Fin n, ContDiffOn ℝ 1 (fun v : ℝ => chartAt ℂ (x i) (γ.extend v))
      (Icc (τ i.castSucc) (τ i.succ))) :
    phiLengthPath q γ =
      ∑ i : Fin n, ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ),
        phiDensity (q (x i)) (chartAt ℂ (x i) (γ.extend u)) *
          ‖deriv (fun v : ℝ => chartAt ℂ (x i) (γ.extend v)) u‖ₑ := by
  have hadm := c1_chartSubdivision_admissible γ τ x h0 hn hτ hsrc hC1
  apply le_antisymm
  · unfold phiLengthPath phiLengthOn
    exact iInf_le_of_le n (iInf_le_of_le τ (iInf_le_of_le x (iInf_le _ hadm)))
  · unfold phiLengthPath phiLengthOn
    refine le_iInf fun m => le_iInf fun σ => le_iInf fun y => le_iInf fun h => ?_
    have he := chart_partition_integral_eq hq γ τ x hτ hsrc
    have he' := chart_partition_integral_eq hq γ σ y h.2.2.1 (fun i => (h.2.2.2 i).1)
    rw [h0, hn] at he
    rw [h.1, h.2.1] at he'
    exact le_of_eq (he.trans he'.symm)

/-- The same formula for a native quadratic differential in the actual atlas of
the original arbitrary Riemann surface. -/
theorem quadraticLengthPath_eq_c1_chartSubdivision
    {X : Type u} [TopologicalSpace X] (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) {a b : X} (γ : Path a b)
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (x : Fin n → X) :
    letI := R.toRiemannAtlas.toChartedSpace
    τ 0 = 0 → τ (Fin.last n) = 1 → Monotone τ →
      (∀ i : Fin n,
        γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source) →
      (∀ i : Fin n, ContDiffOn ℝ 1 (fun v : ℝ => chartAt ℂ (x i) (γ.extend v))
        (Icc (τ i.castSucc) (τ i.succ))) →
      phiLengthPath (q : X → ℂ → ℂ) γ =
        ∑ i : Fin n, ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ),
          phiDensity ((q : X → ℂ → ℂ) (x i)) (chartAt ℂ (x i) (γ.extend u)) *
            ‖deriv (fun v : ℝ => chartAt ℂ (x i) (γ.extend v)) u‖ₑ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro h0 hn hτ hsrc hC1
  exact phiLengthPath_eq_c1_chartSubdivision q.property γ τ x h0 hn hτ hsrc hC1

/-- The same original length is the literal upstairs integral of the actual
pullback quadratic differential along the supplied lift. -/
theorem quadraticLengthPath_eq_liftIntegral_of_c1_chartSubdivision
    {X : Type u} [TopologicalSpace X] (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : ℍ → X}
    {a b : X} (γ : Path a b) (γ' : C(unitInterval, ℍ))
    {n : ℕ} (τ : Fin (n + 1) → ℝ) (x : Fin n → X) :
    letI := R.toRiemannAtlas.toChartedSpace
    IsUniformization Γ p → (∀ t, p (γ' t) = γ t) →
      τ 0 = 0 → τ (Fin.last n) = 1 → Monotone τ →
      (∀ i : Fin n,
        γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source) →
      (∀ i : Fin n, ContDiffOn ℝ 1 (fun v : ℝ => chartAt ℂ (x i) (γ.extend v))
        (Icc (τ i.castSucc) (τ i.succ))) →
      phiLengthPath (q : X → ℂ → ℂ) γ =
        ∫⁻ u in Ioo (0 : ℝ) 1,
          phiDensity (utm_liftQD (q : X → ℂ → ℂ) p)
              (γ' (Set.projIcc 0 1 zero_le_one u) : ℂ) *
            ‖deriv (fun v : ℝ => (γ' (Set.projIcc 0 1 zero_le_one v) : ℂ)) u‖ₑ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp hγ' h0 hn hτ hsrc hC1
  rw [phiLengthPath_eq_c1_chartSubdivision q.property γ τ x h0 hn hτ hsrc hC1]
  have he := utm_a_lintegral_sum_eq (fun u =>
    phiDensity (utm_liftQD (q : X → ℂ → ℂ) p)
        (γ' (Set.projIcc 0 1 zero_le_one u) : ℂ) *
      ‖deriv (fun v : ℝ => (γ' (Set.projIcc 0 1 zero_le_one v) : ℂ)) u‖ₑ) n τ hτ
  rw [h0, hn] at he
  refine Eq.trans ?_ he
  refine Finset.sum_congr rfl fun i _ => ?_
  refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
  exact utm_a_density_speed q.property hp γ γ' hγ' (x i)
    (hsrc i ⟨u, Ioo_subset_Icc_self hu, rfl⟩)

end LowDimensionalTopology.Geometry.Teichmuller
