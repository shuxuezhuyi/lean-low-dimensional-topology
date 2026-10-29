/-
The partition-integral argument is adapted from Wu Xiaobin's
Li-Zhong-QC-formalization (Copyright 2026), released under Apache-2.0.
See THIRD_PARTY_NOTICES.md for the pinned source and retained license.
-/
module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.HolomorphicQuadraticDifferential
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedUniqueness

/-!
# Quadratic length on a finite subinterval and its actual lift

Every admissible chart partition has the same lifted coefficient integral.
Finite native subinterval length supplies such a partition, so the defining
infimum equals that integral. No smoothness or nonvanishing premise is added.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

/-- Finite native length on the given subinterval is the literal coefficient
integral of its actual lift, including at zeros of the differential. -/
theorem quadraticLengthOn_eq_liftIntegral_of_lt_top
    {X : Type} [TopologicalSpace X] (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    {a b : X} (γ : Path a b) (c : C(unitInterval, UpperHalfPlane)) (s t : ℝ) :
    letI := R.toRiemannAtlas.toChartedSpace
    IsUniformization Γ p → (∀ u, p (c u) = γ u) →
      0 ≤ s → s < t → t ≤ 1 →
      phiLengthOn (q : X → ℂ → ℂ) γ s t < ⊤ →
      phiLengthOn (q : X → ℂ → ℂ) γ s t =
        ∫⁻ u in Ioo s t,
          phiDensity (utm_liftQD (q : X → ℂ → ℂ) p)
              (c (Set.projIcc 0 1 zero_le_one u) : ℂ) *
            ‖deriv (fun v : ℝ => (c (Set.projIcc 0 1 zero_le_one v) : ℂ)) u‖ₑ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp hc _hs _hst _ht hfinite
  let F : ℝ → ℝ≥0∞ := fun u =>
    phiDensity (utm_liftQD (q : X → ℂ → ℂ) p)
        (c (Set.projIcc 0 1 zero_le_one u) : ℂ) *
      ‖deriv (fun v : ℝ => (c (Set.projIcc 0 1 zero_le_one v) : ℂ)) u‖ₑ
  have hsum (n : ℕ) (τ : Fin (n + 1) → ℝ) (x : Fin n → X)
      (h0 : τ 0 = s) (hn : τ (Fin.last n) = t) (hτ : Monotone τ)
      (hsrc : ∀ i : Fin n,
        γ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source) :
      (∑ i : Fin n, ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ),
        phiDensity ((q : X → ℂ → ℂ) (x i)) (chartAt ℂ (x i) (γ.extend u)) *
          ‖deriv (fun v : ℝ => chartAt ℂ (x i) (γ.extend v)) u‖ₑ) =
        ∫⁻ u in Ioo s t, F u := by
    have hE := utm_a_lintegral_sum_eq F n τ hτ
    rw [h0, hn] at hE
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hE
    refine setLIntegral_congr_fun measurableSet_Ioo fun u hu => ?_
    exact utm_a_density_speed q.property hp γ c hc (x i)
      (hsrc i ⟨u, Ioo_subset_Icc_self hu, rfl⟩)
  unfold phiLengthOn at hfinite
  simp only [iInf_lt_iff] at hfinite
  obtain ⟨n, τ, x, hP, _⟩ := hfinite
  change phiLengthOn (q : X → ℂ → ℂ) γ s t = ∫⁻ u in Ioo s t, F u
  apply le_antisymm
  · unfold phiLengthOn
    refine iInf_le_of_le n (iInf_le_of_le τ (iInf_le_of_le x (iInf_le_of_le hP ?_)))
    exact le_of_eq (hsum n τ x hP.1 hP.2.1 hP.2.2.1 fun i => (hP.2.2.2 i).1)
  · unfold phiLengthOn
    refine le_iInf fun m => le_iInf fun σ => le_iInf fun y => le_iInf fun hQ => ?_
    exact le_of_eq (hsum m σ y hQ.1 hQ.2.1 hQ.2.2.1 fun i => (hQ.2.2.2 i).1).symm

end LowDimensionalTopology.Geometry.Teichmuller
