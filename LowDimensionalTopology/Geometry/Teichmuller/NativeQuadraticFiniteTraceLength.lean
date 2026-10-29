module

public import LowDimensionalTopology.Unproved.Teichmuller.QuadraticSmoothCarrierInputs
public import LowDimensionalTopology.Geometry.Teichmuller.NativeLiftedQuadraticIntervalLength
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticProjectionDistance

/-!
# Weighted length of finite native paths with the same trace

The actual monotone clocks may have plateaus. The existing weighted
absolutely-continuous substitution proof uses the original two path functions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Manifold

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC LowDimensionalTopology.Unproved.Teichmuller

private theorem native_length_eq_reparam_of_lipschitz
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (α κ : Path a b) (σ : unitInterval → unitInterval)
        (hσ : Continuous σ) (hσ0 : σ 0 = 0) (hσ1 : σ 1 = 1),
        Monotone σ → α = κ.reparam σ hσ hσ0 hσ1 →
        (∃ K : NNReal, LipschitzOnWith K (fun u : ℝ => (α.extend u : ℂ)) (Icc 0 1)) →
        (∃ K : NNReal, LipschitzOnWith K (fun u : ℝ => (κ.extend u : ℂ)) (Icc 0 1)) →
        phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) α =
          phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) κ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b α κ σ hσ hσ0 hσ1 hmono hEq hαLip hκLip
  obtain ⟨Kα, hKα⟩ := hαLip
  obtain ⟨Kκ, hKκ⟩ := hκLip
  let F : ℝ → ℂ := fun u => (κ.extend u : ℂ)
  let T : ℝ → ℝ := fun u => (σ (projIcc 0 1 zero_le_one u) : ℝ)
  have hT : Monotone T ∧ Continuous T := s26v_b_reparam_real σ hσ hmono
  have hT0 : T 0 = 0 := by
    dsimp only [T]
    rw [projIcc_of_mem zero_le_one (show (0 : ℝ) ∈ Icc 0 1 from ⟨le_rfl, zero_le_one⟩)]
    change (σ (0 : unitInterval) : ℝ) = 0
    exact congrArg (fun v : unitInterval => (v : ℝ)) hσ0
  have hT1 : T 1 = 1 := by
    dsimp only [T]
    rw [projIcc_of_mem zero_le_one (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)]
    change (σ (1 : unitInterval) : ℝ) = 1
    exact congrArg (fun v : unitInterval => (v : ℝ)) hσ1
  have hG : (fun u : ℝ => (α.extend u : ℂ)) = F ∘ T := by
    funext u
    change (α.extend u : ℂ) =
      (κ.extend (σ (projIcc 0 1 zero_le_one u) : ℝ) : ℂ)
    rw [hEq, s26v_b_reparam_extend]
  have hFA : AbsolutelyContinuousOnInterval F 0 1 :=
    (show LipschitzOnWith Kκ F (uIcc (0 : ℝ) 1) by
      simpa only [uIcc_of_le zero_le_one, F] using hKκ).absolutelyContinuousOnInterval
  have hGA : AbsolutelyContinuousOnInterval (F ∘ T) 0 1 := by
    rw [← hG]
    exact (show LipschitzOnWith Kα (fun u : ℝ => (α.extend u : ℂ))
      (uIcc (0 : ℝ) 1) by
        simpa only [uIcc_of_le zero_le_one] using hKα).absolutelyContinuousOnInterval
  let g : ℝ → ENNReal := fun u => phiDensity ψ (F u)
  have hFc : Continuous F := UpperHalfPlane.continuous_coe.comp κ.continuous_extend
  have hψF : Continuous (fun u => ψ (F u)) :=
    (utm_liftQD_differentiableOn q.property hp).continuousOn.comp_continuous hFc
      (fun u => (κ.extend u).im_pos)
  have hg : Measurable g := by
    have hgc : Continuous g := ENNReal.continuous_ofReal.comp
      (Real.continuous_sqrt.comp hψF.norm)
    exact hgc.measurable
  have hweighted := s26v_b_reparam_lintegral (α := 0) (β := 1) zero_le_one hT.1 hT.2
    (by simpa only [hT0, hT1] using hFA) hGA hg
  rw [hT0, hT1] at hweighted
  have hpoint : ∀ u, F (T u) = (α.extend u : ℂ) :=
    fun u => (congrFun hG u).symm
  have hintegral :
      (∫⁻ u in Ioo (0 : ℝ) 1, phiDensity ψ (α.extend u : ℂ) *
        ‖deriv (fun v : ℝ => (α.extend v : ℂ)) u‖ₑ) =
      ∫⁻ u in Ioo (0 : ℝ) 1, phiDensity ψ (F u) * ‖deriv F u‖ₑ := by
    simpa only [g, hpoint, ← hG] using hweighted
  have hlenα := liftedQuadraticLengthOn_eq_integral_of_lipschitz R.toRiemannSurface q hp
    a b α 0 1 le_rfl zero_lt_one le_rfl ⟨Kα, hKα⟩
  have hlenκ := liftedQuadraticLengthOn_eq_integral_of_lipschitz R.toRiemannSurface q hp
    a b κ 0 1 le_rfl zero_lt_one le_rfl ⟨Kκ, hKκ⟩
  change phiLengthOn (qH : UpperHalfPlane → ℂ → ℂ) α 0 1 =
    phiLengthOn (qH : UpperHalfPlane → ℂ → ℂ) κ 0 1
  rw [hlenα, hlenκ]
  simpa only [F] using hintegral

/-- Finite actual same-trace paths have equal weighted lengths through their
common monotone arc and their own Lipschitz parametrizations. -/
theorem native_finite_sameTrace_length_eq_of_common_arc
    (hArc : NativeCommonMonotoneArc)
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (α β : Path a b), a ≠ b →
        phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) α < ⊤ →
        phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) β < ⊤ →
        NativePathHasIntervalFibers α → NativePathHasIntervalFibers β →
        Set.range α = Set.range β →
        phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) α =
          phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) β := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
    (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b α β hab hαFinite hβFinite hαFib hβFib htrace
  have hαLip := nativeH_lipschitz_of_length_lt_top (qH : UpperHalfPlane → ℂ → ℂ) α
    hαFinite
  have hβLip := nativeH_lipschitz_of_length_lt_top (qH : UpperHalfPlane → ℂ → ℂ) β
    hβFinite
  obtain ⟨κ, K, σ, τ, hσ, hσ0, hσ1, hτ, hτ0, hτ1, _, hK, hσm, hτm, hαEq, hβEq⟩ :=
    hArc α β hab hαLip hβLip hαFib hβFib htrace
  have hακ := native_length_eq_reparam_of_lipschitz R q hp α κ σ hσ hσ0 hσ1
    hσm hαEq hαLip ⟨K, hK⟩
  have hβκ := native_length_eq_reparam_of_lipschitz R q hp β κ τ hτ hτ0 hτ1
    hτm hβEq hβLip ⟨K, hK⟩
  exact hακ.trans hβκ.symm

end LowDimensionalTopology.Geometry.Teichmuller
