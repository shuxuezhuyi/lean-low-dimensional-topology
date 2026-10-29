module

public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticUpperHalfDistance

/-!
# Native interval length of the actual lifted differential

Every preferred chart of the native upper half-plane is its original complex
coordinate. All admissible partitions therefore give the same coefficient
integral, and the supplied Lipschitz interval gives an actual partition witness.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

/-- The native interval length of the actual lifted differential is its original
coefficient integral on every supplied Lipschitz interval, including at zeros. -/
theorem liftedQuadraticLengthOn_eq_integral_of_lipschitz
    {X : Type} [TopologicalSpace X] (R : RiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ (a b : UpperHalfPlane) (δ : Path a b) (s t : ℝ),
        0 ≤ s → s < t → t ≤ 1 →
        (∃ K : ℝ≥0, LipschitzOnWith K (fun u : ℝ => (δ.extend u : ℂ)) (Icc s t)) →
        phiLengthOn (qH : UpperHalfPlane → ℂ → ℂ) δ s t =
          ∫⁻ u in Ioo s t, phiDensity (utm_liftQD (q : X → ℂ → ℂ) p) (δ.extend u : ℂ) *
            ‖deriv (fun v : ℝ => (δ.extend v : ℂ)) u‖ₑ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b δ s t _hs hst _ht hLip
  obtain ⟨K, hK⟩ := hLip
  let F : ℝ → ℝ≥0∞ := fun u =>
    phiDensity ψ (δ.extend u : ℂ) * ‖deriv (fun v : ℝ => (δ.extend v : ℂ)) u‖ₑ
  have hchart (x : UpperHalfPlane) : chartAt ℂ x = UpperHalfPlane.ofComplex.symm := by
    have hx := chart_mem_atlas ℂ x
    change chartAt ℂ x ∈ ({UpperHalfPlane.ofComplex.symm} :
      Set (OpenPartialHomeomorph UpperHalfPlane ℂ)) at hx
    exact Set.mem_singleton_iff.mp hx
  have hcoord (x : UpperHalfPlane) :
      (fun v : ℝ => chartAt ℂ x (δ.extend v)) = (fun v : ℝ => (δ.extend v : ℂ)) := by
    funext v
    rw [hchart x]
    rfl
  have hdensity (x : UpperHalfPlane) (u : ℝ) :
      phiDensity ((qH : UpperHalfPlane → ℂ → ℂ) x) (chartAt ℂ x (δ.extend u)) =
        phiDensity ψ (δ.extend u : ℂ) := by
    rw [hchart x]
    change phiDensity (upperHalf.indicator ψ) (δ.extend u : ℂ) = _
    have hz : (δ.extend u : ℂ) ∈ upperHalf := (δ.extend u).im_pos
    simp only [phiDensity]
    rw [Set.indicator_of_mem hz]
  have hsum (n : ℕ) (τ : Fin (n + 1) → ℝ) (x : Fin n → UpperHalfPlane)
      (h0 : τ 0 = s) (hn : τ (Fin.last n) = t) (hτ : Monotone τ) :
      (∑ i : Fin n, ∫⁻ u in Ioo (τ i.castSucc) (τ i.succ),
        phiDensity ((qH : UpperHalfPlane → ℂ → ℂ) (x i)) (chartAt ℂ (x i) (δ.extend u)) *
          ‖deriv (fun v : ℝ => chartAt ℂ (x i) (δ.extend v)) u‖ₑ) =
        ∫⁻ u in Ioo s t, F u := by
    have hE := utm_a_lintegral_sum_eq F n τ hτ
    rw [h0, hn] at hE
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hE
    refine setLIntegral_congr_fun measurableSet_Ioo fun u _ => ?_
    rw [hcoord (x i), hdensity (x i) u]
  let τ : Fin 2 → ℝ := ![s, t]
  let x : Fin 1 → UpperHalfPlane := fun _ => a
  have hτ : Monotone τ := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [τ, hst.le]
  have hP : τ 0 = s ∧ τ (Fin.last 1) = t ∧ Monotone τ ∧
      ∀ i : Fin 1,
        δ.extend '' Icc (τ i.castSucc) (τ i.succ) ⊆ (chartAt ℂ (x i)).source ∧
          ∃ K : ℝ≥0, LipschitzOnWith K (fun v : ℝ => chartAt ℂ (x i) (δ.extend v))
            (Icc (τ i.castSucc) (τ i.succ)) := by
    refine ⟨rfl, rfl, hτ, fun i => ⟨?_, K, ?_⟩⟩
    · intro z _
      rw [hchart (x i)]
      change z ∈ (univ : Set UpperHalfPlane)
      trivial
    · rw [hcoord (x i)]
      fin_cases i
      exact hK
  change phiLengthOn (qH : UpperHalfPlane → ℂ → ℂ) δ s t = ∫⁻ u in Ioo s t, F u
  apply le_antisymm
  · unfold phiLengthOn
    refine iInf_le_of_le 1 (iInf_le_of_le τ (iInf_le_of_le x (iInf_le_of_le hP ?_)))
    exact (hsum 1 τ x rfl rfl hτ).le
  · unfold phiLengthOn
    refine le_iInf fun m => le_iInf fun σ => le_iInf fun y => le_iInf fun hQ => ?_
    exact (hsum m σ y hQ.1 hQ.2.1 hQ.2.2.1).symm.le

end LowDimensionalTopology.Geometry.Teichmuller
