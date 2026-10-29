module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeInverseBersGermContinuity
public import LowDimensionalTopology.Geometry.Teichmuller.NativeBersFiniteEvaluations
public import LowDimensionalTopology.Geometry.Teichmuller.DeformedCompactUniformization
public import LowDimensionalTopology.Geometry.Teichmuller.BersAutomorphicCompleteness
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.S34mOsgood
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Genuine analyticity of the actual inverse Bers-coordinate germ

The actual Ahlfors-Bers coefficient family gives scalar holomorphy at every
lower-half-plane point. Faithful finite point evaluations give genuine vector
holomorphy along every complex curve. Together with the proved original-norm
continuity, Osgood's theorem now proves full several-variable analyticity of
the independently defined normalized pullback followed by the Bers map.

The final original closed-surface consumer derives both finite dimensions
from actual uniformization: the source uses its existing weighted chart and
the deformed group uses its genuine compact same-genus holomorphic covering.
No finite-dimensionality, analytic dependence, or derivative premise remains.

Osgood's theorem is reused from Wu Xiaobin's LiZhongQC development,
Apache-2.0, fixed upstream commit
`1c0d5473c020b66ed5106331a38a61536760b9b2`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped UpperHalfPlane Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport

open GammaMeasurableBeltrami Surfaces

variable {Γ : Subgroup Deck}

/-- Osgood upgrades the actual coefficient family to full analyticity in the genuine weighted norm. -/
theorem analyticOnNhd_inverseBersGerm
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ)
    [FiniteDimensional ℂ (BersWeighted.Automorphic Γ)]
    [FiniteDimensional ℂ (BersWeighted.Automorphic (deformedGroup hΓ ν))] :
    AnalyticOnNhd ℂ (inverseBersGerm hΓ ν)
      (Metric.ball (0 : BersWeighted.Automorphic (deformedGroup hΓ ν))
        (inverseSectionRadius ν)) := by
  classical
  let : CompleteSpace (BersWeighted.Automorphic Γ) := BersWeighted.automorphic_completeSpace Γ
  let : Module.Free ℂ (BersWeighted.Automorphic (deformedGroup hΓ ν)) :=
    Module.Free.of_divisionRing ℂ (BersWeighted.Automorphic (deformedGroup hΓ ν))
  let e := (Module.finBasis ℂ (BersWeighted.Automorphic (deformedGroup hΓ ν))).equivFunL
  let U := e.symm ⁻¹'
    Metric.ball (0 : BersWeighted.Automorphic (deformedGroup hΓ ν)) (inverseSectionRadius ν)
  have hU : IsOpen U := Metric.isOpen_ball.preimage e.symm.continuous
  have hr : inverseSectionRadius ν < 1 / 2 := by
    unfold inverseSectionRadius
    linarith [norm_nonneg ν.val.val]
  have hcont : ContinuousOn (fun v => inverseBersGerm hΓ ν (e.symm v)) U := by
    apply (continuousOn_inverseBersGerm hΓ ν).comp e.symm.continuous.continuousOn
    intro v hv
    exact mem_ball_zero_iff.mpr ((mem_ball_zero_iff.mp hv).trans hr)
  have hA : AnalyticOnNhd ℂ (fun v => inverseBersGerm hΓ ν (e.symm v)) U := by
    apply LiZhongQC.s34m_osgood hU hcont
    intro v hv i
    let q : ℂ → BersWeighted.Automorphic (deformedGroup hΓ ν) :=
      fun t => e.symm (Function.update v i t)
    let P : Set ℂ := q ⁻¹'
      Metric.ball (0 : BersWeighted.Automorphic (deformedGroup hΓ ν)) (inverseSectionRadius ν)
    have hqc : Continuous q :=
      e.symm.continuous.comp (continuous_const.update i continuous_id)
    have hP : IsOpen P := Metric.isOpen_ball.preimage hqc
    have hvi : v i ∈ P := by
      change e.symm (Function.update v i (v i)) ∈
        Metric.ball (0 : BersWeighted.Automorphic (deformedGroup hΓ ν)) (inverseSectionRadius ν)
      rw [Function.update_eq_self]
      exact hv
    have hq : DifferentiableOn ℂ q P := by
      intro t _
      exact (e.symm.toContinuousLinearMap.differentiableAt.comp t
        (hasDerivAt_update v i t).differentiableAt).differentiableWithinAt
    have hd := inverseBersGerm_curve_differentiableOn hΓ ν hP q hq
      (fun t ht => mem_ball_zero_iff.mp ht)
    exact (hd (v i) hvi).differentiableAt (hP.mem_nhds hvi)
  intro φ hφ
  have hmem : e φ ∈ U := by
    change e.symm (e φ) ∈
      Metric.ball (0 : BersWeighted.Automorphic (deformedGroup hΓ ν)) (inverseSectionRadius ν)
    rw [e.symm_apply_apply]
    exact hφ
  have ha := (hA (e φ) hmem).comp (e.toContinuousLinearMap.analyticAt φ)
  apply ha.congr
  exact Eventually.of_forall fun ψ => by
    simp only [Function.comp_apply, e.symm_apply_apply]

universe u
variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {p : ℍ → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)

include R hp hg hgenus in
/-- Both finite-dimensional spaces arise from the actual compact original and deformed surfaces. -/
theorem analyticOnNhd_inverseBersGerm_of_uniformization
    (hΓ : LiZhongQC.IsFuchsian Γ) (ν : Ball Γ) :
    AnalyticOnNhd ℂ (inverseBersGerm hΓ ν)
      (Metric.ball (0 : BersWeighted.Automorphic (deformedGroup hΓ ν))
        (inverseSectionRadius ν)) := by
  let e := TeichmullerSpace.weightedLinearBersEquiv R hg hgenus
    (canonicalHandleGroupPresentation g) hΓ hp
  let : FiniteDimensional ℂ (BersWeighted.Automorphic Γ) :=
    FiniteDimensional.of_injective e.toLinearMap e.injective
  let : FiniteDimensional ℂ (BersWeighted.Automorphic (deformedGroup hΓ ν)) :=
    deformed_weighted_finiteDimensional R hg hgenus hΓ hp ν
  exact analyticOnNhd_inverseBersGerm hΓ ν

end LowDimensionalTopology.Geometry.Teichmuller.NormalizedCoefficientTransport
