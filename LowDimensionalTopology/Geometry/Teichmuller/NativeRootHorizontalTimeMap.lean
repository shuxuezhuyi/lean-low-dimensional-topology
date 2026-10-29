module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeMaximalHorizontalTrajectory

/-!
# Natural time maps oriented by an actual global quadratic root

The time maps use the full complement of the critical-trajectory set. Their
curves are maximal unit trajectories with positive root velocity at time zero.
An action law, measurability and area preservation are separate properties.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

/-- An actual holomorphic Abelian differential whose square is the same q. -/
def IsGlobalQuadraticRoot
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (β : X → ℂ → ℂ) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  IsDiffFamily 1 0 β ∧
    (∀ x, DifferentiableOn ℂ (β x) (chartAt ℂ x).target) ∧
    ∀ x z, β x z ^ 2 = (q : X → ℂ → ℂ) x z

/-- Unit positive velocity for the original Abelian root in the actual chart. -/
def IsRootHorizontalAt
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (β : X → ℂ → ℂ) (c : ℝ → X) (t : ℝ) : Prop :=
  letI := R.toRiemannAtlas.toChartedSpace
  ContinuousAt c t ∧ ∃ v : ℂ,
    HasDerivAt (fun s => chartAt ℂ (c t) (c s)) v t ∧
      β (c t) (chartAt ℂ (c t) (c t)) * v = 1

/-- Evaluate the actual bi-infinite trajectory with the root's initial sign. -/
noncomputable def nativeRootHorizontalTimeMap
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (β : X → ℂ → ℂ) :
    letI := R.toRiemannAtlas.toChartedSpace
    ℝ → {p : X // p ∉ s26v_E (q : X → ℂ → ℂ)} →
      {p : X // p ∉ s26v_E (q : X → ℂ → ℂ)} := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  intro t p
  let c := s26v_traj (q : X → ℂ → ℂ) (p : X)
  let d : ℂ := deriv (fun s => chartAt ℂ (p : X) (c s)) 0
  exact if β (p : X) (chartAt ℂ (p : X) (p : X)) * d = 1 then
    ⟨c t, s26v_a_not_mem_E (s26v_traj_spec p.property).1 t⟩
  else
    ⟨c (-t), s26v_a_not_mem_E (s26v_traj_spec p.property).1 (-t)⟩

/-- Each concrete time curve is maximal and has the root's positive initial
velocity. The critical set removed here includes critical trajectories. -/
theorem nativeRootHorizontalTimeMap_trajectory
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (β : X → ℂ → ℂ) (hβ : IsGlobalQuadraticRoot R q β) :
    letI := R.toRiemannAtlas.toChartedSpace
    ∀ p : {p : X // p ∉ s26v_E (q : X → ℂ → ℂ)},
      IsMaximalHorizontalTrajectory R q (p : X) Set.univ
        (fun t => (nativeRootHorizontalTimeMap R q β t p : X)) ∧
      IsRootHorizontalAt R β
        (fun t => (nativeRootHorizontalTimeMap R q β t p : X)) 0 := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  intro p
  let c := s26v_traj (q : X → ℂ → ℂ) (p : X)
  let d : ℂ := deriv (fun s => chartAt ℂ (p : X) (c s)) 0
  have hc : s26v_IsTraj (q : X → ℂ → ℂ) c ∧ c 0 = (p : X) :=
    s26v_traj_spec p.property
  have hc0 : c 0 = (p : X) := hc.2
  obtain ⟨_, v, hv, hqv⟩ := hc.1 0
  rw [hc0] at hv hqv
  have hd : d = v := hv.deriv
  have hsign : (β (p : X) (chartAt ℂ (p : X) (p : X)) * d) ^ 2 = 1 := by
    rw [mul_pow, hβ.2.2 (p : X) (chartAt ℂ (p : X) (p : X)), hd]
    exact hqv
  have hmaximal (c' : ℝ → X) (h0 : c' 0 = (p : X))
      (hT : ∀ t, s26v_IsTrajAt (q : X → ℂ → ℂ) c' t) :
      IsMaximalHorizontalTrajectory R q (p : X) Set.univ c' := by
    refine ⟨isOpen_univ, convex_univ, mem_univ 0, h0, fun t _ => hT t, ?_⟩
    intro J' _ _ _ _ _ _
    exact subset_univ J'
  by_cases hdir : β (p : X) (chartAt ℂ (p : X) (p : X)) * d = 1
  · have hdir' : β (p : X) (chartAt ℂ (p : X) (p : X)) *
        deriv (fun s => chartAt ℂ (p : X) (s26v_traj (q : X → ℂ → ℂ) (p : X) s)) 0 = 1 := by
      simpa only [c, d] using hdir
    have hcurve : (fun t => (nativeRootHorizontalTimeMap R q β t p : X)) = c := by
      funext t
      simp only [nativeRootHorizontalTimeMap, ite_eq_left hdir', c]
    rw [hcurve]
    refine ⟨hmaximal c hc0 hc.1, ?_⟩
    change ContinuousAt c 0 ∧ ∃ w : ℂ,
      HasDerivAt (fun s => chartAt ℂ (c 0) (c s)) w 0 ∧
        β (c 0) (chartAt ℂ (c 0) (c 0)) * w = 1
    rw [hc0]
    refine ⟨c.continuous.continuousAt, v, hv, ?_⟩
    simpa only [hd] using hdir
  · have hdir' : β (p : X) (chartAt ℂ (p : X) (p : X)) *
        deriv (fun s => chartAt ℂ (p : X) (s26v_traj (q : X → ℂ → ℂ) (p : X) s)) 0 ≠ 1 := by
      simpa only [c, d] using hdir
    have hcurve : (fun t => (nativeRootHorizontalTimeMap R q β t p : X)) =
        fun t => c (-t) := by
      funext t
      simp only [nativeRootHorizontalTimeMap, ite_eq_right hdir', c]
    have hminus : β (p : X) (chartAt ℂ (p : X) (p : X)) * v = -1 := by
      simpa only [hd] using (sq_eq_one_iff.mp hsign).resolve_left hdir
    have hvneg : HasDerivAt (fun s => chartAt ℂ (p : X) (c (-s))) (-v) 0 := by
      have h := HasDerivAt.scomp_of_eq (0 : ℝ) hv (hasDerivAt_neg (0 : ℝ))
        (by simp only [neg_zero])
      simpa [Function.comp_def] using h
    have hneg0 : c (-(0 : ℝ)) = (p : X) := by simpa only [neg_zero] using hc0
    rw [hcurve]
    refine ⟨hmaximal (fun t => c (-t)) hneg0
      (fun t => s26v_trajAt_neg (hc.1 (-t))), ?_⟩
    change ContinuousAt (fun t => c (-t)) 0 ∧ ∃ w : ℂ,
      HasDerivAt (fun s => chartAt ℂ (c (-0)) (c (-s))) w 0 ∧
        β (c (-0)) (chartAt ℂ (c (-0)) (c (-0))) * w = 1
    rw [hneg0]
    refine ⟨(c.continuous.comp continuous_neg).continuousAt, -v, hvneg, ?_⟩
    rw [mul_neg, hminus, neg_neg]

end LowDimensionalTopology.Geometry.Teichmuller
