module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.LocallyMinimizingArcTrace
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.LocalTrace

/-!
# Complete line lifts from actual locally minimizing surface arcs

The local data use genuine open patches of the original covering, actual
rectifiable coordinate curves and the original native surface C1 length.
Arc injectivity is local data, not an assumption on arbitrary nontrivial loops.
No global lift or axis is included in the definition: ordinary covering lifting
constructs the continuous lift, and its complete line is proved from local arc
traces and connected propagation.

This is an explicit branch formulation of local minimality. Equivalence with
an independent original-atlas chartwise BV definition remains a separate
interface; it is not silently inserted as a structure field.
-/

public section
noncomputable section
open Set Filter
open scoped UpperHalfPlane unitInterval Topology MatrixGroups ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- Every point has an actual open covering patch in which the curve is an arc
and every compact subarc is rectifiable and minimizing for the original native
surface length. The covering coordinates and minimizing inequalities are local. -/
@[expose] def IsLocallyRectifiableMinimizingArc
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (α : ℝ → X) : Prop :=
  Continuous α ∧ ∀ x : ℝ, ∃ (E : OpenPartialHomeomorph ℍ X) (a b : ℝ),
    M.halfPlaneCover = E ∧ a < x ∧ x < b ∧
    (∀ t ∈ Ioo a b, α t ∈ E.target) ∧ InjOn α (Ioo a b) ∧
    ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, s < t →
      ∃ c : RectifiableCurve, c.a = s ∧ c.b = t ∧
        (∀ u ∈ Icc s t, c.curve u = (E.symm (α u) : ℂ)) ∧
        ∀ q : HyperbolicSurfaceC1CurvePiece M,
          (∀ r : I, q.curve r ∈ E.target) → q.curve 0 = α s → q.curve 1 = α t →
          c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) ≤ ENNReal.ofReal q.length

private theorem branch_hLine_germ_of_minimizing_arcs
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) {α : ℝ → X} (hα : Continuous α)
    (E : OpenPartialHomeomorph ℍ X) (hpE : M.halfPlaneCover = E)
    {a b x : ℝ} (hax : a < x) (hxb : x < b)
    (hU : ∀ t ∈ Ioo a b, α t ∈ E.target) (hinj : InjOn α (Ioo a b))
    (hmin : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, s < t →
      ∃ c : RectifiableCurve, c.a = s ∧ c.b = t ∧
        (∀ u ∈ Icc s t, c.curve u = (E.symm (α u) : ℂ)) ∧
        ∀ q : HyperbolicSurfaceC1CurvePiece M,
          (∀ r : I, q.curve r ∈ E.target) → q.curve 0 = α s → q.curve 1 = α t →
          c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) ≤ ENNReal.ofReal q.length) :
    ∃ S : Set ℍ, IsHalfPlaneHLine S ∧ ∀ᶠ t in 𝓝 x, E.symm (α t) ∈ S := by
  let g : ℝ → ℍ := fun t => E.symm (α t)
  have hpg (t : ℝ) (ht : t ∈ Ioo a b) : M.halfPlaneCover (g t) = α t := by
    rw [hpE]
    exact E.right_inv (hU t ht)
  have hxsource : g x ∈ E.source := E.map_target (hU x ⟨hax, hxb⟩)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (E.open_source.mem_nhds hxsource)
  let r : ℝ := ε / 4
  have hr : 0 < r := by dsimp only [r]; positivity
  have hpatch : Metric.ball (g x) (3 * r) ⊆ E.source := by
    intro z hz
    apply hεsub
    apply Metric.mem_ball.mpr
    have hz' := Metric.mem_ball.mp hz
    dsimp only [r] at hz'
    linarith
  have hgc : ContinuousAt g x := (E.symm.continuousAt (hU x ⟨hax, hxb⟩)).comp hα.continuousAt
  have hnear : ∀ᶠ t in 𝓝 x, t ∈ Ioo a b ∧ g t ∈ Metric.ball (g x) r :=
    inter_mem (Ioo_mem_nhds hax hxb) (hgc.eventually (Metric.ball_mem_nhds (g x) hr))
  obtain ⟨l, u, ⟨hlx, hxu⟩, hsub⟩ := hnear.exists_Ioo_subset
  let s : ℝ := (l + x) / 2
  let t : ℝ := (x + u) / 2
  have hlsx : l < s ∧ s < x := by dsimp only [s]; constructor <;> linarith
  have hxtu : x < t ∧ t < u := by dsimp only [t]; constructor <;> linarith
  have hsI : s ∈ Ioo l u := ⟨hlsx.1, hlsx.2.trans hxu⟩
  have htI : t ∈ Ioo l u := ⟨hlx.trans hxtu.1, hxtu.2⟩
  have hsJ : s ∈ Ioo a b := (hsub hsI).1
  have htJ : t ∈ Ioo a b := (hsub htI).1
  have hst : s < t := hlsx.2.trans hxtu.1
  have hne : g s ≠ g t := by
    intro he
    have he' : α s = α t := (hpg s hsJ).symm.trans
      ((congrArg M.halfPlaneCover he).trans (hpg t htJ))
    exact hst.ne (hinj hsJ htJ he')
  obtain ⟨c, ha, hb, hpoint, hcmin⟩ := hmin s hsJ t htJ hst
  have hc : c.IsPathIn LiZhongQC.upperHalf (g s) (g t) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [ha]
      exact hpoint s (left_mem_Icc.mpr hst.le)
    · rw [hb]
      exact hpoint t (right_mem_Icc.mpr hst.le)
    · rintro _ ⟨v, hv, rfl⟩
      have hv' : v ∈ Icc s t := by simpa only [ha, hb] using hv
      rw [hpoint v hv']
      exact (g v).im_pos
  have hcminimum : ∀ q : HyperbolicSurfaceC1CurvePiece M,
      (∀ v : I, q.curve v ∈ E.target) →
      q.curve 0 = M.halfPlaneCover (g s) → q.curve 1 = M.halfPlaneCover (g t) →
      c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) ≤ ENNReal.ofReal q.length := by
    intro q hq hq0 hq1
    exact hcmin q hq (hq0.trans (hpg s hsJ)) (hq1.trans (hpg t htJ))
  have htrace := M.rectifiable_minimizing_arc_trace_in_cover_patch E hpE (g x) hpatch
    (hsub hsI).2 (hsub htI).2 hne c hc hcminimum
  obtain ⟨L, hLs, hLt⟩ := exists_halfPlaneLine_through (g s) (g t) hne
  have hsegment : closedHSegment (g s) (g t) ⊆ L.carrier := by
    intro z hz
    obtain ⟨γ, hγ, p, q, _hpq, hp, hq, v, _hv, hvz⟩ := hz
    have hrange : range γ = L.carrier := isHLine_eq_of_two_points hγ.2 L.isHLine hne
      (hp ▸ mem_range_self p) (hq ▸ mem_range_self q) hLs hLt
    exact hrange ▸ (hvz ▸ mem_range_self v)
  refine ⟨L.carrier, L.isHLine, ?_⟩
  filter_upwards [Icc_mem_nhds hlsx.2 hxtu.1] with v hv
  have hv' : v ∈ Icc c.a c.b := by simpa only [ha, hb] using hv
  have hmem : (g v : ℂ) ∈ c.curve '' Icc c.a c.b := ⟨v, hv', hpoint v hv⟩
  rw [htrace] at hmem
  obtain ⟨z, hz, hzg⟩ := hmem
  have hzg' : z = g v := UpperHalfPlane.ext hzg
  change g v ∈ L.carrier
  rw [← hzg']
  exact hsegment hz

/-- Actual local minimizing arc data on the original surface construct a
continuous lift on one complete hyperbolic line. Neither the lift nor the line
is assumed; arbitrary original arc parameters are preserved. -/
theorem IsLocallyRectifiableMinimizingArc.exists_hLine_lift
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} {α : ℝ → X}
    (hα : IsLocallyRectifiableMinimizingArc M α) :
    ∃ (f : C(ℝ, ℍ)) (S : Set ℍ),
      (∀ t : ℝ, M.halfPlaneCover (f t) = α t) ∧ IsHalfPlaneHLine S ∧ range f ⊆ S := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, _hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨z, hz⟩ := hp.2.2.1 (α 0)
  obtain ⟨f, ⟨_hf0, hpf⟩, _hfu⟩ :=
    hp.1.existsUnique_continuousMap_lifts ⟨α, hα.1⟩ 0 z hz
  have hproj (t : ℝ) : M.halfPlaneCover (f t) = α t := congrFun hpf t
  have hfinj : IsLocallyInjective (f : ℝ → ℍ) := by
    intro x
    obtain ⟨E, a, b, _hpE, hax, hxb, _hU, hinj, _hmin⟩ := hα.2 x
    refine ⟨Ioo a b, isOpen_Ioo, ⟨hax, hxb⟩, ?_⟩
    intro s hs t ht he
    apply hinj hs ht
    exact (hproj s).symm.trans ((congrArg M.halfPlaneCover he).trans (hproj t))
  have hloc : ∀ x : ℝ, ∃ S : Set ℍ,
      IsHalfPlaneHLine S ∧ ∀ᶠ t in 𝓝 x, f t ∈ S := by
    intro x
    obtain ⟨E, a, b, hpE, hax, hxb, hU, hinj, hmin⟩ := hα.2 x
    obtain ⟨S, hS, hnearS⟩ :=
      branch_hLine_germ_of_minimizing_arcs M hα.1 E hpE hax hxb hU hinj hmin
    let g : ℝ → ℍ := fun t => E.symm (α t)
    have hpg (t : ℝ) (ht : t ∈ Ioo a b) : M.halfPlaneCover (g t) = α t := by
      rw [hpE]
      exact E.right_inv (hU t ht)
    obtain ⟨A, hA, hAx⟩ := (hp.2.2.2 (g x) (f x)).1
      ((hpg x ⟨hax, hxb⟩).trans (hproj x).symm)
    have hgc : ContinuousAt g x :=
      (E.symm.continuousAt (hU x ⟨hax, hxb⟩)).comp hα.1.continuousAt
    obtain ⟨V, hVopen, hxV, hVinj⟩ := hp.1.isLocalHomeomorph.isLocallyInjective (f x)
    have hfV : ∀ᶠ t in 𝓝 x, f t ∈ V :=
      f.continuous.continuousAt.eventually (hVopen.mem_nhds hxV)
    have hAgV : ∀ᶠ t in 𝓝 x, A • g t ∈ V :=
      ((continuous_const_smul A).continuousAt.comp hgc).eventually
        (hVopen.mem_nhds (by
          change A • g x ∈ V
          rw [hAx]
          exact hxV))
    have heq : f =ᶠ[𝓝 x] (fun t => A • g t) := by
      filter_upwards [hfV, hAgV, Ioo_mem_nhds hax hxb] with t hft hAgt ht
      apply hVinj hft hAgt
      rw [hproj, LiZhongQC.s30a_p_smul hp hA, hpg t ht]
    obtain ⟨L, hL⟩ := exists_halfPlaneLine_of_isHLine hS
    obtain ⟨N, hN⟩ := LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine
      (show Isometry (fun y : ℍ => A • y) from isometry_smul ℍ A) L
    refine ⟨N.carrier, N.isHLine, ?_⟩
    filter_upwards [heq, hnearS] with t ht hSt
    rw [ht, ← hN]
    exact ⟨g t, hL.symm ▸ hSt, rfl⟩
  obtain ⟨S, hS, hfS⟩ := exists_hLine_containing_range_of_locally_geodesic_arcs hfinj hloc
  exact ⟨f, S, hproj, hS, hfS⟩

end LowDimensionalTopology.Geometry.Surfaces
