module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.LocallyMinimizingArcs
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.RectifiableC1Compatibility
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.RectifiableSubarcs

/-!
# The original-atlas, all-rectifiable locally minimizing arc contract

This definition uses only the original continuous curve, original atlas,
actual open surface neighborhoods, arc injectivity, and the full intrinsic
rectifiable length of original-surface curves. Covering branches, BV lifts and
supporting lines are derived. All continuous BV competitors are admitted;
native C1 curves enter only as a proved length-preserving subclass.
-/

public section
noncomputable section
open Set Filter
open scoped UpperHalfPlane unitInterval Topology ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- A locally minimizing arc in the original analytic surface. The injectivity
expresses the book's arc convention; it is local and imposes no unit-speed,
Lipschitz or absolute-continuity requirement on the given parameter. -/
@[expose] def IsOriginalLocallyMinimizingArc
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (α : ℝ → X) : Prop :=
  ∃ hα : Continuous α, ∀ x : ℝ, ∃ (U : Set X) (a b : ℝ),
    IsOpen U ∧ α x ∈ U ∧ a < x ∧ x < b ∧
    (∀ t ∈ Ioo a b, α t ∈ U) ∧ InjOn α (Ioo a b) ∧
    ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, ∀ hst : s < t,
      ∃ hrect : R.toRiemannAtlas.IsChartwiseBVOn α (Icc s t),
        ∀ q : RiemannSurfaceRectifiableCurvePiece R,
          (∀ r : I, q.curve r ∈ U) → q.curve 0 = α s → q.curve 1 = α t →
          M.rectifiableCurveLength
            (RiemannSurfaceRectifiableCurvePiece.ofInterval α hα s t hst.le hrect) ≤
              M.rectifiableCurveLength q

/-- The intrinsic definition derives actual covering-coordinate BV and the
native C1 comparison used by the independent minimizing-trace proof. This is
a theorem about the full original-surface definition, rather than a lift field. -/
theorem IsOriginalLocallyMinimizingArc.to_cover_branch
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} {α : ℝ → X}
    (hα : IsOriginalLocallyMinimizingArc M α) :
    IsLocallyRectifiableMinimizingArc M α := by
  obtain ⟨hcont, hlocal⟩ := hα
  refine ⟨hcont, ?_⟩
  intro x
  obtain ⟨U, a, b, hUopen, hxU, hax, hxb, _hαU, hinj, hmin⟩ := hlocal x
  obtain ⟨z, hz⟩ := M.halfPlaneCover_surjective (α x)
  obtain ⟨E₀, hzE₀, hpE₀⟩ := M.halfPlaneCover_covering.isLocalHomeomorph z
  have hVopen : IsOpen (M.halfPlaneCover ⁻¹' U) :=
    hUopen.preimage M.halfPlaneCover_covering.continuous
  let E := E₀.restrOpen (M.halfPlaneCover ⁻¹' U) hVopen
  have hpE : M.halfPlaneCover = E := hpE₀
  have hzE : z ∈ E.source := by
    refine ⟨hzE₀, ?_⟩
    change M.halfPlaneCover z ∈ U
    rw [hz]
    exact hxU
  have hxT : α x ∈ E.target := by
    rw [← hz, hpE]
    exact E.map_source hzE
  have hEsub : E.target ⊆ U := by
    intro y hy
    have hsource := E.map_target hy
    have hyU : M.halfPlaneCover (E.symm y) ∈ U := hsource.2
    rw [hpE, E.right_inv hy] at hyU
    exact hyU
  have hnear : ∀ᶠ t in 𝓝 x, t ∈ Ioo a b ∧ α t ∈ E.target :=
    inter_mem (Ioo_mem_nhds hax hxb)
      (hcont.continuousAt.eventually (E.open_target.mem_nhds hxT))
  obtain ⟨l, u, ⟨hlx, hxu⟩, hsub⟩ := hnear.exists_Ioo_subset
  refine ⟨E, l, u, hpE, hlx, hxu, fun t ht => (hsub ht).2,
    hinj.mono (fun _ ht => (hsub ht).1), ?_⟩
  intro s hs t ht hst
  have hsJ : s ∈ Ioo a b := (hsub hs).1
  have htJ : t ∈ Ioo a b := (hsub ht).1
  obtain ⟨hrect, hminimum⟩ := hmin s hsJ t htJ hst
  have hparam : Icc s t ⊆ Ioo l u := by
    intro v hv
    exact ⟨hs.1.trans_le hv.1, hv.2.trans_lt ht.2⟩
  let f : ℝ → ℍ := fun v => E.symm (α v)
  have hf : ContinuousOn f (Icc s t) :=
    E.symm.continuousOn.comp hcont.continuousOn (fun _ hv => (hsub (hparam hv)).2)
  have hprojection (v : ℝ) (hv : v ∈ Icc s t) : M.halfPlaneCover (f v) = α v := by
    rw [hpE]
    exact E.right_inv (hsub (hparam hv)).2
  have hchart : R.toRiemannAtlas.IsChartwiseBVOn (M.halfPlaneCover ∘ f) (Icc s t) :=
    hrect.congr (fun v hv => (hprojection v hv).symm)
  have hfBV := (M.boundedVariation_iff_chartwiseBV hf).mpr hchart
  have hcoeBV := (halfPlane_boundedVariation_iff_coe_of_continuousOn hf).mp hfBV
  let c : RectifiableCurve :=
    { a := s
      b := t
      ordered := hst.le
      curve := fun v => (f v : ℂ)
      continuous := UpperHalfPlane.continuous_coe.comp_continuousOn hf
      boundedVariation := hcoeBV }
  refine ⟨c, rfl, rfl, fun _ _ => rfl, ?_⟩
  intro q hqU hq0 hq1
  have hcomparison := hminimum q.toRectifiable
    (fun r => hEsub (hqU r)) hq0 hq1
  have hlength := M.rectifiableInterval_length_eq_of_branch α hcont s t hst.le hrect
    c rfl rfl (fun v _ => (f v).im_pos) hprojection
  rw [hlength, q.toRectifiable_length] at hcomparison
  exact hcomparison

/-- Every original-atlas, all-rectifiable locally minimizing arc has an actual
continuous covering lift whose entire range lies in one complete h-line.
The original arbitrary parameter is preserved throughout the conclusion. -/
theorem IsOriginalLocallyMinimizingArc.exists_hLine_lift
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} {α : ℝ → X}
    (hα : IsOriginalLocallyMinimizingArc M α) :
    ∃ (f : C(ℝ, ℍ)) (S : Set ℍ),
      (∀ t : ℝ, M.halfPlaneCover (f t) = α t) ∧ IsHalfPlaneHLine S ∧ range f ⊆ S :=
  hα.to_cover_branch.exists_hLine_lift

end LowDimensionalTopology.Geometry.Surfaces
