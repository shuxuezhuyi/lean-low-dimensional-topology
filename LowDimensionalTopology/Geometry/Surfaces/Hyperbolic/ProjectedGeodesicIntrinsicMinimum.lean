module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.IntrinsicLocallyMinimizingArcs
public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.RectifiableLiftBounds

/-!
# Actual projected geodesics satisfy the original all-rectifiable arc minimum

A genuine complete unit-speed half-plane geodesic may be traversed with any
positive affine scale. Original-atlas rectifiability of each subarc is derived
from its native C1 representative; exact full-BV length agrees with native C1
length. Every original-atlas rectifiable competitor admits a continuous local
branch, which is proved BV and obeys the actual endpoint-distance bound.
The input parameter is never substituted into a derivative formula.
-/

public section
noncomputable section
open Set Filter
open scoped UpperHalfPlane unitInterval Topology ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

private theorem chartwiseBV_of_actual_affine_curve
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {α : ℝ → X} {a b : ℝ} (hab : a < b)
    (q : RiemannSurfaceRectifiableCurvePiece R)
    (hpoint : ∀ r : I, q.curve r = α (a + (b - a) * (r : ℝ))) :
    R.toRiemannAtlas.IsChartwiseBVOn α (Icc a b) := by
  let reparam : ℝ → ℝ := fun t => (t - a) / (b - a)
  have hden : 0 < b - a := sub_pos.mpr hab
  have hmap : MapsTo reparam (Icc a b) (Icc 0 1) := by
    intro t ht
    refine ⟨div_nonneg (sub_nonneg.mpr ht.1) hden.le, ?_⟩
    apply (div_le_one hden).mpr
    linarith [ht.2]
  have hm : Monotone reparam := by
    intro s t hst
    exact div_le_div_of_nonneg_right (sub_le_sub_right hst a) hden.le
  have hBV := q.rectifiable.comp_monotone reparam (by fun_prop) (hm.monotoneOn (Icc a b)) hmap
  apply hBV.congr
  intro t ht
  have hσt := hmap ht
  change q.curve (projIcc 0 1 zero_le_one (reparam t)) = α t
  rw [projIcc_of_mem zero_le_one hσt, hpoint ⟨reparam t, hσt⟩]
  apply congrArg α
  dsimp only [reparam]
  field_simp [hden.ne']
  ring

/-- Every actual complete geodesic, projected to the original surface with a
positive affine parameter, satisfies the genuine original-atlas local ARC
minimum against every original rectifiable competitor. -/
theorem HyperbolicSurfaceModel.original_locallyMinimizingArc_projected_affine_geodesic
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ)
    (c k : ℝ) (hk : 0 < k) :
    IsOriginalLocallyMinimizingArc M (fun t => M.halfPlaneCover (γ (c + k * t))) := by
  let α : ℝ → X := fun t => M.halfPlaneCover (γ (c + k * t))
  have hcont : Continuous α :=
    M.halfPlaneCover_covering.continuous.comp (hγ.1.continuous.comp (by fun_prop))
  refine ⟨hcont, ?_⟩
  intro x
  obtain ⟨E, hxE, hpE⟩ := M.halfPlaneCover_covering.isLocalHomeomorph (γ (c + k * x))
  have hsource : ∀ᶠ t in 𝓝 x, γ (c + k * t) ∈ E.source :=
    (hγ.1.continuous.comp (show Continuous (fun t : ℝ => c + k * t) from by fun_prop)).continuousAt.eventually
      (E.open_source.mem_nhds hxE)
  obtain ⟨a, b, ⟨hax, hxb⟩, hsub⟩ := hsource.exists_Ioo_subset
  have hU (t : ℝ) (ht : t ∈ Ioo a b) : α t ∈ E.target := by
    change M.halfPlaneCover (γ (c + k * t)) ∈ E.target
    rw [hpE]
    exact E.map_source (hsub ht)
  have hinj : InjOn α (Ioo a b) := by
    intro s hs t ht he
    have hγeq : γ (c + k * s) = γ (c + k * t) := E.injOn (hsub hs) (hsub ht) (by
      simpa only [α, hpE] using he)
    have heq := hγ.1.injective hγeq
    exact mul_left_cancel₀ hk.ne' (add_left_cancel heq)
  refine ⟨E.target, a, b, E.open_target, hU x ⟨hax, hxb⟩, hax, hxb, hU, hinj, ?_⟩
  intro s hs t ht hst
  have hord : c + k * s ≤ c + k * t := by
    have hmul := mul_le_mul_of_nonneg_left hst.le hk.le
    linarith
  obtain ⟨q, hqpoint, hqlen⟩ := M.exists_projected_geodesic_c1_piece hγ
    (c + k * s) (c + k * t) hord
  have hqα (r : I) : q.curve r = α (s + (t - s) * (r : ℝ)) := by
    rw [hqpoint]
    change M.halfPlaneCover (γ (c + k * s + (c + k * t - (c + k * s)) * (r : ℝ))) =
      M.halfPlaneCover (γ (c + k * (s + (t - s) * (r : ℝ))))
    congr 2
    ring
  have hrect := chartwiseBV_of_actual_affine_curve hst q.toRectifiable hqα
  refine ⟨hrect, ?_⟩
  intro v hvU hv0 hv1
  let e : C(I, ℍ) := ⟨fun r => E.symm (v.curve r),
    E.symm.continuousOn.comp_continuous v.curve.continuous hvU⟩
  have he (r : I) : M.halfPlaneCover (e r) = v.curve r := by
    rw [hpE]
    exact E.right_inv (hvU r)
  have he0 : e 0 = γ (c + k * s) := by
    change E.symm (v.curve 0) = γ (c + k * s)
    rw [hv0]
    change E.symm (M.halfPlaneCover (γ (c + k * s))) = _
    rw [hpE, E.left_inv (hsub hs)]
  have he1 : e 1 = γ (c + k * t) := by
    change E.symm (v.curve 1) = γ (c + k * t)
    rw [hv1]
    change E.symm (M.halfPlaneCover (γ (c + k * t))) = _
    rw [hpE, E.left_inv (hsub ht)]
  have hbound := M.dist_le_rectifiable_length_of_continuous_lift v e he
  rw [he0, he1, hγ.1.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hord), neg_sub] at hbound
  have hlen := M.rectifiableCurveLength_congr
    (RiemannSurfaceRectifiableCurvePiece.ofInterval α hcont s t hst.le hrect)
    q.toRectifiable (fun r => (hqα r).symm)
  rw [q.toRectifiable_length, hqlen] at hlen
  rw [hlen]
  exact hbound

end LowDimensionalTopology.Geometry.Surfaces
