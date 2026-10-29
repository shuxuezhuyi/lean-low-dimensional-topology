module

public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.C1Subpieces
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.LocalLifting
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.RectifiableDistance

/-!
# Local minimizing lengths on the original hyperbolic surface

The existing surface C1 length is compared with the actual hyperbolic distance
in any continuous covering lift. A locally projected unit-speed geodesic then
has actual native C1 subpieces of the expected literal length, and those
subpieces minimize among all native C1 competitors in a genuine open surface
patch. A separate comparison includes every continuous BV competitor in the
same covering branch, using its full weighted arclength.

The original surface, topology, cover and native curve-length definition are
retained. No global quotient metric or local isometry instance is assumed.
-/

public section
noncomputable section
open Set Filter
open scoped UpperHalfPlane unitInterval Topology MatrixGroups ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic

/-- The literal native surface length dominates endpoint distance in every
actual continuous half-plane lift, without a regularity premise on that lift. -/
theorem HyperbolicSurfaceModel.dist_le_c1_length_of_continuous_lift
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) (q : HyperbolicSurfaceC1CurvePiece M)
    (e : C(I, ℍ)) (he : ∀ t : I, M.halfPlaneCover (e t) = q.curve t) :
    dist (e 0) (e 1) ≤ q.length := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, _hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  let d := q.toQuotient.lift
  have ha : d.toHalfPlane.a = 0 := q.toQuotient.lift_spec.1
  have hb : d.toHalfPlane.b = 1 := q.toQuotient.lift_spec.2.1
  let f : C(I, ℍ) := ⟨fun t => d.toHalfPlane.curve t,
    d.toHalfPlane.continuous_curve.comp_continuous continuous_subtype_val
      (fun t => by simpa only [ha, hb] using t.property)⟩
  have hf (t : I) : M.halfPlaneCover (f t) = q.curve t := by
    change M.discCover (discFiniteHomeomorph.symm
      (halfPlaneToDisc (discToHalfPlane (d.curve t)))) = q.curve t
    rw [halfPlaneToDisc_discToHalfPlane]
    change M.homeomorph.symm (discQuotientProjection M.invariant (d.curve t)) = q.curve t
    rw [q.toQuotient.lift_spec.2.2 t]
    exact M.homeomorph.symm_apply_apply _
  obtain ⟨A, hA, hA0⟩ := (hp.2.2.2 (f 0) (e 0)).1 ((hf 0).trans (he 0).symm)
  have hwhole : (fun t : I => A • f t) = e := by
    apply hp.1.eq_of_comp_eq ((continuous_const_smul A).comp f.continuous)
      e.continuous ?_ 0 hA0
    funext t
    simp only [Function.comp_apply]
    rw [LiZhongQC.s30a_p_smul hp hA, hf, he]
  have hdist : dist (e 0) (e 1) = dist (f 0) (f 1) := by
    rw [← congrFun hwhole 0, ← congrFun hwhole 1, dist_smul]
  have hbound : dist (f 0) (f 1) ≤ d.toHalfPlane.length := by
    change dist (d.toHalfPlane.curve ((0 : I) : ℝ))
      (d.toHalfPlane.curve ((1 : I) : ℝ)) ≤ d.toHalfPlane.length
    simpa only [ha, hb, Set.Icc.coe_zero, Set.Icc.coe_one] using d.toHalfPlane.dist_le_length
  calc
    dist (e 0) (e 1) = dist (f 0) (f 1) := hdist
    _ ≤ d.toHalfPlane.length := hbound
    _ = q.length := d.toHalfPlane_length

/-- Every actual unit-speed geodesic interval projects to a native C1 curve on
the same original surface, with its full pointwise parameter and literal length. -/
theorem HyperbolicSurfaceModel.exists_projected_geodesic_c1_piece
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ q : HyperbolicSurfaceC1CurvePiece M,
      (∀ t : I, q.curve t = M.halfPlaneCover (γ (a + (b - a) * (t : ℝ)))) ∧
      q.length = b - a := by
  obtain ⟨c, ha, hb, hpoint, hlen⟩ := hγ.exists_c1_affine_piece a b hab
  let q := M.projectDiscC1Piece c.toDisc ha hb
  refine ⟨q, ?_, ?_⟩
  · intro t
    change M.halfPlaneCover (c.curve t) = M.halfPlaneCover (γ (a + (b - a) * (t : ℝ)))
    rw [hpoint]
  · exact (M.projectDiscC1Piece_length c.toDisc ha hb).trans (c.toDisc_length.trans hlen)

/-- Genuine projected unit-speed germs are locally minimizing for the
original surface's native C1 hyperbolic length. The entire competitor curve
stays in an actual open surface patch; its lift is not an input hypothesis. -/
theorem HyperbolicSurfaceModel.locally_minimizing_c1_of_projected_unit_geodesic
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) {α : ℝ → X}
    (hα : IsLocallyProjectedUnitGeodesic M.halfPlaneCover α) (x : ℝ) :
    ∃ (U : Set X) (a b : ℝ), IsOpen U ∧ α x ∈ U ∧ a < x ∧ x < b ∧
      ∀ s t : ℝ, a < s → s ≤ t → t < b →
        ∃ q : HyperbolicSurfaceC1CurvePiece M,
          (∀ r : I, q.curve r = α (s + (t - s) * (r : ℝ))) ∧
          (∀ r : I, q.curve r ∈ U) ∧ q.length = t - s ∧
          ∀ v : HyperbolicSurfaceC1CurvePiece M,
            (∀ r : I, v.curve r ∈ U) → v.curve 0 = α s → v.curve 1 = α t →
            q.length ≤ v.length := by
  obtain ⟨γ, hγ, hlocal⟩ := hα x
  obtain ⟨E, hxE, hpE⟩ := M.halfPlaneCover_covering.isLocalHomeomorph (γ x)
  have hsource : ∀ᶠ t in 𝓝 x, γ t ∈ E.source :=
    hγ.1.continuous.continuousAt.eventually (E.open_source.mem_nhds hxE)
  obtain ⟨a, b, ⟨hax, hxb⟩, hsub⟩ := (hsource.and hlocal).exists_Ioo_subset
  have hlocal' (t : ℝ) (ht : t ∈ Ioo a b) : α t = M.halfPlaneCover (γ t) := (hsub ht).2
  have hsource' (t : ℝ) (ht : t ∈ Ioo a b) : γ t ∈ E.source := (hsub ht).1
  have hxU : α x ∈ E.target := by
    rw [hlocal' x ⟨hax, hxb⟩, hpE]
    exact E.map_source hxE
  refine ⟨E.target, a, b, E.open_target, hxU, hax, hxb, ?_⟩
  intro s t has hst htb
  have hsJ : s ∈ Ioo a b := ⟨has, hst.trans_lt htb⟩
  have htJ : t ∈ Ioo a b := ⟨has.trans_le hst, htb⟩
  obtain ⟨q, hqpoint, hqlen⟩ := M.exists_projected_geodesic_c1_piece hγ s t hst
  have hparamJ (r : I) : s + (t - s) * (r : ℝ) ∈ Ioo a b := by
    have hlo : 0 ≤ (t - s) * (r : ℝ) := mul_nonneg (sub_nonneg.mpr hst) r.property.1
    have hhi : (t - s) * (r : ℝ) ≤ t - s :=
      mul_le_of_le_one_right (sub_nonneg.mpr hst) r.property.2
    constructor <;> linarith
  refine ⟨q, fun r => (hqpoint r).trans (hlocal' _ (hparamJ r)).symm, ?_, hqlen, ?_⟩
  · intro r
    rw [hqpoint r, hpE]
    exact E.map_source (hsource' _ (hparamJ r))
  · intro v hvU hv0 hv1
    let e : C(I, ℍ) := ⟨fun r => E.symm (v.curve r),
      E.symm.continuousOn.comp_continuous v.curve.continuous hvU⟩
    have he (r : I) : M.halfPlaneCover (e r) = v.curve r := by
      rw [hpE]
      exact E.right_inv (hvU r)
    have he0 : e 0 = γ s := by
      change E.symm (v.curve 0) = γ s
      rw [hv0, hlocal' s hsJ, hpE, E.left_inv (hsource' s hsJ)]
    have he1 : e 1 = γ t := by
      change E.symm (v.curve 1) = γ t
      rw [hv1, hlocal' t htJ, hpE, E.left_inv (hsource' t htJ)]
    have hbound := M.dist_le_c1_length_of_continuous_lift v e he
    rw [he0, he1, hγ.1.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)] at hbound
    rw [hqlen]
    linarith

/-- The branch comparison also quantifies over every actual continuous BV
competitor, including singular parametrizations, with the full literal
Poincaré arclength integral. -/
theorem HyperbolicSurfaceModel.geodesic_interval_le_rectifiable_branch_length
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    (M : HyperbolicSurfaceModel R) {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ)
    (E : OpenPartialHomeomorph ℍ X) (hpE : M.halfPlaneCover = E)
    {s t : ℝ} (hst : s ≤ t) (hs : γ s ∈ E.source) (ht : γ t ∈ E.source)
    (c : RectifiableCurve)
    (hbranch : ∀ r ∈ Icc c.a c.b, ∃ z : ℍ, z ∈ E.source ∧ c.curve r = (z : ℂ))
    (h0 : ∀ hz : 0 < (c.curve c.a).im,
      M.halfPlaneCover ⟨c.curve c.a, hz⟩ = M.halfPlaneCover (γ s))
    (h1 : ∀ hz : 0 < (c.curve c.b).im,
      M.halfPlaneCover ⟨c.curve c.b, hz⟩ = M.halfPlaneCover (γ t)) :
    ENNReal.ofReal (t - s) ≤
      c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) := by
  have hpos (r : ℝ) (hr : r ∈ Icc c.a c.b) : 0 < (c.curve r).im := by
    obtain ⟨z, _hz, heq⟩ := hbranch r hr
    rw [heq]
    exact z.im_pos
  let z : ℍ := ⟨c.curve c.a, hpos c.a (left_mem_Icc.mpr c.ordered)⟩
  let w : ℍ := ⟨c.curve c.b, hpos c.b (right_mem_Icc.mpr c.ordered)⟩
  have hzE : z ∈ E.source := by
    obtain ⟨v, hv, heq⟩ := hbranch c.a (left_mem_Icc.mpr c.ordered)
    have hzv : z = v := UpperHalfPlane.ext heq
    exact hzv.symm ▸ hv
  have hwE : w ∈ E.source := by
    obtain ⟨v, hv, heq⟩ := hbranch c.b (right_mem_Icc.mpr c.ordered)
    have hwv : w = v := UpperHalfPlane.ext heq
    exact hwv.symm ▸ hv
  have hzs : z = γ s := E.injOn hzE hs (by rw [← hpE]; exact h0 _)
  have hwt : w = γ t := E.injOn hwE ht (by rw [← hpE]; exact h1 _)
  have hc : c.IsPathIn LiZhongQC.upperHalf z w := by
    refine ⟨rfl, rfl, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    exact hpos r hr
  calc
    ENNReal.ofReal (t - s) = ENNReal.ofReal (dist z w) := by
      rw [hzs, hwt, hγ.1.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hst)]
      congr 1
      ring
    _ = rectifiableMetricDist LiZhongQC.upperHalf
        (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) z w := (halfPlane_rectifiable_distance z w).symm
    _ ≤ c.weightedLength (fun ζ : ℂ => ENNReal.ofReal (1 / ζ.im)) := iInf₂_le c hc

end LowDimensionalTopology.Geometry.Surfaces
