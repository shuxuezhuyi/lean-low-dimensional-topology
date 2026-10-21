module
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.Measure.LocalAngularMeasure
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.DiscOrthogonalActions
public import LowDimensionalTopology.Geometry.Hyperbolic.Convexity.NativeHalfPlaneComponents
public import Mathlib.Tactic
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory
open scoped Complex.UnitDisc UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Hyperbolic

theorem kleinCoordinate_inner_nonnegative (n : ℂ) (z : Complex.UnitDisc) :
    (0 ≤ inner ℝ n (kleinCoordinate z))  ↔ 0 ≤ inner ℝ n (z : ℂ) := by
  have hp : 0<(2/(1+‖(z : ℂ)‖^2) : ℝ):=by positivity
  have he : kleinCoordinate z=(2/(1+‖(z : ℂ)‖^2) : ℝ) • (z : ℂ):=by
    simp [kleinCoordinate,poincareToKlein,kleinFormula,Complex.real_smul]
  rw [he,real_inner_smul_right]
  exact mul_nonneg_iff_of_pos_left hp

/-- A genuine Euclidean half-disc with diameter through zero is hyperbolically convex. -/
theorem discOriginClosedHalfspace_hConvex (n : ℂ) :
    DiscHConvex {z : Complex.UnitDisc | 0 ≤ inner ℝ n (z : ℂ)} := by
  apply (discHConvex_iff_klein_convex _).mpr
  have he : kleinCoordinate '' {z : Complex.UnitDisc | 0 ≤ inner ℝ n (z : ℂ)}=
      {w : ℂ | 0 ≤ inner ℝ n w}∩Metric.ball 0 1 := by
    ext w
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨(kleinCoordinate_inner_nonnegative n z).mpr hz,(by rw [←range_kleinCoordinate];exact mem_range_self z)⟩
    · rintro ⟨hw,hwB⟩
      have hwR : w∈range kleinCoordinate:=by rwa [range_kleinCoordinate]
      obtain ⟨z,rfl⟩:=hwR
      exact ⟨z,(kleinCoordinate_inner_nonnegative n z).mp hw,rfl⟩
  rw [he]
  exact (convex_halfSpace_ge (innerSL ℝ n).toLinearMap.isLinear 0).inter (convex_ball 0 1)

/-- The actual local angle of the standard straight side is pi. -/
theorem discLocalAngle_closedHalfDisc :
    discLocalAngle {z : Complex.UnitDisc | 0 ≤ (z : ℂ).re} 0=Real.pi := by
  have hc : DiscHConvex {z : Complex.UnitDisc | 0 ≤ (z : ℂ).re} := by
    convert discOriginClosedHalfspace_hConvex (1 : ℂ) using 1
    ext z
    simp [Complex.inner]
  rw [discLocalAngle_eq_of_convex hc (by simp)]
  exact discSubtendedAngle_closedHalfDisc

/-- Every genuine diameter half-disc has angle pi, regardless of its actual direction. -/
theorem discLocalAngle_closedLinearHalfspace (n : ℂ) (hn : n≠0) :
    discLocalAngle {z : Complex.UnitDisc | 0 ≤ inner ℝ n (z : ℂ)} 0=Real.pi := by
  let :=discHyperbolicMetric
  have hnR : 0<‖n‖:=norm_pos_iff.mpr hn
  let u : Circle:=⟨n/(‖n‖ : ℂ),by
    change n/(‖n‖ : ℂ)∈Metric.sphere (0 : ℂ) 1
    rw [mem_sphere_zero_iff_norm,norm_div,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos hnR,div_self hnR.ne']⟩
  let L : ℂ≃ₗᵢ[ℝ]ℂ:=rotation u
  let e : Complex.UnitDisc≃ₜComplex.UnitDisc:=(discOrthogonalIsometry L).toHomeomorph
  have hnL : n=‖n‖ • L 1 := by
    change n=‖n‖ • ((n/(‖n‖ : ℂ))*1)
    rw [mul_one,Complex.real_smul,mul_div_cancel₀ n (Complex.ofReal_ne_zero.mpr hnR.ne')]
  have hs (w : ℂ) : (0 ≤ inner ℝ n w) ↔0 ≤ (L.symm w).re := by
    rw [hnL,real_inner_smul_left,L.inner_map_eq_flip]
    simpa [Complex.inner] using (mul_nonneg_iff_of_pos_left hnR :
      (0 ≤ ‖n‖*inner ℝ (1 : ℂ) (L.symm w)) ↔0 ≤ inner ℝ (1 : ℂ) (L.symm w))
  have hset : e '' {z : Complex.UnitDisc | 0 ≤ (z : ℂ).re}=
      {z : Complex.UnitDisc | 0 ≤ inner ℝ n (z : ℂ)} := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      apply (hs _).mpr
      change 0 ≤ (L.symm (L (w : ℂ))).re
      change 0 ≤ (w : ℂ).re at hw
      simpa only [L.symm_apply_apply] using hw
    · intro hz
      refine ⟨e.symm z,?_,e.apply_symm_apply z⟩
      change 0 ≤ (L.symm (z : ℂ)).re
      exact (hs _).mp hz
  have h0 : e 0=0:=discOrthogonalMap_zero L
  have he:=discLocalAngle_isometry e (discOrthogonalIsometry L).isometry
    {z : Complex.UnitDisc | 0 ≤ (z : ℂ).re} 0
  rw [hset,h0] at he
  exact he.trans discLocalAngle_closedHalfDisc

theorem disc_support_isOpenMap {n : ℂ} (hn : n≠0) :
    IsOpenMap (fun z : Complex.UnitDisc=>inner ℝ n (kleinCoordinate z)) := by
  let f : ℂ→L[ℝ]ℝ:=innerSL ℝ n
  have hs : Function.Surjective f := by
    intro r
    refine ⟨(r/‖n‖^2) • n,?_⟩
    change inner ℝ n ((r/‖n‖^2) • n)=r
    rw [inner_smul_right,real_inner_self_eq_norm_sq]
    exact div_mul_cancel₀ r (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))
  exact (f.isOpenMap hs).comp isOpenEmbedding_kleinCoordinate.isOpenMap

theorem disc_support_cut_closure {n : ℂ} (hn : n≠0) (t : ℝ) :
    closure {z : Complex.UnitDisc | inner ℝ n (kleinCoordinate z)<t}=
      {z : Complex.UnitDisc | inner ℝ n (kleinCoordinate z) ≤ t} := by
  have hc : Continuous (fun z : Complex.UnitDisc=>inner ℝ n (kleinCoordinate z)):=
    continuous_const.inner continuous_kleinCoordinate
  have he:=(disc_support_isOpenMap hn).preimage_closure_eq_closure_preimage hc (Iio t)
  rw [closure_Iio] at he
  exact he.symm

/-- At its genuine boundary origin, an actual closed geodesic half-plane is a literal
Euclidean diameter half-disc. The normal and its orientation are derived from the component. -/
theorem closedDiscHalfPlane_at_origin (L : DiscLine) (u : Complex.UnitDisc)
    (hu : u∉L.carrier) (h0 : (0 : Complex.UnitDisc)∈L.carrier) :
    ∃n : ℂ,n≠0 ∧closedDiscHalfPlane L u={z : Complex.UnitDisc | 0 ≤ inner ℝ n (z : ℂ)} := by
  obtain ⟨n,t,hn,hLine⟩:=L.exists_klein_linear_equation
  have ht : t=0 := by
    have he:=(hLine 0).mp h0
    simpa [kleinCoordinate,poincareToKlein,kleinFormula] using he.symm
  subst t
  have hne : inner ℝ n (kleinCoordinate u)≠0:=fun h=>hu ((hLine u).mpr h)
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine ⟨-n,neg_ne_zero.mpr hn,?_⟩
    rw [closedDiscHalfPlane,connectedComponentIn_discLine_lt L n 0 hLine u hneg]
    change closure {z : Complex.UnitDisc | inner ℝ n (kleinCoordinate z)<0}=_
    rw [disc_support_cut_closure hn]
    ext z
    change (inner ℝ n (kleinCoordinate z) ≤ 0) ↔0 ≤ inner ℝ (-n) (z : ℂ)
    rw [←kleinCoordinate_inner_nonnegative (-n) z]
    simp only [inner_neg_left,neg_nonneg]
  · refine ⟨n,hn,?_⟩
    rw [closedDiscHalfPlane,connectedComponentIn_discLine_gt L n 0 hLine u hpos]
    have he : discKleinCutGt n 0={z : Complex.UnitDisc | inner ℝ (-n) (kleinCoordinate z)<0} := by
      ext z
      simp only [discKleinCutGt,mem_ofPred_eq,inner_neg_left,neg_lt_zero]
    rw [he,disc_support_cut_closure (neg_ne_zero.mpr hn)]
    ext z
    change (inner ℝ (-n) (kleinCoordinate z) ≤ 0) ↔0 ≤ inner ℝ n (z : ℂ)
    rw [←kleinCoordinate_inner_nonnegative n z]
    simp only [inner_neg_left,neg_nonpos]

/-- The original local angle at any diameter half-plane's actual boundary origin is pi. -/
theorem discLocalAngle_closedDiscHalfPlane_origin (L : DiscLine) (u : Complex.UnitDisc)
    (hu : u∉L.carrier) (h0 : (0 : Complex.UnitDisc)∈L.carrier) :
    discLocalAngle (closedDiscHalfPlane L u) 0=Real.pi := by
  obtain ⟨n,hn,he⟩:=closedDiscHalfPlane_at_origin L u hu h0
  rw [he]
  exact discLocalAngle_closedLinearHalfspace n hn

end LowDimensionalTopology.Geometry.Hyperbolic
