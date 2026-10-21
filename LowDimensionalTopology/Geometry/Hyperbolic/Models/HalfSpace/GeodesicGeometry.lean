module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfSpace.PathMetric
@[expose] public section
noncomputable section
open Set
open scoped OnePoint RealInnerProductSpace UpperHalfPlane MatrixGroups
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic

/-- Two squared distances to distinct real anchors determine a real point. -/
theorem real_eq_of_two_sq_dist (a b x y : ℝ) (hab : a ≠ b)
    (ha : (a - x) ^ 2 = (a - y) ^ 2) (hb : (b - x) ^ 2 = (b - y) ^ 2) : x = y := by
  have hmul : (a - b) * (x - y) = 0 := by nlinarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hab))

/-- Every distance-preserving self-map of the real line is onto. -/
theorem real_isometry_surjective (f : ℝ → ℝ) (hf : Isometry f) : Function.Surjective f := by
  have hab : f 0 ≠ f 1 := hf.injective.ne (by norm_num)
  have hd : (f 1 - f 0) ^ 2 = 1 := by
    have h := congrArg (fun r : ℝ => r ^ 2) (hf.dist_eq 1 0)
    simpa only [Real.dist_eq, sq_abs, sub_zero, one_pow] using h
  have hcases : f 1 = f 0 + 1 ∨ f 1 = f 0 - 1 := by
    have he : (f 1 - f 0 - 1) * (f 1 - f 0 + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp he with he | he
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  intro y
  have hsq (a t : ℝ) : (f a - f t) ^ 2 = (a - t) ^ 2 := by
    have h := congrArg (fun r : ℝ => r ^ (2 : ℕ)) (hf.dist_eq a t)
    rw [Real.dist_eq, Real.dist_eq] at h
    simpa only [sq_abs] using h
  rcases hcases with hp | hm
  · refine ⟨y - f 0, real_eq_of_two_sq_dist (f 0) (f 1) _ y hab ?_ ?_⟩
    · rw [hsq]
      ring
    · rw [hsq, hp]
      ring
  · refine ⟨f 0 - y, real_eq_of_two_sq_dist (f 0) (f 1) _ y hab ?_ ?_⟩
    · rw [hsq]
      ring
    · rw [hsq, hm]
      ring

/-- The horizontal part is linear on differences. -/
theorem halfSpaceHorizontalPart_sub {n : ℕ} (x y : Inversive.Euclidean (n + 1)) :
    halfSpaceHorizontalPart (x - y) = halfSpaceHorizontalPart x - halfSpaceHorizontalPart y := by
  simp only [halfSpaceHorizontalPart, map_sub, sub_smul]
  module

/-- Coordinates of a point of a native vertical two-plane. -/
theorem halfSpaceHorizontalPart_planeEmbed {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (hu0 : halfSpaceHeight n u = 0) (z : ℂ) :
    halfSpaceHorizontalPart (halfSpacePlaneEmbed x u z) =
      halfSpaceHorizontalPart x + z.re • u := by
  rw [halfSpaceHorizontalPart, halfSpacePlaneEmbed_height x u hu0]
  simp only [halfSpacePlaneEmbed, halfSpacePlaneEmbedCLM, twoPlaneEmbedCLM_apply]
  module

/-- Squared Euclidean distance from a boundary centre splits into horizontal and height squares. -/
theorem halfSpace_norm_sub_boundary_sq {n : ℕ} (x c : Inversive.Euclidean (n + 1))
    (hc : halfSpaceHeight n c = 0) :
    ‖x - c‖ ^ 2 = ‖halfSpaceHorizontalPart x - c‖ ^ 2 + (halfSpaceHeight n x) ^ 2 := by
  have he : x - c = (halfSpaceHorizontalPart x - c) +
      halfSpaceHeight n x • halfSpaceVerticalUnit n := by
    simp only [halfSpaceHorizontalPart]
    module
  have hi : inner ℝ (halfSpaceHorizontalPart x - c) (halfSpaceVerticalUnit n) = 0 := by
    rw [inner_halfSpaceVerticalUnit, map_sub, halfSpaceHeight_horizontalPart, hc, sub_self]
  rw [he, norm_add_sq_real, inner_smul_right, hi, mul_zero,
    norm_smul, halfSpaceVerticalUnit_norm, mul_one, Real.norm_eq_abs, sq_abs]
  ring

/-- A perpendicular Euclidean semicircle cannot contain distinct positive points with the same horizontal part. -/
theorem halfSpace_circle_same_horizontal_eq {n : ℕ}
    (p q : HyperbolicHalfSpace n) (c : Inversive.Euclidean (n + 1)) (hc : halfSpaceHeight n c = 0)
    (hh : halfSpaceHorizontalPart p.val = halfSpaceHorizontalPart q.val)
    (hr : ‖p.val - c‖ = ‖q.val - c‖) : p = q := by
  have hs := congrArg (fun r : ℝ => r ^ 2) hr
  rw [halfSpace_norm_sub_boundary_sq p.val c hc,
    halfSpace_norm_sub_boundary_sq q.val c hc, hh] at hs
  have hp : 0 < halfSpaceHeight n p.val := p.property
  have hq : 0 < halfSpaceHeight n q.val := q.property
  have he : halfSpaceHeight n p.val = halfSpaceHeight n q.val := by nlinarith
  apply Subtype.ext
  have h := hh
  simp only [halfSpaceHorizontalPart, he] at h
  exact sub_left_inj.mp h

/-- A native geodesic line through two distinct points with equal horizontal parts is their vertical line. -/
theorem halfSpace_geodesicLine_same_horizontal {n : ℕ}
    {L : Set (HyperbolicHalfSpace n)} (hL : IsHalfSpaceGeodesicLine n L)
    (p q : HyperbolicHalfSpace n) (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q)
    (hh : halfSpaceHorizontalPart p.val = halfSpaceHorizontalPart q.val) :
    L = {r | halfSpaceHorizontalPart r.val = halfSpaceHorizontalPart p.val} := by
  rcases hL with ⟨v, _, rfl⟩ | ⟨x, u, _, hu0, c, r, _, rfl⟩
  · change halfSpaceHorizontalPart p.val = v at hp
    rw [hp]
  · exact False.elim (hpq (halfSpace_circle_same_horizontal_eq p q _
      (by rw [halfSpacePlaneEmbed_height x u hu0]; exact Complex.ofReal_im c) hh
      (hp.2.trans hq.2.symm)))

/-- Any three points of a complete metric geodesic lie on one genuine native geodesic line. -/
theorem halfSpace_metric_geodesic_three_points {n : ℕ} (hn : 1 ≤ n)
    (γ : ℝ → HyperbolicHalfSpace n)
    (hγ : ∀ s t, halfSpacePathDist (γ s) (γ t) = dist s t) (a b c : ℝ) :
    ∃ L : Set (HyperbolicHalfSpace n), IsHalfSpaceGeodesicLine n L ∧
      γ a ∈ L ∧ γ b ∈ L ∧ γ c ∈ L := by
  let s := min a (min b c)
  let t := max a (max b c)
  obtain ⟨Γ, u, v, _, hΓ, _, _, hinterval⟩ := exists_halfSpace_geodesic_geometry hn (γ s) (γ t)
  have hmem (r : ℝ) (hsr : s ≤ r) (hrt : r ≤ t) : γ r ∈ Set.range Γ := by
    have heq : halfSpacePathDist (γ s) (γ r) + halfSpacePathDist (γ r) (γ t) =
        halfSpacePathDist (γ s) (γ t) := by
      rw [hγ, hγ, hγ]
      exact (halfPlane_real_triangle_eq_iff_uIcc s t r).mpr (Set.mem_uIcc_of_le hsr hrt)
    obtain ⟨w, _, hw⟩ := (hinterval (γ r)).mp heq
    exact ⟨w, hw⟩
  refine ⟨Set.range Γ, hΓ, hmem a ?_ ?_, hmem b ?_ ?_, hmem c ?_ ?_⟩
  · exact min_le_left _ _
  · exact le_max_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- All horizontal displacements on a native geodesic line are multiples of any nonzero horizontal chord. -/
theorem halfSpace_geodesicLine_horizontal_chord {n : ℕ}
    {L : Set (HyperbolicHalfSpace n)} (hL : IsHalfSpaceGeodesicLine n L)
    (p q r : HyperbolicHalfSpace n) (hp : p ∈ L) (hq : q ∈ L) (hr : r ∈ L)
    (hh : halfSpaceHorizontalPart p.val ≠ halfSpaceHorizontalPart q.val) :
    ∃ t : ℝ, halfSpaceHorizontalPart r.val - halfSpaceHorizontalPart p.val =
      t • (halfSpaceHorizontalPart q.val - halfSpaceHorizontalPart p.val) := by
  rcases hL with ⟨v, _, rfl⟩ | ⟨x, u, _, hu0, c, rad, _, rfl⟩
  · exact False.elim (hh (hp.trans hq.symm))
  · obtain ⟨zp, hzp⟩ := hp.1
    obtain ⟨zq, hzq⟩ := hq.1
    obtain ⟨zr, hzr⟩ := hr.1
    have hpH : halfSpaceHorizontalPart p.val = halfSpaceHorizontalPart x + zp.re • u := by
      rw [← hzp, halfSpaceHorizontalPart_planeEmbed x u hu0]
    have hqH : halfSpaceHorizontalPart q.val = halfSpaceHorizontalPart x + zq.re • u := by
      rw [← hzq, halfSpaceHorizontalPart_planeEmbed x u hu0]
    have hrH : halfSpaceHorizontalPart r.val = halfSpaceHorizontalPart x + zr.re • u := by
      rw [← hzr, halfSpaceHorizontalPart_planeEmbed x u hu0]
    have hdiff : zq.re - zp.re ≠ 0 := by
      intro he
      apply hh
      rw [hpH, hqH, sub_eq_zero.mp he]
    refine ⟨(zr.re - zp.re) / (zq.re - zp.re), ?_⟩
    rw [hpH, hqH, hrH]
    simp only [add_sub_add_left_eq_sub, ← sub_smul, smul_smul, div_mul_cancel₀ _ hdiff]

/-- Orthogonal plane projection is exact at every actual point of the plane. -/
theorem halfSpacePlaneEmbedUHP_project_of_mem {n : ℕ} (x u : Inversive.Euclidean (n + 1))
    (hu : ‖u‖ = 1) (hu0 : halfSpaceHeight n u = 0) (p : HyperbolicHalfSpace n)
    (hp : p.val ∈ Set.range (halfSpacePlaneEmbed x u)) :
    halfSpacePlaneEmbedUHP x u hu0 (halfSpacePlaneProjectUHP x u p) = p := by
  obtain ⟨z, hz⟩ := hp
  have hzpos : 0 < z.im := by
    rw [← halfSpacePlaneEmbed_height x u hu0 z, hz]
    exact p.property
  let w : ℍ := ⟨z, hzpos⟩
  have hw : halfSpacePlaneEmbedUHP x u hu0 w = p := Subtype.ext hz
  rw [← hw, halfSpacePlaneProjectUHP_embed x u hu hu0]

/-- Every complete metric geodesic is contained in one actual vertical two-plane. -/
theorem halfSpace_metric_geodesic_planar {n : ℕ} (hn : 1 ≤ n)
    (γ : ℝ → HyperbolicHalfSpace n)
    (hγ : ∀ s t, halfSpacePathDist (γ s) (γ t) = dist s t) :
    ∃ (u : Inversive.Euclidean (n + 1)) (hu0 : halfSpaceHeight n u = 0), ‖u‖ = 1 ∧
      ∀ t : ℝ, halfSpacePlaneEmbedUHP (γ 0).val u hu0
        (halfSpacePlaneProjectUHP (γ 0).val u (γ t)) = γ t := by
  obtain ⟨u, a, hu, hu0, hdir⟩ := exists_halfSpace_horizontal_direction hn (γ 0).val (γ 1).val
  have hneq : γ 0 ≠ γ 1 := by
    intro he
    have h := hγ 0 1
    rw [he, (halfSpacePathDist_metric_axioms (γ 1) (γ 1) (γ 1)).2.1.mpr rfl] at h
    norm_num at h
  refine ⟨u, hu0, hu, ?_⟩
  intro t
  obtain ⟨L, hL, h0L, h1L, htL⟩ := halfSpace_metric_geodesic_three_points hn γ hγ 0 1 t
  have hhorizontal : ∃ r : ℝ,
      halfSpaceHorizontalPart ((γ t).val - (γ 0).val) = r • u := by
    by_cases hh : halfSpaceHorizontalPart (γ 0).val = halfSpaceHorizontalPart (γ 1).val
    · have hvertical := halfSpace_geodesicLine_same_horizontal hL (γ 0) (γ 1) h0L h1L hneq hh
      rw [hvertical] at htL
      refine ⟨0, ?_⟩
      rw [halfSpaceHorizontalPart_sub, htL, sub_self, zero_smul]
    · obtain ⟨r, hr⟩ := halfSpace_geodesicLine_horizontal_chord hL (γ 0) (γ 1) (γ t) h0L h1L htL hh
      refine ⟨r * a, ?_⟩
      rw [halfSpaceHorizontalPart_sub] at hdir ⊢
      rw [hr, hdir, smul_smul]
  obtain ⟨r, hr⟩ := hhorizontal
  apply halfSpacePlaneEmbedUHP_project_of_mem _ _ hu hu0
  exact ⟨(r : ℂ) + (halfSpaceHeight n (γ t).val : ℂ) * Complex.I,
    halfSpacePlaneEmbed_of_horizontalPart_sub (γ 0).val (γ t).val u r hr⟩

/-- A genuine upper-half-plane geodesic through distinct equal-real-part points is vertical. -/
theorem halfPlane_geodesicLine_same_real {L : Set ℍ} (hL : IsHalfPlaneGeodesicLine L)
    (p q : ℍ) (hp : p ∈ L) (hq : q ∈ L) (hpq : p ≠ q) (hh : p.re = q.re) :
    L = {r | r.re = p.re} := by
  rcases hL with ⟨a, rfl⟩ | ⟨c, r, _, rfl⟩
  · change p.re = a at hp
    rw [hp]
  · have hs := congrArg (fun t : ℝ => t ^ (2 : ℕ)) (hp.trans hq.symm)
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq] at hs
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im, hh] at hs
    have him : p.im = q.im := by nlinarith [p.im_pos, q.im_pos]
    exact False.elim (hpq (UpperHalfPlane.ext_re_im hh him))

/-- Any three points of a complete upper-half-plane metric geodesic lie on a native line. -/
theorem halfPlane_metric_geodesic_three_points (γ : ℝ → ℍ) (hγ : Isometry γ) (a b c : ℝ) :
    ∃ L : Set ℍ, IsHalfPlaneGeodesicLine L ∧ γ a ∈ L ∧ γ b ∈ L ∧ γ c ∈ L := by
  let s := min a (min b c)
  let t := max a (max b c)
  obtain ⟨g, hg⟩ := exists_sl2_same_real_part (γ s) (γ t)
  let Γ := halfPlaneSL2Geodesic g (g • γ s).re
  have hmem (r : ℝ) (hsr : s ≤ r) (hrt : r ≤ t) : γ r ∈ Set.range Γ := by
    have heq : dist (γ s) (γ r) + dist (γ r) (γ t) = dist (γ s) (γ t) := by
      rw [hγ.dist_eq, hγ.dist_eq, hγ.dist_eq]
      exact (halfPlane_real_triangle_eq_iff_uIcc s t r).mpr (Set.mem_uIcc_of_le hsr hrt)
    obtain ⟨w, _, hw⟩ := (halfPlane_triangle_eq_iff_geodesic_interval g (γ s) (γ t) (γ r) hg).mp heq
    exact ⟨w, hw⟩
  refine ⟨Set.range Γ, halfPlaneSL2Geodesic_isLine _ _,
    hmem a ?_ ?_, hmem b ?_ ?_, hmem c ?_ ?_⟩
  · exact min_le_left _ _
  · exact le_max_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (min_le_right _ _).trans (min_le_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

/-- Every complete metric geodesic of the upper half-plane is the entire range of a native SL2 geodesic. -/
theorem halfPlane_metric_geodesic_eq_SL2 (γ : ℝ → ℍ) (hγ : Isometry γ) :
    ∃ (g : Matrix.SpecialLinearGroup (Fin 2) ℝ) (a : ℝ),
      Set.range γ = Set.range (halfPlaneSL2Geodesic g a) := by
  obtain ⟨g, hg⟩ := exists_sl2_same_real_part (γ 0) (γ 1)
  let δ : ℝ → ℍ := fun t => g • γ t
  have hδ : Isometry δ := by
    apply Isometry.of_dist_eq
    intro s t
    simpa only [δ, dist_smul] using hγ.dist_eq s t
  have hδreal : ∀ t : ℝ, (δ t).re = (δ 0).re := by
    intro t
    obtain ⟨L, hL, h0L, h1L, htL⟩ := halfPlane_metric_geodesic_three_points δ hδ 0 1 t
    have hneq : δ 0 ≠ δ 1 := hδ.injective.ne (by norm_num)
    have hvertical := halfPlane_geodesicLine_same_real hL (δ 0) (δ 1) h0L h1L hneq hg
    rw [hvertical] at htL
    exact htL
  let ℓ : ℝ → ℝ := fun t => Real.log (δ t).im
  have hℓ : Isometry ℓ := by
    apply Isometry.of_dist_eq
    intro s t
    have hd := hδ.dist_eq s t
    rw [UpperHalfPlane.dist_of_re_eq ((hδreal s).trans (hδreal t).symm)] at hd
    exact hd
  have hℓsurj := real_isometry_surjective ℓ hℓ
  refine ⟨g, (δ 0).re, ?_⟩
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨ℓ t, halfPlaneSL2Geodesic_parameter g (δ 0).re (γ t) (hδreal t)⟩
  · rintro ⟨r, rfl⟩
    obtain ⟨t, ht⟩ := hℓsurj r
    refine ⟨t, ?_⟩
    rw [← ht]
    exact (halfPlaneSL2Geodesic_parameter g (δ 0).re (γ t) (hδreal t)).symm

/-- Every complete real isometry into any genuine upper half-space has exactly a vertical-line or perpendicular-semicircle image. -/
theorem halfSpace_metric_geodesic_isLine {n : ℕ} (hn : 1 ≤ n)
    (γ : ℝ → HyperbolicHalfSpace n)
    (hγ : ∀ s t, halfSpacePathDist (γ s) (γ t) = dist s t) :
    IsHalfSpaceGeodesicLine n (Set.range γ) := by
  obtain ⟨u, hu0, hu, hreconstruct⟩ := halfSpace_metric_geodesic_planar hn γ hγ
  let η : ℝ → ℍ := fun t => halfSpacePlaneProjectUHP (γ 0).val u (γ t)
  have hη : Isometry η := by
    apply Isometry.of_dist_eq
    intro s t
    have hd := halfSpacePlaneEmbed_pathDist (γ 0).val u hu hu0 (η s) (η t)
    rw [show halfSpacePlaneEmbedUHP (γ 0).val u hu0 (η s) = γ s from hreconstruct s,
      show halfSpacePlaneEmbedUHP (γ 0).val u hu0 (η t) = γ t from hreconstruct t, hγ] at hd
    exact hd.symm
  obtain ⟨g, a, hηrange⟩ := halfPlane_metric_geodesic_eq_SL2 η hη
  have hrange : Set.range γ =
      Set.range (halfSpacePlaneSL2Geodesic (γ 0).val u hu0 g a) := by
    rw [halfSpacePlaneSL2Geodesic_range, ← hηrange, ← Set.range_comp]
    congr 1
    funext t
    exact (hreconstruct t).symm
  rw [hrange]
  exact halfSpacePlaneSL2Geodesic_isLine _ _ hu hu0 g a

/-- The complete metric-geodesic and actual Euclidean-geometric definitions agree in every permitted dimension. -/
theorem halfSpace_geodesicLine_iff_metric_param {n : ℕ} (hn : 1 ≤ n)
    (L : Set (HyperbolicHalfSpace n)) :
    IsHalfSpaceGeodesicLine n L ↔
      ∃ γ : ℝ → HyperbolicHalfSpace n,
        (∀ s t, halfSpacePathDist (γ s) (γ t) = dist s t) ∧ Set.range γ = L := by
  constructor
  · exact halfSpace_geodesicLine_exists_param hn
  · rintro ⟨γ, hγ, rfl⟩
    exact halfSpace_metric_geodesic_isLine hn γ hγ

/-- Every isometry for the actual path metric sends genuine native geodesic lines to genuine native lines. -/
theorem halfSpace_geodesicLine_image_pathIsometry {n : ℕ} (hn : 1 ≤ n)
    (F : HyperbolicHalfSpace n → HyperbolicHalfSpace n)
    (hF : ∀ p q, halfSpacePathDist (F p) (F q) = halfSpacePathDist p q)
    {L : Set (HyperbolicHalfSpace n)} (hL : IsHalfSpaceGeodesicLine n L) :
    IsHalfSpaceGeodesicLine n (F '' L) := by
  obtain ⟨γ, hγ, hrange⟩ := halfSpace_geodesicLine_exists_param hn hL
  have h := halfSpace_metric_geodesic_isLine hn (F ∘ γ) (fun s t => (hF _ _).trans (hγ s t))
  rwa [Set.range_comp, hrange] at h

/-- Genuine canonical Poincare extensions preserve the actual Euclidean shapes of complete geodesics. -/
theorem poincareHalfSpaceHomeomorph_image_geodesicLine {n : ℕ} [NeZero n]
    (hn : 1 ≤ n) (g : Inversive.GM n) {L : Set (HyperbolicHalfSpace n)}
    (hL : IsHalfSpaceGeodesicLine n L) :
    IsHalfSpaceGeodesicLine n (poincareHalfSpaceHomeomorph g '' L) :=
  halfSpace_geodesicLine_image_pathIsometry hn (poincareHalfSpaceHomeomorph g)
    (poincareHalfSpaceHomeomorph_pathDist g) hL

end LowDimensionalTopology.Geometry.Hyperbolic
