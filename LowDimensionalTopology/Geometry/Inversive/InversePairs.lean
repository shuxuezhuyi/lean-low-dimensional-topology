module
public import LowDimensionalTopology.Geometry.Inversive.SphereOrthogonality

/-!
# The geometric inverse-pair criterion

For distinct extended points, reflection in a generalized sphere interchanges
them exactly when every generalized sphere through them is geometrically
orthogonal to that sphere. The finite plane case follows from the polynomial
reflection formula, planes through the pair, and its midpoint sphere.
Conjugation treats all spheres and all infinity branches. A proved repeated-
point counterexample records why the distinctness hypothesis is necessary.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint RealInnerProductSpace
open Filter EuclideanGeometry Metric InnerProductGeometry
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}

/-- Every actual generalized sphere through the two specified points is geometrically perpendicular to the given sphere. -/
def EverySphereThroughOrthogonal (S : GeneralizedSphere n) (x y : ExtendedEuclidean n) : Prop :=
  ∀ T : GeneralizedSphere n, x ∈ T.val → y ∈ T.val → GeneralizedSpheresOrthogonal S T

/-- The geometric universal condition has the equivalent inversive-product expression. -/
theorem everySphereThroughOrthogonal_iff_product_zero (hn : 2 ≤ n) (S : GeneralizedSphere n)
    (x y : ExtendedEuclidean n) : EverySphereThroughOrthogonal S x y ↔
      ∀ T : GeneralizedSphere n, x ∈ T.val → y ∈ T.val → inversiveProduct S T = 0 := by
  simp only [EverySphereThroughOrthogonal, generalizedSpheresOrthogonal_iff_inversiveProduct_eq_zero hn]

/-- The polynomial discrepancy between a finite point and its plane reflection. -/
theorem coefficient_polynomial_planeReflection (a : Euclidean n) (t : ℝ) (ha : a ≠ 0)
    (b : SphereCoefficients n) (x : Euclidean n) :
    (b.1 * ‖planeReflectionFinite a t x‖ ^ 2 - 2 * inner ℝ (planeReflectionFinite a t x) b.2.1 + b.2.2) -
      (b.1 * ‖x‖ ^ 2 - 2 * inner ℝ x b.2.1 + b.2.2) =
      (4 * (inner ℝ x a - t) / ‖a‖ ^ 2) * (inner ℝ a b.2.1 - b.1 * t) := by
  rw [norm_sq_planeReflectionFinite a t ha x, planeReflectionFinite, inner_sub_left, real_inner_smul_left]
  ring

/-- Distinct finite plane inverse points force every sphere through them to be orthogonal. -/
theorem plane_inversePair_product_zero [NeZero n] (a : Euclidean n) (t : ℝ) (ha : a ≠ 0)
    (x y : Euclidean n) (hxy : x ≠ y) (hreflect : planeReflectionFinite a t x = y)
    (T : GeneralizedSphere n) (hx : (x : ExtendedEuclidean n) ∈ T.val) (hy : (y : ExtendedEuclidean n) ∈ T.val) :
    inversiveProduct (planeGeneralizedSphere a t ha) T = 0 := by
  let b := generalizedSphereCoefficients T
  have hb : sphereCoefficientCarrier b = T.val := generalizedSphereCoefficients_carrier T
  have hxb : b.1 * ‖x‖ ^ 2 - 2 * inner ℝ x b.2.1 + b.2.2 = 0 := by
    change (x : ExtendedEuclidean n) ∈ sphereCoefficientCarrier b
    rw [hb]
    exact hx
  have hyb : b.1 * ‖planeReflectionFinite a t x‖ ^ 2 -
      2 * inner ℝ (planeReflectionFinite a t x) b.2.1 + b.2.2 = 0 := by
    rw [hreflect]
    change (y : ExtendedEuclidean n) ∈ sphereCoefficientCarrier b
    rw [hb]
    exact hy
  have hd : inner ℝ x a - t ≠ 0 := by
    intro h
    apply hxy
    rw [← hreflect, planeReflectionFinite, h, mul_zero, zero_div, zero_smul, sub_zero]
  have hfactor : 4 * (inner ℝ x a - t) / ‖a‖ ^ 2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (by norm_num) hd) (pow_ne_zero _ (norm_ne_zero_iff.mpr ha))
  have hdiff := coefficient_polynomial_planeReflection a t ha b x
  rw [hxb, hyb, sub_self] at hdiff
  have hnorm : inner ℝ a b.2.1 - b.1 * t = 0 := (mul_eq_zero.mp hdiff.symm).resolve_left hfactor
  rw [inversiveProduct_eq_coefficients _ _ (planeCoefficients a t) b
    (sphereCoefficients_ne_zero_of_pos _ (sphereDiscriminant_pos_plane a t ha))
    (sphereCoefficients_ne_zero_of_pos _ (generalizedSphereCoefficients_pos T))
    (sphereCoefficientCarrier_plane a t) hb]
  have hpair : inversivePairing (planeCoefficients a t) b = 0 := by
    simp only [inversivePairing, planeCoefficients, zero_mul, sub_zero]
    nlinarith
  simp only [coefficientInversiveProduct, hpair, abs_zero, zero_div]

/-- Conversely, planes through the pair and its midpoint sphere determine the plane inverse relation. -/
theorem plane_reflection_of_every_sphere_product_zero [NeZero n] (a : Euclidean n) (t : ℝ) (ha : a ≠ 0)
    (x y : Euclidean n) (hxy : x ≠ y)
    (horth : ∀ T : GeneralizedSphere n, (x : ExtendedEuclidean n) ∈ T.val →
      (y : ExtendedEuclidean n) ∈ T.val → inversiveProduct (planeGeneralizedSphere a t ha) T = 0) :
    planeReflectionFinite a t x = y := by
  let d := x - y
  have hd : d ≠ 0 := sub_ne_zero.mpr hxy
  have hfixnormal (v : Euclidean n) (hv : inner ℝ v d = 0) : inner ℝ v a = 0 := by
    by_cases hv0 : v = 0
    · simp [hv0]
    have hy : inner ℝ y v = inner ℝ x v := by
      have h : inner ℝ (x - y) v = 0 := by rw [real_inner_comm v (x - y)]; exact hv
      rw [inner_sub_left] at h
      linarith
    have hp := horth (planeGeneralizedSphere v (inner ℝ x v) hv0)
      (Or.inr ⟨x, rfl, rfl⟩) (Or.inr ⟨y, hy, rfl⟩)
    rw [inversiveProduct_plane_plane] at hp
    have hzero := (div_eq_zero_iff.mp hp).resolve_right
      (mul_ne_zero (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hv0))
    rw [real_inner_comm a v]
    exact abs_eq_zero.mp hzero
  have hamem : a ∈ ((ℝ ∙ d)ᗮ)ᗮ := by
    intro v hv
    exact hfixnormal v (Submodule.mem_orthogonal_singleton_iff_inner_left.mp hv)
  rw [Submodule.orthogonal_orthogonal] at hamem
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hamem
  have hk0 : k ≠ 0 := by intro hz; rw [hz, zero_smul] at hk; exact ha hk.symm
  let m := (1 / 2 : ℝ) • (x + y)
  let r := ‖d‖ / 2
  have hr : 0 < r := div_pos (norm_pos_iff.mpr hd) two_pos
  have hxm : dist x m = r := by
    rw [dist_eq_norm]
    have h : x - m = (1 / 2 : ℝ) • d := by dsimp [m, d]; module
    rw [h, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    dsimp [r]
    ring
  have hym : dist y m = r := by
    rw [dist_eq_norm]
    have h : y - m = -(1 / 2 : ℝ) • d := by dsimp [m, d]; module
    rw [h, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    dsimp [r]
    ring
  have hmid := horth (euclideanGeneralizedSphere m r hr) ⟨x, hxm, rfl⟩ ⟨y, hym, rfl⟩
  rw [inversiveProduct_comm, inversiveProduct_sphere_plane] at hmid
  have hnum := (div_eq_zero_iff.mp hmid).resolve_right (mul_ne_zero hr.ne' (norm_ne_zero_iff.mpr ha))
  have hma : inner ℝ m a = t := sub_eq_zero.mp (abs_eq_zero.mp hnum)
  have hsum : inner ℝ x a + inner ℝ y a = 2 * t := by
    dsimp [m] at hma
    rw [real_inner_smul_left, inner_add_left] at hma
    linarith
  have hda : inner ℝ x a - inner ℝ y a = k * ‖d‖ ^ 2 := by
    have h : inner ℝ d a = k * ‖d‖ ^ 2 := by
      rw [← hk, real_inner_smul_right, real_inner_self_eq_norm_sq]
    simpa only [d, inner_sub_left] using h
  have hdiscrep : 2 * (inner ℝ x a - t) = k * ‖d‖ ^ 2 := by linarith
  have hnorma : ‖a‖ ^ 2 = k ^ 2 * ‖d‖ ^ 2 := by
    rw [← hk, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hscale : (2 * (inner ℝ x a - t) / ‖a‖ ^ 2) * k = 1 := by
    rw [hdiscrep, hnorma]
    field_simp [hk0, norm_ne_zero_iff.mpr hd]
  have hvec : (2 * (inner ℝ x a - t) / ‖a‖ ^ 2) • a = d := by
    calc
      _ = (2 * (inner ℝ x a - t) / ‖a‖ ^ 2) • (k • d) := congrArg _ hk.symm
      _ = _ := by rw [smul_smul, hscale, one_smul]
  rw [planeReflectionFinite, hvec]
  dsimp [d]
  abel


/-- A plane has inversive product one with any parallel translate of itself. -/
theorem inversiveProduct_parallel_self [NeZero n] (a : Euclidean n) (r t : ℝ) (ha : a ≠ 0) :
    inversiveProduct (planeGeneralizedSphere a r ha) (planeGeneralizedSphere a t ha) = 1 := by
  rw [inversiveProduct_plane_plane, real_inner_self_eq_norm_sq, abs_of_nonneg (sq_nonneg _)]
  field_simp [norm_ne_zero_iff.mpr ha]

/-- The plane case of the inverse-pair criterion, including all infinity branches. -/
theorem plane_isInversePair_iff_everySphereThroughOrthogonal (hn : 2 ≤ n)
    (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) (x y : ExtendedEuclidean n) (hxy : x ≠ y) :
    IsInversePair (plane a t) x y ↔ EverySphereThroughOrthogonal (planeGeneralizedSphere a t ha) x y := by
  let : NeZero n := ⟨by omega⟩
  rw [isInversePair_iff_reflection_apply (plane a t) (planeReflectionHomeomorph a t ha)
    (planeReflection_isReflection a t ha) (fixedPoints_planeReflection a t ha),
    everySphereThroughOrthogonal_iff_product_zero hn]
  induction x using OnePoint.rec with
  | infty =>
    induction y using OnePoint.rec with
    | infty => exact (hxy rfl).elim
    | coe y =>
      constructor
      · intro h; exact (OnePoint.coe_ne_infty y h.symm).elim
      · intro h
        have hp := h (planeGeneralizedSphere a (inner ℝ y a) ha) (Or.inl rfl) (Or.inr ⟨y, rfl, rfl⟩)
        rw [inversiveProduct_parallel_self] at hp
        exact (one_ne_zero hp).elim
  | coe x =>
    induction y using OnePoint.rec with
    | infty =>
      constructor
      · intro h; exact (OnePoint.coe_ne_infty _ h).elim
      · intro h
        have hp := h (planeGeneralizedSphere a (inner ℝ x a) ha) (Or.inr ⟨x, rfl, rfl⟩) (Or.inl rfl)
        rw [inversiveProduct_parallel_self] at hp
        exact (one_ne_zero hp).elim
    | coe y =>
      have hxy' : x ≠ y := by intro h; exact hxy (congrArg OnePoint.some h)
      change (planeReflectionFinite a t x : ExtendedEuclidean n) = y ↔ _
      rw [OnePoint.coe_eq_coe]
      exact ⟨fun h => plane_inversePair_product_zero a t ha x y hxy' h,
        fun h => plane_reflection_of_every_sphere_product_zero a t ha x y hxy' h⟩

/-- A Möbius image carries the universal geometric orthogonality condition to the image pair. -/
theorem EverySphereThroughOrthogonal.image [NeZero n] (hn : 2 ≤ n)
    {S : GeneralizedSphere n} {x y : ExtendedEuclidean n} (h : EverySphereThroughOrthogonal S x y)
    (g : ExtendedHomeomorph n) (hg : g ∈ generalMobiusGroup n) :
    EverySphereThroughOrthogonal (generalizedSphereImage g hg S) (g x) (g y) := by
  intro T hxT hyT
  let U := generalizedSphereImage g⁻¹ ((generalMobiusGroup n).inv_mem hg) T
  have hxU : x ∈ U.val := ⟨g x, hxT, by simp⟩
  have hyU : y ∈ U.val := ⟨g y, hyT, by simp⟩
  have hST := (h U hxU hyU).image hn S U g hg
  have hU : generalizedSphereImage g hg U = T := by
    apply Subtype.ext
    simp [U, generalizedSphereImage, Set.image_image]
  rwa [hU] at hST

/-- With distinctness of the two points made explicit. -/
theorem isInversePair_iff_everySphereThroughOrthogonal (hn : 2 ≤ n)
    (S : GeneralizedSphere n) (x y : ExtendedEuclidean n) (hxy : x ≠ y) :
    IsInversePair S.val x y ↔ EverySphereThroughOrthogonal S x y := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨f, hf, hS⟩ := (isGeneralizedSphere_iff_fixedPoints_reflection S.val).mp S.property
  obtain ⟨a, ha⟩ := exists_ne (0 : Euclidean n)
  let R := planeReflectionHomeomorph a 0 ha
  obtain ⟨g, hg, hfconj⟩ := reflections_conjugate f R hf (planeReflection_isReflection a 0 ha)
  have himage : generalizedSphereImage g⁻¹ ((generalMobiusGroup n).inv_mem hg) S = planeGeneralizedSphere a 0 ha := by
    apply Subtype.ext
    change g.symm '' S.val = plane a 0
    rw [← hS, hfconj, fixedPoints_homeomorph_conjugation, fixedPoints_planeReflection]
    simp [Set.image_image]
  have hinverse (U : GeneralizedSphere n) :
      generalizedSphereImage g hg (generalizedSphereImage g⁻¹ ((generalMobiusGroup n).inv_mem hg) U) = U := by
    apply Subtype.ext
    simp [generalizedSphereImage, Set.image_image]
  have hne : g⁻¹ x ≠ g⁻¹ y := g.symm.injective.ne hxy
  constructor
  · intro h
    have hp := h.image ((generalMobiusGroup n).inv_mem hg)
    have hcarrier : g.symm '' S.val = plane a 0 := congrArg Subtype.val himage
    change IsInversePair (g.symm '' S.val) (g.symm x) (g.symm y) at hp
    rw [hcarrier] at hp
    have ho := (plane_isInversePair_iff_everySphereThroughOrthogonal hn a 0 ha (g⁻¹ x) (g⁻¹ y) hne).mp hp
    rw [← himage] at ho
    have hh := ho.image hn g hg
    simpa [hinverse] using hh
  · intro h
    have ho := h.image hn g⁻¹ ((generalMobiusGroup n).inv_mem hg)
    rw [himage] at ho
    have hp := (plane_isInversePair_iff_everySphereThroughOrthogonal hn a 0 ha (g⁻¹ x) (g⁻¹ y) hne).mpr ho
    have hh := hp.image hg
    have hcarrier : g '' plane a 0 = S.val := by
      have hp : g.symm '' S.val = plane a 0 := congrArg Subtype.val himage
      rw [← hp]
      simp [Set.image_image]
    rw [hcarrier] at hh
    simpa using hh


/-- A genuine generalized sphere has inversive product one with itself. -/
theorem inversiveProduct_self (S : GeneralizedSphere n) : inversiveProduct S S = 1 := by
  let a := generalizedSphereCoefficients S
  have ha : 0 < sphereDiscriminant a := generalizedSphereCoefficients_pos S
  change |inversivePairing a a| / (2 * Real.sqrt (sphereDiscriminant a) * Real.sqrt (sphereDiscriminant a)) = 1
  rw [inversivePairing_self, abs_of_pos (mul_pos two_pos ha)]
  have hd : 2 * Real.sqrt (sphereDiscriminant a) * Real.sqrt (sphereDiscriminant a) =
      2 * sphereDiscriminant a := by nlinarith [Real.sq_sqrt ha.le]
  rw [hd, div_self (mul_pos two_pos ha).ne']

/-- A repeated point on the reflecting sphere is an inverse pair but fails the universal orthogonality criterion. -/
theorem repeated_inversePair_not_everySphereThroughOrthogonal (hn : 2 ≤ n) (S : GeneralizedSphere n)
    (x : ExtendedEuclidean n) (hx : x ∈ S.val) :
    IsInversePair S.val x x ∧ ¬EverySphereThroughOrthogonal S x x := by
  obtain ⟨f, hf, hS⟩ := (isGeneralizedSphere_iff_fixedPoints_reflection S.val).mp S.property
  constructor
  · exact ⟨f, hf, hS, (hS.symm ▸ hx : x ∈ Function.fixedPoints f)⟩
  · intro h
    have hzero := (generalizedSpheresOrthogonal_iff_inversiveProduct_eq_zero hn S S).mp (h S hx hx)
    rw [inversiveProduct_self] at hzero
    exact one_ne_zero hzero

end LowDimensionalTopology.Geometry.Inversive
