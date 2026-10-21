module
public import LowDimensionalTopology.Geometry.Inversive.InversiveInvariance
public import LowDimensionalTopology.Geometry.Inversive.SpherePointwiseFixer
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Angles and orthogonality of generalized spheres

Normals of the actual quadratic loci recover the intersection-angle formula.
In dimension at least two, zero inversive product supplies a finite intersection
with perpendicular normals; the proof constructs intersections in all three
sphere/plane cases. Centre-to-plane distance uses Mathlib's metric infimum
distance, with the explicit perpendicular foot attaining that infimum.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint RealInnerProductSpace
open Filter EuclideanGeometry Metric InnerProductGeometry
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}

/-- The geometric normal of a generalized-sphere quadratic equation at a finite point. -/
def sphereCoefficientNormal (a : SphereCoefficients n) (x : Euclidean n) : Euclidean n :=
  a.1 • x - a.2.1

/-- On the sphere the squared normal length is its coefficient discriminant. -/
theorem sphereCoefficientNormal_norm_sq (a : SphereCoefficients n) (x : Euclidean n)
    (hx : (x : ExtendedEuclidean n) ∈ sphereCoefficientCarrier a) :
    ‖sphereCoefficientNormal a x‖ ^ 2 = sphereDiscriminant a := by
  change a.1 * ‖x‖ ^ 2 - 2 * inner ℝ x a.2.1 + a.2.2 = 0 at hx
  have hm : a.1 * (a.1 * ‖x‖ ^ 2 - 2 * inner ℝ x a.2.1 + a.2.2) = 0 := by rw [hx, mul_zero]
  simp only [sphereCoefficientNormal, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow,
    sq_abs, real_inner_smul_left, sphereDiscriminant]
  nlinarith

/-- The coefficient pairing is twice the inner product of the two geometric normals. -/
theorem sphereCoefficientNormal_pairing (a b : SphereCoefficients n) (x : Euclidean n)
    (ha : (x : ExtendedEuclidean n) ∈ sphereCoefficientCarrier a)
    (hb : (x : ExtendedEuclidean n) ∈ sphereCoefficientCarrier b) :
    inversivePairing a b = 2 * inner ℝ (sphereCoefficientNormal a x) (sphereCoefficientNormal b x) := by
  change a.1 * ‖x‖ ^ 2 - 2 * inner ℝ x a.2.1 + a.2.2 = 0 at ha
  change b.1 * ‖x‖ ^ 2 - 2 * inner ℝ x b.2.1 + b.2.2 = 0 at hb
  have ham : b.1 * (a.1 * ‖x‖ ^ 2 - 2 * inner ℝ x a.2.1 + a.2.2) = 0 := by rw [ha, mul_zero]
  have hbm : a.1 * (b.1 * ‖x‖ ^ 2 - 2 * inner ℝ x b.2.1 + b.2.2) = 0 := by rw [hb, mul_zero]
  simp only [sphereCoefficientNormal, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, real_inner_self_eq_norm_sq, inversivePairing]
  rw [real_inner_comm x a.2.1]
  nlinarith

/-- Intersecting generalized spheres have inversive product equal to the absolute cosine of their normal angle. -/
theorem coefficientInversiveProduct_eq_abs_cos_angle (a b : SphereCoefficients n) (x : Euclidean n)
    (ha : (x : ExtendedEuclidean n) ∈ sphereCoefficientCarrier a)
    (hb : (x : ExtendedEuclidean n) ∈ sphereCoefficientCarrier b) :
    coefficientInversiveProduct a b =
      |Real.cos (angle (sphereCoefficientNormal a x) (sphereCoefficientNormal b x))| := by
  have hsa : Real.sqrt (sphereDiscriminant a) = ‖sphereCoefficientNormal a x‖ := by
    rw [← sphereCoefficientNormal_norm_sq a x ha, Real.sqrt_sq (norm_nonneg _)]
  have hsb : Real.sqrt (sphereDiscriminant b) = ‖sphereCoefficientNormal b x‖ := by
    rw [← sphereCoefficientNormal_norm_sq b x hb, Real.sqrt_sq (norm_nonneg _)]
  rw [coefficientInversiveProduct, sphereCoefficientNormal_pairing a b x ha hb, hsa, hsb,
    cos_angle, abs_div, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)), abs_mul, abs_of_pos two_pos]
  rw [show 2 * ‖sphereCoefficientNormal a x‖ * ‖sphereCoefficientNormal b x‖ =
    2 * (‖sphereCoefficientNormal a x‖ * ‖sphereCoefficientNormal b x‖) by ring]
  exact mul_div_mul_left _ _ two_ne_zero

/-- The angle formula is independent of the chosen nonzero equations for the actual geometric spheres. -/
theorem inversiveProduct_eq_abs_cos_angle [NeZero n] (S T : GeneralizedSphere n)
    (a b : SphereCoefficients n) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : sphereCoefficientCarrier a = S.val) (hb : sphereCoefficientCarrier b = T.val)
    (x : Euclidean n) (hxS : (x : ExtendedEuclidean n) ∈ S.val) (hxT : (x : ExtendedEuclidean n) ∈ T.val) :
    inversiveProduct S T = |Real.cos (angle (sphereCoefficientNormal a x) (sphereCoefficientNormal b x))| := by
  rw [inversiveProduct_eq_coefficients S T a b ha0 hb0 ha hb]
  exact coefficientInversiveProduct_eq_abs_cos_angle a b x (ha.symm ▸ hxS) (hb.symm ▸ hxT)

/-- At a finite intersection, vanishing of the inversive product is exactly perpendicularity of normals. -/
theorem inversiveProduct_eq_zero_iff_normals_orthogonal [NeZero n] (S T : GeneralizedSphere n)
    (a b : SphereCoefficients n) (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (ha : sphereCoefficientCarrier a = S.val) (hb : sphereCoefficientCarrier b = T.val)
    (x : Euclidean n) (hxS : (x : ExtendedEuclidean n) ∈ S.val) (hxT : (x : ExtendedEuclidean n) ∈ T.val) :
    inversiveProduct S T = 0 ↔ inner ℝ (sphereCoefficientNormal a x) (sphereCoefficientNormal b x) = 0 := by
  have hapos := sphereDiscriminant_pos_of_carrier a ha0 (ha.symm ▸ S.property)
  have hbpos := sphereDiscriminant_pos_of_carrier b hb0 (hb.symm ▸ T.property)
  rw [inversiveProduct_eq_coefficients S T a b ha0 hb0 ha hb, coefficientInversiveProduct,
    sphereCoefficientNormal_pairing a b x (ha.symm ▸ hxS) (hb.symm ▸ hxT),
    div_eq_zero_iff]
  simp only [abs_eq_zero, mul_eq_zero, two_ne_zero, false_or]
  exact or_iff_left (not_or.mpr ⟨(Real.sqrt_pos.mpr hapos).ne', (Real.sqrt_pos.mpr hbpos).ne'⟩)

/-- The foot of the perpendicular from a point to an affine plane. -/
def planeProjection (a : Euclidean n) (t : ℝ) (x : Euclidean n) : Euclidean n :=
  x - ((inner ℝ x a - t) / ‖a‖ ^ 2) • a

theorem planeProjection_mem (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) (x : Euclidean n) :
    inner ℝ (planeProjection a t x) a = t := by
  unfold planeProjection
  rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    div_mul_cancel₀ _ (pow_ne_zero _ (norm_ne_zero_iff.mpr ha))]
  ring

theorem dist_planeProjection (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) (x : Euclidean n) :
    dist x (planeProjection a t x) = |inner ℝ x a - t| / ‖a‖ := by
  rw [dist_eq_norm]
  unfold planeProjection
  rw [sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_div, abs_pow, abs_norm]
  field_simp [norm_ne_zero_iff.mpr ha]

/-- The Euclidean distance to an affine plane is its normalized normal-coordinate discrepancy. -/
theorem infDist_plane (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) (x : Euclidean n) :
    Metric.infDist x {y : Euclidean n | inner ℝ y a = t} = |inner ℝ x a - t| / ‖a‖ := by
  let S := {y : Euclidean n | inner ℝ y a = t}
  have hp : planeProjection a t x ∈ S := planeProjection_mem a t ha x
  apply le_antisymm
  · calc
      _ ≤ dist x (planeProjection a t x) := Metric.infDist_le_dist_of_mem hp
      _ = _ := dist_planeProjection a t ha x
  · apply (Metric.le_infDist ⟨_, hp⟩).mpr
    intro y hy
    apply (div_le_iff₀ (norm_pos_iff.mpr ha)).mpr
    rw [dist_eq_norm]
    have h := abs_real_inner_le_norm (x - y) a
    rw [inner_sub_left, hy] at h
    exact h

/-- The sphere-plane inversive product is centre-to-plane distance divided by the positive radius. -/
theorem inversiveProduct_sphere_plane_eq_infDist [NeZero n] (c a : Euclidean n) (r t : ℝ)
    (hr : 0 < r) (ha : a ≠ 0) :
    inversiveProduct (euclideanGeneralizedSphere c r hr) (planeGeneralizedSphere a t ha) =
      Metric.infDist c {y : Euclidean n | inner ℝ y a = t} / r := by
  rw [inversiveProduct_sphere_plane c a r t hr ha, infDist_plane a t ha c]
  ring


@[simp] theorem sphereCoefficientNormal_euclidean (c : Euclidean n) (r : ℝ) (x : Euclidean n) :
    sphereCoefficientNormal (euclideanSphereCoefficients c r) x = x - c := by
  simp [sphereCoefficientNormal, euclideanSphereCoefficients]

@[simp] theorem sphereCoefficientNormal_plane (a : Euclidean n) (t : ℝ) (x : Euclidean n) :
    sphereCoefficientNormal (planeCoefficients a t) x = -a := by
  simp [sphereCoefficientNormal, planeCoefficients]

/-- The normals in the sphere-angle formula are the ordinary radius vectors. -/
theorem inversiveProduct_sphere_sphere_eq_abs_cos_angle [NeZero n] (c d x : Euclidean n)
    (r t : ℝ) (hr : 0 < r) (ht : 0 < t) (hxr : dist x c = r) (hxt : dist x d = t) :
    inversiveProduct (euclideanGeneralizedSphere c r hr) (euclideanGeneralizedSphere d t ht) =
      |Real.cos (angle (x - c) (x - d))| := by
  have hxS : (x : ExtendedEuclidean n) ∈ extendedSphere c r := ⟨x, hxr, rfl⟩
  have hxT : (x : ExtendedEuclidean n) ∈ extendedSphere d t := ⟨x, hxt, rfl⟩
  have h := inversiveProduct_eq_abs_cos_angle (euclideanGeneralizedSphere c r hr)
    (euclideanGeneralizedSphere d t ht) (euclideanSphereCoefficients c r) (euclideanSphereCoefficients d t)
    (sphereCoefficients_ne_zero_of_pos _ (sphereDiscriminant_pos_euclidean c r hr))
    (sphereCoefficients_ne_zero_of_pos _ (sphereDiscriminant_pos_euclidean d t ht))
    (sphereCoefficientCarrier_euclidean c r hr) (sphereCoefficientCarrier_euclidean d t ht) x hxS hxT
  simpa only [sphereCoefficientNormal_euclidean] using h

/-- Positive spheres with the orthogonality distance relation meet with perpendicular radius vectors. -/
theorem exists_orthogonal_sphere_intersection (hn : 2 ≤ n) (c d : Euclidean n) (r t : ℝ)
    (hr : 0 < r) (ht : 0 < t) (hcd : ‖d - c‖ ^ 2 = r ^ 2 + t ^ 2) :
    ∃ x : Euclidean n, dist x c = r ∧ dist x d = t ∧ inner ℝ (x - c) (x - d) = 0 := by
  have hv : d - c ≠ 0 := by intro hz; rw [hz, norm_zero, zero_pow (by decide)] at hcd; nlinarith
  have hnorm : ‖d - c‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  obtain ⟨v, hv0, hvorth⟩ := exists_nonzero_normal_orthogonal hn (d - c) hv
  let w := ‖v‖⁻¹ • v
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (norm_pos_iff.mpr hv0))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)
  have hwortho : inner ℝ (d - c) w = 0 := by
    dsimp [w]
    rw [real_inner_smul_right, real_inner_comm v (d - c), hvorth, mul_zero]
  let α := r ^ 2 / ‖d - c‖ ^ 2
  let β := r * t / ‖d - c‖
  let x := c + α • (d - c) + β • w
  have hxc : x - c = α • (d - c) + β • w := by dsimp [x]; abel
  have hxd : x - d = (α - 1) • (d - c) + β • w := by dsimp [x]; module
  have hmulr : r ^ 2 * ‖d - c‖ ^ 2 = r ^ 2 * (r ^ 2 + t ^ 2) := congrArg (fun z : ℝ => r ^ 2 * z) hcd
  have hmult : t ^ 2 * ‖d - c‖ ^ 2 = t ^ 2 * (r ^ 2 + t ^ 2) := congrArg (fun z : ℝ => t ^ 2 * z) hcd
  have hmuln : ‖d - c‖ ^ 2 * ‖d - c‖ ^ 2 = ‖d - c‖ ^ 2 * (r ^ 2 + t ^ 2) :=
    congrArg (fun z : ℝ => ‖d - c‖ ^ 2 * z) hcd
  have hsqc : ‖x - c‖ ^ 2 = r ^ 2 := by
    rw [hxc, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left,
      real_inner_smul_right, hwortho, mul_zero, hw, mul_one, add_zero]
    dsimp [α, β]
    field_simp
    nlinarith
  have hsqd : ‖x - d‖ ^ 2 = t ^ 2 := by
    rw [hxd, norm_add_sq_real]
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left,
      real_inner_smul_right, hwortho, mul_zero, hw, mul_one, add_zero]
    dsimp [α, β]
    field_simp
    nlinarith
  refine ⟨x, ?_, ?_, ?_⟩
  · rw [dist_eq_norm]; nlinarith [norm_nonneg (x - c)]
  · rw [dist_eq_norm]; nlinarith [norm_nonneg (x - d)]
  · have hsub : (x - c) - (x - d) = d - c := by abel
    have h := norm_sub_sq_real (x - c) (x - d)
    rw [hsub, hsqc, hsqd, hcd] at h
    linarith


/-- A sphere whose centre is on a plane meets that plane when the ambient dimension is at least two. -/
theorem exists_sphere_plane_intersection_of_center_mem (hn : 2 ≤ n) (c a : Euclidean n)
    (r t : ℝ) (hr : 0 < r) (ha : a ≠ 0) (hc : inner ℝ c a = t) :
    ∃ x : Euclidean n, dist x c = r ∧ inner ℝ x a = t := by
  obtain ⟨v, hv, hva⟩ := exists_nonzero_normal_orthogonal hn a ha
  let x := c + (r / ‖v‖) • v
  refine ⟨x, ?_, ?_⟩
  · rw [dist_eq_norm]
    change ‖c + (r / ‖v‖) • v - c‖ = r
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos (div_pos hr (norm_pos_iff.mpr hv))]
    exact div_mul_cancel₀ r (norm_ne_zero_iff.mpr hv)
  · change inner ℝ (c + (r / ‖v‖) • v) a = t
    rw [inner_add_left, real_inner_smul_left, hva, mul_zero, add_zero, hc]

/-- Two planes with perpendicular nonzero normals have a finite common point. -/
theorem exists_plane_plane_intersection_of_inner_eq_zero (a b : Euclidean n) (r t : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : inner ℝ a b = 0) :
    ∃ x : Euclidean n, inner ℝ x a = r ∧ inner ℝ x b = t := by
  let x := (r / ‖a‖ ^ 2) • a + (t / ‖b‖ ^ 2) • b
  have hba : inner ℝ b a = 0 := by rw [real_inner_comm a b, hab]
  refine ⟨x, ?_, ?_⟩
  · change inner ℝ ((r / ‖a‖ ^ 2) • a + (t / ‖b‖ ^ 2) • b) a = r
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hba, mul_zero, add_zero]
    exact div_mul_cancel₀ r (pow_ne_zero _ (norm_ne_zero_iff.mpr ha))
  · change inner ℝ ((r / ‖a‖ ^ 2) • a + (t / ‖b‖ ^ 2) • b) b = t
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_self_eq_norm_sq, hab, mul_zero, zero_add]
    exact div_mul_cancel₀ t (pow_ne_zero _ (norm_ne_zero_iff.mpr hb))

/-- Vanishing inversive product forces an actual finite intersection, with dimension at least two. -/
theorem exists_finite_intersection_of_inversiveProduct_zero (hn : 2 ≤ n) (S T : GeneralizedSphere n)
    (hzero : inversiveProduct S T = 0) :
    ∃ x : Euclidean n, (x : ExtendedEuclidean n) ∈ S.val ∧ (x : ExtendedEuclidean n) ∈ T.val := by
  let : NeZero n := ⟨by omega⟩
  rcases S.property with ⟨c, r, hr, hS⟩ | ⟨a, u, ha, hS⟩
  · have heS : S = euclideanGeneralizedSphere c r hr := Subtype.ext hS
    rcases T.property with ⟨d, t, ht, hT⟩ | ⟨a, t, ha, hT⟩
    · have heT : T = euclideanGeneralizedSphere d t ht := Subtype.ext hT
      rw [heS, heT, inversiveProduct_sphere_sphere] at hzero
      have hz := abs_eq_zero.mp hzero
      have hnum := (div_eq_zero_iff.mp hz).resolve_right (by positivity : 2 * r * t ≠ 0)
      have hcd : ‖d - c‖ ^ 2 = r ^ 2 + t ^ 2 := by rw [norm_sub_rev]; linarith
      obtain ⟨x, hx, hy, _⟩ := exists_orthogonal_sphere_intersection hn c d r t hr ht hcd
      rw [hS, hT]
      exact ⟨x, ⟨x, hx, rfl⟩, ⟨x, hy, rfl⟩⟩
    · have heT : T = planeGeneralizedSphere a t ha := Subtype.ext hT
      rw [heS, heT, inversiveProduct_sphere_plane] at hzero
      have hz := (div_eq_zero_iff.mp hzero).resolve_right (mul_ne_zero hr.ne' (norm_ne_zero_iff.mpr ha))
      have hc : inner ℝ c a = t := sub_eq_zero.mp (abs_eq_zero.mp hz)
      obtain ⟨x, hx, hy⟩ := exists_sphere_plane_intersection_of_center_mem hn c a r t hr ha hc
      rw [hS, hT]
      exact ⟨x, ⟨x, hx, rfl⟩, Or.inr ⟨x, hy, rfl⟩⟩
  · have heS : S = planeGeneralizedSphere a u ha := Subtype.ext hS
    rcases T.property with ⟨c, r, hr, hT⟩ | ⟨b, t, hb, hT⟩
    · have heT : T = euclideanGeneralizedSphere c r hr := Subtype.ext hT
      rw [heS, heT, inversiveProduct_comm, inversiveProduct_sphere_plane] at hzero
      have hz := (div_eq_zero_iff.mp hzero).resolve_right (mul_ne_zero hr.ne' (norm_ne_zero_iff.mpr ha))
      have hc : inner ℝ c a = u := sub_eq_zero.mp (abs_eq_zero.mp hz)
      obtain ⟨x, hx, hy⟩ := exists_sphere_plane_intersection_of_center_mem hn c a r u hr ha hc
      rw [hS, hT]
      exact ⟨x, Or.inr ⟨x, hy, rfl⟩, ⟨x, hx, rfl⟩⟩
    · have heT : T = planeGeneralizedSphere b t hb := Subtype.ext hT
      rw [heS, heT, inversiveProduct_plane_plane] at hzero
      have hz := (div_eq_zero_iff.mp hzero).resolve_right
        (mul_ne_zero (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hb))
      obtain ⟨x, hx, hy⟩ := exists_plane_plane_intersection_of_inner_eq_zero a b u t ha hb (abs_eq_zero.mp hz)
      rw [hS, hT]
      exact ⟨x, Or.inr ⟨x, hx, rfl⟩, Or.inr ⟨x, hy, rfl⟩⟩

/-- Geometric orthogonality means a finite intersection with perpendicular normal directions. -/
def GeneralizedSpheresOrthogonal (S T : GeneralizedSphere n) : Prop :=
  ∃ x : Euclidean n, (x : ExtendedEuclidean n) ∈ S.val ∧ (x : ExtendedEuclidean n) ∈ T.val ∧
    inner ℝ (sphereCoefficientNormal (generalizedSphereCoefficients S) x)
      (sphereCoefficientNormal (generalizedSphereCoefficients T) x) = 0

/-- Geometric perpendicularity of generalized spheres is exactly vanishing inversive product. -/
theorem generalizedSpheresOrthogonal_iff_inversiveProduct_eq_zero (hn : 2 ≤ n) (S T : GeneralizedSphere n) :
    GeneralizedSpheresOrthogonal S T ↔ inversiveProduct S T = 0 := by
  let : NeZero n := ⟨by omega⟩
  have hnormal (x : Euclidean n) (hxS : (x : ExtendedEuclidean n) ∈ S.val)
      (hxT : (x : ExtendedEuclidean n) ∈ T.val) :=
    inversiveProduct_eq_zero_iff_normals_orthogonal S T (generalizedSphereCoefficients S)
      (generalizedSphereCoefficients T)
      (sphereCoefficients_ne_zero_of_pos _ (generalizedSphereCoefficients_pos S))
      (sphereCoefficients_ne_zero_of_pos _ (generalizedSphereCoefficients_pos T))
      (generalizedSphereCoefficients_carrier S) (generalizedSphereCoefficients_carrier T) x hxS hxT
  constructor
  · rintro ⟨x, hxS, hxT, horth⟩
    exact (hnormal x hxS hxT).mpr horth
  · intro hz
    obtain ⟨x, hxS, hxT⟩ := exists_finite_intersection_of_inversiveProduct_zero hn S T hz
    exact ⟨x, hxS, hxT, (hnormal x hxS hxT).mp hz⟩


/-- The ordinary angle between two plane normals gives the inversive product even when their only intersection is infinity. -/
theorem inversiveProduct_plane_plane_eq_abs_cos_angle [NeZero n] (a b : Euclidean n) (r t : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    inversiveProduct (planeGeneralizedSphere a r ha) (planeGeneralizedSphere b t hb) =
      |Real.cos (angle a b)| := by
  rw [inversiveProduct_plane_plane a b r t ha hb, cos_angle, abs_div,
    abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]

/-- For a sphere and plane the normals are its radius vector and the plane normal up to sign. -/
theorem inversiveProduct_sphere_plane_eq_abs_cos_angle [NeZero n] (c a x : Euclidean n)
    (r t : ℝ) (hr : 0 < r) (ha : a ≠ 0) (hxr : dist x c = r) (hxt : inner ℝ x a = t) :
    inversiveProduct (euclideanGeneralizedSphere c r hr) (planeGeneralizedSphere a t ha) =
      |Real.cos (angle (x - c) (-a))| := by
  have hxS : (x : ExtendedEuclidean n) ∈ extendedSphere c r := ⟨x, hxr, rfl⟩
  have hxT : (x : ExtendedEuclidean n) ∈ plane a t := Or.inr ⟨x, hxt, rfl⟩
  have h := inversiveProduct_eq_abs_cos_angle (euclideanGeneralizedSphere c r hr)
    (planeGeneralizedSphere a t ha) (euclideanSphereCoefficients c r) (planeCoefficients a t)
    (sphereCoefficients_ne_zero_of_pos _ (sphereDiscriminant_pos_euclidean c r hr))
    (sphereCoefficients_ne_zero_of_pos _ (sphereDiscriminant_pos_plane a t ha))
    (sphereCoefficientCarrier_euclidean c r hr) (sphereCoefficientCarrier_plane a t) x hxS hxT
  simpa only [sphereCoefficientNormal_euclidean, sphereCoefficientNormal_plane] using h

/-- Geometric orthogonality can equivalently be expressed by an actual right angle of the normal directions. -/
theorem generalizedSpheresOrthogonal_iff_normal_angle (S T : GeneralizedSphere n) :
    GeneralizedSpheresOrthogonal S T ↔
      ∃ x : Euclidean n, (x : ExtendedEuclidean n) ∈ S.val ∧ (x : ExtendedEuclidean n) ∈ T.val ∧
        angle (sphereCoefficientNormal (generalizedSphereCoefficients S) x)
          (sphereCoefficientNormal (generalizedSphereCoefficients T) x) = Real.pi / 2 := by
  simp only [GeneralizedSpheresOrthogonal, inner_eq_zero_iff_angle_eq_pi_div_two]

/-- Actual Möbius transformations preserve geometric orthogonality of generalized spheres. -/
theorem GeneralizedSpheresOrthogonal.image [NeZero n] (hn : 2 ≤ n) (S T : GeneralizedSphere n)
    (hST : GeneralizedSpheresOrthogonal S T) (g : ExtendedHomeomorph n) (hg : g ∈ generalMobiusGroup n) :
    GeneralizedSpheresOrthogonal (generalizedSphereImage g hg S) (generalizedSphereImage g hg T) := by
  rw [generalizedSpheresOrthogonal_iff_inversiveProduct_eq_zero hn] at hST ⊢
  rw [generalMobius_preservesInversiveProduct g hg, hST]

end LowDimensionalTopology.Geometry.Inversive
