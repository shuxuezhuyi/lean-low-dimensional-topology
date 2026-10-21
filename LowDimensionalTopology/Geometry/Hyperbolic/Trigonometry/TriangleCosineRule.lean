/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.Gram
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleTrigonometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.IsometryClassification

@[expose] public section
open Set InnerProductGeometry
open scoped UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- A coordinate vector pointing along the actual h-geodesic from the first point to the second. -/
def hyperbolicDirection (z w : ℍ) : ℂ :=
  ⟨2 * z.im * (w.re - z.re),(w.re - z.re) ^ 2 + w.im ^ 2 - z.im ^ 2⟩

theorem HRayAt.longitudinal_forward_pos {z w : ℍ} (R : HRayAt z)
    (hw : w ∈ R.val) (hwz : w ≠ z) :
    0 < R.tangentSign * (R.longitudinal w - R.longitudinal z) := by
  have horder := (R.mem_iff_longitudinal (R.subset_support hw)).mp hw
  have hne : R.longitudinal w ≠ R.longitudinal z := fun h =>
    hwz (R.supportLine.longitudinal_injective_on_carrier (R.subset_support hw)
      R.start_mem_support h)
  by_cases ht : R.longitudinal z < R.longitudinal R.directionPoint
  · rw [ite_eq_left ht] at horder
    rw [HRayAt.tangentSign,ite_eq_left ht,one_mul]
    exact sub_pos.mpr (lt_of_le_of_ne horder (Ne.symm hne))
  · rw [ite_eq_right ht] at horder
    rw [HRayAt.tangentSign,ite_eq_right ht,neg_one_mul]
    linarith [lt_of_le_of_ne horder hne]

theorem hyperbolicDirection_pos_smul_tangent {z w : ℍ} (R : HRayAt z)
    (hw : w ∈ R.val) (hwz : w ≠ z) :
    ∃ r : ℝ, 0 < r ∧ hyperbolicDirection z w = r • R.tangentVector := by
  have hpos := R.longitudinal_forward_pos hw hwz
  have hz := R.start_mem_support
  have hwL := R.subset_support hw
  cases hL : R.supportLine with
  | vertical a =>
    rw [hL] at hz hwL
    have hzr : z.re = a := hz
    have hwr : w.re = a := hwL
    have he : R.longitudinal w - R.longitudinal z = w.im - z.im := by
      simp only [HRayAt.longitudinal,hL,HalfPlaneLine.longitudinal,Complex.imCLM_apply,
        UpperHalfPlane.coe_im]
    rw [he] at hpos
    refine ⟨R.tangentSign * (w.im - z.im) * (w.im + z.im),
      mul_pos hpos (add_pos w.im_pos z.im_pos),?_⟩
    calc
      _ = ((w.im - z.im) * (w.im + z.im)) • R.supportLine.tangentAt z := by
        apply Complex.ext <;>
          simp [hyperbolicDirection,hL,HalfPlaneLine.tangentAt,hwr,hzr]
        ring
      _ = ((w.im - z.im) * (w.im + z.im)) • (R.tangentSign • R.tangentVector) := by
        rw [R.tangentSign_smul_vector]
      _ = _ := by rw [smul_smul]; congr 1; ring
  | circle c r hr =>
    rw [hL] at hz hwL
    have hz' := norm_sub_real_eq_radius_sq hz
    have hw' := norm_sub_real_eq_radius_sq hwL
    have he : R.longitudinal w - R.longitudinal z = z.re - w.re := by
      simp only [HRayAt.longitudinal,hL,HalfPlaneLine.longitudinal,neg_apply,
        Complex.reCLM_apply,UpperHalfPlane.coe_re]
      ring
    rw [he] at hpos
    refine ⟨2 * (R.tangentSign * (z.re - w.re)),mul_pos (by norm_num) hpos,?_⟩
    calc
      _ = (2 * (z.re - w.re)) • R.supportLine.tangentAt z := by
        apply Complex.ext
        · simp only [hyperbolicDirection,hL,HalfPlaneLine.tangentAt,Complex.smul_re,
            smul_eq_mul,Complex.mul_re,Complex.sub_im,Complex.ofReal_im,Complex.I_re,
            Complex.I_im,zero_mul,one_mul,sub_zero,UpperHalfPlane.coe_im,zero_sub]
          ring
        · simp only [hyperbolicDirection,hL,HalfPlaneLine.tangentAt,Complex.smul_im,
            smul_eq_mul,Complex.mul_im,Complex.sub_re,Complex.ofReal_re,Complex.I_re,
            Complex.I_im,zero_mul,one_mul,UpperHalfPlane.coe_re]
          nlinarith only [hz',hw']
      _ = (2 * (z.re - w.re)) • (R.tangentSign • R.tangentVector) := by
        rw [R.tangentSign_smul_vector]
      _ = _ := by rw [smul_smul]; congr 1; ring

theorem hyperbolicDirection_norm (z w : ℍ) :
    ‖hyperbolicDirection z w‖ = 2 * z.im * w.im * Real.sinh (dist z w) := by
  have hD : 2 * z.im * w.im ≠ 0 := ne_of_gt (by positivity)
  have hc : 2 * z.im * w.im * Real.cosh (dist z w) =
      (z.re - w.re) ^ 2 + z.im ^ 2 + w.im ^ 2 := by
    rw [UpperHalfPlane.cosh_dist',mul_div_cancel₀ _ hD]
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (by positivity)
    (Real.sinh_nonneg_iff.mpr dist_nonneg))).mp
  calc
    _ = ((z.re - w.re) ^ 2 + z.im ^ 2 + w.im ^ 2) ^ 2 -
        (2 * z.im * w.im) ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq]
      simp only [hyperbolicDirection,Complex.normSq_apply]
      ring
    _ = (2 * z.im * w.im) ^ 2 * (Real.cosh (dist z w) ^ 2 - 1) := by
      rw [← hc]
      ring
    _ = _ := by rw [← Real.sinh_sq]; ring

theorem hyperbolicDirection_inner (z w u : ℍ) :
    inner ℝ (hyperbolicDirection z w) (hyperbolicDirection z u) =
      (2 * z.im * w.im) * (2 * z.im * u.im) *
        (Real.cosh (dist z w) * Real.cosh (dist z u) - Real.cosh (dist w u)) := by
  rw [_root_.LowDimensionalTopology.Geometry.Euclidean.complex_real_inner_coordinates]
  simp only [hyperbolicDirection]
  rw [UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist',UpperHalfPlane.cosh_dist']
  field_simp [z.im_ne_zero,w.im_ne_zero,u.im_ne_zero]
  ring

theorem hInteriorAngleMeasure_eq_direction {z w u : ℍ} (R S : HRayAt z)
    (hw : w ∈ R.val) (hwz : w ≠ z) (hu : u ∈ S.val) (huz : u ≠ z) :
    hInteriorAngleMeasure R S = angle (hyperbolicDirection z w) (hyperbolicDirection z u) := by
  obtain ⟨r,hr,he⟩ := hyperbolicDirection_pos_smul_tangent R hw hwz
  obtain ⟨s,hs,hf⟩ := hyperbolicDirection_pos_smul_tangent S hu huz
  rw [he,hf,angle_smul_left_of_pos _ _ hr,angle_smul_right_of_pos _ _ hs]
  rfl

/-- The hyperbolic cosine relation for two actual rays and points on their forward branches. -/
theorem hInteriorAngleMeasure_cosine_rule {z w u : ℍ} (R S : HRayAt z)
    (hw : w ∈ R.val) (hwz : w ≠ z) (hu : u ∈ S.val) (huz : u ≠ z) :
    Real.cosh (dist w u) = Real.cosh (dist z w) * Real.cosh (dist z u) -
      Real.sinh (dist z w) * Real.sinh (dist z u) * Real.cos (hInteriorAngleMeasure R S) := by
  have hc := cos_angle_mul_norm_mul_norm (hyperbolicDirection z w) (hyperbolicDirection z u)
  rw [← hInteriorAngleMeasure_eq_direction R S hw hwz hu huz,hyperbolicDirection_norm,
    hyperbolicDirection_norm,hyperbolicDirection_inner] at hc
  have hd : (2 * z.im * w.im) * (2 * z.im * u.im) ≠ 0 := by positivity
  have hrel : Real.sinh (dist z w) * Real.sinh (dist z u) *
      Real.cos (hInteriorAngleMeasure R S) =
      Real.cosh (dist z w) * Real.cosh (dist z u) - Real.cosh (dist w u) := by
    apply mul_left_cancel₀ hd
    calc
      _ = Real.cos (hInteriorAngleMeasure R S) *
          ((2 * z.im * w.im * Real.sinh (dist z w)) *
          (2 * z.im * u.im * Real.sinh (dist z u))) := by ring
      _ = _ := hc
  linarith

/-- The first cosine rule for an actual finite triangle. -/
theorem HTriangle.cosine_rule_I (T : HTriangle) :
    Real.cosh T.lengthC = Real.cosh T.lengthA * Real.cosh T.lengthB -
      Real.sinh T.lengthA * Real.sinh T.lengthB * Real.cos T.gamma := by
  have h := hInteriorAngleMeasure_cosine_rule T.rayCA T.rayCB T.a_mem_rayCA
    T.c_ne_a.symm T.b_mem_rayCB T.b_ne_c
  simpa only [HTriangle.lengthA,HTriangle.lengthB,HTriangle.lengthC,HTriangle.gamma,
    dist_comm,mul_comm] using h

theorem DiscTriangle.cosine_rule_I (T : DiscTriangle) :
    Real.cosh T.lengthC = Real.cosh T.lengthA * Real.cosh T.lengthB -
      Real.sinh T.lengthA * Real.sinh T.lengthB * Real.cos T.gamma := by
  rw [T.lengths_eq_halfPlane.1,T.lengths_eq_halfPlane.2.1,T.lengths_eq_halfPlane.2.2,
    T.angles_eq_halfPlane.2.2]
  exact T.toHalfPlane.cosine_rule_I

theorem HTriangle.cosine_rule_A (T : HTriangle) :
    Real.cosh T.lengthA = Real.cosh T.lengthB * Real.cosh T.lengthC -
      Real.sinh T.lengthB * Real.sinh T.lengthC * Real.cos T.alpha := by
  have h := hInteriorAngleMeasure_cosine_rule T.rayAB T.rayAC T.b_mem_rayAB
    T.a_ne_b.symm T.c_mem_rayAC T.c_ne_a
  simpa only [HTriangle.lengthA,HTriangle.lengthB,HTriangle.lengthC,HTriangle.alpha,
    dist_comm,mul_comm] using h

theorem HTriangle.cosine_rule_B (T : HTriangle) :
    Real.cosh T.lengthB = Real.cosh T.lengthC * Real.cosh T.lengthA -
      Real.sinh T.lengthC * Real.sinh T.lengthA * Real.cos T.beta := by
  have h := hInteriorAngleMeasure_cosine_rule T.rayBC T.rayBA T.c_mem_rayBC
    T.b_ne_c.symm T.a_mem_rayBA T.a_ne_b
  simpa only [HTriangle.lengthA,HTriangle.lengthB,HTriangle.lengthC,HTriangle.beta,
    hInteriorAngleMeasure_comm,dist_comm,mul_comm] using h

theorem angle_eq_of_hyperbolic_cosine_rule {a b c θ η : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hθ : θ ∈ Icc (0 : ℝ) Real.pi) (hη : η ∈ Icc (0 : ℝ) Real.pi)
    (hcosθ : Real.cosh a = Real.cosh b * Real.cosh c -
      Real.sinh b * Real.sinh c * Real.cos θ)
    (hcosη : Real.cosh a = Real.cosh b * Real.cosh c -
      Real.sinh b * Real.sinh c * Real.cos η) : θ = η := by
  apply Real.injOn_cos hθ hη
  apply mul_left_cancel₀ (mul_ne_zero (ne_of_gt (Real.sinh_pos_iff.mpr hb))
    (ne_of_gt (Real.sinh_pos_iff.mpr hc)))
  linarith only [hcosθ,hcosη]

theorem HTriangle.angles_eq_of_lengths_eq (T S : HTriangle)
    (hA : T.lengthA = S.lengthA) (hB : T.lengthB = S.lengthB)
    (hC : T.lengthC = S.lengthC) : T.alpha = S.alpha ∧ T.beta = S.beta ∧ T.gamma = S.gamma := by
  have hα := S.cosine_rule_A
  have hβ := S.cosine_rule_B
  have hγ := S.cosine_rule_I
  rw [← hA,← hB,← hC] at hα hβ hγ
  refine ⟨angle_eq_of_hyperbolic_cosine_rule T.lengths_pos.2.1 T.lengths_pos.2.2
    ⟨T.angles_mem_Ioo.1.1.le,T.angles_mem_Ioo.1.2.le⟩
    ⟨S.angles_mem_Ioo.1.1.le,S.angles_mem_Ioo.1.2.le⟩ T.cosine_rule_A hα,
    angle_eq_of_hyperbolic_cosine_rule T.lengths_pos.2.2 T.lengths_pos.1
    ⟨T.angles_mem_Ioo.2.1.1.le,T.angles_mem_Ioo.2.1.2.le⟩
    ⟨S.angles_mem_Ioo.2.1.1.le,S.angles_mem_Ioo.2.1.2.le⟩ T.cosine_rule_B hβ,
    angle_eq_of_hyperbolic_cosine_rule T.lengths_pos.1 T.lengths_pos.2.1
    ⟨T.angles_mem_Ioo.2.2.1.le,T.angles_mem_Ioo.2.2.2.le⟩
    ⟨S.angles_mem_Ioo.2.2.1.le,S.angles_mem_Ioo.2.2.2.le⟩ T.cosine_rule_I hγ⟩

/-- An arbitrary distance-preserving map sends actual noncollinear vertices to such vertices. -/
def HTriangle.mapIsometry (T : HTriangle) (f : ℍ → ℍ) (hf : Isometry f) : HTriangle where
  a := f T.a
  b := f T.b
  c := f T.c
  noncollinear := by
    obtain ⟨g,rfl⟩ := isometry_exists_realGL hf
    rintro ⟨L,ha,hb,hc⟩
    obtain ⟨M,hM⟩ := realGL_image_hLine g⁻¹ L
    apply T.noncollinear
    refine ⟨M,?_,?_,?_⟩
    all_goals rw [← hM]
    · exact ⟨g • T.a,ha,inv_smul_smul g T.a⟩
    · exact ⟨g • T.b,hb,inv_smul_smul g T.b⟩
    · exact ⟨g • T.c,hc,inv_smul_smul g T.c⟩

theorem HTriangle.mapIsometry_lengths (T : HTriangle) (f : ℍ → ℍ) (hf : Isometry f) :
    (T.mapIsometry f hf).lengthA = T.lengthA ∧
      (T.mapIsometry f hf).lengthB = T.lengthB ∧
        (T.mapIsometry f hf).lengthC = T.lengthC :=
  ⟨hf.dist_eq _ _,hf.dist_eq _ _,hf.dist_eq _ _⟩

/-- The actual three tangent angles are preserved by every metric isometry, without an onto hypothesis. -/
theorem HTriangle.mapIsometry_angles (T : HTriangle) (f : ℍ → ℍ) (hf : Isometry f) :
    (T.mapIsometry f hf).alpha = T.alpha ∧
      (T.mapIsometry f hf).beta = T.beta ∧
        (T.mapIsometry f hf).gamma = T.gamma :=
  (T.mapIsometry f hf).angles_eq_of_lengths_eq T (T.mapIsometry_lengths f hf).1
    (T.mapIsometry_lengths f hf).2.1 (T.mapIsometry_lengths f hf).2.2

end
end LowDimensionalTopology.Geometry.Hyperbolic
