/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.DiscRays
public import Mathlib.Tactic

/-!
# Actual isometries of the hyperbolic plane
-/

@[expose] public section
open Set Filter
open scoped UpperHalfPlane MatrixGroups OnePoint Topology ComplexConjugate Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
noncomputable section

/-- A genuine upper half-plane coordinate probe. -/
def metricProbe (x y : ℝ) (hy : 0 < y) : ℍ := ⟨⟨x,y⟩,hy⟩

/-- Positive real dilation represented by an actual determinant-one matrix. -/
def verticalDilationSL (k : ℝ) (hk : 0 < k) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![Real.sqrt k,0;0,1 / Real.sqrt k],by
    simp [Matrix.det_fin_two, (Real.sqrt_pos.mpr hk).ne']⟩

theorem verticalDilationSL_coe (k : ℝ) (hk : 0 < k) (z : ℍ) :
    ((verticalDilationSL k hk • z : ℍ) : ℂ) = (k : ℂ) * z := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  have hs : (Real.sqrt k : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hk).ne'
  have hsq : (Real.sqrt k : ℂ) ^ 2 = (k : ℂ) := by exact_mod_cast Real.sq_sqrt hk.le
  simp only [Algebra.algebraMap_self_apply]
  change ((Real.sqrt k : ℂ) * z + ((0 : ℝ) : ℂ)) /
    (((0 : ℝ) : ℂ) * z + ((1 / Real.sqrt k : ℝ) : ℂ)) = _
  push_cast
  simp only [zero_mul, zero_add, add_zero]
  field_simp
  linear_combination z * hsq

theorem verticalDilationSL_re (k : ℝ) (hk : 0 < k) (z : ℍ) :
    (verticalDilationSL k hk • z).re = k * z.re := by
  change (((verticalDilationSL k hk • z : ℍ) : ℂ)).re = _
  rw [verticalDilationSL_coe]
  simp

theorem verticalDilationSL_im (k : ℝ) (hk : 0 < k) (z : ℍ) :
    (verticalDilationSL k hk • z).im = k * z.im := by
  change (((verticalDilationSL k hk • z : ℍ) : ℂ)).im = _
  rw [verticalDilationSL_coe]
  simp

/-- Equal distances to the first two imaginary-axis probes determine height and squared real part. -/
theorem equal_two_probe_distances {z w : ℍ}
    (h₁ : dist z (metricProbe 0 1 (by norm_num)) = dist w (metricProbe 0 1 (by norm_num)))
    (h₂ : dist z (metricProbe 0 2 (by norm_num)) = dist w (metricProbe 0 2 (by norm_num))) :
    z.im = w.im ∧ z.re ^ 2 = w.re ^ 2 := by
  have h₁' := congrArg Real.cosh h₁
  have h₂' := congrArg Real.cosh h₂
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist'] at h₁' h₂'
  norm_num [metricProbe] at h₁' h₂'
  have hA := (div_eq_div_iff (by positivity : 2 * z.im ≠ 0)
    (by positivity : 2 * w.im ≠ 0)).mp h₁'
  have hB := (div_eq_div_iff (by positivity : 2 * z.im * 2 ≠ 0)
    (by positivity : 2 * w.im * 2 ≠ 0)).mp h₂'
  have hy : z.im = w.im := by nlinarith
  refine ⟨hy,?_⟩
  rw [hy] at hA
  nlinarith [w.im_pos]

/-- Three genuine noncollinear probes determine every point by distance. -/
theorem equal_three_probe_distances {z w : ℍ}
    (h₁ : dist z (metricProbe 0 1 (by norm_num)) = dist w (metricProbe 0 1 (by norm_num)))
    (h₂ : dist z (metricProbe 0 2 (by norm_num)) = dist w (metricProbe 0 2 (by norm_num)))
    (h₃ : dist z (metricProbe 1 1 (by norm_num)) = dist w (metricProbe 1 1 (by norm_num))) :
    z = w := by
  obtain ⟨hy,hx2⟩ := equal_two_probe_distances h₁ h₂
  have h₃' := congrArg Real.cosh h₃
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist'] at h₃'
  norm_num [metricProbe] at h₃'
  rw [hy] at h₃'
  have he := (div_left_inj' (by positivity : 2 * w.im ≠ 0)).mp h₃'
  apply UpperHalfPlane.ext
  apply Complex.ext
  · change z.re = w.re
    nlinarith
  · exact hy

/-- An actual isometry fixing three noncollinear probes is the identity. -/
theorem isometry_eq_id_of_fix_three {f : ℍ → ℍ} (hf : Isometry f)
    (h₁ : f (metricProbe 0 1 (by norm_num)) = metricProbe 0 1 (by norm_num))
    (h₂ : f (metricProbe 0 2 (by norm_num)) = metricProbe 0 2 (by norm_num))
    (h₃ : f (metricProbe 1 1 (by norm_num)) = metricProbe 1 1 (by norm_num)) : f = id := by
  funext z
  change f z = z
  apply equal_three_probe_distances
  · simpa only [h₁] using hf.dist_eq z (metricProbe 0 1 (by norm_num))
  · simpa only [h₂] using hf.dist_eq z (metricProbe 0 2 (by norm_num))
  · simpa only [h₃] using hf.dist_eq z (metricProbe 1 1 (by norm_num))

/-- A two-point normalization of any genuine isometry uses an actual determinant-one matrix. -/
theorem exists_sl2_normalized_isometry (f : ℍ → ℍ) (hf : Isometry f) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      g • f (metricProbe 0 1 (by norm_num)) = metricProbe 0 1 (by norm_num) ∧
      g • f (metricProbe 0 2 (by norm_num)) = metricProbe 0 2 (by norm_num) := by
  let p := metricProbe 0 1 (by norm_num)
  let q := metricProbe 0 2 (by norm_num)
  have hpq : p ≠ q := by
    intro h
    have he := congrArg UpperHalfPlane.im h
    norm_num [p,q,metricProbe] at he
  obtain ⟨s,hs₁,hs₂,hslt⟩ := exists_sl2_ordered_imaginary (f p) (f q) (hf.injective.ne hpq)
  have hd : dist (s • f p) (s • f q) = dist p q := by
    rw [(isometry_smul ℍ s).dist_eq, hf.dist_eq]
  have hc := congrArg Real.cosh hd
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist'] at hc
  rw [hs₁,hs₂] at hc
  norm_num [p,q,metricProbe] at hc
  have hcross := (div_eq_div_iff (by positivity : 2 * (s • f p).im * (s • f q).im ≠ 0)
    (by norm_num : (4:ℝ) ≠ 0)).mp hc
  change ((s • f p).im ^ 2 + (s • f q).im ^ 2) * 4 =
    5 * (2 * (s • f p).im * (s • f q).im) at hcross
  have hfactor : ((s • f q).im - 2 * (s • f p).im) *
      (2 * (s • f q).im - (s • f p).im) = 0 := by nlinarith
  have hheight : (s • f q).im = 2 * (s • f p).im := by
    rcases mul_eq_zero.mp hfactor with h | h
    · linarith
    · linarith [(s • f p).im_pos]
  let k := verticalDilationSL (1 / (s • f p).im) (by positivity)
  refine ⟨k * s,?_,?_⟩
  · apply UpperHalfPlane.ext
    apply Complex.ext
    · change ((k * s) • f p).re = 0
      rw [mul_smul, verticalDilationSL_re, hs₁, mul_zero]
    · change ((k * s) • f p).im = 1
      rw [mul_smul, verticalDilationSL_im]
      exact one_div_mul_cancel (s • f p).im_ne_zero
  · apply UpperHalfPlane.ext
    apply Complex.ext
    · change ((k * s) • f q).re = 0
      rw [mul_smul, verticalDilationSL_re, hs₂, mul_zero]
    · change ((k * s) • f q).im = 2
      rw [mul_smul, verticalDilationSL_im, hheight]
      field_simp

/-- Fixing the two imaginary probes leaves only identity and reflection in their h-line. -/
theorem isometry_eq_id_or_axisReflection {f : ℍ → ℍ} (hf : Isometry f)
    (h₁ : f (metricProbe 0 1 (by norm_num)) = metricProbe 0 1 (by norm_num))
    (h₂ : f (metricProbe 0 2 (by norm_num)) = metricProbe 0 2 (by norm_num)) :
    f = id ∨ f = (UpperHalfPlane.J • · : ℍ → ℍ) := by
  let q := metricProbe 1 1 (by norm_num)
  have he := equal_two_probe_distances
    (by simpa only [h₁] using hf.dist_eq q (metricProbe 0 1 (by norm_num)))
    (by simpa only [h₂] using hf.dist_eq q (metricProbe 0 2 (by norm_num)))
  have hy : (f q).im = 1 := he.1
  have hx : (f q).re ^ 2 = 1 := by
    have h := he.2
    change (f q).re ^ 2 = 1 ^ 2 at h
    rw [one_pow] at h
    exact h
  have hor : (f q).re = 1 ∨ (f q).re = -1 := by
    have : ((f q).re - 1) * ((f q).re + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp this with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  rcases hor with hp | hm
  · apply Or.inl
    apply isometry_eq_id_of_fix_three hf h₁ h₂
    apply UpperHalfPlane.ext
    exact Complex.ext hp hy
  · have hJ (z : ℍ) : ((UpperHalfPlane.J • z : ℍ) : ℂ) = -conj (z : ℂ) :=
      UpperHalfPlane.coe_J_smul z
    have hfix (x y : ℝ) (hy : 0 < y) (hx : x = 0) :
        UpperHalfPlane.J • metricProbe x y hy = metricProbe x y hy := by
      apply UpperHalfPlane.ext
      rw [hJ]
      apply Complex.ext <;> simp [metricProbe,hx]
    have hid : (fun z : ℍ => UpperHalfPlane.J • f z) = id := by
      apply isometry_eq_id_of_fix_three ((realGL_isometry UpperHalfPlane.J).comp hf)
      · dsimp only [Function.comp_def]
        rw [h₁]
        exact hfix 0 1 (by norm_num) rfl
      · dsimp only [Function.comp_def]
        rw [h₂]
        exact hfix 0 2 (by norm_num) rfl
      · dsimp only [Function.comp_def]
        apply UpperHalfPlane.ext
        rw [hJ]
        apply Complex.ext
        · change -(f q).re = 1
          linarith
        · rw [Complex.neg_im, Complex.conj_im, neg_neg]
          change (f q).im = 1
          exact hy
    apply Or.inr
    funext z
    have he' := congrFun hid z
    have hh := congrArg (fun u : ℍ => UpperHalfPlane.J • u) he'
    simpa only [smul_smul, ← pow_two, UpperHalfPlane.J_sq, one_smul, id_eq] using hh

/-- Every actual distance-preserving map of H is an actual real fractional-linear action.
Surjectivity is a conclusion, so no unproved onto assumption is used in the classification. -/
theorem isometry_exists_realGL {f : ℍ → ℍ} (hf : Isometry f) :
    ∃ g : GL (Fin 2) ℝ, f = (g • · : ℍ → ℍ) := by
  obtain ⟨s,hs₁,hs₂⟩ := exists_sl2_normalized_isometry f hf
  have hnormal := isometry_eq_id_or_axisReflection
    ((isometry_smul ℍ s).comp hf) hs₁ hs₂
  let S := Matrix.SpecialLinearGroup.mapGL ℝ s
  rcases hnormal with hi | hj
  · refine ⟨S⁻¹,?_⟩
    funext z
    have he := congrFun hi z
    change S • f z = z at he
    exact (eq_inv_smul_iff.mpr he)
  · refine ⟨S⁻¹ * UpperHalfPlane.J,?_⟩
    funext z
    rw [mul_smul]
    have he := congrFun hj z
    change S • f z = UpperHalfPlane.J • z at he
    exact (eq_inv_smul_iff.mpr he)

theorem isometry_iff_realGL (f : ℍ → ℍ) :
    Isometry f ↔ ∃ g : GL (Fin 2) ℝ, f = (g • · : ℍ → ℍ) := by
  constructor
  · exact isometry_exists_realGL
  · rintro ⟨g,rfl⟩
    exact realGL_isometry g

theorem Isometry.halfPlane_surjective {f : ℍ → ℍ} (hf : Isometry f) : Function.Surjective f := by
  obtain ⟨g,rfl⟩ := isometry_exists_realGL hf
  exact MulAction.surjective g

/-- An isometry is either a determinant-one action or that action after the actual axis reflection. -/
theorem isometry_exists_sl2_or_reflected {f : ℍ → ℍ} (hf : Isometry f) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      f = (s • · : ℍ → ℍ) ∨ f = (s • · : ℍ → ℍ) ∘ (UpperHalfPlane.J • · : ℍ → ℍ) := by
  obtain ⟨s,hs₁,hs₂⟩ := exists_sl2_normalized_isometry f hf
  have hnormal := isometry_eq_id_or_axisReflection ((isometry_smul ℍ s).comp hf) hs₁ hs₂
  refine ⟨s⁻¹,?_⟩
  rcases hnormal with hi | hj
  · apply Or.inl
    funext z
    have he := congrFun hi z
    exact eq_inv_smul_iff.mpr he
  · apply Or.inr
    funext z
    have he := congrFun hj z
    exact eq_inv_smul_iff.mpr he

/-- Finite words in the actual h-line reflections, including the empty word. -/
inductive HReflectionWord : (ℍ → ℍ) → Prop
  | identity : HReflectionWord id
  | cons (L : HalfPlaneLine) {f : ℍ → ℍ} : HReflectionWord f → HReflectionWord (L.reflection ∘ f)

theorem HReflectionWord.reflection (L : HalfPlaneLine) : HReflectionWord L.reflection := by
  simpa only [Function.comp_id] using _root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.cons L _root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.identity

theorem HReflectionWord.comp {f g : ℍ → ℍ} (hf : HReflectionWord f) (hg : HReflectionWord g) :
    HReflectionWord (f ∘ g) := by
  induction hf with
  | identity => simpa only [Function.id_comp] using hg
  | cons L h ih => simpa only [Function.comp_assoc] using _root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.cons L ih

theorem HReflectionWord.isometry {f : ℍ → ℍ} (hf : HReflectionWord f) : Isometry f := by
  induction hf with
  | identity => exact isometry_id
  | cons L h ih => exact L.reflection_isometry.comp ih

/-- Translation is the composition of two actual vertical-line reflections. -/
theorem translation_eq_two_reflections (t : ℝ) :
    (t +ᵥ · : ℍ → ℍ) = (HalfPlaneLine.vertical (t / 2)).reflection ∘
      (HalfPlaneLine.vertical 0).reflection := by
  funext z
  apply UpperHalfPlane.ext
  change ((t +ᵥ z : ℍ) : ℂ) = (verticalReflection (t / 2) (verticalReflection 0 z) : ℂ)
  rw [UpperHalfPlane.coe_vadd, verticalReflection_coe, verticalReflection_coe]
  simp only [Complex.ofReal_zero, mul_zero, zero_sub, map_neg, Complex.conj_conj, sub_neg_eq_add]
  push_cast
  ring

/-- Dilation is the composition of two actual concentric semicircle reflections. -/
theorem dilation_eq_two_reflections (u : {x : ℝ // 0 < x}) :
    (u • · : ℍ → ℍ) = (HalfPlaneLine.circle 0 (Real.sqrt u) (Real.sqrt_pos.mpr u.2)).reflection ∘
      (HalfPlaneLine.circle 0 1 (by norm_num)).reflection := by
  funext z
  apply UpperHalfPlane.ext
  change ((u • z : ℍ) : ℂ) = (circleReflection 0 (Real.sqrt u) _ (circleReflection 0 1 _ z) : ℂ)
  rw [UpperHalfPlane.coe_pos_real_smul, circleReflection_coe, circleReflection_coe]
  have hsq : (Real.sqrt u : ℂ) ^ 2 = (u : ℝ) := by exact_mod_cast Real.sq_sqrt u.2.le
  simp only [Complex.ofReal_zero, Complex.ofReal_one, zero_add, sub_zero, one_pow,
    map_div₀, map_one, Complex.conj_conj, hsq]
  rw [Complex.real_smul]
  field_simp

/-- The standard reciprocal map is the unit-circle reflection after the axis reflection. -/
theorem reciprocal_eq_two_reflections :
    (ModularGroup.S • · : ℍ → ℍ) = (HalfPlaneLine.circle 0 1 (by norm_num)).reflection ∘
      (HalfPlaneLine.vertical 0).reflection := by
  funext z
  apply UpperHalfPlane.ext
  change ((ModularGroup.S • z : ℍ) : ℂ) = (circleReflection 0 1 _ (verticalReflection 0 z) : ℂ)
  rw [UpperHalfPlane.modular_S_smul, circleReflection_coe, verticalReflection_coe]
  simp [map_neg, inv_neg]

theorem axisReflection_eq_reflection :
    (UpperHalfPlane.J • · : ℍ → ℍ) = (HalfPlaneLine.vertical 0).reflection := by
  funext z
  apply UpperHalfPlane.ext
  change ((UpperHalfPlane.J • z : ℍ) : ℂ) = (verticalReflection 0 z : ℂ)
  rw [UpperHalfPlane.coe_J_smul, verticalReflection_coe]
  simp

theorem HReflectionWord.translation (t : ℝ) : HReflectionWord (t +ᵥ · : ℍ → ℍ) := by
  rw [translation_eq_two_reflections]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.reflection
    _).comp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.reflection _)

theorem HReflectionWord.dilation (u : {x : ℝ // 0 < x}) : HReflectionWord (u • · : ℍ → ℍ) := by
  rw [dilation_eq_two_reflections]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.reflection
    _).comp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.reflection _)

theorem HReflectionWord.reciprocal : HReflectionWord (ModularGroup.S • · : ℍ → ℍ) := by
  rw [reciprocal_eq_two_reflections]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.reflection
    _).comp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.reflection _)

theorem HReflectionWord.sl2 (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    HReflectionWord (s • · : ℍ → ℍ) := by
  by_cases hc : s 1 0 = 0
  · obtain ⟨u,v,he⟩ := UpperHalfPlane.exists_SL2_smul_eq_of_apply_zero_one_eq_zero s hc
    rw [he]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.translation
      v).comp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.dilation u)
  · obtain ⟨u,v,w,he⟩ := UpperHalfPlane.exists_SL2_smul_eq_of_apply_zero_one_ne_zero s hc
    rw [he]
    exact ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.translation w).comp
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.reciprocal).comp
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.translation v).comp
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.dilation u))

/-- All genuine hyperbolic isometries are finite words in actual h-line reflections. -/
theorem isometry_iff_reflectionWord (f : ℍ → ℍ) : Isometry f ↔ HReflectionWord f := by
  constructor
  · intro hf
    obtain ⟨s,hs | hs⟩ := isometry_exists_sl2_or_reflected hf
    · rw [hs]
      exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.sl2 s
    · rw [hs,axisReflection_eq_reflection]
      exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.sl2
        s).comp (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.reflection _)
  · exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.HReflectionWord.isometry

/-- The explicit positive-determinant and conjugate branches. -/
theorem isometry_complex_formula {f : ℍ → ℍ} (hf : Isometry f) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀ z : ℍ, (f z : ℂ) = ((s 0 0 : ℂ) * z + s 0 1) / ((s 1 0 : ℂ) * z + s 1 1)) ∨
      (∀ z : ℍ, (f z : ℂ) = ((s 0 0 : ℂ) * (-conj (z : ℂ)) + s 0 1) /
        ((s 1 0 : ℂ) * (-conj (z : ℂ)) + s 1 1)) := by
  obtain ⟨s,hs | hs⟩ := isometry_exists_sl2_or_reflected hf
  · refine ⟨s,Or.inl (fun z => ?_)⟩
    rw [hs, UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [Algebra.algebraMap_self_apply]
  · refine ⟨s,Or.inr (fun z => ?_)⟩
    rw [hs, Function.comp_apply, UpperHalfPlane.coe_specialLinearGroup_apply,
      UpperHalfPlane.coe_J_smul]
    simp only [Algebra.algebraMap_self_apply]

theorem realGL_axis_preimage_isHLine (g : GL (Fin 2) ℝ) :
    IsHalfPlaneHLine {z : ℍ | (g • z).re = 0} := by
  by_cases hg : 0 < g.val.det
  · exact realMobius_axis_preimage_isHLine g hg
  · have hneg : g.val.det < 0 := lt_of_le_of_ne (not_lt.mp hg) g.det_ne_zero
    have hJ : UpperHalfPlane.J.val.det = -1 := by simp [UpperHalfPlane.J, Matrix.det_fin_two]
    have hpos : 0 < (UpperHalfPlane.J * g).val.det := by
      change 0 < (UpperHalfPlane.J.val * g.val).det
      rw [Matrix.det_mul,hJ]
      linarith
    have he : {z : ℍ | (g • z).re = 0} = {z : ℍ | ((UpperHalfPlane.J * g) • z).re = 0} := by
      ext z
      simp only [mem_ofPred, mul_smul, imaginaryAxisReflection_re, neg_eq_zero]
    rw [he]
    exact realMobius_axis_preimage_isHLine _ hpos

/-- Any actual real fractional-linear action sends a genuine Euclidean h-line to another. -/
theorem realGL_image_hLine (g : GL (Fin 2) ℝ) (L : HalfPlaneLine) :
    ∃ M : HalfPlaneLine, (g • · : ℍ → ℍ) '' L.carrier = M.carrier := by
  obtain ⟨h,_,hL⟩ := L.exists_normalizer
  have he : (g • · : ℍ → ℍ) '' L.carrier = {z : ℍ | ((h * g⁻¹) • z).re = 0} := by
    rw [hL]
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      change (h • w).re = 0 at hw
      change ((h * g⁻¹) • (g • w)).re = 0
      simpa only [mul_smul, inv_smul_smul] using hw
    · intro hz
      change ((h * g⁻¹) • z).re = 0 at hz
      refine ⟨g⁻¹ • z,?_,smul_inv_smul g z⟩
      change (h • (g⁻¹ • z)).re = 0
      simpa only [mul_smul] using hz
  obtain ⟨M,hM⟩ := exists_halfPlaneLine_of_isHLine (realGL_axis_preimage_isHLine (h * g⁻¹))
  exact ⟨M,he.trans hM.symm⟩

/-- A genuine isometry preserves complete h-lines as actual point sets. -/
theorem Isometry.halfPlane_image_hLine {f : ℍ → ℍ} (hf : Isometry f) (L : HalfPlaneLine) :
    ∃ M : HalfPlaneLine, f '' L.carrier = M.carrier := by
  obtain ⟨g,rfl⟩ := isometry_exists_realGL hf
  exact realGL_image_hLine g L

/-- A genuine isometry preserves the actual closed h-segment. -/
theorem Isometry.image_closedHSegment {f : ℍ → ℍ} (hf : Isometry f) {z w : ℍ} (hzw : z ≠ w) :
    f '' closedHSegment z w = closedHSegment (f z) (f w) := by
  ext u
  constructor
  · rintro ⟨v,hv,rfl⟩
    apply mem_closedHSegment_of_dist_triangle_eq (hf.injective.ne hzw)
    simpa only [hf.dist_eq] using dist_triangle_eq_of_mem_closedHSegment hv
  · intro hu
    obtain ⟨v,rfl⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_surjective hf u
    refine ⟨v,?_,rfl⟩
    apply mem_closedHSegment_of_dist_triangle_eq hzw
    simpa only [hf.dist_eq] using dist_triangle_eq_of_mem_closedHSegment hu

/-- A genuine isometry preserves betweenness, including the strict endpoint exclusions. -/
theorem Isometry.hBetween_iff {f : ℍ → ℍ} (hf : Isometry f) {z w u : ℍ} (hzw : z ≠ w) :
    HBetween (f z) (f u) (f w) ↔ HBetween z u w := by
  rw [hBetween_iff_dist_triangle_eq (hf.injective.ne hzw),hBetween_iff_dist_triangle_eq hzw]
  simp only [hf.dist_eq,hf.injective.ne_iff]

/-- A genuine isometry preserves the actual open h-segment. -/
theorem Isometry.image_openHSegment {f : ℍ → ℍ} (hf : Isometry f) {z w : ℍ} (hzw : z ≠ w) :
    f '' openHSegment z w = openHSegment (f z) (f w) := by
  ext u
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.hBetween_iff hf hzw).mpr hv
  · intro hu
    obtain ⟨v,rfl⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_surjective hf u
    exact ⟨v,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.hBetween_iff hf hzw).mp hu,rfl⟩

/-- The actual Cayley conjugate of a native disc map. -/
def discMapConjugate (f : 𝔻 → 𝔻) : ℍ → ℍ := discToHalfPlane ∘ f ∘ halfPlaneToDisc

theorem disc_isometry_conjugate {f : 𝔻 → 𝔻} :
    letI := discHyperbolicMetric
    Isometry f → Isometry (discMapConjugate f) := by
  let := discHyperbolicMetric
  intro hf
  exact inverse_cayley_isometry.comp (hf.comp cayley_isometry)

theorem disc_map_cayley_image (f : 𝔻 → 𝔻) (S : Set ℍ) :
    f '' (halfPlaneToDisc '' S) = halfPlaneToDisc '' (discMapConjugate f '' S) := by
  rw [image_image,image_image]
  apply Set.image_congr
  intro z _
  exact (halfPlaneToDisc_discToHalfPlane (f (halfPlaneToDisc z))).symm

/-- Every genuine native disc isometry preserves native Euclidean h-line carriers. -/
theorem disc_isometry_image_hLine {f : 𝔻 → 𝔻} :
    letI := discHyperbolicMetric
    Isometry f → ∀ L : DiscLine, ∃ M : DiscLine, f '' L.carrier = M.carrier := by
  let := discHyperbolicMetric
  intro hf L
  obtain ⟨M,hM⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine (disc_isometry_conjugate hf) L.toHalfPlane
  refine ⟨M.toDiscLine,?_⟩
  rw [L.carrier_eq_cayley_image_halfPlane,disc_map_cayley_image,hM,
    HalfPlaneLine.toDiscLine_carrier,HalfPlaneLine.discCarrier_eq_cayley_image]

/-- Native disc isometries preserve the actual closed segment point set. -/
theorem disc_isometry_image_closedHSegment {f : 𝔻 → 𝔻} :
    letI := discHyperbolicMetric
    Isometry f → ∀ {z w : 𝔻}, z ≠ w →
      f '' closedDiscHSegment z w = closedDiscHSegment (f z) (f w) := by
  let := discHyperbolicMetric
  intro hf z w hzw
  have hH := disc_isometry_conjugate hf
  have hZW := discToHalfPlane_injective.ne hzw
  rw [closedDiscHSegment_eq_cayley_image,disc_map_cayley_image,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.image_closedHSegment hH hZW,closedDiscHSegment_eq_cayley_image]
  simp only [discMapConjugate,Function.comp_def,halfPlaneToDisc_discToHalfPlane]

/-- Native disc isometries preserve the actual open segment point set. -/
theorem disc_isometry_image_openHSegment {f : 𝔻 → 𝔻} :
    letI := discHyperbolicMetric
    Isometry f → ∀ {z w : 𝔻}, z ≠ w →
      f '' openDiscHSegment z w = openDiscHSegment (f z) (f w) := by
  let := discHyperbolicMetric
  intro hf z w hzw
  have hH := disc_isometry_conjugate hf
  have hZW := discToHalfPlane_injective.ne hzw
  rw [openDiscHSegment_eq_cayley_image,disc_map_cayley_image,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.Isometry.image_openHSegment hH hZW,openDiscHSegment_eq_cayley_image]
  simp only [discMapConjugate,Function.comp_def,halfPlaneToDisc_discToHalfPlane]

/-- The same segment preservation holds for the source's native component-based segment. -/
theorem disc_isometry_image_nativeClosedSegment {f : 𝔻 → 𝔻} :
    letI := discHyperbolicMetric
    Isometry f → ∀ (L M : DiscLine) {z w : 𝔻}, z ≠ w → z ∈ L.carrier → w ∈ L.carrier →
      f '' L.carrier = M.carrier →
      f '' nativeDiscClosedSegment L z w = nativeDiscClosedSegment M (f z) (f w) := by
  let := discHyperbolicMetric
  intro hf L M z w hzw hz hw hLM
  have hfz : f z ∈ M.carrier := hLM ▸ mem_image_of_mem f hz
  have hfw : f w ∈ M.carrier := hLM ▸ mem_image_of_mem f hw
  rw [nativeDiscClosedSegment_eq L hzw hz hw,
    nativeDiscClosedSegment_eq M (hf.injective.ne hzw) hfz hfw]
  exact disc_isometry_image_closedHSegment hf hzw

/-- Native disc isometries preserve strict h-betweenness. -/
theorem disc_isometry_between_iff {f : 𝔻 → 𝔻} :
    letI := discHyperbolicMetric
    Isometry f → ∀ {z w u : 𝔻}, z ≠ w →
      (DiscHBetween (f z) (f u) (f w) ↔ DiscHBetween z u w) := by
  let := discHyperbolicMetric
  intro hf z w u hzw
  change f u ∈ openDiscHSegment (f z) (f w) ↔ u ∈ openDiscHSegment z w
  rw [← disc_isometry_image_openHSegment hf hzw]
  constructor
  · rintro ⟨v,hv,he⟩
    exact hf.injective he ▸ hv
  · exact fun hu => mem_image_of_mem f hu

/-- Native component-defined open segments are preserved as actual point sets. -/
theorem disc_isometry_image_nativeOpenSegment {f : 𝔻 → 𝔻} :
    letI := discHyperbolicMetric
    Isometry f → ∀ (L M : DiscLine) {z w : 𝔻}, z ≠ w → z ∈ L.carrier → w ∈ L.carrier →
      f '' L.carrier = M.carrier →
      f '' nativeDiscOpenSegment L z w = nativeDiscOpenSegment M (f z) (f w) := by
  let := discHyperbolicMetric
  intro hf L M z w hzw hz hw hLM
  have hfz : f z ∈ M.carrier := hLM ▸ mem_image_of_mem f hz
  have hfw : f w ∈ M.carrier := hLM ▸ mem_image_of_mem f hw
  rw [nativeDiscOpenSegment_eq L hzw hz hw,
    nativeDiscOpenSegment_eq M (hf.injective.ne hzw) hfz hfw]
  exact disc_isometry_image_openHSegment hf hzw

end
end LowDimensionalTopology.Geometry.Hyperbolic
