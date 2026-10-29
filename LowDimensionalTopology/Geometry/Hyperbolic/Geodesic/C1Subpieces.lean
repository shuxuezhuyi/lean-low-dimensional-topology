module

public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.LocalExtension
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfPlaneDisk

/-!
# Literal C1 lengths of unit-speed geodesic subpieces

Two actual parameter values normalize an arbitrary unit-speed geodesic to an
exponential vertical line. Two-time uniqueness identifies the complete
parameter, so the existing native C1 constructors give every affine subpiece
with its exact original parametrization and literal weighted length.
-/

public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups

namespace LowDimensionalTopology.Geometry.Hyperbolic

/-- Every complete unit-speed geodesic has an actual positive real normalizer
and an additive parameter constant. The original orientation is retained. -/
theorem IsHGeodesicParam.exists_normalizer_param
    {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ) :
    ∃ (g : GL (Fin 2) ℝ) (c : ℝ), 0 < g.val.det ∧
      ∀ t : ℝ, γ t = normalizerGeodesic g (t + c) := by
  have hne : γ 0 ≠ γ 1 := hγ.1.injective.ne (by norm_num)
  obtain ⟨_a, _b, g, _ha, _hb, _hab, hg, _hga, _hgb, hz, hw, hi⟩ :=
    exists_ordered_ideal_normalizer (γ 0) (γ 1) hne
  let c : ℝ := Real.log (g • γ 0).im
  have hlog : Real.log (g • γ 1).im - Real.log (g • γ 0).im = 1 := by
    have hd : dist (g • γ 0) (g • γ 1) = 1 := by
      rw [realGL_distance, hγ.1.dist_eq]
      norm_num [Real.dist_eq]
    rwa [metric_vertical_distance_of_im_le (hz.trans hw.symm) hi.le] at hd
  let η : ℝ → ℍ := fun t => normalizerGeodesic g (t + c)
  have hshift : Isometry (fun t : ℝ => t + c) := by
    apply Isometry.of_dist_eq
    intro s t
    simp only [Real.dist_eq, add_sub_add_right_eq_sub]
  have hrange : range η = range (normalizerGeodesic g) := by
    ext z
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t + c, rfl⟩
    · rintro ⟨t, rfl⟩
      refine ⟨t - c, ?_⟩
      change normalizerGeodesic g (t - c + c) = normalizerGeodesic g t
      rw [sub_add_cancel]
  have hη : IsHGeodesicParam η :=
    ⟨(normalizerGeodesic_isometry g hg).comp hshift,
      hrange.symm ▸ normalizerGeodesic_isHLine g hg⟩
  have hη0 : η 0 = γ 0 := by
    change normalizerGeodesic g (0 + c) = γ 0
    rw [zero_add]
    exact normalizerGeodesic_parameter g (γ 0) hz
  have hη1 : η 1 = γ 1 := by
    have hc : 1 + c = Real.log (g • γ 1).im := by dsimp only [c]; linarith
    change normalizerGeodesic g (1 + c) = γ 1
    rw [hc]
    exact normalizerGeodesic_parameter g (γ 1) hw
  have heq : γ = η := hγ.eq_of_eq_two_times hη (by norm_num) hη0.symm hη1.symm
  exact ⟨g, c, hg, fun t => congrFun heq t⟩

/-- An arbitrary unit-speed geodesic segment has a native C1 affine traversal
on `[0,1]`, pointwise in the original parameter, of literal length `b-a`. -/
theorem IsHGeodesicParam.exists_c1_affine_piece
    {γ : ℝ → ℍ} (hγ : IsHGeodesicParam γ) (a b : ℝ) (hab : a ≤ b) :
    ∃ c : C1CurvePiece, c.a = 0 ∧ c.b = 1 ∧
      (∀ t : ℝ, c.curve t = γ (a + (b - a) * t)) ∧ c.length = b - a := by
  obtain ⟨g, r, hg, hparam⟩ := hγ.exists_normalizer_param
  let v := verticalPiece 0 (Real.exp (a + r)) (Real.exp (b + r))
    (Real.exp_pos _) (Real.exp_pos _)
  let c := v.mapGLPos g⁻¹ (gl_pos_inverse g hg)
  refine ⟨c, rfl, rfl, ?_, ?_⟩
  · intro t
    rw [hparam]
    change g⁻¹ • v.curve t = g⁻¹ • imaginaryAxisParam (a + (b - a) * t + r)
    apply congrArg (fun z : ℍ => g⁻¹ • z)
    apply UpperHalfPlane.ext
    rw [imaginaryAxisParam_coe]
    change (0 : ℂ) + (Real.exp
      (Real.log (Real.exp (a + r)) + t *
        (Real.log (Real.exp (b + r)) - Real.log (Real.exp (a + r)))) : ℂ) * Complex.I =
      (Real.exp (a + (b - a) * t + r) : ℂ) * Complex.I
    simp only [Real.log_exp, zero_add]
    apply congrArg (fun u : ℝ => (Real.exp u : ℂ) * Complex.I)
    ring
  · change (v.mapGLPos g⁻¹ (gl_pos_inverse g hg)).length = b - a
    rw [C1CurvePiece.mapGLPos_length]
    change (verticalPiece 0 (Real.exp (a + r)) (Real.exp (b + r))
      (Real.exp_pos _) (Real.exp_pos _)).length = b - a
    rw [verticalPiece_length, Real.log_exp, Real.log_exp]
    have he : b + r - (a + r) = b - a := by ring
    rw [he, abs_of_nonneg (sub_nonneg.mpr hab)]

end LowDimensionalTopology.Geometry.Hyperbolic
