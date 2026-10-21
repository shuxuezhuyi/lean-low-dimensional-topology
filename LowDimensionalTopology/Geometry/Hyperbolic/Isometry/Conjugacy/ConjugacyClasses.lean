module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalReconstruction
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ParabolicReflectionPencils
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.NativeLineReflections
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianNormalization
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Actual real conformal conjugacy multiplies a nonzero parabolic parameter by a positive square. -/
theorem hTranslationSL_conjugacy_parameter (C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (p q : ℝ) (hp : p ≠ 0)
    (hconj : realSLMobius (C * hTranslationSL p * C⁻¹) = realSLMobius (hTranslationSL q)) :
    ∃ a : ℝ, a ≠ 0 ∧ q = a ^ 2 * p := by
  have hcomm : realSLMobius (C * hTranslationSL p) = realSLMobius (hTranslationSL q * C) := by
    calc
      realSLMobius (C * hTranslationSL p) = realSLMobius (C * hTranslationSL p * C⁻¹) * realSLMobius C := by
        rw [← map_mul]
        congr 1
        group
      _ = realSLMobius (hTranslationSL q) * realSLMobius C := by rw [hconj]
      _ = realSLMobius (hTranslationSL q * C) := (map_mul realSLMobius _ _).symm
  have hdet := C.property
  rw [Matrix.det_fin_two] at hdet
  rcases (realSLMobius_eq_iff_sign _ _).mp hcomm with h | h
  · have h11 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) ℝ => A 1 1) h
    have h01 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) ℝ => A 0 1) h
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hTranslationSL] at h11 h01
    have hc : C 1 0 = 0 := h11.resolve_right hp
    rw [hc, mul_zero, sub_zero] at hdet
    have ha : C 0 0 ≠ 0 := by intro ha; rw [ha, zero_mul] at hdet; norm_num at hdet
    have hparam : C 0 0 * p = q * C 1 1 := by linarith
    refine ⟨C 0 0, ha, ?_⟩
    calc
      q = q * (C 0 0 * C 1 1) := by rw [hdet, mul_one]
      _ = C 0 0 * (C 0 0 * p) := by rw [hparam]; ring
      _ = C 0 0 ^ 2 * p := by ring
  · have h10 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) ℝ => A 1 0) h
    have h00 := congrArg (fun A : Matrix.SpecialLinearGroup (Fin 2) ℝ => A 0 0) h
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.mul_apply, Fin.sum_univ_two, hTranslationSL] at h10 h00
    have hc : C 1 0 = 0 := by linarith
    have ha : C 0 0 = 0 := by rw [hc, mul_zero, add_zero] at h00; linarith
    rw [ha, hc] at hdet
    norm_num at hdet

/-- The genuine positive real diagonal conjugacy of parabolic translations. -/
theorem verticalDilationSL_hTranslation_conjugation (k : ℝ) (hk : 0 < k) (p : ℝ) :
    verticalDilationSL k hk * hTranslationSL p * (verticalDilationSL k hk)⁻¹ = hTranslationSL (k * p) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hs : Real.sqrt k ≠ 0 := (Real.sqrt_pos.mpr hk).ne'
  have hsq := Real.sq_sqrt hk.le
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      verticalDilationSL, hTranslationSL]
  field_simp [hs]
  rw [hsq]
  ring

/-- The oriented parabolic classes are exactly the two signs of the translation parameter. -/
theorem hTranslationSL_conformal_conjugacy_iff (p q : ℝ) (hp : p ≠ 0) :
    (∃ C : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      realSLMobius (C * hTranslationSL p * C⁻¹) = realSLMobius (hTranslationSL q)) ↔ 0 < p * q := by
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨a, ha, rfl⟩ := hTranslationSL_conjugacy_parameter C p q hp hC
    have hpos := mul_pos (sq_pos_of_ne_zero ha) (sq_pos_of_ne_zero hp)
    nlinarith
  · intro hpq
    have hk : 0 < q / p := by
      have h : 0 < q * p := by simpa only [mul_comm] using hpq
      exact (div_pos_iff).mpr ((mul_pos_iff.mp h))
    refine ⟨verticalDilationSL (q / p) hk, ?_⟩
    rw [verticalDilationSL_hTranslation_conjugation]
    congr 2
    field_simp

/-- The genuine conformal real-matrix homomorphism into the native hyperbolic isometry group. -/
def halfPlaneConformalIsometryHom : Matrix.SpecialLinearGroup (Fin 2) ℝ →* (ℍ ≃ᵢ ℍ) where
  toFun := hSLIsometry
  map_one' := by apply IsometryEquiv.ext; intro z; exact one_smul (Matrix.SpecialLinearGroup (Fin 2) ℝ) z
  map_mul' A B := by apply IsometryEquiv.ext; intro z; exact mul_smul A B z

theorem hSLIsometry_eq_iff_projective (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    hSLIsometry A = hSLIsometry B ↔ realSLMobius A = realSLMobius B := by
  constructor
  · intro h
    apply realSLMobius_ext_action
    intro z
    exact congrArg (fun e : ℍ ≃ᵢ ℍ => e z) h
  · intro h
    rcases (realSLMobius_eq_iff_sign A B).mp h with h | h
    · rw [h]
    · rw [h, hSLIsometry_neg]

/-- A real conformal conjugator yields actual conjugacy in the full native isometry group. -/
theorem hSLIsometry_isConj_of_real_conjugator (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : realSLMobius (C * A * C⁻¹) = realSLMobius B) :
    IsConj (hSLIsometry A) (hSLIsometry B) := by
  have he : halfPlaneConformalIsometryHom (C * A * C⁻¹) = halfPlaneConformalIsometryHom B :=
    (hSLIsometry_eq_iff_projective _ _).mpr h
  rw [map_mul, map_mul, map_inv] at he
  exact isConj_iff.mpr ⟨halfPlaneConformalIsometryHom C, he⟩

/-- A genuine geometric reflection bundled as a native hyperbolic isometry. -/
def HalfPlaneLine.reflectionIsometry (L : HalfPlaneLine) : ℍ ≃ᵢ ℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneLineReflectionIsometry L

/-- The actual axis reflection interchanges the two oriented parabolic classes. -/
theorem hTranslationSL_axis_reflection_conjugation (p : ℝ) :
    HalfPlaneLine.reflectionIsometry (.vertical 0) * hSLIsometry (hTranslationSL p) *
      (HalfPlaneLine.reflectionIsometry (.vertical 0))⁻¹ = hSLIsometry (hTranslationSL (-p)) := by
  apply IsometryEquiv.ext
  intro z
  apply UpperHalfPlane.ext
  change (verticalReflection 0 (hTranslationSL p • verticalReflection 0 z) : ℂ) =
    ((hTranslationSL (-p) • z : ℍ) : ℂ)
  rw [verticalReflection_coe, hTranslationSL_coe, verticalReflection_coe, hTranslationSL_coe]
  simp only [Complex.ofReal_zero, mul_zero, zero_sub, map_add, map_neg, Complex.conj_ofReal,
    Complex.conj_conj, Complex.ofReal_neg]
  ring

/-- All nonzero parabolic translations are conjugate in the full native isometry group. -/
theorem hTranslationSL_full_isConj (p q : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) :
    IsConj (hSLIsometry (hTranslationSL p)) (hSLIsometry (hTranslationSL q)) := by
  by_cases hpos : 0 < p * q
  · obtain ⟨C, hC⟩ := (hTranslationSL_conformal_conjugacy_iff p q hp).mpr hpos
    exact hSLIsometry_isConj_of_real_conjugator _ _ C hC
  · have hneg : 0 < p * (-q) := by
      have hne : p * q ≠ 0 := mul_ne_zero hp hq
      have hn : p * q < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hne
      nlinarith
    obtain ⟨C, hC⟩ := (hTranslationSL_conformal_conjugacy_iff p (-q) hp).mpr hneg
    have hfirst := hSLIsometry_isConj_of_real_conjugator _ _ C hC
    have hsecond : IsConj (hSLIsometry (hTranslationSL q)) (hSLIsometry (hTranslationSL (-q))) :=
      isConj_iff.mpr ⟨HalfPlaneLine.reflectionIsometry (.vertical 0), hTranslationSL_axis_reflection_conjugation q⟩
    exact hfirst.trans hsecond.symm

/-- Every original parabolic action is actually conjugate to a nonzero translation. -/
theorem hParabolic_conjugate_translation (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) :
    ∃ p : ℝ, p ≠ 0 ∧ IsConj (hSLIsometry A) (hSLIsometry (hTranslationSL p)) := by
  obtain ⟨C, p, hp, hC⟩ := realSLMobius_parabolic_normal_form A hA
  have he : realSLMobius (C * A * C⁻¹) = realSLMobius (hTranslationSL p) := by
    rcases hC with hC | hC
    · rw [hC]
    · rw [hC, realSLMobius_neg]
  exact ⟨p, hp, hSLIsometry_isConj_of_real_conjugator A _ C he⟩

/-- The full-isometry assertion for arbitrary original parabolic elements. -/
theorem hParabolic_full_isConj (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) (hB : Mobius.MobiusParabolic (realSLMobius B)) :
    IsConj (hSLIsometry A) (hSLIsometry B) := by
  obtain ⟨p, hp, hAp⟩ := hParabolic_conjugate_translation A hA
  obtain ⟨q, hq, hBq⟩ := hParabolic_conjugate_translation B hB
  exact (hAp.trans (hTranslationSL_full_isConj p q hp hq)).trans hBq.symm

/-- The actual subgroup of native hyperbolic isometries represented by real determinant-one maps. -/
def halfPlaneConformalIsometryGroup : Subgroup (ℍ ≃ᵢ ℍ) := halfPlaneConformalIsometryHom.range

/-- Original conformal actions bundled in their genuine native isometry subgroup. -/
def halfPlaneConformalElement : Matrix.SpecialLinearGroup (Fin 2) ℝ →* halfPlaneConformalIsometryGroup :=
  halfPlaneConformalIsometryHom.rangeRestrict

/-- Native subgroup conjugacy agrees exactly with actual real projective conjugacy. -/
theorem halfPlaneConformalElement_isConj_iff (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    IsConj (halfPlaneConformalElement A) (halfPlaneConformalElement B) ↔
      ∃ C : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        realSLMobius (C * A * C⁻¹) = realSLMobius B := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := isConj_iff.mp h
    obtain ⟨C, hC⟩ := halfPlaneConformalIsometryHom.rangeRestrict_surjective e
    have hCv : halfPlaneConformalIsometryHom C = e.val := congrArg Subtype.val hC
    have hev : e.val * halfPlaneConformalIsometryHom A * e.val⁻¹ = halfPlaneConformalIsometryHom B :=
      congrArg Subtype.val he
    rw [← hCv] at hev
    refine ⟨C, (hSLIsometry_eq_iff_projective _ _).mp ?_⟩
    change halfPlaneConformalIsometryHom (C * A * C⁻¹) = halfPlaneConformalIsometryHom B
    rw [map_mul, map_mul, map_inv]
    exact hev
  · rintro ⟨C, hC⟩
    apply isConj_iff.mpr
    refine ⟨halfPlaneConformalElement C, ?_⟩
    apply Subtype.ext
    change halfPlaneConformalIsometryHom C * halfPlaneConformalIsometryHom A *
      (halfPlaneConformalIsometryHom C)⁻¹ = halfPlaneConformalIsometryHom B
    rw [← map_inv, ← map_mul, ← map_mul]
    exact (hSLIsometry_eq_iff_projective _ _).mpr hC

/-- The sign classification holds inside the actual conformal native isometry group. -/
theorem hTranslationSL_oriented_isConj_iff (p q : ℝ) (hp : p ≠ 0) :
    IsConj (halfPlaneConformalElement (hTranslationSL p)) (halfPlaneConformalElement (hTranslationSL q)) ↔ 0 < p * q := by
  rw [halfPlaneConformalElement_isConj_iff]
  exact hTranslationSL_conformal_conjugacy_iff p q hp

/-- The two standard parabolic actions are genuinely distinct oriented conjugacy classes. -/
theorem hTranslationSL_opposite_oriented_not_isConj :
    ¬IsConj (halfPlaneConformalElement (hTranslationSL 1)) (halfPlaneConformalElement (hTranslationSL (-1))) := by
  rw [hTranslationSL_oriented_isConj_iff 1 (-1) one_ne_zero]
  norm_num

/-- Every original parabolic belongs to one of precisely the two oriented standard classes. -/
theorem hParabolic_oriented_two_classes (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) :
    IsConj (halfPlaneConformalElement A) (halfPlaneConformalElement (hTranslationSL 1)) ∨
      IsConj (halfPlaneConformalElement A) (halfPlaneConformalElement (hTranslationSL (-1))) := by
  obtain ⟨C, p, hp, hC⟩ := realSLMobius_parabolic_normal_form A hA
  have he : realSLMobius (C * A * C⁻¹) = realSLMobius (hTranslationSL p) := by
    rcases hC with hC | hC
    · rw [hC]
    · rw [hC, realSLMobius_neg]
  have hAp := (halfPlaneConformalElement_isConj_iff A (hTranslationSL p)).mpr ⟨C, he⟩
  by_cases hp0 : 0 < p
  · exact Or.inl (hAp.trans ((hTranslationSL_oriented_isConj_iff p 1 hp).mpr (by simpa only [mul_one] using hp0)))
  · have hpneg : p < 0 := lt_of_le_of_ne (le_of_not_gt hp0) hp
    exact Or.inr (hAp.trans ((hTranslationSL_oriented_isConj_iff p (-1) hp).mpr (by nlinarith)))

/-- Actual conjugation by the axis reflection, expressed as a real determinant-one matrix. -/
def hReflectedSL (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![A 0 0, -A 0 1; -A 1 0, A 1 1], by
    have hd := A.det_coe
    rw [Matrix.det_fin_two] at hd ⊢
    change A 0 0 * A 1 1 - (-A 0 1) * (-A 1 0) = 1
    simpa only [neg_mul_neg] using hd⟩

theorem hReflectedSL_trace (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.trace (hReflectedSL A).val = Matrix.trace A.val := by
  simp [Matrix.trace_fin_two, hReflectedSL]

theorem hReflectedSL_squaredTrace (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Mobius.mobiusSquaredTrace (realSLMobius (hReflectedSL A)) = Mobius.mobiusSquaredTrace (realSLMobius A) := by
  rw [realSLMobius_squaredTrace, realSLMobius_squaredTrace, hReflectedSL_trace]

theorem hReflectedSL_native_conjugation (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    HalfPlaneLine.reflectionIsometry (.vertical 0) * hSLIsometry A *
      (HalfPlaneLine.reflectionIsometry (.vertical 0))⁻¹ = hSLIsometry (hReflectedSL A) := by
  apply IsometryEquiv.ext
  intro z
  apply UpperHalfPlane.ext
  change (verticalReflection 0 (A • verticalReflection 0 z) : ℂ) = ((hReflectedSL A • z : ℍ) : ℂ)
  rw [verticalReflection_coe, UpperHalfPlane.coe_specialLinearGroup_apply, verticalReflection_coe,
    UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [Complex.ofReal_zero, mul_zero, zero_sub, map_div₀, map_add, map_mul,
    map_neg, Complex.conj_ofReal, Complex.conj_conj]
  change -(((A 0 0 : ℂ) * (-(z : ℂ)) + A 0 1) / ((A 1 0 : ℂ) * (-(z : ℂ)) + A 1 1)) =
    ((A 0 0 : ℂ) * (z : ℂ) + (-A 0 1 : ℝ)) / ((-A 1 0 : ℝ) * (z : ℂ) + A 1 1)
  rw [← neg_div]
  congr 1 <;> push_cast <;> ring

/-- The full native isometry group is generated by the genuine conformal subgroup and one reflection. -/
theorem halfPlane_native_isometry_cases (E : ℍ ≃ᵢ ℍ) :
    ∃ C : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      E = halfPlaneConformalIsometryHom C ∨
        E = halfPlaneConformalIsometryHom C * HalfPlaneLine.reflectionIsometry (.vertical 0) := by
  obtain ⟨C, hC | hC⟩ := isometry_exists_sl2_or_reflected E.isometry
  · exact ⟨C, Or.inl (IsometryEquiv.ext (fun z => congrFun hC z))⟩
  · rw [axisReflection_eq_reflection] at hC
    exact ⟨C, Or.inr (IsometryEquiv.ext (fun z => congrFun hC z))⟩

theorem nativeSL_conjugation_squaredTrace (A B C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : halfPlaneConformalIsometryHom C * hSLIsometry A * (halfPlaneConformalIsometryHom C)⁻¹ = hSLIsometry B) :
    Mobius.mobiusSquaredTrace (realSLMobius A) = Mobius.mobiusSquaredTrace (realSLMobius B) := by
  have he : halfPlaneConformalIsometryHom (C * A * C⁻¹) = halfPlaneConformalIsometryHom B := by
    rw [map_mul, map_mul, map_inv]
    exact h
  have hp := (hSLIsometry_eq_iff_projective _ _).mp he
  have ht := congrArg Mobius.mobiusSquaredTrace hp
  rw [map_mul, map_mul, map_inv, Mobius.mobiusSquaredTrace_conjugation] at ht
  exact ht

/-- Squared trace is invariant under the entire native isometry group, including reflections. -/
theorem hSLIsometry_isConj_squaredTrace (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : IsConj (hSLIsometry A) (hSLIsometry B)) :
    Mobius.mobiusSquaredTrace (realSLMobius A) = Mobius.mobiusSquaredTrace (realSLMobius B) := by
  obtain ⟨E, hE⟩ := isConj_iff.mp h
  obtain ⟨C, hC | hC⟩ := halfPlane_native_isometry_cases E
  · rw [hC] at hE
    exact nativeSL_conjugation_squaredTrace A B C hE
  · rw [hC] at hE
    have he : halfPlaneConformalIsometryHom C * hSLIsometry (hReflectedSL A) *
        (halfPlaneConformalIsometryHom C)⁻¹ = hSLIsometry B := by
      rw [← hReflectedSL_native_conjugation A]
      calc
        _ = (halfPlaneConformalIsometryHom C * HalfPlaneLine.reflectionIsometry (.vertical 0)) * hSLIsometry A *
          (halfPlaneConformalIsometryHom C * HalfPlaneLine.reflectionIsometry (.vertical 0))⁻¹ := by group
        _ = hSLIsometry B := hE
    exact (hReflectedSL_squaredTrace A).symm.trans (nativeSL_conjugation_squaredTrace _ B C he)

/-- The actual conformal reciprocal z ↦ -1/z. -/
def hReciprocalSL : Matrix.SpecialLinearGroup (Fin 2) ℝ := hRotationSL 0 1 (by norm_num)

theorem hReciprocalSL_diagonal_inverse (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hb : A 0 1 = 0) (hc : A 1 0 = 0) : hReciprocalSL * A * hReciprocalSL⁻¹ = A⁻¹ := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hReciprocalSL, hRotationSL, hb, hc]

theorem hPositiveDilation_inverse_oriented_isConj (k : ℝ) (hk : 0 < k) :
    IsConj (halfPlaneConformalElement (verticalDilationSL k hk))
      ((halfPlaneConformalElement (verticalDilationSL k hk))⁻¹) := by
  have hm := hReciprocalSL_diagonal_inverse (verticalDilationSL k hk) rfl rfl
  have hh := (halfPlaneConformalElement_isConj_iff (verticalDilationSL k hk) (verticalDilationSL k hk)⁻¹).mpr
    ⟨hReciprocalSL, congrArg realSLMobius hm⟩
  simpa only [map_inv] using hh

/-- The genuine real normalizer and its preserved trace for an arbitrary hyperbolic action. -/
theorem hHyperbolic_oriented_standard (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusHyperbolic (realSLMobius A)) :
    ∃ k : ℝ, ∃ hk : 0 < k, k ≠ 1 ∧
      IsConj (halfPlaneConformalElement A) (halfPlaneConformalElement (verticalDilationSL k hk)) ∧
      Mobius.mobiusSquaredTrace (realSLMobius A) = Mobius.mobiusSquaredTrace (realSLMobius (verticalDilationSL k hk)) :=
        by
  have ht := (realSLMobius_hyperbolic_iff A hA.1.1).mp hA
  obtain ⟨C, k, hk, hk1, hC, _⟩ := realSLMobius_hyperbolic_normalizer A hA.1.1 ht
  have he : realSLMobius (C * A * C⁻¹) = realSLMobius (verticalDilationSL k hk) :=
    hC.trans (Fuchsian.realSLMobius_verticalDilation k hk).symm
  have hs := congrArg Mobius.mobiusSquaredTrace he
  rw [map_mul, map_mul, map_inv, Mobius.mobiusSquaredTrace_conjugation] at hs
  exact ⟨k, hk, hk1, (halfPlaneConformalElement_isConj_iff _ _).mpr ⟨C, he⟩, hs⟩

/-- Equal positive dilation trace parameters give one oriented conjugacy class. -/
theorem hPositiveDilations_oriented_isConj (k l : ℝ) (hk : 0 < k) (hl : 0 < l)
    (hk1 : k ≠ 1) (hl1 : l ≠ 1)
    (ht : Mobius.mobiusSquaredTrace (realSLMobius (verticalDilationSL k hk)) =
      Mobius.mobiusSquaredTrace (realSLMobius (verticalDilationSL l hl))) :
    IsConj (halfPlaneConformalElement (verticalDilationSL k hk))
      (halfPlaneConformalElement (verticalDilationSL l hl)) := by
  let u : ℂˣ := Units.mk0 (k : ℂ) (Complex.ofReal_ne_zero.mpr hk.ne')
  let v : ℂˣ := Units.mk0 (l : ℂ) (Complex.ofReal_ne_zero.mpr hl.ne')
  have hu1 : (u : ℂ) ≠ 1 := fun h => hk1 (Complex.ofReal_injective h)
  have hv1 : (v : ℂ) ≠ 1 := fun h => hl1 (Complex.ofReal_injective h)
  have hkp : realSLMobius (verticalDilationSL k
    hk) = Mobius.mobiusScaling u := Fuchsian.realSLMobius_verticalDilation k hk
  have hlp : realSLMobius (verticalDilationSL l
    hl) = Mobius.mobiusScaling v := Fuchsian.realSLMobius_verticalDilation l hl
  rw [hkp, hlp, DiscreteGroups.mobiusScaling_eq_standard u hu1, DiscreteGroups.mobiusScaling_eq_standard v hv1,
    Mobius.mobiusStandardElement_squaredTrace, Mobius.mobiusStandardElement_squaredTrace] at ht
  rcases (Mobius.Classification.standardTrace_eq_iff u v).mp ht with huv | huv
  · have hp : realSLMobius (verticalDilationSL k hk) = realSLMobius (verticalDilationSL l hl) := by
      rw [hkp, hlp, huv]
    have hn : halfPlaneConformalElement (verticalDilationSL k hk) = halfPlaneConformalElement (verticalDilationSL l
      hl) :=
      Subtype.ext ((hSLIsometry_eq_iff_projective _ _).mpr hp)
    rw [hn]
  · have hp : realSLMobius (verticalDilationSL k hk) = (realSLMobius (verticalDilationSL l hl))⁻¹ := by
      rw [hkp, hlp, DiscreteGroups.mobiusScaling_inv, huv]
    have hn : halfPlaneConformalElement (verticalDilationSL k hk) = (halfPlaneConformalElement (verticalDilationSL l hl))⁻¹ := by
      apply Subtype.ext
      change halfPlaneConformalIsometryHom (verticalDilationSL k hk) =
        (halfPlaneConformalIsometryHom (verticalDilationSL l hl))⁻¹
      rw [← map_inv]
      apply (hSLIsometry_eq_iff_projective _ _).mpr
      rw [map_inv]
      exact hp
    rw [hn]
    exact (hPositiveDilation_inverse_oriented_isConj l hl).symm

/-- The hyperbolic branch in the actual conformal isometry subgroup. -/
theorem hHyperbolic_oriented_isConj_of_squaredTrace (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusHyperbolic (realSLMobius A)) (hB : Mobius.MobiusHyperbolic (realSLMobius B))
    (ht : Mobius.mobiusSquaredTrace (realSLMobius A) = Mobius.mobiusSquaredTrace (realSLMobius B)) :
    IsConj (halfPlaneConformalElement A) (halfPlaneConformalElement B) := by
  obtain ⟨k, hk, hk1, hAk, htAk⟩ := hHyperbolic_oriented_standard A hA
  obtain ⟨l, hl, hl1, hBl, htBl⟩ := hHyperbolic_oriented_standard B hB
  have hkl := hPositiveDilations_oriented_isConj k l hk hl hk1 hl1 (htAk.symm.trans (ht.trans htBl))
  exact (hAk.trans hkl).trans hBl.symm

theorem hRotationSL_squaredTrace (a b : ℝ) (hu : a ^ 2 + b ^ 2 = 1) :
    Mobius.mobiusSquaredTrace (realSLMobius (hRotationSL a b hu)) = ((4 * a ^ 2 : ℝ) : ℂ) := by
  rw [realSLMobius_squaredTrace]
  congr 1
  simp [Matrix.trace_fin_two, hRotationSL]
  ring

theorem hRotationSL_inverse (a b : ℝ) (hu : a ^ 2 + b ^ 2 = 1) :
    (hRotationSL a b hu)⁻¹ = hRotationSL a (-b) (by nlinarith [hu]) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hRotationSL]

theorem hRotationSL_commute (a b c d : ℝ) (hu : a ^ 2 + b ^ 2 = 1) (hv : c ^ 2 + d ^ 2 = 1) :
    hRotationSL a b hu * hRotationSL c d hv = hRotationSL c d hv * hRotationSL a b hu := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_two, hRotationSL] <;> ring

/-- An elliptic isometry is genuinely normalized within the conformal subgroup. -/
theorem hElliptic_oriented_standard (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) :
    ∃ (a b : ℝ) (hu : a ^ 2 + b ^ 2 = 1), b ≠ 0 ∧
      IsConj (halfPlaneConformalElement A) (halfPlaneConformalElement (hRotationSL a b hu)) ∧
      Mobius.mobiusSquaredTrace (realSLMobius A) = ((4 * a ^ 2 : ℝ) : ℂ) := by
  obtain ⟨C, a, b, hu, _hC, hb, he⟩ := realSLMobius_elliptic_normal_form A hA
  have hp := congrArg realSLMobius he
  have ht := congrArg Mobius.mobiusSquaredTrace hp
  rw [map_mul, map_mul, map_inv, Mobius.mobiusSquaredTrace_conjugation, hRotationSL_squaredTrace] at ht
  exact ⟨a, b, hu, hb, (halfPlaneConformalElement_isConj_iff _ _).mpr ⟨C, hp⟩, ht⟩

/-- An oriented conjugator between nontrivial standard rotations fixes their literal center. -/
theorem hRotationSL_conjugator_fixes_I (a b c d : ℝ)
    (hu : a ^ 2 + b ^ 2 = 1) (hv : c ^ 2 + d ^ 2 = 1) (hd : d ≠ 0)
    (C : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (he : realSLMobius (C * hRotationSL a b hu * C⁻¹) = realSLMobius (hRotationSL c d hv)) :
    C • UpperHalfPlane.I = UpperHalfPlane.I := by
  have htrace : (Matrix.trace (hRotationSL c d hv).val) ^ 2 < 4 := by
    simp only [Matrix.trace_fin_two]
    change (c + c) ^ 2 < 4
    nlinarith [sq_pos_of_ne_zero hd]
  have hfix : hRotationSL c d hv • (C • UpperHalfPlane.I) = C • UpperHalfPlane.I := by
    have hn := (hSLIsometry_eq_iff_projective _ _).mpr he
    have hact := congrArg (fun e : ℍ ≃ᵢ ℍ => e (C • UpperHalfPlane.I)) hn
    change (C * hRotationSL a b hu * C⁻¹) • (C • UpperHalfPlane.I) =
      hRotationSL c d hv • (C • UpperHalfPlane.I) at hact
    rw [mul_smul, mul_smul, inv_smul_smul, hRotationSL_fixes_I] at hact
    exact hact.symm
  exact ((hSL_elliptic_fixed_iff _ htrace _).mp hfix).trans
    ((hSL_elliptic_fixed_iff _ htrace _).mp (hRotationSL_fixes_I c d hv)).symm

/-- At a fixed center each oriented elliptic conjugacy class contains one actual rotation. -/
theorem hRotationSL_oriented_isConj_iff_eq (a b c d : ℝ)
    (hu : a ^ 2 + b ^ 2 = 1) (hv : c ^ 2 + d ^ 2 = 1) (hd : d ≠ 0) :
    IsConj (halfPlaneConformalElement (hRotationSL a b hu)) (halfPlaneConformalElement (hRotationSL c d hv)) ↔
      halfPlaneConformalElement (hRotationSL a b hu) = halfPlaneConformalElement (hRotationSL c d hv) := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := (halfPlaneConformalElement_isConj_iff _ _).mp h
    obtain ⟨u, v, hw, heC⟩ := hSL_fix_I_rotation C (hRotationSL_conjugator_fixes_I a b c d hu hv hd C hC)
    have he : C * hRotationSL a b hu * C⁻¹ = hRotationSL a b hu := by
      rw [heC, hRotationSL_commute u v a b hw hu]
      group
    rw [he] at hC
    exact Subtype.ext ((hSLIsometry_eq_iff_projective _ _).mpr hC)
  · intro h
    rw [h]

theorem halfPlaneConformalElement_eq_iff_projective (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    halfPlaneConformalElement A = halfPlaneConformalElement B ↔ realSLMobius A = realSLMobius B := by
  constructor
  · intro h
    exact (hSLIsometry_eq_iff_projective A B).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((hSLIsometry_eq_iff_projective A B).mpr h)

theorem halfPlaneConformalElement_full_isConj (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h : IsConj (halfPlaneConformalElement A) (halfPlaneConformalElement B)) :
    IsConj (hSLIsometry A) (hSLIsometry B) := by
  obtain ⟨C, hC⟩ := (halfPlaneConformalElement_isConj_iff A B).mp h
  exact hSLIsometry_isConj_of_real_conjugator A B C hC

/-- Equal rotation traces determine the actual rotation or its actual inverse. -/
theorem hRotationSL_equalTrace_eq_or_inverse (a b c d : ℝ)
    (hu : a ^ 2 + b ^ 2 = 1) (hv : c ^ 2 + d ^ 2 = 1)
    (ht : Mobius.mobiusSquaredTrace (realSLMobius (hRotationSL a b hu)) =
      Mobius.mobiusSquaredTrace (realSLMobius (hRotationSL c d hv))) :
    realSLMobius (hRotationSL a b hu) = realSLMobius (hRotationSL c d hv) ∨
      realSLMobius (hRotationSL a b hu) = (realSLMobius (hRotationSL c d hv))⁻¹ := by
  rw [hRotationSL_squaredTrace, hRotationSL_squaredTrace] at ht
  have ha : c ^ 2 = a ^ 2 := by have hh := Complex.ofReal_injective ht; linarith
  have hb : d ^ 2 = b ^ 2 := by nlinarith [hu, hv]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp ha with hc | hc <;>
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hb with hd | hd
  · left
    apply (realSLMobius_eq_iff_sign _ _).mpr
    left
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [hRotationSL, hc, hd]
  · right
    rw [← map_inv]
    apply (realSLMobius_eq_iff_sign _ _).mpr
    left
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hRotationSL, hc, hd]
  · right
    rw [← map_inv]
    apply (realSLMobius_eq_iff_sign _ _).mpr
    right
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.adjugate_fin_two, hRotationSL, hc, hd]
  · left
    apply (realSLMobius_eq_iff_sign _ _).mpr
    right
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.SpecialLinearGroup.coe_neg, hRotationSL, hc, hd]

theorem hRotationSL_reflected_inverse (a b : ℝ) (hu : a ^ 2 + b ^ 2 = 1) :
    hReflectedSL (hRotationSL a b hu) = (hRotationSL a b hu)⁻¹ := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [hReflectedSL, hRotationSL, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

/-- Reflection identifies the two inverse elliptic classes in the full isometry group. -/
theorem hRotationSL_full_inverse_isConj (a b : ℝ) (hu : a ^ 2 + b ^ 2 = 1) :
    IsConj (hSLIsometry (hRotationSL a b hu)) ((hSLIsometry (hRotationSL a b hu))⁻¹) := by
  apply isConj_iff.mpr
  refine ⟨HalfPlaneLine.reflectionIsometry (.vertical 0), ?_⟩
  rw [hReflectedSL_native_conjugation, hRotationSL_reflected_inverse, hSLIsometry_inverse]
  rfl

/-- The full native isometry conjugacy class of a rotation is determined by its squared trace. -/
theorem hRotationSL_full_isConj_of_squaredTrace (a b c d : ℝ)
    (hu : a ^ 2 + b ^ 2 = 1) (hv : c ^ 2 + d ^ 2 = 1)
    (ht : Mobius.mobiusSquaredTrace (realSLMobius (hRotationSL a b hu)) =
      Mobius.mobiusSquaredTrace (realSLMobius (hRotationSL c d hv))) :
    IsConj (hSLIsometry (hRotationSL a b hu)) (hSLIsometry (hRotationSL c d hv)) := by
  rcases hRotationSL_equalTrace_eq_or_inverse a b c d hu hv ht with hp | hp
  · rw [(hSLIsometry_eq_iff_projective _ _).mpr hp]
  · have hn : hSLIsometry (hRotationSL a b hu) = (hSLIsometry (hRotationSL c d hv))⁻¹ := by
      change hSLIsometry (hRotationSL a b hu) = (hSLIsometry (hRotationSL c d hv)).symm
      rw [← hSLIsometry_inverse]
      apply (hSLIsometry_eq_iff_projective _ _).mpr
      rw [map_inv]
      exact hp
    rw [hn]
    exact (hRotationSL_full_inverse_isConj c d hv).symm

/-- The full-isometry elliptic branch for arbitrary original actions. -/
theorem hElliptic_full_isConj_of_squaredTrace (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (hB : Mobius.MobiusElliptic (realSLMobius B))
    (ht : Mobius.mobiusSquaredTrace (realSLMobius A) = Mobius.mobiusSquaredTrace (realSLMobius B)) :
    IsConj (hSLIsometry A) (hSLIsometry B) := by
  obtain ⟨a, b, hu, _hb, hAr, htA⟩ := hElliptic_oriented_standard A hA
  obtain ⟨c, d, hv, _hd, hBs, htB⟩ := hElliptic_oriented_standard B hB
  have hstd : Mobius.mobiusSquaredTrace (realSLMobius (hRotationSL a b hu)) =
      Mobius.mobiusSquaredTrace (realSLMobius (hRotationSL c d hv)) := by
    rw [hRotationSL_squaredTrace, hRotationSL_squaredTrace]
    exact htA.symm.trans (ht.trans htB)
  exact ((halfPlaneConformalElement_full_isConj _ _ hAr).trans
    (hRotationSL_full_isConj_of_squaredTrace a b c d hu hv hstd)).trans
      (halfPlaneConformalElement_full_isConj _ _ hBs).symm

/-- The full native-isometry assertion, with nontriviality explicit. -/
theorem hNontrivial_full_isConj_iff_squaredTrace (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : realSLMobius A ≠ 1) (hB : realSLMobius B ≠ 1) :
    IsConj (hSLIsometry A) (hSLIsometry B) ↔
      Mobius.mobiusSquaredTrace (realSLMobius A) = Mobius.mobiusSquaredTrace (realSLMobius B) := by
  constructor
  · exact hSLIsometry_isConj_squaredTrace A B
  · intro ht
    have htr : (Matrix.trace A.val) ^ 2 = (Matrix.trace B.val) ^ 2 := by
      rw [realSLMobius_squaredTrace, realSLMobius_squaredTrace] at ht
      exact Complex.ofReal_injective ht
    rcases lt_trichotomy ((Matrix.trace A.val) ^ 2) 4 with h | h | h
    · exact hElliptic_full_isConj_of_squaredTrace A B
        ((realSLMobius_elliptic_iff A hA).mpr h)
        ((realSLMobius_elliptic_iff B hB).mpr (by rwa [← htr])) ht
    · exact hParabolic_full_isConj A B
        ((realSLMobius_parabolic_iff A hA).mpr h)
        ((realSLMobius_parabolic_iff B hB).mpr (by rwa [← htr]))
    · exact halfPlaneConformalElement_full_isConj A B
        (hHyperbolic_oriented_isConj_of_squaredTrace A B
          ((realSLMobius_hyperbolic_iff A hA).mpr h)
          ((realSLMobius_hyperbolic_iff B hB).mpr (by rwa [← htr])) ht)

theorem isConj_inverse {G : Type*} [Group G] {a b : G} (h : IsConj a b) :
    IsConj a⁻¹ b⁻¹ := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  apply isConj_iff.mpr
  refine ⟨c, ?_⟩
  rw [← conj_inv, hc]

/-- An elliptic squared trace gives at most the two inverse oriented classes. -/
theorem hElliptic_oriented_isConj_or_inverse (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (hB : Mobius.MobiusElliptic (realSLMobius B))
    (ht : Mobius.mobiusSquaredTrace (realSLMobius A) = Mobius.mobiusSquaredTrace (realSLMobius B)) :
    IsConj (halfPlaneConformalElement A) (halfPlaneConformalElement B) ∨
      IsConj (halfPlaneConformalElement A) (halfPlaneConformalElement B)⁻¹ := by
  obtain ⟨a, b, hu, _hb, hAr, htA⟩ := hElliptic_oriented_standard A hA
  obtain ⟨c, d, hv, _hd, hBs, htB⟩ := hElliptic_oriented_standard B hB
  have hstd : Mobius.mobiusSquaredTrace (realSLMobius (hRotationSL a b hu)) =
      Mobius.mobiusSquaredTrace (realSLMobius (hRotationSL c d hv)) := by
    rw [hRotationSL_squaredTrace, hRotationSL_squaredTrace]
    exact htA.symm.trans (ht.trans htB)
  rcases hRotationSL_equalTrace_eq_or_inverse a b c d hu hv hstd with hp | hp
  · left
    have hn := (halfPlaneConformalElement_eq_iff_projective _ _).mpr hp
    exact (hAr.trans (by rw [hn])).trans hBs.symm
  · right
    have hn : halfPlaneConformalElement (hRotationSL a b hu) =
        (halfPlaneConformalElement (hRotationSL c d hv))⁻¹ := by
      rw [← map_inv]
      apply (halfPlaneConformalElement_eq_iff_projective _ _).mpr
      rw [map_inv]
      exact hp
    exact (hAr.trans (by rw [hn])).trans (isConj_inverse hBs).symm

/-- A nontrivial standard elliptic map equals its inverse exactly for a half-turn. -/
theorem hRotationSL_projective_eq_inverse_iff (a b : ℝ)
    (hu : a ^ 2 + b ^ 2 = 1) (hb : b ≠ 0) :
    realSLMobius (hRotationSL a b hu) = (realSLMobius (hRotationSL a b hu))⁻¹ ↔ a = 0 := by
  rw [← map_inv, realSLMobius_eq_iff_sign]
  constructor
  · rintro (h | h)
    · have he := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) ℝ => M 0 1) h
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, hRotationSL] at he
      exact False.elim (hb (by linarith))
    · have he := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) ℝ => M 0 0) h
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.adjugate_fin_two, hRotationSL] at he
      linarith
  · intro ha
    right
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_neg,
        Matrix.adjugate_fin_two, hRotationSL, ha]

/-- The two inverse elliptic oriented classes coincide exactly at squared trace zero. -/
theorem hElliptic_oriented_self_inverse_iff (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) :
    IsConj (halfPlaneConformalElement A) (halfPlaneConformalElement A)⁻¹ ↔
      Mobius.mobiusSquaredTrace (realSLMobius A) = 0 := by
  obtain ⟨a, b, hu, hb, hAr, htA⟩ := hElliptic_oriented_standard A hA
  have hinv : (halfPlaneConformalElement (hRotationSL a b hu))⁻¹ =
      halfPlaneConformalElement (hRotationSL a (-b) (by nlinarith [hu])) := by
    rw [← map_inv, hRotationSL_inverse]
  constructor
  · intro h
    have hr := (hAr.symm.trans h).trans (isConj_inverse hAr)
    rw [hinv] at hr
    have he := (hRotationSL_oriented_isConj_iff_eq a b a (-b) hu
      (by nlinarith [hu]) (neg_ne_zero.mpr hb)).mp hr
    rw [← hinv] at he
    have hp : realSLMobius (hRotationSL a b hu) = (realSLMobius (hRotationSL a b hu))⁻¹ := by
      rw [← map_inv] at he ⊢
      exact (halfPlaneConformalElement_eq_iff_projective _ _).mp he
    have ha := (hRotationSL_projective_eq_inverse_iff a b hu hb).mp hp
    rw [htA, ha]
    norm_num
  · intro ht
    have ha : a = 0 := by
      rw [htA] at ht
      have hh : 4 * a ^ 2 = 0 := by exact_mod_cast ht
      nlinarith [sq_nonneg a]
    have hp := (hRotationSL_projective_eq_inverse_iff a b hu hb).mpr ha
    have he : halfPlaneConformalElement (hRotationSL a b hu) =
        (halfPlaneConformalElement (hRotationSL a b hu))⁻¹ := by
      rw [← map_inv]
      apply (halfPlaneConformalElement_eq_iff_projective _ _).mpr
      rw [map_inv]
      exact hp
    exact (hAr.trans (by nth_rw 1 [he])).trans (isConj_inverse hAr).symm

/-- The half-turn branch has only one oriented conjugacy class. -/
theorem hElliptic_zeroTrace_oriented_isConj (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (hB : Mobius.MobiusElliptic (realSLMobius B))
    (htA : Mobius.mobiusSquaredTrace (realSLMobius A) = 0)
    (htB : Mobius.mobiusSquaredTrace (realSLMobius B) = 0) :
    IsConj (halfPlaneConformalElement A) (halfPlaneConformalElement B) := by
  rcases hElliptic_oriented_isConj_or_inverse A B hA hB (htA.trans htB.symm) with h | h
  · exact h
  · exact h.trans ((hElliptic_oriented_self_inverse_iff B hB).mpr htB).symm

/-- Away from the half-turn value, the inverse elliptic oriented classes are distinct. -/
theorem hElliptic_nonzeroTrace_not_oriented_inverse (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusElliptic (realSLMobius A)) (ht : Mobius.mobiusSquaredTrace (realSLMobius A) ≠ 0) :
    ¬ IsConj (halfPlaneConformalElement A) (halfPlaneConformalElement A)⁻¹ := by
  exact mt (hElliptic_oriented_self_inverse_iff A hA).mp ht

/-- A real determinant-one representative of an actual conformal isometry. -/
def halfPlaneConformalLift (f : halfPlaneConformalIsometryGroup) :
    Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  Classical.choose (halfPlaneConformalIsometryHom.rangeRestrict_surjective f)

theorem halfPlaneConformalLift_spec (f : halfPlaneConformalIsometryGroup) :
    halfPlaneConformalElement (halfPlaneConformalLift f) = f :=
  Classical.choose_spec (halfPlaneConformalIsometryHom.rangeRestrict_surjective f)

/-- Squared trace on the genuine conformal isometry group, independent of its real lift. -/
def halfPlaneConformalSquaredTrace (f : halfPlaneConformalIsometryGroup) : ℂ :=
  Mobius.mobiusSquaredTrace (realSLMobius (halfPlaneConformalLift f))

theorem halfPlaneConformalSquaredTrace_apply (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    halfPlaneConformalSquaredTrace (halfPlaneConformalElement A) =
      Mobius.mobiusSquaredTrace (realSLMobius A) := by
  unfold halfPlaneConformalSquaredTrace
  rw [(halfPlaneConformalElement_eq_iff_projective _ _).mp
    (halfPlaneConformalLift_spec (halfPlaneConformalElement A))]

theorem halfPlaneConformalLift_nontrivial (f : halfPlaneConformalIsometryGroup) (hf : f ≠ 1) :
    realSLMobius (halfPlaneConformalLift f) ≠ 1 := by
  intro h
  have he : halfPlaneConformalElement (halfPlaneConformalLift f) =
      halfPlaneConformalElement 1 := by
    apply (halfPlaneConformalElement_eq_iff_projective _ _).mpr
    simpa only [map_one] using h
  rw [halfPlaneConformalLift_spec, map_one] at he
  exact hf he

/-- For all actual nonidentity conformal isometries, conjugated inside the full group. -/
theorem halfPlaneConformal_full_isConj_iff_squaredTrace
    (f g : halfPlaneConformalIsometryGroup) (hf : f ≠ 1) (hg : g ≠ 1) :
    IsConj (f : ℍ ≃ᵢ ℍ) (g : ℍ ≃ᵢ ℍ) ↔
      halfPlaneConformalSquaredTrace f = halfPlaneConformalSquaredTrace g := by
  have hfv : hSLIsometry (halfPlaneConformalLift f) = (f : ℍ ≃ᵢ ℍ) :=
    congrArg Subtype.val (halfPlaneConformalLift_spec f)
  have hgv : hSLIsometry (halfPlaneConformalLift g) = (g : ℍ ≃ᵢ ℍ) :=
    congrArg Subtype.val (halfPlaneConformalLift_spec g)
  rw [← hfv, ← hgv]
  exact hNontrivial_full_isConj_iff_squaredTrace _ _
    (halfPlaneConformalLift_nontrivial f hf) (halfPlaneConformalLift_nontrivial g hg)

end LowDimensionalTopology.Geometry.Hyperbolic
