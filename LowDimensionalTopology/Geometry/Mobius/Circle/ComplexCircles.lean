module
public import LowDimensionalTopology.Geometry.Mobius.CrossRatio.CrossRatioGeometry
public import LowDimensionalTopology.Geometry.Inversive.SphereOrthogonality

/-!
# Native complex circles and the real cross-ratio criterion

All circle and line carriers are genuine geometric subsets
of the extended complex plane, using the fixed real isometric coordinate chart.
Reflection fixed sets and normal orthogonality agree with their real geometric
models, and complex concyclicity is characterized by the imaginary part of the
complex cross-ratio.
-/

@[expose] public section
noncomputable section
open scoped OnePoint RealInnerProductSpace ComplexConjugate
open EuclideanGeometry Metric
namespace LowDimensionalTopology.Geometry.Mobius
open LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.Mobius

/-- The real isometric coordinate chart used throughout the complex model. -/
abbrev complexPlaneCoordinates := Complex.orthonormalBasisOneI.repr

/-- A genuine positive-radius finite complex circle when r is positive. -/
def complexCircle (c : ℂ) (r : ℝ) : Set ExtendedComplex :=
  extendedComplexEuclideanHomeomorph ⁻¹' Inversive.extendedSphere (complexPlaneCoordinates c) r

/-- A real affine complex line together with infinity; a nonzero normal is required for a genuine line. -/
def complexLine (a : ℂ) (t : ℝ) : Set ExtendedComplex :=
  extendedComplexEuclideanHomeomorph ⁻¹' Inversive.plane (complexPlaneCoordinates a) t

/-- Generalized circles are precisely the real geometric generalized spheres in complex coordinates. -/
def IsComplexGeneralizedCircle (S : Set ExtendedComplex) : Prop :=
  Inversive.IsGeneralizedSphere (extendedComplexEuclideanHomeomorph '' S)

theorem complexChart_image_preimage (S : Set (Inversive.ExtendedEuclidean 2)) :
    extendedComplexEuclideanHomeomorph '' (extendedComplexEuclideanHomeomorph ⁻¹' S) = S := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hz
    exact ⟨extendedComplexEuclideanHomeomorph.symm z, by simpa using hz, by simp⟩

theorem complexChart_preimage_image (S : Set ExtendedComplex) :
    extendedComplexEuclideanHomeomorph ⁻¹' (extendedComplexEuclideanHomeomorph '' S) = S := by
  exact Set.preimage_image_eq _ extendedComplexEuclideanHomeomorph.injective

@[simp] theorem complexCircle_coe (c z : ℂ) (r : ℝ) :
    (z : ExtendedComplex) ∈ complexCircle c r ↔ ‖z - c‖ = r := by
  simp only [complexCircle, Set.mem_preimage, extendedComplexEuclideanHomeomorph_coe,
    Inversive.extendedSphere, Set.mem_image, OnePoint.coe_eq_coe, Metric.mem_sphere, dist_eq_norm]
  constructor
  · rintro ⟨x, hx, he⟩
    subst x
    simpa only [← map_sub, complexPlaneCoordinates.norm_map] using hx
  · intro h
    refine ⟨complexPlaneCoordinates z, ?_, rfl⟩
    simpa only [← map_sub, complexPlaneCoordinates.norm_map] using h

@[simp] theorem complexCircle_infty (c : ℂ) (r : ℝ) : ∞ ∉ complexCircle c r := by
  simp [complexCircle, Inversive.extendedSphere, extendedComplexEuclideanHomeomorph_infty]

@[simp] theorem complexLine_coe (a z : ℂ) (t : ℝ) :
    (z : ExtendedComplex) ∈ complexLine a t ↔ inner ℝ z a = t := by
  simp [complexLine, Inversive.plane, extendedComplexEuclideanHomeomorph_coe,
    complexPlaneCoordinates.inner_map_map]

@[simp] theorem complexLine_infty (a : ℂ) (t : ℝ) : ∞ ∈ complexLine a t := by
  simp [complexLine, Inversive.plane, extendedComplexEuclideanHomeomorph_infty]

theorem complexCircle_isGeneralized (c : ℂ) (r : ℝ) (hr : 0 < r) :
    IsComplexGeneralizedCircle (complexCircle c r) := by
  unfold IsComplexGeneralizedCircle complexCircle
  rw [complexChart_image_preimage]
  exact Or.inl ⟨_, r, hr, rfl⟩

theorem complexLine_isGeneralized (a : ℂ) (t : ℝ) (ha : a ≠ 0) :
    IsComplexGeneralizedCircle (complexLine a t) := by
  unfold IsComplexGeneralizedCircle complexLine
  rw [complexChart_image_preimage]
  exact Or.inr ⟨_, t, (complexPlaneCoordinates.map_ne_zero_iff).mpr ha, rfl⟩

theorem isComplexGeneralizedCircle_iff (S : Set ExtendedComplex) :
    IsComplexGeneralizedCircle S ↔
      (∃ c : ℂ, ∃ r : ℝ, 0 < r ∧ S = complexCircle c r) ∨
      (∃ a : ℂ, ∃ t : ℝ, a ≠ 0 ∧ S = complexLine a t) := by
  constructor
  · rintro (⟨c, r, hr, he⟩ | ⟨a, t, ha, he⟩)
    · refine Or.inl ⟨complexPlaneCoordinates.symm c, r, hr, ?_⟩
      have hp := congrArg (fun T => extendedComplexEuclideanHomeomorph ⁻¹' T) he
      simpa only [complexChart_preimage_image, complexCircle, LinearIsometryEquiv.apply_symm_apply] using hp
    · refine Or.inr ⟨complexPlaneCoordinates.symm a, t, ?_, ?_⟩
      · intro hz
        apply ha
        simpa only [LinearIsometryEquiv.apply_symm_apply, map_zero] using congrArg complexPlaneCoordinates hz
      · have hp := congrArg (fun T => extendedComplexEuclideanHomeomorph ⁻¹' T) he
        simpa only [complexChart_preimage_image, complexLine, LinearIsometryEquiv.apply_symm_apply] using hp
  · rintro (⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩)
    · exact complexCircle_isGeneralized c r hr
    · exact complexLine_isGeneralized a t ha

theorem complexReflection_fixedPoints (r : Inversive.ExtendedHomeomorph 2) :
    Function.fixedPoints (euclideanToComplexHom r) =
      extendedComplexEuclideanHomeomorph ⁻¹' Function.fixedPoints r := by
  ext z
  change extendedComplexEuclideanHomeomorph.symm (r (extendedComplexEuclideanHomeomorph z)) = z ↔
    r (extendedComplexEuclideanHomeomorph z) = extendedComplexEuclideanHomeomorph z
  exact extendedComplexEuclideanHomeomorph.symm_apply_eq

theorem IsComplexGeneralizedCircle.exists_reflection {S : Set ExtendedComplex}
    (hS : IsComplexGeneralizedCircle S) :
    ∃ r : Inversive.ExtendedHomeomorph 2, Inversive.IsReflection r ∧ Function.fixedPoints (euclideanToComplexHom
      r) = S := by
  obtain ⟨r, hr, he⟩ := (Inversive.isGeneralizedSphere_iff_fixedPoints_reflection _).mp hS
  exact ⟨r, hr, by rw [complexReflection_fixedPoints, he, complexChart_preimage_image]⟩

/-- Coordinate transport commutes with the whole extended geometric action. -/
theorem complexChart_image_image (g : Inversive.ExtendedHomeomorph 2) (S : Set ExtendedComplex) :
    extendedComplexEuclideanHomeomorph '' (euclideanToComplexHom g '' S) =
      g '' (extendedComplexEuclideanHomeomorph '' S) := by
  have hi : extendedComplexEuclideanHomeomorph ∘ euclideanToComplexHom g =
      g ∘ extendedComplexEuclideanHomeomorph := by
    funext z
    simp [euclideanToComplexHom_apply]
  rw [Set.image_image]
  change (extendedComplexEuclideanHomeomorph ∘ euclideanToComplexHom g) '' S = _
  rw [hi]
  simpa only [Function.comp_def] using
    (Set.image_image (g : Inversive.ExtendedEuclidean 2 → Inversive.ExtendedEuclidean 2)
      (extendedComplexEuclideanHomeomorph : ExtendedComplex → Inversive.ExtendedEuclidean 2) S).symm

/-- The complete fixed set of the real circle reflection is the native complex circle. -/
theorem complexCircle_reflection (c : ℂ) (r : ℝ) (hr : 0 < r) :
    Function.fixedPoints (euclideanToComplexHom
      (Inversive.sphereInversionHomeomorph (complexPlaneCoordinates c) r hr.ne')) = complexCircle c r := by
  rw [complexReflection_fixedPoints, Inversive.fixedPoints_sphereInversion _ _ hr]
  rfl

/-- The complete fixed set of the real line reflection is the native complex line, including infinity. -/
theorem complexLine_reflection (a : ℂ) (t : ℝ) (ha : a ≠ 0) :
    Function.fixedPoints (euclideanToComplexHom (Inversive.planeReflectionHomeomorph
      (complexPlaneCoordinates a) t ((complexPlaneCoordinates.map_ne_zero_iff).mpr ha))) = complexLine a t := by
  rw [complexReflection_fixedPoints, Inversive.fixedPoints_planeReflection]
  rfl

/-- Generalized circles are preserved by every actual reflection-generated complex transformation. -/
theorem IsComplexGeneralizedCircle.image {S : Set ExtendedComplex} (hS : IsComplexGeneralizedCircle S)
    {f : Equiv.Perm ExtendedComplex} (hf : f ∈ complexGeneralMobiusGroup) :
    IsComplexGeneralizedCircle (f '' S) := by
  obtain ⟨g, hg, rfl⟩ := hf
  have hi : extendedComplexEuclideanHomeomorph ∘ euclideanToComplexHom g =
      g ∘ extendedComplexEuclideanHomeomorph := by
    funext z
    simp [euclideanToComplexHom_apply]
  unfold IsComplexGeneralizedCircle at *
  rw [Set.image_image]
  change Inversive.IsGeneralizedSphere ((extendedComplexEuclideanHomeomorph ∘ euclideanToComplexHom g) '' S)
  rw [hi]
  simpa only [Set.image_image, Function.comp_def] using hS.image hg

/-- Native complex generalized circles, bundled by their actual extended-point carriers. -/
abbrev ComplexGeneralizedCircle := {S : Set ExtendedComplex // IsComplexGeneralizedCircle S}

/-- The real geometric circle represented by a complex circle; its carrier is exactly the coordinate image. -/
def ComplexGeneralizedCircle.realModel (S : ComplexGeneralizedCircle) : Inversive.GeneralizedSphere 2 :=
  ⟨extendedComplexEuclideanHomeomorph '' S.val, S.property⟩

/-- Geometric normal orthogonality transported by the fixed real isometry, not by the value of a cross-ratio. -/
def ComplexCirclesOrthogonal (S T : ComplexGeneralizedCircle) : Prop :=
  Inversive.GeneralizedSpheresOrthogonal S.realModel T.realModel

/-- The orthogonality criterion for native complex circle carriers. -/
theorem complexCirclesOrthogonal_iff_inversiveProduct_zero (S T : ComplexGeneralizedCircle) :
    ComplexCirclesOrthogonal S T ↔ Inversive.inversiveProduct S.realModel T.realModel = 0 :=
  Inversive.generalizedSpheresOrthogonal_iff_inversiveProduct_eq_zero (by norm_num) _ _

/-- The actual image of a native circle under an orientation-preserving complex Möbius transformation. -/
def ComplexGeneralizedCircle.image (f : complexMobiusGroup) (S : ComplexGeneralizedCircle) : ComplexGeneralizedCircle :=
  ⟨f.val '' S.val, S.property.image f.property.1⟩

/-- Native geometric orthogonality is invariant under the actual complex Möbius action. -/
theorem ComplexCirclesOrthogonal.image (S T : ComplexGeneralizedCircle) (hST : ComplexCirclesOrthogonal S T)
    (f : complexMobiusGroup) : ComplexCirclesOrthogonal (S.image f) (T.image f) := by
  obtain ⟨g, hg, he⟩ := f.property.1
  have hreal (U : ComplexGeneralizedCircle) :
      (U.image f).realModel = Inversive.generalizedSphereImage g hg U.realModel := by
    apply Subtype.ext
    change extendedComplexEuclideanHomeomorph '' (f.val '' U.val) =
      g '' (extendedComplexEuclideanHomeomorph '' U.val)
    rw [← he]
    exact complexChart_image_image g U.val
  change Inversive.GeneralizedSpheresOrthogonal _ _
  rw [hreal, hreal]
  exact Inversive.GeneralizedSpheresOrthogonal.image (by norm_num) _ _ hST g hg

/-- The real axis completed by infinity, characterized by complex conjugation. -/
def complexRealAxis : Set ExtendedComplex := Function.fixedPoints complexConjugation

@[simp] theorem complexRealAxis_coe (z : ℂ) : (z : ExtendedComplex) ∈ complexRealAxis ↔ z.im = 0 := by
  change ((conj z : ℂ) : ExtendedComplex) = (z : ExtendedComplex) ↔ _
  rw [OnePoint.coe_eq_coe, Complex.conj_eq_iff_im]

@[simp] theorem complexRealAxis_infty : ∞ ∈ complexRealAxis := rfl

theorem complexRealAxis_eq_line : complexRealAxis = complexLine Complex.I 0 := by
  ext z
  induction z using OnePoint.rec with
  | infty => simp
  | coe z => simp [Complex.inner, Complex.mul_re]

theorem complexRealAxis_isGeneralized : IsComplexGeneralizedCircle complexRealAxis := by
  rw [complexRealAxis_eq_line]
  exact complexLine_isGeneralized _ _ Complex.I_ne_zero

/-- A generalized circle through zero, one and infinity is the actual extended real axis. -/
theorem complexCircle_through_zero_one_infty {S : Set ExtendedComplex}
    (hS : IsComplexGeneralizedCircle S) (h0 : ((0 : ℂ) : ExtendedComplex) ∈ S) (h1 : ((1 : ℂ) : ExtendedComplex) ∈
      S) (hi : ∞ ∈ S) :
    S = complexRealAxis := by
  obtain ⟨r, hr, hfix⟩ := hS.exists_reflection
  let f : complexMobiusGroup := ⟨euclideanToComplexHom r * complexConjugation,
    by rw [complexMobiusGroup_eq_fractionalLinearGroup]; exact reflection_complex_anti hr⟩
  have hr0 : euclideanToComplexHom r (0 : ℂ) = (0 : ℂ) :=
    by change ((0 : ℂ) : ExtendedComplex) ∈ Function.fixedPoints _; rwa [hfix]
  have hr1 : euclideanToComplexHom r (1 : ℂ) = (1 : ℂ) :=
    by change ((1 : ℂ) : ExtendedComplex) ∈ Function.fixedPoints _; rwa [hfix]
  have hri : euclideanToComplexHom r ∞ = ∞ := by change ∞ ∈ Function.fixedPoints _; rwa [hfix]
  have hf : f = 1 := mobius_eq_one_of_fixes_zero_one_infty f
    (by simpa [f, Equiv.Perm.mul_apply] using hr0)
    (by simpa [f, Equiv.Perm.mul_apply] using hr1)
    (by simpa [f, Equiv.Perm.mul_apply] using hri)
  have he : euclideanToComplexHom r * complexConjugation = 1 := congrArg Subtype.val hf
  have he' : euclideanToComplexHom r = complexConjugation := by
    calc
      euclideanToComplexHom r = (euclideanToComplexHom r * complexConjugation) * complexConjugation := by
        rw [mul_assoc, complexConjugation_sq, mul_one]
      _ = complexConjugation := by rw [he, one_mul]
  rw [← hfix, he']
  rfl

/-- Concyclicity includes lines completed by infinity. -/
def ComplexConcyclic (a b c d : ExtendedComplex) : Prop :=
  QuadrupleDistinct a b c d ∧
    ∃ S : Set ExtendedComplex, IsComplexGeneralizedCircle S ∧ a ∈ S ∧ b ∈ S ∧ c ∈ S ∧ d ∈ S

/-- four distinct extended complex points lie on one generalized circle exactly when their ratio is real. -/
theorem complexConcyclic_iff_crossRatio_real (a b c d : ExtendedComplex)
    (hd : QuadrupleDistinct a b c d) :
    ComplexConcyclic a b c d ↔ (extendedCrossRatio a b c d).im = 0 := by
  obtain ⟨q, h0, h1, hi⟩ := mobius_normalize_triple a b d ⟨hd.1, hd.2.2.1, hd.2.2.2.2.1⟩
  have hratio := mobius_normalized_crossRatio q a b c d h0 h1 hi hd.2.2.2.2.2
  constructor
  · rintro ⟨_, S, hS, ha, hb, hc, hdS⟩
    have hT : (q : Equiv.Perm ExtendedComplex) '' S = complexRealAxis :=
      complexCircle_through_zero_one_infty (hS.image q.property.1)
        ⟨a, ha, h0⟩ ⟨b, hb, h1⟩ ⟨d, hdS, hi⟩
    rw [← complexRealAxis_coe, hratio, ← hT]
    exact ⟨c, hc, rfl⟩
  · intro hreal
    refine ⟨hd, (q⁻¹ : complexMobiusGroup).val '' complexRealAxis,
      complexRealAxis_isGeneralized.image (q⁻¹).property.1, ?_, ?_, ?_, ?_⟩
    · exact ⟨q.val a, by rw [h0]; simp, by simp⟩
    · exact ⟨q.val b, by rw [h1]; simp, by simp⟩
    · exact ⟨q.val c, by rw [← hratio, complexRealAxis_coe]; exact hreal, by simp⟩
    · exact ⟨q.val d, by rw [hi]; simp, by simp⟩

end LowDimensionalTopology.Geometry.Mobius
