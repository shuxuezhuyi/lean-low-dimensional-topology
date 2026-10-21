module
public import LowDimensionalTopology.Geometry.Inversive.GeneralizedSpheres

/-!
# Invariance of the inversive product

Explicit transformations of quadratic coefficient vectors cover translations,
positive dilations, orthogonal maps, and extended unit-sphere inversion.
They preserve the geometric inversive product, hence so does every finite
word of genuine sphere and plane reflections. All poles and infinity are
included in the coefficient-locus transport equations.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint RealInnerProductSpace
open Filter EuclideanGeometry
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}

/-- The actual generalized-sphere image under a reflection-generated transformation. -/
def generalizedSphereImage [NeZero n] (g : ExtendedHomeomorph n) (hg : g ∈ generalMobiusGroup n)
    (S : GeneralizedSphere n) : GeneralizedSphere n := ⟨g '' S.val, S.property.image hg⟩

theorem generalizedSphereImage_one [NeZero n] (S : GeneralizedSphere n) :
    generalizedSphereImage 1 (generalMobiusGroup n).one_mem S = S := by
  apply Subtype.ext
  exact Set.image_id _

theorem generalizedSphereImage_mul [NeZero n] (g f : ExtendedHomeomorph n)
    (hg : g ∈ generalMobiusGroup n) (hf : f ∈ generalMobiusGroup n) (S : GeneralizedSphere n) :
    generalizedSphereImage (g * f) ((generalMobiusGroup n).mul_mem hg hf) S =
      generalizedSphereImage g hg (generalizedSphereImage f hf S) := by
  apply Subtype.ext
  change (fun x => g (f x)) '' S.val = g '' (f '' S.val)
  exact (Set.image_image g f S.val).symm

/-- Geometric preservation of the inversive product. -/
def PreservesInversiveProduct [NeZero n] (g : ExtendedHomeomorph n) (hg : g ∈ generalMobiusGroup n) : Prop :=
  ∀ S T : GeneralizedSphere n,
    inversiveProduct (generalizedSphereImage g hg S) (generalizedSphereImage g hg T) = inversiveProduct S T

theorem PreservesInversiveProduct.one [NeZero n] :
    PreservesInversiveProduct (1 : ExtendedHomeomorph n) (generalMobiusGroup n).one_mem := by
  intro S T
  rw [generalizedSphereImage_one, generalizedSphereImage_one]

theorem PreservesInversiveProduct.mul [NeZero n] {g f : ExtendedHomeomorph n}
    {hg : g ∈ generalMobiusGroup n} {hf : f ∈ generalMobiusGroup n}
    (hgp : PreservesInversiveProduct g hg) (hfp : PreservesInversiveProduct f hf) :
    PreservesInversiveProduct (g * f) ((generalMobiusGroup n).mul_mem hg hf) := by
  intro S T
  rw [generalizedSphereImage_mul g f hg hf S, generalizedSphereImage_mul g f hg hf T, hgp, hfp]

theorem PreservesInversiveProduct.inv [NeZero n] {g : ExtendedHomeomorph n}
    {hg : g ∈ generalMobiusGroup n} (hgp : PreservesInversiveProduct g hg) :
    PreservesInversiveProduct g⁻¹ ((generalMobiusGroup n).inv_mem hg) := by
  intro S T
  have h := hgp (generalizedSphereImage g⁻¹ ((generalMobiusGroup n).inv_mem hg) S)
    (generalizedSphereImage g⁻¹ ((generalMobiusGroup n).inv_mem hg) T)
  have him (U : GeneralizedSphere n) :
      generalizedSphereImage g hg (generalizedSphereImage g⁻¹ ((generalMobiusGroup n).inv_mem hg) U) = U := by
    apply Subtype.ext
    simp [generalizedSphereImage, Set.image_image]
  rw [him S, him T] at h
  exact h.symm

/-- A coefficient transformation gives the full geometric invariance statement. -/
theorem preservesInversiveProduct_of_coefficients [NeZero n] (g : ExtendedHomeomorph n)
    (hg : g ∈ generalMobiusGroup n) (A : SphereCoefficients n → SphereCoefficients n)
    (hcarrier : ∀ a, sphereCoefficientCarrier (A a) = g '' sphereCoefficientCarrier a)
    (hpos : ∀ a, 0 < sphereDiscriminant a → 0 < sphereDiscriminant (A a))
    (hprod : ∀ a b, coefficientInversiveProduct (A a) (A b) = coefficientInversiveProduct a b) :
    PreservesInversiveProduct g hg := by
  intro S T
  let a := generalizedSphereCoefficients S
  let b := generalizedSphereCoefficients T
  have ha : 0 < sphereDiscriminant a := generalizedSphereCoefficients_pos S
  have hb : 0 < sphereDiscriminant b := generalizedSphereCoefficients_pos T
  rw [inversiveProduct_eq_coefficients _ _ (A a) (A b)
    (sphereCoefficients_ne_zero_of_pos _ (hpos a ha)) (sphereCoefficients_ne_zero_of_pos _ (hpos b hb))
    (by rw [hcarrier, generalizedSphereCoefficients_carrier]; rfl)
    (by rw [hcarrier, generalizedSphereCoefficients_carrier]; rfl)]
  exact hprod a b

/-- Equivalence of locus membership proves the image equation, including infinity. -/
theorem coefficientCarrier_transport (g : ExtendedHomeomorph n)
    (A : SphereCoefficients n → SphereCoefficients n)
    (h : ∀ a z, g z ∈ sphereCoefficientCarrier (A a) ↔ z ∈ sphereCoefficientCarrier a)
    (a : SphereCoefficients n) : sphereCoefficientCarrier (A a) = g '' sphereCoefficientCarrier a := by
  ext z
  constructor
  · intro hz
    refine ⟨g⁻¹ z, (h a (g⁻¹ z)).mp ?_, by simp⟩
    simpa using hz
  · rintro ⟨x, hx, rfl⟩
    exact (h a x).mpr hx

namespace InversiveCoefficients

def orthogonal (φ : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) (a : Inversive.SphereCoefficients n) :
    Inversive.SphereCoefficients n :=
  (a.1, φ a.2.1, a.2.2)

theorem orthogonal_carrier (φ : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) (a :
    Inversive.SphereCoefficients n) :
    Inversive.sphereCoefficientCarrier (orthogonal φ a) = Inversive.cartanLinearExtensionHom φ ''
      Inversive.sphereCoefficientCarrier a := by
  apply Inversive.coefficientCarrier_transport
  intro b z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    change b.1 * ‖φ x‖ ^ 2 - 2 * inner ℝ (φ x) (φ b.2.1) + b.2.2 = 0 ↔ _
    rw [φ.norm_map, φ.inner_map_map]
    rfl

theorem orthogonal_discriminant (φ : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) (a :
    Inversive.SphereCoefficients n) :
    Inversive.sphereDiscriminant (orthogonal φ a) = Inversive.sphereDiscriminant a := by
  simp only [Inversive.sphereDiscriminant, orthogonal, φ.norm_map]

theorem orthogonal_pairing (φ : Inversive.Euclidean n ≃ₗᵢ[ℝ] Inversive.Euclidean n) (a b :
    Inversive.SphereCoefficients n) :
    Inversive.inversivePairing (orthogonal φ a) (orthogonal φ b) = Inversive.inversivePairing a b := by
  simp only [Inversive.inversivePairing, orthogonal, φ.inner_map_map]

def translation (b : Inversive.Euclidean n) (a : Inversive.SphereCoefficients n) : Inversive.SphereCoefficients n :=
  (a.1, a.2.1 + a.1 • b, a.2.2 + 2 * inner ℝ b a.2.1 + a.1 * ‖b‖ ^ 2)

theorem translation_carrier (b : Inversive.Euclidean n) (a : Inversive.SphereCoefficients n) :
    Inversive.sphereCoefficientCarrier (translation b a) = Inversive.translationHomeomorph b ''
      Inversive.sphereCoefficientCarrier a := by
  apply Inversive.coefficientCarrier_transport
  intro d z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    change d.1 * ‖x + b‖ ^ 2 - 2 * inner ℝ (x + b) (d.2.1 + d.1 • b) +
      (d.2.2 + 2 * inner ℝ b d.2.1 + d.1 * ‖b‖ ^ 2) = 0 ↔
        d.1 * ‖x‖ ^ 2 - 2 * inner ℝ x d.2.1 + d.2.2 = 0
    rw [norm_add_sq_real]
    simp only [inner_add_left, inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
    have he : d.1 * (‖x‖ ^ 2 + 2 * inner ℝ x b + ‖b‖ ^ 2) -
        2 * ((inner ℝ x d.2.1 + inner ℝ b d.2.1) + (d.1 * inner ℝ x b + d.1 * ‖b‖ ^ 2)) +
        (d.2.2 + 2 * inner ℝ b d.2.1 + d.1 * ‖b‖ ^ 2) =
        d.1 * ‖x‖ ^ 2 - 2 * inner ℝ x d.2.1 + d.2.2 := by ring
    rw [he]

theorem translation_discriminant (b : Inversive.Euclidean n) (a : Inversive.SphereCoefficients n) :
    Inversive.sphereDiscriminant (translation b a) = Inversive.sphereDiscriminant a := by
  simp only [Inversive.sphereDiscriminant, translation, norm_add_sq_real, real_inner_smul_right,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  rw [real_inner_comm b a.2.1]
  ring

theorem translation_pairing (c : Inversive.Euclidean n) (a b : Inversive.SphereCoefficients n) :
    Inversive.inversivePairing (translation c a) (translation c b) = Inversive.inversivePairing a b := by
  simp only [Inversive.inversivePairing, translation, inner_add_left, inner_add_right, real_inner_smul_right,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  rw [real_inner_comm c a.2.1]
  ring


def dilation (k : ℝ) (a : Inversive.SphereCoefficients n) : Inversive.SphereCoefficients n :=
  (a.1, k • a.2.1, k ^ 2 * a.2.2)

theorem dilation_carrier (k : ℝ) (hk : k ≠ 0) (a : Inversive.SphereCoefficients n) :
    Inversive.sphereCoefficientCarrier (dilation k a) = Inversive.dilationHomeomorph k hk ''
      Inversive.sphereCoefficientCarrier a := by
  apply Inversive.coefficientCarrier_transport
  intro d z
  induction z using OnePoint.rec with
  | infty => rfl
  | coe x =>
    change d.1 * ‖k • x‖ ^ 2 - 2 * inner ℝ (k • x) (k • d.2.1) + k ^ 2 * d.2.2 = 0 ↔
      d.1 * ‖x‖ ^ 2 - 2 * inner ℝ x d.2.1 + d.2.2 = 0
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_left, real_inner_smul_right]
    rw [show d.1 * (k ^ 2 * ‖x‖ ^ 2) - 2 * (k * (k * inner ℝ x d.2.1)) + k ^ 2 * d.2.2 =
      k ^ 2 * (d.1 * ‖x‖ ^ 2 - 2 * inner ℝ x d.2.1 + d.2.2) by ring]
    simp only [mul_eq_zero, pow_ne_zero 2 hk, false_or]

theorem dilation_discriminant (k : ℝ) (a : Inversive.SphereCoefficients n) :
    Inversive.sphereDiscriminant (dilation k a) = k ^ 2 * Inversive.sphereDiscriminant a := by
  simp only [Inversive.sphereDiscriminant, dilation, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  ring

theorem dilation_pairing (k : ℝ) (a b : Inversive.SphereCoefficients n) :
    Inversive.inversivePairing (dilation k a) (dilation k b) = k ^ 2 * Inversive.inversivePairing a b := by
  simp only [Inversive.inversivePairing, dilation, real_inner_smul_left, real_inner_smul_right]
  ring

theorem dilation_product (k : ℝ) (hk : k ≠ 0) (a b : Inversive.SphereCoefficients n) :
    Inversive.coefficientInversiveProduct (dilation k a) (dilation k b) = Inversive.coefficientInversiveProduct a
      b := by
  unfold Inversive.coefficientInversiveProduct
  rw [dilation_pairing, dilation_discriminant, dilation_discriminant, abs_mul, abs_of_nonneg (sq_nonneg k),
    Real.sqrt_mul (sq_nonneg k), Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq_eq_abs]
  have hd : 2 * (|k| * Real.sqrt (Inversive.sphereDiscriminant a)) * (|k| * Real.sqrt
    (Inversive.sphereDiscriminant b)) =
      k ^ 2 * (2 * Real.sqrt (Inversive.sphereDiscriminant a) * Real.sqrt (Inversive.sphereDiscriminant b)) := by
    calc
      _ = |k| ^ 2 * (2 * Real.sqrt (Inversive.sphereDiscriminant a) * Real.sqrt (Inversive.sphereDiscriminant b))
        := by ring
      _ = _ := by rw [sq_abs]
  rw [hd]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 hk)

def unitInversion (a : Inversive.SphereCoefficients n) : Inversive.SphereCoefficients n := (a.2.2, a.2.1, a.1)

theorem unitInversion_carrier (a : Inversive.SphereCoefficients n) :
    Inversive.sphereCoefficientCarrier (unitInversion a) =
      Inversive.sphereInversionHomeomorph (0 : Inversive.Euclidean n) 1 one_ne_zero ''
        Inversive.sphereCoefficientCarrier a := by
  apply Inversive.coefficientCarrier_transport
  intro d z
  induction z using OnePoint.rec with
  | infty =>
    simp [Inversive.sphereInversionHomeomorph_apply, Inversive.sphereCoefficientCarrier, unitInversion]
  | coe x =>
    by_cases hx : x = 0
    · subst x
      simp [Inversive.sphereInversionHomeomorph_apply, Inversive.sphereCoefficientCarrier, unitInversion]
    · rw [Inversive.sphereInversionHomeomorph_apply, Inversive.sphereInversion_coe (0 : Inversive.Euclidean n) 1
        hx, Inversive.inversion_unit]
      change d.2.2 * ‖Inversive.unitInversion x‖ ^ 2 - 2 * inner ℝ (Inversive.unitInversion x) d.2.1 + d.1 = 0 ↔
        d.1 * ‖x‖ ^ 2 - 2 * inner ℝ x d.2.1 + d.2.2 = 0
      rw [Inversive.norm_sq_unitInversion x hx]
      simp only [Inversive.unitInversion, real_inner_smul_left]
      have hn : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hx)
      have he : d.2.2 * (‖x‖ ^ 2)⁻¹ - 2 * ((‖x‖ ^ 2)⁻¹ * inner ℝ x d.2.1) + d.1 =
          (d.1 * ‖x‖ ^ 2 - 2 * inner ℝ x d.2.1 + d.2.2) / ‖x‖ ^ 2 := by
        field_simp
        ring
      rw [he, div_eq_zero_iff]
      exact or_iff_left hn

theorem unitInversion_discriminant (a : Inversive.SphereCoefficients n) :
    Inversive.sphereDiscriminant (unitInversion a) = Inversive.sphereDiscriminant a := by
  simp only [Inversive.sphereDiscriminant, unitInversion]
  ring

theorem unitInversion_pairing (a b : Inversive.SphereCoefficients n) :
    Inversive.inversivePairing (unitInversion a) (unitInversion b) = Inversive.inversivePairing a b := by
  simp only [Inversive.inversivePairing, unitInversion]
  ring


end InversiveCoefficients

/-- Orthogonal coordinate changes preserve the geometric inversive product. -/
theorem orthogonal_preservesInversiveProduct [NeZero n] (φ : Euclidean n ≃ₗᵢ[ℝ] Euclidean n)
    (hφ : cartanLinearExtensionHom φ ∈ generalMobiusGroup n) :
    PreservesInversiveProduct (cartanLinearExtensionHom φ) hφ := by
  apply preservesInversiveProduct_of_coefficients _ _ (Inversive.InversiveCoefficients.orthogonal φ)
    (Inversive.InversiveCoefficients.orthogonal_carrier φ)
  · intro a ha
    rwa [Inversive.InversiveCoefficients.orthogonal_discriminant]
  · intro a b
    simp only [coefficientInversiveProduct, Inversive.InversiveCoefficients.orthogonal_pairing,
      Inversive.InversiveCoefficients.orthogonal_discriminant]

/-- Translations preserve the geometric inversive product. -/
theorem translation_preservesInversiveProduct [NeZero n] (c : Euclidean n) :
    PreservesInversiveProduct (translationHomeomorph c) (translation_mem_generalMobiusGroup c) := by
  apply preservesInversiveProduct_of_coefficients _ _ (Inversive.InversiveCoefficients.translation c)
    (Inversive.InversiveCoefficients.translation_carrier c)
  · intro a ha
    rwa [Inversive.InversiveCoefficients.translation_discriminant]
  · intro a b
    simp only [coefficientInversiveProduct, Inversive.InversiveCoefficients.translation_pairing,
      Inversive.InversiveCoefficients.translation_discriminant]

/-- Positive dilations preserve the geometric inversive product. -/
theorem dilation_preservesInversiveProduct [NeZero n] (k : ℝ) (hk : 0 < k) :
    PreservesInversiveProduct (dilationHomeomorph (n := n) k hk.ne') (dilation_mem_generalMobiusGroup k hk) := by
  apply preservesInversiveProduct_of_coefficients _ _ (Inversive.InversiveCoefficients.dilation k)
    (Inversive.InversiveCoefficients.dilation_carrier k hk.ne')
  · intro a ha
    rw [Inversive.InversiveCoefficients.dilation_discriminant]
    exact mul_pos (sq_pos_of_pos hk) ha
  · exact Inversive.InversiveCoefficients.dilation_product k hk.ne'

/-- Unit-sphere inversion interchanges the leading and constant coefficients. -/
theorem unitSphere_preservesInversiveProduct [NeZero n] :
    PreservesInversiveProduct (sphereInversionHomeomorph (0 : Euclidean n) 1 one_ne_zero)
      (sphereInversion_isReflection (0 : Euclidean n) 1 zero_lt_one).mem_generalMobiusGroup := by
  apply preservesInversiveProduct_of_coefficients _ _ Inversive.InversiveCoefficients.unitInversion
    Inversive.InversiveCoefficients.unitInversion_carrier
  · intro a ha
    rwa [Inversive.InversiveCoefficients.unitInversion_discriminant]
  · intro a b
    simp only [coefficientInversiveProduct, Inversive.InversiveCoefficients.unitInversion_pairing,
      Inversive.InversiveCoefficients.unitInversion_discriminant]

/-- Similarities preserve the geometric inversive product. -/
theorem similarity_preservesInversiveProduct [NeZero n] (c : Euclidean n) (r : ℝ) (hr : 0 < r) :
    PreservesInversiveProduct (similarityHomeomorph c r hr.ne') (similarity_mem_generalMobiusGroup c r hr) :=
  (translation_preservesInversiveProduct c).mul (dilation_preservesInversiveProduct r hr)

/-- Every actual generating reflection preserves the geometric inversive product. -/
theorem IsReflection.preservesInversiveProduct [NeZero n] {f : ExtendedHomeomorph n} (hf : IsReflection f) :
    PreservesInversiveProduct f hf.mem_generalMobiusGroup := by
  rcases hf with ⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩
  · have h := ((similarity_preservesInversiveProduct c r hr).mul
        unitSphere_preservesInversiveProduct).mul (similarity_preservesInversiveProduct c r hr).inv
    simpa only [← sphereInversion_similarity_conjugacy c r hr] using h
  · let b := (t / ‖a‖ ^ 2) • a
    have hb : inner ℝ b a = t := by
      dsimp [b]
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      exact div_mul_cancel₀ t (pow_ne_zero _ (norm_ne_zero_iff.mpr ha))
    have hφ : cartanLinearExtensionHom (cartanPlaneLinearIsometry a) ∈ generalMobiusGroup n := by
      rw [cartanLinearExtension_plane a ha]
      exact (planeReflection_isReflection a 0 ha).mem_generalMobiusGroup
    have hlin := orthogonal_preservesInversiveProduct (cartanPlaneLinearIsometry a) hφ
    simp only [cartanLinearExtension_plane a ha] at hlin
    have h := ((translation_preservesInversiveProduct b).mul hlin).mul
      (translation_preservesInversiveProduct b).inv
    simpa only [translation_conjugate_plane a b 0 ha, zero_add, hb] using h

/-- For actual generalized spheres and the complete reflection-generated group. -/
theorem generalMobius_preservesInversiveProduct [NeZero n] (g : ExtendedHomeomorph n)
    (hg : g ∈ generalMobiusGroup n) : PreservesInversiveProduct g hg := by
  obtain ⟨l, hl, rfl⟩ := (mem_generalMobiusGroup_iff g).mp hg
  have hprod : ∀ l : List (ExtendedHomeomorph n), (∀ f ∈ l, IsReflection f) →
      ∀ hmem : l.prod ∈ generalMobiusGroup n, PreservesInversiveProduct l.prod hmem := by
    intro l
    induction l with
    | nil => intro _ _; exact Inversive.PreservesInversiveProduct.one
    | cons f l ih =>
      intro h hmem
      have hf := h f (by simp)
      have hl : ∀ k ∈ l, IsReflection k := fun k hk => h k (by simp [hk])
      have hmeml : l.prod ∈ generalMobiusGroup n :=
        (generalMobiusGroup n).list_prod_mem fun k hk => (hl k hk).mem_generalMobiusGroup
      exact hf.preservesInversiveProduct.mul (ih hl hmeml)
  exact hprod l hl hg

theorem generalizedSphereImage_inversiveProduct [NeZero n] (g : ExtendedHomeomorph n) (hg : g ∈ generalMobiusGroup n)
    (S T : GeneralizedSphere n) :
    inversiveProduct (generalizedSphereImage g hg S) (generalizedSphereImage g hg T) = inversiveProduct S T :=
  generalMobius_preservesInversiveProduct g hg S T

end LowDimensionalTopology.Geometry.Inversive
