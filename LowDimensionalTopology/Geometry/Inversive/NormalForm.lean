/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.CrossRatio
public import LowDimensionalTopology.Geometry.Inversive.Orientation
public import LowDimensionalTopology.Geometry.Euclidean.EuclideanIsometries
/-!
# Similarities and the isometric sphere

Normal forms are equalities of homeomorphisms of the one-point compactification,
including the pole and infinity. Their positive scale and Euclidean isometry
are unique. The isometric sphere is defined by an actual punctured distance-ratio
limit, and its geometric description is derived from the normal form.

The affine branch fixes infinity; the nonaffine branch has a finite pole
and factors into a similarity and an inversion. These forms also determine
local expansion and contraction relative to the isometric sphere.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint
open Filter EuclideanGeometry
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}

def extendedIsometry (φ : Euclidean n ≃ᵢ Euclidean n) : ExtendedHomeomorph n :=
  φ.toHomeomorph.onePointCongr

@[simp] theorem extendedIsometry_coe (φ : Euclidean n ≃ᵢ Euclidean n) (x : Euclidean n) :
    extendedIsometry φ x = (φ x : ExtendedEuclidean n) := rfl

@[simp] theorem extendedIsometry_infty (φ : Euclidean n ≃ᵢ Euclidean n) :
    extendedIsometry φ ∞ = ∞ := rfl

theorem extendedIsometry_mem_generalMobiusGroup (φ : Euclidean n ≃ᵢ Euclidean n) :
    extendedIsometry φ ∈ generalMobiusGroup n := by
  have he : extendedIsometry φ = euclideanIsometryHomeomorph φ φ.isometry := by
    ext z
    induction z using OnePoint.rec <;> rfl
  rw [he]
  exact euclideanIsometry_mem_generalMobiusGroup φ φ.isometry

def extendedSimilarity (k : ℝ) (hk : 0 < k) (φ : Euclidean n ≃ᵢ Euclidean n) :
    ExtendedHomeomorph n := dilationHomeomorph k hk.ne' * extendedIsometry φ

@[simp] theorem extendedSimilarity_coe (k : ℝ) (hk : 0 < k)
    (φ : Euclidean n ≃ᵢ Euclidean n) (x : Euclidean n) :
    extendedSimilarity k hk φ x = ((k • φ x : Euclidean n) : ExtendedEuclidean n) := rfl

@[simp] theorem extendedSimilarity_infty (k : ℝ) (hk : 0 < k)
    (φ : Euclidean n ≃ᵢ Euclidean n) : extendedSimilarity k hk φ ∞ = ∞ := rfl

theorem extendedSimilarity_mem_generalMobiusGroup (k : ℝ) (hk : 0 < k)
    (φ : Euclidean n ≃ᵢ Euclidean n) : extendedSimilarity k hk φ ∈ generalMobiusGroup n :=
  (generalMobiusGroup n).mul_mem (dilation_mem_generalMobiusGroup k hk)
    (extendedIsometry_mem_generalMobiusGroup φ)

@[simp] theorem finiteEuclideanPart_extendedSimilarity (k : ℝ) (hk : 0 < k)
    (φ : Euclidean n ≃ᵢ Euclidean n) (x : Euclidean n) :
    finiteEuclideanPart (extendedSimilarity k hk φ) x = k • φ x := rfl

theorem extendedSimilarity_dist (k : ℝ) (hk : 0 < k)
    (φ : Euclidean n ≃ᵢ Euclidean n) (x y : Euclidean n) :
    dist (finiteEuclideanPart (extendedSimilarity k hk φ) x)
      (finiteEuclideanPart (extendedSimilarity k hk φ) y) = k * dist x y := by
  rw [finiteEuclideanPart_extendedSimilarity, finiteEuclideanPart_extendedSimilarity,
    dist_smul₀, Real.norm_eq_abs, abs_of_pos hk, φ.dist_eq]

theorem extendedSimilarity_unique [NeZero n] {k l : ℝ} (hk : 0 < k) (hl : 0 < l)
    (φ ψ : Euclidean n ≃ᵢ Euclidean n)
    (he : extendedSimilarity k hk φ = extendedSimilarity l hl ψ) : k = l ∧ φ = ψ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : Euclidean n)
  have hd := congrArg (fun f : ExtendedHomeomorph n ↦
    dist (finiteEuclideanPart f 0) (finiteEuclideanPart f v)) he
  rw [extendedSimilarity_dist, extendedSimilarity_dist] at hd
  have hkEq : k = l := (mul_left_inj' (dist_ne_zero.mpr hv.symm)).mp hd
  refine ⟨hkEq, ?_⟩
  ext x : 1
  have hx := congrArg (fun f : ExtendedHomeomorph n ↦ finiteEuclideanPart f x) he
  simp only [finiteEuclideanPart_extendedSimilarity, hkEq] at hx
  have hh := congrArg (fun y : Euclidean n ↦ l⁻¹ • y) hx
  simpa [smul_smul, hl.ne'] using hh

theorem fixing_infty_extendedSimilarity [NeZero n] {f : ExtendedHomeomorph n}
    (hf : PreservesRealCrossRatios (f : ExtendedEuclidean n → ExtendedEuclidean n))
    (hinfty : f ∞ = ∞) :
    ∃ k : ℝ, ∃ hk : 0 < k, ∃ φ : Euclidean n ≃ᵢ Euclidean n,
      f = extendedSimilarity k hk φ := by
  obtain ⟨k, φ, hk, hφ⟩ := hf.fixing_infty_similarity hinfty
  refine ⟨k, hk, φ, ?_⟩
  ext z
  induction z using OnePoint.rec with
  | infty => simpa using hinfty
  | coe x => exact hφ x

theorem fixing_infty_orthogonal_affine [NeZero n] {f : ExtendedHomeomorph n}
    (hf : PreservesRealCrossRatios (f : ExtendedEuclidean n → ExtendedEuclidean n))
    (hinfty : f ∞ = ∞) :
    ∃ k : ℝ, 0 < k ∧ ∃ A : Matrix (Fin n) (Fin n) ℝ, ∃ b : Euclidean n,
      Auxiliary.Algebra.OrthogonalMatrix A ∧ ∀ x : Euclidean n,
      f (x : ExtendedEuclidean n) =
        ((k • WithLp.toLp 2 (Matrix.vecMul x.ofLp A) + b : Euclidean n) : ExtendedEuclidean n) := by
  obtain ⟨k, hk, φ, rfl⟩ := fixing_infty_extendedSimilarity hf hinfty
  obtain ⟨A, hA, hφ⟩ := Euclidean.euclideanIsometry_orthogonal_affine φ φ.isometry
  refine ⟨k, hk, A, k • φ 0, hA, ?_⟩
  intro x
  rw [extendedSimilarity_coe, hφ x, smul_add]

def nonAffineNormalForm (c : Euclidean n) (k : ℝ) (hk : 0 < k)
    (φ : Euclidean n ≃ᵢ Euclidean n) : ExtendedHomeomorph n :=
  extendedSimilarity k hk φ * sphereInversionHomeomorph c 1 one_ne_zero

@[simp] theorem nonAffineNormalForm_center (c : Euclidean n) (k : ℝ) (hk : 0 < k)
    (φ : Euclidean n ≃ᵢ Euclidean n) : nonAffineNormalForm c k hk φ c = ∞ := by
  simp [nonAffineNormalForm, Homeomorph.mul_apply, sphereInversionHomeomorph_apply]

@[simp] theorem nonAffineNormalForm_infty (c : Euclidean n) (k : ℝ) (hk : 0 < k)
    (φ : Euclidean n ≃ᵢ Euclidean n) :
    nonAffineNormalForm c k hk φ ∞ = ((k • φ c : Euclidean n) : ExtendedEuclidean n) := by
  simp [nonAffineNormalForm, Homeomorph.mul_apply, sphereInversionHomeomorph_apply]

theorem nonAffineNormalForm_coe (c x : Euclidean n) (k : ℝ) (hk : 0 < k)
    (φ : Euclidean n ≃ᵢ Euclidean n) (hx : x ≠ c) :
    nonAffineNormalForm c k hk φ x =
      ((k • φ (inversion c 1 x) : Euclidean n) : ExtendedEuclidean n) := by
  simp only [nonAffineNormalForm, Homeomorph.mul_apply, sphereInversionHomeomorph_apply]
  rw [sphereInversion_coe c 1 hx, extendedSimilarity_coe]

theorem nonAffineNormalForm_mem_generalMobiusGroup (c : Euclidean n) (k : ℝ) (hk : 0 < k)
    (φ : Euclidean n ≃ᵢ Euclidean n) : nonAffineNormalForm c k hk φ ∈ generalMobiusGroup n :=
  (generalMobiusGroup n).mul_mem (extendedSimilarity_mem_generalMobiusGroup k hk φ)
    (sphereInversion_isReflection c 1 zero_lt_one).mem_generalMobiusGroup

theorem nonAffineNormalForm_unique [NeZero n] {c d : Euclidean n} {k l : ℝ}
    (hk : 0 < k) (hl : 0 < l) (φ ψ : Euclidean n ≃ᵢ Euclidean n)
    (he : nonAffineNormalForm c k hk φ = nonAffineNormalForm d l hl ψ) :
    c = d ∧ k = l ∧ φ = ψ := by
  have hd : nonAffineNormalForm d l hl ψ c = ∞ := by rw [← he]; exact nonAffineNormalForm_center _ _ _ _
  have hcd : c = d := OnePoint.coe_injective
    ((nonAffineNormalForm d l hl ψ).injective (hd.trans (nonAffineNormalForm_center d l hl ψ).symm))
  subst d
  have heSim : extendedSimilarity k hk φ = extendedSimilarity l hl ψ :=
    mul_right_cancel he
  exact ⟨rfl, extendedSimilarity_unique hk hl φ ψ heSim⟩


theorem finiteEuclideanPart_nonAffineNormalForm (c x : Euclidean n) (k : ℝ) (hk : 0 < k)
    (φ : Euclidean n ≃ᵢ Euclidean n) (hx : x ≠ c) :
    finiteEuclideanPart (nonAffineNormalForm c k hk φ) x = k • φ (inversion c 1 x) := by
  rw [finiteEuclideanPart, nonAffineNormalForm_coe c x k hk φ hx]
  rfl

theorem nonAffineNormalForm_dist (c x y : Euclidean n) (k : ℝ) (hk : 0 < k)
    (φ : Euclidean n ≃ᵢ Euclidean n) (hx : x ≠ c) (hy : y ≠ c) :
    dist (finiteEuclideanPart (nonAffineNormalForm c k hk φ) x)
      (finiteEuclideanPart (nonAffineNormalForm c k hk φ) y) =
      k / (dist x c * dist y c) * dist x y := by
  rw [finiteEuclideanPart_nonAffineNormalForm c x k hk φ hx,
    finiteEuclideanPart_nonAffineNormalForm c y k hk φ hy,
    dist_smul₀, Real.norm_eq_abs, abs_of_pos hk, φ.dist_eq, sphereInversion_dist 1 hx hy]
  ring

theorem nonAffineNormalForm_scale_limit (c x : Euclidean n) (k : ℝ) (hk : 0 < k)
    (φ : Euclidean n ≃ᵢ Euclidean n) (hx : x ≠ c) :
    Tendsto (fun y : Euclidean n ↦
      dist (finiteEuclideanPart (nonAffineNormalForm c k hk φ) y)
        (finiteEuclideanPart (nonAffineNormalForm c k hk φ) x) / dist y x)
      (𝓝[≠] x) (𝓝 (k / dist x c ^ 2)) := by
  have hl := (sphereInversion_scale_limit 1 hx).const_mul k
  simp only [one_pow, mul_one_div] at hl
  apply hl.congr'
  filter_upwards [(eventually_ne_nhds hx).filter_mono nhdsWithin_le_nhds] with y hy
  rw [finiteEuclideanPart_nonAffineNormalForm c y k hk φ hy,
    finiteEuclideanPart_nonAffineNormalForm c x k hk φ hx,
    dist_smul₀, Real.norm_eq_abs, abs_of_pos hk, φ.dist_eq]
  ring

/-- The actual unit infinitesimal Euclidean scale locus, with poles excluded. -/
def isometricSphere (f : ExtendedHomeomorph n) : Set (Euclidean n) :=
  {x | f (x : ExtendedEuclidean n) ≠ ∞ ∧
    Tendsto (fun y : Euclidean n ↦ dist (finiteEuclideanPart f y) (finiteEuclideanPart f x) / dist y x)
      (𝓝[≠] x) (𝓝 1)}

theorem nonAffineNormalForm_isometricSphere [NeZero n] (c : Euclidean n) (k : ℝ)
    (hk : 0 < k) (φ : Euclidean n ≃ᵢ Euclidean n) :
    isometricSphere (nonAffineNormalForm c k hk φ) = Metric.sphere c (Real.sqrt k) := by
  ext x
  constructor
  · rintro ⟨hx, hscale⟩
    have hxc : x ≠ c := by intro h; subst x; exact hx (nonAffineNormalForm_center c k hk φ)
    have hs : k / dist x c ^ 2 = 1 :=
      tendsto_nhds_unique (nonAffineNormalForm_scale_limit c x k hk φ hxc) hscale
    have hden : dist x c ^ 2 ≠ 0 := pow_ne_zero 2 (dist_ne_zero.mpr hxc)
    have hsq : dist x c ^ 2 = k := by
      have he := (div_eq_iff hden).mp hs
      simpa only [one_mul] using he.symm
    change dist x c = Real.sqrt k
    nlinarith [Real.sq_sqrt hk.le, Real.sqrt_pos.mpr hk, dist_nonneg (x := x) (y := c)]
  · intro hx
    change dist x c = Real.sqrt k at hx
    have hxc : x ≠ c := by intro h; subst x; simp only [dist_self] at hx; exact (Real.sqrt_pos.mpr hk).ne' hx.symm
    refine ⟨?_, ?_⟩
    · rw [nonAffineNormalForm_coe c x k hk φ hxc]
      exact OnePoint.coe_ne_infty _
    · have hs : k / dist x c ^ 2 = 1 := by rw [hx, Real.sq_sqrt hk.le, div_self hk.ne']
      simpa only [hs] using nonAffineNormalForm_scale_limit c x k hk φ hxc

theorem nonAffineNormalForm_isometry_on_sphere (c x y : Euclidean n) (k : ℝ)
    (hk : 0 < k) (φ : Euclidean n ≃ᵢ Euclidean n)
    (hx : x ∈ Metric.sphere c (Real.sqrt k)) (hy : y ∈ Metric.sphere c (Real.sqrt k)) :
    dist (finiteEuclideanPart (nonAffineNormalForm c k hk φ) x)
      (finiteEuclideanPart (nonAffineNormalForm c k hk φ) y) = dist x y := by
  have hdx : dist x c = Real.sqrt k := hx
  have hdy : dist y c = Real.sqrt k := hy
  have hxc : x ≠ c := (dist_pos.mp (hdx ▸ Real.sqrt_pos.mpr hk))
  have hyc : y ≠ c := (dist_pos.mp (hdy ▸ Real.sqrt_pos.mpr hk))
  rw [nonAffineNormalForm_dist c x y k hk φ hxc hyc, hdx, hdy,
    Real.mul_self_sqrt hk.le, div_self hk.ne', one_mul]

theorem nonAffineNormalForm_scale_gt_one (c x : Euclidean n) (k : ℝ)
    (hk : 0 < k) (hx : x ≠ c) : k / dist x c ^ 2 > 1 ↔ x ∈ Metric.ball c (Real.sqrt k) := by
  rw [gt_iff_lt, lt_div_iff₀ (sq_pos_of_ne_zero (dist_ne_zero.mpr hx)), one_mul]
  change dist x c ^ 2 < k ↔ dist x c < Real.sqrt k
  constructor <;> intro h <;>
    nlinarith [Real.sq_sqrt hk.le, Real.sqrt_pos.mpr hk, dist_nonneg (x := x) (y := c)]

theorem nonAffineNormalForm_scale_lt_one (c x : Euclidean n) (k : ℝ)
    (hk : 0 < k) (hx : x ≠ c) : k / dist x c ^ 2 < 1 ↔ Real.sqrt k < dist x c := by
  rw [div_lt_one (sq_pos_of_ne_zero (dist_ne_zero.mpr hx))]
  constructor <;> intro h <;> nlinarith [Real.sq_sqrt hk.le, Real.sqrt_pos.mpr hk, dist_nonneg (x := x) (y := c)]


theorem concentric_unit_sqrt_composition [NeZero n] (c : Euclidean n) (k : ℝ) (hk : 0 < k) :
    sphereInversionHomeomorph c 1 one_ne_zero *
      sphereInversionHomeomorph c (Real.sqrt k) (Real.sqrt_pos.mpr hk).ne' =
      translationHomeomorph c * dilationHomeomorph k⁻¹ (inv_ne_zero hk.ne') *
        (translationHomeomorph c)⁻¹ := by
  have hSc : sphereInversionHomeomorph c 1 one_ne_zero =
      translationHomeomorph c * sphereInversionHomeomorph 0 1 one_ne_zero *
        (translationHomeomorph c)⁻¹ := by
    simpa only [zero_add] using (translation_conjugate_sphere (0 : Euclidean n) c 1 one_ne_zero).symm
  have hSr : sphereInversionHomeomorph c (Real.sqrt k) (Real.sqrt_pos.mpr hk).ne' =
      translationHomeomorph c * sphereInversionHomeomorph 0 (Real.sqrt k) (Real.sqrt_pos.mpr hk).ne' *
        (translationHomeomorph c)⁻¹ := by
    simpa only [zero_add] using
      (translation_conjugate_sphere (0 : Euclidean n) c (Real.sqrt k) (Real.sqrt_pos.mpr hk).ne').symm
  have hd : (dilationHomeomorph k hk.ne' : ExtendedHomeomorph n)⁻¹ =
      sphereInversionHomeomorph 0 1 one_ne_zero *
        sphereInversionHomeomorph 0 (Real.sqrt k) (Real.sqrt_pos.mpr hk).ne' := by
    rw [dilationHomeomorph_eq_reflections k hk, mul_inv_rev,
      (sphereInversion_isReflection (0 : Euclidean n) 1 zero_lt_one).inv_eq,
      (sphereInversion_isReflection (0 : Euclidean n) (Real.sqrt k) (Real.sqrt_pos.mpr hk)).inv_eq]
  calc
    _ = translationHomeomorph c *
        (sphereInversionHomeomorph 0 1 one_ne_zero *
          sphereInversionHomeomorph 0 (Real.sqrt k) (Real.sqrt_pos.mpr hk).ne') *
        (translationHomeomorph c)⁻¹ := by rw [hSc, hSr]; group
    _ = translationHomeomorph c * (dilationHomeomorph k hk.ne')⁻¹ *
        (translationHomeomorph c)⁻¹ := by rw [← hd]
    _ = _ := by rw [dilationHomeomorph_inv]

theorem normalForm_isometricFactor_isometry (c : Euclidean n) (k : ℝ) (hk : 0 < k)
    (φ : Euclidean n ≃ᵢ Euclidean n) :
    Isometry (fun x : Euclidean n ↦ k • φ (k⁻¹ • (x - c) + c)) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hk, φ.dist_eq, dist_eq_norm,
    add_sub_add_right_eq_sub, ← smul_sub]
  have hsub : (x-c)-(y-c) = x-y := by abel
  rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk),
    ← mul_assoc, mul_inv_cancel₀ hk.ne', one_mul, ← dist_eq_norm]

theorem nonAffineNormalForm_isometric_factorization [NeZero n] (c : Euclidean n)
    (k : ℝ) (hk : 0 < k) (φ : Euclidean n ≃ᵢ Euclidean n) :
    ∃ Ψ : Euclidean n ≃ᵢ Euclidean n,
      (∀ x, Ψ x = k • φ (k⁻¹ • (x-c) + c)) ∧
      nonAffineNormalForm c k hk φ = extendedIsometry Ψ *
        sphereInversionHomeomorph c (Real.sqrt k) (Real.sqrt_pos.mpr hk).ne' := by
  let Ψ := euclideanIsometryEquiv (fun x : Euclidean n ↦ k • φ (k⁻¹ • (x-c) + c))
    (normalForm_isometricFactor_isometry c k hk φ)
  have hΨ (x : Euclidean n) : Ψ x = k • φ (k⁻¹ • (x-c) + c) := rfl
  refine ⟨Ψ, hΨ, ?_⟩
  have he : nonAffineNormalForm c k hk φ *
      sphereInversionHomeomorph c (Real.sqrt k) (Real.sqrt_pos.mpr hk).ne' = extendedIsometry Ψ := by
    rw [nonAffineNormalForm, mul_assoc, concentric_unit_sqrt_composition c k hk]
    ext z
    induction z using OnePoint.rec with
    | infty => rfl
    | coe x =>
      simp only [Homeomorph.mul_apply, translationHomeomorph_inv, translationHomeomorph_coe,
        dilationHomeomorph_coe, extendedSimilarity_coe, extendedIsometry_coe, hΨ, sub_eq_add_neg]
  have hs := sphereInversion_isReflection c (Real.sqrt k) (Real.sqrt_pos.mpr hk)
  calc
    _ = extendedIsometry Ψ * (sphereInversionHomeomorph c (Real.sqrt k) (Real.sqrt_pos.mpr hk).ne')⁻¹ :=
      eq_mul_inv_iff_mul_eq.mpr he
    _ = _ := by rw [hs.inv_eq]
/-- The similarity branch for the actual reflection group. -/
theorem generalMobius_fixing_infty_normalForm [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hinfty : f ∞ = ∞) :
    ∃ k : ℝ, ∃ hk : 0 < k, ∃ φ : Euclidean n ≃ᵢ Euclidean n,
      f = extendedSimilarity k hk φ :=
  fixing_infty_extendedSimilarity (generalMobius_preservesRealCrossRatios f hf) hinfty

theorem mobius_fix_infty_similarity_normal_form [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hinfty : f ∞ = ∞) :
    ∃ k : ℝ, 0 < k ∧ ∃ A : Matrix (Fin n) (Fin n) ℝ, ∃ b : Euclidean n,
      Auxiliary.Algebra.OrthogonalMatrix A ∧ ∀ x : Euclidean n,
      f (x : ExtendedEuclidean n) =
        ((k • WithLp.toLp 2 (Matrix.vecMul x.ofLp A) + b : Euclidean n) : ExtendedEuclidean n) :=
  fixing_infty_orthogonal_affine (generalMobius_preservesRealCrossRatios f hf) hinfty

/-- The non-affine branch is a global equality, including its pole and infinity. -/
theorem generalMobius_nonAffine_normalForm [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hinfty : f ∞ ≠ ∞) :
    ∃ c : Euclidean n, ∃ k : ℝ, ∃ hk : 0 < k, ∃ φ : Euclidean n ≃ᵢ Euclidean n,
      f = nonAffineNormalForm c k hk φ := by
  have hp : f.symm ∞ ≠ ∞ := by
    intro he
    have hh := congrArg f he
    rw [f.apply_symm_apply] at hh
    exact hinfty hh.symm
  obtain ⟨c, hc⟩ := OnePoint.ne_infty_iff_exists.mp hp
  have hfc : f (c : ExtendedEuclidean n) = ∞ := by rw [hc, f.apply_symm_apply]
  let S := sphereInversionHomeomorph c 1 one_ne_zero
  have hS : IsReflection S := sphereInversion_isReflection c 1 zero_lt_one
  have hFS : f * S ∈ generalMobiusGroup n :=
    (generalMobiusGroup n).mul_mem hf hS.mem_generalMobiusGroup
  have hFSinfty : (f * S) ∞ = ∞ := by
    change f (sphereInversion c 1 ∞) = ∞
    rw [sphereInversion_infty]
    exact hfc
  obtain ⟨k, hk, φ, he⟩ := generalMobius_fixing_infty_normalForm (f * S) hFS hFSinfty
  refine ⟨c, k, hk, φ, ?_⟩
  change f = extendedSimilarity k hk φ * S
  calc
    f = (f * S) * S⁻¹ := by group
    _ = _ := by rw [he, hS.inv_eq]

theorem mobius_move_infty_similarity_mul_inversion [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hinfty : f ∞ ≠ ∞) :
    ∃ c : Euclidean n, ∃ k : ℝ, ∃ hk : 0 < k, ∃ φ : Euclidean n ≃ᵢ Euclidean n,
      f = extendedSimilarity k hk φ * sphereInversionHomeomorph c 1 one_ne_zero :=
  generalMobius_nonAffine_normalForm f hf hinfty

/-- The normal-form centre is exactly the finite preimage of infinity. -/
theorem nonAffineNormalForm_pole (c : Euclidean n) (k : ℝ) (hk : 0 < k)
    (φ : Euclidean n ≃ᵢ Euclidean n) :
    (nonAffineNormalForm c k hk φ).symm ∞ = (c : ExtendedEuclidean n) := by
  apply (nonAffineNormalForm c k hk φ).injective
  rw [Homeomorph.apply_symm_apply, nonAffineNormalForm_center]

/-- The infinitesimal scale and distance formulas determine the isometric sphere. -/
theorem generalMobius_isometricSphere [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hinfty : f ∞ ≠ ∞) :
    ∃ c : Euclidean n, ∃ R : ℝ, 0 < R ∧
      f.symm ∞ = (c : ExtendedEuclidean n) ∧
      isometricSphere f = Metric.sphere c R ∧
      (∀ x y : Euclidean n, x ≠ c → y ≠ c →
        dist (finiteEuclideanPart f x) (finiteEuclideanPart f y) =
          R ^ 2 / (dist x c * dist y c) * dist x y) ∧
      (∀ x : Euclidean n, x ≠ c →
        Tendsto (fun y : Euclidean n ↦
          dist (finiteEuclideanPart f y) (finiteEuclideanPart f x) / dist y x)
          (𝓝[≠] x) (𝓝 (R ^ 2 / dist x c ^ 2))) := by
  obtain ⟨c, k, hk, φ, rfl⟩ := generalMobius_nonAffine_normalForm f hf hinfty
  refine ⟨c, Real.sqrt k, Real.sqrt_pos.mpr hk, nonAffineNormalForm_pole c k hk φ,
    nonAffineNormalForm_isometricSphere c k hk φ, ?_, ?_⟩
  · intro x y hx hy
    simpa only [Real.sq_sqrt hk.le] using nonAffineNormalForm_dist c x y k hk φ hx hy
  · intro x hx
    simpa only [Real.sq_sqrt hk.le] using nonAffineNormalForm_scale_limit c x k hk φ hx

theorem generalMobius_isometry_on_isometricSphere [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hinfty : f ∞ ≠ ∞)
    {x y : Euclidean n} (hx : x ∈ isometricSphere f) (hy : y ∈ isometricSphere f) :
    dist (finiteEuclideanPart f x) (finiteEuclideanPart f y) = dist x y := by
  obtain ⟨c, k, hk, φ, rfl⟩ := generalMobius_nonAffine_normalForm f hf hinfty
  rw [nonAffineNormalForm_isometricSphere] at hx hy
  exact nonAffineNormalForm_isometry_on_sphere c x y k hk φ hx hy

theorem generalMobius_isometric_sphere_factorization [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hinfty : f ∞ ≠ ∞) :
    ∃ c : Euclidean n, ∃ R : ℝ, ∃ hR : 0 < R, ∃ Ψ : Euclidean n ≃ᵢ Euclidean n,
      f.symm ∞ = (c : ExtendedEuclidean n) ∧
      isometricSphere f = Metric.sphere c R ∧
      f = extendedIsometry Ψ * sphereInversionHomeomorph c R hR.ne' := by
  obtain ⟨c, k, hk, φ, rfl⟩ := generalMobius_nonAffine_normalForm f hf hinfty
  obtain ⟨Ψ, _, hΨ⟩ := nonAffineNormalForm_isometric_factorization c k hk φ
  exact ⟨c, Real.sqrt k, Real.sqrt_pos.mpr hk, Ψ, nonAffineNormalForm_pole c k hk φ,
    nonAffineNormalForm_isometricSphere c k hk φ, hΨ⟩

/-- Local expansion, unit scale and contraction use the genuine punctured limit. -/
theorem generalMobius_isometricSphere_scale_trichotomy [NeZero n] (f : ExtendedHomeomorph n)
    (hf : f ∈ generalMobiusGroup n) (hinfty : f ∞ ≠ ∞) :
    ∃ c : Euclidean n, ∃ R : ℝ, 0 < R ∧
      f.symm ∞ = (c : ExtendedEuclidean n) ∧ isometricSphere f = Metric.sphere c R ∧
      ∀ x : Euclidean n, x ≠ c → ∃ L : ℝ,
        Tendsto (fun y : Euclidean n ↦
          dist (finiteEuclideanPart f y) (finiteEuclideanPart f x) / dist y x)
          (𝓝[≠] x) (𝓝 L) ∧
        (1 < L ↔ x ∈ Metric.ball c R) ∧
        (L = 1 ↔ x ∈ Metric.sphere c R) ∧ (L < 1 ↔ R < dist x c) := by
  obtain ⟨c, k, hk, φ, rfl⟩ := generalMobius_nonAffine_normalForm f hf hinfty
  refine ⟨c, Real.sqrt k, Real.sqrt_pos.mpr hk, nonAffineNormalForm_pole c k hk φ,
    nonAffineNormalForm_isometricSphere c k hk φ, ?_⟩
  intro x hx
  refine ⟨k / dist x c ^ 2, nonAffineNormalForm_scale_limit c x k hk φ hx,
    nonAffineNormalForm_scale_gt_one c x k hk hx, ?_,
    nonAffineNormalForm_scale_lt_one c x k hk hx⟩
  change k / dist x c ^ 2 = 1 ↔ dist x c = Real.sqrt k
  rw [div_eq_one_iff_eq (pow_ne_zero 2 (dist_ne_zero.mpr hx))]
  constructor <;> intro h <;>
    nlinarith [Real.sq_sqrt hk.le, Real.sqrt_pos.mpr hk, dist_nonneg (x := x) (y := c)]

end LowDimensionalTopology.Geometry.Inversive
