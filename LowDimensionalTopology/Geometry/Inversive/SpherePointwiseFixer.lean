module
public import LowDimensionalTopology.Geometry.Inversive.GeneralizedSpheres
public import LowDimensionalTopology.Geometry.Inversive.CrossRatio

/-!
# Pointwise generalized-sphere fixers

A plane fixer fixes infinity. The cross-ratio theorem then gives a Euclidean
similarity, whose scale is forced to one by two distinct fixed finite points.
Its linear isometry fixes the tangent hyperplane and acts on the normal line
by either sign. Reflection conjugacy transfers this result to every sphere.
The dimension bound restores the standing n ≥ 2 assumption.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint RealInnerProductSpace
open Filter EuclideanGeometry
namespace LowDimensionalTopology.Geometry.Inversive
variable {n : ℕ}

/-- A hyperplane in dimension at least two has a nonzero tangent vector. -/
theorem exists_nonzero_normal_orthogonal (hn : 2 ≤ n) (a : Euclidean n) (ha : a ≠ 0) :
    ∃ v : Euclidean n, v ≠ 0 ∧ inner ℝ v a = 0 := by
  let K : Submodule ℝ (Euclidean n) := (ℝ ∙ a)ᗮ
  have hdim : 1 + Module.finrank ℝ K = n := by
    have h := (ℝ ∙ a).finrank_add_finrank_orthogonal
    simpa only [K, finrank_span_singleton ha, finrank_euclideanSpace, Fintype.card_fin] using h
  have hp : 0 < Module.finrank ℝ K := by omega
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hp
  refine ⟨v.val, ?_, Submodule.mem_orthogonal_singleton_iff_inner_left.mp v.property⟩
  intro hz
  exact hv (Subtype.ext hz)

/-- A linear isometry fixing a hyperplane pointwise is the identity or its orthogonal reflection. -/
theorem linearIsometry_eq_one_or_reflection (φ : Euclidean n ≃ₗᵢ[ℝ] Euclidean n)
    (a : Euclidean n) (ha : a ≠ 0) (hfix : ∀ v, inner ℝ v a = 0 → φ v = v) :
    φ = 1 ∨ φ = cartanPlaneLinearIsometry a := by
  have hmem : φ a ∈ ((ℝ ∙ a)ᗮ)ᗮ := by
    intro v hv
    have hv0 : inner ℝ v a = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.mp hv
    rw [← hfix v hv0, φ.inner_map_map]
    exact hv0
  rw [Submodule.orthogonal_orthogonal] at hmem
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hmem
  have haφ : φ a = k • a := hk.symm
  have hnorm : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr ha)
  have hsq : k ^ 2 = 1 := by
    have h := congrArg (fun v : Euclidean n => ‖v‖ ^ 2) haφ
    rw [φ.norm_map, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
    apply mul_right_cancel₀ hnorm
    simpa only [one_mul] using h.symm
  have hkpm : k = 1 ∨ k = -1 := by
    have h : (k - 1) * (k + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hdecomp (x : Euclidean n) :
      φ x = x + (inner ℝ x a / ‖a‖ ^ 2) • (φ a - a) := by
    let c := inner ℝ x a / ‖a‖ ^ 2
    have horth : inner ℝ (x - c • a) a = 0 := by
      dsimp [c]
      rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
        div_mul_cancel₀ _ hnorm, sub_self]
    have h := hfix (x - c • a) horth
    rw [map_sub, map_smul] at h
    have he : φ x = x - c • a + c • φ a := by rw [← h]; abel
    rw [he]
    dsimp [c]
    module
  rcases hkpm with hk1 | hkm
  · left
    ext x : 1
    rw [hdecomp, haφ, hk1, one_smul, sub_self, smul_zero, add_zero]
    rfl
  · right
    ext x : 1
    rw [hdecomp, haφ, hkm, neg_one_smul, cartanPlaneLinearIsometry_apply]
    unfold planeReflectionFinite
    simp only [sub_zero, div_eq_mul_inv]
    module


/-- An affine Euclidean isometry fixing an affine hyperplane pointwise has only two possibilities. -/
theorem euclideanIsometry_eq_one_or_planeReflection (ψ : Euclidean n ≃ᵢ Euclidean n)
    (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) (hfix : ∀ x, inner ℝ x a = t → ψ x = x) :
    (∀ x, ψ x = x) ∨ (∀ x, ψ x = planeReflectionFinite a t x) := by
  let F := ψ.toRealAffineIsometryEquiv
  let φ := F.linearIsometryEquiv
  let p := (t / ‖a‖ ^ 2) • a
  have hpinner : inner ℝ p a = t := by
    dsimp [p]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    exact div_mul_cancel₀ t (pow_ne_zero _ (norm_ne_zero_iff.mpr ha))
  have hp : ψ p = p := hfix p hpinner
  have hF (x : Euclidean n) : F x = ψ x := rfl
  have horth (v : Euclidean n) (hv : inner ℝ v a = 0) : φ v = v := by
    have h := F.map_vadd p v
    have hvp : inner ℝ (v + p) a = t := by rw [inner_add_left, hv, hpinner, zero_add]
    simp only [vadd_eq_add, hF] at h
    rw [hfix (v + p) hvp, hp] at h
    exact (add_right_cancel h).symm
  have hcoord (x : Euclidean n) : ψ x = φ (x - p) + p := by
    have h := F.map_vadd p (x - p)
    simpa only [vadd_eq_add, sub_add_cancel, hF, hp] using h
  rcases linearIsometry_eq_one_or_reflection φ a ha horth with hφ | hφ
  · left
    intro x
    rw [hcoord, hφ]
    simp
  · right
    intro x
    rw [hcoord, hφ, cartanPlaneLinearIsometry_apply]
    unfold planeReflectionFinite
    rw [inner_sub_left, hpinner]
    simp only [sub_zero, div_eq_mul_inv]
    module

/-- The plane pointwise-fixer statement includes the necessary dimension hypothesis. -/
theorem plane_pointwiseFixer (hn : 2 ≤ n) (g : ExtendedHomeomorph n)
    (hg : g ∈ generalMobiusGroup n) (a : Euclidean n) (t : ℝ) (ha : a ≠ 0)
    (hfix : ∀ x ∈ plane a t, g x = x) : g = 1 ∨ g = planeReflectionHomeomorph a t ha := by
  let : NeZero n := ⟨by omega⟩
  have hinfty : g ∞ = ∞ := hfix ∞ (Or.inl rfl)
  obtain ⟨k, ψ, hk, hsim⟩ := (generalMobius_preservesRealCrossRatios g hg).fixing_infty_similarity hinfty
  have hfixfinite (x : Euclidean n) (hx : inner ℝ x a = t) : k • ψ x = x := by
    apply OnePoint.coe_injective
    rw [← hsim]
    exact hfix x (Or.inr ⟨x, hx, rfl⟩)
  let p := (t / ‖a‖ ^ 2) • a
  have hp : inner ℝ p a = t := by
    dsimp [p]
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
    exact div_mul_cancel₀ t (pow_ne_zero _ (norm_ne_zero_iff.mpr ha))
  obtain ⟨v, hv, hva⟩ := exists_nonzero_normal_orthogonal hn a ha
  have hpv : inner ℝ (p + v) a = t := by rw [inner_add_left, hp, hva, add_zero]
  have hne : p + v ≠ p := by intro h; exact hv (add_left_cancel (h.trans (add_zero p).symm))
  have hdist : dist (p + v) p = k * dist (p + v) p := by
    calc
      _ = dist (k • ψ (p + v)) (k • ψ p) := by rw [hfixfinite _ hpv, hfixfinite _ hp]
      _ = _ := by rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos hk, ψ.isometry.dist_eq]
  have hk1 : k = 1 := by nlinarith [dist_pos.mpr hne]
  have hψfix (x : Euclidean n) (hx : inner ℝ x a = t) : ψ x = x := by
    simpa only [hk1, one_smul] using hfixfinite x hx
  rcases euclideanIsometry_eq_one_or_planeReflection ψ a t ha hψfix with hψ | hψ
  · left
    ext z
    induction z using OnePoint.rec with
    | infty => exact hinfty
    | coe x => rw [hsim, hk1, one_smul, hψ]; rfl
  · right
    ext z
    induction z using OnePoint.rec with
    | infty => exact hinfty
    | coe x => rw [hsim, hk1, one_smul, hψ]; rfl

/-- A pointwise sphere fixer is the identity or the sphere's unique reflection. -/
theorem generalizedSphere_pointwiseFixer (hn : 2 ≤ n) (g f : ExtendedHomeomorph n)
    (hg : g ∈ generalMobiusGroup n) (hf : IsReflection f)
    (hfix : ∀ x ∈ Function.fixedPoints f, g x = x) : g = 1 ∨ g = f := by
  let : NeZero n := ⟨by omega⟩
  obtain ⟨a, ha⟩ := exists_ne (0 : Euclidean n)
  let R := planeReflectionHomeomorph a 0 ha
  obtain ⟨h, hh, he⟩ := reflections_conjugate f R hf (planeReflection_isReflection a 0 ha)
  have hmem : h⁻¹ * g * h ∈ generalMobiusGroup n :=
    (generalMobiusGroup n).mul_mem ((generalMobiusGroup n).mul_mem ((generalMobiusGroup n).inv_mem hh) hg) hh
  have hfix' : ∀ x ∈ plane a 0, (h⁻¹ * g * h) x = x := by
    intro x hx
    have hxh : h x ∈ Function.fixedPoints f := by
      rw [he, fixedPoints_homeomorph_conjugation, fixedPoints_planeReflection a 0 ha]
      exact ⟨x, hx, rfl⟩
    change h⁻¹ (g (h x)) = x
    rw [hfix (h x) hxh]
    simp
  rcases plane_pointwiseFixer hn (h⁻¹ * g * h) hmem a 0 ha hfix' with hcase | hcase
  · left
    have hh' := congrArg (fun k : ExtendedHomeomorph n => h * k * h⁻¹) hcase
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left, mul_one, mul_inv_cancel] using hh'
  · right
    have hh' := congrArg (fun k : ExtendedHomeomorph n => h * k * h⁻¹) hcase
    have hc : h * (h⁻¹ * g * h) * h⁻¹ = g := by group
    rw [hc, ← he] at hh'
    exact hh'

end LowDimensionalTopology.Geometry.Inversive
