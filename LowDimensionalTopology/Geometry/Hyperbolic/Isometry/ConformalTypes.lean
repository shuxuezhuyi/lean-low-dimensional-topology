/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.IsometryClassification
public import LowDimensionalTopology.Geometry.Hyperbolic.Area.TriangleAreaGeometry
public import LowDimensionalTopology.Geometry.Mobius.InvariantDisc.InvariantDiscConverse
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.AffineDiscreteGroups
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The real determinant-one action, embedded in the original geometric Mobius group. -/
def realSLMobius : Matrix.SpecialLinearGroup (Fin 2) ℝ →* Mobius.complexMobiusGroup :=
  Mobius.mobiusSpecialLinearProjection.comp (Matrix.SpecialLinearGroup.map Complex.ofRealHom)

theorem realSLMobius_matrix (f : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map Complex.ofRealHom f) =
      complexifiedRealMobiusMatrix (Matrix.SpecialLinearGroup.mapGL ℝ f) := by
  ext i j
  rfl

theorem realSLMobius_action (f : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    (realSLMobius f).val (z : ℂ) = ((f • z : ℍ) : ℂ) := by
  rw [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,realSLMobius_matrix]
  exact realMobiusMatrix_coe _ (by change 0 < f.val.det; rw [f.property]; norm_num) z

theorem realSLMobius_squaredTrace (f : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    Mobius.mobiusSquaredTrace (realSLMobius f) = ((Matrix.trace f.val) ^ 2 : ℝ) := by
  rw [realSLMobius,MonoidHom.comp_apply,Mobius.mobiusSquaredTrace_specialLinearProjection]
  simp [Matrix.trace_fin_two]

theorem realSLMobius_parabolic_iff (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) :
    Mobius.MobiusParabolic (realSLMobius f) ↔ (Matrix.trace f.val) ^ 2 = 4 := by
  change Mobius.MobiusBoundaryParabolic (realSLMobius f) ↔ (Matrix.trace f.val) ^ 2 = 4
  rw [Mobius.mobius_parabolic_iff_squaredTrace_eq_four _ hf,realSLMobius_squaredTrace]
  norm_cast

theorem realSLMobius_elliptic_iff (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) :
    Mobius.MobiusElliptic (realSLMobius f) ↔ (Matrix.trace f.val) ^ 2 < 4 := by
  rw [Mobius.mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four _ hf,realSLMobius_squaredTrace]
  constructor
  · rintro ⟨r,_,hr,he⟩
    have h : (Matrix.trace f.val) ^ 2 = r := Complex.ofReal_injective he
    rwa [h]
  · intro h
    exact ⟨_,sq_nonneg _,h,rfl⟩

theorem realSLMobius_hyperbolic_iff (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) :
    Mobius.MobiusHyperbolic (realSLMobius f) ↔ 4 < (Matrix.trace f.val) ^ 2 := by
  rw [Mobius.mobius_hyperbolic_iff_squaredTrace_real_gt_four _ hf,realSLMobius_squaredTrace]
  constructor
  · rintro ⟨r,hr,he⟩
    have h : (Matrix.trace f.val) ^ 2 = r := Complex.ofReal_injective he
    rwa [h]
  · intro h
    exact ⟨_,h,rfl⟩

theorem realSLMobius_preserves_halfDisc (f : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    (realSLMobius f).val '' Mobius.standardComplexHalfDisc = Mobius.standardComplexHalfDisc := by
  exact Mobius.specialLinear_real_preserves_halfDisc _ (by intro i j; simp)

/-- A hyperbolic real matrix has only real finite compactified fixed points. -/
theorem realSLMobius_hyperbolic_fixed_im (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : 4 < (Matrix.trace f.val) ^ 2) (z : ℂ)
    (hz : (realSLMobius f).val z = z) : z.im = 0 := by
  have hp := (Mobius.Classification.fractionalLinear_fixed_coe_iff
    (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map Complex.ofRealHom f)) z).mp
      (show Mobius.fractionalLinear _ (z : Mobius.ExtendedComplex) = z by
        simpa only [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action] using hz)
  change (f 1 0 : ℂ) * (z * z) + ((f 1 1 : ℂ) - (f 0 0 : ℂ)) * z + -(f 0 1 : ℂ) = 0 at hp
  have hr := congrArg Complex.re hp
  have hi := congrArg Complex.im hp
  simp only [Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,Complex.zero_re,Complex.mul_im,zero_mul,sub_zero,add_zero,
    Complex.add_im,Complex.sub_im,Complex.zero_im,Complex.neg_re,Complex.neg_im,neg_zero] at hr hi
  by_contra hy
  have hl : f 0 0 - f 1 1 - 2 * f 1 0 * z.re = 0 := by
    have he : z.im * (f 0 0 - f 1 1 - 2 * f 1 0 * z.re) = 0 := by nlinarith [hi]
    exact (mul_eq_zero.mp he).resolve_left hy
  have hd := f.property
  rw [Matrix.det_fin_two] at hd
  rw [Matrix.trace_fin_two] at ht
  have he : (f 0 0 + f 1 1) ^ 2 - 4 + 4 * (f 1 0 * z.im) ^ 2 = 0 := by
    linear_combination 4 * hd - 4 * f 1 0 * hr +
      (f 0 0 - f 1 1 - 2 * f 1 0 * z.re) * hl
  nlinarith [sq_nonneg (f 1 0 * z.im)]

theorem realSLMobius_hyperbolic_fixed_boundary (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (ht : 4 < (Matrix.trace f.val) ^ 2) (p : Mobius.ExtendedComplex)
    (hp : (realSLMobius f).val p = p) : p ∈ halfPlaneIdealBoundary := by
  induction p using OnePoint.rec with
  | infty => simp [halfPlaneIdealBoundary]
  | coe z => exact (coe_mem_halfPlaneIdealBoundary z).mpr (realSLMobius_hyperbolic_fixed_im f ht z hp)

theorem realSLMobius_hyperbolic_fixed_pair (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) :
    ∃ a b : Mobius.ExtendedComplex, a ≠ b ∧ a ∈ halfPlaneIdealBoundary ∧ b ∈ halfPlaneIdealBoundary ∧
      ∀ z, (realSLMobius f).val z = z ↔ z = a ∨ z = b := by
  have hH := (realSLMobius_hyperbolic_iff f hf).mpr ht
  obtain ⟨a,b,hab,hfix⟩ := DiscreteGroups.mobius_loxodromic_boundary_fixed_pair _ hH.1
  exact ⟨a,b,hab,realSLMobius_hyperbolic_fixed_boundary f ht a ((hfix a).mpr (Or.inl rfl)),
    realSLMobius_hyperbolic_fixed_boundary f ht b ((hfix b).mpr (Or.inr rfl)),hfix⟩

theorem realSLMobius_maps_boundary (f : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    MapsTo (realSLMobius f).val halfPlaneIdealBoundary halfPlaneIdealBoundary := by
  simpa only [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,realSLMobius_matrix]
    using realMobiusMatrix_maps_boundary (Matrix.SpecialLinearGroup.mapGL ℝ f)

theorem realSLMobius_horizontalNormalizer (r : ℝ) :
    (realSLMobius (horizontalNormalizer r)).val =
      Mobius.fractionalLinear (complexifiedRealMobiusMatrix (horizontalAxisNormalizer r)) := by
  rw [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,realSLMobius_matrix]
  congr 2
  ext i j
  rfl

theorem realSLMobius_exists_send_to_infty (p : Mobius.ExtendedComplex) (hp : p ∈ halfPlaneIdealBoundary) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) ℝ, (realSLMobius s).val p = ∞ := by
  obtain ⟨s,hs⟩ := halfPlaneIdealBoundary_exists_sl2_to_infty p hp
  exact ⟨s,by simpa only [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,
    realSLMobius_matrix] using hs⟩

/-- Both ordered ideal endpoints can be normalized by an actual positive real matrix. -/
theorem realSLMobius_boundary_pair_normalizer (a b : Mobius.ExtendedComplex)
    (ha : a ∈ halfPlaneIdealBoundary) (hb : b ∈ halfPlaneIdealBoundary) (hab : a ≠ b) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (realSLMobius s).val a = (0 : ℂ) ∧ (realSLMobius s).val b = ∞ := by
  obtain ⟨s,hs⟩ := realSLMobius_exists_send_to_infty b hb
  have ha' := realSLMobius_maps_boundary s ha
  have hn : (realSLMobius s).val a ≠ ∞ := fun he =>
    hab ((realSLMobius s).val.injective (he.trans hs.symm))
  cases he : (realSLMobius s).val a using OnePoint.rec with
  | infty => exact False.elim (hn he)
  | coe z =>
    rw [he,coe_mem_halfPlaneIdealBoundary] at ha'
    have hz : z = (z.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using ha'
    refine ⟨horizontalNormalizer z.re * s,?_,?_⟩
    · rw [map_mul]
      change (realSLMobius (horizontalNormalizer z.re)).val ((realSLMobius s).val a) = _
      rw [he,hz,realSLMobius_horizontalNormalizer,horizontalNormalizer_boundary]
      simp
    · rw [map_mul]
      change (realSLMobius (horizontalNormalizer z.re)).val ((realSLMobius s).val b) = _
      rw [hs,realSLMobius_horizontalNormalizer,horizontalNormalizer_boundary_infty]

end LowDimensionalTopology.Geometry.Hyperbolic
