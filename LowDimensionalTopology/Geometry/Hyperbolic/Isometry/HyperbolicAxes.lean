/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ConformalTypes
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementFunctions
public import LowDimensionalTopology.Geometry.Hyperbolic.Angle.BoundaryOrder
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteDilationGroups
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The pointwise stabilizer of zero and infinity is an actual positive dilation. -/
theorem realSLMobius_zero_infty_dilation (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h0 : (realSLMobius f).val (0 : ℂ) = (0 : ℂ))
    (hi : (realSLMobius f).val ∞ = ∞) :
    ∃ (k : ℝ) (hk : 0 < k), realSLMobius f = Mobius.mobiusScaling (Units.mk0 (k : ℂ)
      (Complex.ofReal_ne_zero.mpr hk.ne')) := by
  let g := Matrix.SpecialLinearGroup.mapGL ℝ f
  have hci : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) ∞ = ∞ := by
    simpa only [realSLMobius, MonoidHom.comp_apply, Mobius.invariantDisc_specialLinear_action,
      realSLMobius_matrix] using hi
  have hc : f 1 0 = 0 := realMobius_fix_infty_coeff g hci
  have hp := (Mobius.Classification.fractionalLinear_fixed_coe_iff
    (Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map Complex.ofRealHom f)) 0).mp
      (show Mobius.fractionalLinear _ ((0 : ℂ) : Mobius.ExtendedComplex) = (0 : ℂ) by
        simpa only [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action] using h0)
  have hb : f 0 1 = 0 := by
    change (f 1 0 : ℂ) * (0 * 0) + ((f 1 1 : ℂ) - (f 0 0 : ℂ)) * 0 + -(f 0 1 : ℂ) = 0 at hp
    have h : (f 0 1 : ℂ) = 0 := by simpa using hp
    exact Complex.ofReal_eq_zero.mp h
  have hd := f.property
  rw [Matrix.det_fin_two,hb,hc,mul_zero,sub_zero] at hd
  have hd0 : f 1 1 ≠ 0 := by intro he; rw [he,mul_zero] at hd; norm_num at hd
  have hprod : 0 < f 0 0 * f 1 1 := by rw [hd]; norm_num
  have hk : 0 < f 0 0 / f 1 1 := div_pos_iff.mpr (mul_pos_iff.mp hprod)
  let k := f 0 0 / f 1 1
  refine ⟨k,hk,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro p
  rw [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action]
  induction p using OnePoint.rec with
  | infty =>
    rw [Mobius.fractionalLinear_infty,Mobius.mobiusScaling_infty]
    change (if (f 1 0 : ℂ) = 0 then ∞ else _) = ∞
    simp [hc]
  | coe z =>
    rw [Mobius.fractionalLinear_coe,Mobius.mobiusScaling_coe]
    change (if (f 1 0 : ℂ) * z + (f 1 1 : ℂ) = 0 then ∞ else
      ((((f 0 0 : ℂ) * z + (f 0 1 : ℂ)) / ((f 1 0 : ℂ) * z + (f 1 1 : ℂ)) : ℂ) : Mobius.ExtendedComplex)) = _
    rw [hc,hb]
    simp only [Complex.ofReal_zero,zero_mul,zero_add,add_zero]
    rw [ite_eq_right (Complex.ofReal_ne_zero.mpr hd0)]
    apply congrArg OnePoint.some
    change (f 0 0 : ℂ) * z / (f 1 1 : ℂ) = (k : ℂ) * z
    dsimp [k]
    push_cast
    ring


/-- Any nontrivial real hyperbolic transformation has a genuine real dilation normal form. -/
theorem realSLMobius_hyperbolic_normalizer (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) :
    ∃ (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) (k : ℝ) (hk : 0 < k), k ≠ 1 ∧
      realSLMobius (s * f * s⁻¹) = Mobius.mobiusScaling (Units.mk0 (k : ℂ) (Complex.ofReal_ne_zero.mpr hk.ne')) ∧
      ∀ z : ℍ, (s * f * s⁻¹) • z = verticalDilationSL k hk • z := by
  obtain ⟨a,b,hab,ha,hb,hfix⟩ := realSLMobius_hyperbolic_fixed_pair f hf ht
  obtain ⟨s,hsa,hsb⟩ := realSLMobius_boundary_pair_normalizer a b ha hb hab
  have hfa := (hfix a).mpr (Or.inl rfl)
  have hfb := (hfix b).mpr (Or.inr rfl)
  have h0 : (realSLMobius (s * f * s⁻¹)).val (0 : ℂ) = (0 : ℂ) := by
    rw [map_mul,map_mul,map_inv,← hsa]
    change (realSLMobius s).val ((realSLMobius f).val ((realSLMobius s).val.symm ((realSLMobius s).val a))) = _
    rw [Equiv.symm_apply_apply,hfa]
  have hi : (realSLMobius (s * f * s⁻¹)).val ∞ = ∞ := by
    rw [map_mul,map_mul,map_inv,← hsb]
    change (realSLMobius s).val ((realSLMobius f).val ((realSLMobius s).val.symm ((realSLMobius s).val b))) = _
    rw [Equiv.symm_apply_apply,hfb]
  obtain ⟨k,hk,hkg⟩ := realSLMobius_zero_infty_dilation (s * f * s⁻¹) h0 hi
  refine ⟨s,k,hk,?_,hkg,?_⟩
  · intro hk1
    have hu : Units.mk0 (k : ℂ) (Complex.ofReal_ne_zero.mpr hk.ne') = 1 := by
      apply Units.ext
      simpa using congrArg (fun r : ℝ => (r : ℂ)) hk1
    rw [hu,DiscreteGroups.mobiusScaling_one,map_mul,map_mul,map_inv] at hkg
    apply hf
    calc
      realSLMobius f = (realSLMobius s)⁻¹ * (realSLMobius s * realSLMobius f * (realSLMobius s)⁻¹) * realSLMobius s := by group
      _ = 1 := by rw [hkg]; simp
  · intro z
    apply UpperHalfPlane.ext
    apply OnePoint.coe_injective
    rw [← realSLMobius_action,hkg,Mobius.mobiusScaling_coe,verticalDilationSL_coe]
    rfl

/-- The actual axis candidate has exactly the two actual fixed points as ideal endpoints. -/
theorem realSLMobius_hyperbolic_axis_exists (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) :
    ∃ L : HalfPlaneLine, L.idealEndpoints = Function.fixedPoints (realSLMobius f).val := by
  obtain ⟨a,b,hab,ha,hb,hfix⟩ := realSLMobius_hyperbolic_fixed_pair f hf ht
  obtain ⟨s,hsa,hsb⟩ := realSLMobius_boundary_pair_normalizer a b ha hb hab
  let g := Matrix.SpecialLinearGroup.mapGL ℝ s
  have hg : 0 < g.val.det := by change 0 < s.val.det; rw [s.property]; norm_num
  obtain ⟨L,hL⟩ := exists_halfPlaneLine_of_isHLine (realMobius_axis_preimage_isHLine g hg)
  have h0 : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) a = (0 : ℂ) := by
    simpa only [realSLMobius, MonoidHom.comp_apply, Mobius.invariantDisc_specialLinear_action,
      realSLMobius_matrix] using hsa
  have hi : Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) b = ∞ := by
    simpa only [realSLMobius, MonoidHom.comp_apply, Mobius.invariantDisc_specialLinear_action,
      realSLMobius_matrix] using hsb
  refine ⟨L,(L.idealEndpoints_eq_of_normalizer_images g hg hL a b h0 hi).trans ?_⟩
  ext z
  exact (hfix z).symm


/-- The axis is the genuine h-line with the two actual ideal fixed endpoints. -/
def hHyperbolicAxis (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) : HalfPlaneLine :=
  Classical.choose (realSLMobius_hyperbolic_axis_exists f hf ht)

theorem hHyperbolicAxis_idealEndpoints (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) :
    (hHyperbolicAxis f hf ht).idealEndpoints = Function.fixedPoints (realSLMobius f).val :=
  Classical.choose_spec (realSLMobius_hyperbolic_axis_exists f hf ht)

theorem hHyperbolicAxis_unique (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) (L : HalfPlaneLine)
    (hL : L.idealEndpoints = Function.fixedPoints (realSLMobius f).val) :
    L = hHyperbolicAxis f hf ht :=
  HalfPlaneLine.idealEndpoints_injective (hL.trans (hHyperbolicAxis_idealEndpoints f hf ht).symm)

/-- The translation length is the actual infimum of actual hyperbolic displacements. -/
def hTranslationLength (g : ℍ ≃ᵢ ℍ) : ℝ := sInf (range (hDisplacement g))

theorem hTranslationLength_eq_of_min (g : ℍ ≃ᵢ ℍ) (T : ℝ)
    (hbound : ∀ z : ℍ, T ≤ hDisplacement g z) (z : ℍ) (hz : hDisplacement g z = T) :
    hTranslationLength g = T := by
  have hb : BddBelow (range (hDisplacement g)) := ⟨T,by rintro _ ⟨w,rfl⟩; exact hbound w⟩
  exact le_antisymm (csInf_le hb ⟨z,hz⟩)
    (le_csInf (range_nonempty _) (by rintro _ ⟨w,rfl⟩; exact hbound w))

theorem hTranslationLength_conjugation (g h : ℍ ≃ᵢ ℍ) :
    hTranslationLength ((h.symm.trans g).trans h) = hTranslationLength g := by
  unfold hTranslationLength
  congr 1
  ext r
  constructor
  · rintro ⟨z,rfl⟩
    refine ⟨h.symm z,?_⟩
    simpa only [h.apply_symm_apply] using (hDisplacement_conjugation g h (h.symm z)).symm
  · rintro ⟨z,rfl⟩
    exact ⟨h z,hDisplacement_conjugation g h z⟩

theorem dilation_translation_lower_bound (k : ℝ) (hk : 0 < k) (z : ℍ) :
    |Real.log k| ≤ dist z (verticalDilationSL k hk • z) := by
  have h := dilation_half_displacement k hk z
  have hc := Real.one_le_cosh ((HalfPlaneLine.vertical 0).pointDist z)
  have hs : 0 ≤ Real.sinh (|Real.log k| / 2) := Real.sinh_nonneg_iff.mpr (by positivity)
  have he : Real.sinh (|Real.log k| / 2) ≤ Real.sinh (dist z (verticalDilationSL k hk • z) / 2) := by
    nlinarith
  have he' := Real.sinh_le_sinh.mp he
  linarith

theorem dilation_translation_on_axis (k : ℝ) (hk : 0 < k) (z : ℍ) (hz : z.re = 0) :
    dist z (verticalDilationSL k hk • z) = |Real.log k| := by
  have hpd : (HalfPlaneLine.vertical 0).pointDist z = 0 :=
    Metric.infDist_zero_of_mem hz
  have h := dilation_half_displacement k hk z
  rw [hpd,Real.cosh_zero,one_mul] at h
  have he := Real.sinh_injective h
  linarith

theorem dilation_translationLength (k : ℝ) (hk : 0 < k) :
    hTranslationLength (hSLIsometry (verticalDilationSL k hk)) = |Real.log k| :=
  hTranslationLength_eq_of_min _ _ (dilation_translation_lower_bound k hk) UpperHalfPlane.I
    (dilation_translation_on_axis k hk _ (by simp))


theorem dilation_translation_minimum_iff (k : ℝ) (hk : 0 < k) (hk1 : k ≠ 1) (z : ℍ) :
    dist z (verticalDilationSL k hk • z) = |Real.log k| ↔ z.re = 0 := by
  constructor
  · intro he
    have hs : 0 < Real.sinh (|Real.log k| / 2) := Real.sinh_pos_iff.mpr (by
      have h := abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hk hk1)
      linarith)
    have h := dilation_half_displacement k hk z
    rw [he] at h
    have hc : Real.cosh ((HalfPlaneLine.vertical 0).pointDist z) = 1 := by nlinarith
    have hi := Real.cosh_sq_sub_sinh_sq ((HalfPlaneLine.vertical 0).pointDist z)
    rw [hc] at hi
    have hp : Real.sinh ((HalfPlaneLine.vertical 0).pointDist z) = 0 := by nlinarith
    rw [verticalLine_pointDist_sinh] at hp
    have hz0 : |z.re - 0| = 0 := (div_eq_zero_iff.mp hp).resolve_right z.im_ne_zero
    simpa only [sub_zero,abs_eq_zero] using hz0
  · exact dilation_translation_on_axis k hk z

theorem hSLIsometry_conjugation (f s : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    hSLIsometry (s * f * s⁻¹) = ((hSLIsometry s).symm.trans (hSLIsometry f)).trans (hSLIsometry s) := by
  apply IsometryEquiv.ext
  intro z
  change (s * f * s⁻¹) • z = s • (f • (s⁻¹ • z))
  simp only [mul_smul]

theorem realSLMobius_hyperbolic_translationLength (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) :
    ∃ (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) (k : ℝ) (hk : 0 < k), k ≠ 1 ∧
      (∀ z : ℍ, (s * f * s⁻¹) • z = verticalDilationSL k hk • z) ∧
      hTranslationLength (hSLIsometry f) = |Real.log k| := by
  obtain ⟨s,k,hk,hk1,_,hact⟩ := realSLMobius_hyperbolic_normalizer f hf ht
  refine ⟨s,k,hk,hk1,hact,?_⟩
  have hg : hSLIsometry (s * f * s⁻¹) = hSLIsometry (verticalDilationSL k hk) := by
    apply IsometryEquiv.ext
    intro z
    exact hact z
  rw [← hTranslationLength_conjugation (hSLIsometry f) (hSLIsometry s),
    ← hSLIsometry_conjugation,hg,dilation_translationLength]

theorem hHyperbolic_translationLength_pos (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) :
    0 < hTranslationLength (hSLIsometry f) := by
  obtain ⟨_,k,hk,hk1,_,he⟩ := realSLMobius_hyperbolic_translationLength f hf ht
  rw [he]
  exact abs_pos.mpr (Real.log_ne_zero_of_pos_of_ne_one hk hk1)


theorem realSLMobius_conjugate_fixed_iff (f s : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : Mobius.ExtendedComplex) :
    (realSLMobius (s * f * s⁻¹)).val ((realSLMobius s).val z) = (realSLMobius s).val z ↔
      (realSLMobius f).val z = z := by
  rw [map_mul,map_mul,map_inv]
  change (realSLMobius s).val ((realSLMobius f).val ((realSLMobius s).val.symm ((realSLMobius s).val z))) =
    (realSLMobius s).val z ↔ _
  rw [Equiv.symm_apply_apply,(realSLMobius s).val.injective.eq_iff]

theorem hHyperbolicAxis_normalizer_carrier (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2)
    (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) (k : ℝ) (hk : 0 < k) (hk1 : k ≠ 1)
    (hn : realSLMobius (s * f * s⁻¹) = Mobius.mobiusScaling (Units.mk0 (k : ℂ) (Complex.ofReal_ne_zero.mpr hk.ne'))) :
    (hHyperbolicAxis f hf ht).carrier = {z : ℍ | (s • z).re = 0} := by
  let g := Matrix.SpecialLinearGroup.mapGL ℝ s
  have hg : 0 < g.val.det := by change 0 < s.val.det; rw [s.property]; norm_num
  obtain ⟨L,hL⟩ := exists_halfPlaneLine_of_isHLine (realMobius_axis_preimage_isHLine g hg)
  have hq : (realSLMobius s).val = Mobius.fractionalLinear (complexifiedRealMobiusMatrix g) := by
    rw [realSLMobius,MonoidHom.comp_apply,Mobius.invariantDisc_specialLinear_action,realSLMobius_matrix]
  have hkC : (k : ℂ) ≠ 1 := by exact_mod_cast hk1
  have hfix (z : Mobius.ExtendedComplex) : (realSLMobius f).val z = z ↔
      (realSLMobius s).val z = (0 : ℂ) ∨ (realSLMobius s).val z = ∞ := by
    rw [← realSLMobius_conjugate_fixed_iff f s z,hn,DiscreteGroups.mobiusScaling_eq_standard _ hkC,
      Mobius.mobiusStandardElement_boundary_fixed_iff _ hkC]
  have hli : (g • · : ℍ → ℍ) '' L.carrier = (HalfPlaneLine.vertical 0).carrier := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      rw [hL] at hw
      exact hw
    · intro hz
      change z.re = 0 at hz
      refine ⟨g⁻¹ • z,?_,smul_inv_smul g z⟩
      rw [hL]
      change (g • (g⁻¹ • z)).re = 0
      simpa only [smul_inv_smul] using hz
  have hle : (realSLMobius s).val '' L.idealEndpoints = {((0 : ℂ) : Mobius.ExtendedComplex),∞} := by
    rw [hq,← L.idealEndpoints_realGL_image (HalfPlaneLine.vertical 0) g hg hli,vertical_idealEndpoints]
    simp only [Complex.ofReal_zero]
  have hfe : (realSLMobius s).val '' Function.fixedPoints (realSLMobius f).val =
      {((0 : ℂ) : Mobius.ExtendedComplex),∞} := by
    ext z
    constructor
    · rintro ⟨w,hw,rfl⟩
      exact (hfix w).mp hw
    · intro hz
      change z = (0 : ℂ) ∨ z = ∞ at hz
      refine ⟨(realSLMobius s).val.symm z,?_,(realSLMobius s).val.apply_symm_apply z⟩
      apply (hfix _).mpr
      simpa only [Equiv.apply_symm_apply] using hz
  have hends : L.idealEndpoints = Function.fixedPoints (realSLMobius f).val :=
    (Set.image_injective.mpr (realSLMobius s).val.injective) (hle.trans hfe.symm)
  have heL := hHyperbolicAxis_unique f hf ht L hends
  rw [← heL]
  exact hL


/-- The exact axis, metric infimum, and action share one actual real normalizer. -/
theorem hHyperbolicAxis_normalizer (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) :
    ∃ (s : Matrix.SpecialLinearGroup (Fin 2) ℝ) (k : ℝ) (hk : 0 < k), k ≠ 1 ∧
      (hHyperbolicAxis f hf ht).carrier = {z : ℍ | (s • z).re = 0} ∧
      hTranslationLength (hSLIsometry f) = |Real.log k| ∧
      ∀ z : ℍ, (s * f * s⁻¹) • z = verticalDilationSL k hk • z := by
  obtain ⟨s,k,hk,hk1,hn,hact⟩ := realSLMobius_hyperbolic_normalizer f hf ht
  refine ⟨s,k,hk,hk1,hHyperbolicAxis_normalizer_carrier f hf ht s k hk hk1 hn,?_,hact⟩
  have hg : hSLIsometry (s * f * s⁻¹) = hSLIsometry (verticalDilationSL k hk) := by
    apply IsometryEquiv.ext
    intro z
    exact hact z
  rw [← hTranslationLength_conjugation (hSLIsometry f) (hSLIsometry s),
    ← hSLIsometry_conjugation,hg,dilation_translationLength]

/-- The actual metric displacement is minimal exactly on the actual axis. -/
theorem hHyperbolic_translation_minimum (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) (z : ℍ) :
    dist z (f • z) = hTranslationLength (hSLIsometry f) ↔ z ∈ (hHyperbolicAxis f hf ht).carrier := by
  obtain ⟨s,k,hk,hk1,hL,hT,hact⟩ := hHyperbolicAxis_normalizer f hf ht
  have hd : dist z (f • z) = dist (s • z) (verticalDilationSL k hk • (s • z)) := by
    calc
      dist z (f • z) = dist (s • z) (s • (f • z)) := ((isometry_smul ℍ s).dist_eq z (f • z)).symm
      _ = _ := by rw [← hact (s • z)]; simp only [mul_smul,inv_smul_smul]
  rw [hd,hT,dilation_translation_minimum_iff k hk hk1,hL]
  rfl

theorem hHyperbolic_translation_minimum_attained (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) :
    ∃ z ∈ (hHyperbolicAxis f hf ht).carrier,
      dist z (f • z) = hTranslationLength (hSLIsometry f) := by
  obtain ⟨z,hz,_⟩ := (hHyperbolicAxis f hf ht).exists_point_ne UpperHalfPlane.I
  exact ⟨z,hz,(hHyperbolic_translation_minimum f hf ht z).mpr hz⟩

/-- The metric translation infimum satisfies the original real trace identity. -/
theorem hHyperbolic_translation_trace (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) :
    Real.cosh (hTranslationLength (hSLIsometry f) / 2) ^ 2 = (Matrix.trace f.val) ^ 2 / 4 := by
  obtain ⟨s,k,hk,hk1,hn,hact⟩ := realSLMobius_hyperbolic_normalizer f hf ht
  have hkC : (k : ℂ) ≠ 1 := by exact_mod_cast hk1
  have he := congrArg Mobius.mobiusSquaredTrace hn
  rw [map_mul,map_mul,map_inv,Mobius.mobiusSquaredTrace_conjugation,realSLMobius_squaredTrace,
    DiscreteGroups.mobiusScaling_eq_standard _ hkC,Mobius.mobiusStandardElement_squaredTrace] at he
  have htr : (Matrix.trace f.val) ^ 2 = k + k⁻¹ + 2 := by
    change (((Matrix.trace f.val) ^ 2 : ℝ) : ℂ) = (k : ℂ) + (k : ℂ)⁻¹ + 2 at he
    exact_mod_cast he
  have hT : hTranslationLength (hSLIsometry f) = |Real.log k| := by
    have hg : hSLIsometry (s * f * s⁻¹) = hSLIsometry (verticalDilationSL k hk) := by
      apply IsometryEquiv.ext
      intro z
      exact hact z
    rw [← hTranslationLength_conjugation (hSLIsometry f) (hSLIsometry s),
      ← hSLIsometry_conjugation,hg,dilation_translationLength]
  rw [hT,htr]
  have hh := Real.cosh_two_mul (|Real.log k| / 2)
  rw [show 2 * (|Real.log k| / 2) = |Real.log k| by ring,Real.cosh_abs,Real.cosh_log hk] at hh
  linarith [Real.cosh_sq_sub_sinh_sq (|Real.log k| / 2)]


theorem hHyperbolic_translation_abs_trace (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) :
    |Matrix.trace f.val| / 2 = Real.cosh (hTranslationLength (hSLIsometry f) / 2) := by
  apply (sq_eq_sq₀ (by positivity) (Real.cosh_pos _).le).mp
  rw [hHyperbolic_translation_trace f hf ht,div_pow,sq_abs]
  norm_num

/-- The metric minimum characterization also proves actual invariance of the axis. -/
theorem hHyperbolicAxis_invariant (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) :
    (f • · : ℍ → ℍ) '' (hHyperbolicAxis f hf ht).carrier = (hHyperbolicAxis f hf ht).carrier := by
  ext z
  constructor
  · rintro ⟨w,hw,rfl⟩
    apply (hHyperbolic_translation_minimum f hf ht _).mp
    rw [(isometry_smul ℍ f).dist_eq w (f • w)]
    exact (hHyperbolic_translation_minimum f hf ht w).mpr hw
  · intro hz
    refine ⟨f⁻¹ • z,?_,smul_inv_smul f z⟩
    apply (hHyperbolic_translation_minimum f hf ht _).mp
    rw [smul_inv_smul]
    have he := (isometry_smul ℍ f).dist_eq (f⁻¹ • z) z
    rw [smul_inv_smul] at he
    rw [← he]
    exact (hHyperbolic_translation_minimum f hf ht z).mpr hz

/-- The corresponding axis is an actual native disc-line, obtained by the actual Cayley map. -/
def dHyperbolicAxis (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) : DiscLine :=
  (hHyperbolicAxis f hf ht).toDiscLine

theorem dHyperbolicAxis_carrier (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) :
    (dHyperbolicAxis f hf ht).carrier = halfPlaneToDisc '' (hHyperbolicAxis f hf ht).carrier := by
  rw [dHyperbolicAxis,HalfPlaneLine.toDiscLine_carrier,HalfPlaneLine.discCarrier_eq_cayley_image]

/-- The disc-model translation length is its actual weighted-path-distance infimum. -/
def dTranslationLength (g : 𝔻 → 𝔻) : ℝ := sInf (range (fun z => discPathDist z (g z)))

theorem dTranslationLength_realSL (f : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    dTranslationLength (discRealGL (Matrix.SpecialLinearGroup.mapGL ℝ f)) =
      hTranslationLength (hSLIsometry f) := by
  unfold dTranslationLength hTranslationLength
  simp only [discPathDist_eq_halfPlane,discRealGL,discToHalfPlane_halfPlaneToDisc]
  change sInf (range (fun z : 𝔻 => dist (discToHalfPlane z) (f • discToHalfPlane z))) =
    sInf (range (fun z : ℍ => dist z (f • z)))
  congr 1
  ext r
  constructor
  · rintro ⟨z,rfl⟩
    exact ⟨discToHalfPlane z,rfl⟩
  · rintro ⟨z,rfl⟩
    refine ⟨halfPlaneToDisc z,?_⟩
    simp only [discToHalfPlane_halfPlaneToDisc]

theorem dHyperbolic_translation_minimum (f : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hf : realSLMobius f ≠ 1) (ht : 4 < (Matrix.trace f.val) ^ 2) (z : 𝔻) :
    discPathDist z (discRealGL (Matrix.SpecialLinearGroup.mapGL ℝ f) z) =
      dTranslationLength (discRealGL (Matrix.SpecialLinearGroup.mapGL ℝ f)) ↔
      z ∈ (dHyperbolicAxis f hf ht).carrier := by
  rw [dTranslationLength_realSL,discPathDist_eq_halfPlane]
  unfold discRealGL
  rw [discToHalfPlane_halfPlaneToDisc]
  change (dist (discToHalfPlane z) (f • discToHalfPlane z) = hTranslationLength (hSLIsometry f)) ↔ _
  rw [hHyperbolic_translation_minimum,dHyperbolicAxis_carrier]
  constructor
  · intro hz
    exact ⟨discToHalfPlane z,hz,halfPlaneToDisc_discToHalfPlane z⟩
  · rintro ⟨w,hw,rfl⟩
    simpa only [discToHalfPlane_halfPlaneToDisc] using hw

end LowDimensionalTopology.Geometry.Hyperbolic
