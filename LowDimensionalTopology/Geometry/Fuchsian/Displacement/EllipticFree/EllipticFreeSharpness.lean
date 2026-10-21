/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Discreteness.EllipticFreeDiscreteness
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenSharpness
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.MetricFormulas
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology OnePoint UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces

/-- Integral special-linear representatives project to the actual geometric group. -/
def ellipticFreeIntegralProjection : Matrix.SpecialLinearGroup (Fin
  2) ℤ →* _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection.comp (Matrix.SpecialLinearGroup.map
    (Int.castRingHom ℂ))

/-- The level-two congruence condition forces trace congruent to two modulo four. -/
theorem ellipticFree_gammaTwo_trace (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : A ∈ CongruenceSubgroup.Gamma 2) :
    ∃ k : ℤ, Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℤ) = 2 + 4 * k := by
  obtain ⟨h00, h01, h10, h11⟩ := CongruenceSubgroup.Gamma_mem.mp hA
  have hd00 : (2 : ℤ) ∣ A 0 0 - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    simpa only [Int.cast_sub, Int.cast_one, sub_eq_zero] using h00
  have hd11 : (2 : ℤ) ∣ A 1 1 - 1 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp
    simpa only [Int.cast_sub, Int.cast_one, sub_eq_zero] using h11
  obtain ⟨a, ha⟩ := hd00
  obtain ⟨b, hb⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h01
  obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h10
  obtain ⟨d, hd⟩ := hd11
  have hdet := A.det_coe
  rw [Matrix.det_fin_two] at hdet
  refine ⟨b * c - a * d, ?_⟩
  rw [Matrix.trace_fin_two]
  have h00a : A 0 0 = 1 + 2 * a := by omega
  have h11d : A 1 1 = 1 + 2 * d := by omega
  rw [h00a, h11d, hb, hc] at hdet
  norm_num at hdet
  have he : a + d = 2 * (b * c - a * d) := by nlinarith [hdet]
  omega

/-- All congruence-group special-linear traces lie outside the elliptic interval. -/
theorem ellipticFree_gammaTwo_trace_sq (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : A ∈ CongruenceSubgroup.Gamma 2) :
    (4 : ℝ) ≤ (↑(Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℤ) : ℤ) : ℝ) ^ 2 := by
  obtain ⟨k, hk⟩ := ellipticFree_gammaTwo_trace A hA
  rw [hk]
  push_cast
  by_cases hk0 : 0 ≤ k
  · have hkr : (0 : ℝ) ≤ k := by exact_mod_cast hk0
    nlinarith
  · have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
    nlinarith

/-- The projective level-two congruence group contains no actual elliptics. -/
theorem ellipticFree_gammaTwo_projection :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree ((CongruenceSubgroup.Gamma 2).map ellipticFreeIntegralProjection) := by
  intro f hf
  obtain ⟨A, hA, hAf⟩ := f.property
  obtain ⟨r, _, hr,
    he⟩ := (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four _
    hf.1).mp hf
  have he' : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection
      (Matrix.SpecialLinearGroup.map (Int.castRingHom ℂ) A)) = (r : ℂ) :=
    (congrArg _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace hAf).trans he
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_specialLinearProjection] at he'
  have hcast : Matrix.trace ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℂ) A :
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) :
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) =
      (↑(Matrix.trace (A : Matrix (Fin 2) (Fin 2) ℤ) : ℤ) : ℂ) := by
    simp [Matrix.trace_fin_two]
  rw [hcast] at he'
  have hr' := congrArg Complex.re he'
  norm_cast at hr'
  push_cast at hr'
  have hb := ellipticFree_gammaTwo_trace_sq A hA
  nlinarith

/-- Two explicit integral unipotents realize the limiting ideal-square configuration. -/
def ellipticFreeSharpnessFirstLift : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, 2; 0, 1], by simp⟩
def ellipticFreeSharpnessSecondLift : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
  ⟨!![1, 0; 2, 1], by simp⟩
def ellipticFreeSharpnessFirst : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  ellipticFreeIntegralProjection ellipticFreeSharpnessFirstLift
def ellipticFreeSharpnessSecond : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  ellipticFreeIntegralProjection ellipticFreeSharpnessSecondLift
def ellipticFreeSharpnessGroup : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  Subgroup.closure ({ellipticFreeSharpnessFirst, ellipticFreeSharpnessSecond} : Set
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)

theorem ellipticFreeSharpness_lifts_gammaTwo :
    ellipticFreeSharpnessFirstLift ∈ CongruenceSubgroup.Gamma 2 ∧
      ellipticFreeSharpnessSecondLift ∈ CongruenceSubgroup.Gamma 2 := by
  constructor <;> rw [CongruenceSubgroup.Gamma_mem] <;>
    norm_num [ellipticFreeSharpnessFirstLift, ellipticFreeSharpnessSecondLift]
  all_goals decide

theorem ellipticFreeSharpnessGroup_le_gammaTwo :
    ellipticFreeSharpnessGroup ≤ (CongruenceSubgroup.Gamma 2).map ellipticFreeIntegralProjection := by
  apply (Subgroup.closure_le _).mpr
  rintro f (rfl | rfl)
  · exact Subgroup.mem_map.mpr ⟨_, ellipticFreeSharpness_lifts_gammaTwo.1, rfl⟩
  · exact Subgroup.mem_map.mpr ⟨_, ellipticFreeSharpness_lifts_gammaTwo.2, rfl⟩

theorem ellipticFreeSharpnessGroup_ellipticFree : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree ellipticFreeSharpnessGroup := by
  intro f
  exact ellipticFree_gammaTwo_projection ⟨f.val, ellipticFreeSharpnessGroup_le_gammaTwo f.property⟩


/-- The concrete generated group preserves the genuine upper-half-plane disc. -/
theorem ellipticFreeSharpnessGroup_invariantDisc : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc ellipticFreeSharpnessGroup := by
  refine ⟨_root_.LowDimensionalTopology.Geometry.Mobius.standardComplexHalfDisc,
    _root_.LowDimensionalTopology.Geometry.Mobius.standardComplexHalfDisc_isDisc, ?_⟩
  intro f
  obtain ⟨A, _, hAf⟩ := ellipticFreeSharpnessGroup_le_gammaTwo f.property
  have he := _root_.LowDimensionalTopology.Geometry.Mobius.specialLinear_real_preserves_halfDisc
    (Matrix.SpecialLinearGroup.map (Int.castRingHom ℂ) A) (by intro i j; simp)
  exact hAf ▸ he

theorem ellipticFreeSharpness_generators :
    ellipticFreeSharpnessFirst ∈ ellipticFreeSharpnessGroup ∧
      ellipticFreeSharpnessSecond ∈ ellipticFreeSharpnessGroup := by
  constructor <;> apply Subgroup.subset_closure <;> simp

/-- The first generator is the actual translation by two. -/
theorem ellipticFreeSharpnessFirst_translation :
    ellipticFreeSharpnessFirst = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 2 := by
  apply Subtype.ext
  apply Equiv.ext
  intro z
  rw [ellipticFreeSharpnessFirst, ellipticFreeIntegralProjection, MonoidHom.comp_apply,
    _root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action]
  induction z using OnePoint.rec with
  | infty =>
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_infty,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty]
    norm_num [ellipticFreeSharpnessFirstLift, Matrix.SpecialLinearGroup.toGL]
  | coe z =>
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_coe,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
    norm_num [ellipticFreeSharpnessFirstLift, Matrix.SpecialLinearGroup.toGL]

theorem ellipticFreeSharpnessSecond_infty :
    ellipticFreeSharpnessSecond.val ∞ = ((1 / 2 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  rw [ellipticFreeSharpnessSecond, ellipticFreeIntegralProjection, MonoidHom.comp_apply,
    _root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action, _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_infty]
  norm_num [ellipticFreeSharpnessSecondLift, Matrix.SpecialLinearGroup.toGL]

/-- The second generator is genuinely parabolic, with its other fixed point at zero. -/
theorem ellipticFreeSharpnessSecond_parabolic : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic ellipticFreeSharpnessSecond := by
  have hn : ellipticFreeSharpnessSecond ≠ 1 := by
    intro he
    have hx := ellipticFreeSharpnessSecond_infty
    rw [he] at hx
    exact OnePoint.infty_ne_coe _ hx
  apply (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_parabolic_iff_squaredTrace_eq_four _ hn).mpr
  rw [ellipticFreeSharpnessSecond, ellipticFreeIntegralProjection, MonoidHom.comp_apply,
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_specialLinearProjection]
  norm_num [Matrix.trace_fin_two, ellipticFreeSharpnessSecondLift]

/-- The two actual parabolic generators have distinct fixed points and form a non-elementary group. -/
theorem ellipticFreeSharpnessGroup_nonElementary : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary ellipticFreeSharpnessGroup := by
  intro he
  have hp : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic ellipticFreeSharpnessFirst := by
    rw [ellipticFreeSharpnessFirst_translation]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff 2).mpr (by norm_num)
  obtain ⟨a, ha, hh⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.elementary_parabolic_common_fixedPoint _ he _ ellipticFreeSharpness_generators.1 hp
  have hia : (∞ : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = a := (ha ∞).mp (by
    rw [ellipticFreeSharpnessFirst_translation,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty])
  have hx := hh ⟨ellipticFreeSharpnessSecond, ellipticFreeSharpness_generators.2⟩
  rw [← hia] at hx
  change ellipticFreeSharpnessSecond.val ∞ = ∞ at hx
  rw [ellipticFreeSharpnessSecond_infty] at hx
  exact OnePoint.coe_ne_infty _ hx

/-- Discreteness follows from the genuine elliptic-free disc-group theorem, without taking it as a hypothesis. -/
theorem ellipticFreeSharpnessGroup_discrete : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup ellipticFreeSharpnessGroup :=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_of_ellipticFree_nonElementary_invariant_disc _ ellipticFreeSharpnessGroup_invariantDisc
    ellipticFreeSharpnessGroup_ellipticFree ellipticFreeSharpnessGroup_nonElementary

/-- The genuine displacement of each displayed unipotent at j has half-sinh equal to one. -/
theorem ellipticFreeSharpness_displacements :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement ellipticFreeSharpnessFirst _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = 1 ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement ellipticFreeSharpnessSecond _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = 1 := by
  have hp (A : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) (ht : Matrix.trace (A :
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) = 2)
      (hn : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm ((A :
        _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) - 1) ^ 2 = 4) :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A) _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = 1 := by
    have hh := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_trace_two_difference_eq_sinh A ht
    change _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm ((A :
      _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) - 1) =
      2 * _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A) _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ at hh
    nlinarith [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement_nonneg
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A)
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ]
  constructor
  · refine hp (Matrix.SpecialLinearGroup.map (Int.castRingHom ℂ) ellipticFreeSharpnessFirstLift) ?_ ?_
    · norm_num [ellipticFreeSharpnessFirstLift, Matrix.trace_fin_two]
    · norm_num [ellipticFreeSharpnessFirstLift, _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm_sq,
      Matrix.sub_apply, Matrix.one_apply]
  · refine hp (Matrix.SpecialLinearGroup.map (Int.castRingHom ℂ) ellipticFreeSharpnessSecondLift) ?_ ?_
    · norm_num [ellipticFreeSharpnessSecondLift, Matrix.trace_fin_two]
    · norm_num [ellipticFreeSharpnessSecondLift, _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm_sq,
      Matrix.sub_apply, Matrix.one_apply]


/-- The lower bound one is attained by an actual elliptic-free, discrete,
non-elementary two-generator group, with both displacement factors equal to one. -/
theorem ellipticFreeSharpness_exists : ∃ f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,
    _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc (Subgroup.closure ({f, g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree (Subgroup.closure ({f, g} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, g} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f, g} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement f _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = 1 ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement g _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = 1 := by
  refine ⟨ellipticFreeSharpnessFirst, ellipticFreeSharpnessSecond,
    ellipticFreeSharpnessGroup_invariantDisc, ellipticFreeSharpnessGroup_ellipticFree,
    ellipticFreeSharpnessGroup_discrete, ellipticFreeSharpnessGroup_nonElementary, ?_,
    ellipticFreeSharpnessSecond_parabolic, ellipticFreeSharpness_displacements⟩
  rw [ellipticFreeSharpnessFirst_translation]
  exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_parabolic_iff 2).mpr (by norm_num)


/-- The equality witness also uses the literal native hyperbolic-plane metric
at i, with the displayed images given by the actual geometric Mobius maps. -/
theorem ellipticFreeSharpness_native : ∃ u v : ℍ,
    ellipticFreeSharpnessFirst.val (Complex.I : ℂ) = ((u : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧
      ellipticFreeSharpnessSecond.val (Complex.I : ℂ) = ((v : ℂ) :
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧
      Real.sinh (dist UpperHalfPlane.I u / 2) = 1 ∧
      Real.sinh (dist UpperHalfPlane.I v / 2) = 1 := by
  let u : ℍ := ⟨⟨2, 1⟩, by norm_num⟩
  let v : ℍ := ⟨⟨2 / 5, 1 / 5⟩, by norm_num⟩
  refine ⟨u, v, ?_, ?_, ?_, ?_⟩
  · rw [ellipticFreeSharpnessFirst_translation,
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
    apply congrArg OnePoint.some
    apply Complex.ext <;> simp [u]
  · rw [ellipticFreeSharpnessSecond, ellipticFreeIntegralProjection, MonoidHom.comp_apply,
      _root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action, _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_coe]
    norm_num [ellipticFreeSharpnessSecondLift, Matrix.SpecialLinearGroup.toGL, v,
      Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq_apply]
  all_goals
    have hp : ∀ w : ℍ, Real.cosh (dist UpperHalfPlane.I w) = 3 →
        Real.sinh (dist UpperHalfPlane.I w / 2) = 1 := by
      intro w hw
      have hd := Real.cosh_two_mul (dist UpperHalfPlane.I w / 2)
      rw [show 2 * (dist UpperHalfPlane.I w / 2) = dist UpperHalfPlane.I w by ring, hw] at hd
      have hs := Real.cosh_sq_sub_sinh_sq (dist UpperHalfPlane.I w / 2)
      have hn : 0 ≤ Real.sinh (dist UpperHalfPlane.I w / 2) :=
        Real.sinh_nonneg_iff.mpr (by positivity)
      nlinarith
    apply hp
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlane_cosh_dist_eq_norm_sq_formula]
    norm_num [u, v, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im]

end LowDimensionalTopology.Geometry.Fuchsian
