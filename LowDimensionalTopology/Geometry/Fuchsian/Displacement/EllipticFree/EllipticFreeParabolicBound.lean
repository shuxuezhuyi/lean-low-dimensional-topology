/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Discreteness.EllipticFreeDiscreteness
public import Mathlib.Algebra.Order.Round
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

/-- A real arithmetic progression avoiding (-2,2) has step at least four.
This is the exact rounding argument needed for the parabolic case. -/
theorem ellipticFree_progression_gap (s t : ℝ) (ht : t ≠ 0)
    (hgap : ∀ n : ℤ, 2 ≤ |s + (n : ℝ) * t|) : 4 ≤ |t| := by
  have hnear := abs_sub_round (-s / t)
  have he : s + (round (-s / t) : ℝ) * t = -(t * (-s / t - round (-s / t))) := by
    field_simp
    ring
  have h := hgap (round (-s / t))
  rw [he, abs_neg, abs_mul] at h
  have hb := mul_le_mul_of_nonneg_left hnear (abs_nonneg t)
  linarith

/-- Every integer power of a trace-two determinant-one matrix is exactly affine
in its nilpotent difference from identity. -/
theorem ellipticFree_trace_two_zpow (A : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2)
    (ht : Matrix.trace (A : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) = 2) (n : ℤ) :
    ((A ^ n : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) = 1 + (n : ℂ) • ((A : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) - 1) := by
  let X := (A : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) - 1
  have hd : A 1 1 = 2 - A 0 0 := by rw [Matrix.trace_fin_two] at ht; linear_combination ht
  have hdet : A 0 0 * (2 - A 0 0) - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two, hd] using A.det_coe
  have hnil : X * X = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [X, Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply,
        Matrix.one_apply, Matrix.zero_apply] <;> norm_num
    all_goals try rw [hd]
    · linear_combination -hdet
    · ring
    · ring
    · linear_combination -hdet
  have ha : (A : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) = X + 1 := by dsimp [X]; abel
  have hi : (A⁻¹ : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2).val = 1 - X := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, X, hd] <;> ring
  have hXA : X * (A : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) = X := by
    rw [ha, mul_add, hnil, mul_one, zero_add]
  have hXi : X * (A⁻¹ : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2).val = X := by
    rw [hi, mul_sub, mul_one, hnil, sub_zero]
  change ((A ^ n : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) :
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) = 1 + (n : ℂ) • X
  induction n using Int.induction_on with
  | zero => simp
  | succ n hn =>
    rw [zpow_add_one, Matrix.SpecialLinearGroup.coe_mul, hn, add_mul, one_mul,
      smul_mul_assoc, hXA, ha]
    push_cast
    rw [add_smul, one_smul]
    abel
  | pred n hn =>
    rw [zpow_sub_one, Matrix.SpecialLinearGroup.coe_mul, hn, add_mul, one_mul,
      smul_mul_assoc, hXi, hi]
    push_cast
    rw [sub_smul, one_smul]
    abel


/-- The trace linear form of every parabolic translate has the sharp gap four,
in arbitrary genuine complex determinant-one representatives. -/
theorem ellipticFree_parabolic_bilinear_trace_bound (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hD : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc H) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (A B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) (ht : Matrix.trace (A :
      _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) = 2)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A ∈ H) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B ∈ H)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A,
        _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    4 ≤ ‖Matrix.trace (((A : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) - 1) * (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2))‖ := by
  let t := Matrix.trace (((A : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) - 1) * (B :
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2))
  have hxt : Matrix.trace ((A : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) - 1) = 0 := by
    rw [Matrix.trace_sub, ht]
    norm_num [Matrix.trace_fin_two]
  have hrealB := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFree_specialLinear_trace H hD hE B hB).1
  have hrealAB := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFree_specialLinear_trace H hD hE (A *
    B)
    (by rw [map_mul]; exact H.mul_mem hA hB)).1
  have htreal : t.im = 0 := by
    dsimp [t]
    rw [sub_mul, one_mul, Matrix.trace_sub, Complex.sub_im]
    change (Matrix.trace ((A * B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) :
      _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)).im - _ = 0
    rw [hrealB, hrealAB, sub_self]
  have hcenter : Matrix.trace (((A : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) - 1) * ((B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) - 1)) = t := by
    rw [mul_sub, mul_one, Matrix.trace_sub, hxt, sub_zero]
  have ht0 : t ≠ 0 := by
    intro ht0
    have hc := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_parabolic_commutator_identity A B ht
    rw [hcenter, ht0, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hc
    have hmc : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A) (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B) = 2 := by
      rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace_representatives _ _ A B rfl rfl]
      exact sub_eq_zero.mp hc
    obtain ⟨z, hzA, hzB⟩ := (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_commonFixedPoint_iff_commutatorTrace_eq_two _ _).mpr hmc
    exact hPair (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_elementary_of_common_fixed _ _ z hzA
      hzB)
  have he : t = (t.re : ℂ) := Complex.ext rfl (by simpa using htreal)
  have htr0 : t.re ≠ 0 := by intro hz; exact ht0 (by rw [he, hz]; simp)
  have hgap (n : ℤ) : 2 ≤ |(Matrix.trace (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)).re + (n : ℝ) * t.re| := by
    have hmem : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection (A ^ n * B) ∈ H := by
      rw [map_mul, map_zpow]
      exact H.mul_mem (H.zpow_mem hA n) hB
    have hi := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFree_specialLinear_trace H hD hE (A ^ n *
      B) hmem).2
    have htrace : Matrix.trace ((A ^ n * B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) :
      _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) =
        Matrix.trace (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) + (n : ℂ) * t := by
      rw [Matrix.SpecialLinearGroup.coe_mul, ellipticFree_trace_two_zpow A ht,
        add_mul, one_mul, smul_mul_assoc, Matrix.trace_add, Matrix.trace_smul]
      rfl
    rw [htrace] at hi
    have hre : (Matrix.trace (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) + (n : ℂ) *
      t).re =
        (Matrix.trace (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)).re + (n : ℝ) * t.re := by simp
    rw [hre] at hi
    rcases hi with hi | hi
    · rw [abs_of_nonpos (by linarith)]
      linarith
    · exact hi.trans (le_abs_self _)
  have hbound := ellipticFree_progression_gap (Matrix.trace (B :
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)).re t.re htr0 hgap
  change 4 ≤ ‖t‖
  rw [he, Complex.norm_real, Real.norm_eq_abs]
  exact hbound

/-- The centered matrix of every elliptic-free disc-group lift is controlled by
the genuine H3 displacement at j, with the optimal factor two. -/
theorem ellipticFree_centered_norm_le_displacement (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hD : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc H) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H)
    (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B ∈ H) :
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenCenteredMatrix B) ≤
      2 * _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B) _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
  have hi := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFree_specialLinear_trace H hD hE B hB
  have he : Matrix.trace (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) = ((Matrix.trace
    (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)).re : ℂ) :=
    Complex.ext rfl (by simpa using hi.1)
  have hn : 4 ≤ ‖Matrix.trace (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)‖ ^ 2 := by
    rw [he, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rcases hi.2 with h | h <;> nlinarith
  have hb := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenCenteredMatrix_norm_sq_displacement B
  nlinarith [_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm_nonneg
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenCenteredMatrix B),
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement_nonneg (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B) _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ]

/-- The exact sharp parabolic bound at j for the original actual pair. -/
theorem ellipticFree_parabolic_displacement_at_j (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hD : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc H) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f g : H)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val, g.val} :
      Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1 ≤ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement f.val _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ * _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement g.val _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
  obtain ⟨A, hAf, ht⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_parabolic_positive_lift f.val hf
  obtain ⟨B, hBg⟩ := _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection_surjective g.val
  have hA : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A ∈ H := hAf.symm ▸ f.property
  have hB : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B ∈ H := hBg.symm ▸ g.property
  have hp : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A, _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
    rwa [hAf, hBg]
  have hbound := ellipticFree_parabolic_bilinear_trace_bound H hD hE A B ht hA hB hp
  have hxt : Matrix.trace ((A : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) - 1) = 0 := by
    rw [Matrix.trace_sub, ht]
    norm_num [Matrix.trace_fin_two]
  have hcenter : Matrix.trace (((A : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) - 1) *
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenCenteredMatrix B) =
      Matrix.trace (((A : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) - 1) * (B : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)) := by
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenCenteredMatrix, mul_sub, Matrix.mul_smul,
      mul_one,
      Matrix.trace_sub, Matrix.trace_smul, hxt, smul_zero, sub_zero]
  have hcs := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_trace_mul_norm_le ((A :
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) -
    1) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenCenteredMatrix B)
  rw [hcenter] at hcs
  have hBN := ellipticFree_centered_norm_le_displacement H hD hE B hB
  have hAN := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_trace_two_difference_eq_sinh A ht
  change _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm ((A :
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) - 1) =
    2 * _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A) _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ at hAN
  have hm := mul_le_mul_of_nonneg_left hBN (_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm_nonneg
    ((A : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2) - 1))
  rw [hAN, hAf] at hcs hm
  rw [hBg] at hm
  nlinarith


/-- Excluding actual elliptic transformations is invariant under subgroup conjugation. -/
theorem _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree.conjugation {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) := by
  intro f hf
  obtain ⟨g, hg, hgf⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff
    q H f.val).mp f.property
  have he : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (q * g * q⁻¹) := hgf.symm ▸ hf
  exact hE ⟨g, hg⟩ ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation g q).mp he)

/--
The sharp parabolic branch at every genuine H3 point,
with no discrete hypothesis and no restriction on the other nonidentity type.
-/
theorem ellipticFree_parabolic_displacement (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hD : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc H) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f g : H)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val, g.val} :
      Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (x : _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    1 ≤ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement f.val x * _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement g.val x := by
  obtain ⟨h, hx⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_upperHalfSpace_transitive x
  let q := h⁻¹
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  let f' : K := ⟨q * f.val * q⁻¹, f.val, f.property, rfl⟩
  let g' : K := ⟨q * g.val * q⁻¹, g.val, g.property, rfl⟩
  have hf' : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f'.val :=
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q, rfl⟩)).mp hf
  have hPair' := hPair.conjugation q
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation] at hPair'
  have hb := ellipticFree_parabolic_displacement_at_j K (invariantDisc_conjugate H q hD)
    (hE.conjugation q) f' g' hf' hPair'
  have hd (F : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement (q * F * q⁻¹) _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement F x := by
    unfold _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement
    rw [← _root_.LowDimensionalTopology.Geometry.Mobius.upperHalfSpacePathDist_smul h]
    simp only [q, mul_smul, inv_inv, smul_inv_smul, hx]
  change 1 ≤ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement (q * f.val *
    q⁻¹) _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ *
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement (q * g.val *
      q⁻¹) _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ at hb
  rwa [hd f.val, hd g.val] at hb

end LowDimensionalTopology.Geometry.Fuchsian
