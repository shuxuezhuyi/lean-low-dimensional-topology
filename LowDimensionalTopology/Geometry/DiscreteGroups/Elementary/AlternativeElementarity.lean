/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Euclidean.Crystallographic.CrystallographicGroups
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteDilationGroups
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
@[expose] public section
noncomputable section
open Set
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Every pair of infinite-order group elements shares a boundary fixed point. -/
def IsInfinitePairElementary (H : Subgroup Mobius.complexMobiusGroup) : Prop :=
  ∀ f∈H,∀ g∈H,¬IsOfFinOrder f→¬IsOfFinOrder g→Mobius.MobiusCommonFixedPoint f g

theorem isInfinitePairElementary_iff_commutatorTrace (H : Subgroup Mobius.complexMobiusGroup) :
    IsInfinitePairElementary H ↔ ∀ f∈H,∀ g∈H,¬IsOfFinOrder f→¬IsOfFinOrder g→
      Mobius.mobiusCommutatorTrace f g=2 := by
  simp only [IsInfinitePairElementary,Mobius.mobius_commonFixedPoint_iff_commutatorTrace_eq_two]

/-- An explicit irrational rotation parameter in the actual complex units. -/
def irrationalRotationUnit : ℂˣ :=
  Units.mk0 (Complex.exp (((2*Real.pi*Real.sqrt 2:ℝ):ℂ)*Complex.I)) (Complex.exp_ne_zero _)

theorem irrationalRotationUnit_norm : ‖(irrationalRotationUnit:ℂ)‖=1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem irrationalRotationUnit_infinite_order : ¬IsOfFinOrder irrationalRotationUnit := by
  intro hf
  let n := orderOf irrationalRotationUnit
  have hn : 0<n := hf.orderOf_pos
  have he := congrArg (fun a : ℂˣ => (a:ℂ)) (pow_orderOf_eq_one irrationalRotationUnit)
  change (Complex.exp (((2*Real.pi*Real.sqrt 2:ℝ):ℂ)*Complex.I))^n=1 at he
  rw [← Complex.exp_nat_mul] at he
  obtain ⟨k,hk⟩ := Complex.exp_eq_one_iff.mp he
  have him := congrArg Complex.im hk
  simp only [Complex.mul_im,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
    Complex.natCast_re,Complex.natCast_im,Complex.intCast_re,Complex.intCast_im,
    zero_mul,mul_zero,zero_add,add_zero,mul_one] at him
  norm_num at him
  have hx : (2*Real.pi)*((n:ℝ)*Real.sqrt 2-(k:ℝ))=0 := by
    linear_combination him
  have hnk : (n:ℝ)*Real.sqrt 2=(k:ℝ) :=
    sub_eq_zero.mp ((mul_eq_zero.mp hx).resolve_left (mul_ne_zero two_ne_zero Real.pi_ne_zero))
  exact (irrational_sqrt_two.natCast_mul hn.ne').ne_int k hnk

def sphereQuarterTurnMatrix : Mobius.FractionalLinearMatrix := Mobius.coefficientMatrix 1 (-1) 1 1 (by norm_num)

def sphereQuarterTurn : Mobius.complexMobiusGroup := Mobius.mobiusMatrixProjection sphereQuarterTurnMatrix

theorem sphereQuarterTurn_zero : sphereQuarterTurn.val (0:ℂ)=(-1:ℂ) := by
  rw [sphereQuarterTurn,Mobius.mobiusMatrixProjection_apply,Mobius.fractionalLinear_coe]
  norm_num [sphereQuarterTurnMatrix,Mobius.coefficientMatrix_val]

theorem sphereQuarterTurn_infty : sphereQuarterTurn.val ∞=(1:ℂ) := by
  rw [sphereQuarterTurn,Mobius.mobiusMatrixProjection_apply,Mobius.fractionalLinear_infty]
  norm_num [sphereQuarterTurnMatrix,Mobius.coefficientMatrix_val]

theorem sphereQuarterTurn_fixJ : sphereQuarterTurn •
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ=Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
  apply (Mobius.mobius_fixJ_iff_norm sphereQuarterTurn).mpr
  rw [sphereQuarterTurn, Mobius.mobiusNormalizedNorm_projection, Mobius.matrixNormalizedNorm,
    div_pow, Auxiliary.Algebra.matrixNorm_sq]
  norm_num [sphereQuarterTurnMatrix,Mobius.coefficientMatrix_val,Matrix.det_fin_two]

theorem mobiusScaling_parameter_injective : Function.Injective Mobius.mobiusScaling := by
  intro a b h
  apply Units.ext
  have he := congrArg (fun f : Mobius.complexMobiusGroup => f.val (1:ℂ)) h
  rw [Mobius.mobiusScaling_coe,Mobius.mobiusScaling_coe] at he
  exact OnePoint.coe_injective (by simpa only [mul_one] using he)

theorem irrationalScaling_infinite_order : ¬IsOfFinOrder (Mobius.mobiusScaling irrationalRotationUnit) := by
  intro hf
  apply irrationalRotationUnit_infinite_order
  apply orderOf_pos_iff.mp
  rw [← orderOf_injective mobiusScalingHom mobiusScaling_parameter_injective irrationalRotationUnit]
  exact hf.orderOf_pos

theorem irrationalScaling_fixJ : Mobius.mobiusScaling irrationalRotationUnit •
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ=Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
  rw [mobiusScaling_eq_affine,affineMobius_smul_j]
  apply Subtype.ext
  change Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0
    ‖(irrationalRotationUnit:ℂ)‖=Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 1
  rw [irrationalRotationUnit_norm]

/-- The whole interior stabilizer is elementary under the finite-orbit convention but fails the infinite-pair convention. -/
theorem interior_stabilizer_not_infinitePairElementary :
    IsElementary (MulAction.stabilizer Mobius.complexMobiusGroup Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) ∧
      ¬IsInfinitePairElementary (MulAction.stabilizer Mobius.complexMobiusGroup
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) := by
  let H := MulAction.stabilizer Mobius.complexMobiusGroup Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
  refine ⟨isElementary_of_interior_fixed H Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ (fun f => f.property),?_⟩
  let f := Mobius.mobiusScaling irrationalRotationUnit
  let q := sphereQuarterTurn
  let g := q*f*q⁻¹
  have hfH : f∈H := irrationalScaling_fixJ
  have hqH : q∈H := sphereQuarterTurn_fixJ
  have hgH : g∈H := H.mul_mem (H.mul_mem hqH hfH) (H.inv_mem hqH)
  have hfInf : ¬IsOfFinOrder f := irrationalScaling_infinite_order
  have hgInf : ¬IsOfFinOrder g := by
    intro hg
    apply hfInf
    rw [← orderOf_pos_iff] at hg ⊢
    have he : orderOf g=orderOf f := (MulAut.conj q).orderOf_eq f
    rwa [he] at hg
  have ha : (irrationalRotationUnit:ℂ)≠1 := by
    intro he
    apply irrationalRotationUnit_infinite_order
    have hu : irrationalRotationUnit=1 := Units.ext he
    rw [hu]
    exact orderOf_pos_iff.mp (by simp)
  have hfix (z : Mobius.ExtendedComplex) : f.val z=z ↔ z=((0:ℂ):Mobius.ExtendedComplex) ∨ z=∞ := by
    change (Mobius.mobiusScaling irrationalRotationUnit).val z=z ↔ _
    rw [mobiusScaling_eq_standard _ ha]
    exact Mobius.mobiusStandardElement_boundary_fixed_iff _ ha z
  intro hAlt
  obtain ⟨z,hfz,hgz⟩ := hAlt f hfH g hgH hfInf hgInf
  have hr := (hfix z).mp hfz
  have hs := (hfix (q.val.symm z)).mp ((Mobius.mobius_conjugate_boundary_fixed_iff f q z).mp hgz)
  have ht : z=((-1:ℂ):Mobius.ExtendedComplex) ∨ z=((1:ℂ):Mobius.ExtendedComplex) := by
    rcases hs with hs | hs
    · have he := congrArg q.val hs
      simp only [Equiv.apply_symm_apply] at he
      exact Or.inl (he.trans sphereQuarterTurn_zero)
    · have he := congrArg q.val hs
      simp only [Equiv.apply_symm_apply] at he
      exact Or.inr (he.trans sphereQuarterTurn_infty)
  rcases hr with rfl | rfl <;> rcases ht with ht | ht <;> norm_num at ht

end LowDimensionalTopology.Geometry.DiscreteGroups
