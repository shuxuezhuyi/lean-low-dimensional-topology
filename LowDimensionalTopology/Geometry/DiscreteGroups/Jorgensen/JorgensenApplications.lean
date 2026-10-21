module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenInequality
public import LowDimensionalTopology.Geometry.DiscreteGroups.LimitSet.NonElementaryLoxodromics
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteElementaryGroups
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
open Filter Topology
open scoped OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups

/-- Matrix trace is continuous on the actual determinant-one matrix group. -/
theorem jorgensen_specialLinear_trace_continuous :
    Continuous (fun A : Auxiliary.Algebra.SpecialLinear2 => Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)) := by
  unfold Matrix.trace
  fun_prop

/-- Squared trace is continuous in the actual uniform Mobius topology. -/
theorem jorgensen_mobiusSquaredTrace_continuous : Continuous Mobius.mobiusSquaredTrace := by
  apply Mobius.mobiusSpecialLinearProjection_isQuotientMap.continuous_iff.mpr
  have ht := jorgensen_specialLinear_trace_continuous.pow 2
  convert ht using 1
  funext A
  exact Mobius.mobiusSquaredTrace_specialLinearProjection A

/-- The sign-independent ordinary commutator trace is continuous in its first actual argument. -/
theorem jorgensen_mobiusCommutatorTrace_continuous_left (g : Mobius.complexMobiusGroup) :
    Continuous (fun f => Mobius.mobiusCommutatorTrace f g) := by
  obtain ⟨B, rfl⟩ := Mobius.mobiusSpecialLinearProjection_surjective g
  apply Mobius.mobiusSpecialLinearProjection_isQuotientMap.continuous_iff.mpr
  have ht : Continuous (fun A : Auxiliary.Algebra.SpecialLinear2 =>
      Matrix.trace (Mobius.Classification.specialCommutator A B : Auxiliary.Algebra.ComplexMatrix2)) := by
    apply jorgensen_specialLinear_trace_continuous.comp
    unfold Mobius.Classification.specialCommutator
    fun_prop
  convert ht using 1
  funext A
  exact Mobius.mobiusCommutatorTrace_representatives _ _ A B rfl rfl

/-- Jorgensen's scalar defect is continuous when its second map is fixed. -/
theorem jorgensenDefect_continuous_left (g : Mobius.complexMobiusGroup) :
    Continuous (fun f => jorgensenDefect f g) :=
  (jorgensen_mobiusSquaredTrace_continuous.sub continuous_const).norm.add
    ((jorgensen_mobiusCommutatorTrace_continuous_left g).sub continuous_const).norm

/-- At the identity the actual trace defect vanishes for every second generator. -/
theorem jorgensenDefect_one (g : Mobius.complexMobiusGroup) : jorgensenDefect 1 g = 0 := by
  obtain ⟨B, rfl⟩ := Mobius.mobiusSpecialLinearProjection_surjective g
  have he := jorgensenDefect_representatives 1 B
  rw [map_one] at he
  rw [he, jorgensenMatrixDefect]
  norm_num [Mobius.Classification.specialCommutator]

/-- A sequence approaching identity eventually forms elementary pairs with each fixed map,
provided those actual two-generator groups are discrete. -/
theorem jorgensen_eventually_elementary {u : ℕ → Mobius.complexMobiusGroup}
    (hu : Tendsto u atTop (𝓝 1)) (g : Mobius.complexMobiusGroup)
    (hD : ∀ n, Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({u n, g} : Set Mobius.complexMobiusGroup))) :
    ∀ᶠ n in atTop, IsElementary (Subgroup.closure ({u n, g} : Set Mobius.complexMobiusGroup)) := by
  have hl : Tendsto (fun n => jorgensenDefect (u n) g) atTop (𝓝 0) := by
    simpa only [Function.comp_def, jorgensenDefect_one] using ((jorgensenDefect_continuous_left g).tendsto 1).comp hu
  filter_upwards [hl.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with n hn
  by_contra he
  exact (not_le_of_gt hn) (one_le_jorgensenDefect_of_discrete_nonElementary (u n) g (hD n) he)

/-- Involutions are excluded eventually along every actual sequence approaching identity. -/
theorem jorgensen_eventually_not_order_two {u : ℕ → Mobius.complexMobiusGroup}
    (hu : Tendsto u atTop (𝓝 1)) : ∀ᶠ n in atTop, orderOf (u n) ≠ 2 := by
  have ht1 : Mobius.mobiusSquaredTrace 1 = 4 := by
    have he := Mobius.mobiusSquaredTrace_specialLinearProjection (1 : Auxiliary.Algebra.SpecialLinear2)
    norm_num [Matrix.trace_fin_two] at he
    exact he
  have ht : Tendsto (fun n => Mobius.mobiusSquaredTrace (u n)) atTop (𝓝 4) := by
    simpa only [Function.comp_def, ht1] using (jorgensen_mobiusSquaredTrace_continuous.tendsto 1).comp hu
  filter_upwards [ht.eventually_ne (by norm_num : (4 : ℂ) ≠ 0)] with n hn
  intro h2
  have hn1 : u n ≠ 1 := by intro he; norm_num [he] at h2
  exact hn ((Mobius.mobius_orderOf_eq_two_iff_squaredTrace_eq_zero (u n) hn1).mp h2)

/-- The Frobenius scalar-product inequality also bounds the trace of a product. -/
theorem jorgensen_trace_mul_norm_le (X Y : Auxiliary.Algebra.ComplexMatrix2) :
    ‖Matrix.trace (X * Y)‖ ≤ Auxiliary.Algebra.matrixNorm X * Auxiliary.Algebra.matrixNorm Y := by
  have h := Auxiliary.Algebra.matrixScalarProduct_norm_le X Y.conjTranspose
  simpa only [Auxiliary.Algebra.matrixScalarProduct, Matrix.conjTranspose_conjTranspose,
    Auxiliary.Algebra.matrixNorm, Matrix.frobenius_norm_conjTranspose] using h

/-- For a trace-two first lift the commutator defect is an exact squared bilinear trace. -/
theorem jorgensen_parabolic_commutator_identity (A B : Auxiliary.Algebra.SpecialLinear2)
    (hA : Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) = 2) :
    Matrix.trace (Mobius.Classification.specialCommutator A B : Auxiliary.Algebra.ComplexMatrix2) - 2 =
      Matrix.trace (((A : Auxiliary.Algebra.ComplexMatrix2) - 1) * ((B : Auxiliary.Algebra.ComplexMatrix2) - 1)) ^
        2 := by
  have hAt : A 1 1 = 2 - A 0 0 := by
    rw [Matrix.trace_fin_two] at hA
    linear_combination hA
  have hAd : A 0 0 * A 1 1 - A 0 1 * A 1 0 - 1 = 0 := by
    simpa only [Matrix.det_fin_two, sub_eq_zero] using A.det_coe
  have hBd : B 0 0 * B 1 1 - B 0 1 * B 1 0 - 1 = 0 := by
    simpa only [Matrix.det_fin_two, sub_eq_zero] using B.det_coe
  simp only [Mobius.Classification.specialCommutator, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    ite_true, show ¬((0 : Fin 2) = 1) from by decide,
    show ¬((1 : Fin 2) = 0) from by decide, ite_false, sub_zero]
  rw [hAt] at hAd ⊢
  linear_combination ((B 0 0 + B 1 1) ^ 2 -
    2 * (B 0 0 * B 1 1 - B 0 1 * B 1 0)) * hAd + 2 * hBd

/-- The Frobenius difference from identity is determined by norm and real trace. -/
theorem jorgensen_matrixNorm_sub_one_sq (A : Auxiliary.Algebra.ComplexMatrix2) :
    Auxiliary.Algebra.matrixNorm (A - 1) ^ 2 = Auxiliary.Algebra.matrixNorm A ^ 2 + 2 - 2 * (Matrix.trace A).re := by
  have hs (z : ℂ) : ‖z - 1‖ ^ 2 = ‖z‖ ^ 2 + 1 - 2 * z.re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im, sub_zero]
    ring
  rw [Auxiliary.Algebra.matrixNorm_sq, Auxiliary.Algebra.matrixNorm_sq, Matrix.trace_fin_two, Complex.add_re]
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero, hs]
  ring

/-- Trace-two lifts obey the sharp norm-product lower bound whenever their pair is admissible. -/
theorem jorgensen_parabolic_norm_bound_trace_two (A B : Auxiliary.Algebra.SpecialLinear2)
    (hA : Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) = 2)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({Mobius.mobiusSpecialLinearProjection A, Mobius.mobiusSpecialLinearProjection B} : Set
        Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure
      ({Mobius.mobiusSpecialLinearProjection A, Mobius.mobiusSpecialLinearProjection B} : Set
        Mobius.complexMobiusGroup))) :
    1 ≤ Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) * Auxiliary.Algebra.matrixNorm
      ((B : Auxiliary.Algebra.ComplexMatrix2) - 1) := by
  have hl := one_le_jorgensenDefect_of_discrete_nonElementary _ _ hD hH
  rw [jorgensenDefect_representatives, jorgensenMatrixDefect, hA] at hl
  norm_num only [sq, mul_self_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
    sub_self, norm_zero, zero_add] at hl
  rw [jorgensen_parabolic_commutator_identity A B hA, norm_pow] at hl
  have hc := jorgensen_trace_mul_norm_le ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) ((B :
    Auxiliary.Algebra.ComplexMatrix2) - 1)
  nlinarith [norm_nonneg (Matrix.trace (((A : Auxiliary.Algebra.ComplexMatrix2) - 1) * ((B :
    Auxiliary.Algebra.ComplexMatrix2) - 1))),
    mul_nonneg (Auxiliary.Algebra.matrixNorm_nonneg ((A : Auxiliary.Algebra.ComplexMatrix2) - 1))
      (Auxiliary.Algebra.matrixNorm_nonneg ((B : Auxiliary.Algebra.ComplexMatrix2) - 1))]

/-- A genuine pair preserver of order different from two fixes the two endpoints individually. -/
theorem jorgensen_pair_preserver_fixes (f : Mobius.complexMobiusGroup) (a b : Mobius.ExtendedComplex)
    (hab : a ≠ b) (hf2 : orderOf f ≠ 2)
    (hp : f.val '' ({a, b} : Set Mobius.ExtendedComplex) = {a, b}) : f.val a = a ∧ f.val b = b := by
  have hfa : f.val a = a ∨ f.val a = b := by
    have hmem : f.val a ∈ f.val '' ({a, b} : Set Mobius.ExtendedComplex) := ⟨a, by simp, rfl⟩
    rw [hp] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hfb : f.val b = a ∨ f.val b = b := by
    have hmem : f.val b ∈ f.val '' ({a, b} : Set Mobius.ExtendedComplex) := ⟨b, by simp, rfl⟩
    rw [hp] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  rcases hfa with ha | ha
  · refine ⟨ha, ?_⟩
    rcases hfb with hb | hb
    · exact False.elim (hab (f.val.injective (ha.trans hb.symm)))
    · exact hb
  · rcases hfb with hb | hb
    · have hf : f ≠ 1 := by intro he; apply hab; simpa only [he, Subgroup.coe_one, Equiv.Perm.one_apply] using ha
      exact False.elim (hf2 (orderOf_eq_prime (Mobius.mobius_sq_eq_one_of_swaps f a b hab ha hb) hf))
    · exact False.elim (hab (f.val.injective (ha.trans hb.symm)))

/-- discreteness of a non-elementary actual group is detected on all pairs. -/
theorem discrete_iff_all_two_generated_subgroups_discrete (H : Subgroup Mobius.complexMobiusGroup) (hH :
    IsNonElementary H) :
    Mobius.IsDiscreteMobiusSubgroup H ↔ ∀ f g : H,
      Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f.val, g.val} : Set Mobius.complexMobiusGroup)) := by
  constructor
  · intro hD f g
    let _ : DiscreteTopology H := hD
    apply DiscreteGroups.MatrixGroups.subgroup_discrete (L := H)
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with rfl | hx
    · exact f.property
    · exact Set.mem_singleton_iff.mp hx ▸ g.property
  · intro hPair
    obtain ⟨v, _, hL, hDis⟩ := exists_injective_loxodromic_sequence_pairwise_disjoint_fixedPoints H hH
    apply (DiscreteGroups.MatrixGroups.discrete_iff_identity_sequences H).mpr
    intro u hu
    have hE0 := jorgensen_eventually_elementary hu (v 0).val (fun n => hPair (u n) (v 0))
    have hE1 := jorgensen_eventually_elementary hu (v 1).val (fun n => hPair (u n) (v 1))
    have hO := jorgensen_eventually_not_order_two hu
    filter_upwards [hE0, hE1, hO] with n hn0 hn1 hn2
    obtain ⟨a, b, hab, hga, hgb, hpres⟩ := discrete_elementary_loxodromic_fixed_pair _
      (hPair (u n) (v 0)) hn0 (v 0).val
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) (hL 0)
    have hnu0 : (u n).val ∈ Subgroup.closure ({(u n).val, (v 0).val} : Set Mobius.complexMobiusGroup) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    obtain ⟨ha, hb⟩ := jorgensen_pair_preserver_fixes (u n).val a b hab hn2 (hpres ⟨_, hnu0⟩)
    obtain ⟨c, d, hcd, hgc, hgd, hpres'⟩ := discrete_elementary_loxodromic_fixed_pair _
      (hPair (u n) (v 1)) hn1 (v 1).val
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) (hL 1)
    have hnu1 : (u n).val ∈ Subgroup.closure ({(u n).val, (v 1).val} : Set Mobius.complexMobiusGroup) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    obtain ⟨hc, _⟩ := jorgensen_pair_preserver_fixes (u n).val c d hcd hn2 (hpres' ⟨_, hnu1⟩)
    have hac : a ≠ c := by
      intro he
      apply Set.disjoint_left.mp (hDis (by decide : (0 : ℕ) ≠ 1))
        ((Mobius.mobiusExtendedFixedPoints_boundary_iff _ a).mpr hga)
      rw [he]
      exact (Mobius.mobiusExtendedFixedPoints_boundary_iff _ c).mpr hgc
    have hbc : b ≠ c := by
      intro he
      apply Set.disjoint_left.mp (hDis (by decide : (0 : ℕ) ≠ 1))
        ((Mobius.mobiusExtendedFixedPoints_boundary_iff _ b).mpr hgb)
      rw [he]
      exact (Mobius.mobiusExtendedFixedPoints_boundary_iff _ c).mpr hgc
    apply Subtype.ext
    exact Mobius.mobius_eq_one_of_three_fixed (u n).val a b c hab hac hbc ha hb hc

/-- Every genuine parabolic determinant-one representative has trace two or minus two. -/
theorem jorgensen_parabolic_lift_trace (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : Mobius.MobiusParabolic (Mobius.mobiusSpecialLinearProjection A)) :
    Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) = 2 ∨ Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)
      = -2 := by
  have hs := (Mobius.mobius_parabolic_iff_squaredTrace_eq_four _ hA.1).mp hA
  rw [Mobius.mobiusSquaredTrace_specialLinearProjection] at hs
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  convert hs using 1; norm_num

/-- Changing the negative-trace lift to positive trace can only decrease its difference norm. -/
theorem jorgensen_signChange_norm_le (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) = -2) :
    Auxiliary.Algebra.matrixNorm ((Mobius.specialLinearSignChange A : Auxiliary.Algebra.ComplexMatrix2) - 1) ≤
      Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) := by
  have hneg : Auxiliary.Algebra.matrixNorm (-(A : Auxiliary.Algebra.ComplexMatrix2)) =
    Auxiliary.Algebra.matrixNorm (A : Auxiliary.Algebra.ComplexMatrix2) := by
    simpa only [neg_one_smul, norm_neg, norm_one, one_mul] using Auxiliary.Algebra.matrixNorm_scalar (-1 : ℂ) (A :
      Auxiliary.Algebra.ComplexMatrix2)
  have hs := jorgensen_matrixNorm_sub_one_sq (-(A : Auxiliary.Algebra.ComplexMatrix2))
  have ht := jorgensen_matrixNorm_sub_one_sq (A : Auxiliary.Algebra.ComplexMatrix2)
  rw [Matrix.trace_neg, hA, hneg] at hs
  rw [hA] at ht
  norm_num at hs ht
  change Auxiliary.Algebra.matrixNorm (-(A : Auxiliary.Algebra.ComplexMatrix2) - 1) ≤ _
  nlinarith [Auxiliary.Algebra.matrixNorm_nonneg (-(A : Auxiliary.Algebra.ComplexMatrix2) - 1),
    Auxiliary.Algebra.matrixNorm_nonneg ((A : Auxiliary.Algebra.ComplexMatrix2) - 1)]

/-- For either genuine determinant-one choice of both lifts. -/
theorem one_le_parabolic_matrixNorm_defect_product (A B : Auxiliary.Algebra.SpecialLinear2)
    (hA : Mobius.MobiusParabolic (Mobius.mobiusSpecialLinearProjection A))
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({Mobius.mobiusSpecialLinearProjection A, Mobius.mobiusSpecialLinearProjection B} : Set
        Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure
      ({Mobius.mobiusSpecialLinearProjection A, Mobius.mobiusSpecialLinearProjection B} : Set
        Mobius.complexMobiusGroup))) :
    1 ≤ Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) * Auxiliary.Algebra.matrixNorm
      ((B : Auxiliary.Algebra.ComplexMatrix2) - 1) := by
  rcases jorgensen_parabolic_lift_trace A hA with ht | ht
  · exact jorgensen_parabolic_norm_bound_trace_two A B ht hD hH
  · have hp : Mobius.mobiusSpecialLinearProjection (Mobius.specialLinearSignChange A) =
      Mobius.mobiusSpecialLinearProjection A :=
      ((Mobius.specialLinear_sameMobius_iff A (Mobius.specialLinearSignChange A)).mpr (Or.inr rfl)).symm
    have hs : Matrix.trace (Mobius.specialLinearSignChange A : Auxiliary.Algebra.ComplexMatrix2) = 2 := by
      change Matrix.trace (-(A : Auxiliary.Algebra.ComplexMatrix2)) = 2
      rw [Matrix.trace_neg, ht]
      ring
    have hD' : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
        ({Mobius.mobiusSpecialLinearProjection (Mobius.specialLinearSignChange A),
          Mobius.mobiusSpecialLinearProjection B} : Set Mobius.complexMobiusGroup)) := by rwa [hp]
    have hH' : IsNonElementary (Subgroup.closure
        ({Mobius.mobiusSpecialLinearProjection (Mobius.specialLinearSignChange A),
          Mobius.mobiusSpecialLinearProjection B} : Set Mobius.complexMobiusGroup)) := by rwa [hp]
    exact (jorgensen_parabolic_norm_bound_trace_two _ B hs hD' hH').trans
      (mul_le_mul_of_nonneg_right (jorgensen_signChange_norm_le A ht) (Auxiliary.Algebra.matrixNorm_nonneg _))

/-- Every actual parabolic map admits a determinant-one lift with positive trace two. -/
theorem jorgensen_parabolic_positive_lift (f : Mobius.complexMobiusGroup) (hf : Mobius.MobiusParabolic f) :
    ∃ A : Auxiliary.Algebra.SpecialLinear2, Mobius.mobiusSpecialLinearProjection A = f ∧ Matrix.trace (A :
      Auxiliary.Algebra.ComplexMatrix2) = 2 := by
  obtain ⟨A, hA⟩ := Mobius.mobiusSpecialLinearProjection_surjective f
  have hfA : Mobius.MobiusParabolic (Mobius.mobiusSpecialLinearProjection A) := by rwa [hA]
  rcases jorgensen_parabolic_lift_trace A hfA with ht | ht
  · exact ⟨A, hA, ht⟩
  · refine ⟨Mobius.specialLinearSignChange A, ?_, ?_⟩
    · exact ((Mobius.specialLinear_sameMobius_iff A (Mobius.specialLinearSignChange A)).mpr (Or.inr rfl)).symm.trans hA
    · change Matrix.trace (-(A : Auxiliary.Algebra.ComplexMatrix2)) = 2
      rw [Matrix.trace_neg, ht]
      ring

/-- The original H3 path distance is nonnegative, directly from its length infimum. -/
theorem jorgensen_upperHalfSpacePathDist_nonneg (x y : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    0 ≤ Mobius.upperHalfSpacePathDist x y := ENNReal.toReal_nonneg

/-- A positive-trace parabolic lift measures displacement at j through its true difference norm. -/
theorem jorgensen_trace_two_difference_eq_sinh (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) = 2) :
    Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) = 2 * Real.sinh
      (Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
        (Mobius.mobiusSpecialLinearProjection A • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) / 2) := by
  let d := Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
    (Mobius.mobiusSpecialLinearProjection A • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)
  have hd : 0 ≤ d := jorgensen_upperHalfSpacePathDist_nonneg _ _
  have hs := jorgensen_matrixNorm_sub_one_sq (A : Auxiliary.Algebra.ComplexMatrix2)
  rw [hA, ← Mobius.mobiusNormalizedNorm_specialLinearProjection A,
    Mobius.mobiusNormalizedNorm_sq_eq_two_cosh_origin_displacement] at hs
  norm_num at hs
  change Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) ^ 2 = 2 * Real.cosh d + 2 - 4 at hs
  have hcosh := Real.cosh_two_mul (d / 2)
  rw [show 2 * (d / 2) = d by ring] at hcosh
  have hrel := Real.cosh_sq_sub_sinh_sq (d / 2)
  have hsn : 0 ≤ Real.sinh (d / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
  apply (sq_eq_sq₀ (Auxiliary.Algebra.matrixNorm_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hsn)).mp
  change Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) ^ 2 = (2 * Real.sinh (d / 2)) ^ 2
  nlinarith

/-- The sharp simultaneous parabolic displacement lower bound at the original base point j. -/
theorem jorgensen_parabolic_displacement_at_j (f g : Mobius.complexMobiusGroup)
    (hf : Mobius.MobiusParabolic f) (hg : Mobius.MobiusParabolic g)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup))) :
    (1 / 4 : ℝ) ≤ Real.sinh (Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ (f •
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) / 2) *
      Real.sinh (Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ (g •
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) / 2) := by
  obtain ⟨A, hA, htA⟩ := jorgensen_parabolic_positive_lift f hf
  obtain ⟨B, hB, htB⟩ := jorgensen_parabolic_positive_lift g hg
  have hD' : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({Mobius.mobiusSpecialLinearProjection A, Mobius.mobiusSpecialLinearProjection B} : Set
        Mobius.complexMobiusGroup)) := by rwa [hA, hB]
  have hH' : IsNonElementary (Subgroup.closure
      ({Mobius.mobiusSpecialLinearProjection A, Mobius.mobiusSpecialLinearProjection B} : Set
        Mobius.complexMobiusGroup)) := by rwa [hA, hB]
  have hb := jorgensen_parabolic_norm_bound_trace_two A B htA hD' hH'
  rw [jorgensen_trace_two_difference_eq_sinh A htA,
    jorgensen_trace_two_difference_eq_sinh B htB, hA, hB] at hb
  nlinarith

/-- Actual affine Mobius maps act transitively on the genuine H3 upper half-space. -/
theorem jorgensen_upperHalfSpace_transitive (x : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    ∃ h : Mobius.complexMobiusGroup, h • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = x := by
  let t := Hyperbolic.QuaternionHalfSpace.quaternionHeight x.val
  have ht : 0 < t := x.property
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  refine ⟨Mobius.affineMobius (t : ℂ) (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal x.val) ht0, ?_⟩
  apply Subtype.ext
  rw [Mobius.affineMobius_smul, Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ_horizontal,
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ_height]
  simp only [mul_zero, zero_add, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht, mul_one]
  exact Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates x.val

/-- at every point of the actual reciprocal-height H3 path metric. -/
theorem quarter_le_parabolic_sinh_displacement_product (f g : Mobius.complexMobiusGroup)
    (hf : Mobius.MobiusParabolic f) (hg : Mobius.MobiusParabolic g)
    (hD : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)))
    (hH : IsNonElementary (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup))) (x :
      Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (1 / 4 : ℝ) ≤ Real.sinh (Mobius.upperHalfSpacePathDist x (f • x) / 2) *
      Real.sinh (Mobius.upperHalfSpacePathDist x (g • x) / 2) := by
  obtain ⟨h, hx⟩ := jorgensen_upperHalfSpace_transitive x
  let q := h⁻¹
  let H := Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)
  let _ : DiscreteTopology H := hD
  have hmap := jorgensen_generated_conjugation f g q
  have hD' : Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({q * f * q⁻¹, q * g * q⁻¹} : Set Mobius.complexMobiusGroup)) := by
    rw [← hmap]
    exact DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q H
  have hH' := hH.conjugation q
  rw [hmap] at hH'
  have hf' : Mobius.MobiusParabolic (q * f * q⁻¹) :=
    (Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q, rfl⟩)).mp hf
  have hg' : Mobius.MobiusParabolic (q * g * q⁻¹) :=
    (Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q, rfl⟩)).mp hg
  have hb := jorgensen_parabolic_displacement_at_j _ _ hf' hg' hD' hH'
  have hd (F : Mobius.complexMobiusGroup) :
      Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ((q * F * q⁻¹) •
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) =
      Mobius.upperHalfSpacePathDist x (F • x) := by
    rw [← Mobius.upperHalfSpacePathDist_smul h]
    simp only [q, mul_smul, inv_inv, smul_inv_smul, hx]
  rwa [hd f, hd g] at hb

/-- The second parabolic lift in the simultaneous sharpness example. -/
def jorgensenParabolicPartnerLift : Auxiliary.Algebra.SpecialLinear2 := ⟨!![1, 0; 1, 1], by simp⟩

/-- The actual second parabolic transformation, acting by z divided by z plus one. -/
def jorgensenParabolicPartner : Mobius.complexMobiusGroup := Mobius.mobiusSpecialLinearProjection
    jorgensenParabolicPartnerLift

/-- The second parabolic lift is an actual word in the original modular sharpness generators. -/
theorem jorgensenParabolicPartner_word : jorgensenParabolicPartner =
    jorgensenSharpnessTranslation * jorgensenSharpnessInversion * jorgensenSharpnessTranslation := by
  rw [← jorgensenSharpnessTranslation_lift, jorgensenSharpnessInversion, ← map_mul, ← map_mul]
  apply congrArg Mobius.mobiusSpecialLinearProjection
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  change jorgensenParabolicPartnerLift i j =
    (((Mobius.invariantDiscTranslationLift : Auxiliary.Algebra.ComplexMatrix2) *
      (jorgensenSharpnessInversionLift : Auxiliary.Algebra.ComplexMatrix2)) * (Mobius.invariantDiscTranslationLift
        : Auxiliary.Algebra.ComplexMatrix2)) i j
  fin_cases i <;> fin_cases j <;>
    norm_num [jorgensenParabolicPartnerLift, Mobius.invariantDiscTranslationLift,
      jorgensenSharpnessInversionLift, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two parabolic generators generate exactly the already verified actual modular group. -/
theorem jorgensenParabolicPair_group :
    Subgroup.closure ({jorgensenSharpnessTranslation, jorgensenParabolicPartner} : Set Mobius.complexMobiusGroup) =
      jorgensenSharpnessGroup := by
  let K := Subgroup.closure ({jorgensenSharpnessTranslation, jorgensenParabolicPartner} : Set Mobius.complexMobiusGroup)
  have hT : jorgensenSharpnessTranslation ∈ jorgensenSharpnessGroup := Subgroup.subset_closure (Set.mem_insert _ _)
  have hS : jorgensenSharpnessInversion ∈ jorgensenSharpnessGroup :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro f hf
    rcases Set.mem_insert_iff.mp hf with rfl | hf
    · exact hT
    · rw [Set.mem_singleton_iff] at hf
      rw [hf, jorgensenParabolicPartner_word]
      exact jorgensenSharpnessGroup.mul_mem (jorgensenSharpnessGroup.mul_mem hT hS) hT
  · have hTK : jorgensenSharpnessTranslation ∈ K := Subgroup.subset_closure (Set.mem_insert _ _)
    have hUK : jorgensenParabolicPartner ∈ K :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    have hSK : jorgensenSharpnessInversion ∈ K := by
      have he : jorgensenSharpnessInversion =
          jorgensenSharpnessTranslation⁻¹ * jorgensenParabolicPartner * jorgensenSharpnessTranslation⁻¹ := by
        rw [jorgensenParabolicPartner_word]
        group
      rw [he]
      exact K.mul_mem (K.mul_mem (K.inv_mem hTK) hUK) (K.inv_mem hTK)
    apply (Subgroup.closure_le _).mpr
    intro f hf
    rcases Set.mem_insert_iff.mp hf with rfl | hf
    · exact hTK
    · exact Set.mem_singleton_iff.mp hf ▸ hSK

/-- Both parabolic sharpness lifts have trace two and unit difference norm. -/
theorem jorgensenParabolicPair_lift_data :
    Matrix.trace (Mobius.invariantDiscTranslationLift : Auxiliary.Algebra.ComplexMatrix2) = 2 ∧
    Matrix.trace (jorgensenParabolicPartnerLift : Auxiliary.Algebra.ComplexMatrix2) = 2 ∧
    Auxiliary.Algebra.matrixNorm ((Mobius.invariantDiscTranslationLift : Auxiliary.Algebra.ComplexMatrix2) - 1) = 1 ∧
    Auxiliary.Algebra.matrixNorm ((jorgensenParabolicPartnerLift : Auxiliary.Algebra.ComplexMatrix2) - 1) = 1 := by
  norm_num [Mobius.invariantDiscTranslationLift, jorgensenParabolicPartnerLift,
    Matrix.trace_fin_two, Auxiliary.Algebra.matrixNorm_formula]

/-- The second actual equality generator is genuinely parabolic. -/
theorem jorgensenParabolicPartner_parabolic : Mobius.MobiusParabolic jorgensenParabolicPartner := by
  have hi : jorgensenParabolicPartner.val ∞ = ((1 : ℂ) : Mobius.ExtendedComplex) := by
    rw [jorgensenParabolicPartner, Mobius.invariantDisc_specialLinear_action, Mobius.fractionalLinear_infty]
    norm_num [jorgensenParabolicPartnerLift, Matrix.SpecialLinearGroup.toGL]
  have hn : jorgensenParabolicPartner ≠ 1 := by
    intro he
    rw [he] at hi
    exact (OnePoint.coe_ne_infty (1 : ℂ)) hi.symm
  apply (Mobius.mobius_parabolic_iff_squaredTrace_eq_four _ hn).mpr
  rw [jorgensenParabolicPartner, Mobius.mobiusSquaredTrace_specialLinearProjection,
    jorgensenParabolicPair_lift_data.2.1]
  norm_num

/-- attains its sharp lower bound on the actual two-parabolic modular pair. -/
theorem exists_parabolic_matrixNorm_defect_product_eq_one : ∃ A B : Auxiliary.Algebra.SpecialLinear2,
    Mobius.MobiusParabolic (Mobius.mobiusSpecialLinearProjection A) ∧ Mobius.MobiusParabolic
      (Mobius.mobiusSpecialLinearProjection B) ∧
    Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({Mobius.mobiusSpecialLinearProjection A, Mobius.mobiusSpecialLinearProjection B} : Set
        Mobius.complexMobiusGroup)) ∧
    IsNonElementary (Subgroup.closure
      ({Mobius.mobiusSpecialLinearProjection A, Mobius.mobiusSpecialLinearProjection B} : Set
        Mobius.complexMobiusGroup)) ∧
    Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) * Auxiliary.Algebra.matrixNorm ((B :
      Auxiliary.Algebra.ComplexMatrix2) - 1) = 1 := by
  refine ⟨Mobius.invariantDiscTranslationLift, jorgensenParabolicPartnerLift, ?_,
    jorgensenParabolicPartner_parabolic, ?_, ?_, ?_⟩
  · rw [jorgensenSharpnessTranslation_lift]
    exact (mobiusTranslation_parabolic_iff 1).mpr one_ne_zero
  · rw [jorgensenSharpnessTranslation_lift, ← jorgensenParabolicPartner, jorgensenParabolicPair_group]
    exact jorgensenSharpnessGroup_discrete
  · rw [jorgensenSharpnessTranslation_lift, ← jorgensenParabolicPartner, jorgensenParabolicPair_group]
    exact jorgensenSharpnessGroup_nonElementary
  · rw [jorgensenParabolicPair_lift_data.2.2.1, jorgensenParabolicPair_lift_data.2.2.2, mul_one]

/-- A discrete non-elementary parabolic pair attains the quarter displacement bound. -/
theorem exists_parabolic_sinh_displacement_product_eq_quarter : ∃ f g : Mobius.complexMobiusGroup, ∃ x :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace,
    Mobius.MobiusParabolic f ∧ Mobius.MobiusParabolic g ∧
    Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)) ∧
    IsNonElementary (Subgroup.closure ({f, g} : Set Mobius.complexMobiusGroup)) ∧
    Real.sinh (Mobius.upperHalfSpacePathDist x (f • x) / 2) *
      Real.sinh (Mobius.upperHalfSpacePathDist x (g • x) / 2) = (1 / 4 : ℝ) := by
  refine ⟨jorgensenSharpnessTranslation, jorgensenParabolicPartner, Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ,
    (mobiusTranslation_parabolic_iff 1).mpr one_ne_zero, jorgensenParabolicPartner_parabolic,
    ?_, ?_, ?_⟩
  · rw [jorgensenParabolicPair_group]
    exact jorgensenSharpnessGroup_discrete
  · rw [jorgensenParabolicPair_group]
    exact jorgensenSharpnessGroup_nonElementary
  · have hA := jorgensen_trace_two_difference_eq_sinh Mobius.invariantDiscTranslationLift
      jorgensenParabolicPair_lift_data.1
    have hB := jorgensen_trace_two_difference_eq_sinh jorgensenParabolicPartnerLift jorgensenParabolicPair_lift_data.2.1
    rw [jorgensenSharpnessTranslation_lift, jorgensenParabolicPair_lift_data.2.2.1] at hA
    rw [jorgensenParabolicPair_lift_data.2.2.2] at hB
    change Real.sinh (Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
      (jorgensenSharpnessTranslation • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) / 2) *
      Real.sinh (Mobius.upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
        (Mobius.mobiusSpecialLinearProjection jorgensenParabolicPartnerLift •
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) / 2) = (1 / 4 : ℝ)
    nlinarith

end LowDimensionalTopology.Geometry.DiscreteGroups
