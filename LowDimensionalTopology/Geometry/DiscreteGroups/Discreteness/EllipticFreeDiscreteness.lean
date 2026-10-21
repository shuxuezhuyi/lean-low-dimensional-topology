/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Jorgensen.JorgensenAxes
public import LowDimensionalTopology.Geometry.Mobius.InvariantDisc.InvariantDiscConverse
public import LowDimensionalTopology.Geometry.Fuchsian.Basic.FuchsianStabilizers
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology OnePoint
namespace LowDimensionalTopology.Geometry.DiscreteGroups
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups

/-- Every group element is nonelliptic. -/
def IsEllipticFree (H : Subgroup Mobius.complexMobiusGroup) : Prop :=
  ∀ f : H, ¬Mobius.MobiusElliptic f.val

/-- Every nonidentity element is genuinely hyperbolic. -/
def IsPurelyHyperbolic (H : Subgroup Mobius.complexMobiusGroup) : Prop :=
  ∀ f : H, f.val ≠ 1 → Mobius.MobiusHyperbolic f.val

theorem IsPurelyHyperbolic.ellipticFree {H : Subgroup Mobius.complexMobiusGroup} (h : IsPurelyHyperbolic H) :
    IsEllipticFree H := by
  intro f hf
  exact (h f hf.1).1.not_elliptic hf

theorem IsPurelyHyperbolic.no_strictly_loxodromic {H : Subgroup Mobius.complexMobiusGroup}
    (h : IsPurelyHyperbolic H) : ∀ f : H, ¬Mobius.MobiusStrictlyLoxodromic f.val := by
  intro f hf
  exact hf.2 (h f hf.1.1)

/-- A purely hyperbolic group preserves a complex disc. -/
theorem IsPurelyHyperbolic.hasInvariantComplexDisc {H : Subgroup Mobius.complexMobiusGroup}
    (h : IsPurelyHyperbolic H) (hH : IsNonElementary H) : Mobius.HasInvariantComplexDisc H :=
  (Mobius.invariant_disc_iff_no_strictlyLoxodromic H hH).mpr h.no_strictly_loxodromic

/-- Without elliptics, every actual invariant-disc element has real squared trace at least four. -/
theorem ellipticFree_squaredTrace_ge_four (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.HasInvariantComplexDisc H) (hE : IsEllipticFree H) (f : H) :
    ∃ r : ℝ, 4 ≤ r ∧ Mobius.mobiusSquaredTrace f.val = (r : ℂ) := by
  obtain ⟨D, hD, hpres⟩ := hD
  obtain ⟨r, hr, ht⟩ := Mobius.mobius_generalized_disc_preserver_squaredTrace f.val hD (hpres f)
  refine ⟨r, ?_, ht⟩
  by_cases hf : f.val = 1
  · have hone : Mobius.mobiusSquaredTrace (1 : Mobius.complexMobiusGroup) = 4 := by
      have h := Mobius.mobiusSquaredTrace_specialLinearProjection (1 : Auxiliary.Algebra.SpecialLinear2)
      norm_num [Matrix.trace_fin_two] at h
      exact h
    rw [hf, hone] at ht
    have he : r = 4 := by exact_mod_cast ht.symm
    exact he.ge
  · by_contra hn
    exact hE f ((Mobius.mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four f.val hf).mpr ⟨r, hr,
      lt_of_not_ge hn, ht⟩)

/-- A complex square on the real ray above four has real root outside the elliptic trace interval. -/
theorem ellipticFree_trace_of_square (c : ℂ) (r : ℝ) (hr : 4 ≤ r) (hc : c ^ 2 = (r : ℂ)) :
    c.im = 0 ∧ (c.re ≤ -2 ∨ 2 ≤ c.re) := by
  have hRe := congrArg Complex.re hc
  have hIm := congrArg Complex.im hc
  simp only [pow_two, Complex.mul_re, Complex.ofReal_re] at hRe
  simp only [pow_two, Complex.mul_im, Complex.ofReal_im] at hIm
  have hn : c.re ≠ 0 := by intro he; rw [he] at hRe; nlinarith [sq_nonneg c.im]
  have him : c.im = 0 := by
    have hm : c.re * c.im = 0 := by nlinarith
    exact (mul_eq_zero.mp hm).resolve_left hn
  refine ⟨him, ?_⟩
  rw [him] at hRe
  by_cases hneg : c.re ≤ -2
  · exact Or.inl hneg
  · exact Or.inr (by nlinarith)

/-- The actual-group projection respects the source commutator order. -/
theorem ellipticFree_commutator_projection (A B : Auxiliary.Algebra.SpecialLinear2) :
    Mobius.mobiusSpecialLinearProjection (Mobius.Classification.specialCommutator A B) =
      Mobius.mobiusCommutator (Mobius.mobiusSpecialLinearProjection A) (Mobius.mobiusSpecialLinearProjection B) := by
  simp only [Mobius.Classification.specialCommutator, Mobius.mobiusCommutator, map_mul, map_inv]

/-- Genuine special-linear traces of actual elliptic-free disc-preserving elements are real and outside (-2,2). -/
theorem ellipticFree_specialLinear_trace (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.HasInvariantComplexDisc H) (hE : IsEllipticFree H)
    (A : Auxiliary.Algebra.SpecialLinear2) (hA : Mobius.mobiusSpecialLinearProjection A ∈ H) :
    (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).im = 0 ∧
      ((Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2)).re ≤ -2 ∨ 2 ≤ (Matrix.trace (A :
        Auxiliary.Algebra.ComplexMatrix2)).re) := by
  obtain ⟨r, hr, ht⟩ := ellipticFree_squaredTrace_ge_four H hD hE ⟨_, hA⟩
  rw [Mobius.mobiusSquaredTrace_specialLinearProjection] at ht
  exact ellipticFree_trace_of_square _ r hr ht

/-- The off-diagonal product of a commutator with a genuine diagonal matrix. -/
theorem ellipticFree_diagonal_commutator_product (A B : Auxiliary.Algebra.SpecialLinear2)
    (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) :
    Mobius.Classification.specialCommutator A B 0 1 * Mobius.Classification.specialCommutator A B 1 0 =
      -(A 0 0 - A 1 1) ^ 2 * (B 0 1 * B 1 0) * (1 + B 0 1 * B 1 0) := by
  have hA : A 0 0 * A 1 1 = 1 := by
    simpa only [Matrix.det_fin_two, h01, h10, zero_mul, sub_zero] using A.det_coe
  have hB : B 0 0 * B 1 1 = 1 + B 0 1 * B 1 0 := by
    have h := B.det_coe
    rw [Matrix.det_fin_two] at h
    linear_combination h
  have hc01 : Mobius.Classification.specialCommutator A B 0 1 =
      A 0 0 * (A 0 0 - A 1 1) * B 0 0 * B 0 1 := by
    simp only [Mobius.Classification.specialCommutator, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, h01, h10, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  have hc10 : Mobius.Classification.specialCommutator A B 1 0 =
      -(A 1 1) * (A 0 0 - A 1 1) * B 1 0 * B 1 1 := by
    simp only [Mobius.Classification.specialCommutator, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, h01, h10, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    ring
  rw [hc01, hc10]
  calc
    _ = -(A 0 0 * A 1 1) * (A 0 0 - A 1 1) ^ 2 * (B 0 1 * B 1 0) *
      (B 0 0 * B 1 1) := by ring
    _ = _ := by rw [hA, hB]; ring

/-- The exact second-commutator trace recurrence behind the algebraic proof of discreteness. -/
theorem ellipticFree_diagonal_double_commutator_trace (A B : Auxiliary.Algebra.SpecialLinear2)
    (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) :
    Matrix.trace (Mobius.Classification.specialCommutator A (Mobius.Classification.specialCommutator A B) :
      Auxiliary.Algebra.ComplexMatrix2) - 2 =
      (Matrix.trace (Mobius.Classification.specialCommutator A B : Auxiliary.Algebra.ComplexMatrix2) - 2) *
        (Matrix.trace (Mobius.Classification.specialCommutator A B : Auxiliary.Algebra.ComplexMatrix2) - 2 -
          (Matrix.trace (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 - 4)) := by
  rw [Mobius.Classification.specialCommutator_trace_triangular A B h10,
    Mobius.Classification.specialCommutator_trace_triangular A (Mobius.Classification.specialCommutator A B) h10,
    jorgensen_diagonal_trace_defect A h01]
  simp only [h01, zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, add_zero]
  have hp := ellipticFree_diagonal_commutator_product A B h01 h10
  linear_combination -(A 0 0 - A 1 1) ^ 2 * hp

theorem ellipticFree_mobiusCommutator_conjugation (f g q : Mobius.complexMobiusGroup) :
    Mobius.mobiusCommutator (q * f * q⁻¹) (q * g * q⁻¹) = q * Mobius.mobiusCommutator f g * q⁻¹ := by
  unfold Mobius.mobiusCommutator
  group

theorem ellipticFree_commutatorTrace_conjugation (f g q : Mobius.complexMobiusGroup) :
    Mobius.mobiusCommutatorTrace (q * f * q⁻¹) (q * g * q⁻¹) = Mobius.mobiusCommutatorTrace f g := by
  simp only [Mobius.mobiusCommutatorTrace, map_mul, map_inv, Mobius.Classification.commutatorTrace_conjugation]

theorem ellipticFree_diagonal_double_commutator_trace_actual (A B : Auxiliary.Algebra.SpecialLinear2)
    (h01 : A 0 1 = 0) (h10 : A 1 0 = 0) :
    Mobius.mobiusCommutatorTrace (Mobius.mobiusSpecialLinearProjection A)
        (Mobius.mobiusCommutator (Mobius.mobiusSpecialLinearProjection A) (Mobius.mobiusSpecialLinearProjection
          B)) - 2 =
      (Mobius.mobiusCommutatorTrace (Mobius.mobiusSpecialLinearProjection A) (Mobius.mobiusSpecialLinearProjection
        B) - 2) *
        (Mobius.mobiusCommutatorTrace (Mobius.mobiusSpecialLinearProjection A)
          (Mobius.mobiusSpecialLinearProjection B) - 2 -
          (Mobius.mobiusSquaredTrace (Mobius.mobiusSpecialLinearProjection A) - 4)) := by
  rw [← ellipticFree_commutator_projection A B,
    Mobius.mobiusCommutatorTrace_representatives _ _ A (Mobius.Classification.specialCommutator A B) rfl rfl,
    Mobius.mobiusCommutatorTrace_representatives _ _ A B rfl rfl,
    Mobius.mobiusSquaredTrace_specialLinearProjection]
  exact ellipticFree_diagonal_double_commutator_trace A B h01 h10

/-- The exact second-commutator recurrence is invariant under actual geometric conjugation. -/
theorem ellipticFree_hyperbolic_double_commutator_trace (f g : Mobius.complexMobiusGroup)
    (hf : Mobius.MobiusHyperbolic f) :
    Mobius.mobiusCommutatorTrace f (Mobius.mobiusCommutator f g) - 2 =
      (Mobius.mobiusCommutatorTrace f g - 2) *
        (Mobius.mobiusCommutatorTrace f g - 2 - (Mobius.mobiusSquaredTrace f - 4)) := by
  obtain ⟨u, hu, hu1, q, rfl⟩ := mobius_nonparabolic_eigenvalue_normal_form f hf.1.1 hf.1.not_parabolic
  let G := q⁻¹ * g * q
  have he : g = q * G * q⁻¹ := by dsimp [G]; group
  rw [he, ellipticFree_mobiusCommutator_conjugation,
    ellipticFree_commutatorTrace_conjugation, ellipticFree_commutatorTrace_conjugation,
    Mobius.mobiusSquaredTrace_conjugation]
  rw [← eigenvalueSpecialLinearLift_projection u hu]
  obtain ⟨B, hB⟩ := Mobius.mobiusSpecialLinearProjection_surjective G
  rw [← hB]
  exact ellipticFree_diagonal_double_commutator_trace_actual _ B (by rfl) (by rfl)

/-- Ordinary actual commutator trace is continuous when its first map is fixed. -/
theorem ellipticFree_commutatorTrace_continuous_right (f : Mobius.complexMobiusGroup) :
    Continuous (fun g => Mobius.mobiusCommutatorTrace f g) := by
  obtain ⟨A, rfl⟩ := Mobius.mobiusSpecialLinearProjection_surjective f
  apply Mobius.mobiusSpecialLinearProjection_isQuotientMap.continuous_iff.mpr
  have ht : Continuous (fun B : Auxiliary.Algebra.SpecialLinear2 =>
      Matrix.trace (Mobius.Classification.specialCommutator A B : Auxiliary.Algebra.ComplexMatrix2)) := by
    apply jorgensen_specialLinear_trace_continuous.comp
    unfold Mobius.Classification.specialCommutator
    fun_prop
  convert! ht using 1
  funext B
  exact Mobius.mobiusCommutatorTrace_representatives _ _ A B rfl rfl

theorem ellipticFree_commutatorTrace_one_right (f : Mobius.complexMobiusGroup) :
    Mobius.mobiusCommutatorTrace f 1 = 2 := by
  obtain ⟨A, rfl⟩ := Mobius.mobiusSpecialLinearProjection_surjective f
  have h := Mobius.mobiusCommutatorTrace_representatives _ _ A 1 rfl (map_one _)
  rw [h]
  have he : Mobius.Classification.specialCommutator A 1 = 1 := by
    unfold Mobius.Classification.specialCommutator
    group
  rw [he]
  norm_num [Matrix.trace_fin_two]

/-- Ordinary actual commutator trace inherits the non-elliptic real trace interval from the original group. -/
theorem ellipticFree_commutatorTrace_interval (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.HasInvariantComplexDisc H) (hE : IsEllipticFree H)
    (f g : H) : (Mobius.mobiusCommutatorTrace f.val g.val).im = 0 ∧
      ((Mobius.mobiusCommutatorTrace f.val g.val).re ≤ -2 ∨ 2 ≤ (Mobius.mobiusCommutatorTrace f.val g.val).re) := by
  obtain ⟨A, hA⟩ := Mobius.mobiusSpecialLinearProjection_surjective f.val
  obtain ⟨B, hB⟩ := Mobius.mobiusSpecialLinearProjection_surjective g.val
  have hc : Mobius.mobiusSpecialLinearProjection (Mobius.Classification.specialCommutator A B) ∈ H := by
    rw [ellipticFree_commutator_projection, hA, hB]
    exact H.mul_mem (H.mul_mem (H.mul_mem f.property g.property) (H.inv_mem f.property)) (H.inv_mem g.property)
  have ht := ellipticFree_specialLinear_trace H hD hE (Mobius.Classification.specialCommutator A B) hc
  rwa [← Mobius.mobiusCommutatorTrace_representatives f.val g.val A B hA hB] at ht


/-- A convergent near-identity sequence must eventually have zero commutator defect
with any fixed hyperbolic element of the same elliptic-free disc group. -/
theorem ellipticFree_eventually_commutatorTrace_eq_two (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.HasInvariantComplexDisc H) (hE : IsEllipticFree H)
    (u : ℕ → H) (hu : Tendsto (fun n => (u n).val) atTop (𝓝 1))
    (f : H) (hf : Mobius.MobiusHyperbolic f.val) :
    ∀ᶠ n in atTop, Mobius.mobiusCommutatorTrace f.val (u n).val = 2 := by
  obtain ⟨r, hr, htr⟩ := ellipticFree_squaredTrace_ge_four H hD hE f
  have hr4 : 4 < r := by
    apply lt_of_le_of_ne hr
    intro he
    have hpar : Mobius.MobiusBoundaryParabolic f.val :=
      (Mobius.mobius_parabolic_iff_squaredTrace_eq_four f.val hf.1.1).mpr (by
        rw [← he] at htr; norm_num at htr; exact htr)
    exact hf.1.not_parabolic hpar
  let c : ℕ → H := fun n => f * u n * f⁻¹ * (u n)⁻¹
  have hc : Tendsto (fun n => (c n).val) atTop (𝓝 1) := by
    have h := (((tendsto_const_nhds (x := f.val)).mul hu).mul
      (tendsto_const_nhds (x := f.val⁻¹))).mul hu.inv
    simpa only [c, Subgroup.coe_mul, Subgroup.coe_inv, mul_one, mul_inv_cancel, inv_one] using h
  have ht : Tendsto (fun n => (Mobius.mobiusCommutatorTrace f.val (u n).val).re) atTop (𝓝 2) := by
    have h := ((Complex.continuous_re.comp (ellipticFree_commutatorTrace_continuous_right f.val)).tendsto 1).comp hu
    simpa [Function.comp_def, ellipticFree_commutatorTrace_one_right] using h
  have ht2 : Tendsto (fun n => (Mobius.mobiusCommutatorTrace f.val (c n).val).re) atTop (𝓝 2) := by
    have h := ((Complex.continuous_re.comp (ellipticFree_commutatorTrace_continuous_right f.val)).tendsto 1).comp hc
    simpa [Function.comp_def, ellipticFree_commutatorTrace_one_right] using h
  have hsmall := ht.eventually (gt_mem_nhds (show 2 < r - 2 by linarith))
  have hpos := ht.eventually (lt_mem_nhds (show (-1 : ℝ) < 2 by norm_num))
  have hpos2 := ht2.eventually (lt_mem_nhds (show (-1 : ℝ) < 2 by norm_num))
  filter_upwards [hsmall, hpos, hpos2] with n hn hn1 hn2
  obtain ⟨him, hint⟩ := ellipticFree_commutatorTrace_interval H hD hE f (u n)
  obtain ⟨him2, hint2⟩ := ellipticFree_commutatorTrace_interval H hD hE f (c n)
  have hb : 2 ≤ (Mobius.mobiusCommutatorTrace f.val (u n).val).re := by rcases hint with h | h <;> linarith
  have hb2 : 2 ≤ (Mobius.mobiusCommutatorTrace f.val (c n).val).re := by rcases hint2 with h | h <;> linarith
  have he := ellipticFree_hyperbolic_double_commutator_trace f.val (u n).val hf
  have hre := congrArg Complex.re he
  rw [htr] at hre
  change (Mobius.mobiusCommutatorTrace f.val (c n).val - 2).re = _ at hre
  norm_num [Complex.sub_re, Complex.sub_im, Complex.mul_re, him] at hre
  apply Complex.ext
  · change (Mobius.mobiusCommutatorTrace f.val (u n).val).re = 2
    nlinarith
  · simpa using him


/--
In the actual invariant-disc group: excluding
elliptics forces every non-elementary group to be discrete.
-/
theorem discrete_of_ellipticFree_nonElementary_invariant_disc (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.HasInvariantComplexDisc H) (hE : IsEllipticFree H) (hH : IsNonElementary H) :
    Mobius.IsDiscreteMobiusSubgroup H := by
  obtain ⟨v, _, hL, hDis⟩ := exists_injective_loxodromic_sequence_pairwise_disjoint_fixedPoints H hH
  have hHyp (i : ℕ) : Mobius.MobiusHyperbolic (v i).val := by
    obtain ⟨D, hD, hp⟩ := hD
    exact ⟨hL i, D, hD, hp (v i)⟩
  apply (DiscreteGroups.MatrixGroups.discrete_iff_identity_sequences H).mpr
  intro u hu
  have h0 := ellipticFree_eventually_commutatorTrace_eq_two H hD hE u hu (v 0) (hHyp 0)
  have h1 := ellipticFree_eventually_commutatorTrace_eq_two H hD hE u hu (v 1) (hHyp 1)
  have h2 := ellipticFree_eventually_commutatorTrace_eq_two H hD hE u hu (v 2) (hHyp 2)
  filter_upwards [h0, h1, h2] with n hn0 hn1 hn2
  obtain ⟨a, hfa, hua⟩ := (Mobius.mobius_commonFixedPoint_iff_commutatorTrace_eq_two _ _).mpr hn0
  obtain ⟨b, hfb, hub⟩ := (Mobius.mobius_commonFixedPoint_iff_commutatorTrace_eq_two _ _).mpr hn1
  obtain ⟨c, hfc, huc⟩ := (Mobius.mobius_commonFixedPoint_iff_commutatorTrace_eq_two _ _).mpr hn2
  have hne (i j : ℕ) (hij : i ≠ j) (x y : Mobius.ExtendedComplex)
      (hx : (v i).val.val x = x) (hy : (v j).val.val y = y) : x ≠ y := by
    intro he
    apply Set.disjoint_left.mp (hDis hij) ((Mobius.mobiusExtendedFixedPoints_boundary_iff _ x).mpr hx)
    rw [he]
    exact (Mobius.mobiusExtendedFixedPoints_boundary_iff _ y).mpr hy
  apply Subtype.ext
  exact Mobius.mobius_eq_one_of_three_fixed (u n).val a b c
    (hne 0 1 (by decide) a b hfa hfb) (hne 0 2 (by decide) a c hfa hfc)
    (hne 1 2 (by decide) b c hfb hfc) hua hub huc

/-- The discrete-or-elementary assertion for the actual Möbius subgroup. -/
theorem ellipticFree_discrete_or_elementary (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.HasInvariantComplexDisc H) (hE : IsEllipticFree H) :
    Mobius.IsDiscreteMobiusSubgroup H ∨ IsElementary H := by
  by_cases hH : IsElementary H
  · exact Or.inr hH
  · exact Or.inl (discrete_of_ellipticFree_nonElementary_invariant_disc H hD hE hH)

/-- Non-elementary purely hyperbolic groups are discrete without assuming an invariant disc in advance. -/
theorem IsPurelyHyperbolic.discrete {H : Subgroup Mobius.complexMobiusGroup}
    (h : IsPurelyHyperbolic H) (hH : IsNonElementary H) : Mobius.IsDiscreteMobiusSubgroup H :=
  discrete_of_ellipticFree_nonElementary_invariant_disc H (h.hasInvariantComplexDisc hH) h.ellipticFree hH

/-- Purely hyperbolic groups satisfy the discreteness alternative. -/
theorem IsPurelyHyperbolic.discrete_or_elementary {H : Subgroup Mobius.complexMobiusGroup}
    (h : IsPurelyHyperbolic H) : Mobius.IsDiscreteMobiusSubgroup H ∨ IsElementary H := by
  by_cases hH : IsElementary H
  · exact Or.inr hH
  · exact Or.inl (h.discrete hH)


/-- The actual boundary stabilizer at a parabolic fixed point is elementary. -/
theorem parabolicBoundaryStabilizer_elementary (H : Subgroup Mobius.complexMobiusGroup)
    (w : Mobius.ExtendedComplex) : IsElementary (mobiusBoundaryStabilizer H w) := by
  apply isElementary_of_boundary_fixed _ w
  intro f
  exact ((mem_mobiusBoundaryStabilizer H w f.val).mp f.property).2

/--
The intermediate assertion: a parabolic fixed point cannot also be
fixed by any hyperbolic element of an elliptic-free non-elementary disc group.
-/
theorem ellipticFree_parabolic_fixedPoint_not_loxodromic (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.HasInvariantComplexDisc H) (hE : IsEllipticFree H) (hH : IsNonElementary H)
    (p : Mobius.complexMobiusGroup) (hpH : p ∈ H) (hp : Mobius.MobiusParabolic p)
    (w : Mobius.ExtendedComplex) (hpw : p.val w = w)
    (g : Mobius.complexMobiusGroup) (hgH : g ∈ H) (hgw : g.val w = w) : ¬Mobius.MobiusLoxodromic g := by
  let K := mobiusBoundaryStabilizer H w
  have hle : K ≤ H := fun f hf => ((mem_mobiusBoundaryStabilizer H w f).mp hf).1
  have hKd : Mobius.IsDiscreteMobiusSubgroup K :=
    Fuchsian.discreteMobius_subgroup_of_le H K (discrete_of_ellipticFree_nonElementary_invariant_disc H hD hE hH) hle
  have hpK : p ∈ K := (mem_mobiusBoundaryStabilizer H w p).mpr ⟨hpH, hpw⟩
  have hgK : g ∈ K := (mem_mobiusBoundaryStabilizer H w g).mpr ⟨hgH, hgw⟩
  exact discrete_elementary_parabolic_no_loxodromic K hKd
    (parabolicBoundaryStabilizer_elementary H w) p hpK hp g hgK

/--
The full stabilizer assertion, with the genuine subgroup, its native
discrete topology, its cyclicity, and the geometric type of each nonidentity map.
-/
theorem ellipticFree_parabolic_stabilizer (H : Subgroup Mobius.complexMobiusGroup)
    (hD : Mobius.HasInvariantComplexDisc H) (hE : IsEllipticFree H) (hH : IsNonElementary H)
    (p : Mobius.complexMobiusGroup) (hpH : p ∈ H) (hp : Mobius.MobiusParabolic p)
    (w : Mobius.ExtendedComplex) (hpw : p.val w = w) :
    Mobius.IsDiscreteMobiusSubgroup (mobiusBoundaryStabilizer H w) ∧
      IsCyclic (mobiusBoundaryStabilizer H w) ∧
      ∀ f : mobiusBoundaryStabilizer H w, f.val ≠ 1 → Mobius.MobiusParabolic f.val := by
  let K := mobiusBoundaryStabilizer H w
  have hle : K ≤ H := fun f hf => ((mem_mobiusBoundaryStabilizer H w f).mp hf).1
  have hfix : ∀ f ∈ K, f.val w = w :=
    fun f hf => ((mem_mobiusBoundaryStabilizer H w f).mp hf).2
  have hKd : Mobius.IsDiscreteMobiusSubgroup K :=
    Fuchsian.discreteMobius_subgroup_of_le H K (discrete_of_ellipticFree_nonElementary_invariant_disc H hD hE hH) hle
  have hpK : p ∈ K := (mem_mobiusBoundaryStabilizer H w p).mpr ⟨hpH, hpw⟩
  have hKdisc : Mobius.HasInvariantComplexDisc K := by
    obtain ⟨D, hd, hi⟩ := hD
    exact ⟨D, hd, fun f => hi ⟨f.val, hle f.property⟩⟩
  have hKno : ∀ f ∈ K, ¬Mobius.MobiusElliptic f := fun f hf => hE ⟨f, hle hf⟩
  refine ⟨hKd, Fuchsian.discrete_parabolic_common_fixed_cyclic K hKd hKdisc w hfix p hpK hp hKno, ?_⟩
  intro f hf
  rcases Mobius.mobius_nonidentity_type_trichotomy f.val hf with hp' | hl | he
  · exact hp'
  · exact False.elim (ellipticFree_parabolic_fixedPoint_not_loxodromic H hD hE hH p hpH hp
      w hpw f.val (hle f.property) (hfix f.val f.property) hl)
  · exact False.elim (hKno f.val f.property he)

end LowDimensionalTopology.Geometry.DiscreteGroups
