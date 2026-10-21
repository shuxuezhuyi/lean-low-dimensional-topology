/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticNontriangleDisplacement
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.WeakDisplacementGap
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeDisplacementSharpness
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.ParabolicEllipticCommutators
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual conjugate elliptic pair has precisely the commutator displacement.
No least-angle or discreteness condition enters this metric identity. -/
theorem elliptic_conjugate_pair_displacementM_trace
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    2 + 4 * (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (B*A*B⁻¹)))^2 =
      Matrix.trace (A*B*A⁻¹*B⁻¹).val := by
  have hC : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B*A*B⁻¹)) := by
    simp only [map_mul, map_inv]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation _ _).mpr hA
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  let s := Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2)
  have hs : 0 < s := Real.sin_pos_of_pos_of_lt_pi
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo A
      hA).1 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo A hA).2
  have hsC : 0 < Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle (B*A*B⁻¹) hC / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo _ hC).1
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo _ hC).2
  have hsin : Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle (B*A*B⁻¹) hC / 2) = s := by
    have ha := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A hA).2.2.2
    have hc := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec (B*A*B⁻¹) hC).2.2.2
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation] at hc
    dsimp only [s]
    nlinarith [Real.sin_sq_add_cos_sq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA /
      2),
      Real.sin_sq_add_cos_sq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle (B*A*B⁻¹) hC /
        2)]
  have hcenter := native_elliptic_realSL_conjugate_center A B hA hC
  have hM := _root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_pair_displacementM_square A (B*A*B⁻¹) hA hC
  dsimp only at hM
  rw [hcenter, hsin] at hM
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (B*A*B⁻¹)))^2 =
    (s*s)^2 * (Real.cosh (dist u (B • u))^2 - 1) /
      (s^2+s^2+2*s*s*Real.cosh (dist u (B • u))) at hM
  have hd : 0 < s^2+s^2+2*s*s*Real.cosh (dist u (B • u)) := by positivity
  have he := (eq_div_iff hd.ne').mp hM
  have hc := _root_.LowDimensionalTopology.Geometry.Hyperbolic.real_cosh_eq_one_add_two_sinh_half_sq (dist u (B • u))
  have hh : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (B*A*B⁻¹)))^2 =
      s^2 * Real.sinh (dist u (B • u) / 2)^2 := by
    have hfac : (s^2+s^2+2*s*s*Real.cosh (dist u (B • u))) *
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (B*A*B⁻¹)))^2 -
          s^2 * Real.sinh (dist u (B • u) / 2)^2) = 0 := by
      linear_combination he + s^4 *
        (Real.cosh (dist u (B • u)) + 1) * hc
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left hd.ne')
  have ht := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_commutator_trace A B hA
  change Matrix.trace (A*B*A⁻¹*B⁻¹).val / 2 =
    1 + 2 * Real.sinh (dist u (B • u) / 2)^2 * s^2 at ht
  rw [hh]
  linarith

/-- Conjugating a noninvolutory elliptic by a generator in a nonelementary
pair still gives a nonelementary elliptic pair in the original discrete group. -/
theorem native_elliptic_conjugate_pair_nonElementary
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) (hBH :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hord : 3 ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B*A*B⁻¹)} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  have hu : A • u = u := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ u).mpr rfl
  have hBu : B • u ≠ u := by
    intro hfix
    apply hne
    apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_elementary_of_common_fixed _ _ ((u : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (u : ℂ) = (u : ℂ)
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action, hu]
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val (u : ℂ) = (u : ℂ)
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action, hfix]
  let C := B*A*B⁻¹
  have hC : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) := native_elliptic_realSL_conjugate A B hA
  have hCu : C • u ≠ u := by
    intro hfix
    have he : u = B • u := ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff C _ u).mp
      hfix).trans
      (native_elliptic_realSL_conjugate_center A B hA hC)
    exact hBu he.symm
  let K := Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hAK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ K := Subgroup.subset_closure (by simp)
  have hCK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C ∈ K := Subgroup.subset_closure (by simp)
  have hKH : K ≤ H := (Subgroup.closure_le H).mpr (by
    intro k hk
    rcases hk with rfl | rfl
    · exact hAH
    · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B*A*B⁻¹) ∈ H
      simp only [map_mul, map_inv]
      exact H.mul_mem (H.mul_mem hBH hAH) (H.inv_mem hBH))
  intro helem
  let Q : HalfPlaneFuchsianGroup K :=
    ⟨fun k => P.preserves ⟨k.val, hKH k.property⟩,
      discreteMobius_subgroup_of_le H K P.discrete hKH⟩
  let : Finite K := elementary_elliptic_noninvolution_finite Q.asFuchsianDisc
    helem (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) hAK hA (by omega)
  have hcomm := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_commutator_translationLength A C hA hCu).1
  have hcK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*C*A⁻¹*C⁻¹) ∈ K := by
    simp only [map_mul, map_inv]
    exact K.mul_mem (K.mul_mem (K.mul_mem hAK hCK) (K.inv_mem hAK)) (K.inv_mem hCK)
  have hfin := isOfFinOrder_of_finite (⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*C*A⁻¹*C⁻¹),
    hcK⟩ : K)
  obtain ⟨n, hn, hpow⟩ := hfin.exists_pow_eq_one
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_parabolic_or_loxodromic_not_isOfFinOrder _ (Or.inr
    hcomm.1)
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, congrArg Subtype.val hpow⟩)

/--
The unnumbered ambient nontriangle trace assertion following.
The order belongs to the actual original elliptic, without a primitive assumption.
-/
theorem HalfPlaneFuchsianGroup.nontriangle_elliptic_commutator_trace_bound
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) (hBH :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hord : 3 ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hnt : ¬ IsMobiusTriangleGroup H) :
    2 + 4 * Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))^2 ≤
      Matrix.trace (A*B*A⁻¹*B⁻¹).val := by
  let C := B*A*B⁻¹
  let K := Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C} : Set
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hKH : K ≤ H := (Subgroup.closure_le H).mpr (by
    intro k hk
    rcases hk with rfl | rfl
    · exact hAH
    · change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B*A*B⁻¹) ∈ H
      simp only [map_mul, map_inv]
      exact H.mul_mem (H.mul_mem hBH hAH) (H.inv_mem hBH))
  let Q : HalfPlaneFuchsianGroup K :=
    ⟨fun k => P.preserves ⟨k.val, hKH k.property⟩,
      discreteMobius_subgroup_of_le H K P.discrete hKH⟩
  have hC : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) := native_elliptic_realSL_conjugate A B hA
  have hKne := native_elliptic_conjugate_pair_nonElementary P A B hAH hBH hA hord hne
  have hKnt : ¬ IsMobiusTriangleGroup K := fun htri =>
    hnt (fuchsian_supergroup_of_triangleGroup_is_triangleGroup P.asFuchsianDisc K hKH htri)
  have hbound := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_pair_nontriangle_square
    Q A C hA hC rfl hKne hKnt
  have horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) = orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    change orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B*A*B⁻¹)) = _
    simp only [map_mul, map_inv]
    exact (MulAut.conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      B)).orderOf_eq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
  have he (x : ℝ) : (x+x)^2 / (4-(x-x)^2) = x^2 := by ring
  rw [horder, he] at hbound
  have ht := elliptic_conjugate_pair_displacementM_trace A B hA
  change 2 + 4 * (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C))^2 = _ at ht
  linarith

/-- Both source inequalities, including the absolute lower value three. -/
theorem HalfPlaneFuchsianGroup.nontriangle_elliptic_trace_bounds
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) (hBH :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hord : 3 ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hnt : ¬ IsMobiusTriangleGroup H) :
    2 + 4 * Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))^2 ≤
        Matrix.trace (A*B*A⁻¹*B⁻¹).val ∧
      3 ≤ Matrix.trace (A*B*A⁻¹*B⁻¹).val ∧
      4 ≤ |(Matrix.trace A.val)^2-4| + |Matrix.trace (A*B*A⁻¹*B⁻¹).val-2| := by
  have hbound := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nontriangle_elliptic_commutator_trace_bound
    P A B hAH hBH hA hord hne hnt
  have hcos := elliptic_order_cos_ge_half _ hord
  have htr := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA
  have hsin := elliptic_order_half_sine_lower A hA hord
  have hα := pi_div_acute_of_two_lt (orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (by exact_mod_cast (by omega : 2 < orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)))
  have hs : 0 ≤ Real.sin (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :=
    (Real.sin_pos_of_pos_of_lt_pi hα.1 (by linarith [hα.2, Real.pi_pos])).le
  have ht : 0 ≤ Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2) :=
    (Real.sin_pos_of_pos_of_lt_pi (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo A hA).1
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo A hA).2).le
  have hsq := (sq_le_sq₀ hs ht).mpr hsin
  have htrace : (Matrix.trace A.val)^2 ≤
      4 * Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))^2 := by
    have hspec := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A hA).2.2.2
    nlinarith [Real.sin_sq_add_cos_sq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA /
      2),
      Real.sin_sq_add_cos_sq (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))]
  have hthree : 3 ≤ Matrix.trace (A*B*A⁻¹*B⁻¹).val := by
    nlinarith [sq_nonneg (Real.cos (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A)) - 1/2)]
  have htwo : 0 ≤ Matrix.trace (A*B*A⁻¹*B⁻¹).val-2 := by linarith
  refine ⟨hbound, hthree, ?_⟩
  rw [abs_of_neg (by linarith : (Matrix.trace A.val)^2-4 < 0),
    abs_of_nonneg htwo]
  linarith

/-- The ambient nontriangle trace bounds use the actual whole invariant disc,
the actual elliptic order, and lift-independent complex trace quantities. -/
theorem fuchsian_nontriangle_elliptic_trace_bounds
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (g f : H)
    (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val) (hord : 3 ≤ orderOf g.val)
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({g.val, f.val} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hnt : ¬ IsMobiusTriangleGroup H) :
    2 + 4 * Real.cos (Real.pi / orderOf g.val)^2 ≤ (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace
      f.val g.val).re ∧
      3 ≤ (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f.val g.val).re ∧
      4 ≤ ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace g.val-4‖ + ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f.val g.val-2‖ := by
  let A := D.normalizedLift g
  let B := D.normalizedLift f
  let q := D.halfPlaneNormalizer
  let P : HalfPlaneFuchsianGroup D.normalizedGroup :=
    ⟨fun k => D.normalizedGroup_preserves_halfPlane k.val k.property, D.normalizedGroup_discrete⟩
  have hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation g.val q).mpr hg
  have hmem (k : H) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift k) ∈ D.normalizedGroup := by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _
      _).mpr ⟨k.val, k.property, rfl⟩
  have horder : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) = orderOf g.val := by
    rw [D.normalizedLift_spec]
    exact (MulAut.conj q).orderOf_eq g.val
  have hordA : 3 ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by rwa [horder]
  have hneA : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
    have h := hne.conjugation q
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation] at h
    rwa [←D.normalizedLift_spec g, ←D.normalizedLift_spec f] at h
  have hntA : ¬ IsMobiusTriangleGroup D.normalizedGroup := fun ht =>
    hnt (isMobiusTriangleGroup_of_conjugate H q ht)
  have h := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nontriangle_elliptic_trace_bounds
    P A B (hmem g) (hmem f) hA hordA hneA hntA
  have hswap : Matrix.trace (B*A*B⁻¹*A⁻¹).val = Matrix.trace (A*B*A⁻¹*B⁻¹).val := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_commutator_trace,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_commutator_trace]
    have hp : Matrix.trace (B*A).val = Matrix.trace (A*B).val :=
      Matrix.trace_mul_comm B.val A.val
    rw [hp]
    ring
  have hcomm : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f.val g.val =
      ((Matrix.trace (A*B*A⁻¹*B⁻¹).val : ℝ) : ℂ) := by
    rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFree_commutatorTrace_conjugation f.val g.val q,
      ←D.normalizedLift_spec f, ←D.normalizedLift_spec g, realSLMobius_commutatorTrace, hswap]
  have htrace : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace g.val = ((Matrix.trace A.val)^2 : ℝ) := by
    rw [←_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace_conjugation g.val q,
      ←D.normalizedLift_spec g, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace]
  rw [horder] at h
  refine ⟨by simpa only [hcomm, Complex.ofReal_re] using h.1,
    by simpa only [hcomm, Complex.ofReal_re] using h.2.1, ?_⟩
  rw [htrace, hcomm]
  simpa only [←Complex.ofReal_ofNat, ←Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] using h.2.2

/-- The exact elementary-or-both-bounds alternative. -/
theorem fuchsian_nontriangle_elliptic_pair_trace_alternative
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H) (g f : H)
    (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val) (hord : 3 ≤ orderOf g.val)
    (hnt : ¬ IsMobiusTriangleGroup H) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({g.val, f.val} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∨
      (2 + 4 * Real.cos (Real.pi / orderOf g.val)^2 ≤
        (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f.val g.val).re ∧
        3 ≤ (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f.val g.val).re ∧
        4 ≤ ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace g.val-4‖ + ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace f.val g.val-2‖) := by
  by_cases he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({g.val, f.val} :
    Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))
  · exact Or.inl he
  · exact Or.inr (fuchsian_nontriangle_elliptic_trace_bounds D g f hg hord he hnt)

end LowDimensionalTopology.Geometry.Fuchsian
