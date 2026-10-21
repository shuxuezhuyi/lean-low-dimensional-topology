module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleReflectionGroups
public import LowDimensionalTopology.Geometry.Hyperbolic.Trigonometry.TriangleInradius
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticRotationAngles
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
/-- The exact squared trace is determined by the actual finite or ideal triangle angle. -/
theorem closedTriangle_reflection_trace_alpha
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedDiscTriangle) :
    (Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineB.toHalfPlane T.sideLineC.toHalfPlane).val) ^ 2 =
      4 * Real.cos T.alpha ^ 2 := by
  let q := T.incenter
  let x := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineB.incenterNormal T.sideLineB.incenterOffset
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q)
  let y := _root_.LowDimensionalTopology.Geometry.Hyperbolic.closedDiscKleinAffine T.sideLineC.incenterNormal T.sideLineC.incenterOffset
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToClosedModel q)
  let P := inner ℝ T.sideLineB.incenterNormal T.sideLineC.incenterNormal -
    T.sideLineB.incenterOffset * T.sideLineC.incenterOffset
  have hq : q ∈ T.interior := T.incenter_mem_interior
  have hn := T.interior_not_sideLines q hq
  have hx : x ≠ 0 := by
    intro hx
    exact hn.2.1 ((T.sideLineB.closedCarrier_mem_interior_iff q).mp
      ((T.sideLineB.closed_incenter_affine_zero_iff _).mp hx))
  have hy : y ≠ 0 := by
    intro hy
    exact hn.2.2 ((T.sideLineC.closedCarrier_mem_interior_iff q).mp
      ((T.sideLineC.closed_incenter_affine_zero_iff _).mp hy))
  have he : Real.cos T.alpha * |x| * |y| = -(P * x * y) :=
    T.cosine_alpha_side_normals q hq
  have hs := congrArg (fun r : ℝ => r ^ 2) he
  simp only [mul_pow, neg_sq, sq_abs] at hs
  have hc : Real.cos T.alpha ^ 2 = P ^ 2 := by
    apply mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 hx) (pow_ne_zero 2 hy))
    nlinarith only [hs]
  have ht : Matrix.trace
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineB.toHalfPlane T.sideLineC.toHalfPlane).val / 2 = P :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_trace_pairing _ _
  rw [← ht] at hc
  nlinarith only [hc]

theorem triangle_first_generator_trace (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    (Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB).val) ^ 2 =
      4 * Real.cos T.gamma ^ 2 :=
  closedTriangle_reflection_trace_alpha T.toDiscTriangle.cycle.cycle

theorem triangle_second_generator_trace (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    (Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineC T.sideLineB).val) ^ 2 =
      4 * Real.cos T.alpha ^ 2 := by
  have h := closedTriangle_reflection_trace_alpha T.toDiscTriangle
  have ht : Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineC T.sideLineB).val =
      Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineB T.sideLineC).val := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_coe, _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_coe, Matrix.trace_smul, Matrix.trace_smul,
      Matrix.trace_mul_comm, mul_comm T.sideLineC.reflectionScale T.sideLineB.reflectionScale]
  rw [ht]
  exact h

/-- The actual oriented rotation angle is twice the corner angle, with orientation reversed
when the order of the two reflections is reversed. -/
theorem elliptic_rotation_angle_of_trace_cos (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) Real.pi)
    (ht : Matrix.trace A.val ^ 2 = 4 * Real.cos θ ^ 2) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA = 2 * θ ∨
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA = 2 * Real.pi - 2 * θ := by
  have hs := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A hA
  have he : Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2) ^ 2 = Real.cos θ ^ 2 := by
    nlinarith only [ht, hs.2.2.2]
  have hφ : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2 ∈ Icc (0 : ℝ) Real.pi := by
    constructor <;> linarith only [hs.1.1, hs.1.2]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with he | he
  · have heq := Real.injOn_cos hφ ⟨hθ.1.le, hθ.2.le⟩ he
    exact Or.inl (by linarith)
  · have hneg : Real.pi - θ ∈ Icc (0 : ℝ) Real.pi := by
      constructor <;> linarith only [hθ.1, hθ.2]
    have heq := Real.injOn_cos hφ hneg (by simpa only [Real.cos_pi_sub] using he)
    exact Or.inr (by linarith)

theorem triangle_first_generator_elliptic_of_gamma_pos
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hγ : 0 < T.gamma) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB)) := by
  apply reflectionProductSL_common_finite_elliptic _ _ (triangle_sideLineAB_distinct T) T.c
  · intro hi
    have he : T.gamma = 0 :=
      T.toDiscTriangle.gamma_of_ideal ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.closedModelCayley_norm_one_iff T.c).mpr hi)
    linarith
  · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.c).mp T.toDiscTriangle.c_mem_sideLineA
  · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.c).mp T.toDiscTriangle.c_mem_sideLineB

theorem triangle_first_generator_rotation_angle
    (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hγ : 0 < T.gamma) :
    let hE := triangle_first_generator_elliptic_of_gamma_pos T hγ
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB) hE = 2 * T.gamma ∨
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineA T.sideLineB) hE =
        2 * Real.pi - 2 * T.gamma :=
  elliptic_rotation_angle_of_trace_cos _ _ T.gamma
    ⟨hγ, T.toDiscTriangle.cycle.cycle.alpha_mem_Ico.2⟩ (triangle_first_generator_trace T)

/-- Finite order forces rationality of the actual elliptic rotation angle. -/
theorem finite_order_elliptic_rotation_rational (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hfin : IsOfFinOrder (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    ∃ r : ℚ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA = (r : ℝ) * (2 * Real.pi) := by
  let θ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA
  let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  let u := Complex.exp (Complex.I * θ)
  let F := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A
  let ρ : ℍ → ℂ := fun z => ((z : ℂ) - (v : ℂ)) / ((z : ℂ) - star (v : ℂ))
  have hstep (z : ℍ) : ρ (F z) = u * ρ z := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A hA).2.2.1 z
  obtain ⟨z, hz⟩ := exists_ne v
  have hρ : ρ z ≠ 0 := by
    apply div_ne_zero
    · exact sub_ne_zero.mpr (UpperHalfPlane.coe_injective.ne hz)
    · intro he
      have him := congrArg Complex.im he
      simp only [Complex.sub_im, Complex.star_def, Complex.conj_im,
        UpperHalfPlane.coe_im, Complex.zero_im] at him
      linarith [z.im_pos, v.im_pos]
  have hiter (n : ℕ) : ρ ((F ^ n) z) = u ^ n * ρ z := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', IsometryEquiv.mul_apply, hstep, ih, pow_succ']
      exact (mul_assoc _ _ _).symm
  obtain ⟨n, hn, hpow⟩ := hfin.exists_pow_eq_one
  have hnat : F ^ n = 1 := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension_injective
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A ^ n) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneExtension 1
    rw [map_pow, nativeHalfPlaneExtension_hSL, ← map_pow, hpow, map_one, map_one]
  have hu : u ^ n = 1 := by
    apply mul_right_cancel₀ hρ
    calc
      u ^ n * ρ z = ρ ((F ^ n) z) := (hiter n).symm
      _ = 1 * ρ z := by rw [hnat]; simp
  have hexp : Complex.exp ((n : ℂ) * (Complex.I * θ)) = 1 := by
    rw [Complex.exp_nat_mul]
    exact hu
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp hexp
  have hr : (n : ℝ) * θ = (k : ℝ) * (2 * Real.pi) := by
    have him := congrArg Complex.im hk
    norm_num at him
    exact him
  refine ⟨(k : ℚ) / (n : ℚ), ?_⟩
  change θ = _
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp [hnR]
  nlinarith only [hr]

theorem discrete_native_elliptic_rotation_rational (H : Subgroup (ℍ ≃ᵢ ℍ))
    (hd : DiscreteTopology H) (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A ∈ H) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    ∃ r : ℚ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA = (r : ℝ) * (2 * Real.pi) := by
  have hD := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlane_subgroup_discrete_iff H).mp hd
  have hm : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusToFull (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.nativeHalfPlaneImage H := by
    rw [← nativeHalfPlaneExtension_hSL]
    exact Subgroup.mem_map.mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A, hmem, rfl⟩
  have hf := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.full_discrete_ellipticsFiniteOrder _ hD _ hm ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A, rfl, hA⟩
  have ho := orderOf_injective _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusToFull _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusToFull_isometry.injective
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
  apply finite_order_elliptic_rotation_rational A hA
  apply orderOf_pos_iff.mp
  simpa only [ho] using hf.orderOf_pos

theorem discrete_native_corner_rational (H : Subgroup (ℍ ≃ᵢ ℍ)) (hd : DiscreteTopology H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hmem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A ∈ H)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) Real.pi)
    (ht : Matrix.trace A.val ^ 2 = 4 * Real.cos θ ^ 2) :
    ∃ r : ℚ, θ = (r : ℝ) * Real.pi := by
  obtain ⟨r, hr⟩ := discrete_native_elliptic_rotation_rational H hd A hmem hA
  rcases elliptic_rotation_angle_of_trace_cos A hA θ hθ ht with he | he
  · exact ⟨r, by nlinarith only [hr, he]⟩
  · refine ⟨1-r, ?_⟩
    push_cast
    nlinarith only [hr, he]

theorem triangleReflectionGroup_cycle (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    triangleReflectionGroup T.cycle = triangleReflectionGroup T := by
  change Subgroup.closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry ''
      {T.sideLineB, T.sideLineC, T.sideLineA}) =
    Subgroup.closure (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.reflectionIsometry ''
      {T.sideLineA, T.sideLineB, T.sideLineC})
  have hs : ({T.sideLineB, T.sideLineC, T.sideLineA} : Set _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) =
      {T.sideLineA, T.sideLineB, T.sideLineC} := by
    ext L
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  rw [hs]

theorem triangleConformalGroup_cycle (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    triangleConformalGroup T.cycle = triangleConformalGroup T := by
  simp only [triangleConformalGroup, triangleReflectionGroup_cycle]

/-- The actual angle at every finite or ideal first vertex is a rational multiple of pi
whenever the original conformal triangle subgroup is discrete. -/
theorem discrete_triangle_alpha_rational (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hd : DiscreteTopology (triangleConformalGroup T)) :
    ∃ r : ℚ, T.alpha = (r : ℝ) * Real.pi := by
  by_cases hzero : T.alpha = 0
  · exact ⟨0, by simp [hzero]⟩
  have hα : T.alpha ∈ Ioo (0 : ℝ) Real.pi :=
    ⟨lt_of_le_of_ne T.toDiscTriangle.alpha_mem_Ico.1 (Ne.symm hzero),
      T.toDiscTriangle.alpha_mem_Ico.2⟩
  let A := _root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL T.sideLineB T.sideLineC
  have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A ∈ triangleConformalGroup T := by
    rw [triangleConformalGroup_eq_pairProductGroup, ← reflectionProductSL_native]
    exact trianglePairProductGroup_pair_mem T _ _
      (by simp [triangleReflectionSides]) (by simp [triangleReflectionSides])
  have hE : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    apply reflectionProductSL_common_finite_elliptic _ _ (triangle_sideLineCB_distinct T).symm T.a
    · intro hi
      exact hzero (T.ideal_vertex_data hi).1
    · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.a).mp T.toDiscTriangle.a_mem_sideLineB
    · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscLine.closedCarrier_cayley_mem _ T.a).mp T.toDiscTriangle.a_mem_sideLineC
  exact discrete_native_corner_rational _ hd A hm hE T.alpha hα
    (closedTriangle_reflection_trace_alpha T.toDiscTriangle)

/-- The necessary rational-angle condition for all three original triangle angles. -/
theorem discrete_triangle_angles_rational (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hd : DiscreteTopology (triangleConformalGroup T)) :
    (∃ r : ℚ, T.alpha = (r : ℝ) * Real.pi) ∧
      (∃ r : ℚ, T.beta = (r : ℝ) * Real.pi) ∧
      (∃ r : ℚ, T.gamma = (r : ℝ) * Real.pi) := by
  have hcycle : DiscreteTopology (triangleConformalGroup T.cycle) := by
    rw [triangleConformalGroup_cycle]
    exact hd
  have hcycle2 : DiscreteTopology (triangleConformalGroup T.cycle.cycle) := by
    rw [triangleConformalGroup_cycle]
    exact hcycle
  exact ⟨discrete_triangle_alpha_rational T hd,
    discrete_triangle_alpha_rational T.cycle hcycle,
    discrete_triangle_alpha_rational T.cycle.cycle hcycle2⟩

theorem positive_rational_angle_reduced (θ : ℝ) (hθ : θ ∈ Ioo (0 : ℝ) Real.pi)
    (hr : ∃ r : ℚ, θ = (r : ℝ) * Real.pi) :
    ∃ k p : ℕ, 0 < k ∧ k < p ∧ Nat.Coprime k p ∧ θ = (k : ℝ) * Real.pi / p := by
  obtain ⟨r, hr⟩ := hr
  have hrR : 0 < (r : ℝ) := by nlinarith only [hr, hθ.1, Real.pi_pos]
  have hrQ : 0 < r := by exact_mod_cast hrR
  have hn := Rat.num_pos.mpr hrQ
  have hc : (r.num.natAbs : ℝ) = (r.num : ℝ) := by
    have he : (r.num.natAbs : ℤ) = r.num := Int.natAbs_of_nonneg hn.le
    simpa only [Int.cast_natCast] using congrArg (fun n : ℤ => (n : ℝ)) he
  have hd : 0 < (r.den : ℝ) := by exact_mod_cast r.den_pos
  have hform : θ = (r.num.natAbs : ℝ) * Real.pi / r.den := by
    rw [hc, hr, Rat.cast_def]
    ring
  have hkp : (r.num.natAbs : ℝ) < r.den := by
    apply (mul_lt_mul_iff_left₀ Real.pi_pos).mp
    have hh := (div_lt_iff₀ hd).mp (hform ▸ hθ.2)
    nlinarith only [hh]
  refine ⟨r.num.natAbs, r.den, ?_, ?_, r.reduced, hform⟩
  · have hpos : 0 < (r.num.natAbs : ℝ) := by rw [hc]; exact_mod_cast hn
    exact_mod_cast hpos
  · exact_mod_cast hkp

/-- With a genuinely reduced positive numerator and denominator. -/
theorem discrete_triangle_positive_angle_reduced (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hd : DiscreteTopology (triangleConformalGroup T)) (θ : ℝ)
    (hmem : θ ∈ ({T.alpha, T.beta, T.gamma} : Set ℝ)) (hpos : 0 < θ) :
    ∃ k p : ℕ, 0 < k ∧ k < p ∧ Nat.Coprime k p ∧ θ = (k : ℝ) * Real.pi / p := by
  have hs := discrete_triangle_angles_rational T hd
  have hlt : θ < Real.pi := by
    simp only [mem_insert_iff, mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact T.toDiscTriangle.alpha_mem_Ico.2
    · exact T.toDiscTriangle.cycle.alpha_mem_Ico.2
    · exact T.toDiscTriangle.cycle.cycle.alpha_mem_Ico.2
  apply positive_rational_angle_reduced θ ⟨hpos, hlt⟩
  · simp only [mem_insert_iff, mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hs.1
    · exact hs.2.1
    · exact hs.2.2

theorem triangleConformalGroup_relIndex_two (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    (triangleConformalGroup T).relIndex (triangleReflectionGroup T) = 2 := by
  have hk : (triangleConformalGroup T).subgroupOf (triangleReflectionGroup T) =
      triangleConformalKernel T := by
    ext b
    change (b.val ∈ triangleReflectionGroup T ∧ b.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup) ↔
      b.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup
    exact and_iff_right b.property
  change ((triangleConformalGroup T).subgroupOf (triangleReflectionGroup T)).index = 2
  rw [hk]
  exact triangleConformalKernel_index_two T

theorem triangle_discrete_full_iff_conformal (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    DiscreteTopology (triangleReflectionGroup T) ↔ DiscreteTopology (triangleConformalGroup T) := by
  have hfin : (triangleConformalGroup T).IsFiniteRelIndex (triangleReflectionGroup T) :=
    ⟨by rw [triangleConformalGroup_relIndex_two]; norm_num⟩
  exact (Subgroup.discreteTopology_iff_of_isFiniteRelIndex
    (show triangleConformalGroup T ≤ triangleReflectionGroup T from inf_le_left)).symm

theorem discrete_full_triangle_angles_rational (T : _root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (hd : DiscreteTopology (triangleReflectionGroup T)) :
    (∃ r : ℚ, T.alpha = (r : ℝ) * Real.pi) ∧
      (∃ r : ℚ, T.beta = (r : ℝ) * Real.pi) ∧
      (∃ r : ℚ, T.gamma = (r : ℝ) * Real.pi) :=
  discrete_triangle_angles_rational T ((triangle_discrete_full_iff_conformal T).mp hd)

theorem IsConformalTriangleType.discrete_angles_rational {G : Subgroup (ℍ ≃ᵢ ℍ)}
    {α β γ : ℝ} (hG : IsConformalTriangleType G α β γ) (hd : DiscreteTopology G) :
    (∃ r : ℚ, α = (r : ℝ) * Real.pi) ∧
      (∃ r : ℚ, β = (r : ℝ) * Real.pi) ∧
      (∃ r : ℚ, γ = (r : ℝ) * Real.pi) := by
  obtain ⟨T, rfl, rfl, rfl, rfl⟩ := hG
  exact discrete_triangle_angles_rational T hd

end LowDimensionalTopology.Geometry.Fuchsian
