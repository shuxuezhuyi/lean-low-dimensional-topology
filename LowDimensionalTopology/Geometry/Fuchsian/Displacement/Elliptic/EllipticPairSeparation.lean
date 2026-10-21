/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticMinimizers
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicEllipticOrderBounds
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.FuchsianDisplacementInvariants
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

/-- The least half-angle sine bound includes genuine order-two elliptics. -/
theorem elliptic_finite_order_half_sine_lower
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hp : 2 ≤ orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    Real.sin (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) ≤
      Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2) := by
  by_cases hthree : 3 ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
  · exact elliptic_order_half_sine_lower A hA hthree
  · have ht : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) = 2 := by omega
    have htrace := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_order_two_iff_trace_zero A
      hA.1).mp ht
    have hrot := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A hA).2.2.2
    rw [htrace] at hrot
    have hs := Real.sin_pos_of_pos_of_lt_pi (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo A hA).1
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo A hA).2
    rw [ht]
    norm_num only [Nat.cast_ofNat, Real.sin_pi_div_two]
    nlinarith only [hrot, hs, Real.sin_sq_add_cos_sq
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2)]

/-- A nonelliptic actual product gives the center separation in the source cosine formula.
The premise concerns the actual product type, not a prescribed distance bound. -/
theorem elliptic_pair_separation_of_product_not_elliptic
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))
    (hAB : ¬ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A * B))) :
    let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
    let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
    let θ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2
    let φ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB / 2
    (1 + Real.cos θ * Real.cos φ) / (Real.sin θ * Real.sin φ) ≤
      Real.cosh (dist u v) := by
  have hne := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_ne_one_of_centers_ne A B hA hB huv
  have htrace : 4 ≤ (Matrix.trace (A * B).val)^2 := by
    exact le_of_not_gt (fun hlt => hAB ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _
      hne).mpr hlt))
  have ht := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_abs_trace A B hA hB
  have hneg := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_expression_gt_neg_one A B hA hB huv
  have hθ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo A hA
  have hφ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo B hB
  have hs := mul_pos (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2)
    (Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2)
  dsimp only at ht hneg ⊢
  apply (div_le_iff₀ hs).mpr
  have htr : 2 ≤ |Matrix.trace (A * B).val| := by
    nlinarith only [htrace, sq_abs (Matrix.trace (A * B).val),
      abs_nonneg (Matrix.trace (A * B).val)]
  have habs : 1 ≤ |Real.cosh
      (dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB))) *
      Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2) *
      Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB / 2) -
      Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2) *
      Real.cos (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB / 2)| := by linarith only [ht, htr]
  rcases le_abs.mp habs with h | h
  · nlinarith only [h]
  · linarith only [hneg, h]

/-- Reducing both actual elliptic angles to their least order angles can only lower
the infimum. The centers remain the original centers, including for nonprimitive elements. -/
theorem elliptic_pair_order_radial_ratio_lower
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hp : 2 ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hq : 2 ≤ orderOf
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
    let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
    let s := Real.sin (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    let t := Real.sin (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (s * t)^2 * (Real.cosh (dist u v)^2 - 1) /
      (s^2 + t^2 + 2 * s * t * Real.cosh (dist u v)) ≤
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B))^2 := by
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
  let s := Real.sin (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
  let t := Real.sin (Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
  have hsin (n : ℕ) (hn : 2 ≤ n) : 0 < Real.sin (Real.pi / n) := by
    have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    apply Real.sin_pos_of_pos_of_lt_pi (div_pos Real.pi_pos hn0)
    exact (div_lt_iff₀ hn0).mpr (by nlinarith only [Real.pi_pos, hnR])
  have hs : 0 < s := hsin _ hp
  have ht : 0 < t := hsin _ hq
  obtain ⟨z, hz, heq⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.exists_balanced_radial_point u v s t hs ht
  let m := s * Real.sinh (dist u z)
  have hm0 : 0 ≤ m := mul_nonneg hs.le (Real.sinh_nonneg_iff.mpr dist_nonneg)
  have hm : m ≤ _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) := by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_lower_bound _ _ _).mpr
    intro w
    have hmin := _root_.LowDimensionalTopology.Geometry.Hyperbolic.balanced_radial_point_minimizes u v z hz s t hs.le ht.le heq w
    rw [← heq, max_self] at hmin
    refine hmin.trans (max_le_max ?_ ?_)
    · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_actual_angle_radial A hA]
      exact mul_le_mul_of_nonneg_right (elliptic_finite_order_half_sine_lower A hA hp)
        (Real.sinh_nonneg_iff.mpr dist_nonneg)
    · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_actual_angle_radial B hB]
      exact mul_le_mul_of_nonneg_right (elliptic_finite_order_half_sine_lower B hB hq)
        (Real.sinh_nonneg_iff.mpr dist_nonneg)
  have hden : 0 < s^2 + t^2 + 2 * s * t * Real.cosh (dist u v) := by positivity
  have hsum := _root_.LowDimensionalTopology.Geometry.Hyperbolic.dist_triangle_eq_of_mem_closedHSegment hz
  rw [dist_comm z v] at hsum
  have hid := _root_.LowDimensionalTopology.Geometry.Hyperbolic.balanced_sinh_square_identity s t (dist u z) (dist v
    z) heq
  rw [hsum, Real.sinh_sq] at hid
  change m^2 * (s^2 + t^2 + 2 * s * t * Real.cosh (dist u v)) = _ at hid
  dsimp only
  have he : (s * t)^2 * (Real.cosh (dist u v)^2 - 1) /
      (s^2 + t^2 + 2 * s * t * Real.cosh (dist u v)) = m^2 := by
    apply (div_eq_iff hden.ne').mpr
    nlinarith only [hid]
  change (s * t)^2 * (Real.cosh (dist u v)^2 - 1) /
      (s^2 + t^2 + 2 * s * t * Real.cosh (dist u v)) ≤ _
  rw [he]
  exact (sq_le_sq₀ hm0 (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_nonneg _ _)).mpr hm

/-- The primitive element of the actual full center stabilizer has no larger
displacement at any point. The original element is an actual integer power of it. -/
theorem FuchsianDisc.elliptic_exists_primitive_displacement_dominator
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ D.normalizedGroup) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B),
      IsPrimitive D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) =
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ∧
      (∀ z : ℍ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z ≤
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) := by
  obtain ⟨B, hpB, hB, hfix, _hmax, _hregion⟩ :=
    D.elliptic_exists_primitive_canonical_maximum A hA hAH
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  let p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ((u : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer D.normalizedGroup p
  have hcenter : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) = u :=
    primitive_realSL_elliptic_center_eq B hB u hfix
  have hgen : Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    B) = K := hpB.generates p hfix
  have hAK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ K := by
    apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer _ _ _).mpr
    refine ⟨hAH, ?_⟩
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ u).mpr rfl]
  have hBK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ K := hgen ▸ Subgroup.mem_zpowers _
  let : Finite K := D.normalized_interior_stabilizer_finite u
  let : IsCyclic K := D.normalized_stabilizer_isCyclic p
  have hN : 1 < Nat.card K := by
    have hn : (⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A, hAK⟩ : K) ≠ 1 := by
      intro he
      exact hA.1 (congrArg Subtype.val he)
    let : Nontrivial K := ⟨⟨_, _, hn⟩⟩
    let : Fintype K := Fintype.ofFinite _
    simpa only [Nat.card_eq_fintype_card] using (Fintype.one_lt_card : 1 < Fintype.card K)
  obtain ⟨q, hmodel⟩ := primitive_finite_cyclic_full_root_model K (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) hBK hB.1
  have htraceA := primitive_realSL_trace_bound_of_full_root_model K hN q hmodel A hAK hA.1
  have htraceB := ((primitive_iff_of_elliptic hB).mp hpB).2.2.squaredTrace_order
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace] at htraceB
  have hcard : Nat.card K = orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) := by rw [← hgen, Nat.card_zpowers]
  rw [hcard] at htraceA
  have htrace : (Matrix.trace A.val)^2 ≤ (Matrix.trace B.val)^2 := by
    rw [Complex.ofReal_inj] at htraceB
    rwa [htraceB]
  have hs : Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB / 2) ≤
      Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2) := by
    have hrotA := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A hA).2.2.2
    have hrotB := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec B hB).2.2.2
    have hθ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo A hA
    have hφ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo B hB
    have hsinA := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have hsinB := Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
    nlinarith only [htrace, hrotA, hrotB, hsinA, hsinB,
      Real.sin_sq_add_cos_sq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2),
      Real.sin_sq_add_cos_sq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB / 2)]
  refine ⟨B, hB, hpB, hcenter, ?_, hgen.symm ▸ hAK⟩
  intro z
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_actual_angle_radial B hB,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_actual_angle_radial A hA, hcenter]
  exact mul_le_mul_of_nonneg_right hs (Real.sinh_nonneg_iff.mpr dist_nonneg)

/-- For the literal original generated group, full-stabilizer primitive replacement
preserves that entire group and can only decrease the genuine displacement infimum. -/
theorem fuchsian_elliptic_pair_primitive_reduction
    (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : FuchsianDisc (Subgroup.closure ({f, g} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) (hg :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) :
    ∃ C E : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      IsPrimitive D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) ∧
      IsPrimitive D.normalizedGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E) ∧
      Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) =
        D.normalizedGroup ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry E) ≤
        _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM D ⟨f, Subgroup.subset_closure (by simp)⟩
          ⟨g, Subgroup.subset_closure (by simp)⟩ := by
  let H := Subgroup.closure ({f, g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  let F : H := ⟨f, Subgroup.subset_closure (by simp)⟩
  let G : H := ⟨g, Subgroup.subset_closure (by simp)⟩
  let A := D.normalizedLift F
  let B := D.normalizedLift G
  let q := D.halfPlaneNormalizer
  have hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation f q).mpr hf
  have hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) := by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation g q).mpr hg
  have hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ D.normalizedGroup := by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨f,
      F.property, rfl⟩
  have hBm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ D.normalizedGroup := by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨g,
      G.property, rfl⟩
  obtain ⟨C, hC, hpC, _hc, hCdisp, hAC⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.elliptic_exists_primitive_displacement_dominator D A hA hAm
  obtain ⟨E, hE, hpE, _he, hEdisp, hBE⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.elliptic_exists_primitive_displacement_dominator D B hB hBm
  let K := Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E} : Set
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hCK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C ∈ K := Subgroup.subset_closure (by simp)
  have hEK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E ∈ K := Subgroup.subset_closure (by simp)
  have hAK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ K := (Subgroup.zpowers_le.mpr hCK) hAC
  have hBK : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ K := (Subgroup.zpowers_le.mpr hEK) hBE
  have hAB : Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) =
      D.normalizedGroup := by
    exact (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.generated_normalized_pair D F G).symm
  have hK : K = D.normalizedGroup := by
    apply le_antisymm
    · apply (Subgroup.closure_le D.normalizedGroup).mpr
      rintro k (rfl | rfl)
      · exact hpC.mem
      · exact hpE.mem
    · rw [← hAB]
      apply (Subgroup.closure_le K).mpr
      rintro k (rfl | rfl)
      · exact hAK
      · exact hBK
  refine ⟨C, E, hpC, hpE, hC, hE, hK, ?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.displacementM_eq_native]
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_lower_bound _ _ _).mpr
  intro z
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_le
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry C)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry E) z).trans
    (max_le_max (hCdisp z) (hEdisp z))

end LowDimensionalTopology.Geometry.Fuchsian
