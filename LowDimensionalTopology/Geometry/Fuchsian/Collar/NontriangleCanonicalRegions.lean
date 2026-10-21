/- Released under Apache 2.0 license as described in the file LICENSE. -/
module

public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticTriangleSubgroups
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.CanonicalSurfaceRegions
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegion.CanonicalRegionFormulas
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.NonTriangleParabolicGroups
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticParabolicTriangles
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.NonTriangleParabolicDisplacement
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.CanonicalSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleHyperbolicAxisSeparation

/-!
# Nontriangle canonical-region separation

Canonical regions of elliptic or parabolic elements in an invariant disc are
disjoint unless they generate a cyclic subgroup or the ambient group is a
triangle group. This includes half-turn singleton regions and nonprimitive
elements.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane OnePoint MatrixGroups
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

private theorem elliptic_acute_canonical_orientation
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ, (B = A ∨ B = A⁻¹) ∧
      ∃ hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B),
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB / 2 ≤ Real.pi / 2 ∧
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A := by
  by_cases h : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2 ≤ Real.pi / 2
  · exact ⟨A, Or.inl rfl, hA, h, rfl⟩
  · let hi := elliptic_realSL_inverse A hA
    refine ⟨A⁻¹, Or.inr rfl, hi, ?_, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_inverse A⟩
    rw [elliptic_realSL_inverse_angle A hA hi]
    linarith

private theorem elliptic_canonical_radial_bounds
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hacute : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2 ≤ Real.pi / 2)
    (z : ℍ) (hz : z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A) :
    let θ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2
    let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
    Real.sin θ * Real.sinh (dist u z) ≤ Real.cos θ ∧
      Real.sin θ * Real.cosh (dist u z) ≤ 1 ∧
      (Matrix.trace A.val ≠ 0 → Real.sin θ * Real.cosh (dist u z) < 1) := by
  dsimp only
  let θ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle A hA / 2
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
  have hθ : 0 < θ := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo A hA).1
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo A hA).2
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hacute⟩
  change Real.sin θ * Real.sinh (dist u z) ≤ Real.cos θ ∧
    Real.sin θ * Real.cosh (dist u z) ≤ 1 ∧
    (Matrix.trace A.val ≠ 0 → Real.sin θ * Real.cosh (dist u z) < 1)
  by_cases ht : Matrix.trace A.val = 0
  · have hzfix : A • z = z := by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_of_trace_zero A ht, mem_ofPred_eq] using hz
    have hzu : z = u := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ z).mp hzfix
    rw [hzu, dist_self, Real.sinh_zero, mul_zero, Real.cosh_zero, mul_one]
    exact ⟨hc, Real.sin_le_one θ, fun hn => (hn ht).elim⟩
  · have he : |Matrix.trace A.val|/2 = Real.cos θ := by
      have htθ := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle_spec A hA).2.2.2
      change (Matrix.trace A.val)^2 = 4 * Real.cos θ ^ 2 at htθ
      nlinarith [sq_abs (Matrix.trace A.val), abs_nonneg (Matrix.trace A.val)]
    have hdisp : Real.sin θ * Real.sinh (dist u z) < Real.cos θ := by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_of_trace_ne_zero A ht] at hz
      change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z < |Matrix.trace A.val|/2 at hz
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.elliptic_actual_angle_radial A hA, he] at hz
      exact hz
    have hcosh : Real.sin θ * Real.cosh (dist u z) < 1 := by
      have hp : 0 ≤ Real.sin θ * Real.sinh (dist u z) :=
        mul_nonneg hs.le (Real.sinh_nonneg_iff.mpr dist_nonneg)
      have hsq := (sq_lt_sq₀ hp hc).mpr hdisp
      have htrig := Real.sin_sq_add_cos_sq θ
      have hhyper := Real.cosh_sq_sub_sinh_sq (dist u z)
      have hpos : 0 ≤ Real.sin θ * Real.cosh (dist u z) := by positivity
      nlinarith
    exact ⟨hdisp.le, hcosh.le, fun _ => hcosh⟩

/-- The actual elliptic canonical regions in a nontriangle whole group are disjoint
when their genuine centers differ. Half-turn singleton regions are included. -/
theorem HalfPlaneFuchsianGroup.nontriangle_elliptic_canonical_disjoint
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (hnt : ¬ IsMobiusTriangleGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) (hBH :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H)
    (hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B) := by
  obtain ⟨C,hCA,hC,hac,hregC⟩ := elliptic_acute_canonical_orientation A hA
  obtain ⟨E,hEB,hE,hae,hregE⟩ := elliptic_acute_canonical_orientation B hB
  have hCH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C ∈ H := by
    rcases hCA with rfl | rfl
    · exact hAH
    · rw [map_inv]; exact H.inv_mem hAH
  have hEH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E ∈ H := by
    rcases hEB with rfl | rfl
    · exact hBH
    · rw [map_inv]; exact H.inv_mem hBH
  have hcenterC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) := by
    rcases hCA with rfl | rfl
    · rfl
    · exact elliptic_realSL_inverse_center A hA hC
  have hcenterE : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter E ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff E hE.1).mp hE) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) := by
    rcases hEB with rfl | rfl
    · rfl
    · exact elliptic_realSL_inverse_center B hB hE
  have hCE : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter E ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff E hE.1).mp hE) := by
    rwa [hcenterC,hcenterE]
  rw [←hregC,←hregE]
  apply Set.disjoint_left.mpr
  intro z hzC hzE
  let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC)
  let v := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter E ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff E hE.1).mp hE)
  let θ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle C hC / 2
  let φ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle E hE / 2
  have hθ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo C hC
  have hφ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_halfAngle_mem_Ioo E hE
  change θ ∈ Ioo 0 Real.pi at hθ
  change φ ∈ Ioo 0 Real.pi at hφ
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have ht : 0 < Real.sin φ := Real.sin_pos_of_pos_of_lt_pi hφ.1 hφ.2
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1,Real.pi_pos], hac⟩
  have hd : 0 ≤ Real.cos φ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [hφ.1,Real.pi_pos], hae⟩
  have hbC := elliptic_canonical_radial_bounds C hC hac z hzC
  have hbE := elliptic_canonical_radial_bounds E hE hae z hzE
  change Real.sin θ * Real.sinh (dist u z) ≤ Real.cos θ ∧
    Real.sin θ * Real.cosh (dist u z) ≤ 1 ∧
    (Matrix.trace C.val ≠ 0 → Real.sin θ * Real.cosh (dist u z) < 1) at hbC
  change Real.sin φ * Real.sinh (dist v z) ≤ Real.cos φ ∧
    Real.sin φ * Real.cosh (dist v z) ≤ 1 ∧
    (Matrix.trace E.val ≠ 0 → Real.sin φ * Real.cosh (dist v z) < 1) at hbE
  have hnzero : Matrix.trace C.val ≠ 0 ∨ Matrix.trace E.val ≠ 0 := by
    by_contra! h
    have hzu : z = u := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff C _ z).mp
      (by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_of_trace_zero C h.1, mem_ofPred_eq] using hzC)
    have hzv : z = v := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff E _ z).mp
      (by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_of_trace_zero E h.2, mem_ofPred_eq] using hzE)
    exact hCE (hzu.symm.trans hzv)
  have hstrict : (Real.sin θ * Real.cosh (dist u z)) *
      (Real.sin φ * Real.cosh (dist v z)) < 1 := by
    rcases hnzero with h | h
    · have hmul := mul_lt_mul_of_pos_right (hbC.2.2 h)
        (by positivity : 0 < Real.sin φ * Real.cosh (dist v z))
      nlinarith [hbE.2.1]
    · have hmul := mul_lt_mul_of_pos_left (hbE.2.2 h)
        (by positivity : 0 < Real.sin θ * Real.cosh (dist u z))
      nlinarith [hbC.2.1]
  have hsecond : (Real.sin θ * Real.sinh (dist u z)) *
      (Real.sin φ * Real.sinh (dist v z)) ≤ Real.cos θ * Real.cos φ :=
    mul_le_mul hbC.1 hbE.1 (by positivity) hc
  have hdist : Real.cosh (dist u v) ≤ Real.cosh (dist u z + dist v z) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_of_nonneg dist_nonneg,abs_of_nonneg (by positivity)]
    simpa only [dist_comm z v] using dist_triangle u z v
  have hsep := elliptic_pair_separation_of_product_not_elliptic C E hC hE hCE
    (fun hp => hnt (_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_product_forces_triangle P C E hC hE hCH hEH hp hCE))
  change (1 + Real.cos θ * Real.cos φ) / (Real.sin θ * Real.sin φ) ≤
    Real.cosh (dist u v) at hsep
  have hsep' := (div_le_iff₀ (mul_pos hs ht)).mp hsep
  have hmul := mul_le_mul_of_nonneg_left hdist (mul_pos hs ht).le
  rw [Real.cosh_add] at hmul
  nlinarith [hstrict,hsecond]

/-- The parabolic product case for arbitrary actual elliptic elements in a
whole discrete group, with least positive replacements derived internally. -/
theorem HalfPlaneFuchsianGroup.elliptic_parabolic_product_forces_triangle
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) (hBH :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H)
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B)))
    (huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)) :
    IsMobiusTriangleGroup H := by
  obtain ⟨C,hC,hCH,hlC,haC,hcenterC,_hstabC,hpowC,_horderC⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_exists_native_positive_replacement P A hA hAH
  obtain ⟨E,hE,hEH,hlE,haE,hcenterE,_hstabE,hpowE,_horderE⟩ :=
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_exists_native_positive_replacement P B hB hBH
  let δ := Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C)
  let ε := Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius E)
  have hsmall (F : Matrix.SpecialLinearGroup (Fin 2) ℝ)
      (hF : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F)) (hlF : HasLeastEllipticRotation
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F)) :
      Real.pi / orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F) ∈ Ioc 0 (Real.pi / 2) := by
    have hn := least_elliptic_realSL_order_two_le F hF hlF
    have hnR : (2 : ℝ) ≤ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F) := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F) := by linarith
    exact ⟨div_pos Real.pi_pos hn0,
      div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hnR⟩
  have hδ : δ ∈ Ioc 0 (Real.pi / 2) := hsmall C hC hlC
  have hε : ε ∈ Ioc 0 (Real.pi / 2) := hsmall E hE hlE
  have hsδ := elliptic_sin_half_lower_of_trace_bound A hA hδ
    (least_elliptic_nonidentity_power_trace_bound C A hC hlC hA.1 hpowC)
  have hsε := elliptic_sin_half_lower_of_trace_bound B hB hε
    (least_elliptic_nonidentity_power_trace_bound E B hE hlE hB.1 hpowE)
  have hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter E ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff E hE.1).mp hE) := by
    rwa [hcenterC,hcenterE]
  have htr : (Matrix.trace (C*E).val)^2 ≤ 4 :=
    elliptic_primitive_cut_product_trace_le_four A B C E hA hB hC hE hδ hε
      (by rw [haC]; dsimp only [δ]; ring) (by rw [haE]; dsimp only [ε]; ring)
      hsδ hsε (by rw [hcenterC,hcenterE]) hne
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff _ hAB.1).mp hAB).le
  have hCE1 := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_product_ne_one_of_centers_ne C E hC hE hne
  rcases lt_or_eq_of_le htr with hlt | heq
  · exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_product_forces_triangle P C E hC hE hCH hEH
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _ hCE1).mpr hlt) hne
  · have hp : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (C*E)) :=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff _ hCE1).mpr heq
    have ht := positive_elliptic_parabolic_product_isMobiusTriangleGroup
      C E hC hE hlC hlE haC haE hne hp
    apply halfPlane_supergroup_of_triangleGroup_is_triangleGroup P _ _ ht
    apply (Subgroup.closure_le H).mpr
    rintro g (rfl | rfl)
    · exact hCH
    · exact hEH

/-- An actual parabolic/elliptic pair with an elliptic product forces the
entire discrete ambient group to be a triangle group. -/
theorem HalfPlaneFuchsianGroup.parabolic_elliptic_product_forces_triangle
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) (hBH :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H)
    (hAB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B))) :
    IsMobiusTriangleGroup H := by
  let C := (A*B)⁻¹
  have hC : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) := elliptic_realSL_inverse (A*B) hAB
  have hCH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C ∈ H := by
    dsimp only [C]
    rw [map_inv,map_mul]
    exact H.inv_mem (H.mul_mem hAH hBH)
  have hBC : B*C = A⁻¹ := by dsimp only [C]; group
  have hp : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (B*C)) := by
    rw [hBC]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_parabolic_inv A hA
  have huv : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter C ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hC.1).mp hC) := by
    intro he
    let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
    have hBu : B • u = u := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff B _ u).mpr rfl
    have hCu : C • u = u := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff C _ u).mpr he
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_parabolic_no_fixed (B*C) hp u (by rw [mul_smul,hCu,hBu])
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.elliptic_parabolic_product_forces_triangle
    P B C hB hC hBH hCH hp huv

private theorem elliptic_canonical_height_bound
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (z : ℍ) (hz : z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B) :
    2 * |B 1 0| * z.im ≤ 2 + |Matrix.trace B.val| := by
  by_cases ht : Matrix.trace B.val = 0
  · have hzfix : B • z = z := by
      simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_of_trace_zero B
        ht,mem_ofPred_eq] using hz
    have hzu : z = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB) :=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff B _ z).mp hzfix
    have he := elliptic_actual_angle_height B hB
    rw [hzu]
    nlinarith [Real.sin_le_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticRotationAngle B hB /
      2),abs_nonneg (Matrix.trace B.val)]
  · have hc : B 1 0 ≠ 0 := by
      intro hc
      have hd := B.det_coe
      rw [Matrix.det_fin_two,hc,mul_zero,sub_zero] at hd
      have htr := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB
      rw [Matrix.trace_fin_two] at htr
      nlinarith [sq_nonneg (B 0 0 - B 1 1)]
    have hQ := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_mem_quadratic B ht z).mp hz
    have hmul := mul_lt_mul_of_pos_left hQ (abs_pos.mpr hc)
    have hle : B 1 0 * _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic B z ≤
        |B 1 0| * |_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic B z| := by
      rw [←abs_mul]
      exact le_abs_self _
    have hid : 4 * B 1 0 * _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic B z =
        (2 * B 1 0 * z.re + B 1 1 - B 0 0)^2 +
          (2 * B 1 0 * z.im)^2 + 4 - (Matrix.trace B.val)^2 := by
      have hd := B.det_coe
      rw [Matrix.det_fin_two] at hd
      dsimp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalQuadratic]
      rw [Matrix.trace_fin_two]
      nlinarith
    have hcsq : (2 * B 1 0 * z.im)^2 = (2 * |B 1 0| * z.im)^2 := by
      simp only [mul_pow,sq_abs]
    rw [hcsq] at hid
    have hs : |2 * |B 1 0| * z.im - 2| < |Matrix.trace B.val| := by
      apply (sq_lt_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
      rw [sq_abs,sq_abs]
      nlinarith [sq_abs (B 1 0),sq_nonneg (2 * B 1 0 * z.re + B 1 1 - B 0 0)]
    linarith [le_abs_self (2 * |B 1 0| * z.im - 2)]

/-- Overlap with a true parabolic canonical horoball forces a genuinely
elliptic product with one of the two orientations of the elliptic element. -/
private theorem translation_elliptic_canonical_overlap_product
    (t : ℝ) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (z : ℍ) (hzT : z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t))
    (hzB : z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t * B)) ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t * B⁻¹)) := by
  have hy : |t| / 2 < z.im := by simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_translation,mem_ofPred_eq] using hzT
  have hc : B 1 0 ≠ 0 := by
    intro hc
    have hd := B.det_coe
    rw [Matrix.det_fin_two,hc,mul_zero,sub_zero] at hd
    have htr := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB
    rw [Matrix.trace_fin_two] at htr
    nlinarith [sq_nonneg (B 0 0 - B 1 1)]
  have hheight := elliptic_canonical_height_bound B hB z hzB
  have hupper : |t * B 1 0| < 2 + |Matrix.trace B.val| := by
    rw [abs_mul]
    have hh := mul_lt_mul_of_pos_right hy (abs_pos.mpr hc)
    linarith
  have htr : |Matrix.trace B.val| < 2 := by
    have hh := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB
    nlinarith [sq_abs (Matrix.trace B.val),abs_nonneg (Matrix.trace B.val)]
  have hp : Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t * B).val = Matrix.trace B.val + t * B 1 0 := by
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.trace_fin_two,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
    ring
  have hm : Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t * B⁻¹).val = Matrix.trace B.val - t * B 1 0 := by
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.trace_fin_two,
      Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two]
    ring
  have hell (C : Matrix.SpecialLinearGroup (Fin 2) ℝ) (h : |Matrix.trace C.val| < 2) :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) := by
    have hsq : (Matrix.trace C.val)^2 < 4 := by
      nlinarith [sq_abs (Matrix.trace C.val),abs_nonneg (Matrix.trace C.val)]
    have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C ≠ 1 := by
      intro he
      have hh := congrArg _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace he
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace] at hh
      have hone : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace (1 : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) = (4 : ℂ) := by
        have hh := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace (1 :
          Matrix.SpecialLinearGroup (Fin 2) ℝ)
        norm_num [Matrix.trace_fin_two] at hh
        exact hh
      rw [hone] at hh
      have hfour : (Matrix.trace C.val)^2 = 4 := by exact_mod_cast hh
      linarith
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff C hn).mpr hsq
  rcases le_total 0 (Matrix.trace B.val) with ht | ht <;>
    rcases le_total 0 (t * B 1 0) with hc | hc
  · right
    apply hell
    rw [hm]
    simp only [abs_of_nonneg ht,abs_of_nonneg hc] at htr hupper
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  · left
    apply hell
    rw [hp]
    simp only [abs_of_nonneg ht,abs_of_nonpos hc] at htr hupper
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  · left
    apply hell
    rw [hp]
    simp only [abs_of_nonpos ht,abs_of_nonneg hc] at htr hupper
    exact abs_lt.mpr ⟨by linarith,by linarith⟩
  · right
    apply hell
    rw [hm]
    simp only [abs_of_nonpos ht,abs_of_nonpos hc] at htr hupper
    exact abs_lt.mpr ⟨by linarith,by linarith⟩

private theorem canonical_pair_cyclic_of_common_fixed
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hfH : f ∈ H) (hgH : g ∈ H)
    (p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hfp : f.val p = p) (hgp : g.val p = p) :
    IsCyclic (Subgroup.closure ({f,g} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  let _ := P.asFuchsianDisc.stabilizer_isCyclic p
  apply Subgroup.isCyclic_of_le (H' := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H
    p)
  apply (Subgroup.closure_le _).mpr
  rintro k (rfl | rfl)
  · exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p _).mpr ⟨hfH,hfp⟩
  · exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H p _).mpr ⟨hgH,hgp⟩

/-- The original unit-threshold canonical horoballs, rather than the smaller
Jorgensen half-threshold sets, are separated in a nontriangle ambient group. -/
theorem HalfPlaneFuchsianGroup.nontriangle_parabolic_canonical_disjoint
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (hnt : ¬ IsMobiusTriangleGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) (hBH :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H)
    (hn : ¬ ∃ p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val p = p ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val p = p) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B) := by
  let K := Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hKH : K ≤ H := (Subgroup.closure_le H).mpr (by
    rintro k (rfl | rfl)
    · exact hAH
    · exact hBH)
  let Q : HalfPlaneFuchsianGroup K :=
    ⟨fun k => P.preserves ⟨k.val,hKH k.property⟩,
      discreteMobius_subgroup_of_le H K P.discrete hKH⟩
  have hne := parabolic_pair_nonElementary_of_no_common_fixed _ _ hA hn
  have hntK : ¬ IsMobiusTriangleGroup K := fun h => hnt (halfPlane_supergroup_of_triangleGroup_is_triangleGroup P K hKH
    h)
  have htrace := fuchsian_two_parabolic_nontriangle_trace_ge_eighteen
    _ _ Q.asFuchsianDisc hA hB hne hntK
  rw [realSLMobius_commutatorTrace,Complex.ofReal_re] at htrace
  have hP := parabolic_displacementP_of_commutator_trace A B hA
    (le_of_eq ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff B hB.1).mp hB).symm) htrace
  apply Set.disjoint_left.mpr
  intro z hzA hzB
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.canonical_region_parabolic A hA] at hzA
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.canonical_region_parabolic B hB] at hzB
  have hz := hP.trans (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_le
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z)
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z < 1 at hzA
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z < 1 at hzB
  have hm := mul_le_mul_of_nonneg_right hzA.le (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement_nonneg (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z)
  nlinarith

/-- Parabolic and elliptic canonical regions of the entire nontriangle
Fuchsian group are genuinely disjoint, without a primitive hypothesis. -/
theorem HalfPlaneFuchsianGroup.nontriangle_mixed_canonical_disjoint
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (hnt : ¬ IsMobiusTriangleGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) (hBH :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H) :
    Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B) := by
  obtain ⟨q,t,_ht,hnorm⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_normal_form A hA
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) H
  let Q : HalfPlaneFuchsianGroup K := _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.realSLConjugateData P q
  let C := q*B*q⁻¹
  have hC : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C) := native_elliptic_realSL_conjugate B q hB
  have hCH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C ∈ K := by
    simp only [C,map_mul,map_inv]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ H
      _).mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,hBH,rfl⟩
  have hTH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) ∈ K := by
    have hm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹) ∈ K := by
      simp only [map_mul,map_inv]
      exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ H
        _).mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hAH,rfl⟩
    rcases hnorm with h | h
    · rwa [h] at hm
    · rwa [h,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg] at hm
  have hp : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t)) := by
    have hh : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)) := by
      simp only [map_mul,map_inv]
      exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr
        ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q,rfl⟩)).mp hA
    rcases hnorm with h | h
    · rwa [h] at hh
    · rwa [h,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg] at hh
  have hntK : ¬ IsMobiusTriangleGroup K := fun h =>
    hnt (isMobiusTriangleGroup_of_conjugate H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) h)
  apply Set.disjoint_left.mpr
  intro z hzA hzB
  have hzT : q • z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) := by
    have hh := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_conjugation_mem A q z).mpr hzA
    rcases hnorm with h | h
    · rwa [h] at hh
    · rwa [h,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_neg] at hh
  have hzC : q • z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion C :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion_conjugation_mem B q z).mpr hzB
  rcases translation_elliptic_canonical_overlap_product t C hC (q•z) hzT hzC with h | h
  · exact hntK (_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.parabolic_elliptic_product_forces_triangle
      Q (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) C hp hC hTH hCH h)
  · exact hntK (_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.parabolic_elliptic_product_forces_triangle
      Q (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t) C⁻¹ hp (elliptic_realSL_inverse C hC) hTH
      (by rw [map_inv]; exact K.inv_mem hCH) h)

/--
In the literal native half-plane, with the whole ambient
nontriangle condition and the original actual canonical regions.
-/
theorem HalfPlaneFuchsianGroup.canonical_elliptic_parabolic_alternative
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (hnt : ¬ IsMobiusTriangleGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAH : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) (hBH :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)) :
    IsCyclic (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∨
      Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hCanonicalRegion B) := by
  rcases hA with hA | hA <;> rcases hB with hB | hB
  · by_cases hc : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA) =
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter B ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B hB.1).mp hB)
    · left
      let u := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA.1).mp hA)
      apply canonical_pair_cyclic_of_common_fixed P _ _ hAH hBH ((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
      · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ u).mpr rfl]
      · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff B _ u).mpr hc]
    · exact Or.inr (_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nontriangle_elliptic_canonical_disjoint
        P hnt A B hA hB hAH hBH hc)
  · exact Or.inr (_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nontriangle_mixed_canonical_disjoint
      P hnt B A hB hA hBH hAH).symm
  · exact Or.inr (_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nontriangle_mixed_canonical_disjoint
      P hnt A B hA hB hAH hBH)
  · by_cases hc : ∃p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val p=p ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val p=p
    · obtain ⟨p,hp,hq⟩ := hc
      exact Or.inl (canonical_pair_cyclic_of_common_fixed P _ _ hAH hBH p hp hq)
    · exact Or.inr (_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.nontriangle_parabolic_canonical_disjoint
        P hnt A B hA hB hAH hBH hc)

/--
For the original arbitrary Fuchsian disc,
actual group elements and their original physical canonical regions.
-/
theorem nontriangle_elliptic_or_parabolic_pair_cyclic_or_canonicalRegions_disjoint
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (_hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hnt : ¬ IsMobiusTriangleGroup H)
    (g h : H) (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic g.val)
    (hh : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic h.val ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic h.val) :
    IsCyclic (Subgroup.closure ({g.val,h.val} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) ∨
      Disjoint (D.canonicalRegion g) (D.canonicalRegion h) := by
  let q := D.halfPlaneNormalizer
  let A := D.normalizedLift g
  let B := D.normalizedLift h
  let P : HalfPlaneFuchsianGroup D.normalizedGroup :=
    ⟨fun f => D.normalizedGroup_preserves_halfPlane f.val f.property,
      D.normalizedGroup_discrete⟩
  have hmem (k : H) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift k) ∈ D.normalizedGroup := by
    rw [D.normalizedLift_spec]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨k.val,k.property,rfl⟩
  have htypes (k : H) (hk : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic k.val ∨
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic k.val) :
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift k)) ∨
        _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (D.normalizedLift k)) := by
    rw [D.normalizedLift_spec]
    rcases hk with hk | hk
    · exact Or.inl ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation k.val q).mpr hk)
    · exact Or.inr ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp
      hk)
  have hntN : ¬ IsMobiusTriangleGroup D.normalizedGroup := fun ht =>
    hnt (isMobiusTriangleGroup_of_conjugate H q ht)
  rcases _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.canonical_elliptic_parabolic_alternative
      P hntN A B (hmem g) (hmem h) (htypes g hg) (htypes h hh) with hcyc | hdis
  · left
    let K := Subgroup.closure ({g.val,h.val} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    have heq : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K =
        Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) := by
      change (Subgroup.closure ({g.val,h.val} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)).map
        (MulAut.conj q).toMonoidHom = _
      rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation]
      rw [←D.normalizedLift_spec g,←D.normalizedLift_spec h]
    let _ : IsCyclic (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
      K) := heq ▸ hcyc
    let e := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugateEquivalence q K
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  · right
    apply Set.disjoint_left.mpr
    intro x hxg hxh
    have hxA : q.val x ∈ nativeCanonicalSphere A := by
      rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_normalized_image D g]
      exact mem_image_of_mem q.val hxg
    have hxB : q.val x ∈ nativeCanonicalSphere B := by
      rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.canonicalRegion_normalized_image D h]
      exact mem_image_of_mem q.val hxh
    obtain ⟨u,hu,heqU⟩ := hxA
    obtain ⟨v,hv,heqV⟩ := hxB
    have huv : u = v := _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective (heqU.trans
      heqV.symm)
    exact Set.disjoint_left.mp hdis hu (huv ▸ hv)

end LowDimensionalTopology.Geometry.Fuchsian
