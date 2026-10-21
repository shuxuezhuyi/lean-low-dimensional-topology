/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Geodesic.SideNormalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ReflectionProductTraces
public import LowDimensionalTopology.Geometry.Polygon.Quadrilateral.SaccheriQuadrilaterals
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.HalfPlaneLorentzReflections
public import LowDimensionalTopology.Geometry.Polygon.Pentagon.PentagonNormals
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A prescribed actual axis perpendicular gives the genuine half-translation segment
and reflection factor, without supplying the half-length identity as a hypothesis. -/
theorem hyperbolic_perpendicular_reflection_half_length
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠
      1)
    (htA : 4 < (Matrix.trace A.val)^2) (N : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (u : ℍ)
    (hu : N.OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA) u) :
    ∃ (K : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (v :
      ℍ), K.OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA) v ∧
      (∀ z : ℍ, A • z = K.reflection (N.reflection z)) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) = 2 * dist u v := by
  obtain ⟨K, ⟨hK, he⟩,
    _⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_hyperbolic_reflection_factor A hA htA N ⟨u, hu⟩
  obtain ⟨v, hv⟩ := hK
  have huv : u ≠ v := by
    intro huv
    have hfix : A • u = u := by
      rw [congrFun he u, Function.comp_apply, (N.reflection_fixed_iff u).mpr hu.1]
      exact (K.reflection_fixed_iff u).mpr (huv.symm ▸ hv.1)
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_hyperbolic_no_fixed A htA u hfix
  have hmid := K.reflection_perpendicular_midpoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A
    hA htA) v u hv hu.2.1 huv
  have hlen := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translation_minimum A hA htA u).mpr hu.2.1
  rw [congrFun he u, Function.comp_apply, (N.reflection_fixed_iff u).mpr hu.1] at hlen
  exact ⟨K, v, hv, congrFun he, hlen.symm.trans hmid.2⟩

/-- The source disjoint-axis figure is constructed using actual common perpendiculars,
actual mirror factors, and genuine metric half-translation lengths. -/
theorem disjoint_hyperbolic_reflection_frame
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ≠ 1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    (hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) :
    ∃ (N K R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (u v a b : ℍ),
      N.OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA) u ∧
      N.OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) v ∧
      K.OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA) a ∧
      R.OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) b ∧
      (∀ z : ℍ, A • z = K.reflection (N.reflection z)) ∧
      (∀ z : ℍ, B • z = R.reflection (N.reflection z)) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) = 2 * dist u a ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) = 2 * dist v b ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
        htA).lineDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) = dist u v ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL R K) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B * (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)⁻¹ := by
  obtain ⟨N, u, v, hu, hv, hdist, _⟩ :=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
      htA).exists_commonOrthogonal_minimum (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB
      htB) hd
  have hu' : N.OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA) u :=
    ⟨hu.2.1, hu.1, by rw [real_inner_comm]; exact hu.2.2⟩
  have hv' : N.OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) v :=
    ⟨hv.2.1, hv.1, by rw [real_inner_comm]; exact hv.2.2⟩
  obtain ⟨K, a, ha, hAf, hAlen⟩ := hyperbolic_perpendicular_reflection_half_length A hA htA N u hu'
  obtain ⟨R, b, hb, hBf, hBlen⟩ := hyperbolic_perpendicular_reflection_half_length B hB htB N v hv'
  refine ⟨N, K, R, u, v, a, b, hu', hv', ha, hb, hAf, hBf, hAlen, hBlen, hdist, ?_⟩
  rw [← map_inv, ← map_mul]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_of_native_action
  intro z
  have hAi : A⁻¹ • z = N.reflection (K.reflection z) := by
    apply MulAction.injective A
    change A • (A⁻¹ • z) = A • (N.reflection (K.reflection z))
    rw [smul_inv_smul, hAf, N.reflection_involutive, K.reflection_involutive]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action, mul_smul, hAi, hBf,
    N.reflection_involutive]


/-- The signed actual mirror coordinate changes sign under its genuine reflection. -/
theorem _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalTimeAt_own_reflection (N :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (z : ℍ) :
    N.normalTimeAt (N.reflection z) = -N.normalTimeAt z := by
  have hunit := N.incenterNormal_lorentz_unit
  have hself : N.normalPairing N = 1 := by
    change inner ℝ N.incenterNormal N.incenterNormal - N.incenterOffset * N.incenterOffset = 1
    rw [real_inner_self_eq_norm_sq]
    nlinarith only [hunit]
  rw [N.normalTimeAt_reflection N z, hself]
  ring

/-- Reversing a hyperbolic factor reflects its outer foot across the common mirror.
All lines and actions are genuine native reflections. -/
theorem perpendicular_reflection_inverse_factor
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (M N R :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (v b : ℍ)
    (hv : N.OrthogonalAt M v) (hb : R.OrthogonalAt M b)
    (hB : ∀ z : ℍ, B • z = R.reflection (N.reflection z)) :
    ∃ R' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine, R'.OrthogonalAt M (N.reflection b) ∧
      (∀ z : ℍ, B⁻¹ • z = R'.reflection (N.reflection z)) ∧
      dist v (N.reflection b) = dist v b ∧
      N.normalTimeAt (N.reflection b) = -N.normalTimeAt b := by
  let R' := R.realGLMap N.reflectionMatrix
  have hRimage : N.reflection '' R.carrier = R'.carrier := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    congr 1
    funext z
    exact (N.reflectionMatrix_action z).symm
  have hMimage := N.reflection_image_of_orthogonalAt M v hv
  have horth := R.orthogonalAt_isometry_image M R' M N.reflection
    N.reflection_isometry hRimage hMimage hb
  refine ⟨R', horth, ?_, ?_, _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.normalTimeAt_own_reflection
    N b⟩
  · intro z
    have hBi : B⁻¹ • z = N.reflection (R.reflection z) := by
      apply MulAction.injective B
      change B • (B⁻¹ • z) = B • (N.reflection (R.reflection z))
      rw [smul_inv_smul, hB, N.reflection_involutive, R.reflection_involutive]
    have hi : N.reflectionMatrix⁻¹ • N.reflection z = z := by
      rw [← N.reflectionMatrix_action, inv_smul_smul]
    have hconj := R.reflection_realGL_conjugation N.reflectionMatrix (N.reflection z)
    rw [hi, N.reflectionMatrix_action] at hconj
    exact hBi.trans hconj
  · simpa only [(N.reflection_fixed_iff v).mpr hv.1] using N.reflection_isometry.dist_eq v b

/-- The two outer feet can be placed on the same actual side of the common mirror
by replacing only the second group element with its inverse. -/
theorem perpendicular_reflection_same_side_choice
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (M N R :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (v a b : ℍ)
    (hv : N.OrthogonalAt M v) (hb : R.OrthogonalAt M b)
    (haN : a ∉ N.carrier) (hbN : b ∉ N.carrier)
    (hB : ∀ z : ℍ, B • z = R.reflection (N.reflection z)) :
    ∃ (B' : Matrix.SpecialLinearGroup (Fin 2) ℝ) (R' :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (b' : ℍ),
      (B' = B ∨ B' = B⁻¹) ∧ R'.OrthogonalAt M b' ∧
      (∀ z : ℍ, B' • z = R'.reflection (N.reflection z)) ∧
      dist v b' = dist v b ∧ 0 < N.normalTimeAt a * N.normalTimeAt b' := by
  have ha0 : N.normalTimeAt a ≠ 0 := fun he => haN ((N.normalTimeAt_eq_zero_iff a).mp he)
  have hb0 : N.normalTimeAt b ≠ 0 := fun he => hbN ((N.normalTimeAt_eq_zero_iff b).mp he)
  by_cases hsame : 0 < N.normalTimeAt a * N.normalTimeAt b
  · exact ⟨B, R, b, Or.inl rfl, hb, hB, rfl, hsame⟩
  · obtain ⟨R', hb', hBi, hdist, htime⟩ :=
      perpendicular_reflection_inverse_factor B M N R v b hv hb hB
    refine ⟨B⁻¹, R', N.reflection b, Or.inr rfl, hb', hBi, hdist, ?_⟩
    rw [htime, mul_neg]
    exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hsame) (mul_ne_zero ha0 hb0))


/-- The genuine disjoint-axis reflection frame can be oriented on one side of the
common perpendicular by reversing at most the second actual group element. -/
theorem disjoint_hyperbolic_same_side_reflection_frame
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ≠ 1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    (hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) :
    ∃ (B' : Matrix.SpecialLinearGroup (Fin 2) ℝ) (N K R :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (u v a b : ℍ),
      (B' = B ∨ B' = B⁻¹) ∧
      N.OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA) u ∧
      N.OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) v ∧
      K.OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA) a ∧
      R.OrthogonalAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) b ∧
      (∀ z : ℍ, A • z = K.reflection (N.reflection z)) ∧
      (∀ z : ℍ, B' • z = R.reflection (N.reflection z)) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) = 2 * dist u a ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) = 2 * dist v b ∧
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
        htA).lineDist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) = dist u v ∧
      0 < N.normalTimeAt a * N.normalTimeAt b ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL R K) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B' * (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)⁻¹ := by
  obtain ⟨N, K, R, u, v, a, b, hu, hv, ha, hb, hAf, hBf, hAlen, hBlen, hdist, _⟩ :=
    disjoint_hyperbolic_reflection_frame A B hA hB htA htB hd
  have hane : a ≠ u := by
    intro he
    rw [he, dist_self, mul_zero] at hAlen
    linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos A hA htA]
  have hbne : b ≠ v := by
    intro he
    rw [he, dist_self, mul_zero] at hBlen
    linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos B hB htB]
  have haN : a ∉ N.carrier := by
    intro haN
    exact N.reflection_ne_of_perpendicular (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
      htA) u a hu ha.2.1 hane
      ((N.reflection_fixed_iff a).mpr haN)
  have hbN : b ∉ N.carrier := by
    intro hbN
    exact N.reflection_ne_of_perpendicular (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB
      htB) v b hv hb.2.1 hbne
      ((N.reflection_fixed_iff b).mpr hbN)
  obtain ⟨B', R', b', hB', hb', hBf', hbdist, hsame⟩ :=
    perpendicular_reflection_same_side_choice B (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB
      htB) N R v a b hv hb haN hbN hBf
  refine ⟨B', N, K, R', u, v, a, b', hB', hu, hv, ha, hb', hAf, hBf', hAlen,
    hBlen.trans (by rw [hbdist]), hdist, hsame, ?_⟩
  rw [← map_inv, ← map_mul]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_of_native_action
  intro z
  have hAi : A⁻¹ • z = N.reflection (K.reflection z) := by
    apply MulAction.injective A
    change A • (A⁻¹ • z) = A • (N.reflection (K.reflection z))
    rw [smul_inv_smul, hAf, N.reflection_involutive, K.reflection_involutive]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL_action, mul_smul, hAi, hBf',
    N.reflection_involutive]

/-- The source disjoint-axis length expression is the actual inward signed pairing
of two real reflection factors. No angle or separation bound is assumed. -/
theorem disjoint_hyperbolic_signed_pairing_formula
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ≠ 1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    (hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) :
    ∃ (B' : Matrix.SpecialLinearGroup (Fin 2) ℝ) (K R :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) (u v : ℍ),
      (B' = B ∨ B' = B⁻¹) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.reflectionProductSL R K) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B' * (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)⁻¹ ∧
      K.inwardNormalSign u * R.inwardNormalSign v * K.normalPairing R =
        Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) / 2) *
            Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
              (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) / 2) -
          Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
            (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) / 2) *
            Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).lineDist
              (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) *
            Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) / 2) := by
  obtain ⟨B', N, K, R, u, v, a, b, hB', hu, hv, ha, hb, _hAf, _hBf, hAlen, hBlen,
    hdist, hsame, hprod⟩ := disjoint_hyperbolic_same_side_reflection_frame A B hA hB htA htB hd
  have ha' : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).OrthogonalAt K a :=
    ⟨ha.2.1, ha.1, by rw [real_inner_comm]; exact ha.2.2⟩
  have hb' : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).OrthogonalAt R b :=
    ⟨hb.2.1, hb.1, by rw [real_inner_comm]; exact hb.2.2⟩
  have hua : u ≠ a := by
    intro he
    rw [he, dist_self, mul_zero] at hAlen
    linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos A hA htA]
  have hvb : v ≠ b := by
    intro he
    rw [he, dist_self, mul_zero] at hBlen
    linarith [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos B hB htB]
  have he := N.four_right_chain_inward_pairing (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
    htA)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) K R u a v b hu ha' hv hb' hua hvb hsame
  have hAhalf : dist u a = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) / 2 := by linarith only [hAlen]
  have hBhalf : dist v b = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) / 2 := by linarith only [hBlen]
  rw [hAhalf, hBhalf, ← hdist] at he
  exact ⟨B', K, R, u, v, hB', hprod, he⟩

end LowDimensionalTopology.Geometry.Fuchsian
