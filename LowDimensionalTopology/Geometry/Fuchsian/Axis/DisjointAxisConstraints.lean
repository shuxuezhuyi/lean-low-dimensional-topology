/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.TranslatedSubsets
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.AxisTranslateLocalFiniteness
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.HyperbolicCollarSeparation
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology Pointwise UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Removing one genuine translated subset leaves a locally finite closed family.
Group labels repeated by a stabilizer are not counted as distinct subsets. -/
theorem translated_compactCore_family_isClosed
    {G X : Type*} [Group G] [MetricSpace X] [ProperSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X]
    (S C L : Set X) (K : Subgroup G) (hS : IsClosed S) (hC : IsCompact C)
    (hstable : ∀ k : K, (k.val • ·) '' S = S)
    (hcover : ∀ x ∈ S, ∃ k : K, ∃ c ∈ C, k.val • c = x) :
    IsClosed (⋃ T : {T : Set X | T ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.translatedSubsetFamily (G := G) S ∧ T ≠ L}, T.val) := by
  let I := {T : Set X | T ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.translatedSubsetFamily (G := G)
    S ∧ T ≠ L}
  have hlocal : LocallyFinite (fun T : I => T.val) := by
    intro x
    refine ⟨Metric.closedBall x 1, Metric.closedBall_mem_nhds x zero_lt_one, ?_⟩
    have hf := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.finite_translated_subsets_meeting_compact S C (Metric.closedBall x 1) K
      hC (isCompact_closedBall x 1) hstable hcover
    exact (hf.preimage Subtype.val_injective.injOn).subset (fun T hT => ⟨T.property.1, hT⟩)
  apply hlocal.isClosed_iUnion
  intro T
  obtain ⟨g, hg⟩ := T.property.1
  rw [hg]
  exact isClosedMap_smul g S hS

/-- Two genuine compact cyclic cores give a closest distinct translated pair of points.
No simplicity or noncrossing assumption on either family is required. -/
theorem compactCore_pair_minimizing_translates
    {G X : Type*} [Group G] [MetricSpace X] [ProperSpace X] [MulAction G X]
    [ContinuousConstSMul G X] [ProperlyDiscontinuousSMul G X] [IsIsometricSMul G X]
    (L S C D : Set X) (K J : Subgroup G) (hS : IsClosed S) (hSn : S.Nonempty)
    (hC : IsCompact C) (hCL : C ⊆ L) (hCn : C.Nonempty) (hD : IsCompact D)
    (hK : ∀ k : K, (k.val • ·) '' L = L)
    (hLcover : ∀ x ∈ L, ∃ k : K, ∃ c ∈ C, k.val • c = x)
    (hJ : ∀ k : J, (k.val • ·) '' S = S)
    (hScover : ∀ x ∈ S, ∃ k : J, ∃ c ∈ D, k.val • c = x)
    (hSL : S ≠ L) :
    ∃ T ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.translatedSubsetFamily (G := G) S, T ≠ L ∧
      ∃ x ∈ L, ∃ y ∈ T,
        ∀ U ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.translatedSubsetFamily (G := G) S, U ≠ L →
          ∀ p ∈ L, ∀ q ∈ U, dist x y ≤ dist p q := by
  let I := {T : Set X | T ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.translatedSubsetFamily (G := G)
    S ∧ T ≠ L}
  let W : Set X := ⋃ T : I, T.val
  have hWclosed : IsClosed W := translated_compactCore_family_isClosed
    S D L J hS hD hJ hScover
  have hSW : S ⊆ W := by
    intro x hx
    apply mem_iUnion.mpr
    exact ⟨⟨S, ⟨1, by simp⟩, hSL⟩, hx⟩
  have hWn : W.Nonempty := hSn.mono hSW
  obtain ⟨x, hxC, hmin⟩ := hC.exists_isMinOn hCn (Metric.continuous_infDist_pt W).continuousOn
  obtain ⟨y, hyW, hxy⟩ := hWclosed.exists_infDist_eq_dist hWn x
  obtain ⟨T, hyT⟩ := mem_iUnion.mp hyW
  refine ⟨T.val, T.property.1, T.property.2, x, hCL hxC, y, hyT, ?_⟩
  intro U hU hUL p hpL q hqU
  obtain ⟨k, c, hcC, hcp⟩ := hLcover p hpL
  let V : Set X := (k.val⁻¹ • ·) '' U
  have hV : V ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.translatedSubsetFamily (G := G) S := by
    obtain ⟨g, rfl⟩ := hU
    refine ⟨k.val⁻¹ * g, ?_⟩
    dsimp only [V]
    rw [image_image]
    congr 1
    funext z
    exact (mul_smul k.val⁻¹ g z).symm
  have hVL : V ≠ L := by
    intro he
    apply hUL
    have hh := congrArg (Set.image (k.val • ·)) he
    rw [show (k.val • ·) '' V = U by
      dsimp only [V]
      rw [image_image]
      simp only [smul_inv_smul]
      exact Set.image_id U] at hh
    rwa [hK k] at hh
  have hqV : k.val⁻¹ • q ∈ V := mem_image_of_mem _ hqU
  have hqW : k.val⁻¹ • q ∈ W := mem_iUnion.mpr ⟨⟨V, hV, hVL⟩, hqV⟩
  have hdist : dist c (k.val⁻¹ • q) = dist p q := by
    rw [← hcp]
    simpa only [smul_inv_smul] using ((isometry_smul X k.val).dist_eq c (k.val⁻¹ • q)).symm
  calc
    dist x y = Metric.infDist x W := hxy.symm
    _ ≤ Metric.infDist c W := hmin hcC
    _ ≤ dist c (k.val⁻¹ • q) := Metric.infDist_le_dist_of_mem hqW
    _ = dist p q := hdist

/-- A nearest distinct genuine translated hyperbolic axis exists, even when either
closed geodesic has self intersections. The minimum uses actual compact cyclic cores. -/
theorem HalfPlaneFuchsianGroup.exists_closest_distinct_hyperbolic_axis_pair
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ≠ 1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    (hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA ≠
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) :
    ∃ C : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C ∈ H ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA ≠
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB
          htB).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ C) ∧
      ∀ D : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D ∈ H →
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA ≠
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB
            htB).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ D) →
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).lineDist
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).realGLMap
            (Matrix.SpecialLinearGroup.mapGL ℝ C)) ≤
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).lineDist
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ D)) := by
  let disjointAxisPairAction := P.nativeAction
  let disjointAxisPairProper := P.native_properlyDiscontinuous
  let disjointAxisPairIsometric : IsIsometricSMul H ℍ := ⟨fun g => (P.nativeHom g).isometry⟩
  let L := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA
  let M := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB
  obtain ⟨C, hC, hCL, hK, hLcover⟩ := P.hyperbolic_axis_compact_core A hAm hA htA
  obtain ⟨D, hD, _hDM, hJ, hMcover⟩ := P.hyperbolic_axis_compact_core B hBm hB htB
  obtain ⟨p, _q, hpL, _hq, _hpq⟩ := L.exists_two_points
  obtain ⟨_k, c, hcC, _hcp⟩ := hLcover p hpL
  obtain ⟨m, _n, hmM, _hn, _hmn⟩ := M.exists_two_points
  have hML : M.carrier ≠ L.carrier := fun he => hne (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective he).symm
  obtain ⟨T, hT, hTne, x, hxL, y, hyT, hmin⟩ := compactCore_pair_minimizing_translates
    L.carrier M.carrier C D _ _ M.isClosed_carrier ⟨m, hmM⟩ hC hCL ⟨c, hcC⟩ hD
    hK hLcover hJ hMcover hML
  obtain ⟨g, hTg⟩ := hT
  obtain ⟨Q, hQ⟩ := mobius_preserves_halfPlane_exists_SL g.val (P.preserves g)
  have himage (g : H) (Q : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hQ :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius Q = g.val) :
      (M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ Q)).carrier = (g • ·) '' M.carrier := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    congr 1
    funext z
    exact (P.nativeAction_realSL g Q hQ z).symm
  have hMT : (M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ Q)).carrier = T :=
    (himage g Q hQ).trans hTg.symm
  have hQne : L ≠ M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ Q) := by
    intro he
    apply hTne
    rw [← hMT, ← he]
  refine ⟨Q, hQ ▸ g.property, hQne, ?_⟩
  intro R hR hRne
  let gR : H := ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius R, hR⟩
  have hMR : (M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ R)).carrier =
      (gR • ·) '' M.carrier := himage gR R rfl
  have hURne : (gR • ·) '' M.carrier ≠ L.carrier := by
    intro he
    apply hRne
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective ((hMR.trans he).symm)
  have hxy : L.lineDist (M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ Q)) ≤ dist x y :=
    L.lineDist_le_dist _ hxL (hMT.symm ▸ hyT)
  apply hxy.trans
  apply le_csInf (L.pairDistances_nonempty (M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ R)))
  rintro d ⟨u, hu, v, hv, rfl⟩
  exact hmin _ ⟨gR, rfl⟩ hURne u hu v (hMR ▸ hv)

/-- The source cross-family condition only forbids intersections between the two
translated families; it imposes no self-family simplicity hypothesis. -/
def HyperbolicAxisFamiliesNoncrossing (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (L M : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine) : Prop :=
  ∀ C : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C ∈ H →
    L = M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ C) ∨
      Disjoint L.carrier (M.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ C)).carrier

/-- Discreteness excludes asymptotic distinct hyperbolic axes, so the genuine
cross-family condition gives the full disjoint-line geometry at every distinct image. -/
theorem HalfPlaneFuchsianGroup.noncrossing_axis_image_hDisjoint
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : HalfPlaneFuchsianGroup H)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ≠ 1)
    (htA : 4 < (Matrix.trace A.val)^2) (htB : 4 < (Matrix.trace B.val)^2)
    (hno : HyperbolicAxisFamiliesNoncrossing H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
      htA) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB))
    (C : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C ∈
      H)
    (hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA ≠
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB
        htB).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ C)) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).HDisjoint
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ C)) := by
  have he := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation B C hB htB
  have hCB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (C * B * C⁻¹) ∈ H := by
    rw [map_mul, map_mul, map_inv]
    exact H.mul_mem (H.mul_mem hC hBm) (H.inv_mem hC)
  refine ⟨hne, disjoint_left.mpr ?_, (hno C hC).resolve_left hne⟩
  intro p hpA hpB
  rw [← he] at hpB
  have haxes := _root_.LowDimensionalTopology.Geometry.Fuchsian.discrete_realSL_hyperbolic_axes_eq_of_shared_endpoint H P.discrete
    A (C * B * C⁻¹) hAm hCB hA (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation B C hB) htA
    (by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]) p hpA hpB
  exact hne (haxes.trans he)

/-- The exact numerical reduction for equal-translation conjugate axes. -/
theorem equal_length_weak_collar_reduction (a d : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hgap : Real.cosh a ^ 2 - (1 : ℝ) / 2 ≤ Real.sinh a ^ 2 * Real.cosh d) :
    (1 : ℝ) / 2 ≤ Real.sinh a * Real.sinh (d / 2) := by
  have hid := Real.cosh_sq_sub_sinh_sq a
  have hdbl := Real.cosh_two_mul (d / 2)
  rw [show 2 * (d / 2) = d by ring] at hdbl
  have htrig := Real.cosh_sq_sub_sinh_sq (d / 2)
  have hnonneg : 0 ≤ Real.sinh a * Real.sinh (d / 2) :=
    mul_nonneg (Real.sinh_nonneg_iff.mpr ha) (Real.sinh_nonneg_iff.mpr (by linarith only [hd]))
  nlinarith only [hgap, hid, hdbl, htrig, hnonneg]

/-- The same original equal-length reduction gives the stronger elliptic-free constant. -/
theorem equal_length_strong_collar_reduction (a d : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d)
    (hgap : Real.cosh a ^ 2 + 1 ≤ Real.sinh a ^ 2 * Real.cosh d) :
    1 ≤ Real.sinh a * Real.sinh (d / 2) := by
  have hid := Real.cosh_sq_sub_sinh_sq a
  have hdbl := Real.cosh_two_mul (d / 2)
  rw [show 2 * (d / 2) = d by ring] at hdbl
  have htrig := Real.cosh_sq_sub_sinh_sq (d / 2)
  have hnonneg : 0 ≤ Real.sinh a * Real.sinh (d / 2) :=
    mul_nonneg (Real.sinh_nonneg_iff.mpr ha) (Real.sinh_nonneg_iff.mpr (by linarith only [hd]))
  nlinarith only [hgap, hid, hdbl, htrig, hnonneg]

end LowDimensionalTopology.Geometry.Fuchsian
