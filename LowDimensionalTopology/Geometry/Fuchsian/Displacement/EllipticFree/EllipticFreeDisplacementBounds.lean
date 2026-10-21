/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.EllipticFree.EllipticFreeParabolicBound
public import LowDimensionalTopology.Geometry.Fuchsian.CanonicalRegion.PrimitiveCanonicalRegions
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.EllipticFree.EllipticFreeSimpleHyperbolicBounds
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.DisjointHyperbolicDirections
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A genuine real half-turn interchanges the logarithmic diagonal direction. -/
theorem hLogDilationSL_rotation_conjugation (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL 0 1 (by norm_num)*hLogDilationSL t*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL 0 1 (by norm_num))⁻¹=
      hLogDilationSL (-t) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL,hLogDilationSL,Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two]

/-- Every original actual hyperbolic map has a constructed positive logarithmic diagonal chart. -/
theorem realSLMobius_hyperbolic_positive_log_normal_form
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    ∃q : Matrix.SpecialLinearGroup (Fin 2) ℝ,∃t : ℝ,0<t ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (hLogDilationSL t) := by
  obtain ⟨q,t,ht0,hq⟩:=realSLMobius_hyperbolic_log_normal_form A hA
  by_cases ht : 0<t
  · exact ⟨q,t,ht,hq⟩
  · let S:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL 0 1 (by norm_num)
    have ht' : 0< -t:=by linarith [lt_of_le_of_ne (not_lt.mp ht) ht0]
    refine ⟨S*q,-t,ht',?_⟩
    have he : (S*q)*A*(S*q)⁻¹=S*(q*A*q⁻¹)*S⁻¹:=by group
    rw [he,map_mul,map_mul,map_inv,hq,←map_inv,←map_mul,←map_mul]
    rw [hLogDilationSL_rotation_conjugation]

/-- Equality of actual geometric projections gives equality of the whole native isometry. -/
theorem hSLIsometry_eq_of_realSLMobius_eq
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B := by
  rcases (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_iff_sign A B).mp he with rfl | rfl
  · rfl
  · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_neg A).symm

/-- Equality of actual geometric projections gives the same complete actual hyperbolic axis. -/
theorem hHyperbolicAxis_eq_of_realSLMobius_eq
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.idealEndpoints_injective
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints,he]

/-- The sharp simple/disjoint branch for the original actual pair, with its diagonal chart constructed in the proof. -/
theorem hEllipticFree_simple_disjoint_displacement_bound
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hG :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (hs : IsSimple G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hdis : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) (z : ℍ) :
    1≤Real.sinh (dist z (A • z)/2)*Real.sinh (dist z (B • z)/2) := by
  have hAH:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hA).mpr htA
  obtain ⟨q,t,ht,he⟩:=realSLMobius_hyperbolic_positive_log_normal_form A hAH
  let D:=hLogDilationSL t
  let C:=q*B*q⁻¹
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) G
  have hK : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree K:=hG.conjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
  have hQH : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)) := by
    simpa only [map_mul,map_inv] using
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)).mpr hAH
  have hDH : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D):=he ▸ hQH
  have hD : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D≠1:=hDH.1.1
  have htD : 4<(Matrix.trace D.val)^2:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff D
    hD).mp hDH
  have hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C≠1:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation B q hB
  have htC : 4<(Matrix.trace C.val)^2 := by dsimp only [C];rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]
  have hA' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)≠1:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation A q hA
  have htA' : 4<(Matrix.trace (q*A*q⁻¹).val)^2 := by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]
  have hAD:=hHyperbolicAxis_eq_of_realSLMobius_eq (q*A*q⁻¹) D hA' hD htA' htD he
  have hDaxis:=hLogDilationSL_hyperbolic_axis t ht hD htD
  have hImageA : (q • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis D hD htD).carrier := by
    rw [←hAD,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation A q hA
      htA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl
  have hImageB : (q • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC).carrier := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation B q hB
      htB,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl
  have hqpos : 0<(Matrix.SpecialLinearGroup.mapGL ℝ q).val.det := by
    change 0<q.val.det
    rw [q.det_coe]
    norm_num
  have hdis':=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
    htA).hDisjoint_realGL_image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis D hD
      htD) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis C hC htC)
    (Matrix.SpecialLinearGroup.mapGL ℝ q) hqpos hImageA hImageB hdis
  rw [hDaxis] at hdis'
  have hsQ : IsSimple K (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*A*q⁻¹)) := by
    simpa only [map_mul,map_inv] using (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_conjugation G
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)).mpr hs
  have hsD : IsSimple K (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D):=he ▸ hsQ
  have hCm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C∈K := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (q*B*q⁻¹)∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q) G
    rw [map_mul,map_mul,map_inv]
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff _ _
      _).mpr ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,hBm,rfl⟩
  have hPairQ:=hPair.conjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation] at hPairQ
  have hqa : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D := by
    simpa only [map_mul,map_inv] using he
  have hqb : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius q)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C := by
    simp only [C,map_mul,map_inv]
  have hPairK : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius D,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius C}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
    simpa only [hqa,hqb] using hPairQ
  have hbnd:=hEllipticFree_simple_disjoint_logDilation_displacement_bound K hK t ht hD htD C hC htC hsD hCm hPairK hdis' (q • z)
  have hact (w : ℍ) : D • w=(q*A*q⁻¹) • w :=
    (congrArg (fun F : ℍ ≃ᵢ ℍ=>F w) (hSLIsometry_eq_of_realSLMobius_eq _ _ he)).symm
  rw [hact] at hbnd
  simpa only [C,mul_smul,inv_smul_smul,(isometry_smul ℍ q).dist_eq] using hbnd

/-- The exact sharp bound for every original non-elementary hyperbolic pair, with all actual axis cases exhausted. -/
theorem hEllipticFree_hyperbolic_displacement_bound
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hG :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G)
    (hLift : ∀g∈G,∃A : Matrix.SpecialLinearGroup (Fin 2)
      ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=g)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈G) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (hB :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA : 4<(Matrix.trace A.val)^2) (htB : 4<(Matrix.trace B.val)^2)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (z : ℍ) : 1≤Real.sinh (dist z (A • z)/2)*Real.sinh (dist z (B • z)/2) := by
  let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA
  let M:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB
  have hends : Disjoint L.idealEndpoints M.idealEndpoints := by
    apply Set.disjoint_left.mpr
    intro p hpA hpB
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints] at hpA hpB
    exact hPair (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_elementary_of_common_fixed _ _ p hpA
      hpB)
  have hneq : L≠M := by
    intro he
    obtain ⟨a,b,_γ,_hab,_ha,_hb,hab,_hrest⟩:=L.exists_idealEndpoints_pair
    have ha : a∈L.idealEndpoints:=by rw [hab];simp
    exact Set.disjoint_left.mp hends ha (he ▸ ha)
  by_cases hi : (L.carrier∩M.carrier).Nonempty
  · obtain ⟨p,hpA,hpB⟩:=hi
    exact hEllipticFree_hyperbolic_crossing_displacement_bound G hG A B hAm hBm hA hB htA htB p hpA hpB hneq z
  · have hd : L.HDisjoint M := by
      refine ⟨hneq,hends,Set.disjoint_left.mpr ?_⟩
      intro p hpA hpB
      exact hi ⟨p,hpA,hpB⟩
    by_cases hsA : IsSimple G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
    · exact hEllipticFree_simple_disjoint_displacement_bound G hG A B hA hB htA htB hsA hBm hPair hd z
    · by_cases hsB : IsSimple G (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)
      · have hPair' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
          rw [Set.pair_comm]
          exact hPair
        have hd' : M.HDisjoint L:=⟨hneq.symm,hends.symm,hd.2.2.symm⟩
        simpa only [mul_comm] using
          hEllipticFree_simple_disjoint_displacement_bound G hG B A hB hA htB htA hsB hAm hPair' hd' z
      · exact hEllipticFree_both_nonsimple_displacement_bound G hG hLift A B hAm hBm hA hB htA htB hsA hsB z

/-- The sharp exact bound for every original pair of an elliptic-free native real group, including both parabolic cases. -/
theorem hEllipticFree_displacement_bound
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hD :
      _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc G) (hG :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G)
    (hLift : ∀g∈G,∃A : Matrix.SpecialLinearGroup (Fin 2)
      ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=g)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈G) (hBm :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (z : ℍ) : 1≤Real.sinh (dist z (A • z)/2)*Real.sinh (dist z (B • z)/2) := by
  have hPair' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
    rw [Set.pair_comm]
    exact hPair
  have hA:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_left_ne_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) hPair
  have hB:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_left_ne_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) hPair'
  have hn : ¬∃p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val p=p ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val p=p := by
    rintro ⟨p,hpA,hpB⟩
    exact hPair (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_elementary_of_common_fixed _ _ p hpA
      hpB)
  rcases lt_trichotomy ((Matrix.trace A.val)^2) 4 with hEA | hPA | hHA
  · exact False.elim (hG ⟨_,hAm⟩ ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hA).mpr
    hEA))
  · exact _root_.LowDimensionalTopology.Geometry.Fuchsian.native_ellipticFree_parabolic_product G hD hG A B hAm hBm
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff A hA).mpr hPA) hn z
  · rcases lt_trichotomy ((Matrix.trace B.val)^2) 4 with hEB | hPB | hHB
    · exact False.elim (hG ⟨_,hBm⟩ ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff B
      hB).mpr hEB))
    · have hn' : ¬∃p : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex,(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val p=p ∧ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val p=p := by
        rintro ⟨p,hpB,hpA⟩
        exact hn ⟨p,hpA,hpB⟩
      have hb:=_root_.LowDimensionalTopology.Geometry.Fuchsian.native_ellipticFree_parabolic_product G hD hG B A hBm hAm
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_parabolic_iff B hB).mpr hPB) hn' z
      simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hDisplacement,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_apply, mul_comm] using hb
    · exact hEllipticFree_hyperbolic_displacement_bound G hG hLift A B hAm hBm hA hB hHA hHB hPair z

/-- Whole-disc real normalization requires no discreteness hypothesis. -/
theorem invariantDisc_halfPlane_normalizer_exists (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (D : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hD :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D)
    (hInv : ∀f : H,f.val.val '' D=D) :
    ∃q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,q.val '' D=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧
      ∀f∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H,∃A : Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=f := by
  obtain ⟨q,hq⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.IsComplexOpenDisc.halfPlane_normalizer hD
  refine ⟨q,hq,?_⟩
  intro f hf
  obtain ⟨g,hg,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
    f).mp hf
  apply mobius_preserves_halfPlane_exists_SL
  rw [←hq,_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image,hInv ⟨g,hg⟩,hq]

/-- The universal sharp bound in the original invariant-disc frame, with the entire original group normalized inside the proof. -/
theorem ellipticFree_invariantDisc_displacement_bound
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (D : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hD :
      _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D)
    (hInv : ∀f : H,f.val.val '' D=D) (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) :
    ∃q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,q.val '' D=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧
      ∀f g : H,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
        ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))→
      ∀z : ℍ,1≤_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement f.val (q⁻¹ •
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z)*
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement g.val (q⁻¹ • _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z) := by
  obtain ⟨q,hq,hLift⟩:=invariantDisc_halfPlane_normalizer_exists H D hD hInv
  refine ⟨q,hq,?_⟩
  intro f g hPair z
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  have hKD : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc K:=invariantDisc_conjugate H q ⟨D,hD,hInv⟩
  have hKE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree K:=hE.conjugation q
  have hfm : q*f.val*q⁻¹∈K:=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨f.val,f.property,rfl⟩
  have hgm : q*g.val*q⁻¹∈K:=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨g.val,g.property,rfl⟩
  obtain ⟨A,hAf⟩:=hLift _ hfm
  obtain ⟨B,hBg⟩:=hLift _ hgm
  have hPairK:=hPair.conjugation q
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,←hAf,←hBg] at hPairK
  have hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈K:=hAf ▸ hfm
  have hBm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈K:=hBg ▸ hgm
  have hb:=hEllipticFree_displacement_bound K hKD hKE hLift A B hAm hBm hPairK z
  change 1≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z at hb
  rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.halfPlaneH3Embed_sinh_displacement A z,
    ←_root_.LowDimensionalTopology.Geometry.Fuchsian.halfPlaneH3Embed_sinh_displacement B z,hAf,hBg] at hb
  have hconj (F : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement (q*F*q⁻¹) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z)=
        _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement F (q⁻¹ • _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z) := by
    unfold _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement
    rw [←_root_.LowDimensionalTopology.Geometry.Mobius.upperHalfSpacePathDist_smul q⁻¹]
    simp only [mul_smul,inv_smul_smul]
  rwa [hconj f.val,hconj g.val] at hb

end LowDimensionalTopology.Geometry.Fuchsian
