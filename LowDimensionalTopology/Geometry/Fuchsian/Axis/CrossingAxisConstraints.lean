/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.FuchsianCrossingHalfTurns
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.ConcurrentHyperbolicAxes
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

/-- A half-turn factorization partner lies on the hyperbolic axis. -/
theorem halfturn_factorization_partner_on_axis (A:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1) (htA:4<(Matrix.trace A.val)^2) (u v:ℍ)
    (hu:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
      htA).carrier) (hf:_root_.LowDimensionalTopology.Geometry.Hyperbolic.HasHalfTurnFactorization A u v) :
    v∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier := by
  obtain ⟨w,⟨hw,hf',_⟩,_⟩:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_hyperbolic_halfturn_factor A hA htA u hu
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfTurnFactorization_partner_unique A u v w hf hf' ▸ hw

/-- Non-elementarity forces concurrent hyperbolic axes of the two generators to be distinct. -/
theorem nonElementary_crossing_axes_ne (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A≠1) (hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA:4<(Matrix.trace A.val)^2) (htB:4<(Matrix.trace B.val)^2)
    (u:ℍ) (huA:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier)
    (huB:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier)
    (hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB := by
  obtain ⟨T,hu,hf,hg,_hTA,_hTB,_hgroup⟩:=crossingAxis_halfturn_triangle A B hA hB htA htB u huA huB hd hne
  have hTa:T.a∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier:=hu ▸ huA
  have hTb:T.b∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier:=
    halfturn_factorization_partner_on_axis A hA htA T.a T.b hTa
      ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL
        T.a,_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL
        T.b,_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at
        T.a,_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at T.b,hf⟩
  have hTc:T.c∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier:=
    halfturn_factorization_partner_on_axis B hB htB T.a T.c (hu ▸ huB)
      ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL
        T.a,_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL
        T.c,_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at
        T.a,_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at T.c,hg⟩
  intro he
  exact T.noncollinear ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA,hTa,hTb,he ▸ hTc⟩

/-- A nonelliptic commutator gives the crossing-angle estimate
for the smaller angle between the two tangent lines. -/
theorem hHyperbolic_crossing_nonElliptic_commutator_bound
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A≠1) (hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA:4<(Matrix.trace A.val)^2) (htB:4<(Matrix.trace B.val)^2)
    (u:ℍ) (huA:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier)
    (huB:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier)
    (hneq:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA
      htA≠_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)
    (hcomm:¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B*A⁻¹*B⁻¹))) :
    1≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)*
        Real.sin ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).acuteAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) u) := by
  let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA
  let M:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB
  let R:=L.rayAt u huA
  let S:=M.rayAt u huB
  have hR:R.supportLine=L:=L.rayAt_support u huA
  have hS:S.supportLine=M:=M.rayAt_support u huB
  have hRS:R.supportLine≠S.supportLine:=by rw [hR,hS];exact hneq
  have hb:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_commutator_intersection_bound A B hA hB htA htB R S hR hS
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_pos R S
      hRS) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure_lt_pi R S hRS) hcomm
  have he:Real.sin (L.acuteAngle M u)=Real.sin (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hInteriorAngleMeasure R S):=by
    rw [←hR,←hS,←R.acuteAngle_eq_support S,min_def]
    split_ifs <;> simp only [Real.sin_pi_sub]
  rwa [←he] at hb

/--
elliptic-free branch: the full actual original pair subgroup supplies
commutator nonellipticity and the true nondegenerate crossing-angle condition.
-/
theorem crossing_hyperbolic_ellipticFree_length_angle_bound
    (A B:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A≠1) (hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B≠1)
    (htA:4<(Matrix.trace A.val)^2) (htB:4<(Matrix.trace B.val)^2)
    (u:ℍ) (huA:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).carrier)
    (huB:u∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier)
    (hd:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hno:∀g∈Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup),¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g) :
    1≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B)/2)*
        Real.sin ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA).acuteAngle (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) u) := by
  apply hHyperbolic_crossing_nonElliptic_commutator_bound A B hA hB htA htB u huA huB
    (nonElementary_crossing_axes_ne A B hA hB htA htB u huA huB hd hne)
  apply hno
  simp only [map_mul,map_inv]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)))
    (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))))
    (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))


/-- The actual original pair and both actual axis-model matrices have exactly the same whole group. -/
theorem FuchsianAxisModel.generated_pair_conjugation {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) (M:FuchsianAxisModel D f.val) (N:FuchsianAxisModel D g.val) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate D.halfPlaneNormalizer
      (Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))=
        Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N.matrix}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) := by
  change (Subgroup.closure _).map _=_
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,←M.projection,←N.projection]

/-- The actual smaller tangent angle of the two original hyperbolic axes,
expressed in the genuine whole-disc conformal metric chart. -/
def FuchsianDisc.axesAngle {H:Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (D:FuchsianDisc
  H)
    (f g:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      f.val) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g.val)
    (x:(fuchsianGeometricDomain D).carrier) : ℝ:=
  (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf).line.acuteAngle
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g
      hg).line (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x)

/--
The elliptic-free clause on every original geometric invariant disc,
with original displacement-infimum lengths and the genuine crossing tangent angle.
-/
theorem fuchsian_crossing_ellipticFree_length_angle_bound {H:Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D:FuchsianDisc H) (f g:H) (hf:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      f.val) (hg:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic g.val)
    (hne:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hno:∀h∈Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup),¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic h)
    (x:(fuchsianGeometricDomain D).carrier)
    (hxf:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf).carrier)
    (hxg:x.val∈(_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g hg).carrier) :
    1≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D f/2)*
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.translationLength D g/2)*
        Real.sin (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.axesAngle D f g hf hg x) := by
  let M:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D f hf
  let N:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.chosenAxisModel D g hg
  let q:=D.halfPlaneNormalizer
  let G:=Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hGH:G≤H:=(Subgroup.closure_le H).mpr (by
    intro s hs
    rcases hs with rfl|rfl
    · exact f.property
    · exact g.property)
  have hdG:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G:=discreteMobius_subgroup_of_le H G D.discrete hGH
  have hmap:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.generated_pair_conjugation D f g M N
  have hdN:_root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N.matrix}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    let originalCrossingNoEllipticDiscrete:DiscreteTopology G:=hdG
    have hh:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q G
    change DiscreteTopology (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q
      G) at hh
    rwa [hmap] at hh
  have hneN:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N.matrix}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
    have hh:=hne.conjugation q
    change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q G) at hh
    rwa [hmap] at hh
  have hnoN:∀h∈Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius M.matrix,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius N.matrix}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup),¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic h:=by
    intro h hh he
    rw [←hmap] at hh
    obtain ⟨a,ha,hea⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q
      G h).mp hh
    exact hno a ha ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation a q).mp (hea.symm ▸ he))
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.translationLength f
    M,_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.translationLength g N]
  exact crossing_hyperbolic_ellipticFree_length_angle_bound M.matrix N.matrix M.nontrivial
    N.nontrivial M.trace_gt N.trace_gt (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.hyperbolicCoordinate D x)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.hyperbolicCoordinate_mem M x hxf)
    (_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianAxisModel.hyperbolicCoordinate_mem N x hxg) hdN hneN hnoN

end LowDimensionalTopology.Geometry.Fuchsian
