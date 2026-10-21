module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.ClosedTriangleNonElementary
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Data
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Topology
open scoped UpperHalfPlane Pointwise ENNReal
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- Every genuine measurable fundamental domain of the actual conformal kernel has area twice the original triangle's angle defect. -/
theorem triangleConformalKernel_measureDomain_volume
    (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) {S:Set ℍ}
    (hS:MeasureTheory.IsFundamentalDomain (triangleConformalKernel T) S volume) :
    volume S=ENNReal.ofReal (2*(Real.pi-T.alpha-T.beta-T.gamma)) := by
  let triangleExactAreaReflectionCountable:Countable (triangleReflectionGroup T):=
    triangleReflectionGroup_countable T
  let triangleExactAreaReflectionContinuous:ContinuousConstSMul (triangleReflectionGroup T) ℍ:=
    ⟨fun g=>g.val.continuous⟩
  let triangleExactAreaReflectionInvariant:SMulInvariantMeasure (triangleReflectionGroup T) ℍ volume:=⟨by
    intro g U hU
    exact (show MeasurePreserving g.val volume volume from
      ⟨g.val.continuous.measurable,native_isometry_volume_map g.val⟩).measure_preimage hU.nullMeasurableSet⟩
  let triangleExactAreaKernelFiniteIndex:(triangleConformalKernel T).FiniteIndex:=⟨by
    rw [triangleConformalKernel_index_two]
    norm_num⟩
  have hD:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle.fundamentalDomain_of_integral_angles T ha hb hc
  obtain ⟨F,hF,hTF,hFC⟩:=hD.exists_fundamentalSet
  have hm:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.nullMeasurableSet_of_between _ _ hD hTF hFC
  have hnull:∀g:triangleReflectionGroup T,g≠1→volume {x:ℍ|g•x=x}=0:=by
    intro g hg
    exact native_isometry_fixed_volume_zero g.val (fun he=>hg (Subtype.ext he))
  have hK:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.subgroupTransversalSet_measureDomain (triangleConformalKernel T) hF hm hnull
  have hCard:Nat.card (triangleReflectionGroup T ⧸ triangleConformalKernel T)=2:=
    triangleConformalKernel_index_two T
  rw [hS.measure_eq hK,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.subgroupTransversalSet_measure _ hF hm hnull,
    ENat.card_eq_coe_natCard,hCard,ENat.toENNReal_coe]
  rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain.measure_eq_of_between _ _ hD hTF hFC,T.area_eq_angle_defect]
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2)]
  norm_num

/-- The faithful full Mobius image has the same exact genuine hyperbolic covolume, independently of the chosen measurable domain. -/
theorem closedTriangle_measureDomain_volume (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (S:Set ℍ) :
    letI:=P.nativeAction
    MeasureTheory.IsFundamentalDomain (closedTriangleMobiusGroup T) S volume→
    volume S=ENNReal.ofReal (2*(Real.pi-T.alpha-T.beta-T.gamma)) := by
  let triangleExactAreaImageAction:=P.nativeAction
  intro hS
  let F:=nativeConformalSubgroupMobiusHom (triangleConformalGroup T) inf_le_right
  let triangleExactAreaRangeAction:MulAction F.range ℍ:=P.nativeAction
  let e:triangleConformalKernel T≃*F.range:=(triangleConformalKernelEquiv T).trans
    (MonoidHom.ofInjective (nativeConformalSubgroupMobiusHom_isometry _ _).injective)
  have he (g:triangleConformalKernel T) (z:ℍ):e g•z=g•z:=by
    apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
    rw [←P.nativeAction_boundary]
    exact nativeConformalSubgroupMobiusHom_action _ _ (triangleConformalKernelEquiv T g) z
  have hi (g:F.range) (z:ℍ):e.symm g•z=g•z:=by
    have h:=he (e.symm g) z
    rw [e.apply_symm_apply] at h
    exact h.symm
  have hK:=hS.preimage_of_equiv (f:=id) (MeasurePreserving.id volume).quasiMeasurePreserving
    e.symm.bijective (by intro g z;exact hi g z)
  exact triangleConformalKernel_measureDomain_volume T ha hb hc
    (by simpa only [preimage_id] using hK)

/-- The actual finite-corner reciprocal-order weights sum to the finite-corner count minus the physical total angle divided by pi. -/
theorem closedTriangle_signature_weight_sum (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) :
    ((closedTriangleFiniteCornerOrderList T ha hb hc).map (fun m:ℕ=>1-1/(m:ℝ))).sum=
      (Nat.card {i:Fin 3|0<closedTriangleCornerAngle T i}:ℝ)-
        (T.alpha+T.beta+T.gamma)/Real.pi := by
  classical
  let V:={i:Fin 3|0<closedTriangleCornerAngle T i}
  let E:Fin (Fintype.card V)≃V:=(Fintype.equivFin V).symm
  have hzero (i:Fin 3) (hi:¬0<closedTriangleCornerAngle T i):closedTriangleCornerAngle T i=0:=by
    apply le_antisymm (not_lt.mp hi)
    rw [←closedTriangleCornerCycle_angle]
    exact (closedTriangleCornerCycle T i).toDiscTriangle.alpha_mem_Ico.1
  have hs:∑i:V,closedTriangleCornerAngle T i.val=T.alpha+T.beta+T.gamma:=by
    have h:=Fintype.sum_subtype_add_sum_subtype
      (fun i:Fin 3=>0<closedTriangleCornerAngle T i) (closedTriangleCornerAngle T)
    change (∑i:V,closedTriangleCornerAngle T i.val)+
      (∑i:{i:Fin 3|¬0<closedTriangleCornerAngle T i},closedTriangleCornerAngle T i.val)=
        ∑i:Fin 3,closedTriangleCornerAngle T i at h
    have hz:∑i:{i:Fin 3|¬0<closedTriangleCornerAngle T i},closedTriangleCornerAngle T i.val=0:=by
      apply Finset.sum_eq_zero
      intro i _hi
      exact hzero i.val i.property
    rw [hz,add_zero,Fin.sum_univ_three] at h
    exact h
  have hr (i:V):1/(closedTriangleFiniteCornerOrder T ha hb hc i:ℝ)=
      closedTriangleCornerAngle T i.val/Real.pi:=by
    rw [(closedTriangleFiniteCornerOrder_spec T ha hb hc i).2]
    field_simp
  unfold closedTriangleFiniteCornerOrderList
  rw [List.map_ofFn,List.sum_ofFn]
  change (∑j:Fin (Fintype.card V),(1-1/(closedTriangleFiniteCornerOrder T ha hb hc (E j):ℝ)))=_
  rw [E.sum_comp (fun i:V=>1-1/(closedTriangleFiniteCornerOrder T ha hb hc i:ℝ))]
  simp_rw [hr]
  rw [Finset.sum_sub_distrib,←Finset.sum_div,hs]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,Nat.card_eq_fintype_card]
  rfl

/-- The three actual vertices split into precisely the finite corners and genuine cusp labels. -/
theorem closedTriangle_finite_ideal_card_sum (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle) :
    Nat.card {i:Fin 3|0<closedTriangleCornerAngle T i}+
      Nat.card {i:Fin 3|closedTriangleCornerAngle T i=0}=3 := by
  classical
  have he:{i:Fin 3|closedTriangleCornerAngle T i=0}={i:Fin 3|¬0<closedTriangleCornerAngle T i}:=by
    ext i
    change closedTriangleCornerAngle T i=0 ↔¬0<closedTriangleCornerAngle T i
    constructor
    · intro hi
      rw [hi]
      exact lt_irrefl _
    · intro hi
      apply le_antisymm (not_lt.mp hi)
      rw [←closedTriangleCornerCycle_angle]
      exact (closedTriangleCornerCycle T i).toDiscTriangle.alpha_mem_Ico.1
  rw [he,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  have hcomp:=Fintype.card_subtype_compl (fun i:Fin 3=>0<closedTriangleCornerAngle T i)
  change Fintype.card {i:Fin 3|¬0<closedTriangleCornerAngle T i}=
    Fintype.card (Fin 3)-Fintype.card {i:Fin 3|0<closedTriangleCornerAngle T i} at hcomp
  rw [hcomp]
  have hle:=Fintype.card_subtype_le (fun i:Fin 3=>0<closedTriangleCornerAngle T i)
  change Fintype.card {i:Fin 3//0<closedTriangleCornerAngle T i}≤3 at hle
  change Fintype.card {i:Fin 3//0<closedTriangleCornerAngle T i}+
    (3-Fintype.card {i:Fin 3//0<closedTriangleCornerAngle T i})=3
  omega

/-- Numerical data extracted from the proved actual full triangle signature; the area is not a defining field. -/
def closedTriangleSignatureData (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) : FuchsianSignature where
  genus:=0
  ellipticOrders:=closedTriangleFiniteCornerOrderList T ha hb hc
  ellipticOrders_two_le:=by
    intro m hm
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hm
    exact (closedTriangleFiniteCornerOrder_spec T ha hb hc _).1
  parabolicEnds:=Nat.card {i:Fin 3|closedTriangleCornerAngle T i=0}
  boundaryHyperbolicEnds:=0

/-- These data realize the genuine genus, elliptic orders and cusp classes of the original whole group. -/
theorem closedTriangleSignatureData_actual (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T)) :
    HasCofiniteFuchsianSignature P.asFuchsianDisc (closedTriangleSignatureData T ha hb hc).genus
      (closedTriangleSignatureData T ha hb hc).ellipticOrders
      (closedTriangleSignatureData T ha hb hc).parabolicEnds :=
  closedTriangle_actual_cofinite_signature T ha hb hc P

/-- The actual triangle signature deficit is its physical angle defect divided by pi. -/
theorem closedTriangleSignatureData_deficit (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) :
    (closedTriangleSignatureData T ha hb hc).deficit=
      1-(T.alpha+T.beta+T.gamma)/Real.pi := by
  simp only [_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.deficit, closedTriangleSignatureData,
    Nat.cast_zero, mul_zero, zero_sub, add_zero]
  rw [closedTriangle_signature_weight_sum]
  have h:=closedTriangle_finite_ideal_card_sum T
  have hr:(Nat.card {i:Fin 3|0<closedTriangleCornerAngle T i}:ℝ)+
      (Nat.card {i:Fin 3|closedTriangleCornerAngle T i=0}:ℝ)=3:=by exact_mod_cast h
  linarith

/-- Every true measurable fundamental domain has exactly the area formula of its independently proved genuine signature. -/
theorem closedTriangle_actual_signature_area (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (S:Set ℍ) :
    letI:=P.nativeAction
    MeasureTheory.IsFundamentalDomain (closedTriangleMobiusGroup T) S volume→
    volume S=ENNReal.ofReal (closedTriangleSignatureData T ha hb hc).areaFormulaValue := by
  let triangleSignatureAreaNativeAction:=P.nativeAction
  intro hS
  rw [closedTriangle_measureDomain_volume T ha hb hc P S hS,
    _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.areaFormulaValue,closedTriangleSignatureData_deficit]
  congr 1
  field_simp
  ring

/-- The genuine hyperbolic angle sum makes the independently extracted actual signature deficit positive. -/
theorem closedTriangleSignatureData_deficit_pos (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) : 0<(closedTriangleSignatureData T ha hb hc).deficit := by
  rw [closedTriangleSignatureData_deficit]
  have h:(T.alpha+T.beta+T.gamma)/Real.pi<1:=
    (div_lt_one Real.pi_pos).mpr T.angle_sum_lt_pi
  linarith

/-- The actual conformal quotient area is at least pi/21, with equality precisely for its true (2,3,7) elliptic multiset and no cusps. This theorem is for actual integral triangle groups. -/
theorem closedTriangle_measureDomain_volume_sharp (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) (P:HalfPlaneFuchsianGroup (closedTriangleMobiusGroup T))
    (S:Set ℍ) :
    letI:=P.nativeAction
    MeasureTheory.IsFundamentalDomain (closedTriangleMobiusGroup T) S volume→
    Real.pi/21≤(volume S).toReal ∧
      ((volume S).toReal=Real.pi/21 ↔
        Nat.card {i:Fin 3|closedTriangleCornerAngle T i=0}=0 ∧
          (closedTriangleFiniteCornerOrderList T ha hb hc).Perm [2,3,7]) := by
  let triangleSharpAreaNativeAction:=P.nativeAction
  intro hS
  have hp:=closedTriangleSignatureData_deficit_pos T ha hb hc
  have hn:0≤(closedTriangleSignatureData T ha hb hc).areaFormulaValue:=by
    unfold _root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianSignature.areaFormulaValue
    positivity
  rw [closedTriangle_actual_signature_area T ha hb hc P S hS,ENNReal.toReal_ofReal hn]
  simpa only [closedTriangleSignatureData,true_and] using
    (closedTriangleSignatureData T ha hb hc).areaFormulaValue_sharp hp

/-- Every original integral-angle reflection chamber has genuine area at least pi/42, including finite and ideal vertices. Discreteness alone without integral angles is not assumed to imply this here. -/
theorem closedTriangle_integral_area_lower_bound (T:_root_.LowDimensionalTopology.Geometry.Hyperbolic.ClosedHTriangle)
    (ha:IsIntegralTriangleAngle T.alpha) (hb:IsIntegralTriangleAngle T.beta)
    (hc:IsIntegralTriangleAngle T.gamma) : Real.pi/42≤(volume T.interior).toReal := by
  have hδ:(closedTriangleSignatureData T ha hb hc).deficit=
      (Real.pi-T.alpha-T.beta-T.gamma)/Real.pi:=by
    rw [closedTriangleSignatureData_deficit]
    field_simp
    ring
  have h:=((closedTriangleSignatureData T ha hb hc).deficit_sharp
    (closedTriangleSignatureData_deficit_pos T ha hb hc)).1
  rw [hδ] at h
  have hmul:Real.pi/42≤Real.pi-T.alpha-T.beta-T.gamma:=by
    convert (le_div_iff₀ Real.pi_pos).mp h using 1
    ring
  rw [T.area_eq_angle_defect,ENNReal.toReal_ofReal]
  · exact hmul
  · linarith [T.angle_sum_lt_pi]

end LowDimensionalTopology.Geometry.Fuchsian
