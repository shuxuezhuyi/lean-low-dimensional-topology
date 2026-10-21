module
public import LowDimensionalTopology.Geometry.Euclidean.InnerProduct.ComplexAffine
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.FiniteHull
public import LowDimensionalTopology.Geometry.Euclidean.Convexity.Separation
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.CappedSurface
public import LowDimensionalTopology.Geometry.Auxiliary.Topology.FiniteClosedCoverHomeomorph
public import Mathlib.Dynamics.PeriodicPts.Lemmas
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Analysis.Convex.Combination
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.CanonicalCylinderCoordinates
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.CanonicalHandleEuler
public import Mathlib.Topology.LocallyFinite
public import Mathlib.Data.Set.UnionLift
public import Mathlib.Topology.Homeomorph.Defs
/-!
# The Fuchsian quotient as a punctured capped surface

Boundary-hyperbolic ends are modeled by funnels and matched to punctured caps
of the geometric Nielsen surface. Local homeomorphisms on the completed core
and the end pieces agree along their common boundary circles, so they paste
to a homeomorphism of the whole quotient with the punctured capped surface.

Cusp and boundary-end labels determine the removed points. The resulting
surface identification transports the genus used in the core-area formula.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter MeasureTheory
open scoped UpperHalfPlane Complex.UnitDisc OnePoint RealInnerProductSpace Pointwise


namespace LowDimensionalTopology.Geometry.Fuchsian
attribute [local instance] nielsenInteriorSphereMeasurableSpace nielsenInteriorSphereBorelSpace

section NielsenCanonicalGeometricCaps
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} (P:UnitDiscFuchsianGroup H)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)

/-- The genuine original-group Nielsen capping and area construction uses only non-elementarity and finite generation; every Dirichlet polygon, marked boundary and cap datum in the conclusion is actually derived. -/
theorem finitelyGenerated_nielsenCore_geometric_caps_area :
    ∃w:P.domain.carrier,∃hw:IsDirichletCenter P w,∃hwN:w∈fuchsianNielsenCore P hNE,
      let D:=dirichletDomain P w
      let hD:=dirichletDomain_isConvexFuchsianPolygon P w hw
      let hfin:=finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw
      let hwD:=dirichletDomain_center_mem P w hw
      ∃J:Moise.PolygonalCircle,
      ∃hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier),
      ∃hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG,
      ∃n:ℕ,∃S:Polygon.CyclicDiscPolygonSupportData n,
      ∃hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE),
    let _nielsenGeometricCapsEllipticFinite : Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
      finite_sided_polygon_elliptic_classes_finite hD hfin
    ∃g,Surfaces.HasTopologicalGenus ((nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv).PolygonalRealization
      (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)) g ∧
      Topology.IsClosedEmbedding ((nielsenCompletedCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr)) ∧
      (range ((nielsenCompletedCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S
        hr)))ᶜ=⋃f:{f:(nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv).Face // f≠nielsenCappedOriginalFace
        hD hNE hFG hfin w hwD hwN J hc hv},range (((nielsenCappedFaceInterior hD hNE hFG hfin w hwD hwN J hc hv))
        f.val) ∧
      (∀f:{f:(nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv).Face // f≠nielsenCappedOriginalFace hD hNE
        hFG hfin w hwD hwN J hc hv},Topology.IsOpenEmbedding (((nielsenCappedFaceInterior hD hNE hFG hfin w hwD hwN J hc
        hv)) f.val)) ∧
      (∀f:{f:(nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv).Face // f≠nielsenCappedOriginalFace hD hNE
        hFG hfin w hwD hwN J hc hv},Topology.IsClosedEmbedding (((nielsenCappedClosedCap hD hNE hFG hfin w hwD hwN J hc
        hv)) f.val)) ∧
      Pairwise (fun f k:{f:(nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv).Face //
        f≠nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv}=>Disjoint (range (((nielsenCappedClosedCap hD hNE
        hFG hfin w hwD hwN J hc hv)) f.val)) (range (((nielsenCappedClosedCap hD hNE hFG hfin w hwD hwN J hc hv))
        k.val))) ∧
      (∀f:{f:(nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv).Face // f≠nielsenCappedOriginalFace hD hNE
        hFG hfin w hwD hwN J hc hv},Topology.IsClosedEmbedding (((nielsenCappedCapClock hD hNE hFG hfin w hwD hwN J hc
        hv)) f.val)) ∧
      (∀f:{f:(nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv).Face // f≠nielsenCappedOriginalFace hD hNE
        hFG hfin w hwD hwN J hc hv},range (((nielsenCappedOriginalCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr))
        f.val f.property)=
        (fuchsianCuspCompletionOld P.asFuchsianDisc) '' ((nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc
          hv) (((nielsenCappedCapCycle hD hNE hFG hfin w hwD hwN J hc hv)) f.val f.property))) ∧
      (∀f:{f:(nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv).Face // f≠nielsenCappedOriginalFace hD hNE
        hFG hfin w hwD hwN J hc hv},∀z:Circle,((nielsenCompletedCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S
        hr)) (((nielsenCompletedCoreCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr)) f z)=((nielsenCappedCapClock hD
        hNE hFG hfin w hwD hwN J hc hv)) f.val z) ∧
      Nat.card {f:(nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv).Face // f≠nielsenCappedOriginalFace hD
        hNE hFG hfin w hwD hwN J hc hv}=Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc) ∧
      (fuchsianNielsenCoreArea P hNE D).toReal=2*Real.pi*
        (2*(g:ℝ)-2+Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc)+
          Nat.card (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic)+
          ((fuchsianEllipticOrderList P.asFuchsianDisc).map (fun m:ℕ=>1-1/(m:ℝ))).sum) := by
  obtain ⟨w,hw,hwN,n,S,hr,_⟩:=finitelyGenerated_nielsenCore_polygon P hNE hFG
  let hD:=dirichletDomain_isConvexFuchsianPolygon P w hw
  let hfin:=finitelyGenerated_dirichlet_sides_finite P hNE hFG w hw
  let hwD:=dirichletDomain_center_mem P w hw
  obtain ⟨J,hc,hv⟩:=nielsenCore_actual_marked_cyclic_boundary hD hNE hFG hfin w hwD hwN
  refine ⟨w,hw,hwN,J,hc,hv,n,S,hr,?_⟩
  exact nielsenCompletedCore_geometric_caps_area hD hNE hFG hfin w hwD hwN J hc hv S hr

end NielsenCanonicalGeometricCaps




def nielsenRightFunnel  : Set ℍ:=
  {z | z.re/z.im∈Ici (0:ℝ)}

/-- The native strip is the product of the real geodesic parameter and
the actual closed nonnegative transverse interval, with its genuine native topology. -/
def nielsenRightFunnelHomeomorph  :
    nielsenRightFunnel ≃ₜ ℝ×Ici (0:ℝ) where
  toFun z:=⟨Real.log z.val.im,⟨z.val.re/z.val.im,z.property⟩⟩
  invFun p:=⟨halfPlaneLogRatioHomeomorph.symm (p.1,p.2.val),by
    change (Real.exp p.1*p.2.val)/(Real.exp p.1)∈Ici (0:ℝ)
    simpa only [mul_div_cancel_left₀ _ (Real.exp_ne_zero _)] using p.2.property⟩
  left_inv z:=by
    apply Subtype.ext
    exact halfPlaneLogRatioHomeomorph.left_inv z.val
  right_inv p:=by
    apply Prod.ext
    · change Real.log (Real.exp p.1)=p.1
      exact Real.log_exp _
    · apply Subtype.ext
      change Real.exp p.1*p.2.val/Real.exp p.1=p.2.val
      field_simp
  continuous_toFun:=by
    apply Continuous.prodMk
    · exact (UpperHalfPlane.continuous_im.comp continuous_subtype_val).log
        (fun z=>z.val.im_pos.ne')
    · apply Continuous.subtype_mk
      exact (UpperHalfPlane.continuous_re.comp continuous_subtype_val).div
        (UpperHalfPlane.continuous_im.comp continuous_subtype_val) (fun z=>z.val.im_pos.ne')
  continuous_invFun:=by
    apply Continuous.subtype_mk
    exact halfPlaneLogRatioHomeomorph.symm.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

/-- Every actual dilation power translates the genuine logarithmic
height coordinate and fixes the genuine transverse coordinate. -/
theorem nielsenFunnel_dilation_coordinates (l:ℝ) (n:ℤ) (p:ℝ×Ici (0:ℝ)) :
    (Surfaces.stableAxisDilation l^n).val (Mobius.halfPlaneBoundaryPoint (((nielsenRightFunnelHomeomorph).symm p).val))=
      Mobius.halfPlaneBoundaryPoint ((nielsenRightFunnelHomeomorph).symm (p.1+(n:ℝ)*l,p.2)) := by
  change (Surfaces.stableAxisDilation l^n).val
    (((((nielsenRightFunnelHomeomorph).symm p).val:ℍ):ℂ):Mobius.ExtendedComplex)=_
  rw [stableAxisDilation_zpow_coe]
  change ((((Real.exp ((n:ℝ)*l):ℝ):ℂ)*
      (⟨Real.exp p.1*p.2.val,Real.exp p.1⟩:ℂ):ℂ):Mobius.ExtendedComplex)=
      ((⟨Real.exp (p.1+(n:ℝ)*l)*p.2.val,Real.exp (p.1+(n:ℝ)*l)⟩:ℂ):Mobius.ExtendedComplex)
  apply congrArg ((↑):ℂ→Mobius.ExtendedComplex)
  apply Complex.ext <;> simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,add_zero,Real.exp_add] <;> ring

/-- The actual product-period map, on genuine transverse strip coordinates. -/
def nielsenFunnelPeriodMap (l:ℝ) (p:ℝ×Ici (0:ℝ)) : AddCircle l×Ici (0:ℝ) :=
  ((p.1:AddCircle l),p.2)

theorem nielsenFunnelPeriodMap_isOpenQuotientMap (l:ℝ) :
    IsOpenQuotientMap (nielsenFunnelPeriodMap l) :=
  QuotientAddGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id

/-- The genuine product-period fibers retain exactly the original
integer period and the actual transverse coordinate. -/
theorem nielsenFunnelPeriodMap_fiber (l:ℝ) (p q:ℝ×Ici (0:ℝ)) :
    nielsenFunnelPeriodMap l p=nielsenFunnelPeriodMap l q ↔
      ∃n:ℤ,p.1=q.1+(n:ℝ)*l ∧ p.2=q.2 := by
  constructor
  · intro h
    have ht: (p.1:AddCircle l)=q.1:=congrArg Prod.fst h
    obtain ⟨n,hn⟩:=AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq_iff_sub_mem.mp ht)
    change n • l=p.1-q.1 at hn
    rw [zsmul_eq_mul] at hn
    exact ⟨n,by linarith only [hn],congrArg (fun x:AddCircle l×Ici (0:ℝ)=>x.2) h⟩
  · rintro ⟨n,hn,hr⟩
    apply Prod.ext
    · apply QuotientAddGroup.eq_iff_sub_mem.mpr
      apply AddSubgroup.mem_zmultiples_iff.mpr
      refine ⟨n,?_⟩
      rw [zsmul_eq_mul]
      linarith only [hn]
    · exact hr

/-- The restricted original sphere orbit relation is exactly the genuine
circle-period fiber relation, throughout the whole canonical strip. -/
theorem nielsenFunnel_dilation_orbitRel_iff (l:ℝ) (p q:ℝ×Ici (0:ℝ)) :
    (MulAction.orbitRel (Subgroup.zpowers (Surfaces.stableAxisDilation l)) Mobius.ExtendedComplex)
      (Mobius.halfPlaneBoundaryPoint ((nielsenRightFunnelHomeomorph).symm p).val)
      (Mobius.halfPlaneBoundaryPoint ((nielsenRightFunnelHomeomorph).symm q).val) ↔
      nielsenFunnelPeriodMap l p=nielsenFunnelPeriodMap l q := by
  let E:=nielsenRightFunnelHomeomorph
  constructor
  · rintro ⟨f,hf⟩
    obtain ⟨n,hn⟩:=f.property
    change f.val.val (Mobius.halfPlaneBoundaryPoint (E.symm q).val)=Mobius.halfPlaneBoundaryPoint (E.symm p).val at hf
    rw [←hn,nielsenFunnel_dilation_coordinates] at hf
    have he:(q.1+(n:ℝ)*l,q.2)=p:=E.symm.injective
      (Subtype.ext (Mobius.halfPlaneBoundaryPoint_injective hf))
    exact (nielsenFunnelPeriodMap_fiber l p q).mpr
      ⟨n,(congrArg Prod.fst he).symm,(congrArg Prod.snd he).symm⟩
  · intro h
    obtain ⟨n,hn,hr⟩:=(nielsenFunnelPeriodMap_fiber l p q).mp h
    refine ⟨⟨Surfaces.stableAxisDilation l^n,Subgroup.mem_zpowers_iff.mpr ⟨n,rfl⟩⟩,?_⟩
    change (Surfaces.stableAxisDilation l^n).val (Mobius.halfPlaneBoundaryPoint (E.symm
      q).val)=Mobius.halfPlaneBoundaryPoint (E.symm p).val
    rw [nielsenFunnel_dilation_coordinates]
    have he:(q.1+(n:ℝ)*l,q.2)=p:=Prod.ext hn.symm hr.symm
    rw [he]

/-- The actual cyclic canonical-strip quotient is the genuine product
of the additive circle and the actual closed nonnegative transverse interval. -/
def nielsenRightFunnelQuotientHomeomorph (l:ℝ) :
    Quotient ((MulAction.orbitRel (Subgroup.zpowers (Surfaces.stableAxisDilation l)) Mobius.ExtendedComplex).comap
      (fun z:nielsenRightFunnel=>Mobius.halfPlaneBoundaryPoint z.val)) ≃ₜ
      AddCircle l×Ici (0:ℝ) := by
  let E:=nielsenRightFunnelHomeomorph
  let F:C(ℝ×Ici (0:ℝ),AddCircle l×Ici (0:ℝ)):=
    ⟨nielsenFunnelPeriodMap l,(nielsenFunnelPeriodMap_isOpenQuotientMap l).continuous⟩
  have hF:IsQuotientMap F:=(nielsenFunnelPeriodMap_isOpenQuotientMap l).isQuotientMap
  refine (Homeomorph.Quotient.congr (rY:=Setoid.ker F) E ?_).trans hF.homeomorph
  intro z w
  have h:=nielsenFunnel_dilation_orbitRel_iff l (E z) (E w)
  change (MulAction.orbitRel (Subgroup.zpowers (Surfaces.stableAxisDilation l)) Mobius.ExtendedComplex)
    (Mobius.halfPlaneBoundaryPoint z.val) (Mobius.halfPlaneBoundaryPoint w.val) ↔
    nielsenFunnelPeriodMap l (E z)=nielsenFunnelPeriodMap l (E w)
  simpa only [E,Homeomorph.symm_apply_apply] using h

/-- A nonzero actual dilation period gives the source topological
collar model, a genuine circle times the genuine open transverse interval. -/
def nielsenRightFunnelQuotientCircle (l:ℝ) (hl:l≠0) :
    Quotient ((MulAction.orbitRel (Subgroup.zpowers (Surfaces.stableAxisDilation l)) Mobius.ExtendedComplex).comap
      (fun z:nielsenRightFunnel=>Mobius.halfPlaneBoundaryPoint z.val)) ≃ₜ
      Circle×Ici (0:ℝ) :=
  (nielsenRightFunnelQuotientHomeomorph l).trans
    ((AddCircle.homeomorphCircle hl).prodCongr (Homeomorph.refl _))




/-- The actual closed unit disc with its centre removed, retaining its full boundary circle. -/
abbrev NielsenPuncturedClosedDisc := {z:𝕔𝔻 // z.val≠0}

/-- A genuine closed funnel is a punctured cap, with its actual circle at transverse coordinate zero. -/
def nielsenFunnelPuncturedCapHomeomorph : Circle×Ici (0:ℝ) ≃ₜ NielsenPuncturedClosedDisc where
  toFun p:=⟨⟨(Real.exp (-p.2.val):ℂ)*(p.1:ℂ),by
    apply mem_closedBall_zero_iff.mpr
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Circle.norm_coe,mul_one]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr p.2.property)⟩,by
    apply mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
    exact norm_ne_zero_iff.mp (by rw [Circle.norm_coe];exact one_ne_zero)⟩
  invFun z:=(⟨z.val.val/(‖z.val.val‖:ℂ),by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_div,Complex.norm_real,norm_norm]
    exact div_self (norm_ne_zero_iff.mpr z.property)⟩,
    ⟨-Real.log ‖z.val.val‖,neg_nonneg.mpr (Real.log_nonpos (norm_nonneg _) z.val.norm_le_one)⟩)
  left_inv p:=by
    apply Prod.ext
    · apply Subtype.ext
      change (((Real.exp (-p.2.val):ℝ):ℂ)*(p.1:ℂ))/
        (‖((Real.exp (-p.2.val):ℝ):ℂ)*(p.1:ℂ)‖:ℂ)=(p.1:ℂ)
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Circle.norm_coe,mul_one]
      field_simp
    · apply Subtype.ext
      change -Real.log ‖((Real.exp (-p.2.val):ℝ):ℂ)*(p.1:ℂ)‖=p.2.val
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos
        _),Circle.norm_coe,mul_one,Real.log_exp,neg_neg]
  right_inv z:=by
    apply Subtype.ext
    apply Subtype.ext
    change (Real.exp (- -Real.log ‖z.val.val‖):ℂ)*
      (z.val.val/(‖z.val.val‖:ℂ))=z.val.val
    rw [neg_neg,Real.exp_log (norm_pos_iff.mpr z.property)]
    rw [←mul_div_assoc]
    exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.property))
  continuous_toFun:=by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_subtype_val.comp
      continuous_snd).neg)).mul
      (continuous_subtype_val.comp continuous_fst)
  continuous_invFun:=by
    have hz:Continuous (fun z:NielsenPuncturedClosedDisc=>z.val.val):=
      Complex.UnitClosedDisc.continuous_coe.comp continuous_subtype_val
    have hn:∀z:NielsenPuncturedClosedDisc,‖z.val.val‖≠0:=fun z=>norm_ne_zero_iff.mpr z.property
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      exact hz.div (Complex.continuous_ofReal.comp hz.norm) (fun z=>Complex.ofReal_ne_zero.mpr (hn z))
    · exact (hz.norm.log hn).neg.subtype_mk _

theorem nielsenFunnelPuncturedCapHomeomorph_boundary (z:Circle) :
    ((nielsenFunnelPuncturedCapHomeomorph (z,⟨0,le_rfl⟩)).val:ℂ)=(z:ℂ) := by
  change (Real.exp (-(0:ℝ)):ℂ)*(z:ℂ)=(z:ℂ)
  rw [neg_zero,Real.exp_zero,Complex.ofReal_one,one_mul]



/-- An actual original boundary axis has a genuine half-plane chart in which its entire full stabilizer is the positive dilation lattice. Only the boundary stabilizer is restricted; ambient elliptics remain allowed. -/
theorem boundaryHyperbolic_axis_positive_normal_form
    {H:Subgroup Mobius.complexMobiusGroup}
    (D:FuchsianDisc H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (f:H) (hf:IsBoundaryHyperbolic D f) (M:FuchsianAxisModel D f.val) :
    ∃q:Mobius.complexMobiusGroup,∃l:ℝ,0<l ∧ q.val '' D.carrier=Hyperbolic.openHalfPlaneSet ∧
      q.val '' M.carrier=Hyperbolic.extendedImaginaryAxis ∧
      DiscreteGroups.Action.Actions.subgroupConjugate q (Surfaces.mobiusSetStabilizer H M.carrier)=Subgroup.zpowers (Surfaces.stableAxisDilation l) := by
  obtain ⟨p,hpH,hpL⟩:=Surfaces.stableAxis_nativeLine_normalizer M.line
  let q:=p*D.halfPlaneNormalizer
  have hqD:q.val '' D.carrier=Hyperbolic.openHalfPlaneSet:=by
    change (fun z=>p.val (D.halfPlaneNormalizer.val z)) '' D.carrier=_
    rw [←image_image,D.halfPlaneNormalizer_image,hpH]
  have hqS:q.val '' M.carrier=Hyperbolic.extendedImaginaryAxis:=by
    change (fun z=>p.val (D.halfPlaneNormalizer.val z)) '' M.carrier=_
    rw [←image_image,M.carrier_image]
    exact hpL
  let K:=Surfaces.mobiusSetStabilizer H M.carrier
  let N:=DiscreteGroups.Action.Actions.subgroupConjugate q K
  have hKH:K≤H:=Surfaces.mobiusSetStabilizer_le H M.carrier
  let:DiscreteTopology H:=D.discrete
  let:DiscreteTopology K:=DiscreteGroups.MatrixGroups.subgroup_discrete hKH
  have hdN:Mobius.IsDiscreteMobiusSubgroup N:=DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q K
  have hn:N≠⊥:=by
    intro he
    have hqf:q*f.val*q⁻¹∈N:=
      (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q K _).mpr ⟨f.val,⟨f.property,M.carrier_invariant⟩,rfl⟩
    rw [he] at hqf
    have hconj:q*f.val*q⁻¹=1:=hqf
    apply hf.hyperbolic.1.1
    apply (MulAut.conj q).injective
    simpa only [map_one,MulAut.conj_apply] using hconj
  have hpositive:∀a∈N,∃r:ℝ,∃hr:0<r,
      a=Mobius.mobiusScaling (Units.mk0 (r:ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')):=by
    intro a ha
    obtain ⟨g,hg,rfl⟩:=(DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q K a).mp ha
    have hgK: g∈H ∧ g.val '' M.carrier=M.carrier:=(Surfaces.mem_mobiusSetStabilizer H M.carrier g).mp hg
    apply Surfaces.stableAxis_mobius_positive_scaling
    · simpa only [hqD,D.image_eq ⟨g,hgK.1⟩] using Mobius.stableAxis_conjugate_image q g D.carrier
    · simpa only [hqS,hgK.2] using Mobius.stableAxis_conjugate_image q g M.carrier
    · intro hEll
      exact False.elim (boundaryHyperbolic_axis_stabilizer_no_elliptics hNE hf M g hg
        ((Mobius.mobiusElliptic_conjugation g q).mp hEll))
  obtain ⟨l,hl,hN⟩:=Surfaces.stableAxis_positive_generator N hdN hn hpositive
  exact ⟨q,l,hl,hqD,hqS,hN⟩



theorem boundaryHyperbolic_axis_positive_lattice_of_normalizer
    {H:Subgroup Mobius.complexMobiusGroup}(D:FuchsianDisc H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (f:H) (hf:IsBoundaryHyperbolic D f) (M:FuchsianAxisModel D f.val)
    (q:Mobius.complexMobiusGroup)
    (hqD:q.val '' D.carrier=Hyperbolic.openHalfPlaneSet)
    (hqS:q.val '' M.carrier=Hyperbolic.extendedImaginaryAxis) :
    ∃l:ℝ,0<l ∧ DiscreteGroups.Action.Actions.subgroupConjugate q (Surfaces.mobiusSetStabilizer H M.carrier)=
      Subgroup.zpowers (Surfaces.stableAxisDilation l) := by
  let K:=Surfaces.mobiusSetStabilizer H M.carrier
  let N:=DiscreteGroups.Action.Actions.subgroupConjugate q K
  have hKH:K≤H:=Surfaces.mobiusSetStabilizer_le H M.carrier
  let:DiscreteTopology H:=D.discrete
  let:DiscreteTopology K:=DiscreteGroups.MatrixGroups.subgroup_discrete hKH
  have hdN:Mobius.IsDiscreteMobiusSubgroup N:=DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q K
  have hn:N≠⊥:=by
    intro he
    have hqf:q*f.val*q⁻¹∈N:=
      (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q K _).mpr ⟨f.val,⟨f.property,M.carrier_invariant⟩,rfl⟩
    rw [he] at hqf
    have hconj:q*f.val*q⁻¹=1:=hqf
    apply hf.hyperbolic.1.1
    apply (MulAut.conj q).injective
    simpa only [map_one,MulAut.conj_apply] using hconj
  have hpositive:∀a∈N,∃r:ℝ,∃hr:0<r,
      a=Mobius.mobiusScaling (Units.mk0 (r:ℂ) (Complex.ofReal_ne_zero.mpr hr.ne')):=by
    intro a ha
    obtain ⟨g,hg,rfl⟩:=(DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q K a).mp ha
    have hgK: g∈H ∧ g.val '' M.carrier=M.carrier:=(Surfaces.mem_mobiusSetStabilizer H M.carrier g).mp hg
    apply Surfaces.stableAxis_mobius_positive_scaling
    · simpa only [hqD,D.image_eq ⟨g,hgK.1⟩] using Mobius.stableAxis_conjugate_image q g D.carrier
    · simpa only [hqS,hgK.2] using Mobius.stableAxis_conjugate_image q g M.carrier
    · intro hEll
      exact False.elim (boundaryHyperbolic_axis_stabilizer_no_elliptics hNE hf M g hg
        ((Mobius.mobiusElliptic_conjugation g q).mp hEll))
  obtain ⟨l,hl,hN⟩:=Surfaces.stableAxis_positive_generator N hdN hn hpositive
  exact ⟨l,hl,hN⟩

theorem nielsenAxisSwap_param (t:ℝ) :
    (Hyperbolic.realSLMobius (Hyperbolic.axisHalfTurnSL 1 (by norm_num))).val
      (Hyperbolic.extendedHalfPlanePoint (Hyperbolic.imaginaryAxisParam t))=
      Hyperbolic.extendedHalfPlanePoint (Hyperbolic.imaginaryAxisParam (-t)) := by
  change (Hyperbolic.realSLMobius (Hyperbolic.axisHalfTurnSL 1 (by norm_num))).val
    ((Hyperbolic.imaginaryAxisParam t:ℍ):ℂ)=_
  rw [Hyperbolic.realSLMobius_action,Hyperbolic.axisHalfTurnSL_coe]
  apply congrArg ((↑):ℂ→Mobius.ExtendedComplex)
  rw [Hyperbolic.imaginaryAxisParam_coe,Hyperbolic.imaginaryAxisParam_coe,Real.exp_neg]
  push_cast
  field_simp [Real.exp_ne_zero t,Complex.I_ne_zero]
  simp [Complex.I_sq]

theorem nielsenAxisSwap_axis :
    (Hyperbolic.realSLMobius (Hyperbolic.axisHalfTurnSL 1 (by norm_num))).val '' Hyperbolic.extendedImaginaryAxis=
      Hyperbolic.extendedImaginaryAxis := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_,⟨t,rfl⟩,rfl⟩
    rw [nielsenAxisSwap_param]
    exact ⟨-t,rfl⟩
  · rintro _ ⟨t,rfl⟩
    refine ⟨Hyperbolic.extendedHalfPlanePoint (Hyperbolic.imaginaryAxisParam (-t)),⟨-t,rfl⟩,?_⟩
    rw [nielsenAxisSwap_param,neg_neg]

theorem nielsenAxisSwap_re (z:ℍ) :
    (Hyperbolic.axisHalfTurnSL 1 (by norm_num) • z:ℍ).re= -z.re/Complex.normSq (z:ℂ) := by
  change (((Hyperbolic.axisHalfTurnSL 1 (by norm_num) • z:ℍ):ℂ).re)=_
  rw [Hyperbolic.axisHalfTurnSL_coe]
  simp [Complex.div_re]

/-- The actual full boundary stabilizer admits a positive dilation chart with
the supplied original point strictly on the retained left side. -/
theorem boundaryHyperbolic_axis_left_point_normal_form
    {H:Subgroup Mobius.complexMobiusGroup}(D:FuchsianDisc H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (f:H) (hf:IsBoundaryHyperbolic D f) (M:FuchsianAxisModel D f.val)
    (w:(fuchsianGeometricDomain D).carrier) (hw:w.val∉M.carrier) :
    ∃q:Mobius.complexMobiusGroup,∃l:ℝ,∃_hl:0<l,
      ∃hqD:q.val '' D.carrier=Hyperbolic.openHalfPlaneSet,
      q.val '' M.carrier=Hyperbolic.extendedImaginaryAxis ∧
      DiscreteGroups.Action.Actions.subgroupConjugate q (Surfaces.mobiusSetStabilizer H M.carrier)=
        Subgroup.zpowers (Surfaces.stableAxisDilation l) ∧
      (geometricHalfPlaneChart D q hqD w).re<0 := by
  obtain ⟨q,l,hl,hqD,hqS,hqK⟩:=boundaryHyperbolic_axis_positive_normal_form D hNE f hf M
  let E:=geometricHalfPlaneChart D q hqD
  have hE:Hyperbolic.extendedHalfPlanePoint (E w)=q.val w.val:=geometricHalfPlaneChart_extended D q hqD w
  have hwr:(E w).re≠0:=by
    intro he
    have hp:Hyperbolic.extendedHalfPlanePoint (E w)∈Hyperbolic.extendedImaginaryAxis:=by
      refine ⟨Real.log (E w).im,?_⟩
      apply congrArg Hyperbolic.extendedHalfPlanePoint
      apply UpperHalfPlane.ext_re_im
      · exact he.symm
      · exact Real.exp_log (E w).im_pos
    rw [hE,←hqS] at hp
    exact hw (q.val.injective.mem_set_image.mp hp)
  rcases lt_or_gt_of_ne hwr with hneg|hpos
  · exact ⟨q,l,hl,hqD,hqS,hqK,hneg⟩
  · let s:=Hyperbolic.realSLMobius (Hyperbolic.axisHalfTurnSL 1 (by norm_num))
    let p:=s*q
    have hpD:p.val '' D.carrier=Hyperbolic.openHalfPlaneSet:=by
      change (fun z=>s.val (q.val z)) '' D.carrier=_
      rw [←image_image,hqD]
      exact realSLMobius_image_openHalfPlane _
    have hpS:p.val '' M.carrier=Hyperbolic.extendedImaginaryAxis:=by
      change (fun z=>s.val (q.val z)) '' M.carrier=_
      rw [←image_image,hqS]
      exact nielsenAxisSwap_axis
    obtain ⟨k,hk,hpK⟩:=boundaryHyperbolic_axis_positive_lattice_of_normalizer D hNE f hf M p hpD hpS
    refine ⟨p,k,hk,hpD,hpS,hpK,?_⟩
    have he:geometricHalfPlaneChart D p hpD w=Hyperbolic.axisHalfTurnSL 1 (by norm_num) • E w:=by
      apply nielsen_halfPlanePoint_isOpenEmbedding.injective
      calc
        Hyperbolic.extendedHalfPlanePoint (geometricHalfPlaneChart D p hpD w)=p.val w.val:=
          geometricHalfPlaneChart_extended D p hpD w
        _=s.val (Hyperbolic.extendedHalfPlanePoint (E w)):=congrArg s.val hE.symm
        _=Hyperbolic.extendedHalfPlanePoint (Hyperbolic.axisHalfTurnSL 1 (by norm_num) • E w):=Hyperbolic.realSLMobius_action _ _
    rw [he,nielsenAxisSwap_re]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos hpos) (Complex.normSq_pos.mpr (E w).ne_zero)



/-- The genuine closed funnel cut off by an ordinary real gap, including its axis. -/
def nielsenGapClosedFunnel
    (G:Hyperbolic.NielsenHalfPlaneGap) : Set ℍ := G.keptSideᶜ

theorem nielsenGapClosedFunnel_isClosed (G:Hyperbolic.NielsenHalfPlaneGap) :
    IsClosed (nielsenGapClosedFunnel G) := by
  have hc:Continuous (fun z:ℍ=>inner ℝ G.cutNormal (Hyperbolic.halfPlaneKleinCoordinate z)):=
    continuous_const.inner Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.continuous
  have he:G.keptSide={z:ℍ|inner ℝ G.cutNormal (Hyperbolic.halfPlaneKleinCoordinate z)<G.cutThreshold}:=by
    ext z
    exact (G.cut_keptSide z).symm
  change IsClosed G.keptSideᶜ
  rw [he]
  exact (isOpen_lt hc continuous_const).isClosed_compl

theorem nielsenGapClosedFunnel_bounded_re (a b:ℝ) (hab:a<b) (z:ℍ)
    (hz:z∈nielsenGapClosedFunnel (.bounded a b hab)) : a<z.re ∧ z.re<b := by
  have hs:z.im^2≤(z.re-a)*(b-z.re):=le_of_not_gt hz
  have hp:0<(z.re-a)*(b-z.re):=lt_of_lt_of_le (sq_pos_of_pos z.im_pos) hs
  rcases mul_pos_iff.mp hp with ⟨ha,hb⟩|⟨ha,hb⟩ <;> constructor <;> linarith

/-- Distinct actual complementary gaps give disjoint closed funnels when the same
actual Nielsen point lies on both retained sides. -/
theorem nielsenGapClosedFunnel_disjoint (G J:Hyperbolic.NielsenHalfPlaneGap)
    (hd:Disjoint G.carrier J.carrier) (w:ℍ) (hwG:w∈G.keptSide) (hwJ:w∈J.keptSide) :
    Disjoint (nielsenGapClosedFunnel G) (nielsenGapClosedFunnel J) := by
  apply Set.disjoint_left.mpr
  intro z hzG hzJ
  have hdis:=Set.disjoint_left.mp hd
  cases G with
  | bounded a b hab =>
    obtain ⟨ha,hb⟩:=nielsenGapClosedFunnel_bounded_re a b hab z hzG
    cases J with
    | bounded c d hcd =>
      obtain ⟨hc,hd'⟩:=nielsenGapClosedFunnel_bounded_re c d hcd z hzJ
      exact hdis ⟨ha,hb⟩ ⟨hc,hd'⟩
    | left c =>
      have hc:z.re≤c:=le_of_not_gt hzJ
      exact hdis (a:=(a+z.re)/2) (by constructor <;> linarith) (by change (a+z.re)/2<c;linarith)
    | right c =>
      have hc:c≤z.re:=le_of_not_gt hzJ
      exact hdis (a:=(z.re+b)/2) (by constructor <;> linarith) (by change c<(z.re+b)/2;linarith)
  | left b =>
    have hb:z.re≤b:=le_of_not_gt hzG
    cases J with
    | bounded c d hcd =>
      obtain ⟨hc,hd'⟩:=nielsenGapClosedFunnel_bounded_re c d hcd z hzJ
      exact hdis (a:=(c+z.re)/2) (by change (c+z.re)/2<b;linarith) (by constructor <;> linarith)
    | left c =>
      exact hdis (a:=min b c-1) (by change min b c-1<b;linarith [min_le_left b c])
        (by change min b c-1<c;linarith [min_le_right b c])
    | right c =>
      have hc:c≤z.re:=le_of_not_gt hzJ
      change b<w.re at hwG
      change w.re<c at hwJ
      linarith
  | right a =>
    have ha:a≤z.re:=le_of_not_gt hzG
    cases J with
    | bounded c d hcd =>
      obtain ⟨hc,hd'⟩:=nielsenGapClosedFunnel_bounded_re c d hcd z hzJ
      exact hdis (a:=(z.re+d)/2) (by change a<(z.re+d)/2;linarith) (by constructor <;> linarith)
    | left b =>
      have hb:z.re≤b:=le_of_not_gt hzJ
      change w.re<a at hwG
      change b<w.re at hwJ
      linarith
    | right c =>
      exact hdis (a:=max a c+1) (by change a<max a c+1;linarith [le_max_left a c])
        (by change c<max a c+1;linarith [le_max_right a c])

theorem nielsenGap_funnel_strip_interval
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (z : ℍ)
    (hz : z∈nielsenGapClosedFunnel G) (ε : ℝ) (hε : 0<ε) (hy : ε≤z.im)
    (R : ℝ) (hR : |z.re|≤R) :
    ∃c : ℝ,Ioo c (c+ε)⊆G.carrier∩Ioo (-R-2*ε) (R+2*ε) := by
  obtain ⟨hxlo,hxhi⟩ := abs_le.mp hR
  cases G with
  | bounded a b hab =>
    have hsq : z.im^2≤(z.re-a)*(b-z.re):=le_of_not_gt hz
    have hpos : 0<(z.re-a)*(b-z.re):=lt_of_lt_of_le (sq_pos_of_pos z.im_pos) hsq
    have hx : a<z.re ∧ z.re<b := by
      rcases mul_pos_iff.mp hpos with ⟨ha,hb⟩|⟨ha,hb⟩ <;> constructor <;> linarith
    have hwide : ε≤z.re-a ∨ ε≤b-z.re := by
      by_contra hn
      push Not at hn
      have hh : 0<(ε-(z.re-a))*(ε-(b-z.re)):=mul_pos (by linarith [hn.1]) (by linarith [hn.2])
      nlinarith [sq_nonneg (z.im-ε)]
    rcases hwide with hleft|hright
    · refine ⟨z.re-ε,?_⟩
      intro t ht
      change t∈Ioo a b ∧ t∈Ioo (-R-2*ε) (R+2*ε)
      constructor <;> constructor <;> linarith [ht.1,ht.2,hx.1,hx.2]
    · refine ⟨z.re,?_⟩
      intro t ht
      change t∈Ioo a b ∧ t∈Ioo (-R-2*ε) (R+2*ε)
      constructor <;> constructor <;> linarith [ht.1,ht.2,hx.1,hx.2]
  | left b =>
    have hre : z.re≤b:=le_of_not_gt hz
    refine ⟨z.re-ε,?_⟩
    intro t ht
    change t<b ∧ t∈Ioo (-R-2*ε) (R+2*ε)
    constructor
    · linarith [ht.2]
    · constructor <;> linarith [ht.1,ht.2]
  | right a =>
    have hre : a≤z.re:=le_of_not_gt hz
    refine ⟨z.re,?_⟩
    intro t ht
    change a<t ∧ t∈Ioo (-R-2*ε) (R+2*ε)
    constructor
    · linarith [ht.1]
    · constructor <;> linarith [ht.1,ht.2]

/-- The lower interval length gives a genuine uniform positive Lebesgue
measure bound on each actual gap meeting that native compact strip. -/
theorem nielsenGap_funnel_strip_measure_lower
    (G : Hyperbolic.NielsenHalfPlaneGap)
    (z : ℍ)
    (hz : z∈nielsenGapClosedFunnel G) (ε : ℝ) (hε : 0<ε) (hy : ε≤z.im)
    (R : ℝ) (hR : |z.re|≤R) :
    ENNReal.ofReal ε≤volume (G.carrier∩Ioo (-R-2*ε) (R+2*ε)) := by
  obtain ⟨c,hc⟩ := nielsenGap_funnel_strip_interval G z hz ε hε hy R hR
  have hh : volume (Ioo c (c+ε))≤volume (G.carrier∩Ioo (-R-2*ε) (R+2*ε)):=measure_mono hc
  rw [Real.volume_Ioo,show c+ε-c=ε by ring] at hh
  exact hh


/-- Distinct genuine complementary real gaps meeting one fixed bounded
positive-height strip form a finite set; the uniform measure bound is proved. -/
theorem nielsenRealGapFamily_strip_funnel_hits_finite (A : Set ℝ) (hA : IsClosed A)
    (ε : ℝ) (hε : 0<ε) (R : ℝ) :
    {S : Set ℝ | S∈Auxiliary.Topology.nielsenRealGapFamily A ∧ ∃G : Hyperbolic.NielsenHalfPlaneGap,
      G.carrier=S ∧ ∃z∈nielsenGapClosedFunnel G,ε≤z.im ∧ |z.re|≤R}.Finite := by
  classical
  let ι:=Auxiliary.Topology.nielsenRealGapFamily A
  let B:=Ioo (-R-2*ε) (R+2*ε)
  let F (i : ι) : Set ℝ:=i.val∩B
  have hm (i : ι) : MeasurableSet (F i):=
    (Auxiliary.Topology.nielsenRealGapFamily_isOpen hA i.property).measurableSet.inter isOpen_Ioo.measurableSet
  have hd : Pairwise (fun i j : ι=>Disjoint (F i) (F j)) := by
    intro i j hij
    exact (Auxiliary.Topology.nielsenRealGapFamily_pairwiseDisjoint A i.property j.property
      (fun he=>hij (Subtype.ext he))).mono inter_subset_left inter_subset_left
  have hvol : volume (⋃i : ι,F i)≠⊤ := by
    apply ne_top_of_le_ne_top (b:=volume B)
    · rw [Real.volume_Ioo]
      exact ENNReal.ofReal_ne_top
    · apply measure_mono
      exact iUnion_subset (fun _=>inter_subset_right)
  have hf:=Measure.finite_const_le_meas_of_disjoint_iUnion volume
    (ENNReal.ofReal_pos.mpr hε) hm hd hvol
  apply (hf.image (fun i : ι=>i.val)).subset
  rintro S ⟨hS,G,hGS,z,hz,hy,hre⟩
  refine ⟨⟨S,hS⟩,?_,rfl⟩
  change ENNReal.ofReal ε≤volume (S∩B)
  rw [←hGS]
  exact nielsenGap_funnel_strip_measure_lower G z hz ε hε hy R hre

/-- Genuine complete geodesics bounding different complementary real gaps
are locally finite in the actual half-plane. No boundary local-finiteness
or finite-polygon hypothesis is assumed. -/
theorem nielsenRealGapFamily_compact_funnel_hits_finite (A : Set ℝ) (hA : IsClosed A)
    (K : Set ℍ) (hK : IsCompact K) :
    {S : Set ℝ | S∈Auxiliary.Topology.nielsenRealGapFamily A ∧ ∃G : Hyperbolic.NielsenHalfPlaneGap,
      G.carrier=S ∧ (nielsenGapClosedFunnel G∩K).Nonempty}.Finite := by
  rcases K.eq_empty_or_nonempty with rfl|hne
  · simp
  obtain ⟨z,hz,hmin⟩ := hK.exists_isMinOn hne UpperHalfPlane.continuous_im.continuousOn
  obtain ⟨R,hR⟩ := (hK.image UpperHalfPlane.continuous_re).isBounded.subset_closedBall (0:ℝ)
  apply (nielsenRealGapFamily_strip_funnel_hits_finite A hA z.im z.im_pos R).subset
  rintro S ⟨hS,G,hGS,w,hwG,hwK⟩
  refine ⟨hS,G,hGS,w,hwG,hmin hwK,?_⟩
  have hh:=hR (mem_image_of_mem UpperHalfPlane.re hwK)
  simpa only [Metric.mem_closedBall,Real.dist_eq,sub_zero] using hh





/-- The actual closed side opposite the Nielsen point, bounded by the specified whole native line. -/
def nielsenOriginalClosedFunnel {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (L:Hyperbolic.DiscLine)
    (w:P.domain.carrier) : Set P.domain.carrier :=
  (connectedComponentIn (P.finiteCoordinate.symm '' L.carrier)ᶜ w)ᶜ

theorem nielsenOriginalClosedFunnel_chart {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (G:Hyperbolic.NielsenHalfPlaneGap)
    (hG:G.carrier∈Auxiliary.Topology.nielsenRealGapFamily (Hyperbolic.nielsenHalfPlaneRealSet
      (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate
        (P.asFuchsianDisc.nielsenArcNormalizer hNE) H))))
    (hGL:P.finiteCoordinate '' ((nielsenHalfPlaneChart P hNE).symm '' G.line.carrier)=L.carrier)
    (w:P.domain.carrier) (hw:w∈fuchsianNielsenCore P hNE) :
    nielsenHalfPlaneChart P hNE '' nielsenOriginalClosedFunnel P L w=nielsenGapClosedFunnel G := by
  let E:=nielsenHalfPlaneChart P hNE
  have hline:E '' (P.finiteCoordinate.symm '' L.carrier)=G.line.carrier:=by
    rw [←hGL,image_image,image_image]
    simp only [Homeomorph.symm_apply_apply]
    change E '' E.symm '' G.line.carrier=_
    rw [image_image]
    simp only [Homeomorph.apply_symm_apply,Set.image_id']
  have hwG:E w∈G.keptSide:=by
    have hh: E w∈Hyperbolic.nielsenRealArcRegion (Hyperbolic.nielsenHalfPlaneRealSet
        (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate (P.asFuchsianDisc.nielsenArcNormalizer hNE) H))):=by
      rw [←nielsenHalfPlaneChart_core_image P hNE]
      exact mem_image_of_mem E hw
    exact hh G hG
  have hwL:w∉P.finiteCoordinate.symm '' L.carrier:=by
    intro hh
    have he:E w∈G.line.carrier:=hline ▸ mem_image_of_mem E hh
    exact Set.disjoint_left.mp G.keptSide_disjoint_line hwG he
  have he:=E.image_connectedComponentIn (show w∈(P.finiteCoordinate.symm '' L.carrier)ᶜ from hwL)
  have hc:E '' (P.finiteCoordinate.symm '' L.carrier)ᶜ=G.line.carrierᶜ:=by
    rw [E.image_compl,hline]
  rw [hc] at he
  change E '' (connectedComponentIn (P.finiteCoordinate.symm '' L.carrier)ᶜ w)ᶜ=G.keptSideᶜ
  rw [E.image_compl,he]
  exact congrArg compl (G.keptSide_eq_openHalfPlane (E w) hwG).symm

theorem nielsenOriginalClosedFunnel_independent
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (w v:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) (hv:v∈fuchsianNielsenCore P hNE) :
    nielsenOriginalClosedFunnel P L w=nielsenOriginalClosedFunnel P L v := by
  obtain ⟨G,hG,hGL⟩:=hL
  apply (nielsenHalfPlaneChart P hNE).injective.image_injective
  rw [nielsenOriginalClosedFunnel_chart P hNE L G hG hGL w hw,
    nielsenOriginalClosedFunnel_chart P hNE L G hG hGL v hv]

theorem nielsenOriginalClosedFunnel_isClosed
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) : IsClosed (nielsenOriginalClosedFunnel P L w) := by
  obtain ⟨G,hG,hGL⟩:=hL
  apply (nielsenHalfPlaneChart P hNE).isClosed_image.mp
  rw [nielsenOriginalClosedFunnel_chart P hNE L G hG hGL w hw]
  exact nielsenGapClosedFunnel_isClosed G

theorem nielsenOriginalClosedFunnels_pairwiseDisjoint
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) :
    (nielsenBoundaryDiscLineFamily P hNE).PairwiseDisjoint (fun L=>nielsenOriginalClosedFunnel P L w) := by
  intro L hL M hM hne
  obtain ⟨G,hG,hGL⟩:=hL
  obtain ⟨J,hJ,hJM⟩:=hM
  have hneG:G.carrier≠J.carrier:=by
    intro he
    have heL:=nielsenGap_line_eq_of_carrier_eq G J he
    exact hne (nielsen_discLine_carrier_injective (hGL.symm.trans (heL ▸ hJM)))
  have hwN:nielsenHalfPlaneChart P hNE w∈Hyperbolic.nielsenRealArcRegion (Hyperbolic.nielsenHalfPlaneRealSet
      (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate (P.asFuchsianDisc.nielsenArcNormalizer hNE) H))):=by
    rw [←nielsenHalfPlaneChart_core_image P hNE]
    exact mem_image_of_mem _ hw
  have hd:=nielsenGapClosedFunnel_disjoint G J
    (Auxiliary.Topology.nielsenRealGapFamily_pairwiseDisjoint _ hG hJ hneG) _ (hwN G hG) (hwN J hJ)
  apply Set.disjoint_left.mpr
  intro z hzL hzM
  apply Set.disjoint_left.mp hd
  · rw [←nielsenOriginalClosedFunnel_chart P hNE L G hG hGL w hw]
    exact mem_image_of_mem _ hzL
  · rw [←nielsenOriginalClosedFunnel_chart P hNE M J hJ hJM w hw]
    exact mem_image_of_mem _ hzM

/-- The original whole group genuinely permutes the closed funnels. -/
theorem nielsenOriginalClosedFunnel_image {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) (g:H) :
    ∃M∈nielsenBoundaryDiscLineFamily P hNE,
      g • nielsenOriginalClosedFunnel P L w=nielsenOriginalClosedFunnel P M w := by
  obtain ⟨M,hM,heM⟩:=nielsenBoundary_original_line_image P hNE L hL g
  have hwL:w∉P.finiteCoordinate.symm '' L.carrier:=by
    rintro ⟨x,hx,hxw⟩
    have hh:=nielsenBoundaryDiscLineFamily_subset_frontier P hNE L hL hx
    obtain ⟨y,hy,hyx⟩:=hh
    have hyw:y=w:=(P.finiteCoordinate.symm_apply_apply y).symm.trans (congrArg P.finiteCoordinate.symm hyx) |>.trans hxw
    exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr (fuchsianNielsenCore_isOpen P hNE))
      hy (hyw.symm ▸ hw)
  have he: (Homeomorph.smul g) '' connectedComponentIn (P.finiteCoordinate.symm '' L.carrier)ᶜ w=
      connectedComponentIn (P.finiteCoordinate.symm '' M.carrier)ᶜ (g • w):=by
    have hh:=(Homeomorph.smul g).image_connectedComponentIn
      (show w∈(P.finiteCoordinate.symm '' L.carrier)ᶜ from hwL)
    have hc:(Homeomorph.smul g) '' (P.finiteCoordinate.symm '' L.carrier)ᶜ=
        (P.finiteCoordinate.symm '' M.carrier)ᶜ:=by
      rw [(Homeomorph.smul g).image_compl]
      exact congrArg compl heM
    rw [hc] at hh
    exact hh
  refine ⟨M,hM,?_⟩
  change (Homeomorph.smul g) '' (connectedComponentIn (P.finiteCoordinate.symm '' L.carrier)ᶜ w)ᶜ=_
  rw [(Homeomorph.smul g).image_compl,he]
  exact nielsenOriginalClosedFunnel_independent P hNE M hM (g • w) w
    (fuchsianNielsenCore_invariant P hNE g w hw) hw

theorem nielsenOriginalClosedFunnels_compact_hits_finite
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) (K:Set P.domain.carrier) (hK:IsCompact K) :
    {L:Hyperbolic.DiscLine|L∈nielsenBoundaryDiscLineFamily P hNE ∧
      (nielsenOriginalClosedFunnel P L w∩K).Nonempty}.Finite := by
  let A:=Hyperbolic.nielsenHalfPlaneRealSet
    (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate
      (P.asFuchsianDisc.nielsenArcNormalizer hNE) H))
  let E:=nielsenHalfPlaneChart P hNE
  let F:={S:Set ℝ|S∈Auxiliary.Topology.nielsenRealGapFamily A ∧ ∃G:Hyperbolic.NielsenHalfPlaneGap,
    G.carrier=S ∧ (nielsenGapClosedFunnel G∩E '' K).Nonempty}
  have hF:F.Finite:=nielsenRealGapFamily_compact_funnel_hits_finite A
    (Hyperbolic.nielsenHalfPlaneRealSet_isClosed _ (DiscreteGroups.mobiusLimitSet_isClosed _)) (E '' K) (hK.image
      E.continuous)
  let B (S:Set ℝ):Set Hyperbolic.DiscLine:={L|∃G:Hyperbolic.NielsenHalfPlaneGap,G.carrier=S ∧
    P.finiteCoordinate '' (E.symm '' G.line.carrier)=L.carrier}
  have hB (S:Set ℝ):(B S).Finite:=by
    apply Set.Subsingleton.finite
    rintro L ⟨G,hGS,hGL⟩ M ⟨J,hJS,hJM⟩
    have he:=nielsenGap_line_eq_of_carrier_eq G J (hGS.trans hJS.symm)
    exact nielsen_discLine_carrier_injective (hGL.symm.trans (he ▸ hJM))
  apply (hF.biUnion (fun S _=>hB S)).subset
  rintro L ⟨hL,x,hxF,hxK⟩
  obtain ⟨G,hG,hGL⟩:=hL
  have hxG:E x∈nielsenGapClosedFunnel G:=by
    rw [←nielsenOriginalClosedFunnel_chart P hNE L G hG hGL w hw]
    exact mem_image_of_mem E hxF
  have hFS:G.carrier∈F:=⟨hG,G,rfl,E x,hxG,x,hxK,rfl⟩
  exact mem_iUnion₂.mpr ⟨G.carrier,hFS,G,rfl,hGL⟩

/-- Closed funnels are locally finite in the actual original open disc. -/
theorem nielsenOriginalClosedFunnels_locallyFinite
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) :
    LocallyFinite (fun L:nielsenBoundaryDiscLineFamily P hNE=>nielsenOriginalClosedFunnel P L.val w) := by
  classical
  intro x
  obtain ⟨K,hK,hxK⟩:=exists_compact_mem_nhds x
  have hf:=nielsenOriginalClosedFunnels_compact_hits_finite P hNE w hw K hK
  refine ⟨K,hxK,?_⟩
  apply (hf.preimage (f:=fun L:nielsenBoundaryDiscLineFamily P hNE=>L.val)
    Subtype.val_injective.injOn).subset
  rintro L ⟨y,hyL,hyK⟩
  exact ⟨L.property,y,hyL,hyK⟩

/-- Every original translate is either the same true closed funnel or is disjoint from it. -/
theorem nielsenOriginalClosedFunnel_stable {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) (g:H) :
    g • nielsenOriginalClosedFunnel P L w=nielsenOriginalClosedFunnel P L w ∨
      Disjoint (g • nielsenOriginalClosedFunnel P L w) (nielsenOriginalClosedFunnel P L w) := by
  obtain ⟨M,hM,heM⟩:=nielsenOriginalClosedFunnel_image P hNE L hL w hw g
  rw [heM]
  by_cases he:M=L
  · exact Or.inl (congrArg (fun N=>nielsenOriginalClosedFunnel P N w) he)
  · exact Or.inr (nielsenOriginalClosedFunnels_pairwiseDisjoint P hNE w hw hM hL he)

theorem nielsenOriginalClosedFunnel_inter_core_closure
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) :
    nielsenOriginalClosedFunnel P L w∩closure (fuchsianNielsenCore P hNE)=
      P.finiteCoordinate.symm '' L.carrier := by
  obtain ⟨G,hG,hGL⟩:=hL
  let E:=nielsenHalfPlaneChart P hNE
  apply Set.Subset.antisymm
  · rintro z ⟨hzF,hzN⟩
    have hzG:E z∈nielsenGapClosedFunnel G:=by
      rw [←nielsenOriginalClosedFunnel_chart P hNE L G hG hGL w hw]
      exact mem_image_of_mem E hzF
    have hzC:E z∈closure (Hyperbolic.nielsenRealArcRegion (Hyperbolic.nielsenHalfPlaneRealSet
        (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate (P.asFuchsianDisc.nielsenArcNormalizer hNE) H)))):=by
      rw [←nielsenHalfPlaneChart_core_image P hNE,←E.image_closure]
      exact mem_image_of_mem E hzN
    have hclosed:IsClosed {u:ℍ|inner ℝ G.cutNormal (Hyperbolic.halfPlaneKleinCoordinate u)≤G.cutThreshold}:=
      isClosed_le (continuous_const.inner
        Hyperbolic.isOpenEmbedding_halfPlaneKleinCoordinate.continuous) continuous_const
    have hle:inner ℝ G.cutNormal (Hyperbolic.halfPlaneKleinCoordinate (E z))≤G.cutThreshold:=
      closure_minimal (fun u (hu:u∈Hyperbolic.nielsenRealArcRegion _)=>(G.cut_keptSide u).mpr (hu G hG) |>.le)
        hclosed hzC
    have hge:G.cutThreshold≤ inner ℝ G.cutNormal (Hyperbolic.halfPlaneKleinCoordinate (E z)):=by
      apply le_of_not_gt
      intro hh
      exact hzG ((G.cut_keptSide (E z)).mp hh)
    have hzLine:E z∈G.line.carrier:=(Hyperbolic.NielsenHalfPlaneGap.cut_line_iff G (E z)).mpr (le_antisymm hle hge)
    have hzL:P.finiteCoordinate z∈L.carrier:=by
      rw [←hGL]
      exact ⟨z,⟨E z,hzLine,E.symm_apply_apply z⟩,rfl⟩
    exact ⟨P.finiteCoordinate z,hzL,P.finiteCoordinate.symm_apply_apply z⟩
  · intro z hz
    refine ⟨?_,?_⟩
    · intro hc
      exact connectedComponentIn_subset _ _ hc hz
    · obtain ⟨v,hv,rfl⟩:=hz
      have hvF:=nielsenBoundaryDiscLineFamily_subset_frontier P hNE L ⟨G,hG,hGL⟩ hv
      obtain ⟨x,hx,hxv⟩:=hvF
      have he:P.finiteCoordinate.symm v=x:=by rw [←hxv,P.finiteCoordinate.symm_apply_apply]
      rw [he]
      exact frontier_subset_closure hx

/-- The genuine whole original disc is covered by the closed Nielsen core and the genuine closed funnels. -/
theorem nielsenOriginalClosedFunnels_cover {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) :
    (univ:Set P.domain.carrier)=closure (fuchsianNielsenCore P hNE)∪
      ⋃L:nielsenBoundaryDiscLineFamily P hNE,nielsenOriginalClosedFunnel P L.val w := by
  apply Set.Subset.antisymm
  · intro x _hx
    by_cases hxN:x∈fuchsianNielsenCore P hNE
    · exact Or.inl (subset_closure hxN)
    · right
      let E:=nielsenHalfPlaneChart P hNE
      have hn:E x∉Hyperbolic.nielsenRealArcRegion (Hyperbolic.nielsenHalfPlaneRealSet
          (DiscreteGroups.mobiusLimitSet (DiscreteGroups.Action.Actions.subgroupConjugate (P.asFuchsianDisc.nielsenArcNormalizer hNE) H))):=by
        rw [←nielsenHalfPlaneChart_core_image P hNE]
        exact fun he=>hxN (E.injective.mem_set_image.mp he)
      change ¬∀G:Hyperbolic.NielsenHalfPlaneGap,G.carrier∈Auxiliary.Topology.nielsenRealGapFamily _→E x∈G.keptSide at hn
      push Not at hn
      obtain ⟨G,hG,hxG⟩:=hn
      obtain ⟨L,hGL⟩:=nielsenGap_original_native_line P hNE G
      have hL:L∈nielsenBoundaryDiscLineFamily P hNE:=⟨G,hG,hGL⟩
      apply mem_iUnion.mpr
      refine ⟨⟨L,hL⟩,?_⟩
      have he:E x∈E '' nielsenOriginalClosedFunnel P L w:=by
        rw [nielsenOriginalClosedFunnel_chart P hNE L G hG hGL w hw]
        exact hxG
      exact E.injective.mem_set_image.mp he
  · exact subset_univ _

theorem nielsenOriginalClosedFunnel_invariant_iff_axis
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) (g:H) :
    g • nielsenOriginalClosedFunnel P L w=nielsenOriginalClosedFunnel P L w ↔
      g • (P.finiteCoordinate.symm '' L.carrier)=P.finiteCoordinate.symm '' L.carrier := by
  constructor
  · intro he
    rw [←nielsenOriginalClosedFunnel_inter_core_closure P hNE L hL w hw,
      smul_set_inter,he,fuchsianNielsenCore_smul_closure]
  · intro he
    have hwL:w∉P.finiteCoordinate.symm '' L.carrier:=by
      rintro ⟨v,hv,hvw⟩
      obtain ⟨x,hx,hxv⟩:=nielsenBoundaryDiscLineFamily_subset_frontier P hNE L hL hv
      have hxw:x=w:=(P.finiteCoordinate.symm_apply_apply x).symm.trans (congrArg P.finiteCoordinate.symm
        hxv) |>.trans hvw
      exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr (fuchsianNielsenCore_isOpen P hNE))
        hx (hxw.symm ▸ hw)
    have hc: (Homeomorph.smul g) '' (P.finiteCoordinate.symm '' L.carrier)ᶜ=
        (P.finiteCoordinate.symm '' L.carrier)ᶜ:=by
      rw [(Homeomorph.smul g).image_compl]
      exact congrArg compl he
    have hcc:=(Homeomorph.smul g).image_connectedComponentIn
      (show w∈(P.finiteCoordinate.symm '' L.carrier)ᶜ from hwL)
    rw [hc] at hcc
    change (Homeomorph.smul g) '' (connectedComponentIn (P.finiteCoordinate.symm '' L.carrier)ᶜ w)ᶜ=_
    rw [(Homeomorph.smul g).image_compl,hcc]
    exact nielsenOriginalClosedFunnel_independent P hNE L hL (g • w) w
      (fuchsianNielsenCore_invariant P hNE g w hw) hw



/-- Each true closed funnel has a closed image in the original whole-group quotient. -/
theorem nielsenOriginalClosedFunnel_projection_isClosed
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) :
    IsClosed (Surfaces.mobiusDomainProjection P.domain '' nielsenOriginalClosedFunnel P L w) := by
  classical
  let I:=nielsenBoundaryDiscLineFamily P hNE
  let F (i:I):Set P.domain.carrier:=nielsenOriginalClosedFunnel P i.val w
  let J: Set I:={i|∃g:H,g • nielsenOriginalClosedFunnel P L w=F i}
  have hlf:LocallyFinite (fun i:J=>F i.val):=
    (nielsenOriginalClosedFunnels_locallyFinite P hNE w hw).comp_injective Subtype.val_injective
  have hclosed:IsClosed (⋃i:J,F i.val):=hlf.isClosed_iUnion
    (fun i=>nielsenOriginalClosedFunnel_isClosed P hNE i.val.val i.val.property w hw)
  apply (Surfaces.mobiusDomainProjection_isOpenQuotientMap P.domain).isQuotientMap.isCoinducing.isClosed_preimage.mp
  have he:Surfaces.mobiusDomainProjection P.domain ⁻¹'
      (Surfaces.mobiusDomainProjection P.domain '' nielsenOriginalClosedFunnel P L w)=⋃i:J,F i.val:=by
    ext x
    constructor
    · rintro ⟨y,hy,hxy⟩
      obtain ⟨g,hg⟩:=Quotient.exact hxy.symm
      obtain ⟨M,hM,heM⟩:=nielsenOriginalClosedFunnel_image P hNE L hL w hw g
      refine mem_iUnion.mpr ⟨⟨⟨M,hM⟩,g,heM⟩,?_⟩
      change x∈nielsenOriginalClosedFunnel P M w
      rw [←heM]
      exact ⟨y,hy,hg⟩
    · intro hx
      obtain ⟨i,hxi⟩:=mem_iUnion.mp hx
      obtain ⟨g,hgi⟩:=i.property
      rw [←hgi] at hxi
      obtain ⟨y,hy,rfl⟩:=hxi
      exact ⟨y,hy,(Surfaces.mobiusDomainProjection_smul P.domain g y).symm⟩
  rwa [he]

/-- A true closed funnel has an actual open isolating neighborhood relative to its orbit saturation. -/
theorem nielsenOriginalClosedFunnel_isolating_open
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) :
    ∃O:Set P.domain.carrier,IsOpen O ∧ nielsenOriginalClosedFunnel P L w⊆O ∧
      ∀x∈nielsenOriginalClosedFunnel P L w,∀y∈O,
        Surfaces.mobiusDomainProjection P.domain y=Surfaces.mobiusDomainProjection P.domain x→
        y∈nielsenOriginalClosedFunnel P L w := by
  classical
  let I:=nielsenBoundaryDiscLineFamily P hNE
  let F (i:I):Set P.domain.carrier:=nielsenOriginalClosedFunnel P i.val w
  let J: Set I:={i|i.val≠L}
  let O:=(⋃i:J,F i.val)ᶜ
  have hlf:LocallyFinite (fun i:J=>F i.val):=
    (nielsenOriginalClosedFunnels_locallyFinite P hNE w hw).comp_injective Subtype.val_injective
  have hO:IsOpen O:=(hlf.isClosed_iUnion
    (fun i=>nielsenOriginalClosedFunnel_isClosed P hNE i.val.val i.val.property w hw)).isOpen_compl
  refine ⟨O,hO,?_,?_⟩
  · intro x hx hxo
    obtain ⟨i,hxi⟩:=mem_iUnion.mp hxo
    exact Set.disjoint_left.mp
      (nielsenOriginalClosedFunnels_pairwiseDisjoint P hNE w hw hL i.val.property (Ne.symm i.property)) hx hxi
  · intro x hx y hy he
    obtain ⟨g,hg⟩:=Quotient.exact he
    obtain ⟨M,hM,heM⟩:=nielsenOriginalClosedFunnel_image P hNE L hL w hw g
    have hyM:y∈nielsenOriginalClosedFunnel P M w:=by
      rw [←heM]
      exact ⟨x,hx,hg⟩
    by_cases hML:M=L
    · exact hML ▸ hyM
    · exact False.elim (hy (mem_iUnion.mpr ⟨⟨⟨M,hM⟩,hML⟩,hyM⟩))

def nielsenClosedFunnelRangeProjection {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (L:Hyperbolic.DiscLine) (w:P.domain.carrier) :
    nielsenOriginalClosedFunnel P L w→
      ↥(Surfaces.mobiusDomainProjection P.domain '' nielsenOriginalClosedFunnel P L w) :=
  fun x=>⟨Surfaces.mobiusDomainProjection P.domain x.val,⟨x.val,x.property,rfl⟩⟩

/-- The closed funnel's own orbit topology is exactly its actual subspace topology in the whole quotient. -/
theorem nielsenClosedFunnelRangeProjection_isOpenQuotientMap
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) :
    IsOpenQuotientMap (nielsenClosedFunnelRangeProjection P L w) := by
  obtain ⟨O,hO,hFO,hiso⟩:=nielsenOriginalClosedFunnel_isolating_open P hNE L hL w hw
  refine ⟨?_,?_,?_⟩
  · rintro ⟨q,x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,rfl⟩
  · exact ((Surfaces.mobiusDomainProjection_continuous P.domain).comp continuous_subtype_val).subtype_mk _
  · intro U hU
    obtain ⟨V,hV,hVU⟩:=IsInducing.subtypeVal.isOpen_iff.mp hU
    have he:nielsenClosedFunnelRangeProjection P L w '' U=
        Subtype.val ⁻¹' (Surfaces.mobiusDomainProjection P.domain '' (V∩O)):=by
      ext q
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact ⟨x.val,⟨by change x∈Subtype.val ⁻¹' V;rw [hVU];exact hx,hFO x.property⟩,rfl⟩
      · rintro ⟨y,⟨hyV,hyO⟩,hyq⟩
        obtain ⟨x,hx,hxq⟩:=q.property
        have hyF:=hiso x hx y hyO (hyq.trans hxq.symm)
        let z:nielsenOriginalClosedFunnel P L w:=⟨y,hyF⟩
        refine ⟨z,?_,?_⟩
        · rw [←hVU]
          exact hyV
        · exact Subtype.ext hyq
    rw [he]
    exact ((Surfaces.mobiusDomainProjection_isOpenQuotientMap P.domain).isOpenMap _ (hV.inter hO)).preimage
      continuous_subtype_val



theorem nielsenImaginaryAxis_native_image :
    Hyperbolic.extendedHalfPlanePoint '' (Hyperbolic.HalfPlaneLine.vertical 0).carrier=Hyperbolic.extendedImaginaryAxis := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z,hz,rfl⟩
    refine ⟨Real.log z.im,?_⟩
    apply congrArg Hyperbolic.extendedHalfPlanePoint
    apply UpperHalfPlane.ext_re_im
    · exact hz.symm
    · exact Real.exp_log z.im_pos
  · rintro _ ⟨t,rfl⟩
    exact ⟨Hyperbolic.imaginaryAxisParam t,rfl,rfl⟩

theorem nielsenOriginalAxis_chart_image {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (L:Hyperbolic.DiscLine)
    (f:H)
    (M:FuchsianAxisModel P.asFuchsianDisc f.val)
    (hML:M.carrier=Subtype.val '' (P.finiteCoordinate.symm '' L.carrier))
    (q:Mobius.complexMobiusGroup)
    (hqD:q.val '' P.domain.carrier=Hyperbolic.openHalfPlaneSet)
    (hqM:q.val '' M.carrier=Hyperbolic.extendedImaginaryAxis) :
    geometricHalfPlaneChart P.asFuchsianDisc q hqD '' (P.finiteCoordinate.symm '' L.carrier)=
      (Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
  apply nielsen_halfPlanePoint_isOpenEmbedding.injective.image_injective
  calc
    Hyperbolic.extendedHalfPlanePoint '' (geometricHalfPlaneChart P.asFuchsianDisc q hqD ''
        (P.finiteCoordinate.symm '' L.carrier))=
        q.val '' (Subtype.val '' (P.finiteCoordinate.symm '' L.carrier)):=by
      simp only [image_image]
      apply image_congr
      intro x _hx
      exact geometricHalfPlaneChart_extended P.asFuchsianDisc q hqD (P.finiteCoordinate.symm x)
    _=Hyperbolic.extendedImaginaryAxis:=by rw [←hML,hqM]
    _=Hyperbolic.extendedHalfPlanePoint '' (Hyperbolic.HalfPlaneLine.vertical
      0).carrier:=nielsenImaginaryAxis_native_image.symm

theorem nielsenOriginalClosedFunnel_oriented_chart
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (L:Hyperbolic.DiscLine) (w:P.domain.carrier)
    (q:Mobius.complexMobiusGroup)
    (hqD:q.val '' P.domain.carrier=Hyperbolic.openHalfPlaneSet)
    (hqL:geometricHalfPlaneChart P.asFuchsianDisc q hqD ''
      (P.finiteCoordinate.symm '' L.carrier)=(Hyperbolic.HalfPlaneLine.vertical 0).carrier)
    (hw:(geometricHalfPlaneChart P.asFuchsianDisc q hqD w).re<0) :
    geometricHalfPlaneChart P.asFuchsianDisc q hqD '' nielsenOriginalClosedFunnel P L w=
      nielsenRightFunnel := by
  let E:=geometricHalfPlaneChart P.asFuchsianDisc q hqD
  have hwL:w∉P.finiteCoordinate.symm '' L.carrier:=by
    intro hh
    have he:E w∈(Hyperbolic.HalfPlaneLine.vertical 0).carrier:=hqL ▸ mem_image_of_mem E hh
    exact hw.ne he
  have he:=E.image_connectedComponentIn (show w∈(P.finiteCoordinate.symm '' L.carrier)ᶜ from hwL)
  have hc:E '' (P.finiteCoordinate.symm '' L.carrier)ᶜ=(Hyperbolic.HalfPlaneLine.vertical 0).carrierᶜ:=by
    rw [E.image_compl,hqL]
  rw [hc] at he
  change E '' (connectedComponentIn (P.finiteCoordinate.symm '' L.carrier)ᶜ w)ᶜ=_
  rw [E.image_compl,he]
  change (Hyperbolic.openHHalfPlane (.vertical 0) (E w))ᶜ=_
  rw [Hyperbolic.hReCutLt_eq_openHalfPlane 0 (E w) hw]
  ext z
  change ¬z.re<0 ↔ 0≤z.re/z.im
  rw [not_lt,le_div_iff₀ z.im_pos,zero_mul]

def nielsenOriginalClosedFunnelNativeHomeomorph
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (L:Hyperbolic.DiscLine) (w:P.domain.carrier)
    (q:Mobius.complexMobiusGroup)
    (hqD:q.val '' P.domain.carrier=Hyperbolic.openHalfPlaneSet)
    (hqF:geometricHalfPlaneChart P.asFuchsianDisc q hqD '' nielsenOriginalClosedFunnel P L w=
      nielsenRightFunnel) : nielsenOriginalClosedFunnel P L w ≃ₜ nielsenRightFunnel :=
  ((geometricHalfPlaneChart P.asFuchsianDisc q hqD).image _).trans (Homeomorph.setCongr hqF)

theorem nielsenOriginalClosedFunnel_positive_normal_form
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) (f:H) (hf:IsBoundaryHyperbolic P.asFuchsianDisc f)
    (M:FuchsianAxisModel P.asFuchsianDisc f.val)
    (hML:M.carrier=Subtype.val '' (P.finiteCoordinate.symm '' L.carrier)) :
    ∃q:Mobius.complexMobiusGroup,∃l:ℝ,∃_hl:0<l,
      ∃hqD:q.val '' P.domain.carrier=Hyperbolic.openHalfPlaneSet,
      q.val '' M.carrier=Hyperbolic.extendedImaginaryAxis ∧
      DiscreteGroups.Action.Actions.subgroupConjugate q (Surfaces.mobiusSetStabilizer H M.carrier)=
        Subgroup.zpowers (Surfaces.stableAxisDilation l) ∧
      geometricHalfPlaneChart P.asFuchsianDisc q hqD '' nielsenOriginalClosedFunnel P L w=nielsenRightFunnel := by
  have hwM:w.val∉M.carrier:=by
    rw [hML]
    intro hh
    have hx:w∈P.finiteCoordinate.symm '' L.carrier:=Subtype.val_injective.mem_set_image.mp hh
    obtain ⟨v,hv,hvw⟩:=hx
    obtain ⟨x,hx,hxv⟩:=nielsenBoundaryDiscLineFamily_subset_frontier P hNE L hL hv
    have hxw:x=w:=(P.finiteCoordinate.symm_apply_apply x).symm.trans (congrArg P.finiteCoordinate.symm hxv) |>.trans hvw
    exact Set.disjoint_left.mp (disjoint_frontier_iff_isOpen.mpr (fuchsianNielsenCore_isOpen P hNE))
      hx (hxw.symm ▸ hw)
  obtain ⟨q,l,hl,hqD,hqM,hqK,hqw⟩:=boundaryHyperbolic_axis_left_point_normal_form
    P.asFuchsianDisc hNE f hf M w hwM
  exact ⟨q,l,hl,hqD,hqM,hqK,nielsenOriginalClosedFunnel_oriented_chart P L w q hqD
    (nielsenOriginalAxis_chart_image P L f M hML q hqD hqM) hqw⟩



theorem nielsenOriginalAxis_stabilizer_mem {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (L:Hyperbolic.DiscLine)
    (f:H)
    (M:FuchsianAxisModel P.asFuchsianDisc f.val)
    (hML:M.carrier=Subtype.val '' (P.finiteCoordinate.symm '' L.carrier))
    (g:H) (hg:g • (P.finiteCoordinate.symm '' L.carrier)=P.finiteCoordinate.symm '' L.carrier) :
    g.val∈Surfaces.mobiusSetStabilizer H M.carrier := by
  refine ⟨g.property,?_⟩
  rw [hML]
  calc
    g.val.val '' (Subtype.val '' (P.finiteCoordinate.symm '' L.carrier))=
        Subtype.val '' (g • (P.finiteCoordinate.symm '' L.carrier)):=by
      ext z
      constructor
      · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
        exact ⟨g • x,⟨x,hx,rfl⟩,rfl⟩
      · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
        exact ⟨x.val,⟨x,hx,rfl⟩,rfl⟩
    _=Subtype.val '' (P.finiteCoordinate.symm '' L.carrier):=congrArg (image Subtype.val) hg

theorem nielsenClosedFunnel_projection_fiber
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) (f:H) (M:FuchsianAxisModel P.asFuchsianDisc f.val)
    (hML:M.carrier=Subtype.val '' (P.finiteCoordinate.symm '' L.carrier))
    (q:Mobius.complexMobiusGroup)
    (hqD:q.val '' P.domain.carrier=Hyperbolic.openHalfPlaneSet)
    (l:ℝ)
    (hqK:DiscreteGroups.Action.Actions.subgroupConjugate q (Surfaces.mobiusSetStabilizer H M.carrier)=
      Subgroup.zpowers (Surfaces.stableAxisDilation l))
    (hqF:geometricHalfPlaneChart P.asFuchsianDisc q hqD '' nielsenOriginalClosedFunnel P L w=nielsenRightFunnel)
    (x y:nielsenOriginalClosedFunnel P L w) :
    nielsenClosedFunnelRangeProjection P L w x=nielsenClosedFunnelRangeProjection P L w y ↔
      (MulAction.orbitRel (Subgroup.zpowers (Surfaces.stableAxisDilation l)) Mobius.ExtendedComplex)
        (Mobius.halfPlaneBoundaryPoint (nielsenOriginalClosedFunnelNativeHomeomorph P L w q hqD hqF x).val)
        (Mobius.halfPlaneBoundaryPoint (nielsenOriginalClosedFunnelNativeHomeomorph P L w q hqD hqF y).val) := by
  let E:=geometricHalfPlaneChart P.asFuchsianDisc q hqD
  have hx:Mobius.halfPlaneBoundaryPoint (nielsenOriginalClosedFunnelNativeHomeomorph P L w q hqD hqF x).val=
      q.val x.val.val:=geometricHalfPlaneChart_extended P.asFuchsianDisc q hqD x.val
  have hy:Mobius.halfPlaneBoundaryPoint (nielsenOriginalClosedFunnelNativeHomeomorph P L w q hqD hqF y).val=
      q.val y.val.val:=geometricHalfPlaneChart_extended P.asFuchsianDisc q hqD y.val
  constructor
  · intro he
    have hxy:Surfaces.mobiusDomainProjection P.domain x.val=Surfaces.mobiusDomainProjection P.domain y.val:=congrArg Subtype.val he
    obtain ⟨g,hg⟩:=Quotient.exact hxy
    have hgF:g • nielsenOriginalClosedFunnel P L w=nielsenOriginalClosedFunnel P L w:=by
      rcases nielsenOriginalClosedFunnel_stable P hNE L hL w hw g with heF|hd
      · exact heF
      · exact False.elim (Set.disjoint_left.mp hd ⟨y.val,y.property,hg⟩ x.property)
    have hgL: g • (P.finiteCoordinate.symm '' L.carrier)=P.finiteCoordinate.symm '' L.carrier:=
      (nielsenOriginalClosedFunnel_invariant_iff_axis P hNE L hL w hw g).mp hgF
    have hgK:=nielsenOriginalAxis_stabilizer_mem P L f M hML g hgL
    have hk:q*g.val*q⁻¹∈Subgroup.zpowers (Surfaces.stableAxisDilation l):=by
      rw [←hqK]
      exact (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q _ _).mpr ⟨g.val,hgK,rfl⟩
    refine ⟨⟨q*g.val*q⁻¹,hk⟩,?_⟩
    change (q*g.val*q⁻¹).val
      (Mobius.halfPlaneBoundaryPoint (nielsenOriginalClosedFunnelNativeHomeomorph P L w q hqD hqF y).val)=
        Mobius.halfPlaneBoundaryPoint (nielsenOriginalClosedFunnelNativeHomeomorph P L w q hqD hqF x).val
    rw [hy,hx]
    change q.val (g.val.val (q.val.symm (q.val y.val.val)))=q.val x.val.val
    rw [q.val.symm_apply_apply]
    exact congrArg q.val (congrArg Subtype.val hg)
  · rintro ⟨k,hk⟩
    have hkQ:k.val∈DiscreteGroups.Action.Actions.subgroupConjugate q (Surfaces.mobiusSetStabilizer H
      M.carrier):=hqK.symm ▸ k.property
    obtain ⟨a,ha,hea⟩:=(DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q _ k.val).mp hkQ
    change k.val.val
      (Mobius.halfPlaneBoundaryPoint (nielsenOriginalClosedFunnelNativeHomeomorph P L w q hqD hqF y).val)=
        Mobius.halfPlaneBoundaryPoint (nielsenOriginalClosedFunnelNativeHomeomorph P L w q hqD hqF x).val at hk
    rw [hy,hx,←hea] at hk
    have haxy:a.val y.val.val=x.val.val:=by
      apply q.val.injective
      change q.val (a.val (q.val.symm (q.val y.val.val)))=q.val x.val.val at hk
      rwa [q.val.symm_apply_apply] at hk
    apply Subtype.ext
    apply Quotient.sound
    exact ⟨⟨a,ha.1⟩,Subtype.ext haxy⟩

/-- Genuine closed funnel coordinates on its actual image in the original whole-group quotient. -/
def nielsenOriginalClosedFunnelQuotientCircle
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) (f:H) (M:FuchsianAxisModel P.asFuchsianDisc f.val)
    (hML:M.carrier=Subtype.val '' (P.finiteCoordinate.symm '' L.carrier))
    (q:Mobius.complexMobiusGroup)
    (hqD:q.val '' P.domain.carrier=Hyperbolic.openHalfPlaneSet)
    (l:ℝ)
    (hl:l≠0)
    (hqK:DiscreteGroups.Action.Actions.subgroupConjugate q (Surfaces.mobiusSetStabilizer H M.carrier)=
      Subgroup.zpowers (Surfaces.stableAxisDilation l))
    (hqF:geometricHalfPlaneChart P.asFuchsianDisc q hqD '' nielsenOriginalClosedFunnel P L w=nielsenRightFunnel) :
    ↥(Surfaces.mobiusDomainProjection P.domain '' nielsenOriginalClosedFunnel P L w) ≃ₜ Circle×Ici (0:ℝ) := by
  let E:=nielsenOriginalClosedFunnelNativeHomeomorph P L w q hqD hqF
  let F:C(nielsenOriginalClosedFunnel P L w,
      ↥(Surfaces.mobiusDomainProjection P.domain '' nielsenOriginalClosedFunnel P L w)):=
    ⟨nielsenClosedFunnelRangeProjection P L w,
      (nielsenClosedFunnelRangeProjection_isOpenQuotientMap P hNE L hL w hw).continuous⟩
  have hF:IsQuotientMap F:=
    (nielsenClosedFunnelRangeProjection_isOpenQuotientMap P hNE L hL w hw).isQuotientMap
  exact hF.homeomorph.symm.trans ((Homeomorph.Quotient.congr E
    (fun x y=>nielsenClosedFunnel_projection_fiber P hNE L hL w hw f M hML q hqD l hqK hqF x y)).trans
      (nielsenRightFunnelQuotientCircle l hl))

theorem nielsenOriginalClosedFunnelQuotientCircle_transverse
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) (f:H) (M:FuchsianAxisModel P.asFuchsianDisc f.val)
    (hML:M.carrier=Subtype.val '' (P.finiteCoordinate.symm '' L.carrier))
    (q:Mobius.complexMobiusGroup)
    (hqD:q.val '' P.domain.carrier=Hyperbolic.openHalfPlaneSet)
    (l:ℝ)
    (hl:l≠0)
    (hqK:DiscreteGroups.Action.Actions.subgroupConjugate q (Surfaces.mobiusSetStabilizer H M.carrier)=
      Subgroup.zpowers (Surfaces.stableAxisDilation l))
    (hqF:geometricHalfPlaneChart P.asFuchsianDisc q hqD '' nielsenOriginalClosedFunnel P L w=nielsenRightFunnel)
    (x:nielsenOriginalClosedFunnel P L w) :
    ((nielsenOriginalClosedFunnelQuotientCircle P hNE L hL w hw f M hML q hqD l hl hqK hqF)
      (nielsenClosedFunnelRangeProjection P L w x)).2.val=
      (geometricHalfPlaneChart P.asFuchsianDisc q hqD x.val).re/
        (geometricHalfPlaneChart P.asFuchsianDisc q hqD x.val).im := by
  let E:=nielsenOriginalClosedFunnelNativeHomeomorph P L w q hqD hqF
  let F:C(nielsenOriginalClosedFunnel P L w,
      ↥(Surfaces.mobiusDomainProjection P.domain '' nielsenOriginalClosedFunnel P L w)):=
    ⟨nielsenClosedFunnelRangeProjection P L w,
      (nielsenClosedFunnelRangeProjection_isOpenQuotientMap P hNE L hL w hw).continuous⟩
  have hF:IsQuotientMap F:=
    (nielsenClosedFunnelRangeProjection_isOpenQuotientMap P hNE L hL w hw).isQuotientMap
  have hmk:hF.homeomorph (Quotient.mk _ x)=F x:=rfl
  change ((nielsenRightFunnelQuotientCircle l hl)
    ((Homeomorph.Quotient.congr E
      (fun a b=>nielsenClosedFunnel_projection_fiber P hNE L hL w hw f M hML q hqD l hqK hqF a b))
        (hF.homeomorph.symm (F x)))).2.val=_
  rw [←hmk,hF.homeomorph.symm_apply_apply]
  rfl

theorem nielsenOriginalClosedFunnelQuotientCircle_zero_iff
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) (f:H) (M:FuchsianAxisModel P.asFuchsianDisc f.val)
    (hML:M.carrier=Subtype.val '' (P.finiteCoordinate.symm '' L.carrier))
    (q:Mobius.complexMobiusGroup)
    (hqD:q.val '' P.domain.carrier=Hyperbolic.openHalfPlaneSet)
    (l:ℝ)
    (hl:l≠0)
    (hqM:q.val '' M.carrier=Hyperbolic.extendedImaginaryAxis)
    (hqK:DiscreteGroups.Action.Actions.subgroupConjugate q (Surfaces.mobiusSetStabilizer H M.carrier)=
      Subgroup.zpowers (Surfaces.stableAxisDilation l))
    (hqF:geometricHalfPlaneChart P.asFuchsianDisc q hqD '' nielsenOriginalClosedFunnel P L w=nielsenRightFunnel)
    (x:nielsenOriginalClosedFunnel P L w) :
    ((nielsenOriginalClosedFunnelQuotientCircle P hNE L hL w hw f M hML q hqD l hl hqK hqF)
      (nielsenClosedFunnelRangeProjection P L w x)).2.val=0 ↔
      x.val∈P.finiteCoordinate.symm '' L.carrier := by
  rw [nielsenOriginalClosedFunnelQuotientCircle_transverse P hNE L hL w hw f M hML q hqD l hl hqK hqF x,
    div_eq_zero_iff]
  rw [or_iff_left (geometricHalfPlaneChart P.asFuchsianDisc q hqD x.val).im_pos.ne']
  have hline:=nielsenOriginalAxis_chart_image P L f M hML q hqD hqM
  change geometricHalfPlaneChart P.asFuchsianDisc q hqD x.val∈(Hyperbolic.HalfPlaneLine.vertical 0).carrier ↔ _
  rw [←hline]
  exact (geometricHalfPlaneChart P.asFuchsianDisc q hqD).injective.mem_set_image



theorem nielsenFunnelPuncturedCapHomeomorph_norm_one_iff (p:Circle×Ici (0:ℝ)) :
    ‖((nielsenFunnelPuncturedCapHomeomorph p).val:ℂ)‖=1 ↔ p.2.val=0 := by
  change ‖(Real.exp (-p.2.val):ℂ)*(p.1:ℂ)‖=1 ↔ _
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),Circle.norm_coe,mul_one,
    Real.exp_eq_one_iff,neg_eq_zero]

/-- Every actual Nielsen boundary line has its genuine closed original quotient funnel,
homeomorphic to a punctured closed disc with precisely the original axis at its boundary. -/
theorem finitelyGenerated_originalClosedFunnel_puncturedCap
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (hFG:H.FG)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) :
    IsClosed (Surfaces.mobiusDomainProjection P.domain '' nielsenOriginalClosedFunnel P L w) ∧
      ∃B:↥(Surfaces.mobiusDomainProjection P.domain '' nielsenOriginalClosedFunnel P L w) ≃ₜ NielsenPuncturedClosedDisc,
        ∀x:nielsenOriginalClosedFunnel P L w,
          ‖((B (nielsenClosedFunnelRangeProjection P L w x)).val:ℂ)‖=1 ↔
            x.val∈P.finiteCoordinate.symm '' L.carrier := by
  refine ⟨nielsenOriginalClosedFunnel_projection_isClosed P hNE L hL w hw,?_⟩
  obtain ⟨f,hf,M,hML⟩:=finitelyGenerated_nielsen_boundary_line_boundaryHyperbolic P hNE hFG L hL
  obtain ⟨q,l,hl,hqD,hqM,hqK,hqF⟩:=nielsenOriginalClosedFunnel_positive_normal_form P hNE L hL w hw f hf M hML
  let C:=nielsenOriginalClosedFunnelQuotientCircle P hNE L hL w hw f M hML q hqD l hl.ne' hqK hqF
  refine ⟨C.trans nielsenFunnelPuncturedCapHomeomorph,?_⟩
  intro x
  change ‖((nielsenFunnelPuncturedCapHomeomorph (C (nielsenClosedFunnelRangeProjection P L w x))).val:ℂ)‖=1 ↔ _
  rw [nielsenFunnelPuncturedCapHomeomorph_norm_one_iff]
  exact nielsenOriginalClosedFunnelQuotientCircle_zero_iff P hNE L hL w hw f M hML q hqD l hl.ne' hqM hqK hqF x



theorem nielsenOriginalClosedFunnel_image_of_axis_image
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L M:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (_hM:M∈nielsenBoundaryDiscLineFamily P hNE)
    (w:P.domain.carrier) (hw:w∈fuchsianNielsenCore P hNE) (g:H)
    (he:g • (P.finiteCoordinate.symm '' L.carrier)=P.finiteCoordinate.symm '' M.carrier) :
    g • nielsenOriginalClosedFunnel P L w=nielsenOriginalClosedFunnel P M w := by
  obtain ⟨K,hK,hgK⟩:=nielsenOriginalClosedFunnel_image P hNE L hL w hw g
  have hKM:P.finiteCoordinate.symm '' K.carrier=P.finiteCoordinate.symm '' M.carrier:=by
    calc
      P.finiteCoordinate.symm '' K.carrier=
          nielsenOriginalClosedFunnel P K w∩closure (fuchsianNielsenCore P hNE):=
        (nielsenOriginalClosedFunnel_inter_core_closure P hNE K hK w hw).symm
      _=(g • nielsenOriginalClosedFunnel P L w)∩closure (fuchsianNielsenCore P hNE):=by rw [hgK]
      _=g • (nielsenOriginalClosedFunnel P L w∩closure (fuchsianNielsenCore P hNE)):=by
        rw [smul_set_inter,fuchsianNielsenCore_smul_closure]
      _=P.finiteCoordinate.symm '' M.carrier:=by
        rw [nielsenOriginalClosedFunnel_inter_core_closure P hNE L hL w hw,he]
  have hKe:K=M:=nielsen_discLine_carrier_injective (P.finiteCoordinate.symm.injective.image_injective hKM)
  exact hgK.trans (congrArg (fun N=>nielsenOriginalClosedFunnel P N w) hKe)

theorem nielsenWholeProjection_smul_image {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (g:H) (S:Set P.domain.carrier) :
    Surfaces.mobiusDomainProjection P.domain '' (g • S)=Surfaces.mobiusDomainProjection P.domain '' S := by
  ext q
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,rfl⟩
    exact ⟨x,hx,(Surfaces.mobiusDomainProjection_smul P.domain g x).symm⟩
  · rintro ⟨x,hx,rfl⟩
    exact ⟨g • x,⟨x,hx,rfl⟩,Surfaces.mobiusDomainProjection_smul P.domain g x⟩

/-- One genuine whole-orbit intersection of the two complete axes determines the same closed funnel image. -/
theorem nielsenOriginalClosedFunnel_projection_eq_of_axis_inter
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L M:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (hM:M∈nielsenBoundaryDiscLineFamily P hNE)
    (w:P.domain.carrier) (hw:w∈fuchsianNielsenCore P hNE)
    (q:Surfaces.MobiusDomainQuotient P.domain)
    (hqL:q∈Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' L.carrier))
    (hqM:q∈Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' M.carrier)) :
    Surfaces.mobiusDomainProjection P.domain '' nielsenOriginalClosedFunnel P L w=
      Surfaces.mobiusDomainProjection P.domain '' nielsenOriginalClosedFunnel P M w := by
  obtain ⟨x,hx,hxq⟩:=hqL
  obtain ⟨y,hy,hyq⟩:=hqM
  obtain ⟨g,hg⟩:=Quotient.exact (hxq.trans hyq.symm)
  obtain ⟨K,hK,hgK⟩:=nielsenBoundary_original_line_image P hNE M hM g
  have hxK:x∈P.finiteCoordinate.symm '' K.carrier:=by
    rw [←hgK]
    exact ⟨y,hy,hg⟩
  have hKL:K=L:=by
    by_contra hn
    have hd:=nielsenBoundaryDiscLineFamily_pairwise_disjoint P hNE hK hL hn
    obtain ⟨u,hu,hux⟩:=hxK
    obtain ⟨v,hv,hvx⟩:=hx
    have huv:u=v:=P.finiteCoordinate.symm.injective (hux.trans hvx.symm)
    exact Set.disjoint_left.mp hd hu (huv.symm ▸ hv)
  have hgML:g • (P.finiteCoordinate.symm '' M.carrier)=P.finiteCoordinate.symm '' L.carrier:=hKL ▸ hgK
  have heF:=nielsenOriginalClosedFunnel_image_of_axis_image P hNE M L hM hL w hw g hgML
  rw [←heF,nielsenWholeProjection_smul_image]

theorem nielsenOriginalClosedFunnel_projection_inter_core
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (w:P.domain.carrier)
    (hw:w∈fuchsianNielsenCore P hNE) :
    (Surfaces.mobiusDomainProjection P.domain '' nielsenOriginalClosedFunnel P L w)∩
        (Surfaces.mobiusDomainProjection P.domain '' closure (fuchsianNielsenCore P hNE))=
      Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' L.carrier) := by
  apply Set.Subset.antisymm
  · rintro q ⟨⟨x,hx,hxq⟩,⟨y,hy,hyq⟩⟩
    obtain ⟨g,hg⟩:=Quotient.exact (hxq.trans hyq.symm)
    have hxN:x∈closure (fuchsianNielsenCore P hNE):=by
      rw [←fuchsianNielsenCore_smul_closure P hNE g]
      exact ⟨y,hy,hg⟩
    exact ⟨x,(nielsenOriginalClosedFunnel_inter_core_closure P hNE L hL w hw) ▸ ⟨hx,hxN⟩,hxq⟩
  · rintro _ ⟨x,hx,rfl⟩
    have hh:x∈nielsenOriginalClosedFunnel P L w∩closure (fuchsianNielsenCore P hNE):=
      (nielsenOriginalClosedFunnel_inter_core_closure P hNE L hL w hw).symm ▸ hx
    exact ⟨⟨x,hh.1,rfl⟩,⟨x,hh.2,rfl⟩⟩

theorem nielsenOriginalClosedFunnel_axis_projection_eq_of_funnel_inter
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H)
    (hNE:DiscreteGroups.IsNonElementary H)
    (L M:Hyperbolic.DiscLine)
    (hL:L∈nielsenBoundaryDiscLineFamily P hNE) (hM:M∈nielsenBoundaryDiscLineFamily P hNE)
    (w:P.domain.carrier) (hw:w∈fuchsianNielsenCore P hNE)
    (q:Surfaces.MobiusDomainQuotient P.domain)
    (hqL:q∈Surfaces.mobiusDomainProjection P.domain '' nielsenOriginalClosedFunnel P L w)
    (hqM:q∈Surfaces.mobiusDomainProjection P.domain '' nielsenOriginalClosedFunnel P M w) :
    Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' L.carrier)=
      Surfaces.mobiusDomainProjection P.domain '' (P.finiteCoordinate.symm '' M.carrier) := by
  obtain ⟨x,hx,hxq⟩:=hqL
  obtain ⟨y,hy,hyq⟩:=hqM
  obtain ⟨g,hg⟩:=Quotient.exact (hxq.trans hyq.symm)
  obtain ⟨K,hK,hgK⟩:=nielsenBoundary_original_line_image P hNE M hM g
  have heF:=nielsenOriginalClosedFunnel_image_of_axis_image P hNE M K hM hK w hw g hgK
  have hxK:x∈nielsenOriginalClosedFunnel P K w:=by rw [←heF];exact ⟨y,hy,hg⟩
  have hKL:K=L:=by
    by_contra hn
    exact Set.disjoint_left.mp (nielsenOriginalClosedFunnels_pairwiseDisjoint P hNE w hw hK hL hn) hxK hx
  have hgML:g • (P.finiteCoordinate.symm '' M.carrier)=P.finiteCoordinate.symm '' L.carrier:=hKL ▸ hgK
  rw [←hgML,nielsenWholeProjection_smul_image]



section NielsenFiniteQuotientFunnels
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier}(hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier|IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "side" => nielsenCyclicBoundaryUnpairedSide hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "lineImage" => nielsenBoundaryCompleteLineProjection hD hNE hFG hfin w hwD hwN J hc hv
local notation "π" => Surfaces.mobiusDomainProjection P.domain

def nielsenBoundaryCycleFunnel
    (c:C) : Set (Surfaces.MobiusDomainQuotient P.domain) :=
  (π) '' nielsenOriginalClosedFunnel P ((side) c.out).val w
local notation "funnel" => nielsenBoundaryCycleFunnel hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenProjectedBoundaryCycle_eq_out_line (c:C) : cycleCarrier c=lineImage c.out := by
  simpa only [Quotient.out_eq] using
    nielsenProjectedBoundaryCycle_eq_completeLine hD hNE hFG hfin w hwD hwN J hc hv c.out

theorem nielsenBoundaryCycleFunnel_mk (b:B) :
    funnel (Quotient.mk _ b)=(π) '' nielsenOriginalClosedFunnel P ((side) b).val w := by
  obtain ⟨p,hp⟩:=nielsenProjectedBoundaryCycle_nonempty hD hNE hFG hfin w hwD hwN J hc hv (Quotient.mk _ b)
  have hpL:p∈lineImage (Quotient.mk _ b:C).out:=by
    rw [←nielsenProjectedBoundaryCycle_eq_out_line hD hNE hFG hfin w hwD hwN J hc hv]
    exact hp
  have hpM:p∈lineImage b:=by
    rw [←nielsenProjectedBoundaryCycle_eq_completeLine hD hNE hFG hfin w hwD hwN J hc hv b]
    exact hp
  exact nielsenOriginalClosedFunnel_projection_eq_of_axis_inter P hNE
    ((side) (Quotient.mk _ b:C).out).val ((side) b).val
    ((side) (Quotient.mk _ b:C).out).property.1 ((side) b).property.1 w hwN p hpL hpM

theorem nielsenBoundaryCycleFunnel_isClosed (c:C) : IsClosed (funnel c) :=
  nielsenOriginalClosedFunnel_projection_isClosed P hNE ((side) c.out).val ((side) c.out).property.1 w hwN

theorem nielsenBoundaryCycleFunnel_inter_core (c:C) :
    funnel c∩((π) '' closure (fuchsianNielsenCore P hNE))=cycleCarrier c := by
  change ((π) '' nielsenOriginalClosedFunnel P ((side) c.out).val w)∩_= _
  rw [nielsenOriginalClosedFunnel_projection_inter_core P hNE ((side) c.out).val ((side) c.out).property.1 w hwN]
  exact (nielsenProjectedBoundaryCycle_eq_out_line hD hNE hFG hfin w hwD hwN J hc hv c).symm

theorem nielsenBoundaryCycleFunnels_pairwise_disjoint : Pairwise (fun c d:C=>Disjoint (funnel c) (funnel d)) := by
  intro c d hcd
  apply Set.disjoint_left.mpr
  intro p hpc hpd
  have he:lineImage c.out=lineImage d.out:=
    nielsenOriginalClosedFunnel_axis_projection_eq_of_funnel_inter P hNE
      ((side) c.out).val ((side) d.out).val ((side) c.out).property.1 ((side) d.out).property.1 w hwN p hpc hpd
  have hcy:cycleCarrier c=cycleCarrier d:=by
    rw [nielsenProjectedBoundaryCycle_eq_out_line hD hNE hFG hfin w hwD hwN J hc hv c,
      nielsenProjectedBoundaryCycle_eq_out_line hD hNE hFG hfin w hwD hwN J hc hv d,he]
  obtain ⟨q,hq⟩:=nielsenProjectedBoundaryCycle_nonempty hD hNE hFG hfin w hwD hwN J hc hv c
  exact Set.disjoint_left.mp (nielsenProjectedBoundaryCycle_pairwise_disjoint hD hNE hFG hfin w hwD hwN J hc hv hcd)
    hq (hcy ▸ hq)

/-- These finitely many genuine closed funnel images and the original closed core cover the original whole quotient. -/
theorem nielsenBoundaryCycleFunnels_whole_quotient_cover :
    (univ:Set (Surfaces.MobiusDomainQuotient P.domain))=((π) '' closure (fuchsianNielsenCore P hNE))∪⋃c:C,funnel c := by
  apply Set.Subset.antisymm
  · intro q _hq
    obtain ⟨x,rfl⟩:=Surfaces.mobiusDomainProjection_surjective P.domain q
    have hx:x∈closure (fuchsianNielsenCore P hNE)∪
        ⋃L:nielsenBoundaryDiscLineFamily P hNE,nielsenOriginalClosedFunnel P L.val w:=by
      rw [←nielsenOriginalClosedFunnels_cover P hNE w hwN]
      trivial
    rcases hx with hx|hx
    · exact Or.inl ⟨x,hx,rfl⟩
    · right
      obtain ⟨L,hxL⟩:=mem_iUnion.mp hx
      obtain ⟨z,_v,hz,_hv,_hne⟩:=L.val.toHalfPlane.exists_two_points
      have hzL:Hyperbolic.halfPlaneToDisc z∈L.val.carrier:=by
        rw [Hyperbolic.DiscLine.mem_carrier,Hyperbolic.discToHalfPlane_halfPlaneToDisc]
        exact hz
      obtain ⟨a,ha,haL⟩:=nielsenBoundaryDiscLineFamily_subset_frontier P hNE L.val L.property hzL
      have haAxis:a∈P.finiteCoordinate.symm '' L.val.carrier:=
        ⟨Hyperbolic.halfPlaneToDisc z,hzL,by rw [←haL,P.finiteCoordinate.symm_apply_apply]⟩
      have haCover:(π) a∈⋃c:C,cycleCarrier c:=by
        rw [nielsenProjectedBoundaryCycles_cover hD hNE hFG hfin w hwD hwN J hc hv]
        exact ⟨a,ha,rfl⟩
      obtain ⟨c,hac⟩:=mem_iUnion.mp haCover
      have haOther:(π) a∈lineImage c.out:=by
        rw [←nielsenProjectedBoundaryCycle_eq_out_line hD hNE hFG hfin w hwD hwN J hc hv]
        exact hac
      have he: (π) '' nielsenOriginalClosedFunnel P L.val w=funnel c:=
        nielsenOriginalClosedFunnel_projection_eq_of_axis_inter P hNE L.val ((side) c.out).val
          L.property ((side) c.out).property.1 w hwN ((π) a) ⟨a,haAxis,rfl⟩ haOther
      exact mem_iUnion.mpr ⟨c,he ▸ mem_image_of_mem (π) hxL⟩
  · exact subset_univ _

end NielsenFiniteQuotientFunnels



def nielsenPuncturedClosedDiscBoundary (z:Circle) : NielsenPuncturedClosedDisc :=
  nielsenFunnelPuncturedCapHomeomorph (z,⟨0,le_rfl⟩)

theorem nielsenPuncturedClosedDiscBoundary_isEmbedding : Topology.IsEmbedding nielsenPuncturedClosedDiscBoundary := by
  have hi:Topology.IsEmbedding (fun z:Circle=>(z,(⟨0,le_rfl⟩:Ici (0:ℝ)))):=
    Topology.IsEmbedding.of_leftInverse (fun _=>rfl) continuous_fst (continuous_id.prodMk continuous_const)
  exact nielsenFunnelPuncturedCapHomeomorph.isEmbedding.comp hi

theorem nielsenPuncturedClosedDiscBoundary_range :
    range nielsenPuncturedClosedDiscBoundary={z:NielsenPuncturedClosedDisc|‖(z.val:ℂ)‖=1} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z,rfl⟩
    exact (nielsenFunnelPuncturedCapHomeomorph_norm_one_iff (z,⟨0,le_rfl⟩)).mpr rfl
  · intro z hz
    obtain ⟨⟨c,s⟩,rfl⟩:=nielsenFunnelPuncturedCapHomeomorph.surjective z
    have hs:s=(⟨0,le_rfl⟩:Ici (0:ℝ)):=
      Subtype.ext ((nielsenFunnelPuncturedCapHomeomorph_norm_one_iff (c,s)).mp hz)
    subst s
    exact ⟨c,rfl⟩

def nielsenPuncturedCapAngularHomeomorph (a:Circle≃ₜCircle) :
    NielsenPuncturedClosedDisc≃ₜNielsenPuncturedClosedDisc :=
  nielsenFunnelPuncturedCapHomeomorph.symm.trans
    ((a.prodCongr (Homeomorph.refl _)).trans nielsenFunnelPuncturedCapHomeomorph)

theorem nielsenPuncturedCapAngularHomeomorph_boundary (a:Circle≃ₜCircle) (z:Circle) :
    nielsenPuncturedCapAngularHomeomorph a (nielsenPuncturedClosedDiscBoundary z)=
      nielsenPuncturedClosedDiscBoundary (a z) := by
  change nielsenFunnelPuncturedCapHomeomorph ((a.prodCongr (Homeomorph.refl _))
    (nielsenFunnelPuncturedCapHomeomorph.symm (nielsenFunnelPuncturedCapHomeomorph (z,⟨0,le_rfl⟩))))=_
  rw [Homeomorph.symm_apply_apply]
  rfl

theorem nielsenPuncturedCapAngularHomeomorph_norm_one_iff (a:Circle≃ₜCircle) (z:NielsenPuncturedClosedDisc) :
    ‖((nielsenPuncturedCapAngularHomeomorph a z).val:ℂ)‖=1 ↔ ‖(z.val:ℂ)‖=1 := by
  obtain ⟨p,rfl⟩:=nielsenFunnelPuncturedCapHomeomorph.surjective z
  change ‖((nielsenFunnelPuncturedCapHomeomorph ((a.prodCongr (Homeomorph.refl _))
    (nielsenFunnelPuncturedCapHomeomorph.symm (nielsenFunnelPuncturedCapHomeomorph p)))).val:ℂ)‖=1 ↔ _
  rw [Homeomorph.symm_apply_apply,nielsenFunnelPuncturedCapHomeomorph_norm_one_iff,
    nielsenFunnelPuncturedCapHomeomorph_norm_one_iff]
  rfl



section NielsenOriginalCapQuotientClocks
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
  {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "W" => FiniteCyclicPresentation.PolygonalRealization
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv)
  (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)
local notation "A" => {f:FiniteCyclicPresentation.Face
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv) //
  f≠nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv}
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "coreHomeo" => nielsenCappedFirstFaceCompletedCoreHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "F" => nielsenCappedFirstFaceCompletedCoreMap hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "openCap" => nielsenCappedFaceInterior hD hNE hFG hfin w hwD hwN J hc hv
local notation "closedCap" => nielsenCappedClosedCap hD hNE hFG hfin w hwD hwN J hc hv
local notation "clock" => nielsenCappedCapClock hD hNE hFG hfin w hwD hwN J hc hv
local notation "originalClock" => nielsenCappedOriginalCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "capCycle" => nielsenCappedCapCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv


theorem nielsenCappedOriginalCapClock_isEmbedding (f:A) :
    Topology.IsEmbedding ((originalClock) f.val f.property) := by
  let k:Circle→↥(range (modelPoint)):=fun z=>⟨(clock) f.val z,by
    have hz:(clock) f.val z∈range ((clock) f.val):=mem_range_self z
    exact ((nielsenCappedCapClock_range hD hNE hFG hfin w hwD hwN J hc hv f.val f.property) ▸ hz).2⟩
  have hk:Topology.IsEmbedding k:=(Topology.IsEmbedding.subtypeVal.of_comp_iff).mp
    (nielsenCappedCapClock_isClosedEmbedding hD hNE hFG hfin w hwD hwN J hc hv f.val f.property).isEmbedding
  have he:(originalClock) f.val f.property=Subtype.val ∘ (coreHomeo) ∘ k:=rfl
  rw [he]
  exact Topology.IsEmbedding.subtypeVal.comp ((coreHomeo).isEmbedding.comp hk)

def nielsenCappedOriginalQuotientClock
    (f:A)
    (z:Circle) : Surfaces.MobiusDomainQuotient P.domain :=
  Classical.choose (show ∃q:Surfaces.MobiusDomainQuotient P.domain,
    fuchsianCuspCompletionOld P.asFuchsianDisc q=(originalClock) f.val f.property z from by
      have hz:(originalClock) f.val f.property z∈
          fuchsianCuspCompletionOld P.asFuchsianDisc '' (cycleCarrier ((capCycle) f.val f.property)):=by
        rw [←nielsenCappedOriginalCapClock_range hD hNE hFG hfin w hwD hwN J hc hv S hr f.val f.property]
        exact mem_range_self z
      obtain ⟨q,_hq,he⟩:=hz
      exact ⟨q,he⟩)
local notation "quotientClock" => nielsenCappedOriginalQuotientClock hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenCappedOriginalQuotientClock_old (f:A) (z:Circle) :
    fuchsianCuspCompletionOld P.asFuchsianDisc ((quotientClock) f z)=(originalClock) f.val f.property z :=
  by
    unfold nielsenCappedOriginalQuotientClock
    exact Classical.choose_spec (p:=fun q:Surfaces.MobiusDomainQuotient P.domain=>
      fuchsianCuspCompletionOld P.asFuchsianDisc q=(originalClock) f.val f.property z) _

theorem nielsenCappedOriginalQuotientClock_isEmbedding (f:A) : Topology.IsEmbedding ((quotientClock) f) := by
  have he:fuchsianCuspCompletionOld P.asFuchsianDisc ∘ (quotientClock) f=(originalClock) f.val f.property:=
    funext (nielsenCappedOriginalQuotientClock_old hD hNE hFG hfin w hwD hwN J hc hv S hr f)
  apply (fuchsianCuspCompletionOld_isOpenEmbedding P.asFuchsianDisc).isEmbedding.of_comp_iff.mp
  rw [he]
  exact nielsenCappedOriginalCapClock_isEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr f

theorem nielsenCappedOriginalQuotientClock_range (f:A) :
    range ((quotientClock) f)=cycleCarrier ((capCycle) f.val f.property) := by
  apply (fuchsianCuspCompletionOld_isOpenEmbedding P.asFuchsianDisc).injective.image_injective
  calc
    fuchsianCuspCompletionOld P.asFuchsianDisc '' range ((quotientClock) f)=
        range ((originalClock) f.val f.property):=by
      rw [←Set.range_comp]
      congr 1
      funext z
      exact nielsenCappedOriginalQuotientClock_old hD hNE hFG hfin w hwD hwN J hc hv S hr f z
    _=fuchsianCuspCompletionOld P.asFuchsianDisc '' (cycleCarrier ((capCycle) f.val f.property)):=
      nielsenCappedOriginalCapClock_range hD hNE hFG hfin w hwD hwN J hc hv S hr f.val f.property

end NielsenOriginalCapQuotientClocks



section NielsenCapBoundaryCycleEquiv
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
  {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "W" => FiniteCyclicPresentation.PolygonalRealization
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv)
  (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)
local notation "A" => {f:FiniteCyclicPresentation.Face
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv) //
  f≠nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv}
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "coreHomeo" => nielsenCappedFirstFaceCompletedCoreHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "F" => nielsenCappedFirstFaceCompletedCoreMap hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "openCap" => nielsenCappedFaceInterior hD hNE hFG hfin w hwD hwN J hc hv
local notation "closedCap" => nielsenCappedClosedCap hD hNE hFG hfin w hwD hwN J hc hv
local notation "clock" => nielsenCappedCapClock hD hNE hFG hfin w hwD hwN J hc hv
local notation "originalClock" => nielsenCappedOriginalCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "capCycle" => nielsenCappedCapCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv



local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "occIndex" => nielsenCappedOccurrenceIndex hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenCappedCapCycle_injective : Function.Injective (fun f:A=>(capCycle) f.val f.property) := by
  intro f g hfg
  let b:B:=((capCycle) f.val f.property).out
  have hb:(Quotient.mk _ b:C)=(capCycle) f.val f.property:=Quotient.out_eq _
  obtain ⟨i,hi⟩:=nielsenCappedCapCycle_occurrence hD hNE hFG hfin w hwD hwN J hc hv f.val f.property b hb
  obtain ⟨j,hj⟩:=nielsenCappedCapCycle_occurrence hD hNE hFG hfin w hwD hwN J hc hv g.val g.property b (hb.trans hfg)
  apply Subtype.ext
  have he:(⟨f.val,i⟩:(Pcap).BoundaryOccurrence)=⟨g.val,j⟩:=(occIndex).injective (hi.trans hj.symm)
  exact congrArg Sigma.fst he

theorem nielsenCappedCapCycle_bijective : Function.Bijective (fun f:A=>(capCycle) f.val f.property) := by
  apply (Nat.bijective_iff_injective_and_card _).mpr
  refine ⟨nielsenCappedCapCycle_injective hD hNE hFG hfin w hwD hwN J hc hv,?_⟩
  rw [nielsenCappedCapFaceCount_eq hD hNE hFG hfin w hwD hwN J hc hv,
    nielsenBoundaryCycleClassCount_eq hD hNE hFG hfin w hwD hwN J hc hv]

def nielsenCappedCapBoundaryCycleEquiv : A≃C :=
  Equiv.ofBijective (fun f:A=>(capCycle) f.val f.property)
    (nielsenCappedCapCycle_bijective hD hNE hFG hfin w hwD hwN J hc hv)

end NielsenCapBoundaryCycleEquiv



section NielsenCycleFunnelBoundaryClocks
open LeanEval.Topology.ClassificationOfSurfaces.Moise
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier}(hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier|IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
local notation "B" => NielsenCyclicBoundaryIndex hD hNE hFG hfin w hwD hwN J hc hv
local notation "C" => NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "side" => nielsenCyclicBoundaryUnpairedSide hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "lineImage" => nielsenBoundaryCompleteLineProjection hD hNE hFG hfin w hwD hwN J hc hv
local notation "π" => Surfaces.mobiusDomainProjection P.domain


local notation "funnel" => nielsenBoundaryCycleFunnel hD hNE hFG hfin w hwD hwN J hc hv

def nielsenBoundaryCycleFunnelHomeomorph (c:C) : ↥(funnel c)≃ₜNielsenPuncturedClosedDisc :=
  Classical.choose ((finitelyGenerated_originalClosedFunnel_puncturedCap P hNE hFG
    ((side) c.out).val ((side) c.out).property.1 w hwN).2)
local notation "funnelHomeo" => nielsenBoundaryCycleFunnelHomeomorph hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenBoundaryCycleFunnelHomeomorph_norm_one_iff (c:C)
    (x:nielsenOriginalClosedFunnel P ((side) c.out).val w) :
    ‖(((funnelHomeo) c (nielsenClosedFunnelRangeProjection P ((side) c.out).val w x)).val:ℂ)‖=1 ↔
      x.val∈P.finiteCoordinate.symm '' ((side) c.out).val.carrier :=
  (Classical.choose_spec ((finitelyGenerated_originalClosedFunnel_puncturedCap P hNE hFG
    ((side) c.out).val ((side) c.out).property.1 w hwN).2)) x

def nielsenBoundaryCycleFunnelClock
    (c:C)
    (z:Circle) : Surfaces.MobiusDomainQuotient P.domain :=
  (((funnelHomeo) c).symm (nielsenPuncturedClosedDiscBoundary z)).val
local notation "funnelClock" => nielsenBoundaryCycleFunnelClock hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenBoundaryCycleFunnelClock_isEmbedding (c:C) : Topology.IsEmbedding ((funnelClock) c) :=
  Topology.IsEmbedding.subtypeVal.comp (((funnelHomeo) c).symm.isEmbedding.comp
    nielsenPuncturedClosedDiscBoundary_isEmbedding)

theorem nielsenBoundaryCycleFunnelClock_range (c:C) : range ((funnelClock) c)=cycleCarrier c := by
  rw [nielsenProjectedBoundaryCycle_eq_out_line hD hNE hFG hfin w hwD hwN J hc hv c]
  apply Set.Subset.antisymm
  · rintro _ ⟨z,rfl⟩
    let q:↥(funnel c):=((funnelHomeo) c).symm (nielsenPuncturedClosedDiscBoundary z)
    obtain ⟨x,hx,hxq⟩:=q.property
    let xF:nielsenOriginalClosedFunnel P ((side) c.out).val w:=⟨x,hx⟩
    have he:nielsenClosedFunnelRangeProjection P ((side) c.out).val w xF=q:=Subtype.ext hxq
    have hn:‖(((funnelHomeo) c (nielsenClosedFunnelRangeProjection P ((side) c.out).val w xF)).val:ℂ)‖=1:=by
      rw [he]
      change ‖((((funnelHomeo) c) (((funnelHomeo) c).symm (nielsenPuncturedClosedDiscBoundary z))).val:ℂ)‖=1
      rw [Homeomorph.apply_symm_apply]
      change nielsenPuncturedClosedDiscBoundary z∈{v:NielsenPuncturedClosedDisc|‖(v.val:ℂ)‖=1}
      rw [←nielsenPuncturedClosedDiscBoundary_range]
      exact mem_range_self z
    have hxL: x∈P.finiteCoordinate.symm '' ((side) c.out).val.carrier:=
      (nielsenBoundaryCycleFunnelHomeomorph_norm_one_iff hD hNE hFG hfin w hwD hwN J hc hv c xF).mp hn
    exact ⟨x,hxL,hxq⟩
  · rintro q ⟨x,hx,hxq⟩
    have hxF:x∈nielsenOriginalClosedFunnel P ((side) c.out).val w:=
      ((nielsenOriginalClosedFunnel_inter_core_closure P hNE ((side) c.out).val
        ((side) c.out).property.1 w hwN).symm ▸ hx).1
    let xF:nielsenOriginalClosedFunnel P ((side) c.out).val w:=⟨x,hxF⟩
    have hn:((funnelHomeo) c (nielsenClosedFunnelRangeProjection P ((side) c.out).val w xF))∈
        range nielsenPuncturedClosedDiscBoundary:=by
      rw [nielsenPuncturedClosedDiscBoundary_range]
      exact (nielsenBoundaryCycleFunnelHomeomorph_norm_one_iff hD hNE hFG hfin w hwD hwN J hc hv c xF).mpr hx
    obtain ⟨z,hz⟩:=hn
    refine ⟨z,?_⟩
    change (((funnelHomeo) c).symm (nielsenPuncturedClosedDiscBoundary z)).val=q
    rw [hz,Homeomorph.symm_apply_apply]
    exact hxq

end NielsenCycleFunnelBoundaryClocks



section NielsenAlignedFunnelClocks
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
  {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "W" => FiniteCyclicPresentation.PolygonalRealization
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv)
  (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)
local notation "A" => {f:FiniteCyclicPresentation.Face
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv) //
  f≠nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv}
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "coreHomeo" => nielsenCappedFirstFaceCompletedCoreHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "F" => nielsenCappedFirstFaceCompletedCoreMap hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "openCap" => nielsenCappedFaceInterior hD hNE hFG hfin w hwD hwN J hc hv
local notation "closedCap" => nielsenCappedClosedCap hD hNE hFG hfin w hwD hwN J hc hv
local notation "clock" => nielsenCappedCapClock hD hNE hFG hfin w hwD hwN J hc hv
local notation "originalClock" => nielsenCappedOriginalCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "capCycle" => nielsenCappedCapCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv



local notation "quotientClock" => nielsenCappedOriginalQuotientClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "funnel" => nielsenBoundaryCycleFunnel hD hNE hFG hfin w hwD hwN J hc hv
local notation "funnelHomeo" => nielsenBoundaryCycleFunnelHomeomorph hD hNE hFG hfin w hwD hwN J hc hv
local notation "funnelClock" => nielsenBoundaryCycleFunnelClock hD hNE hFG hfin w hwD hwN J hc hv

def nielsenFunnelCapAngularClock (f:A) : Circle≃ₜCircle :=
  (nielsenCappedOriginalQuotientClock_isEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr f).toHomeomorph.trans
    ((Homeomorph.setCongr ((nielsenCappedOriginalQuotientClock_range hD hNE hFG hfin w hwD hwN J hc hv S hr f).trans
      (nielsenBoundaryCycleFunnelClock_range hD hNE hFG hfin w hwD hwN J hc hv ((capCycle) f.val
        f.property)).symm)).trans
      (nielsenBoundaryCycleFunnelClock_isEmbedding hD hNE hFG hfin w hwD hwN J hc hv ((capCycle) f.val
        f.property)).toHomeomorph.symm)
local notation "angularClock" => nielsenFunnelCapAngularClock hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenFunnelCapAngularClock_spec (f:A) (z:Circle) :
    (funnelClock) ((capCycle) f.val f.property) ((angularClock) f z)=(quotientClock) f z := by
  exact congrArg Subtype.val
    ((nielsenBoundaryCycleFunnelClock_isEmbedding hD hNE hFG hfin w hwD hwN J hc hv ((capCycle) f.val
      f.property)).toHomeomorph.apply_symm_apply _)

def nielsenCappedQuotientClockInFunnel (f:A) (z:Circle) : ↥(funnel ((capCycle) f.val f.property)) :=
  ⟨(quotientClock) f z,by
    have hz:(quotientClock) f z∈cycleCarrier ((capCycle) f.val f.property):=by
      rw [←nielsenCappedOriginalQuotientClock_range hD hNE hFG hfin w hwD hwN J hc hv S hr f]
      exact mem_range_self z
    exact ((nielsenBoundaryCycleFunnel_inter_core hD hNE hFG hfin w hwD hwN J hc hv _).symm ▸ hz).1⟩
local notation "clockInFunnel" => nielsenCappedQuotientClockInFunnel hD hNE hFG hfin w hwD hwN J hc hv S hr

/-- Reparameterizing only the angular coordinate matches this genuine funnel to its own unchanged actual cap clock. -/
def nielsenAlignedFunnelHomeomorph (f:A) : ↥(funnel ((capCycle) f.val f.property)) ≃ₜ NielsenPuncturedClosedDisc :=
  ((funnelHomeo) ((capCycle) f.val f.property)).trans (nielsenPuncturedCapAngularHomeomorph ((angularClock) f).symm)
local notation "aligned" => nielsenAlignedFunnelHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenAlignedFunnelHomeomorph_clock (f:A) (z:Circle) :
    (aligned) f ((clockInFunnel) f z)=nielsenPuncturedClosedDiscBoundary z := by
  have he:((funnelHomeo) ((capCycle) f.val f.property)).symm
      (nielsenPuncturedClosedDiscBoundary ((angularClock) f z))=(clockInFunnel) f z:=
    Subtype.ext (nielsenFunnelCapAngularClock_spec hD hNE hFG hfin w hwD hwN J hc hv S hr f z)
  change nielsenPuncturedCapAngularHomeomorph ((angularClock) f).symm
    ((funnelHomeo) ((capCycle) f.val f.property) ((clockInFunnel) f z))=_
  rw [←he,Homeomorph.apply_symm_apply,nielsenPuncturedCapAngularHomeomorph_boundary,Homeomorph.symm_apply_apply]

end NielsenAlignedFunnelClocks



section NielsenWholeCoreCappedEmbedding
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
  {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "W" => FiniteCyclicPresentation.PolygonalRealization
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv)
  (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)
local notation "A" => {f:FiniteCyclicPresentation.Face
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv) //
  f≠nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv}
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "coreHomeo" => nielsenCappedFirstFaceCompletedCoreHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "F" => nielsenCappedFirstFaceCompletedCoreMap hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "openCap" => nielsenCappedFaceInterior hD hNE hFG hfin w hwD hwN J hc hv
local notation "closedCap" => nielsenCappedClosedCap hD hNE hFG hfin w hwD hwN J hc hv
local notation "clock" => nielsenCappedCapClock hD hNE hFG hfin w hwD hwN J hc hv
local notation "originalClock" => nielsenCappedOriginalCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "capCycle" => nielsenCappedCapCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv



local notation "coreEmbedding" => nielsenCompletedCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "coreClock" => nielsenCompletedCoreCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "quotientClock" => nielsenCappedOriginalQuotientClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "old" => fuchsianCuspCompletionOld P.asFuchsianDisc
local notation "cusp" => fuchsianCuspCompletionPoint P.asFuchsianDisc
local notation "coreImage" => (Surfaces.mobiusDomainProjection P.domain) '' closure (fuchsianNielsenCore P hNE)
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "weight" => nielsenRawCornerClassWeight hD hNE hFG hfin w hwD hwN J hc hv

def nielsenWholeCoreCappedEmbedding (q:↥coreImage) : W :=
  (coreEmbedding) ⟨(old) q.val,Or.inl ⟨q.val,q.property,rfl⟩⟩
local notation "oldEmbedding" => nielsenWholeCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenWholeCoreCappedEmbedding_isEmbedding : Topology.IsEmbedding (oldEmbedding) := by
  have hi:Topology.IsEmbedding (fun q:↥coreImage=>
      (⟨(old) q.val,Or.inl ⟨q.val,q.property,rfl⟩⟩:↥(nielsenCompletedCoreSet P hNE))):=
    Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
      ((fuchsianCuspCompletionOld_isOpenEmbedding P.asFuchsianDisc).isEmbedding.comp Topology.IsEmbedding.subtypeVal)
  exact (nielsenCompletedCoreCappedEmbedding_isClosedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S
    hr).isEmbedding.comp hi

def nielsenCappedActualCuspPoint (c:FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) : W :=
  (coreEmbedding) ⟨(cusp) c,Or.inr ⟨c,rfl⟩⟩
local notation "cappedCusp" => nielsenCappedActualCuspPoint hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenCappedActualCuspPoint_injective : Function.Injective (cappedCusp) := by
  intro c e hce
  have hi:Topology.IsEmbedding (coreEmbedding):=
    (nielsenCompletedCoreCappedEmbedding_isClosedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr).isEmbedding
  exact fuchsianCuspCompletionPoint_injective P.asFuchsianDisc (congrArg Subtype.val (hi.injective hce))

theorem nielsenCappedActualCuspPoint_range_finite : (range (cappedCusp)).Finite := by
  let e:=nielsenRawIdealCuspEquiv hD hNE hFG hfin w hwD hwN J hc hv S hr
  let:Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic):=
    Finite.of_surjective e e.surjective
  exact Set.finite_range _

/-- The actual old closed-core image is exactly the same first face with its true cusp points removed. -/
theorem nielsenWholeCoreCappedEmbedding_range :
    range (oldEmbedding)=range (modelPoint)\range (cappedCusp) := by
  have hi:Topology.IsEmbedding (coreEmbedding):=
    (nielsenCompletedCoreCappedEmbedding_isClosedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr).isEmbedding
  rw [←nielsenCompletedCoreCappedEmbedding_range hD hNE hFG hfin w hwD hwN J hc hv S hr]
  apply Set.Subset.antisymm
  · rintro _ ⟨q,rfl⟩
    refine ⟨⟨_,rfl⟩,?_⟩
    rintro ⟨c,hc⟩
    have he:(cusp) c=(old) q.val:=congrArg Subtype.val (hi.injective hc)
    exact fuchsianCuspCompletionPoint_not_mem_old P.asFuchsianDisc c ⟨q.val,he.symm⟩
  · rintro _ ⟨⟨s,rfl⟩,hs⟩
    rcases fuchsianCuspCompletion_old_or_cusp P.asFuchsianDisc s.val with hOld|⟨c,hc⟩
    · obtain ⟨q,hq⟩:=hOld
      have hsOld:(old) q∈nielsenCompletedCoreSet P hNE:=hq.symm ▸ s.property
      obtain ⟨a,ha,hea⟩:=(nielsenCompletedCore_old_iff hNE ((old) q)).mp ⟨hsOld,mem_range_self q⟩
      exact ⟨⟨a,ha⟩,congrArg (coreEmbedding) (Subtype.ext (hea.trans hq))⟩
    · exact False.elim (hs ⟨c,congrArg (coreEmbedding) (Subtype.ext hc.symm)⟩)

def nielsenCappedQuotientClockInCore (f:A) (z:Circle) : ↥coreImage :=
  ⟨(quotientClock) f z,by
    have hz:(quotientClock) f z∈cycleCarrier ((capCycle) f.val f.property):=by
      rw [←nielsenCappedOriginalQuotientClock_range hD hNE hFG hfin w hwD hwN J hc hv S hr f]
      exact mem_range_self z
    exact ((nielsenBoundaryCycleFunnel_inter_core hD hNE hFG hfin w hwD hwN J hc hv _).symm ▸ hz).2⟩
local notation "clockInCore" => nielsenCappedQuotientClockInCore hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenWholeCoreCappedEmbedding_clock (f:A) (z:Circle) :
    (oldEmbedding) ((clockInCore) f z)=(clock) f.val z := by
  have he:(⟨(old) ((quotientClock) f z),Or.inl ⟨(quotientClock) f z,((clockInCore) f z).property,rfl⟩⟩:
      ↥(nielsenCompletedCoreSet P hNE))=(coreClock) f z:=
    Subtype.ext (nielsenCappedOriginalQuotientClock_old hD hNE hFG hfin w hwD hwN J hc hv S hr f z)
  exact (congrArg (coreEmbedding) he).trans
    (nielsenCompletedCoreCapClock_filling hD hNE hFG hfin w hwD hwN J hc hv S hr f z)

end NielsenWholeCoreCappedEmbedding



section NielsenActualCapDiscs
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
  {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "W" => FiniteCyclicPresentation.PolygonalRealization
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv)
  (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)
local notation "A" => {f:FiniteCyclicPresentation.Face
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv) //
  f≠nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv}
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "coreHomeo" => nielsenCappedFirstFaceCompletedCoreHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "F" => nielsenCappedFirstFaceCompletedCoreMap hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "openCap" => nielsenCappedFaceInterior hD hNE hFG hfin w hwD hwN J hc hv
local notation "closedCap" => nielsenCappedClosedCap hD hNE hFG hfin w hwD hwN J hc hv
local notation "clock" => nielsenCappedCapClock hD hNE hFG hfin w hwD hwN J hc hv
local notation "originalClock" => nielsenCappedOriginalCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "capCycle" => nielsenCappedCapCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv



local notation "coreEmbedding" => nielsenCompletedCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "coreClock" => nielsenCompletedCoreCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "quotientClock" => nielsenCappedOriginalQuotientClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "old" => fuchsianCuspCompletionOld P.asFuchsianDisc
local notation "cusp" => fuchsianCuspCompletionPoint P.asFuchsianDisc
local notation "coreImage" => (Surfaces.mobiusDomainProjection P.domain) '' closure (fuchsianNielsenCore P hNE)
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "weight" => nielsenRawCornerClassWeight hD hNE hFG hfin w hwD hwN J hc hv


local notation "cappedCusp" => nielsenCappedActualCuspPoint hD hNE hFG hfin w hwD hwN J hc hv S hr

def nielsenActualCapDisc (f:A) (z:𝕔𝔻) : W :=
  (closedCap) f.val ((PolygonCell.closedUnitDiscHomeomorph ((Pcap).boundary f.val).length).symm z)
local notation "capDisc" => nielsenActualCapDisc hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenActualCapDisc_isClosedEmbedding (f:A) : Topology.IsClosedEmbedding ((capDisc) f) :=
  (nielsenCappedClosedCap_isClosedEmbedding hD hNE hFG hfin w hwD hwN J hc hv f.val f.property).comp
    (PolygonCell.closedUnitDiscHomeomorph ((Pcap).boundary f.val).length).symm.isClosedEmbedding

theorem nielsenActualCapDisc_boundary (f:A) (z:Circle) :
    (capDisc) f (nielsenPuncturedClosedDiscBoundary z).val=(clock) f.val z := by
  apply congrArg ((closedCap) f.val)
  apply PolygonCell.ext
  exact nielsenFunnelPuncturedCapHomeomorph_boundary z

theorem nielsenActualCapDisc_range (f:A) : range ((capDisc) f)=range ((closedCap) f.val) := by
  change range (((closedCap) f.val) ∘ (PolygonCell.closedUnitDiscHomeomorph ((Pcap).boundary f.val).length).symm)=_
  rw [Set.range_comp,(PolygonCell.closedUnitDiscHomeomorph ((Pcap).boundary
    f.val).length).symm.surjective.range_eq,image_univ]

theorem nielsenActualCapDisc_mem_firstFace_iff (f:A) (z:𝕔𝔻) :
    (capDisc) f z∈range (modelPoint) ↔ ‖(z:ℂ)‖=1 :=
  nielsenCappedClosedCap_mem_firstFace_iff hD hNE hFG hfin w hwD hwN J hc hv f.val f.property _

def nielsenActualCapCenter (f:A) : W := (capDisc) f 0
local notation "capCenter" => nielsenActualCapCenter hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenActualCapCenter_not_firstFace (f:A) : (capCenter) f∉range (modelPoint) := by
  rw [nielsenActualCapCenter,nielsenActualCapDisc_mem_firstFace_iff]
  norm_num

theorem nielsenActualCapCenter_injective : Function.Injective (capCenter) := by
  intro f g he
  by_contra hne
  have hd:=nielsenCappedClosedCap_pairwise_disjoint hD hNE hFG hfin w hwD hwN J hc hv
    hne
  have hf:(capCenter) f∈range ((closedCap) f.val):=⟨_,rfl⟩
  have hg:(capCenter) g∈range ((closedCap) g.val):=⟨_,rfl⟩
  exact Set.disjoint_left.mp hd hf (he.symm ▸ hg)

theorem nielsenCappedActualCuspPoint_not_clock (c:FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) (f:A) :
    (cappedCusp) c∉range ((clock) f.val) := by
  rintro ⟨z,hz⟩
  have hi:Topology.IsEmbedding (coreEmbedding):=
    (nielsenCompletedCoreCappedEmbedding_isClosedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr).isEmbedding
  have he:(⟨(cusp) c,Or.inr ⟨c,rfl⟩⟩:↥(nielsenCompletedCoreSet P hNE))=(coreClock) f z:=by
    apply hi.injective
    change (cappedCusp) c=(coreEmbedding) ((coreClock) f z)
    rw [nielsenCompletedCoreCapClock_filling]
    exact hz.symm
  have heOld:(cusp) c=(old) ((quotientClock) f z):=
    (congrArg Subtype.val he).trans (nielsenCappedOriginalQuotientClock_old hD hNE hFG hfin w hwD hwN J hc hv S hr f
      z).symm
  exact fuchsianCuspCompletionPoint_not_mem_old P.asFuchsianDisc c ⟨_,heOld.symm⟩

theorem nielsenCappedActualCuspPoint_not_capDisc (c:FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic) (f:A) :
    (cappedCusp) c∉range ((capDisc) f) := by
  intro hcCap
  have hcFirst:(cappedCusp) c∈range (modelPoint):=by
    rw [←nielsenCompletedCoreCappedEmbedding_range hD hNE hFG hfin w hwD hwN J hc hv S hr]
    exact ⟨_,rfl⟩
  have hcClock:(cappedCusp) c∈range ((clock) f.val):=by
    rw [nielsenCappedCapClock_range hD hNE hFG hfin w hwD hwN J hc hv f.val f.property]
    exact ⟨(nielsenActualCapDisc_range hD hNE hFG hfin w hwD hwN J hc hv f) ▸ hcCap,hcFirst⟩
  exact nielsenCappedActualCuspPoint_not_clock hD hNE hFG hfin w hwD hwN J hc hv S hr c f hcClock

end NielsenActualCapDiscs



section NielsenCappedPuncturedSurface
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
  {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "W" => FiniteCyclicPresentation.PolygonalRealization
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv)
  (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)
local notation "A" => {f:FiniteCyclicPresentation.Face
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv) //
  f≠nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv}
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "coreHomeo" => nielsenCappedFirstFaceCompletedCoreHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "F" => nielsenCappedFirstFaceCompletedCoreMap hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "openCap" => nielsenCappedFaceInterior hD hNE hFG hfin w hwD hwN J hc hv
local notation "closedCap" => nielsenCappedClosedCap hD hNE hFG hfin w hwD hwN J hc hv
local notation "clock" => nielsenCappedCapClock hD hNE hFG hfin w hwD hwN J hc hv
local notation "originalClock" => nielsenCappedOriginalCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "capCycle" => nielsenCappedCapCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv



local notation "coreEmbedding" => nielsenCompletedCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "coreClock" => nielsenCompletedCoreCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "quotientClock" => nielsenCappedOriginalQuotientClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "old" => fuchsianCuspCompletionOld P.asFuchsianDisc
local notation "cusp" => fuchsianCuspCompletionPoint P.asFuchsianDisc
local notation "coreImage" => (Surfaces.mobiusDomainProjection P.domain) '' closure (fuchsianNielsenCore P hNE)
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "weight" => nielsenRawCornerClassWeight hD hNE hFG hfin w hwD hwN J hc hv


local notation "cappedCusp" => nielsenCappedActualCuspPoint hD hNE hFG hfin w hwD hwN J hc hv S hr


local notation "capDisc" => nielsenActualCapDisc hD hNE hFG hfin w hwD hwN J hc hv
local notation "capCenter" => nielsenActualCapCenter hD hNE hFG hfin w hwD hwN J hc hv
local notation "oldEmbedding" => nielsenWholeCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr

/-- The points removed from the very same faithful capped surface are its actual original cusps and its actual cap centres. -/
def nielsenCappedEndMarks : Set W := range (cappedCusp)∪range (capCenter)
local notation "marks" => nielsenCappedEndMarks hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "Y" => ↥((marks)ᶜ)

theorem nielsenCappedEndMarks_finite : (marks).Finite :=
  (nielsenCappedActualCuspPoint_range_finite hD hNE hFG hfin w hwD hwN J hc hv S hr).union (Set.finite_range
    (capCenter))

theorem nielsenActualCapDisc_mem_endMarks_iff (f:A) (z:𝕔𝔻) : (capDisc) f z∈marks ↔ z=0 := by
  constructor
  · rintro (⟨c,hcEq⟩|⟨g,hg⟩)
    · exact False.elim (nielsenCappedActualCuspPoint_not_capDisc hD hNE hFG hfin w hwD hwN J hc hv S hr c f
      ⟨z,hcEq.symm⟩)
    · by_cases hgf:g=f
      · subst g
        exact ((nielsenActualCapDisc_isClosedEmbedding hD hNE hFG hfin w hwD hwN J hc hv f).injective hg).symm
      · have hd:Disjoint (range ((capDisc) g)) (range ((capDisc) f)):=by
          rw [nielsenActualCapDisc_range,nielsenActualCapDisc_range]
          exact nielsenCappedClosedCap_pairwise_disjoint hD hNE hFG hfin w hwD hwN J hc hv hgf
        exact False.elim (Set.disjoint_left.mp hd ⟨0,rfl⟩ ⟨z,hg.symm⟩)
  · rintro rfl
    exact Or.inr (mem_range_self f)

def nielsenOldCoreIntoPunctured (q:↥coreImage) : Y :=
  ⟨(oldEmbedding) q,by
    have hq:(oldEmbedding) q∈range (modelPoint)\range (cappedCusp):=by
      rw [←nielsenWholeCoreCappedEmbedding_range hD hNE hFG hfin w hwD hwN J hc hv S hr]
      exact mem_range_self q
    rintro (hc|⟨f,hf⟩)
    · exact hq.2 hc
    · exact nielsenActualCapCenter_not_firstFace hD hNE hFG hfin w hwD hwN J hc hv f (hf.symm ▸ hq.1)⟩
local notation "oldInto" => nielsenOldCoreIntoPunctured hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenOldCoreIntoPunctured_isEmbedding : Topology.IsEmbedding (oldInto) :=
  Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
    (nielsenWholeCoreCappedEmbedding_isEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr)

theorem nielsenOldCoreIntoPunctured_range : range (oldInto)=Subtype.val ⁻¹' range (modelPoint) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨q,rfl⟩
    exact ((nielsenWholeCoreCappedEmbedding_range hD hNE hFG hfin w hwD hwN J hc hv S hr) ▸ mem_range_self q).1
  · intro y hy
    have hn:y.val∉range (cappedCusp):=fun h=>y.property (Or.inl h)
    have hm:y.val∈range (oldEmbedding):=(nielsenWholeCoreCappedEmbedding_range hD hNE hFG hfin w hwD hwN J hc hv S
      hr).symm ▸ ⟨hy,hn⟩
    obtain ⟨q,hq⟩:=hm
    exact ⟨q,Subtype.ext hq⟩

def nielsenCapIntoPunctured (f:A) (z:NielsenPuncturedClosedDisc) : Y :=
  ⟨(capDisc) f z.val,fun hz=>z.property
    (congrArg (fun p:𝕔𝔻=>(p:ℂ)) ((nielsenActualCapDisc_mem_endMarks_iff hD hNE hFG hfin w hwD hwN J hc hv S hr f
      z.val).mp hz))⟩
local notation "capInto" => nielsenCapIntoPunctured hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenCapIntoPunctured_isEmbedding (f:A) : Topology.IsEmbedding ((capInto) f) :=
  Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
    ((nielsenActualCapDisc_isClosedEmbedding hD hNE hFG hfin w hwD hwN J hc hv f).isEmbedding.comp
      Topology.IsEmbedding.subtypeVal)

theorem nielsenCapIntoPunctured_range (f:A) : range ((capInto) f)=Subtype.val ⁻¹' range ((capDisc) f) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z,rfl⟩
    exact mem_range_self z.val
  · rintro y ⟨z,hz⟩
    have hzne:z.val≠0:=by
      intro h0
      have hz0:z=0:=Subtype.ext h0
      exact y.property (hz ▸ ((nielsenActualCapDisc_mem_endMarks_iff hD hNE hFG hfin w hwD hwN J hc hv S hr f z).mpr
        hz0))
    exact ⟨⟨z,hzne⟩,Subtype.ext hz⟩

def nielsenCappedPuncturedCover : Option A→Set Y
  | none=>Subtype.val ⁻¹' range (modelPoint)
  | some f=>Subtype.val ⁻¹' range ((capDisc) f)
local notation "cover" => nielsenCappedPuncturedCover hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenCappedPuncturedCover_isClosed (i:Option A) : IsClosed ((cover) i) := by
  cases i with
  | none =>
    have hcFirst:IsClosed (range (modelPoint)):=by
      rw [←nielsenCompletedCoreCappedEmbedding_range hD hNE hFG hfin w hwD hwN J hc hv S hr]
      exact (nielsenCompletedCoreCappedEmbedding_isClosedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S
        hr).isClosed_range
    exact hcFirst.preimage continuous_subtype_val
  | some f => exact (nielsenActualCapDisc_isClosedEmbedding hD hNE hFG hfin w hwD hwN J hc hv
    f).isClosed_range.preimage continuous_subtype_val

theorem nielsenCappedPuncturedCover_covers : (⋃i:Option A,(cover) i)=univ := by
  apply Set.Subset.antisymm (subset_univ _) ?_
  intro y _hy
  by_cases hy:y.val∈range (modelPoint)
  · exact mem_iUnion.mpr ⟨none,hy⟩
  · have hcap:y.val∈⋃f:A,range ((openCap) f.val):=by
      rw [←nielsenCappedFirstFace_complement_eq hD hNE hFG hfin w hwD hwN J hc hv]
      exact hy
    obtain ⟨f,z,hz⟩:=mem_iUnion.mp hcap
    refine mem_iUnion.mpr ⟨some f,?_⟩
    exact ⟨Hyperbolic.discToClosedModel z,hz⟩

end NielsenCappedPuncturedSurface


theorem nielsenOriginalCoreProjection_isClosed
    {H:Subgroup Mobius.complexMobiusGroup}
    (P:UnitDiscFuchsianGroup H) (hNE:DiscreteGroups.IsNonElementary H) :
    IsClosed (Surfaces.mobiusDomainProjection P.domain '' closure (fuchsianNielsenCore P hNE)) := by
  apply (Surfaces.mobiusDomainProjection_isOpenQuotientMap P.domain).isQuotientMap.isCoinducing.isClosed_preimage.mp
  have he:Surfaces.mobiusDomainProjection P.domain ⁻¹'
      (Surfaces.mobiusDomainProjection P.domain '' closure (fuchsianNielsenCore P hNE))=closure (fuchsianNielsenCore P hNE):=by
    apply Set.Subset.antisymm
    · rintro x ⟨y,hy,hxy⟩
      obtain ⟨g,hg⟩:=Quotient.exact hxy.symm
      rw [←fuchsianNielsenCore_smul_closure P hNE g]
      exact ⟨y,hy,hg⟩
    · intro x hx
      exact ⟨x,hx,rfl⟩
  rw [he]
  exact isClosed_closure


section NielsenWholeQuotientClosedCover
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
  {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "W" => FiniteCyclicPresentation.PolygonalRealization
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv)
  (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)
local notation "A" => {f:FiniteCyclicPresentation.Face
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv) //
  f≠nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv}
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "coreHomeo" => nielsenCappedFirstFaceCompletedCoreHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "F" => nielsenCappedFirstFaceCompletedCoreMap hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "openCap" => nielsenCappedFaceInterior hD hNE hFG hfin w hwD hwN J hc hv
local notation "closedCap" => nielsenCappedClosedCap hD hNE hFG hfin w hwD hwN J hc hv
local notation "clock" => nielsenCappedCapClock hD hNE hFG hfin w hwD hwN J hc hv
local notation "originalClock" => nielsenCappedOriginalCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "capCycle" => nielsenCappedCapCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv



local notation "coreEmbedding" => nielsenCompletedCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "coreClock" => nielsenCompletedCoreCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "quotientClock" => nielsenCappedOriginalQuotientClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "old" => fuchsianCuspCompletionOld P.asFuchsianDisc
local notation "cusp" => fuchsianCuspCompletionPoint P.asFuchsianDisc
local notation "coreImage" => (Surfaces.mobiusDomainProjection P.domain) '' closure (fuchsianNielsenCore P hNE)
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "weight" => nielsenRawCornerClassWeight hD hNE hFG hfin w hwD hwN J hc hv


local notation "cappedCusp" => nielsenCappedActualCuspPoint hD hNE hFG hfin w hwD hwN J hc hv S hr


local notation "capDisc" => nielsenActualCapDisc hD hNE hFG hfin w hwD hwN J hc hv
local notation "capCenter" => nielsenActualCapCenter hD hNE hFG hfin w hwD hwN J hc hv
local notation "oldEmbedding" => nielsenWholeCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr


local notation "marks" => nielsenCappedEndMarks hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "Y" => ↥((marks)ᶜ)
local notation "sourceImage" => nielsenBoundaryCycleFunnel hD hNE hFG hfin w hwD hwN J hc hv
local notation "targetCover" => nielsenCappedPuncturedCover hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "oldInto" => nielsenOldCoreIntoPunctured hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "capInto" => nielsenCapIntoPunctured hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "aligned" => nielsenAlignedFunnelHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "clockInFunnel" => nielsenCappedQuotientClockInFunnel hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "clockInCore" => nielsenCappedQuotientClockInCore hD hNE hFG hfin w hwD hwN J hc hv S hr

def nielsenWholeQuotientCover : Option A→Set
    (Surfaces.MobiusDomainQuotient P.domain)
  | none=>coreImage
  | some f=>sourceImage ((capCycle) f.val f.property)
local notation "sourceCover" => nielsenWholeQuotientCover hD hNE hFG hfin w hwD hwN J hc hv

theorem nielsenWholeQuotientCover_isClosed (i:Option A) : IsClosed ((sourceCover) i) := by
  cases i with
  | none => exact nielsenOriginalCoreProjection_isClosed P hNE
  | some f => exact nielsenBoundaryCycleFunnel_isClosed hD hNE hFG hfin w hwD hwN J hc hv _

theorem nielsenWholeQuotientCover_covers : (⋃i:Option A,(sourceCover) i)=univ := by
  apply Set.Subset.antisymm (subset_univ _) ?_
  intro q _hq
  have hq:q∈coreImage∪⋃c:NielsenCyclicBoundaryClasses hD hNE hFG hfin w hwD hwN J hc hv,sourceImage c:=by
    rw [←nielsenBoundaryCycleFunnels_whole_quotient_cover hD hNE hFG hfin w hwD hwN J hc hv]
    trivial
  rcases hq with hq|hq
  · exact mem_iUnion.mpr ⟨none,hq⟩
  · obtain ⟨c,hcQ⟩:=mem_iUnion.mp hq
    obtain ⟨f,hfc⟩:=(nielsenCappedCapCycle_bijective hD hNE hFG hfin w hwD hwN J hc hv).2 c
    refine mem_iUnion.mpr ⟨some f,?_⟩
    change q∈sourceImage ((capCycle) f.val f.property)
    exact (congrArg (fun c=>q∈sourceImage c) hfc).mpr hcQ

def nielsenWholeQuotientPieceHomeomorph : ∀i:Option A,↥((sourceCover) i)≃ₜ↥((targetCover) i)
  | none=>(nielsenOldCoreIntoPunctured_isEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr).toHomeomorph.trans
      (Homeomorph.setCongr (nielsenOldCoreIntoPunctured_range hD hNE hFG hfin w hwD hwN J hc hv S hr))
  | some f=>((aligned) f).trans
      ((nielsenCapIntoPunctured_isEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr f).toHomeomorph.trans
        (Homeomorph.setCongr (nielsenCapIntoPunctured_range hD hNE hFG hfin w hwD hwN J hc hv S hr f)))
local notation "piece" => nielsenWholeQuotientPieceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenWholeQuotientPieceHomeomorph_core_coe (x:↥((sourceCover) none)) :
    (((piece) none x).val).val=(oldEmbedding) x := rfl

theorem nielsenWholeQuotientPieceHomeomorph_cap_coe (f:A) (x:↥((sourceCover) (some f))) :
    (((piece) (some f) x).val).val=(capDisc) f (((aligned) f x).val) := rfl

theorem nielsenWholeQuotientPieceHomeomorph_clock_core (f:A) (z:Circle) :
    (((piece) none ((clockInCore) f z)).val).val=(clock) f.val z :=
  nielsenWholeCoreCappedEmbedding_clock hD hNE hFG hfin w hwD hwN J hc hv S hr f z

theorem nielsenWholeQuotientPieceHomeomorph_clock_cap (f:A) (z:Circle) :
    (((piece) (some f) ((clockInFunnel) f z)).val).val=(clock) f.val z := by
  rw [nielsenWholeQuotientPieceHomeomorph_cap_coe,
    nielsenAlignedFunnelHomeomorph_clock,nielsenActualCapDisc_boundary]

theorem nielsenWholeQuotientPieceHomeomorph_core_cap_agree
    (f:A) (x:Surfaces.MobiusDomainQuotient P.domain) (hx:x∈coreImage)
    (hxF:x∈sourceImage ((capCycle) f.val f.property)) :
    ((piece) none ⟨x,hx⟩).val=((piece) (some f) ⟨x,hxF⟩).val := by
  have hxC:x∈cycleCarrier ((capCycle) f.val f.property):=
    (nielsenBoundaryCycleFunnel_inter_core hD hNE hFG hfin w hwD hwN J hc hv _) ▸ ⟨hxF,hx⟩
  rw [←nielsenCappedOriginalQuotientClock_range hD hNE hFG hfin w hwD hwN J hc hv S hr f] at hxC
  obtain ⟨z,hz⟩:=hxC
  have hCore:(⟨x,hx⟩:↥coreImage)=(clockInCore) f z:=Subtype.ext hz.symm
  have hFunnel:(⟨x,hxF⟩:↥(sourceImage ((capCycle) f.val f.property)))=(clockInFunnel) f z:=Subtype.ext hz.symm
  apply Subtype.ext
  calc
    (((piece) none ⟨x,hx⟩).val).val=(((piece) none ((clockInCore) f z)).val).val:=
      congrArg (fun q=>(((piece) none q).val).val) hCore
    _=(clock) f.val z:=nielsenWholeQuotientPieceHomeomorph_clock_core hD hNE hFG hfin w hwD hwN J hc hv S hr f z
    _=(((piece) (some f) ((clockInFunnel) f z)).val).val:=
      (nielsenWholeQuotientPieceHomeomorph_clock_cap hD hNE hFG hfin w hwD hwN J hc hv S hr f z).symm
    _=(((piece) (some f) ⟨x,hxF⟩).val).val:=congrArg (fun q=>(((piece) (some f) q).val).val) hFunnel.symm

end NielsenWholeQuotientClosedCover


section NielsenWholeQuotientPasting
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
  {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "W" => FiniteCyclicPresentation.PolygonalRealization
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv)
  (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)
local notation "A" => {f:FiniteCyclicPresentation.Face
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv) //
  f≠nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv}
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "coreHomeo" => nielsenCappedFirstFaceCompletedCoreHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "F" => nielsenCappedFirstFaceCompletedCoreMap hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "openCap" => nielsenCappedFaceInterior hD hNE hFG hfin w hwD hwN J hc hv
local notation "closedCap" => nielsenCappedClosedCap hD hNE hFG hfin w hwD hwN J hc hv
local notation "clock" => nielsenCappedCapClock hD hNE hFG hfin w hwD hwN J hc hv
local notation "originalClock" => nielsenCappedOriginalCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "capCycle" => nielsenCappedCapCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv



local notation "coreEmbedding" => nielsenCompletedCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "coreClock" => nielsenCompletedCoreCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "quotientClock" => nielsenCappedOriginalQuotientClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "old" => fuchsianCuspCompletionOld P.asFuchsianDisc
local notation "cusp" => fuchsianCuspCompletionPoint P.asFuchsianDisc
local notation "coreImage" => (Surfaces.mobiusDomainProjection P.domain) '' closure (fuchsianNielsenCore P hNE)
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "weight" => nielsenRawCornerClassWeight hD hNE hFG hfin w hwD hwN J hc hv


local notation "cappedCusp" => nielsenCappedActualCuspPoint hD hNE hFG hfin w hwD hwN J hc hv S hr


local notation "capDisc" => nielsenActualCapDisc hD hNE hFG hfin w hwD hwN J hc hv
local notation "capCenter" => nielsenActualCapCenter hD hNE hFG hfin w hwD hwN J hc hv
local notation "oldEmbedding" => nielsenWholeCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr


local notation "marks" => nielsenCappedEndMarks hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "Y" => ↥((marks)ᶜ)
local notation "sourceImage" => nielsenBoundaryCycleFunnel hD hNE hFG hfin w hwD hwN J hc hv
local notation "targetCover" => nielsenCappedPuncturedCover hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "oldInto" => nielsenOldCoreIntoPunctured hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "capInto" => nielsenCapIntoPunctured hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "aligned" => nielsenAlignedFunnelHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "clockInFunnel" => nielsenCappedQuotientClockInFunnel hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "clockInCore" => nielsenCappedQuotientClockInCore hD hNE hFG hfin w hwD hwN J hc hv S hr

local notation "sourceCover" => nielsenWholeQuotientCover hD hNE hFG hfin w hwD hwN J hc hv
local notation "piece" => nielsenWholeQuotientPieceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenWholeQuotientPieceHomeomorph_compatible :
    ∀i j (x:Surfaces.MobiusDomainQuotient P.domain) (hi:x∈sourceCover i) (hj:x∈sourceCover j),
      ((piece) i ⟨x,hi⟩).val=((piece) j ⟨x,hj⟩).val := by
  intro i j x hi hj
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some f => exact nielsenWholeQuotientPieceHomeomorph_core_cap_agree hD hNE hFG hfin w hwD hwN J hc hv S hr f x hi hj
  | some f =>
    cases j with
    | none => exact (nielsenWholeQuotientPieceHomeomorph_core_cap_agree hD hNE hFG hfin w hwD hwN J hc hv S hr f x hj
      hi).symm
    | some g =>
      by_cases hfg:f=g
      · subst g
        rfl
      · have hcycles:(capCycle) f.val f.property≠(capCycle) g.val g.property:=by
          intro he
          exact hfg ((nielsenCappedCapCycle_injective hD hNE hFG hfin w hwD hwN J hc hv) he)
        exact False.elim (Set.disjoint_left.mp
          (nielsenBoundaryCycleFunnels_pairwise_disjoint hD hNE hFG hfin w hwD hwN J hc hv hcycles) hi hj)

theorem nielsenWholeQuotientPieceHomeomorph_inverse_core_cap_agree
    (f:A) (y:Y) (hy:y∈targetCover none) (hyF:y∈targetCover (some f)) :
    (((piece) none).symm ⟨y,hy⟩).val=(((piece) (some f)).symm ⟨y,hyF⟩).val := by
  have hyFirst:y.val∈range (modelPoint):=hy
  have hyDisc:y.val∈range ((capDisc) f):=hyF
  rw [nielsenActualCapDisc_range] at hyDisc
  have hyClock:y.val∈range ((clock) f.val):=by
    rw [nielsenCappedCapClock_range hD hNE hFG hfin w hwD hwN J hc hv f.val f.property]
    exact ⟨hyDisc,hyFirst⟩
  obtain ⟨z,hz⟩:=hyClock
  have hn:(piece) none ((clockInCore) f z)=⟨y,hy⟩:=by
    apply Subtype.ext
    apply Subtype.ext
    exact (nielsenWholeQuotientPieceHomeomorph_clock_core hD hNE hFG hfin w hwD hwN J hc hv S hr f z).trans hz
  have hf:(piece) (some f) ((clockInFunnel) f z)=⟨y,hyF⟩:=by
    apply Subtype.ext
    apply Subtype.ext
    exact (nielsenWholeQuotientPieceHomeomorph_clock_cap hD hNE hFG hfin w hwD hwN J hc hv S hr f z).trans hz
  have hn':((piece) none).symm ⟨y,hy⟩=(clockInCore) f z:=by
    apply ((piece) none).injective
    exact (((piece) none).apply_symm_apply _).trans hn.symm
  have hf':((piece) (some f)).symm ⟨y,hyF⟩=(clockInFunnel) f z:=by
    apply ((piece) (some f)).injective
    exact (((piece) (some f)).apply_symm_apply _).trans hf.symm
  rw [hn',hf']
  rfl

theorem nielsenWholeQuotientPieceHomeomorph_inverse_compatible :
    ∀i j (y:Y) (hi:y∈targetCover i) (hj:y∈targetCover j),
      (((piece) i).symm ⟨y,hi⟩).val=(((piece) j).symm ⟨y,hj⟩).val := by
  intro i j y hi hj
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some f => exact nielsenWholeQuotientPieceHomeomorph_inverse_core_cap_agree hD hNE hFG hfin w hwD hwN J hc hv S hr f y hi hj
  | some f =>
    cases j with
    | none => exact (nielsenWholeQuotientPieceHomeomorph_inverse_core_cap_agree hD hNE hFG hfin w hwD hwN J hc hv S hr f
      y hj hi).symm
    | some g =>
      by_cases hfg:f=g
      · subst g
        rfl
      · have hd:Disjoint (range ((capDisc) f)) (range ((capDisc) g)):=by
          rw [nielsenActualCapDisc_range,nielsenActualCapDisc_range]
          exact nielsenCappedClosedCap_pairwise_disjoint hD hNE hFG hfin w hwD hwN J hc hv hfg
        exact False.elim (Set.disjoint_left.mp hd hi hj)

/-- The original whole orbit surface is the very same faithful capped Nielsen
surface with its actual cusp points and its actual cap centres removed.
The pointwise equalities retain its genuine old-core and funnel maps. -/
theorem nielsenWholeQuotient_same_capped_surface :
    ∃E:Surfaces.MobiusDomainQuotient P.domain≃ₜY,
      (∀i (x:↥((sourceCover) i)),E x=((piece) i x).val) ∧
      (∀i (y:↥((targetCover) i)),E.symm y=(((piece) i).symm y).val) := by
  exact Auxiliary.Topology.finite_closed_cover_homeomorph (sourceCover) (targetCover)
    (nielsenWholeQuotientCover_covers hD hNE hFG hfin w hwD hwN J hc hv)
    (nielsenCappedPuncturedCover_covers hD hNE hFG hfin w hwD hwN J hc hv S hr)
    (nielsenWholeQuotientCover_isClosed hD hNE hFG hfin w hwD hwN J hc hv)
    (nielsenCappedPuncturedCover_isClosed hD hNE hFG hfin w hwD hwN J hc hv S hr)
    (piece)
    (nielsenWholeQuotientPieceHomeomorph_compatible hD hNE hFG hfin w hwD hwN J hc hv S hr)
    (nielsenWholeQuotientPieceHomeomorph_inverse_compatible hD hNE hFG hfin w hwD hwN J hc hv S hr)

end NielsenWholeQuotientPasting


section NielsenActualEndLabels
open LeanEval.Topology.ClassificationOfSurfaces
open FiniteCyclicPresentation SurfaceCellComplex
open LowDimensionalTopology.Geometry.Surfaces.CyclicSurface
open scoped Classical
variable {H:Subgroup Mobius.complexMobiusGroup} {P:UnitDiscFuchsianGroup H}
  {D:Set P.domain.carrier} (hD:IsConvexFuchsianPolygon P D)
  (hNE:DiscreteGroups.IsNonElementary H) (hFG:H.FG)
  (hfin:{S:Set P.domain.carrier | IsFuchsianPolygonSide P D S}.Finite)
  (w:P.domain.carrier) (hwD:w∈D) (hwN:w∈fuchsianNielsenCore P hNE)
  (J:Moise.PolygonalCircle)
  (hc:J.carrier=Polygon.discPolygonKleinPlane '' (⋃s:NielsenBoundarySide hD hNE,s.carrier))
  (hv:∀p,J.IsVertexPoint p↔p∈Polygon.discPolygonKleinPlane '' nielsenCanonicalBoundaryMarks hD hNE hFG)
  {n:ℕ} (S:Polygon.CyclicDiscPolygonSupportData n)
  (hr:S.toCenteredData.kleinRegion=fuchsianPolygonCompactKlein P (D∩fuchsianNielsenCore P hNE))
local notation "Q" => D∩fuchsianNielsenCore P hNE
local notation "K" => Hyperbolic.discClosedModelClosure (P.finiteCoordinate '' Q)
local notation "Pcap" => nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv
local notation "valid" => nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv
local notation "f₀" => nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv
local notation "W" => FiniteCyclicPresentation.PolygonalRealization
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv)
  (nielsenCappedPresentation_valid hD hNE hFG hfin w hwD hwN J hc hv)
local notation "A" => {f:FiniteCyclicPresentation.Face
  (nielsenCappedPresentation hD hNE hFG hfin w hwD hwN J hc hv) //
  f≠nielsenCappedOriginalFace hD hNE hFG hfin w hwD hwN J hc hv}
local notation "modelPoint" => nielsenCappedOriginalModelPoint hD hNE hFG hfin w hwD hwN J hc hv
local notation "coreHomeo" => nielsenCappedFirstFaceCompletedCoreHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "F" => nielsenCappedFirstFaceCompletedCoreMap hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "openCap" => nielsenCappedFaceInterior hD hNE hFG hfin w hwD hwN J hc hv
local notation "closedCap" => nielsenCappedClosedCap hD hNE hFG hfin w hwD hwN J hc hv
local notation "clock" => nielsenCappedCapClock hD hNE hFG hfin w hwD hwN J hc hv
local notation "originalClock" => nielsenCappedOriginalCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "capCycle" => nielsenCappedCapCycle hD hNE hFG hfin w hwD hwN J hc hv
local notation "cycleCarrier" => nielsenProjectedBoundaryCycle hD hNE hFG hfin w hwD hwN J hc hv



local notation "coreEmbedding" => nielsenCompletedCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "coreClock" => nielsenCompletedCoreCapClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "quotientClock" => nielsenCappedOriginalQuotientClock hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "old" => fuchsianCuspCompletionOld P.asFuchsianDisc
local notation "cusp" => fuchsianCuspCompletionPoint P.asFuchsianDisc
local notation "coreImage" => (Surfaces.mobiusDomainProjection P.domain) '' closure (fuchsianNielsenCore P hNE)
local notation "V" => NielsenCoreRawCornerClasses hD hNE hFG hfin w hwD hwN J hc hv
local notation "weight" => nielsenRawCornerClassWeight hD hNE hFG hfin w hwD hwN J hc hv


local notation "cappedCusp" => nielsenCappedActualCuspPoint hD hNE hFG hfin w hwD hwN J hc hv S hr


local notation "capDisc" => nielsenActualCapDisc hD hNE hFG hfin w hwD hwN J hc hv
local notation "capCenter" => nielsenActualCapCenter hD hNE hFG hfin w hwD hwN J hc hv
local notation "oldEmbedding" => nielsenWholeCoreCappedEmbedding hD hNE hFG hfin w hwD hwN J hc hv S hr


local notation "marks" => nielsenCappedEndMarks hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "Y" => ↥((marks)ᶜ)
local notation "sourceImage" => nielsenBoundaryCycleFunnel hD hNE hFG hfin w hwD hwN J hc hv
local notation "targetCover" => nielsenCappedPuncturedCover hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "oldInto" => nielsenOldCoreIntoPunctured hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "capInto" => nielsenCapIntoPunctured hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "aligned" => nielsenAlignedFunnelHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "clockInFunnel" => nielsenCappedQuotientClockInFunnel hD hNE hFG hfin w hwD hwN J hc hv S hr
local notation "clockInCore" => nielsenCappedQuotientClockInCore hD hNE hFG hfin w hwD hwN J hc hv S hr

local notation "sourceCover" => nielsenWholeQuotientCover hD hNE hFG hfin w hwD hwN J hc hv
local notation "piece" => nielsenWholeQuotientPieceHomeomorph hD hNE hFG hfin w hwD hwN J hc hv S hr


/-- Every removed point is labelled by an actual original cusp or by an actual
geodesic-boundary cap; the two label types are not identified. -/
def nielsenCappedEndLabel : FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic ⊕ A→W :=
  Sum.elim (cappedCusp) (capCenter)
local notation "endLabel" => nielsenCappedEndLabel hD hNE hFG hfin w hwD hwN J hc hv S hr

theorem nielsenCappedEndLabel_injective : Function.Injective (endLabel) := by
  intro a b hab
  cases a with
  | inl c =>
    cases b with
    | inl d => exact congrArg Sum.inl ((nielsenCappedActualCuspPoint_injective hD hNE hFG hfin w hwD hwN J hc hv S hr)
      hab)
    | inr f => exact False.elim (nielsenCappedActualCuspPoint_not_capDisc hD hNE hFG hfin w hwD hwN J hc hv S hr c f
      ⟨0,hab.symm⟩)
  | inr f =>
    cases b with
    | inl c => exact False.elim (nielsenCappedActualCuspPoint_not_capDisc hD hNE hFG hfin w hwD hwN J hc hv S hr c f
      ⟨0,hab⟩)
    | inr k => exact congrArg Sum.inr ((nielsenActualCapCenter_injective hD hNE hFG hfin w hwD hwN J hc hv) hab)

theorem nielsenCappedEndLabel_range : range (endLabel)=marks := by
  ext z
  constructor
  · rintro ⟨c|f,rfl⟩
    · exact Or.inl (mem_range_self c)
    · exact Or.inr (mem_range_self f)
  · rintro (⟨c,rfl⟩|⟨f,rfl⟩)
    · exact ⟨Sum.inl c,rfl⟩
    · exact ⟨Sum.inr f,rfl⟩

def nielsenCappedEndLabelEquiv :
    (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic ⊕ A)≃↥marks :=
  (Equiv.ofInjective (endLabel) (nielsenCappedEndLabel_injective hD hNE hFG hfin w hwD hwN J hc hv S hr)).trans
    (Set.equivOfEq (nielsenCappedEndLabel_range hD hNE hFG hfin w hwD hwN J hc hv S hr))

theorem nielsenCappedEndMarks_card :
    Nat.card ↥marks=Nat.card (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic)+
      Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc) := by
  let e:=nielsenRawIdealCuspEquiv hD hNE hFG hfin w hwD hwN J hc hv S hr
  let:Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic):=
    Finite.of_surjective e e.surjective
  rw [←Nat.card_congr (nielsenCappedEndLabelEquiv hD hNE hFG hfin w hwD hwN J hc hv S hr),Nat.card_sum,
    nielsenCappedCapFaceCount_eq hD hNE hFG hfin w hwD hwN J hc hv]

include S hr in
/-- The Nielsen area uses the actual topological genus of this same surface,
whose complement of the genuinely labelled ends is the original whole quotient. -/
theorem nielsenCore_area_of_same_capped_surface_genus
    (g:ℕ)
    (hg:Surfaces.HasTopologicalGenus W g) :
    let _nielsenOriginalEndEllipticFinite:Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
      finite_sided_polygon_elliptic_classes_finite hD hfin
    (fuchsianNielsenCoreArea P hNE D).toReal=2*Real.pi*
      (2*(g:ℝ)-2+Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc)+
        Nat.card (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic)+
        ((fuchsianEllipticOrderList P.asFuchsianDisc).map (fun m:ℕ=>1-1/(m:ℝ))).sum) := by
  let _nielsenOriginalEndEllipticFinite:Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    finite_sided_polygon_elliptic_classes_finite hD hfin
  obtain ⟨k,hk,ha⟩:=nielsenCappedWord_genus_actualBoundaryElliptic_area hD hNE hFG hfin w hwD hwN J hc hv
  have hkg:k=g:=Surfaces.hasTopologicalGenus_unique hk hg
  subst k
  rw [nielsenRawIdealClassCount_eq_actualCusps hD hNE hFG hfin w hwD hwN J hc hv S hr] at ha
  exact ha

/-- A faithful compactification of the original whole quotient, with actual
elliptic, cusp and geodesic-boundary counts and the exact Nielsen area. -/
theorem nielsenWholeQuotient_same_surface_genus_area :
    let _nielsenOriginalEndEllipticFinite:Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
      finite_sided_polygon_elliptic_classes_finite hD hfin
    ∃g,Surfaces.HasTopologicalGenus W g ∧
      Nonempty (Surfaces.MobiusDomainQuotient P.domain≃ₜY) ∧ (marks).Finite ∧
      Nat.card ↥marks=Nat.card (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic)+
        Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc) ∧
      (fuchsianNielsenCoreArea P hNE D).toReal=2*Real.pi*
        (2*(g:ℝ)-2+Nat.card (FuchsianBoundaryHyperbolicCyclicConjugacyClasses P.asFuchsianDisc)+
          Nat.card (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .parabolic)+
          ((fuchsianEllipticOrderList P.asFuchsianDisc).map (fun m:ℕ=>1-1/(m:ℝ))).sum) := by
  let _nielsenOriginalEndEllipticFinite:Finite (FuchsianCyclicConjugacyClasses P.asFuchsianDisc .elliptic):=
    finite_sided_polygon_elliptic_classes_finite hD hfin
  obtain ⟨g,hg,_⟩:=nielsenCappedWord_genus_actualBoundaryElliptic_area hD hNE hFG hfin w hwD hwN J hc hv
  obtain ⟨E,_⟩:=nielsenWholeQuotient_same_capped_surface hD hNE hFG hfin w hwD hwN J hc hv S hr
  exact ⟨g,hg,⟨E⟩,nielsenCappedEndMarks_finite hD hNE hFG hfin w hwD hwN J hc hv S hr,
    nielsenCappedEndMarks_card hD hNE hFG hfin w hwD hwN J hc hv S hr,
    nielsenCore_area_of_same_capped_surface_genus hD hNE hFG hfin w hwD hwN J hc hv S hr g hg⟩

end NielsenActualEndLabels

end LowDimensionalTopology.Geometry.Fuchsian
