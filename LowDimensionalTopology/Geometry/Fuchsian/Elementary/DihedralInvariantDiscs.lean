/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.IdealBoundaryAction
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Elementary.DihedralNearestOrbits
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.FullHalfPlaneIsometries
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenConvexity
@[expose] public section
noncomputable section
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The boundary of a genuine disc preserved by a positive hyperbolic
 scaling and the negative reciprocal is the actual compactified real axis. -/
theorem dihedral_invariantDisc_frontier {D : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hD :
  _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D)
    (d : ℝ) (hd : 1<d)
    (hS : (fuchsianPositiveDilation d (by linarith)).val '' D=D)
    (hJ : fuchsianDihedralFlip.val '' D=D) : frontier D=_root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis := by
  let a : ℂˣ:=Units.mk0 (d:ℂ) (Complex.ofReal_ne_zero.mpr (by linarith only [hd]))
  have hn : ‖(a:ℂ)‖≠1:=by
    change ‖(d:ℂ)‖≠1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith only [hd])]
    linarith only [hd]
  have ha1 : (a:ℂ)≠1:=by intro he;apply hn;rw [he,norm_one]
  have hL : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a):=by
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_eq_standard a ha1]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement_loxodromic_iff a).mpr hn
  have hHyp : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling a):=⟨hL,D,hD,hS⟩
  have hzero : ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈frontier D:=
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_fixed_mem_disc_frontier _ hHyp hD hS (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero a)
  have hinfty : ∞∈frontier D:=
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_fixed_mem_disc_frontier _ hHyp hD hS (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty a)
  have hJi : fuchsianDihedralFlip.val (Complex.I:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(Complex.I:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
    rw [fuchsianDihedralFlip_coe _ Complex.I_ne_zero]
    congr 1
    apply (div_eq_iff Complex.I_ne_zero).mpr
    simp
  have hnoti : (Complex.I:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∉frontier D:=
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_fixed_not_mem_disc_frontier _ circleObstruction_dihedralFlip_elliptic hD hJ hJi
  have hround:=_root_.LowDimensionalTopology.Geometry.Mobius.complexDisc_frontier_isGeneralized hD
  rcases (_root_.LowDimensionalTopology.Geometry.Mobius.isComplexGeneralizedCircle_iff (frontier D)).mp hround with
    ⟨c,r,_,he⟩|⟨v,t,hv,he⟩
  · exact (_root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_infty c r (he ▸ hinfty)).elim
  · have ht : t=0:=by
      have hz:=hzero
      rw [he,_root_.LowDimensionalTopology.Geometry.Mobius.complexLine_coe] at hz
      simpa using hz.symm
    subst t
    have hstable : fuchsianDihedralFlip.val '' frontier D=frontier D:=by
      have hh:=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
        fuchsianDihedralFlip).image_frontier D
      change fuchsianDihedralFlip.val '' frontier D=frontier (fuchsianDihedralFlip.val '' D) at hh
      rwa [hJ] at hh
    have hz : ((Complex.I*v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈frontier D:=by
      rw [he,_root_.LowDimensionalTopology.Geometry.Mobius.complexLine_coe]
      simp [Complex.inner,Complex.mul_re,Complex.mul_im]
      ring
    have hz0 : Complex.I*v≠0:=mul_ne_zero Complex.I_ne_zero hv
    have hzm : ((-1/(Complex.I*v):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈frontier D:=by
      rw [←hstable]
      exact ⟨_,hz,fuchsianDihedralFlip_coe _ hz0⟩
    rw [he,_root_.LowDimensionalTopology.Geometry.Mobius.complexLine_coe] at hzm
    have hnorm : v.re^2+v.im^2≠0:=by
      simpa only [Complex.normSq_apply,pow_two] using (Complex.normSq_pos.mpr hv).ne'
    have hprod : v.re*v.im=0:=by
      simp [Complex.inner,Complex.mul_re,Complex.mul_im,
        Complex.normSq_apply] at hzm
      field_simp [hnorm] at hzm
      nlinarith only [hzm]
    have him : v.im≠0:=by
      intro him
      apply hnoti
      rw [he,_root_.LowDimensionalTopology.Geometry.Mobius.complexLine_coe]
      simp [Complex.inner,him]
    have hre : v.re=0:=(mul_eq_zero.mp hprod).resolve_right him
    have hone : ((1:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈frontier D:=by
      rw [he,_root_.LowDimensionalTopology.Geometry.Mobius.complexLine_coe]
      simpa [Complex.inner] using hre
    exact _root_.LowDimensionalTopology.Geometry.Mobius.complexCircle_through_zero_one_infty hround hzero hone hinfty

/-- The half-turn about the origin exchanges the two genuine sides of
 the compactified real line. -/
def dihedralLowerHalfPlane : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex:=
  (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
    (-1)).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet

theorem dihedralMinus_preserves_realAxis :
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)).val '' _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis=_root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis := by
  have hiff (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)).val z∈_root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis ↔ z∈_root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis:=by
    cases z using OnePoint.rec with
    | infty => rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty]
    | coe z => simp only [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe,Units.val_neg,Units.val_one,neg_one_mul,
        _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis_coe,Complex.neg_im,neg_eq_zero]
  ext z
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (hiff x).mpr hx
  · intro hz
    refine ⟨(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)).val.symm z,?_,by simp⟩
    exact (hiff _).mp (by simpa using hz)

theorem dihedralLowerHalfPlane_isDisc : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc dihedralLowerHalfPlane:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet_isComplexOpenDisc.image _

theorem dihedralLowerHalfPlane_frontier : frontier dihedralLowerHalfPlane=_root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis := by
  have hh:=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
    (-1))).image_frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)).val '' frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=frontier dihedralLowerHalfPlane at hh
  rw [nielsen_openHalfPlane_frontier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary_eq_realAxis,dihedralMinus_preserves_realAxis] at hh
  exact hh.symm

theorem dihedralLowerHalfPlane_coe (z : ℂ) :
    (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈dihedralLowerHalfPlane ↔ z.im<0 := by
  constructor
  · rintro ⟨x,hx,he⟩
    obtain ⟨v,hv,rfl⟩:=hx
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe] at he
    have he' : -v=z:=by simpa using OnePoint.coe_injective he
    rw [←he',Complex.neg_im]
    change 0<v.im at hv
    linarith only [hv]
  · intro hz
    refine ⟨((-z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),?_,?_⟩
    · exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_openHalfPlaneSet _).mpr (by simpa only [Complex.neg_im,neg_pos] using hz)
    · rw [_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe]
      simp

/-- The real-axis boundary determines exactly the upper or lower genuine
 disc, without assuming a preferred side of the original conjugator. -/
theorem complexDisc_real_frontier_sides {D : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hD :
  _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D)
    (hf : frontier D=_root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis) : D=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∨ D=dihedralLowerHalfPlane := by
  obtain ⟨z,hz⟩:=hD.isConnected.nonempty
  have hn : z∉frontier D:=by
    apply (mem_interior_iff_notMem_frontier hz).mp
    rwa [hD.isOpen.interior_eq]
  cases z using OnePoint.rec with
  | infty => exact (hn (hf.symm ▸ _root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis_infty)).elim
  | coe z =>
    have hi : z.im≠0:=by
      intro hi
      exact hn (hf.symm ▸ (_root_.LowDimensionalTopology.Geometry.Mobius.complexRealAxis_coe z).mpr hi)
    have he:=_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_component_of_open_preconnected hD.isOpen hD.isConnected.isPreconnected hz
    rw [hf] at he
    rcases lt_or_gt_of_ne hi with hi|hi
    · right
      have hL:=_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_component_of_open_preconnected dihedralLowerHalfPlane_isDisc.isOpen
        dihedralLowerHalfPlane_isDisc.isConnected.isPreconnected ((dihedralLowerHalfPlane_coe z).mpr hi)
      rw [dihedralLowerHalfPlane_frontier] at hL
      exact he.symm.trans hL
    · left
      have hU:=_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_component_of_open_preconnected _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet_isComplexOpenDisc.isOpen
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet_isComplexOpenDisc.isConnected.isPreconnected ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_openHalfPlaneSet z).mpr hi)
      rw [nielsen_openHalfPlane_frontier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneIdealBoundary_eq_realAxis] at hU
      exact he.symm.trans hU

theorem dihedral_invariantDisc_sides {D : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex} (hD :
  _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc D)
    (d : ℝ) (hd : 1<d)
    (hS : (fuchsianPositiveDilation d (by linarith)).val '' D=D)
    (hJ : fuchsianDihedralFlip.val ''
      D=D) : D=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∨ D=dihedralLowerHalfPlane:=
  complexDisc_real_frontier_sides hD (dihedral_invariantDisc_frontier hD d hd hS hJ)

theorem dihedralMinus_square : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)*_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)=1 := by
  rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mul]
  have he : (-1:ℂˣ)*(-1)=1:=by simp
  rw [he,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_one]

theorem dihedralMinus_inv : (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
  (-1))⁻¹=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1):=
  inv_eq_of_mul_eq_one_left dihedralMinus_square

theorem dihedralMinus_normalizes (d : ℝ) (hd : 0<d) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)) (canonicalDihedralGroup d hd)=
      canonicalDihedralGroup d hd := by
  have hS : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)*fuchsianPositiveDilation d hd*(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1))⁻¹=
      fuchsianPositiveDilation d hd:=by
    change _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)*_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling _*(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1))⁻¹=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling _
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_inv,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mul,←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mul]
    congr 1
    rw [mul_comm (-1:ℂˣ) _,mul_assoc,mul_inv_cancel,mul_one]
  have hJ : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)*fuchsianDihedralFlip*(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1))⁻¹=fuchsianDihedralFlip:=by
    rw [dihedralMinus_inv]
    have he : fuchsianDihedralFlip*_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)*fuchsianDihedralFlip:=by
      rw [dihedralFlip_scaling_relation,dihedralMinus_inv]
    rw [mul_assoc,he,←mul_assoc,dihedralMinus_square,one_mul]
  rw [canonicalDihedralGroup,conjugate_closure_pair,hS,hJ]

theorem dihedralMinus_image_lower :
    (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)).val '' dihedralLowerHalfPlane=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  rw [dihedralLowerHalfPlane,Set.image_image]
  have he : (fun z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex=>(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)).val ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)).val z))=id:=by
    funext z
    change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling
      (-1)*_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1))•z=z
    rw [dihedralMinus_square,one_smul]
  rw [he,Set.image_id]

/-- The elementary noncyclic classification can be normalized while
 carrying the original actual invariant disc to the upper half-plane,
 rather than silently choosing a side of its boundary. -/
theorem FuchsianDisc.elementary_halfPlane_dihedral_normal_form {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) (hcyc : ¬IsCyclic
      H) :
    ∃u : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup,∃d : ℝ,∃hd : 1<d,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H=canonicalDihedralGroup d (by linarith) ∧
      u.val '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  obtain hc|⟨u,d,hd,hmodel⟩:=D.elementary_real_classification he
  · exact (hcyc hc).elim
  change _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H=canonicalDihedralGroup d (by linarith) at hmodel
  have hB : _root_.LowDimensionalTopology.Geometry.Mobius.IsComplexOpenDisc (u.val '' D.carrier):=D.isDisc.image u
  have hpres (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f∈canonicalDihedralGroup d (by linarith)) :
      f.val '' (u.val '' D.carrier)=u.val '' D.carrier:=by
    rw [←hmodel] at hf
    obtain ⟨g,hg,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff u
      H f).mp hf
    rw [_root_.LowDimensionalTopology.Geometry.Mobius.stableAxis_conjugate_image,D.image_eq ⟨g,hg⟩]
  rcases dihedral_invariantDisc_sides hB d hd
    (hpres _ (Subgroup.subset_closure (by simp)))
    (hpres _ (Subgroup.subset_closure (by simp))) with hupper|hlower
  · exact ⟨u,d,hd,hmodel,hupper⟩
  · refine ⟨_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)*u,d,hd,?_,?_⟩
    · rw [←_root_.LowDimensionalTopology.Geometry.DiscreteGroups.dilation_subgroupConjugate_compose,hmodel,dihedralMinus_normalizes]
    · change (fun z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex=>(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling (-1)).val (u.val z)) '' D.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
      rw [←Set.image_image,hlower,dihedralMinus_image_lower]

/-- Any actual sphere map carrying the original unit disc onto the
 upper half-plane induces a genuine distance-preserving native coordinate. -/
theorem radius_actual_halfPlane_coordinate {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' P.domain.carrier=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) :
    ∃e : P.domain.carrier ≃ ℍ,
      (∀x,((e x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=q.val x.val) ∧
      ∀x y,dist (e x) (e y)=P.hyperbolicDist x y := by
  have hpres : (q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    change (fun z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex=>q.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val z)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet=_root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    rw [←Set.image_image,cayleyMobius_image_openHalfPlane]
    exact hq
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL (q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) hpres
  let e : P.domain.carrier ≃ ℍ:=P.halfPlaneCoordinate.toEquiv.trans (Homeomorph.smul A).toEquiv
  refine ⟨e,?_,?_⟩
  · intro x
    have hx:=radius_coordinate_sphere P x
    have hh:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A (P.halfPlaneCoordinate x)
    rw [hA,←hx] at hh
    change (q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)•(_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹•x.val)=((A•P.halfPlaneCoordinate x:ℍ):ℂ) at hh
    change (((A•P.halfPlaneCoordinate x:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=q•x.val
    simpa only [mul_smul,smul_inv_smul] using hh.symm
  · intro x y
    exact (isometry_smul ℍ A).dist_eq (P.halfPlaneCoordinate x) (P.halfPlaneCoordinate y)

/-- Actual orbit membership is preserved in both directions by the same
 original sphere normalizer used for the metric coordinate. -/
theorem radius_actual_coordinate_orbit_iff {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (e :
      P.domain.carrier→ℍ)
    (he : ∀x,((e x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=q.val x.val) (z x :
      P.domain.carrier) :
    ((e x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈MulAction.orbit (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H)
      ((e z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ↔ x∈MulAction.orbit H z := by
  constructor
  · rintro ⟨f,hf⟩
    change f.val.val ((e z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((e
      x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at hf
    obtain ⟨g,hg,hgq⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q
      H f.val).mp f.property
    rw [←hgq,he z,he x] at hf
    refine ⟨⟨g,hg⟩,Subtype.ext (q.val.injective ?_)⟩
    change q•(g•z.val)=q•x.val
    change (q*g*q⁻¹)•(q•z.val)=q•x.val at hf
    simpa only [mul_smul,inv_smul_smul] using hf
  · rintro ⟨g,hg⟩
    refine ⟨⟨q*g.val*q⁻¹,⟨g.val,g.property,rfl⟩⟩,?_⟩
    change (q*g.val*q⁻¹).val ((e z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((e
      x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [he z,he x]
    change q•(g.val•(q⁻¹•(q•z.val)))=q•x.val
    rw [inv_smul_smul]
    exact congrArg q.val (congrArg Subtype.val hg)

/-- No elementary original Fuchsian group has four distinct points of one
 actual nearest orbit on a true circle about a free original center. -/
theorem radius_elementary_no_four_nearest {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H)
    (w : P.domain.carrier) (hw : IsDirichletCenter P w) (z : P.domain.carrier)
    (r : ℝ) (p : Fin 4→P.domain.carrier) (hp : Function.Injective p)
    (hc : ∀i,P.hyperbolicDist w (p i)=r) (ho : ∀i,p i∈MulAction.orbit H z)
    (hnear : ∀u∈MulAction.orbit H z,r≤P.hyperbolicDist w u) : False := by
  by_cases hcyc : IsCyclic H
  · have hh:=cyclic_circle_three_free_center P hcyc w hw z (p 0) (p 1) (p 2) r
      (ho 0) (ho 1) (ho 2) (hc 0) (hc 1) (hc 2)
    rcases hh with hh|hh|hh
    · have he:=hp hh;norm_num at he
    · have he:=hp hh;norm_num at he
    · have he:=hp hh;norm_num at he
  · obtain ⟨q,d,hd,hK,hq⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.FuchsianDisc.elementary_halfPlane_dihedral_normal_form P.asFuchsianDisc hE hcyc
    obtain ⟨e,he,hed⟩:=radius_actual_halfPlane_coordinate P q hq
    have hr : 0≤r:=by rw [←hc 0];exact P.hyperbolicDist_nonneg _ _
    have hfre : ∀f∈canonicalDihedralGroup d (by linarith),
        f.val ((e w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((e w:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)→f=1:=by
      intro f hf hfix
      rw [←hK] at hf
      obtain ⟨g,hg,hgq⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff
        q H f).mp hf
      have hgfix : g.val w.val=w.val:=by
        apply q.val.injective
        rw [←hgq,he w] at hfix
        change (q*g*q⁻¹)•(q•w.val)=q•w.val at hfix
        change q•(g•w.val)=q•w.val
        simpa only [mul_smul,inv_smul_smul] using hfix
      have hg1 : g=1:=congrArg Subtype.val (hw ⟨g,hg⟩ (Subtype.ext hgfix))
      rw [←hgq,hg1,mul_one,mul_inv_cancel]
    apply canonicalDihedralGroup_no_four_nearest d hd (e w) (e z) r hr (e∘p)
      (e.injective.comp hp) (fun i=>(hed w (p i)).trans (hc i)) _ _ hfre
    · intro i
      rw [←hK]
      exact (radius_actual_coordinate_orbit_iff P q e he z (p i)).mpr (ho i)
    · intro u hu
      have huo : e.symm u∈MulAction.orbit H z:=by
        apply (radius_actual_coordinate_orbit_iff P q e he z (e.symm u)).mp
        rw [e.apply_symm_apply,hK]
        exact hu
      have hb:=hnear (e.symm u) huo
      rw [←hed w (e.symm u),e.apply_symm_apply] at hb
      exact hb

/-- Four distinct nearest same-circle points of one original Fuchsian
 orbit generate the true non-elementary branch needed for a radius gap. -/
theorem radius_four_nearest_points_cosh_gap {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (z : P.domain.carrier) (r : ℝ) (p : Fin 4→P.domain.carrier) (hp : Function.Injective p)
    (hc : ∀i,P.hyperbolicDist w (p i)=r) (ho : ∀i,p i∈MulAction.orbit H z)
    (hnear : ∀u∈MulAction.orbit H z,r≤P.hyperbolicDist w u) :
    Real.sqrt (1000001/1000000:ℝ)≤Real.cosh r := by
  have hOr : MulAction.orbit H (p 0)=MulAction.orbit H z:=MulAction.orbit_eq_iff.mpr (ho 0)
  have ho' (i : Fin 4) : p i∈MulAction.orbit H (p 0):=by rw [hOr];exact ho i
  obtain ⟨f,hf⟩:=ho' 1
  obtain ⟨g,hg⟩:=ho' 2
  obtain ⟨h,hh⟩:=ho' 3
  let K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup:=Subgroup.closure {f.val,g.val,h.val}
  have hKH : K≤H:=by
    apply (Subgroup.closure_le _).mpr
    intro k hk
    rcases hk with rfl|rfl|rfl
    · exact f.property
    · exact g.property
    · exact h.property
  have hfK : f.val∈K:=Subgroup.subset_closure (by simp)
  have hgK : g.val∈K:=Subgroup.subset_closure (by simp)
  have hhK : h.val∈K:=Subgroup.subset_closure (by simp)
  let Q:=radius_restrict P K hKH
  let dihedralRestrictedOriginalAction : MulAction K P.domain.carrier:=_root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomainAction Q.domain
  have hQfree : IsDirichletCenter Q w:=by
    intro k hk
    apply Subtype.ext
    exact congrArg (fun a : H=>a.val) (hw ⟨k.val,hKH k.property⟩ hk)
  have hQorb : ∀i : Fin 4,(p i : Q.domain.carrier)∈MulAction.orbit K (p 0 : Q.domain.carrier):=by
    intro i
    fin_cases i
    · exact ⟨1,one_smul _ _⟩
    · exact ⟨⟨f.val,hfK⟩,hf⟩
    · exact ⟨⟨g.val,hgK⟩,hg⟩
    · exact ⟨⟨h.val,hhK⟩,hh⟩
  have hQnear : ∀u : Q.domain.carrier,u∈MulAction.orbit K (p 0 : Q.domain.carrier) → r ≤ Q.hyperbolicDist w u:=by
    intro u hu
    obtain ⟨k,hk⟩:=hu
    apply hnear
    rw [←hOr]
    exact ⟨⟨k.val,hKH k.property⟩,hk⟩
  have hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary K:=by
    intro hE
    exact radius_elementary_no_four_nearest Q hE w hQfree (p 0) r p hp hc hQorb hQnear
  apply radius_nonElementary_triple_circle_cosh_gap P f g h hNE w (p 0) r (hc 0)
  · simpa only [hf] using hc 1
  · simpa only [hg] using hc 2
  · simpa only [hh] using hc 3

/--
An explicit universal constant greater than one
bounds the genuine radius of every original four-point Dirichlet cycle.
-/
theorem sqrt_one_plus_millionth_le_cosh_dirichlet_vertex_distance_of_cycle_four {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : P.domain.carrier) (hw : IsDirichletCenter P w)
    (x : P.domain.carrier) (hx : IsFuchsianPolygonVertex P (dirichletDomain P w) x)
    (hn : fuchsianPolygonCycleLength P (fuchsianPolygonCycle P (dirichletDomain P w) x)=4) :
    Real.sqrt (1000001/1000000:ℝ)≤Real.cosh (P.hyperbolicDist w x) := by
  obtain ⟨p,hp,hpr,hc,hnear⟩:=dirichlet_four_cycle_points P w hw x hx hn
  have ho (i : Fin 4) : p i∈MulAction.orbit H x:=by
    have ht : p i∈fuchsianPolygonCycle P (dirichletDomain P w) x:=by rw [←hpr];exact Set.mem_range_self i
    exact ht.2
  apply radius_four_nearest_points_cosh_gap P w hw x _ p hp hc ho
  intro u hu
  have hOr : MulAction.orbit H (p 0)=MulAction.orbit H x:=MulAction.orbit_eq_iff.mpr (ho 0)
  rw [←hOr] at hu
  obtain ⟨k,hk⟩:=hu
  have ht:=hnear 0 k
  change k•p 0=u at hk
  rw [hc 0,hk] at ht
  exact ht

theorem four_cycle_radius_constant_gt_one : 1<Real.sqrt (1000001/1000000:ℝ) := by
  have hs:=Real.sq_sqrt (show (0:ℝ)≤1000001/1000000 by norm_num)
  have hn:=Real.sqrt_nonneg (1000001/1000000:ℝ)
  nlinarith only [hs,hn]

end LowDimensionalTopology.Geometry.Fuchsian
