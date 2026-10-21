/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.EllipticFree.EllipticFreeDisplacementBounds
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenIdealHull
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.EllipticFree.EllipticFreeSharpness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane MatrixGroups OnePoint Complex.UnitDisc ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The exact maximum displacement constant follows from the product bound alone. -/
theorem ellipticFree_maximum_displacement_scalar (a b : ℝ) (ha : 0≤a) (hb : 0≤b)
    (hprod : 1≤Real.sinh (a/2)*Real.sinh (b/2)) :
    2*Real.arsinh 1≤max a b := by
  by_contra! hlt
  have hA : Real.sinh (a/2)<1 := by
    rw [←Real.sinh_arsinh 1]
    exact Real.sinh_lt_sinh.mpr (by linarith [le_max_left a b])
  have hB : Real.sinh (b/2)<1 := by
    rw [←Real.sinh_arsinh 1]
    exact Real.sinh_lt_sinh.mpr (by linarith [le_max_right a b])
  have hAn : 0≤Real.sinh (a/2):=Real.sinh_nonneg_iff.mpr (by linarith)
  have hBn : 0≤Real.sinh (b/2):=Real.sinh_nonneg_iff.mpr (by linarith)
  nlinarith

/-- The native original-pair maximum bound, with no supplied chart or type cases. -/
theorem hEllipticFree_maximum_displacement
    (G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hD :
      _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc G) (hE :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree G)
    (hLift : ∀g∈G,∃A : Matrix.SpecialLinearGroup (Fin 2)
      ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=g)
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      A∈G) (hBm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈G)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) (z : ℍ) :
    2*Real.arsinh 1≤max (dist z (A•z)) (dist z (B•z)) :=
  ellipticFree_maximum_displacement_scalar _ _ dist_nonneg dist_nonneg
    (hEllipticFree_displacement_bound G hD hE hLift A B hAm hBm hPair z)

/-- The origin formula's product lower bound is equivalent to the Euclidean sum-of-squares bound. -/
theorem ellipticFree_origin_norm_sum_scalar (r s u v : ℝ)
    (hr : r^2<1) (hs : s^2<1)
    (hur : u^2=r^2/(1-r^2)) (hvs : v^2=s^2/(1-s^2)) (hprod : 1≤u*v) :
    1≤r^2+s^2 := by
  have hrp : 0<1-r^2:=by linarith
  have hsp : 0<1-s^2:=by linarith
  have hur' : u^2*(1-r^2)=r^2 := (eq_div_iff hrp.ne').mp hur
  have hvs' : v^2*(1-s^2)=s^2 := (eq_div_iff hsp.ne').mp hvs
  have hp : 1≤u^2*v^2 := by nlinarith [sq_nonneg (u*v-1)]
  have hh:=mul_le_mul_of_nonneg_right hp (mul_pos hrp hsp).le
  have he : (u^2*v^2)*((1-r^2)*(1-s^2))=r^2*s^2 := by
    rw [show (u^2*v^2)*((1-r^2)*(1-s^2))=(u^2*(1-r^2))*(v^2*(1-s^2)) by ring,hur',hvs']
  rw [he] at hh
  nlinarith

/-- Every original whole-disc preserver has a real matrix chart with its entire native disc action identified. -/
theorem discPreserver_realSL_chart (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    ∃A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*f*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius ∧
      ∀z : 𝔻,f.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=(((_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action A z:𝔻):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  obtain ⟨A,hA⟩:=mobius_preserves_halfPlane_exists_SL (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*f*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
    (nielsen_discPreserver_conjugate_halfPlane f hf)
  refine ⟨A,hA,?_⟩
  intro z
  have hz : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z))=((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_halfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  have he:=congrArg (fun p:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val p) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z))
  rw [hA] at he
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ • (f • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius • _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z))))=_ at he
  rw [smul_inv_smul] at he
  change f.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)))=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint (A • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)) at he
  rw [hz,_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius_apply] at he
  change f.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley (((A • _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z:ℍ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at he
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_halfPlane] at he
  exact he

/-- The sharp product bound for the actual images of every point of the original unit disc. -/
theorem ellipticFree_disc_displacement_bound
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hInv : ∀f : H,f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f g : H)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (z u v : 𝔻) (hfu : f.val.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (hgv : g.val.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    1≤Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z u/2)*Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z v/2) := by
  obtain ⟨A,hAf,hActA⟩:=discPreserver_realSL_chart f.val (hInv f)
  obtain ⟨B,hBg,hActB⟩:=discPreserver_realSL_chart g.val (hInv g)
  let q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  have hKE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree K:=hE.conjugation q
  have hKD : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc K:=
    invariantDisc_conjugate H q ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc,hInv⟩
  have hLift : ∀k∈K,∃A : Matrix.SpecialLinearGroup (Fin 2) ℝ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=k := by
    intro k hk
    obtain ⟨a,ha,rfl⟩:=(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q
      H k).mp hk
    obtain ⟨C,hC⟩:=mobius_preserves_halfPlane_exists_SL (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*a*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
      (nielsen_discPreserver_conjugate_halfPlane a (hInv ⟨a,ha⟩))
    exact ⟨C,by simpa only [q,inv_inv] using hC⟩
  have hfm : q*f.val*q⁻¹∈K:=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨f.val,f.property,rfl⟩
  have hgm : q*g.val*q⁻¹∈K:=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨g.val,g.property,rfl⟩
  have hAf' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=q*f.val*q⁻¹:=by simpa only [q,inv_inv] using hAf
  have hBg' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B=q*g.val*q⁻¹:=by simpa only [q,inv_inv] using hBg
  have hAm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈K:=hAf' ▸ hfm
  have hBm : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B∈K:=hBg' ▸ hgm
  have hPairK:=hPair.conjugation q
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,←hAf',←hBg'] at hPairK
  have hb:=hEllipticFree_displacement_bound K hKD hKE hLift A B hAm hBm hPairK (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z)
  have hAU : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action A z=u := by
    apply Subtype.ext
    exact OnePoint.coe_injective ((hActA z).symm.trans hfu)
  have hBV : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action B z=v := by
    apply Subtype.ext
    exact OnePoint.coe_injective ((hActB z).symm.trans hgv)
  have hDA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z u=dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z) (A•_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z) := by
    rw [←hAU,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  have hDB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z v=dist (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z) (B•_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane z) := by
    rw [←hBV,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  rwa [←hDA,←hDB] at hb

/-- The exact maximum bound for the original unit-disc transformations. -/
theorem ellipticFree_disc_maximum_displacement
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hInv : ∀f : H,f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f g : H)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (z u v : 𝔻) (hfu : f.val.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (hgv : g.val.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    2*Real.arsinh 1≤max (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z u) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z v) := by
  apply ellipticFree_maximum_displacement_scalar
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane];exact dist_nonneg
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane];exact dist_nonneg
  · exact ellipticFree_disc_displacement_bound H hInv hE f g hPair z u v hfu hgv

/-- The displacement inequality and its elliptic-free extension for the actual original unit-disc images of zero. -/
theorem ellipticFree_disc_origin_norm_sum
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hInv : ∀f : H,f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f g : H)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (u v : 𝔻) (hfu : f.val.val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (hgv : g.val.val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    1≤‖(u:ℂ)‖^2+‖(v:ℂ)‖^2 := by
  have hb:=ellipticFree_disc_displacement_bound H hInv hE f g hPair 0 u v hfu hgv
  have hu:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_sinh_half_distance_sq (0:𝔻) u
  have hv:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_sinh_half_distance_sq (0:𝔻) v
  simp only [Complex.UnitDisc.coe_zero,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),sub_zero,one_mul,zero_sub,norm_neg] at hu hv
  exact ellipticFree_origin_norm_sum_scalar _ _ _ _ u.sq_norm_lt_one v.sq_norm_lt_one hu hv hb

/-- The exact Cayley transformation fixes the true H3 base point j. -/
theorem ellipticFree_cayley_fixes_j : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius • _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ=_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
  apply (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_fixJ_iff_norm
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius).mpr
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius,_root_.LowDimensionalTopology.Geometry.Mobius.mobiusNormalizedNorm_projection,_root_.LowDimensionalTopology.Geometry.Mobius.matrixNormalizedNorm,div_pow,
    Real.sq_sqrt (norm_nonneg _),_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm_sq]
  norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayleyMatrix,_root_.LowDimensionalTopology.Geometry.Mobius.coefficientMatrix,Matrix.det_fin_two,Complex.normSq_apply,
    Complex.norm_def]

/-- The real-plane model's point i is the same literal point as the H3 base point j. -/
theorem ellipticFree_embed_I_eq_j : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed UpperHalfPlane.I=_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := rfl

/-- At the disc origin, the native metric displacement is exactly the genuine H3 displacement at j. -/
theorem ellipticFree_disc_origin_sinh_eq_j (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (u : 𝔻)
    (hu : f.val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement f _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ=Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 u/2) := by
  obtain ⟨A,hA,hAct⟩:=discPreserver_realSL_chart f hf
  have hAU : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action A 0=u := by
    apply Subtype.ext
    exact OnePoint.coe_injective ((hAct 0).symm.trans hu)
  have hzero : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (0:𝔻)=UpperHalfPlane.I := by
    apply UpperHalfPlane.ext
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane,_root_.LowDimensionalTopology.Geometry.Hyperbolic.inverseCayleyFormula]
  have hpath : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist 0 u=dist UpperHalfPlane.I (A•UpperHalfPlane.I) := by
    rw [←hAU,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc,hzero]
  have hq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ • _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ=_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
    calc
      _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius • _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ):=
        congrArg (fun x:_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.UpperHalfSpace=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ • x) ellipticFree_cayley_fixes_j.symm
      _=_root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ:=inv_smul_smul _ _
  have hc:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement_conjugation f _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
  simp only [hq,inv_inv,←hA] at hc
  rw [←hc,←ellipticFree_embed_I_eq_j,_root_.LowDimensionalTopology.Geometry.Fuchsian.halfPlaneH3Embed_sinh_displacement
    A UpperHalfPlane.I]
  change Real.sinh (dist UpperHalfPlane.I (A•UpperHalfPlane.I)/2)=_
  rw [hpath]

/-- The original unit-disc pair obeys the sharp product bound at the true base point j. -/
theorem ellipticFree_unitDisc_displacement_at_j
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hInv : ∀f : H,f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (f g : H)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1≤_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement f.val _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ*_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement g.val _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
  obtain ⟨A,_hA,hActA⟩:=discPreserver_realSL_chart f.val (hInv f)
  obtain ⟨B,_hB,hActB⟩:=discPreserver_realSL_chart g.val (hInv g)
  have hb:=ellipticFree_disc_displacement_bound H hInv hE f g hPair 0
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action A
      0) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discSL2Action B 0) (hActA 0) (hActB 0)
  rw [←ellipticFree_disc_origin_sinh_eq_j f.val (hInv f) _ (hActA 0),
    ←ellipticFree_disc_origin_sinh_eq_j g.val (hInv g) _ (hActB 0)] at hb
  exact hb

/-- Every actual real-trace special-linear lift has its difference norm bounded below by sqrt(2) times the j-displacement. -/
theorem ellipticFree_matrix_difference_sq_lower (A :
  _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2)
    (hReal : (Matrix.trace (A:_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)).im=0) :
    2*_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A) _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ^2≤
      _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm ((A:_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)-1)^2 := by
  let r:=(Matrix.trace (A:_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)).re
  have htr : Matrix.trace (A:_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)=(r:ℂ):=Complex.ext rfl hReal
  have hn:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_trace_square_norm_le A
  rw [htr,←Complex.ofReal_pow] at hn
  rw [show ((r^2:ℝ):ℂ)-2=((r^2-2:ℝ):ℂ) by push_cast;rfl] at hn
  rw [Complex.norm_real,Real.norm_eq_abs] at hn
  have hN : r^2-2≤_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm (A:_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)^2 := le_trans (le_abs_self _) hn
  have hdisp:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenCenteredMatrix_norm_sq_displacement A
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensenCenteredMatrix_norm_sq] at hdisp
  have hQ : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm (A:_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)^2=
      4*_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A) _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ^2+2 := by
    linarith only [hdisp]
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_matrixNorm_sub_one_sq]
  change _≤_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm (A:_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)^2+2-2*r
  nlinarith [sq_nonneg (r-2)]

/-- The displacement inequality and its elliptic-free extension for arbitrary genuine determinant-one representatives. -/
theorem ellipticFree_unitDisc_matrix_difference_product
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hInv : ∀f : H,f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsEllipticFree H) (A B :
      _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2)
    (hAm : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A∈H) (hBm :
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B∈H)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A,
        _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    2≤_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm ((A:_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)-1)*_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm ((B:_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)-1) := by
  have hD : _root_.LowDimensionalTopology.Geometry.Mobius.HasInvariantComplexDisc H:=⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc,hInv⟩
  have ha:=ellipticFree_matrix_difference_sq_lower A (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFree_specialLinear_trace H hD hE A hAm).1
  have hb:=ellipticFree_matrix_difference_sq_lower B (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFree_specialLinear_trace H hD hE B hBm).1
  have hprod:=ellipticFree_unitDisc_displacement_at_j H hInv hE ⟨_,hAm⟩ ⟨_,hBm⟩ hPair
  have hp : 4≤(_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm ((A:_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)-1)*_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm ((B:_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)-1))^2 := by
    have hmul:=mul_le_mul ha hb (by positivity) (by positivity)
    nlinarith [sq_nonneg (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A)
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ*
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B) _root_.LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ-1)]
  have hn : 0≤_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm ((A:_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)-1)*_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm ((B:_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)-1):=
    mul_nonneg (_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm_nonneg
      _) (_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm_nonneg _)
  nlinarith

/-- The printed decimal comparison is checked by a finite rational exponential bound. -/
theorem ellipticFree_maximum_displacement_constant_gt_decimal : (44:ℝ)/25<2*Real.arsinh 1 := by
  have he:=Real.exp_bound' (x:=(22:ℝ)/25) (by norm_num) (by norm_num) (n:=8) (by norm_num)
  norm_num [Finset.sum_range_succ] at he
  have hr : (1411:ℝ)/1000<Real.sqrt 2 := by
    have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have hn:=Real.sqrt_nonneg (2:ℝ)
    nlinarith
  have hb : Real.exp ((22:ℝ)/25)<1+Real.sqrt 2 := by linarith
  have hl : (22:ℝ)/25<Real.log (1+Real.sqrt 2):=
    (Real.lt_log_iff_exp_lt (by positivity)).mpr hb
  change (44:ℝ)/25<2*Real.log (1+Real.sqrt (1+(1:ℝ)^2))
  norm_num only [one_pow,one_add_one_eq_two]
  linarith

/-- The exact maximum constant is attained in the genuine elliptic-free native-plane example. -/
theorem ellipticFree_maximum_displacement_sharpness : ∃u v : ℍ,
    ellipticFreeSharpnessFirst.val (Complex.I:ℂ)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧
    ellipticFreeSharpnessSecond.val (Complex.I:ℂ)=((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧
    max (dist UpperHalfPlane.I u) (dist UpperHalfPlane.I v)=2*Real.arsinh 1 := by
  obtain ⟨u,v,hfu,hgv,hu,hv⟩:=ellipticFreeSharpness_native
  refine ⟨u,v,hfu,hgv,?_⟩
  have hdu : dist UpperHalfPlane.I u=2*Real.arsinh 1 := by
    have h:=congrArg Real.arsinh hu
    rw [Real.arsinh_sinh] at h
    linarith
  have hdv : dist UpperHalfPlane.I v=2*Real.arsinh 1 := by
    have h:=congrArg Real.arsinh hv
    rw [Real.arsinh_sinh] at h
    linarith
  rw [hdu,hdv,max_self]

/-- The purely hyperbolic maximum conclusion follows for the original native unit-disc action. -/
theorem purelyHyperbolic_disc_maximum_displacement
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hInv : ∀f : H,f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsPurelyHyperbolic H) (f g : H)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (z u v : 𝔻) (hfu : f.val.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (hgv : g.val.val ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    2*Real.arsinh 1≤max (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z
      u) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist z v) :=
  ellipticFree_disc_maximum_displacement H hInv hH.ellipticFree f g hPair z u v hfu hgv

/-- For an actual purely hyperbolic group and its actual images of zero. -/
theorem purelyHyperbolic_disc_origin_norm_sum
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hInv : ∀f : H,f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsPurelyHyperbolic H) (f g : H)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (u v : 𝔻) (hfu : f.val.val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((u:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
    (hgv : g.val.val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    1≤‖(u:ℂ)‖^2+‖(v:ℂ)‖^2 :=
  ellipticFree_disc_origin_norm_sum H hInv hH.ellipticFree f g hPair u v hfu hgv

/-- For arbitrary genuine special-linear representatives of the purely hyperbolic pair. -/
theorem purelyHyperbolic_unitDisc_matrix_difference_product
    (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hInv : ∀f : H,f.val.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc=_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hH : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsPurelyHyperbolic H) (A B :
      _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.SpecialLinear2)
    (hAm : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A∈H) (hBm :
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B∈H)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({
        _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection A,
        _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection B}:Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    2≤_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm ((A:_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)-1)*_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.matrixNorm ((B:_root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2)-1) :=
  ellipticFree_unitDisc_matrix_difference_product H hInv hH.ellipticFree A B hAm hBm hPair

end LowDimensionalTopology.Geometry.Fuchsian
