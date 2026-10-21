/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.CanonicalSeparation
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.DisplacementInvariants
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletElementaryCircles
public import LowDimensionalTopology.Geometry.DiscreteGroups.Discreteness.DiscretenessCriteria
public import LowDimensionalTopology.Geometry.Mobius.Dynamics.MobiusIteration
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Products.ParabolicEllipticCommutators
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

/-- The displacement of a genuine conjugate is bounded by the original
translation path and twice the conjugator's actual displacement. -/
theorem hSL_conjugate_displacement_le (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    dist z ((B*A*B⁻¹)•z)≤dist z (A•z)+2*dist z (B•z) := by
  have hB : dist (B•z) ((B*A*B⁻¹)•z)=dist z ((A*B⁻¹)•z):=by
    rw [mul_assoc,mul_smul]
    exact (isometry_smul ℍ B).dist_eq _ _
  have hA : dist (A•z) ((A*B⁻¹)•z)=dist z (B⁻¹•z):=by
    rw [mul_smul]
    exact (isometry_smul ℍ A).dist_eq _ _
  have hInv : dist z (B⁻¹•z)=dist z (B•z):=by
    have hh:=(isometry_smul ℍ B).dist_eq z (B⁻¹•z)
    rw [smul_inv_smul,dist_comm] at hh
    exact hh.symm
  have ht:=dist_triangle z (B•z) ((B*A*B⁻¹)•z)
  rw [hB] at ht
  have ht':=dist_triangle z (A•z) ((A*B⁻¹)•z)
  rw [hA,hInv] at ht'
  linarith only [ht,ht']

/-- A rational displacement threshold stays small after the three path
segments in a genuine conjugation. -/
theorem sinh_three_arsinh_tenth :
    Real.sinh (3*Real.arsinh (1/10:ℝ))=38/125 := by
  let t:=Real.arsinh (1/10:ℝ)
  have hs : Real.sinh t=1/10:=Real.sinh_arsinh _
  have hc:=Real.cosh_sq_sub_sinh_sq t
  have h2:=Real.sinh_two_mul t
  have hc2:=Real.cosh_two_mul t
  rw [show 3*t=2*t+t by ring,Real.sinh_add,h2,hc2,hs]
  rw [hs] at hc
  nlinarith only [hc]

/--
A discrete non-elementary pair with a parabolic or hyperbolic first
member has a uniform positive actual displacement gap. This weaker auxiliary
gap does not replace the geometric sharp universal constant.
-/
theorem nonelliptic_pair_half_displacement_gap
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) (z : ℍ) :
    1/10≤max (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z) := by
  have hp : 1/8≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (B*A*B⁻¹)) z:=by
    have hbridge : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusSinhDisplacement
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          B*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
          B)⁻¹) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z)=
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (B*A*B⁻¹)) z:=by
      rw [←map_inv,←map_mul,←map_mul,halfPlaneH3Embed_sinh_displacement]
    rcases hA with hA|hA
    · have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.quarter_le_parabolic_conjugate_sinh_displacement_product _ _ hA hd hne (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z)
      rw [halfPlaneH3Embed_sinh_displacement,hbridge] at h
      linarith only [h]
    · have h:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.eighth_le_hyperbolic_conjugate_sinh_displacement_product _ _ hA hd hne (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneH3Embed z)
      rwa [halfPlaneH3Embed_sinh_displacement,hbridge] at h
  by_contra! hm
  have hltA:=(le_max_left (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z)).trans_lt hm
  have hltB:=(le_max_right (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) z)
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) z)).trans_lt hm
  have hdA : dist z (A•z)<2*Real.arsinh (1/10:ℝ):=by
    have hh:=Real.arsinh_strictMono hltA
    change Real.arsinh (Real.sinh (dist z (A•z)/2))<_ at hh
    rw [Real.arsinh_sinh] at hh
    linarith only [hh]
  have hdB : dist z (B•z)<2*Real.arsinh (1/10:ℝ):=by
    have hh:=Real.arsinh_strictMono hltB
    change Real.arsinh (Real.sinh (dist z (B•z)/2))<_ at hh
    rw [Real.arsinh_sinh] at hh
    linarith only [hh]
  have hdC : dist z ((B*A*B⁻¹)•z)/2<3*Real.arsinh (1/10:ℝ):=by
    linarith only [hSL_conjugate_displacement_le A B z,hdA,hdB]
  have hC : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (B*A*B⁻¹)) z<38/125:=by
    change Real.sinh (dist z ((B*A*B⁻¹)•z)/2)<_
    rw [←sinh_three_arsinh_tenth]
    exact Real.sinh_strictMono hdC
  have hprod:=mul_le_mul hltA.le hC.le (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement_nonneg _ _) (by norm_num : (0:ℝ)≤1/10)
  norm_num at hprod
  linarith only [hp,hprod]

theorem nonelliptic_pair_displacementM_gap
    (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
        _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    1/10≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementM_lower_bound _ _
    _).mpr (nonelliptic_pair_half_displacement_gap A B hA hd hne)



/-- A cyclic group containing nonidentity torsion is finite. -/
theorem cyclic_finite_of_nontrivial_torsion {G : Type*} [Group G] [IsCyclic G]
    (f : G) (hf : IsOfFinOrder f) (hf1 : f≠1) : Finite G := by
  by_contra hh
  let cyclicInfiniteGroup : Infinite G:=not_finite_iff_infinite.mp hh
  let e : Multiplicative ℤ≃*G:=intCyclicMulEquiv
  have hefin : IsOfFinOrder (e.symm f):=by
    obtain ⟨n,hn,he⟩:=hf.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,by rw [←map_pow,he,map_one]⟩
  have he1 : e.symm f=1:=(isOfFinOrder_iff_eq_one _).mp hefin
  exact hf1 (e.symm.injective (he1.trans (map_one e.symm).symm))

/-- In an elementary Fuchsian group, an elliptic element of order other
than two forces the whole original group to be finite. -/
theorem elementary_elliptic_noninvolution_finite {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (he : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hfH : f∈H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) (ho : orderOf f≠2) : Finite H := by
  rcases D.elementary_classification he with hcyc|⟨u,d,hdi,hdr,hmodel⟩
  · let cyclicOriginalGroup : IsCyclic H:=hcyc
    have hfin : IsOfFinOrder (⟨f,hfH⟩:H):=by
      obtain ⟨n,hn,heq⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.discrete_elliptic_finiteOrder H D.discrete f hfH hf |>.exists_pow_eq_one
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,Subtype.ext heq⟩
    exact cyclic_finite_of_nontrivial_torsion (⟨f,hfH⟩:H) hfin
      (fun heq=>hf.1 (congrArg Subtype.val heq))
  · obtain ⟨B,hB,hpres⟩:=_root_.LowDimensionalTopology.Geometry.Fuchsian.invariantDisc_conjugate H u ⟨D.carrier,D.isDisc,D.image_eq⟩
    have hp : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H≤_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusZeroInftyPairStabilizer:=by
      rw [hmodel]
      apply (Subgroup.closure_le _).mpr
      intro k hk
      rcases hk with rfl|rfl
      · exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mem_zeroInftyPairStabilizer d
      · exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusZeroInftyPairStabilizer.mul_mem
          (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_mem_zeroInftyPairStabilizer (-1))
          _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusReciprocal_mem_zeroInftyPairStabilizer
    let F:=u*f*u⁻¹
    have hFH : F∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H:=
      (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff u H
        _).mpr ⟨f,hfH,rfl⟩
    have hFE : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic F:=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation f u).mpr hf
    have hFsq : F*F≠1:=by
      intro hs
      have hF2 : orderOf F=2:=orderOf_eq_prime (by simpa only [pow_two] using hs) hFE.1
      have heq : orderOf F=orderOf f:=(MulAut.conj u).orderOf_eq f
      exact ho (heq.symm.trans hF2)
    have hFzero:=endpointPair_fix_zero_of_square_ne_one F (hp hFH) hFsq
    have hdNorm : ‖(d:ℂ)‖≠1:=by
      have hr:=Complex.re_le_norm (d:ℂ)
      linarith only [hr,hdr]
    have hd1 : (d:ℂ)≠1:=by intro hh;apply hdNorm;rw [hh,norm_one]
    have hdL : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusLoxodromic (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d):=by
      rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_eq_standard d hd1]
      exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusStandardElement_loxodromic_iff d).mpr hdNorm
    have hdH : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d∈_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate u H:=by
      rw [hmodel]
      exact Subgroup.subset_closure (by simp)
    have hdHyp : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling d):=⟨hdL,B,hB,hpres ⟨_,hdH⟩⟩
    have hzB : (((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))∈frontier B:=
      _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_fixed_mem_disc_frontier _ hdHyp hB (hpres
        ⟨_,hdH⟩) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero d)
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_fixed_not_mem_disc_frontier F hFE hB (hpres
      ⟨_,hFH⟩) hFzero hzB).elim

/-- A genuine parabolic or hyperbolic element and a noninvolutory elliptic
member in one Fuchsian group generate a non-elementary subgroup. -/
theorem nonelliptic_elliptic_noninvolution_pair_nonElementary
    {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (f g : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val)
    (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val) (hgo : orderOf g.val≠2) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  let K:=Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hKH : K≤H:=(Subgroup.closure_le H).mpr
    (by intro k hk;rcases hk with rfl|rfl;exact f.property;exact g.property)
  have hfK : f.val∈K:=Subgroup.subset_closure (by simp)
  have hgK : g.val∈K:=Subgroup.subset_closure (by simp)
  intro he
  let finiteGeneratedGroup : Finite K:=
    elementary_elliptic_noninvolution_finite (radius_restrict P K hKH).asFuchsianDisc he g.val hgK hg hgo
  have hfin:=isOfFinOrder_of_finite (⟨f.val,hfK⟩:K)
  have hfin' : IsOfFinOrder f.val:=by
    obtain ⟨n,hn,he⟩:=hfin.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,congrArg Subtype.val he⟩
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_parabolic_or_loxodromic_not_isOfFinOrder f.val (hf.imp_right And.left) hfin'

/-- Two actual involutions generate an elementary original Möbius group,
by their invariant finite boundary fixed set. -/
theorem pair_involutions_elementary (f g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hf : f*f=1) (hg : g*g=1) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary (Subgroup.closure ({f,g}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)) := by
  by_cases hf1 : f=1
  · rw [hf1]
    have hle : Subgroup.closure ({1,g}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)≤Subgroup.zpowers g:=
      (Subgroup.closure_le _).mpr (by
        intro k hk;rcases hk with rfl|rfl;exact Subgroup.one_mem _;exact Subgroup.mem_zpowers _)
    have hgfin : IsOfFinOrder g:=isOfFinOrder_iff_pow_eq_one.mpr
      ⟨2,by norm_num,by simpa only [pow_two] using hg⟩
    let finiteGeneratedPowers : Finite (Subgroup.zpowers g):=hgfin.finite_zpowers
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isElementary_of_finite _).mono hle
  · let c:=f*g
    by_cases hc : c=1
    · have hgf : g=f:=by
        calc
          g=f⁻¹*(f*g):=by group
          _=f⁻¹:=by rw [show f*g=1 from hc,mul_one]
          _=f:=inv_eq_of_mul_eq_one_left hf
      rw [hgf]
      exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusIteration_elementary_of_preserves f f hf1 (by
        ext z
        constructor
        · rintro ⟨x,hx,rfl⟩;change f.val (f.val x)=f.val x;rw [show f.val x=x from hx];exact hx
        · intro hz;exact ⟨z,hz,hz⟩)
    · have hfi : f⁻¹=f:=inv_eq_of_mul_eq_one_left hf
      have hgi : g⁻¹=g:=inv_eq_of_mul_eq_one_left hg
      have hconj : f*c*f⁻¹=c⁻¹:=by
        dsimp only [c]
        rw [mul_inv_rev,hfi,hgi]
        calc
          f*(f*g)*f=(f*f)*(g*f):=by group
          _=g*f:=by rw [hf,one_mul]
      have hpres : f.val '' _root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryFixedPoints c=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryFixedPoints c:=by
        apply _root_.LowDimensionalTopology.Geometry.Mobius.mobiusIteration_preserves_of_conjugate_fixes c f hc
        intro z hz
        rw [hconj]
        change c.val.symm z=z
        apply c.val.injective
        rw [Equiv.apply_symm_apply,show c.val z=z from hz]
      have hE:=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusIteration_elementary_of_preserves c f hc hpres
      apply hE.mono
      apply (Subgroup.closure_le _).mpr
      intro k hk
      rcases hk with rfl|rfl
      · exact Subgroup.subset_closure (by simp)
      · have hcK : c∈Subgroup.closure ({c,f}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=
          Subgroup.subset_closure (by simp)
        have hfK : f∈Subgroup.closure ({c,f}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup):=
          Subgroup.subset_closure (by simp)
        have heq : f⁻¹*c=k:=by dsimp only [c];group
        rw [←heq]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hfK) hcK


/-- The positive gap is transported to the original finite disc with its
actual group action and genuine hyperbolic path distances. -/
theorem radius_nonelliptic_pair_half_displacement_gap {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f g : H)
    (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val ∨
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (x : P.domain.carrier) :
    1/10≤max (Real.sinh (P.hyperbolicDist x (f•x)/2))
      (Real.sinh (P.hyperbolicDist x (g•x)/2)) := by
  let q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  have hfm : q*f.val*q⁻¹∈K:=⟨f.val,f.property,rfl⟩
  have hgm : q*g.val*q⁻¹∈K:=⟨g.val,g.property,rfl⟩
  obtain ⟨A,hAf⟩:=mobius_preserves_halfPlane_exists_SL _ (radius_conjugate_preserves_halfPlane P _ hfm)
  obtain ⟨B,hBg⟩:=mobius_preserves_halfPlane_exists_SL _ (radius_conjugate_preserves_halfPlane P _ hgm)
  have hle : Subgroup.closure ({f.val,g.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)≤H:=
    (Subgroup.closure_le H).mpr (by intro k hk;rcases hk with rfl|rfl;exact f.property;exact g.property)
  have hd:=discreteMobius_subgroup_of_le H _ P.asFuchsianDisc.discrete hle
  obtain ⟨hdQ,hPairQ⟩:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_displacement_conjugation_admissible f.val g.val q hd hPair
  rw [←hAf,←hBg] at hdQ hPairQ
  have hAQ : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∨ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [hAf]
    rcases hf with hf|hf
    · exact Or.inl ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusParabolic_isConj (isConj_iff.mpr ⟨q,rfl⟩)).mp
      hf)
    · exact Or.inr (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward _ q hf)
  have hb:=nonelliptic_pair_half_displacement_gap A B hAQ hdQ hPairQ (P.halfPlaneCoordinate x)
  change 1/10≤max (Real.sinh (dist (P.halfPlaneCoordinate x) (A•P.halfPlaneCoordinate x)/2))
    (Real.sinh (dist (P.halfPlaneCoordinate x) (B•P.halfPlaneCoordinate x)/2)) at hb
  rw [radius_coordinate_action_lift P f A hAf x,radius_coordinate_action_lift P g B hBg x] at hb
  exact hb

/-- The commutator of a genuine elliptic generator in a non-elementary
pair is hyperbolic, because the other generator moves its true center. -/
theorem radius_elliptic_commutator_hyperbolic {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f g : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f.val)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup))) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (f.val*g.val*f.val⁻¹*g.val⁻¹) := by
  let q:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  have hfm : q*f.val*q⁻¹∈K:=⟨f.val,f.property,rfl⟩
  have hgm : q*g.val*q⁻¹∈K:=⟨g.val,g.property,rfl⟩
  obtain ⟨A,hAf⟩:=mobius_preserves_halfPlane_exists_SL _ (radius_conjugate_preserves_halfPlane P _ hfm)
  obtain ⟨B,hBg⟩:=mobius_preserves_halfPlane_exists_SL _ (radius_conjugate_preserves_halfPlane P _ hgm)
  have hAQ : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A):=by
    rw [hAf]
    exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusElliptic_conjugation f.val q).mpr hf
  have hPairQ:=hPair.conjugation q
  rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_generated_conjugation,←hAf,←hBg] at hPairQ
  let v:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hEllipticCenter A ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff A hAQ.1).mp hAQ)
  have hv : A•v=v:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_elliptic_fixed_iff A _ v).mpr rfl
  have hBv : B•v≠v:=by
    intro hh
    apply hPairQ
    apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_elementary_of_common_fixed _ _ ((v:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (v:ℂ)=(v:ℂ)
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,hv]
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val (v:ℂ)=(v:ℂ)
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,hh]
  have hC:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hElliptic_commutator_translationLength A B hAQ hBv).1
  have hCq : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (A*B*A⁻¹*B⁻¹)=q*(f.val*g.val*f.val⁻¹*g.val⁻¹)*q⁻¹:=by
    simp only [map_mul,map_inv,hAf,hBg]
    group
  rw [hCq] at hC
  exact (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation _ q).mp hC

/-- The genuine metric action bounds displacement of a product by the two
original displacements at the same point. -/
theorem radius_product_displacement_le {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f g : H) (z : P.domain.carrier) :
    P.hyperbolicDist z ((f*g)•z)≤P.hyperbolicDist z (f•z)+P.hyperbolicDist z (g•z) := by
  have ht:=P.hyperbolicDist_triangle z (f•z) ((f*g)•z)
  rw [mul_smul,P.hyperbolicDist_smul] at ht
  exact ht

theorem radius_inverse_displacement {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f : H) (z : P.domain.carrier) :
    P.hyperbolicDist z (f⁻¹•z)=P.hyperbolicDist z (f•z) := by
  have h:=P.hyperbolicDist_smul f z (f⁻¹•z)
  rw [smul_inv_smul,P.hyperbolicDist_comm] at h
  exact h.symm

/-- The literal four factors of the original commutator give this metric
bound without any matrix or displacement hypothesis. -/
theorem radius_commutator_displacement_le {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f g : H) (z : P.domain.carrier) :
    P.hyperbolicDist z ((f*g*f⁻¹*g⁻¹)•z)≤
      2*P.hyperbolicDist z (f•z)+2*P.hyperbolicDist z (g•z) := by
  have h1:=radius_product_displacement_le P (f*g*f⁻¹) g⁻¹ z
  have h2:=radius_product_displacement_le P (f*g) f⁻¹ z
  have h3:=radius_product_displacement_le P f g z
  rw [radius_inverse_displacement] at h1 h2
  linarith only [h1,h2,h3]

/-- The four-factor small-displacement threshold is a genuine numerical
hyperbolic-sine estimate. -/
theorem sinh_four_arsinh_hundredth_lt_tenth :
    Real.sinh (4*Real.arsinh (1/100:ℝ))<1/10 := by
  let t:=Real.arsinh (1/100:ℝ)
  have hs : Real.sinh t=1/100:=Real.sinh_arsinh _
  have hc:=Real.cosh_sq_sub_sinh_sq t
  rw [hs] at hc
  have hcsq : Real.cosh t^2=10001/10000:=by linarith only [hc]
  have hclt : Real.cosh t<2:=by nlinarith only [hcsq]
  rw [show 4*t=2*(2*t) by ring,Real.sinh_two_mul,Real.sinh_two_mul,
    Real.cosh_two_mul,hs,hcsq]
  linarith only [hclt]

/-- A noninvolutory elliptic member also has a positive original pair gap:
the actual commutator is hyperbolic and forms a non-elementary pair with it. -/
theorem radius_elliptic_noninvolution_half_displacement_gap {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f g : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f.val)
    (hfo : orderOf f.val≠2)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (z : P.domain.carrier) :
    1/100≤max (Real.sinh (P.hyperbolicDist z (f•z)/2))
      (Real.sinh (P.hyperbolicDist z (g•z)/2)) := by
  let c : H:=f*g*f⁻¹*g⁻¹
  have hc : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic c.val:=radius_elliptic_commutator_hyperbolic P f g hf hPair
  have hcf:=nonelliptic_elliptic_noninvolution_pair_nonElementary P c f (Or.inr hc) hf hfo
  have hgap:=radius_nonelliptic_pair_half_displacement_gap P c f (Or.inr hc) hcf z
  by_contra! hm
  have hfsmall:=(le_max_left (Real.sinh (P.hyperbolicDist z (f•z)/2))
    (Real.sinh (P.hyperbolicDist z (g•z)/2))).trans_lt hm
  have hgsmall:=(le_max_right (Real.sinh (P.hyperbolicDist z (f•z)/2))
    (Real.sinh (P.hyperbolicDist z (g•z)/2))).trans_lt hm
  have hdF : P.hyperbolicDist z (f•z)<2*Real.arsinh (1/100:ℝ):=by
    have h:=Real.arsinh_strictMono hfsmall
    rw [Real.arsinh_sinh] at h
    linarith only [h]
  have hdG : P.hyperbolicDist z (g•z)<2*Real.arsinh (1/100:ℝ):=by
    have h:=Real.arsinh_strictMono hgsmall
    rw [Real.arsinh_sinh] at h
    linarith only [h]
  have hdC : P.hyperbolicDist z (c•z)/2<4*Real.arsinh (1/100:ℝ):=by
    have h:=radius_commutator_displacement_le P f g z
    change P.hyperbolicDist z (c•z)≤_ at h
    linarith only [h,hdF,hdG]
  have hCsmall : Real.sinh (P.hyperbolicDist z (c•z)/2)<1/10:=
    (Real.sinh_strictMono hdC).trans sinh_four_arsinh_hundredth_lt_tenth
  have hsmall : max (Real.sinh (P.hyperbolicDist z (c•z)/2))
      (Real.sinh (P.hyperbolicDist z (f•z)/2))<1/10:=
    max_lt hCsmall (by linarith only [hfsmall])
  exact (not_lt_of_ge hgap) hsmall

/-- Every non-elementary original pair with a chosen noninvolutory first
member has a uniform positive displacement gap, with no elliptic-free premise. -/
theorem radius_pair_half_displacement_gap_of_order_ne_two {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f g : H) (hfo : orderOf f.val≠2)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (z : P.domain.carrier) :
    1/100≤max (Real.sinh (P.hyperbolicDist z (f•z)/2))
      (Real.sinh (P.hyperbolicDist z (g•z)/2)) := by
  have hf1:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.jorgensen_left_ne_one f.val g.val hPair
  rcases _root_.LowDimensionalTopology.Geometry.Mobius.mobius_nonidentity_type_trichotomy f.val hf1 with hp|hl|he
  · have h:=radius_nonelliptic_pair_half_displacement_gap P f g (Or.inl hp) hPair z
    linarith only [h]
  · have hh : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val:=⟨hl,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc,P.image_eq f⟩
    have h:=radius_nonelliptic_pair_half_displacement_gap P f g (Or.inr hh) hPair z
    linarith only [h]
  · exact radius_elliptic_noninvolution_half_displacement_gap P f g he hfo hPair z

/-- A universal positive gap holds for the genuine original Fuchsian
pair at every actual point, including all elliptic possibilities.
The constant is deliberately weaker than the separate sharp source constant. -/
theorem radius_pair_half_displacement_gap {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f g : H)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (z : P.domain.carrier) :
    1/100≤max (Real.sinh (P.hyperbolicDist z (f•z)/2))
      (Real.sinh (P.hyperbolicDist z (g•z)/2)) := by
  by_cases hfo : orderOf f.val=2
  · have hgo : orderOf g.val≠2:=by
      intro hgo
      apply hPair
      apply pair_involutions_elementary
      · have h:=pow_orderOf_eq_one f.val
        rwa [hfo,pow_two] at h
      · have h:=pow_orderOf_eq_one g.val
        rwa [hgo,pow_two] at h
    have hSwap : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({g.val,f.val}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)):=by
      rwa [Set.pair_comm]
    have h:=radius_pair_half_displacement_gap_of_order_ne_two P g f hgo hSwap z
    rwa [max_comm] at h
  · exact radius_pair_half_displacement_gap_of_order_ne_two P f g hfo hPair z

/-- A genuine circle containing the three original orbit points of a
non-elementary generating pair has a universal positive radius gap. -/
theorem radius_nonElementary_circle_gap {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f g : H)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (w z : P.domain.carrier) (r : ℝ)
    (hz : P.hyperbolicDist w z=r) (hf : P.hyperbolicDist w (f•z)=r)
    (hg : P.hyperbolicDist w (g•z)=r) : 1/100≤Real.sinh r := by
  have h:=radius_pair_half_displacement_gap P f g hPair z
  have hdf:=P.hyperbolicDist_triangle z w (f•z)
  have hdg:=P.hyperbolicDist_triangle z w (g•z)
  rw [P.hyperbolicDist_comm z w,hz,hf] at hdf
  rw [P.hyperbolicDist_comm z w,hz,hg] at hdg
  have hsf : Real.sinh (P.hyperbolicDist z (f•z)/2)≤Real.sinh r:=
    Real.sinh_le_sinh.mpr (by linarith only [hdf])
  have hsg : Real.sinh (P.hyperbolicDist z (g•z)/2)≤Real.sinh r:=
    Real.sinh_le_sinh.mpr (by linarith only [hdg])
  exact h.trans (max_le hsf hsg)

/-- The same actual circle has a universal cosh gap strictly larger than
one; only the non-elementary-pair branch of the four-cycle argument is used. -/
theorem radius_nonElementary_circle_cosh_gap {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f g : H)
    (hPair : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure ({f.val,g.val}:Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)))
    (w z : P.domain.carrier) (r : ℝ)
    (hz : P.hyperbolicDist w z=r) (hf : P.hyperbolicDist w (f•z)=r)
    (hg : P.hyperbolicDist w (g•z)=r) : Real.sqrt (10001/10000:ℝ)≤Real.cosh r := by
  have hs:=radius_nonElementary_circle_gap P f g hPair w z r hz hf hg
  apply Real.sqrt_le_iff.mpr
  refine ⟨(Real.cosh_pos r).le,?_⟩
  nlinarith [Real.cosh_sq_sub_sinh_sq r]

end LowDimensionalTopology.Geometry.Fuchsian
