/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.DiscreteGroups.Action.OrbitQuotient
public import LowDimensionalTopology.Geometry.Surfaces.Euclidean.EuclideanQuotientSurfaces
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The literal nonzero complex points, with their usual topology. -/
abbrev ExponentialAnnulusPoint:=ℂˣ

def exponentialAnnulusGenerator : ℂˣ:=Units.mk0 2 (by norm_num)
def exponentialAnnulusGroup : Subgroup ℂˣ:=Subgroup.zpowers exponentialAnnulusGenerator
abbrev ExponentialAnnulusAmbientQuotient:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitQuotient exponentialAnnulusGroup ExponentialAnnulusPoint

def exponentialAnnulusPower (n:ℤ) : exponentialAnnulusGroup:=
  ⟨exponentialAnnulusGenerator^n,Subgroup.mem_zpowers_iff.mpr ⟨n,rfl⟩⟩

theorem exponentialAnnulusPower_coe (n:ℤ) (z:ExponentialAnnulusPoint) :
    ((exponentialAnnulusPower n•z:ExponentialAnnulusPoint):ℂ)=(↑((2:ℝ)^n):ℂ)*(z:ℂ) := by
  change (((exponentialAnnulusGenerator^n)*z:ℂˣ):ℂ)=_
  simp [exponentialAnnulusGenerator]

theorem exponentialAnnulusGroup_power_exhaustive (g:exponentialAnnulusGroup) :
    ∃n:ℤ,g=exponentialAnnulusPower n := by
  obtain ⟨n,hn⟩:=Subgroup.mem_zpowers_iff.mp g.property
  exact ⟨n,Subtype.ext hn.symm⟩

/-- The closed diagram region: the exponential tail and the remaining annular sector. -/
def exponentialAnnulusClosedRegion : Set ExponentialAnnulusPoint:=
  {z | (0≤(z:ℂ).re ∧ Real.exp (-(z:ℂ).re)≤(z:ℂ).im ∧
      (z:ℂ).im≤2*Real.exp (-(z:ℂ).re/2)) ∨
    (((z:ℂ).re≤0 ∨ (z:ℂ).im≤0) ∧ 1≤‖(z:ℂ)‖ ∧ ‖(z:ℂ)‖≤2)}

def exponentialAnnulusDomain : Set ExponentialAnnulusPoint:=interior exponentialAnnulusClosedRegion

/-- The graph `y = exp(-x)` for `x ≥ 0`, joined to the unit-circle part
where `x ≤ 0` or `y ≤ 0`. -/
def exponentialAnnulusCurve : Set ExponentialAnnulusPoint:=
  {z | (0≤(z:ℂ).re ∧ (z:ℂ).im=Real.exp (-(z:ℂ).re)) ∨
    (((z:ℂ).re≤0 ∨ (z:ℂ).im≤0) ∧ ‖(z:ℂ)‖=1)}

abbrev ExponentialAnnulusClosedQuotient:=
  _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.restrictedOrbitQuotient exponentialAnnulusGroup ExponentialAnnulusPoint (closure exponentialAnnulusDomain)

theorem exponentialAnnulusClosedRegion_isClosed : IsClosed exponentialAnnulusClosedRegion := by
  have hr:Continuous (fun z:ℂˣ=>(z:ℂ).re):=Complex.continuous_re.comp Units.continuous_val
  have hi:Continuous (fun z:ℂˣ=>(z:ℂ).im):=Complex.continuous_im.comp Units.continuous_val
  have hn:Continuous (fun z:ℂˣ=>‖(z:ℂ)‖):=Units.continuous_val.norm
  exact ((isClosed_le continuous_const hr).inter
      ((isClosed_le (Real.continuous_exp.comp hr.neg) hi).inter
        (isClosed_le hi (continuous_const.mul (Real.continuous_exp.comp (hr.neg.div_const 2)))))).union
    (((isClosed_le hr continuous_const).union (isClosed_le hi continuous_const)).inter
      ((isClosed_le continuous_const hn).inter (isClosed_le hn continuous_const)))

theorem exponentialAnnulusDomain_isOpen : IsOpen exponentialAnnulusDomain:=isOpen_interior

theorem exponentialAnnulusDomain_closure_subset : closure exponentialAnnulusDomain⊆exponentialAnnulusClosedRegion:=
  closure_minimal interior_subset exponentialAnnulusClosedRegion_isClosed

def exponentialAnnulusSlope (z:ExponentialAnnulusPoint) : ℝ:=
  if 0<(z:ℂ).im then max (z:ℂ).re 0/(z:ℂ).im else 0

theorem exponentialAnnulusSlope_power (n:ℤ) (z:ExponentialAnnulusPoint) :
    exponentialAnnulusSlope (exponentialAnnulusPower n•z)=exponentialAnnulusSlope z := by
  have hpos:0<(2:ℝ)^n:=zpow_pos (by norm_num) _
  have hr:(((exponentialAnnulusPower n•z:ExponentialAnnulusPoint):ℂ)).re=(2:ℝ)^n*(z:ℂ).re:=by
    rw [exponentialAnnulusPower_coe]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  have hi:(((exponentialAnnulusPower n•z:ExponentialAnnulusPoint):ℂ)).im=(2:ℝ)^n*(z:ℂ).im:=by
    rw [exponentialAnnulusPower_coe]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  simp only [exponentialAnnulusSlope,hr,hi,mul_pos_iff_of_pos_left hpos]
  split_ifs
  · by_cases hx:0≤(z:ℂ).re
    · rw [max_eq_left hx,max_eq_left (mul_nonneg hpos.le hx)]
      exact mul_div_mul_left _ _ hpos.ne'
    · have hx':(z:ℂ).re≤0:=le_of_not_ge hx
      rw [max_eq_right hx',max_eq_right (mul_nonpos_of_nonneg_of_nonpos hpos.le hx')]
      simp
  · rfl

theorem exponentialAnnulusSlope_orbit (g:exponentialAnnulusGroup) (z:ExponentialAnnulusPoint) :
    exponentialAnnulusSlope (g•z)=exponentialAnnulusSlope z := by
  obtain ⟨n,rfl⟩:=exponentialAnnulusGroup_power_exhaustive g
  exact exponentialAnnulusSlope_power n z

theorem exponentialAnnulusSlope_continuous_closedRegion :
    Continuous (fun z:exponentialAnnulusClosedRegion=>exponentialAnnulusSlope z.val) := by
  have hr:Continuous (fun z:exponentialAnnulusClosedRegion=>(z.val:ℂ).re):=
    Complex.continuous_re.comp (Units.continuous_val.comp continuous_subtype_val)
  have hi:Continuous (fun z:exponentialAnnulusClosedRegion=>(z.val:ℂ).im):=
    Complex.continuous_im.comp (Units.continuous_val.comp continuous_subtype_val)
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hy:0<(z.val:ℂ).im
  · have hE:∀ᶠq:exponentialAnnulusClosedRegion in 𝓝 z,
        exponentialAnnulusSlope q.val=max (q.val:ℂ).re 0/(q.val:ℂ).im:=by
      filter_upwards [hi.continuousAt.eventually (lt_mem_nhds hy)] with q hq
      exact ite_eq_left hq
    have hG:ContinuousAt (fun q:exponentialAnnulusClosedRegion=>max (q.val:ℂ).re 0/(q.val:ℂ).im) z:=
      (hr.max continuous_const).continuousAt.div hi.continuousAt hy.ne'
    exact hG.congr_of_eventuallyEq hE
  · by_cases hyneg:(z.val:ℂ).im<0
    · have hE:∀ᶠq:exponentialAnnulusClosedRegion in 𝓝 z,exponentialAnnulusSlope q.val=0:=by
        filter_upwards [hi.continuousAt.eventually (gt_mem_nhds hyneg)] with q hq
        exact ite_eq_right (not_lt_of_ge hq.le)
      exact (continuousAt_const : ContinuousAt (fun _:exponentialAnnulusClosedRegion=>(0:ℝ)) z).congr_of_eventuallyEq hE
    · have hyzero:(z.val:ℂ).im=0:=le_antisymm (le_of_not_gt hy) (le_of_not_gt hyneg)
      by_cases hx:(z.val:ℂ).re<0
      · have hE:∀ᶠq:exponentialAnnulusClosedRegion in 𝓝 z,exponentialAnnulusSlope q.val=0:=by
          filter_upwards [hr.continuousAt.eventually (gt_mem_nhds hx)] with q hq
          simp only [exponentialAnnulusSlope,max_eq_right hq.le,zero_div,ite_self]
        exact (continuousAt_const : ContinuousAt (fun _:exponentialAnnulusClosedRegion=>(0:ℝ))
          z).congr_of_eventuallyEq hE
      · have hxpos:0<(z.val:ℂ).re:=by
          have hz:(z.val:ℂ)≠0:=Units.ne_zero z.val
          have hxnon:0≤(z.val:ℂ).re:=le_of_not_gt hx
          exact lt_of_le_of_ne hxnon (by
            intro he
            exact hz (Complex.ext he.symm hyzero))
        have hgap:(z.val:ℂ).im<Real.exp (-(z.val:ℂ).re):=by
          rw [hyzero]
          exact Real.exp_pos _
        have hE:∀ᶠq:exponentialAnnulusClosedRegion in 𝓝 z,exponentialAnnulusSlope q.val=0:=by
          filter_upwards [hr.continuousAt.eventually (lt_mem_nhds hxpos),
            (hi.sub (Real.continuous_exp.comp hr.neg)).continuousAt.eventually
              (gt_mem_nhds (sub_neg.mpr hgap))] with q hqx hqy
          have hqy':(q.val:ℂ).im<Real.exp (-(q.val:ℂ).re):=sub_neg.mp hqy
          have him:(q.val:ℂ).im≤0:=by
            rcases q.property with ht|ha
            · exact False.elim (not_le_of_gt hqy' ht.2.1)
            · exact ha.1.resolve_left (not_le_of_gt hqx)
          exact ite_eq_right (not_lt_of_ge him)
        exact (continuousAt_const : ContinuousAt (fun _:exponentialAnnulusClosedRegion=>(0:ℝ))
          z).congr_of_eventuallyEq hE

theorem exponentialAnnulus_tail_gap {x:ℝ} (hx:0≤x) :
    Real.exp (-x)<2*Real.exp (-x/2) := by
  have h:=Real.exp_le_exp.mpr (show -x≤-x/2 by linarith)
  linarith [Real.exp_pos (-x/2)]

theorem exponentialAnnulus_tail_mem_domain (z:ExponentialAnnulusPoint)
    (hx:0<(z:ℂ).re) (hl:Real.exp (-(z:ℂ).re)<(z:ℂ).im)
    (hu:(z:ℂ).im<2*Real.exp (-(z:ℂ).re/2)) : z∈exponentialAnnulusDomain := by
  let T:Set ExponentialAnnulusPoint:={z | 0<(z:ℂ).re ∧ Real.exp (-(z:ℂ).re)<(z:ℂ).im ∧
    (z:ℂ).im<2*Real.exp (-(z:ℂ).re/2)}
  have hr:Continuous (fun z:ℂˣ=>(z:ℂ).re):=Complex.continuous_re.comp Units.continuous_val
  have hi:Continuous (fun z:ℂˣ=>(z:ℂ).im):=Complex.continuous_im.comp Units.continuous_val
  have ho:IsOpen T:=(isOpen_lt continuous_const hr).inter
    ((isOpen_lt (Real.continuous_exp.comp hr.neg) hi).inter
      (isOpen_lt hi (continuous_const.mul (Real.continuous_exp.comp (hr.neg.div_const 2)))))
  have hs:T⊆exponentialAnnulusClosedRegion:=fun _ h=>Or.inl ⟨h.1.le,h.2.1.le,h.2.2.le⟩
  exact (interior_maximal hs ho) ⟨hx,hl,hu⟩

def exponentialAnnulusTailVertical (x:ℝ) (hx:0<x) (t:ℝ) : ExponentialAnnulusPoint:=
  Units.mk0 ((x:ℂ)+((Real.exp (-x)+t:ℝ):ℂ)*Complex.I) (by
    intro he
    have h:=congrArg Complex.re he
    have h':x=0:=by
      simpa only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,Complex.zero_re] using h
    exact hx.ne' h')

theorem exponentialAnnulusTailVertical_re (x:ℝ) (hx:0<x) (t:ℝ) :
    ((exponentialAnnulusTailVertical x hx t:ExponentialAnnulusPoint):ℂ).re=x := by
  simp only [exponentialAnnulusTailVertical,Units.val_mk0,Complex.add_re,Complex.ofReal_re,
    Complex.ofReal_im,Complex.mul_re,Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]

theorem exponentialAnnulusTailVertical_im (x:ℝ) (hx:0<x) (t:ℝ) :
    ((exponentialAnnulusTailVertical x hx t:ExponentialAnnulusPoint):ℂ).im=Real.exp (-x)+t := by
  simp only [exponentialAnnulusTailVertical,Units.val_mk0,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,add_zero]

theorem exponentialAnnulusTailVertical_continuous (x:ℝ) (hx:0<x) :
    Continuous (exponentialAnnulusTailVertical x hx) := by
  apply Units.isEmbedding_val₀.continuous_iff.mpr
  change Continuous (fun t:ℝ=>(x:ℂ)+((Real.exp (-x)+t:ℝ):ℂ)*Complex.I)
  fun_prop

theorem exponentialAnnulusTailVertical_zero_mem_closure (x:ℝ) (hx:0<x) :
    exponentialAnnulusTailVertical x hx 0∈closure exponentialAnnulusDomain := by
  have hg:0<2*Real.exp (-x/2)-Real.exp (-x):=sub_pos.mpr (exponentialAnnulus_tail_gap hx.le)
  have hlim:Tendsto (exponentialAnnulusTailVertical x hx) (𝓝[>] (0:ℝ))
      (𝓝 (exponentialAnnulusTailVertical x hx 0)):=
    (exponentialAnnulusTailVertical_continuous x hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply isClosed_closure.mem_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (gt_mem_nhds hg)] with t ht0 ht1
  change 0<t at ht0
  apply subset_closure
  apply exponentialAnnulus_tail_mem_domain
  · simpa only [exponentialAnnulusTailVertical_re] using hx
  · rw [exponentialAnnulusTailVertical_re,exponentialAnnulusTailVertical_im]
    linarith
  · rw [exponentialAnnulusTailVertical_re,exponentialAnnulusTailVertical_im]
    linarith

theorem exponentialAnnulusSlope_tail_lower (x:ℝ) (hx:0<x) :
    x≤exponentialAnnulusSlope (exponentialAnnulusTailVertical x hx 0) := by
  have he:0<Real.exp (-x):=Real.exp_pos _
  have he1:Real.exp (-x)≤1:=Real.exp_le_one_iff.mpr (by linarith)
  simp only [exponentialAnnulusSlope,exponentialAnnulusTailVertical,Units.val_mk0,Complex.add_re,Complex.add_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,mul_zero,mul_one,sub_zero,add_zero,zero_add,
    ite_eq_left he,max_eq_left hx.le]
  exact (le_div_iff₀ he).mpr ((mul_le_mul_of_nonneg_left he1 hx.le).trans_eq (mul_one x))

def exponentialAnnulusRestrictedSlope : ExponentialAnnulusClosedQuotient→ℝ:=
  Quotient.lift (fun z:closure exponentialAnnulusDomain=>exponentialAnnulusSlope z.val) (by
    intro z w h
    obtain ⟨g,hg⟩:=h
    change g•w.val=z.val at hg
    rw [←hg]
    exact exponentialAnnulusSlope_orbit g w.val)

theorem exponentialAnnulusRestrictedSlope_continuous : Continuous exponentialAnnulusRestrictedSlope := by
  apply continuous_quot_lift
  exact exponentialAnnulusSlope_continuous_closedRegion.comp
    (continuous_subtype_val.subtype_mk (fun z:closure exponentialAnnulusDomain=>
      exponentialAnnulusDomain_closure_subset z.property))

/-- The literal restricted closed-region orbit quotient is not compact. -/
theorem exponentialAnnulusClosedQuotient_not_compact : ¬CompactSpace ExponentialAnnulusClosedQuotient := by
  intro hcompact
  let :=hcompact
  have hc:IsCompact (range
    exponentialAnnulusRestrictedSlope):=isCompact_range exponentialAnnulusRestrictedSlope_continuous
  obtain ⟨B,hB⟩:=hc.bddAbove
  let x:ℝ:=max B 0+1
  have hx:0<x:=by dsimp only [x];linarith [le_max_right B 0]
  have hBx:B<x:=by dsimp only [x];linarith [le_max_left B 0]
  let z:closure exponentialAnnulusDomain:=
    ⟨exponentialAnnulusTailVertical x hx 0,exponentialAnnulusTailVertical_zero_mem_closure x hx⟩
  let q:ExponentialAnnulusClosedQuotient:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.restrictedProjection exponentialAnnulusGroup ExponentialAnnulusPoint
    (closure exponentialAnnulusDomain) z
  have hu:exponentialAnnulusRestrictedSlope q≤B:=hB (mem_range_self q)
  have hl:x≤exponentialAnnulusRestrictedSlope q:=exponentialAnnulusSlope_tail_lower x hx
  linarith

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open scoped Pointwise

theorem exponentialAnnulus_annular_mem_domain (z:ExponentialAnnulusPoint)
    (hs:(z:ℂ).re<0 ∨ (z:ℂ).im<0) (hl:1<‖(z:ℂ)‖) (hu:‖(z:ℂ)‖<2) :
    z∈exponentialAnnulusDomain := by
  let A:Set ExponentialAnnulusPoint:={z | ((z:ℂ).re<0 ∨ (z:ℂ).im<0) ∧ 1<‖(z:ℂ)‖ ∧ ‖(z:ℂ)‖<2}
  have hr:Continuous (fun z:ℂˣ=>(z:ℂ).re):=Complex.continuous_re.comp Units.continuous_val
  have hi:Continuous (fun z:ℂˣ=>(z:ℂ).im):=Complex.continuous_im.comp Units.continuous_val
  have hn:Continuous (fun z:ℂˣ=>‖(z:ℂ)‖):=Units.continuous_val.norm
  have ho:IsOpen A:=((isOpen_lt hr continuous_const).union (isOpen_lt hi continuous_const)).inter
    ((isOpen_lt continuous_const hn).inter (isOpen_lt hn continuous_const))
  have hA:A⊆exponentialAnnulusClosedRegion:=by
    intro p hp
    exact Or.inr ⟨hp.1.imp LT.lt.le LT.lt.le,hp.2.1.le,hp.2.2.le⟩
  exact (interior_maximal hA ho) ⟨hs,hl,hu⟩

theorem exponentialAnnulus_tail_weak_mem_closure (z:ExponentialAnnulusPoint)
    (hx:0≤(z:ℂ).re) (hl:Real.exp (-(z:ℂ).re)≤(z:ℂ).im)
    (hu:(z:ℂ).im≤2*Real.exp (-(z:ℂ).re/2)) : z∈closure exponentialAnnulusDomain := by
  let F:ℝ×ℝ→ℂ:=fun p=>(↑p.1:ℂ)+
    (↑((1-p.2)*Real.exp (-p.1)+p.2*(2*Real.exp (-p.1/2))):ℂ)*Complex.I
  have hFr (p:ℝ×ℝ):(F p).re=p.1:=by
    simp only [F,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero]
  have hFi (p:ℝ×ℝ):(F p).im=(1-p.2)*Real.exp (-p.1)+p.2*(2*Real.exp (-p.1/2)):=by
    simp only [F,Complex.add_im,Complex.ofReal_re,Complex.mul_im,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_add,add_zero]
  have hF:Continuous F:=by fun_prop
  let S:Set (ℝ×ℝ):=Ioi (0:ℝ)×ˢIoo (0:ℝ) 1
  have hsub:F '' S⊆(Units.val:ℂˣ→ℂ) '' exponentialAnnulusDomain:=by
    rintro p ⟨q,hq,rfl⟩
    have hne:F q≠0:=by
      intro he
      have hh:=congrArg Complex.re he
      rw [hFr,Complex.zero_re] at hh
      exact hq.1.ne' hh
    let v:ExponentialAnnulusPoint:=Units.mk0 (F q) hne
    have hvr:(v:ℂ).re=q.1:=hFr q
    have hvi:(v:ℂ).im=(1-q.2)*Real.exp (-q.1)+q.2*(2*Real.exp (-q.1/2)):=hFi q
    refine ⟨v,exponentialAnnulus_tail_mem_domain v (hvr ▸ hq.1) ?_ ?_,rfl⟩
    · rw [hvr,hvi]
      have hpos:=mul_pos hq.2.1 (sub_pos.mpr (exponentialAnnulus_tail_gap hq.1.le))
      nlinarith
    · rw [hvr,hvi]
      have hpos:=mul_pos (sub_pos.mpr hq.2.2) (sub_pos.mpr (exponentialAnnulus_tail_gap hq.1.le))
      nlinarith
  let a:=Real.exp (-(z:ℂ).re)
  let b:=2*Real.exp (-(z:ℂ).re/2)
  let t:=((z:ℂ).im-a)/(b-a)
  have hab:0<b-a:=sub_pos.mpr (exponentialAnnulus_tail_gap hx)
  have ht:0≤t ∧ t≤1:=⟨div_nonneg (sub_nonneg.mpr hl) hab.le,
    (div_le_one hab).mpr (by dsimp only [a,b];linarith)⟩
  have hp:((z:ℂ).re,t)∈closure S:=by
    rw [show S=Ioi (0:ℝ)×ˢIoo (0:ℝ) 1 from rfl,closure_prod_eq,closure_Ioi,
      closure_Ioo (by norm_num : (0:ℝ)≠1)]
    exact ⟨hx,ht⟩
  have he:F ((z:ℂ).re,t)=(z:ℂ):=by
    apply Complex.ext
    · exact hFr _
    · rw [hFi]
      change (1-t)*a+t*b=(z:ℂ).im
      calc
        _=a+t*(b-a):=by ring
        _=(z:ℂ).im:=by dsimp only [t];rw [div_mul_cancel₀ _ hab.ne'];ring
  rw [Units.isEmbedding_val₀.closure_eq_preimage_closure_image]
  change (z:ℂ)∈closure ((Units.val:ℂˣ→ℂ) '' exponentialAnnulusDomain)
  rw [←he]
  exact closure_mono hsub (mem_closure_image hF.continuousAt hp)

theorem exponentialAnnulus_annular_weak_mem_closure (z:ExponentialAnnulusPoint)
    (hs:(z:ℂ).re≤0 ∨ (z:ℂ).im≤0) (hl:1≤‖(z:ℂ)‖) (hu:‖(z:ℂ)‖≤2) :
    z∈closure exponentialAnnulusDomain := by
  let W:ℝ→ℂ:=fun t=>(z:ℂ)-(t:ℂ)*(1+Complex.I)
  let r:ℝ→ℝ:=fun t=>(1-t)*‖(z:ℂ)‖+t*(3/2)
  let F:ℝ→ℂ:=fun t=>(r t/‖W t‖) • W t
  have hW:Continuous W:=by fun_prop
  have hr:Continuous r:=by fun_prop
  have hN:‖W 0‖≠0:=by simpa only [W,Complex.ofReal_zero,zero_mul,sub_zero] using
    norm_ne_zero_iff.mpr (Units.ne_zero z)
  have hF:ContinuousAt F 0:=(hr.continuousAt.div hW.norm.continuousAt hN).smul hW.continuousAt
  have hF0:F 0=(z:ℂ):=by
    simp only [F,r,W,sub_zero,add_zero,one_mul,Complex.ofReal_zero,zero_mul,
      div_self (norm_ne_zero_iff.mpr (Units.ne_zero z)),one_smul]
  have hsub:F '' Ioo (0:ℝ) 1⊆(Units.val:ℂˣ→ℂ) '' exponentialAnnulusDomain:=by
    rintro p ⟨t,ht,rfl⟩
    have ht0:0<t:=ht.1
    have ht1:t<1:=ht.2
    have hwneg:(W t).re<0 ∨ (W t).im<0:=by
      rcases hs with hs|hs
      · left
        simp only [W,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
          Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,
          sub_zero,mul_one,add_zero,zero_add]
        linarith
      · right
        simp only [W,Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
          Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,
          mul_one,add_zero,zero_add]
        linarith
    have hWne:W t≠0:=by
      intro he
      rcases hwneg with hh|hh <;> simp only [he,Complex.zero_re,Complex.zero_im,lt_self_iff_false] at hh
    have hrange:1<r t ∧ r t<2:=by
      dsimp only [r]
      constructor
      · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2.le) (sub_nonneg.mpr hl)]
      · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2.le) (sub_nonneg.mpr hu)]
    have hc:0<r t/‖W t‖:=div_pos (by linarith [hrange.1]) (norm_pos_iff.mpr hWne)
    have hnorm:‖F t‖=r t:=by
      dsimp only [F]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hc,div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hWne)]
    let v:ExponentialAnnulusPoint:=Units.mk0 (F t) (norm_pos_iff.mp (hnorm ▸ lt_trans (by norm_num) hrange.1))
    have hvneg:(v:ℂ).re<0 ∨ (v:ℂ).im<0:=by
      change (F t).re<0 ∨ (F t).im<0
      rcases hwneg with he|he
      · left
        simpa only [F,Complex.smul_re,smul_eq_mul] using mul_neg_of_pos_of_neg hc he
      · right
        simpa only [F,Complex.smul_im,smul_eq_mul] using mul_neg_of_pos_of_neg hc he
    refine ⟨v,exponentialAnnulus_annular_mem_domain v hvneg ?_ ?_,rfl⟩
    · change 1<‖F t‖
      rw [hnorm]
      exact hrange.1
    · change ‖F t‖<2
      rw [hnorm]
      exact hrange.2
  have hzero:(0:ℝ)∈closure (Ioo (0:ℝ) 1):=by
    rw [closure_Ioo (by norm_num : (0:ℝ)≠1)]
    norm_num
  rw [Units.isEmbedding_val₀.closure_eq_preimage_closure_image]
  change (z:ℂ)∈closure ((Units.val:ℂˣ→ℂ) '' exponentialAnnulusDomain)
  rw [←hF0]
  exact closure_mono hsub (mem_closure_image hF hzero)

theorem exponentialAnnulusDomain_closure : closure exponentialAnnulusDomain=exponentialAnnulusClosedRegion := by
  apply subset_antisymm exponentialAnnulusDomain_closure_subset
  intro z hz
  rcases hz with ht|ha
  · exact exponentialAnnulus_tail_weak_mem_closure z ht.1 ht.2.1 ht.2.2
  · exact exponentialAnnulus_annular_weak_mem_closure z ha.1 ha.2.1 ha.2.2

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open scoped Pointwise

theorem exponentialAnnulus_dyadic_bracket (a:ℝ) (ha:0<a) :
    ∃n:ℤ,a≤(2:ℝ)^n ∧ (2:ℝ)^n≤2*a := by
  obtain ⟨m,hm0,hm1⟩:=exists_mem_Ico_zpow ha (by norm_num : (1:ℝ)<2)
  refine ⟨m+1,hm1.le,?_⟩
  rw [zpow_add_one₀ (by norm_num : (2:ℝ)≠0)]
  nlinarith

theorem exponentialAnnulus_graph_ray_intersection (x y:ℝ) (hx:0<x) (hy:0<y) :
    ∃a:ℝ,0<a ∧ a*y=Real.exp (-(a*x)) := by
  let F:ℝ→ℝ:=fun a=>a*y*Real.exp (a*x)
  let M:ℝ:=1/y
  have hM:0<M:=one_div_pos.mpr hy
  have hc:Continuous F:=by fun_prop
  have h0:F 0=0:=by simp [F]
  have hMval:F M=Real.exp (M*x):=by
    change (1/y)*y*Real.exp (M*x)=_
    rw [one_div_mul_cancel hy.ne',one_mul]
  have hM1:1<F M:=by
    rw [hMval]
    exact Real.one_lt_exp_iff.mpr (mul_pos hM hx)
  obtain ⟨a,ha,he⟩:=intermediate_value_Icc hM.le hc.continuousOn
    (show (1:ℝ)∈Icc (F 0) (F M) from ⟨by rw [h0];norm_num,hM1.le⟩)
  have ha0:0<a:=lt_of_le_of_ne ha.1 (by
    intro heq
    rw [←heq,h0] at he
    norm_num at he)
  refine ⟨a,ha0,?_⟩
  rw [Real.exp_neg]
  simpa only [one_div] using (eq_div_iff (Real.exp_ne_zero _)).mpr he

theorem exponentialAnnulusPower_re (n:ℤ) (z:ExponentialAnnulusPoint) :
    ((exponentialAnnulusPower n•z:ExponentialAnnulusPoint):ℂ).re=(2:ℝ)^n*(z:ℂ).re := by
  rw [exponentialAnnulusPower_coe]
  simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]

theorem exponentialAnnulusPower_im (n:ℤ) (z:ExponentialAnnulusPoint) :
    ((exponentialAnnulusPower n•z:ExponentialAnnulusPoint):ℂ).im=(2:ℝ)^n*(z:ℂ).im := by
  rw [exponentialAnnulusPower_coe]
  simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]

theorem exponentialAnnulusPower_norm (n:ℤ) (z:ExponentialAnnulusPoint) :
    ‖((exponentialAnnulusPower n•z:ExponentialAnnulusPoint):ℂ)‖=(2:ℝ)^n*‖(z:ℂ)‖ := by
  rw [exponentialAnnulusPower_coe,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (zpow_pos (by norm_num : (0:ℝ)<2) n)]

theorem exponentialAnnulus_first_quadrant_orbit_region (z:ExponentialAnnulusPoint)
    (hx:0<(z:ℂ).re) (hy:0<(z:ℂ).im) :
    ∃n:ℤ,exponentialAnnulusPower n•z∈exponentialAnnulusClosedRegion := by
  obtain ⟨a,ha,hroot⟩:=exponentialAnnulus_graph_ray_intersection (z:ℂ).re (z:ℂ).im hx hy
  obtain ⟨n,hn0,hn1⟩:=exponentialAnnulus_dyadic_bracket a ha
  have hp:0<(2:ℝ)^n:=zpow_pos (by norm_num) _
  refine ⟨n,Or.inl ⟨?_,?_,?_⟩⟩
  · rw [exponentialAnnulusPower_re]
    exact mul_nonneg hp.le hx.le
  · rw [exponentialAnnulusPower_re,exponentialAnnulusPower_im]
    calc
      Real.exp (-((2:ℝ)^n*(z:ℂ).re))≤Real.exp (-(a*(z:ℂ).re)):=
        Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hn0) hx.le])
      _=a*(z:ℂ).im:=hroot.symm
      _≤(2:ℝ)^n*(z:ℂ).im:=mul_le_mul_of_nonneg_right hn0 hy.le
  · rw [exponentialAnnulusPower_re,exponentialAnnulusPower_im]
    calc
      (2:ℝ)^n*(z:ℂ).im≤2*(a*(z:ℂ).im):=by
        nlinarith [mul_nonneg (sub_nonneg.mpr hn1) hy.le]
      _=2*Real.exp (-(a*(z:ℂ).re)):=by rw [hroot]
      _≤2*Real.exp (-((2:ℝ)^n*(z:ℂ).re)/2):=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
          nlinarith [mul_nonneg (sub_nonneg.mpr hn1) hx.le])) (by norm_num)

theorem exponentialAnnulus_other_quadrants_orbit_region (z:ExponentialAnnulusPoint)
    (hs:(z:ℂ).re≤0 ∨ (z:ℂ).im≤0) :
    ∃n:ℤ,exponentialAnnulusPower n•z∈exponentialAnnulusClosedRegion := by
  have hz:0<‖(z:ℂ)‖:=norm_pos_iff.mpr (Units.ne_zero z)
  obtain ⟨n,hn0,hn1⟩:=exponentialAnnulus_dyadic_bracket (1/‖(z:ℂ)‖) (one_div_pos.mpr hz)
  have hp:0<(2:ℝ)^n:=zpow_pos (by norm_num) _
  refine ⟨n,Or.inr ⟨?_,?_,?_⟩⟩
  · rw [exponentialAnnulusPower_re,exponentialAnnulusPower_im]
    exact hs.imp (mul_nonpos_of_nonneg_of_nonpos hp.le) (mul_nonpos_of_nonneg_of_nonpos hp.le)
  · rw [exponentialAnnulusPower_norm]
    exact (div_le_iff₀ hz).mp hn0
  · rw [exponentialAnnulusPower_norm]
    have hh:=mul_le_mul_of_nonneg_right hn1 hz.le
    rw [mul_assoc,one_div_mul_cancel hz.ne',mul_one] at hh
    exact hh

theorem exponentialAnnulus_closed_meets_every_orbit :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit exponentialAnnulusGroup ExponentialAnnulusPoint (closure exponentialAnnulusDomain) := by
  intro z
  have hs:∃n:ℤ,exponentialAnnulusPower n•z∈exponentialAnnulusClosedRegion:=by
    by_cases h:0<(z:ℂ).re ∧ 0<(z:ℂ).im
    · exact exponentialAnnulus_first_quadrant_orbit_region z h.1 h.2
    · have hn:(z:ℂ).re≤0 ∨ (z:ℂ).im≤0:=by
        by_cases hr:(z:ℂ).re≤0
        · exact Or.inl hr
        · exact Or.inr (le_of_not_gt (fun hi=>h ⟨lt_of_not_ge hr,hi⟩))
      exact exponentialAnnulus_other_quadrants_orbit_region z hn
  obtain ⟨n,hn⟩:=hs
  exact ⟨exponentialAnnulusPower n,exponentialAnnulusDomain_closure.symm ▸ hn⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open scoped Pointwise

theorem exponentialAnnulus_norm_of_re_zero (z:ExponentialAnnulusPoint) (hx:(z:ℂ).re=0)
    (hy:0≤(z:ℂ).im) : ‖(z:ℂ)‖=(z:ℂ).im := by
  have he:(z:ℂ)=(↑((z:ℂ).im):ℂ)*Complex.I:=by
    apply Complex.ext
    · simpa only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero] using hx
    · simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
        Complex.I_re,Complex.I_im,mul_one,mul_zero,add_zero]
  calc
    ‖(z:ℂ)‖=‖(↑((z:ℂ).im):ℂ)*Complex.I‖:=congrArg norm he
    _=(z:ℂ).im:=by
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hy]
      simp only [Complex.norm_I,mul_one]

theorem exponentialAnnulus_other_region_norm (z:ExponentialAnnulusPoint) (hz:z∈exponentialAnnulusClosedRegion)
    (hs:(z:ℂ).re≤0 ∨ (z:ℂ).im≤0) : 1≤‖(z:ℂ)‖ ∧ ‖(z:ℂ)‖≤2 := by
  rcases hz with ht|ha
  · have hy:0<(z:ℂ).im:=lt_of_lt_of_le (Real.exp_pos _) ht.2.1
    have hx:(z:ℂ).re=0:=le_antisymm (hs.resolve_right (not_le_of_gt hy)) ht.1
    have he:Real.exp (-(z:ℂ).re)=1:=by rw [hx];norm_num
    have he':Real.exp (-(z:ℂ).re/2)=1:=by rw [hx];norm_num
    rw [exponentialAnnulus_norm_of_re_zero z hx hy.le]
    simpa only [he,he',mul_one] using ht.2
  · exact ha.2

theorem exponentialAnnulus_scaled_coordinates (r:ℝ) (z w:ExponentialAnnulusPoint)
    (hw:(w:ℂ)=(↑r:ℂ)*(z:ℂ)) (hr:0<r) :
    (w:ℂ).re=r*(z:ℂ).re ∧ (w:ℂ).im=r*(z:ℂ).im ∧
      ‖(w:ℂ)‖=r*‖(z:ℂ)‖ := by
  rw [hw]
  simp only [Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,add_zero,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hr,and_self]

theorem exponentialAnnulus_closed_scaled_overlap_curve (r:ℝ) (hr:2≤r)
    (z w:ExponentialAnnulusPoint) (hw:(w:ℂ)=(↑r:ℂ)*(z:ℂ))
    (hz:z∈exponentialAnnulusClosedRegion) (hwK:w∈exponentialAnnulusClosedRegion) :
    z∈exponentialAnnulusCurve := by
  obtain ⟨hxw,hyw,hnw⟩:=exponentialAnnulus_scaled_coordinates r z w hw (by linarith)
  by_cases hs:(z:ℂ).re≤0 ∨ (z:ℂ).im≤0
  · have hs':(w:ℂ).re≤0 ∨ (w:ℂ).im≤0:=by
      rw [hxw,hyw]
      exact hs.imp (mul_nonpos_of_nonneg_of_nonpos (by linarith))
        (mul_nonpos_of_nonneg_of_nonpos (by linarith))
    have hn:=exponentialAnnulus_other_region_norm z hz hs
    have hn':=exponentialAnnulus_other_region_norm w hwK hs'
    refine Or.inr ⟨hs,le_antisymm ?_ hn.1⟩
    rw [hnw] at hn'
    nlinarith
  · have hzx:0<(z:ℂ).re:=lt_of_not_ge (fun h=>hs (Or.inl h))
    have hzy:0<(z:ℂ).im:=lt_of_not_ge (fun h=>hs (Or.inr h))
    have ht:=hz.resolve_right (fun h=>hs h.1)
    have hwx:0<(w:ℂ).re:=hxw ▸ mul_pos (by linarith) hzx
    have hwy:0<(w:ℂ).im:=hyw ▸ mul_pos (by linarith) hzy
    have ht':=hwK.resolve_right (fun h=>h.1.elim (not_le_of_gt hwx) (not_le_of_gt hwy))
    have hle:Real.exp (-(w:ℂ).re/2)≤Real.exp (-(z:ℂ).re):=by
      apply Real.exp_le_exp.mpr
      rw [hxw]
      nlinarith [mul_nonneg (sub_nonneg.mpr hr) hzx.le]
    refine Or.inl ⟨ht.1,le_antisymm ?_ ht.2.1⟩
    rw [hyw] at ht'
    nlinarith [mul_nonneg (sub_nonneg.mpr hr) hzy.le]

theorem exponentialAnnulus_curve_inward_not_region (r:ℝ) (hr:0<r) (hr1:r<1)
    (z w:ExponentialAnnulusPoint) (hz:z∈exponentialAnnulusCurve)
    (hw:(w:ℂ)=(↑r:ℂ)*(z:ℂ)) : w∉exponentialAnnulusClosedRegion := by
  obtain ⟨hxw,hyw,hnw⟩:=exponentialAnnulus_scaled_coordinates r z w hw hr
  intro hwK
  rcases hz with ht|ha
  · have hzy:0<(z:ℂ).im:=ht.2 ▸ Real.exp_pos _
    have hwy:0<(w:ℂ).im:=hyw ▸ mul_pos hr hzy
    rcases hwK with hwt|hwa
    · have hmono:Real.exp (-(z:ℂ).re)≤Real.exp (-(w:ℂ).re):=by
        apply Real.exp_le_exp.mpr
        rw [hxw]
        nlinarith [mul_nonneg (sub_nonneg.mpr hr1.le) ht.1]
      rw [hyw] at hwt
      nlinarith [mul_pos (sub_pos.mpr hr1) hzy]
    · have hwx:(w:ℂ).re≤0:=hwa.1.resolve_right (not_le_of_gt hwy)
      have hzx:(z:ℂ).re=0:=by rw [hxw] at hwx;nlinarith
      have hzy1:(z:ℂ).im=1:=by rw [ht.2,hzx];norm_num
      have hn:‖(z:ℂ)‖=1:=by rw [exponentialAnnulus_norm_of_re_zero z hzx hzy.le,hzy1]
      rw [hnw,hn,mul_one] at hwa
      linarith [hwa.2.1]
  · have hs:(w:ℂ).re≤0 ∨ (w:ℂ).im≤0:=by
      rw [hxw,hyw]
      exact ha.1.imp (mul_nonpos_of_nonneg_of_nonpos hr.le)
        (mul_nonpos_of_nonneg_of_nonpos hr.le)
    have hn:=exponentialAnnulus_other_region_norm w hwK hs
    rw [hnw,ha.2,mul_one] at hn
    linarith [hn.1]

def exponentialAnnulusInwardPath (z:ExponentialAnnulusPoint) (t:ℝ) : ExponentialAnnulusPoint:=
  Units.mk0 (↑(Real.exp t):ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t))*z

theorem exponentialAnnulusInwardPath_coe (z:ExponentialAnnulusPoint) (t:ℝ) :
    ((exponentialAnnulusInwardPath z t:ExponentialAnnulusPoint):ℂ)=(↑(Real.exp t):ℂ)*(z:ℂ):=rfl

theorem exponentialAnnulusInwardPath_continuous (z:ExponentialAnnulusPoint) :
    Continuous (exponentialAnnulusInwardPath z) := by
  apply Units.isEmbedding_val₀.continuous_iff.mpr
  change Continuous (fun t:ℝ=>(↑(Real.exp t):ℂ)*(z:ℂ))
  fun_prop

theorem exponentialAnnulusInwardPath_zero (z:ExponentialAnnulusPoint) : exponentialAnnulusInwardPath z 0=z := by
  apply Units.ext
  simp only [exponentialAnnulusInwardPath_coe,Real.exp_zero,Complex.ofReal_one,one_mul]

theorem exponentialAnnulus_curve_not_domain (z:ExponentialAnnulusPoint) (hz:z∈exponentialAnnulusCurve) :
    z∉exponentialAnnulusDomain := by
  intro hD
  have hE:∀ᶠt:ℝ in 𝓝[<] (0:ℝ),exponentialAnnulusInwardPath z t∈exponentialAnnulusDomain:=by
    apply (exponentialAnnulusInwardPath_continuous z).continuousAt.tendsto.eventually
      (exponentialAnnulusDomain_isOpen.mem_nhds (exponentialAnnulusInwardPath_zero z ▸ hD)) |>.filter_mono
    exact nhdsWithin_le_nhds
  obtain ⟨t,ht,hmem⟩:=Filter.Eventually.exists (hE.and self_mem_nhdsWithin)
  have htneg:t<0:=hmem
  exact exponentialAnnulus_curve_inward_not_region (Real.exp t) (Real.exp_pos _)
    (Real.exp_lt_one_iff.mpr htneg) z (exponentialAnnulusInwardPath z t) hz
    (exponentialAnnulusInwardPath_coe z t) (interior_subset ht)

theorem exponentialAnnulus_positive_power_not_both_domain (n:ℤ) (hn:0<n)
    (z:ExponentialAnnulusPoint) (hz:z∈exponentialAnnulusDomain) :
    exponentialAnnulusPower n•z∉exponentialAnnulusDomain := by
  intro hw
  have hr:2≤(2:ℝ)^n:=by
    have h:=zpow_le_zpow_right₀ (by norm_num : (1:ℝ)≤2)
      (show (1:ℤ)≤n by omega)
    simpa only [zpow_one] using h
  have hc:=exponentialAnnulus_closed_scaled_overlap_curve ((2:ℝ)^n) hr z
    (exponentialAnnulusPower n•z) (exponentialAnnulusPower_coe n z) (interior_subset hz) (interior_subset hw)
  exact exponentialAnnulus_curve_not_domain z hc hz

theorem exponentialAnnulusDomain_orbit_rigid (g:exponentialAnnulusGroup) (z:ExponentialAnnulusPoint)
    (hz:z∈exponentialAnnulusDomain) (hgz:g•z∈exponentialAnnulusDomain) : g=1 := by
  obtain ⟨n,rfl⟩:=exponentialAnnulusGroup_power_exhaustive g
  rcases lt_trichotomy n 0 with hn|hn|hn
  · have hback:exponentialAnnulusPower (-n)•(exponentialAnnulusPower n•z)=z:=by
      change (exponentialAnnulusGenerator^(-n))*(exponentialAnnulusGenerator^n*z)=z
      rw [zpow_neg,inv_mul_cancel_left]
    exact False.elim (exponentialAnnulus_positive_power_not_both_domain (-n) (by omega)
      (exponentialAnnulusPower n•z) hgz (hback.symm ▸ hz))
  · subst n
    apply Subtype.ext
    change exponentialAnnulusGenerator^0=1
    exact zpow_zero _
  · exact False.elim (exponentialAnnulus_positive_power_not_both_domain n hn z hz hgz)

theorem exponentialAnnulusDomain_at_most_one_per_orbit (z w:ExponentialAnnulusPoint)
    (hz:z∈exponentialAnnulusDomain) (hw:w∈exponentialAnnulusDomain)
    (h:MulAction.orbitRel exponentialAnnulusGroup ExponentialAnnulusPoint z w) : z=w := by
  obtain ⟨g,hg⟩:=h
  change g•w=z at hg
  have hgz:g•w∈exponentialAnnulusDomain:=by rw [hg];exact hz
  have h1:=exponentialAnnulusDomain_orbit_rigid g w hw hgz
  simpa only [h1,one_smul] using hg.symm

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open scoped Pointwise

def exponentialAnnulusDirection (z:ExponentialAnnulusPoint) : Circle:=
  ⟨(z:ℂ)/(↑‖(z:ℂ)‖:ℂ),by
    change dist ((z:ℂ)/(↑‖(z:ℂ)‖:ℂ)) 0=1
    rw [dist_zero_right,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr (Units.ne_zero z))⟩

def exponentialAnnulusPolarInverse (p:ℝ×Circle) : ExponentialAnnulusPoint:=
  Units.mk0 ((↑(Real.exp (p.1*Real.log 2)):ℂ)*(p.2:ℂ))
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) (Circle.coe_ne_zero _))

theorem exponentialAnnulusPolarInverse_norm (p:ℝ×Circle) :
    ‖(exponentialAnnulusPolarInverse p:ℂ)‖=Real.exp (p.1*Real.log 2) := by
  change ‖(↑(Real.exp (p.1*Real.log 2)):ℂ)*(p.2:ℂ)‖=_
  rw [norm_mul,Circle.norm_coe,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

def exponentialAnnulusPolar : ExponentialAnnulusPoint≃ₜℝ×Circle where
  toFun z:=(Real.log ‖(z:ℂ)‖/Real.log 2,exponentialAnnulusDirection z)
  invFun:=exponentialAnnulusPolarInverse
  left_inv z:=by
    apply Units.ext
    have h2:Real.log 2≠0:=ne_of_gt (Real.log_pos (by norm_num))
    change (↑(Real.exp ((Real.log ‖(z:ℂ)‖/Real.log 2)*Real.log 2)):ℂ)*
      ((z:ℂ)/(↑‖(z:ℂ)‖:ℂ))=(z:ℂ)
    rw [div_mul_cancel₀ _ h2,Real.exp_log (norm_pos_iff.mpr (Units.ne_zero z))]
    exact mul_div_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (Units.ne_zero z)))
  right_inv p:=by
    apply Prod.ext
    · change Real.log ‖(exponentialAnnulusPolarInverse p:ℂ)‖/Real.log 2=p.1
      rw [exponentialAnnulusPolarInverse_norm,Real.log_exp]
      exact mul_div_cancel_right₀ _ (ne_of_gt (Real.log_pos (by norm_num)))
    · apply Circle.ext
      change (exponentialAnnulusPolarInverse p:ℂ)/(↑‖(exponentialAnnulusPolarInverse p:ℂ)‖:ℂ)=(p.2:ℂ)
      rw [exponentialAnnulusPolarInverse_norm]
      change ((↑(Real.exp (p.1*Real.log 2)):ℂ)*(p.2:ℂ))/(↑(Real.exp (p.1*Real.log 2)):ℂ)=_
      exact mul_div_cancel_left₀ _ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  continuous_toFun:=by
    apply Continuous.prodMk
    · exact (Units.continuous_val.norm.log (fun z=>norm_ne_zero_iff.mpr (Units.ne_zero z))).div_const _
    · apply Continuous.subtype_mk
      exact Units.continuous_val.div (Complex.continuous_ofReal.comp Units.continuous_val.norm)
        (fun z=>Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (Units.ne_zero z)))
  continuous_invFun:=by
    apply Units.isEmbedding_val₀.continuous_iff.mpr
    change Continuous (fun p:ℝ×Circle=>(↑(Real.exp (p.1*Real.log 2)):ℂ)*(p.2:ℂ))
    exact (Complex.continuous_ofReal.comp (Real.continuous_exp.comp
      (continuous_fst.mul_const _))).mul (continuous_subtype_val.comp continuous_snd)

theorem exponentialAnnulusPolar_power (n:ℤ) (z:ExponentialAnnulusPoint) :
    exponentialAnnulusPolar (exponentialAnnulusPower n•z)=
      ((n:ℝ)+(exponentialAnnulusPolar z).1,(exponentialAnnulusPolar z).2) := by
  have hpos:0<(2:ℝ)^n:=zpow_pos (by norm_num) _
  have hn:‖((exponentialAnnulusPower n•z:ExponentialAnnulusPoint):ℂ)‖=(2:ℝ)^n*‖(z:ℂ)‖:=by
    rw [exponentialAnnulusPower_coe,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hpos]
  apply Prod.ext
  · change Real.log ‖((exponentialAnnulusPower n•z:ExponentialAnnulusPoint):ℂ)‖/Real.log 2=_
    rw [hn,Real.log_mul hpos.ne' (norm_ne_zero_iff.mpr (Units.ne_zero z)),Real.log_zpow]
    change ((n:ℝ)*Real.log 2+Real.log ‖(z:ℂ)‖)/Real.log 2=_
    rw [add_div,mul_div_cancel_right₀ _ (ne_of_gt (Real.log_pos (by norm_num)))]
    rfl
  · apply Circle.ext
    change ((exponentialAnnulusPower n•z:ExponentialAnnulusPoint):ℂ)/(↑‖((exponentialAnnulusPower
      n•z:ExponentialAnnulusPoint):ℂ)‖:ℂ)=
      (z:ℂ)/(↑‖(z:ℂ)‖:ℂ)
    rw [hn,exponentialAnnulusPower_coe]
    push_cast
    exact mul_div_mul_left _ _ (zpow_ne_zero n (by norm_num : (2:ℂ)≠0))

def exponentialAnnulusTorusProjection : C(ExponentialAnnulusPoint,AddCircle (1:ℝ)×Circle) where
  toFun z:=(((exponentialAnnulusPolar z).1:AddCircle (1:ℝ)),(exponentialAnnulusPolar z).2)
  continuous_toFun:=
    (QuotientAddGroup.continuous_mk.comp (continuous_fst.comp exponentialAnnulusPolar.continuous)).prodMk
      (continuous_snd.comp exponentialAnnulusPolar.continuous)

theorem exponentialAnnulusTorusProjection_isQuotientMap : IsQuotientMap exponentialAnnulusTorusProjection := by
  have hq:IsQuotientMap (Prod.map (fun r:ℝ=>(r:AddCircle (1:ℝ))) (id:Circle→Circle)):=
    ((QuotientAddGroup.isOpenQuotientMap_mk (N:=AddSubgroup.zmultiples (1:ℝ))).prodMap
      IsOpenQuotientMap.id).isQuotientMap
  exact hq.comp exponentialAnnulusPolar.isQuotientMap

theorem exponentialAnnulusTorusProjection_power (n:ℤ) (z:ExponentialAnnulusPoint) :
    exponentialAnnulusTorusProjection (exponentialAnnulusPower n•z)=exponentialAnnulusTorusProjection z := by
  have hn:((n:ℝ):AddCircle (1:ℝ))=0:=
    (AddCircle.coe_eq_zero_iff _).mpr ⟨n,by simp⟩
  change (((exponentialAnnulusPolar (exponentialAnnulusPower n•z)).1:AddCircle (1:ℝ)),
    (exponentialAnnulusPolar (exponentialAnnulusPower n•z)).2)=_
  rw [exponentialAnnulusPolar_power]
  simp only [AddCircle.coe_add,hn,zero_add]
  rfl

theorem exponentialAnnulusTorusProjection_fiber (z w:ExponentialAnnulusPoint) :
    MulAction.orbitRel exponentialAnnulusGroup ExponentialAnnulusPoint z w ↔
      exponentialAnnulusTorusProjection z=exponentialAnnulusTorusProjection w := by
  constructor
  · rintro ⟨g,hg⟩
    obtain ⟨n,rfl⟩:=exponentialAnnulusGroup_power_exhaustive g
    rw [←hg]
    exact exponentialAnnulusTorusProjection_power n w
  · intro he
    obtain ⟨hr,hu⟩:=Prod.mk.inj he
    obtain ⟨n,hn⟩:=AddSubgroup.mem_zmultiples_iff.mp (QuotientAddGroup.eq_iff_sub_mem.mp hr)
    change n • (1:ℝ)=(exponentialAnnulusPolar z).1-(exponentialAnnulusPolar w).1 at hn
    rw [zsmul_eq_mul,mul_one] at hn
    refine ⟨exponentialAnnulusPower n,exponentialAnnulusPolar.injective ?_⟩
    rw [exponentialAnnulusPolar_power]
    apply Prod.ext
    · change (n:ℝ)+(exponentialAnnulusPolar w).1=(exponentialAnnulusPolar z).1
      linarith
    · exact hu.symm

/-- The actual nonzero complex plane modulo the entire cyclic group z↦2z is a torus. -/
def exponentialAnnulusAmbientTorusHomeomorph :
    ExponentialAnnulusAmbientQuotient≃ₜAddCircle (1:ℝ)×AddCircle (1:ℝ) :=
  ((Homeomorph.Quotient.congrRight (r:=MulAction.orbitRel exponentialAnnulusGroup ExponentialAnnulusPoint)
    (r':=Setoid.ker exponentialAnnulusTorusProjection) exponentialAnnulusTorusProjection_fiber).trans
      exponentialAnnulusTorusProjection_isQuotientMap.homeomorph).trans
        (Homeomorph.prodCongr (Homeomorph.refl _) (AddCircle.homeomorphCircle one_ne_zero).symm)

theorem exponentialAnnulusAmbientQuotient_compact : CompactSpace ExponentialAnnulusAmbientQuotient:=
  exponentialAnnulusAmbientTorusHomeomorph.symm.compactSpace

theorem exponentialAnnulus_quotients_not_homeomorphic :
    ¬Nonempty (ExponentialAnnulusClosedQuotient≃ₜExponentialAnnulusAmbientQuotient) := by
  rintro ⟨e⟩
  let :=exponentialAnnulusAmbientQuotient_compact
  exact exponentialAnnulusClosedQuotient_not_compact e.symm.compactSpace

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Filter Topology
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
open scoped Pointwise

/-- The point model is the literal punctured complex plane, with the same topology. -/
def exponentialAnnulusNonzeroComplexHomeomorph : ExponentialAnnulusPoint≃ₜ{z:ℂ // z≠0}:=
  unitsHomeomorphNeZero

theorem exponentialAnnulusGenerator_action (z:ExponentialAnnulusPoint) :
    ((exponentialAnnulusPower 1•z:ExponentialAnnulusPoint):ℂ)=2*(z:ℂ) := by
  simpa only [zpow_one,Complex.ofReal_ofNat] using exponentialAnnulusPower_coe 1 z

/-- The closure is precisely the exponential-tail and annular region in the diagram. -/
theorem exponentialAnnulus_exact_closed_diagram (z:ExponentialAnnulusPoint) :
    z∈closure exponentialAnnulusDomain ↔
      (0≤(z:ℂ).re ∧ Real.exp (-(z:ℂ).re)≤(z:ℂ).im ∧
        (z:ℂ).im≤2*Real.exp (-(z:ℂ).re/2)) ∨
      (((z:ℂ).re≤0 ∨ (z:ℂ).im≤0) ∧ 1≤‖(z:ℂ)‖ ∧ ‖(z:ℂ)‖≤2) := by
  rw [exponentialAnnulusDomain_closure]
  rfl

theorem exponentialAnnulus_comparison_continuous_bijective :
    Continuous (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.comparisonMap exponentialAnnulusGroup
      ExponentialAnnulusPoint (closure exponentialAnnulusDomain)) ∧
      Function.Bijective (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.comparisonMap
        exponentialAnnulusGroup ExponentialAnnulusPoint (closure exponentialAnnulusDomain)) :=
  ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.comparisonMap_continuous _ _
    _,_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.comparisonMap_bijective _ _ _
    exponentialAnnulus_closed_meets_every_orbit⟩

/-- The two literal orbit quotients have different compactness. -/
theorem exponentialAnnulus_fundamental_region_compact_torus_and_noncompact_restricted_quotient :
    IsOpen exponentialAnnulusDomain ∧
      closure exponentialAnnulusDomain=exponentialAnnulusClosedRegion ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit exponentialAnnulusGroup ExponentialAnnulusPoint (closure exponentialAnnulusDomain) ∧
      (∀z∈exponentialAnnulusDomain,∀w∈exponentialAnnulusDomain,
        MulAction.orbitRel exponentialAnnulusGroup ExponentialAnnulusPoint z w→z=w) ∧
      Nonempty (ExponentialAnnulusAmbientQuotient≃ₜAddCircle (1:ℝ)×AddCircle (1:ℝ)) ∧
      CompactSpace ExponentialAnnulusAmbientQuotient ∧
      ¬CompactSpace ExponentialAnnulusClosedQuotient ∧
      ¬Nonempty (ExponentialAnnulusClosedQuotient≃ₜExponentialAnnulusAmbientQuotient) :=
  ⟨exponentialAnnulusDomain_isOpen,exponentialAnnulusDomain_closure,exponentialAnnulus_closed_meets_every_orbit,
    fun z hz w hw h=>exponentialAnnulusDomain_at_most_one_per_orbit z w hz hw h,
    ⟨exponentialAnnulusAmbientTorusHomeomorph⟩,exponentialAnnulusAmbientQuotient_compact,
    exponentialAnnulusClosedQuotient_not_compact,exponentialAnnulus_quotients_not_homeomorphic⟩

end LowDimensionalTopology.Geometry.Fuchsian
