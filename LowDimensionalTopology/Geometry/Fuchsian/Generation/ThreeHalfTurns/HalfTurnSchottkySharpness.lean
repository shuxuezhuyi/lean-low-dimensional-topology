/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicSchottkySharpness
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.ParabolicEllipticBounds
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.ParabolicFordFundamentalDomains
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped UpperHalfPlane OnePoint MatrixGroups Topology Pointwise ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The actual hyperbolic word. -/
def halfTurnSchottkyProductSL (v : ℝ) (hv : 0<v) : Matrix.SpecialLinearGroup (Fin 2) ℝ:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1*_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv

theorem halfTurnSchottkyProductSL_coe (v : ℝ) (hv : 0<v) (z : ℍ) :
    ((halfTurnSchottkyProductSL v hv•z:ℍ):ℂ)=1-(v:ℂ)^2/(z:ℂ) := by
  rw [halfTurnSchottkyProductSL, mul_smul, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_coe]
  push_cast
  ring

theorem halfTurnSchottkyProductSL_trace (v : ℝ) (hv : 0<v) :
    Matrix.trace (halfTurnSchottkyProductSL v hv).val=1/v := by
  norm_num [halfTurnSchottkyProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL,Matrix.trace_fin_two,
    Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]

theorem halfTurnSchottkyProductSL_hyperbolic (v : ℝ) (hv : 0<v) (hvu : v<1/2) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (halfTurnSchottkyProductSL v hv)) := by
  have htr : 2<Matrix.trace (halfTurnSchottkyProductSL v hv).val:=by
    rw [halfTurnSchottkyProductSL_trace]
    exact (lt_div_iff₀ hv).mpr (by linarith only [hvu])
  have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (halfTurnSchottkyProductSL v hv)≠1:=by
    intro hid
    have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (halfTurnSchottkyProductSL v hv)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (1:Matrix.SpecialLinearGroup (Fin 2) ℝ):=by
      simpa only [map_one] using hid
    rcases (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_iff_sign _ _).mp he with he|he
    all_goals
      have hh:=congrArg (fun A:Matrix.SpecialLinearGroup (Fin 2) ℝ=>Matrix.trace A.val) he
      norm_num [Matrix.trace_fin_two] at hh
      rw [Matrix.trace_fin_two] at htr
      linarith only [hh,htr]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ hn).mpr (by nlinarith only [htr])

/-- The exact all-point product formula in the original example. -/
theorem halfTurnSchottkyProductSL_product (v : ℝ) (hv : 0<v) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) z*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (halfTurnSchottkyProductSL v hv)) z=
      ‖(z:ℂ)^2-(z:ℂ)+(v:ℂ)^2‖/(4*v*z.im^2) := by
  change Real.sinh (dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1•z)/2)*_=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.translation_half_displacement]
  norm_num only [abs_one]
  change 1/(2*z.im)*Real.sinh (dist z (halfTurnSchottkyProductSL v hv•z)/2)=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_half_displacement_polynomial]
  have hq : (halfTurnSchottkyProductSL v hv 1 0:ℂ)*(z:ℂ)^2+
      ((halfTurnSchottkyProductSL v hv 1 1:ℂ)-(halfTurnSchottkyProductSL v hv 0 0:ℂ))*(z:ℂ)-
        (halfTurnSchottkyProductSL v hv 0 1:ℂ)=((z:ℂ)^2-(z:ℂ)+(v:ℂ)^2)/(v:ℂ):=by
    norm_num [halfTurnSchottkyProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
    field_simp
    ring
  rw [hq,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv]
  field_simp
  ring

/-- The vertical-ray product has the precise limiting constant from the source. -/
theorem halfTurnSchottkyProductSL_vertical_upper (v : ℝ) (hv : 0<v) (y : ℝ) (hy : 0<y) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (halfTurnSchottkyProductSL v hv)) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy)≤
      (y^2+y+v^2)/(4*v*y^2) := by
  rw [halfTurnSchottkyProductSL_product]
  apply (div_le_div_iff_of_pos_right (by positivity : 0<4*v*y^2)).mpr
  have h1:=norm_add_le (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy:ℍ):ℂ)^2-((_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy:ℍ):ℂ)) ((v:ℂ)^2)
  have h2:=norm_sub_le (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy:ℍ):ℂ)^2) ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy:ℍ):ℂ)
  have hnorm : ‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy:ℍ):ℂ)‖=y:=by
    have he : ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hy:ℍ):ℂ)=Complex.I*(y:ℂ):=by
      apply Complex.ext <;> simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
    rw [he,norm_mul]
    simp [abs_of_pos hy]
  rw [norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv] at h1
  rw [norm_pow,hnorm] at h2
  nlinarith only [h1,h2,hnorm]


/-- Actual vertical points approach the exact source product constant. -/
theorem halfTurnSchottkyProductSL_approaches (v : ℝ) (hv : 0<v)
    (ε : ℝ) (hε : 0<ε) :
    ∃z:ℍ,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)) z*
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSinhDisplacement (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (halfTurnSchottkyProductSL v hv)) z<1/(4*v)+ε := by
  let y:=1+(1+v^2)/(4*v*ε)
  have hy : 1<y:=by
    have hp : 0<(1+v^2)/(4*v*ε):=by positivity
    dsimp only [y]
    linarith only [hp]
  have hypos : 0<y:=by linarith only [hy]
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 y hypos,?_⟩
  apply lt_of_le_of_lt (halfTurnSchottkyProductSL_vertical_upper v hv y hypos)
  apply (div_lt_iff₀ (by positivity : 0<4*v*y^2)).mpr
  have hR : (1/(4*v)+ε)*(4*v*y^2)=y^2+4*v*ε*y^2:=by
    field_simp
  rw [hR]
  have he : (1+v^2)=4*v*ε*(y-1):=by dsimp only [y];field_simp;ring
  have hprod : (1+v^2)*y<4*v*ε*y^2:=by
    rw [he]
    nlinarith only [mul_pos (mul_pos (by norm_num : (0:ℝ)<4) hv) hε,hypos]
  have hvy : 0≤v^2*(y-1):=mul_nonneg (sq_nonneg v) (by linarith only [hy])
  nlinarith only [hprod,hvy]

/-- The source's limiting value is the true all-plane infimum, with the
lower inequality valid at every actual native point. -/
theorem halfTurnSchottkyProductSL_displacementP (v : ℝ) (hv : 0<v) (hvu : v<1/2) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (halfTurnSchottkyProductSL v hv))=1/(4*v) := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨z,hz⟩:=halfTurnSchottkyProductSL_approaches v hv ε hε
    exact le_of_lt ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_le _ _ z).trans_lt hz)
  · apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP_lower_bound _ _ _).mpr
    intro z
    have htr : (4:ℝ)≤(Matrix.trace (halfTurnSchottkyProductSL v hv).val)^2:=by
      rw [halfTurnSchottkyProductSL_trace]
      have hh : 2<1/v:=(lt_div_iff₀ hv).mpr (by linarith only [hvu])
      nlinarith only [hh]
    have hcoef : halfTurnSchottkyProductSL v hv 1 0=1/v:=by
      norm_num [halfTurnSchottkyProductSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL,
        Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
    have h:=unitTranslation_displacement_product_lower _ htr z
    rw [hcoef,abs_of_pos (one_div_pos.mpr hv)] at h
    convert h using 1
    ring

/-- The half-turn's original full-sphere finite formula, including real points. -/
theorem halfTurnSchottky_coe (v : ℝ) (hv : 0<v) (z : ℂ) (hz : z≠0) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv)).val (z:Mobius.ExtendedComplex)=
      ((-(v:ℂ)^2/z:ℂ):Mobius.ExtendedComplex) := by
  change (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusSpecialLinearProjection
    (Matrix.SpecialLinearGroup.map Complex.ofRealHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv))).val (z:Mobius.ExtendedComplex)=_
  rw [_root_.LowDimensionalTopology.Geometry.Mobius.invariantDisc_specialLinear_action,
    _root_.LowDimensionalTopology.Geometry.Mobius.fractionalLinear_coe]
  norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL,hv.ne',hz]
  field_simp

/-- All nonidentity powers of the genuine half-turn are that actual half-turn. -/
theorem halfTurnSchottky_zpowers_nonidentity
    (v : ℝ)
    (hv : 0<v)
    (g : Mobius.complexMobiusGroup)
    (hg : g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv))) (hne : g≠1) :
    g=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv) := by
  classical
  let f:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv)
  change g∈Subgroup.zpowers f at hg
  have ho : orderOf f=2:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at v hv).1
  have hfin : IsOfFinOrder f:=orderOf_pos_iff.mp (by rw [ho];decide)
  obtain ⟨m,hm,rfl⟩:=Finset.mem_image.mp (hfin.mem_zpowers_iff_mem_range_orderOf.mp hg)
  have hm' : m<2:=by simpa only [ho,Finset.mem_range] using hm
  have h01 : m=0 ∨ m=1:=by omega
  rcases h01 with rfl|rfl
  · exact False.elim (hne (pow_zero _))
  · exact pow_one _

/-- The actual inversion takes every point outside its circle inside it. -/
theorem halfTurnSchottky_norm_bound (v : ℝ) (hv : 0<v) (z : ℂ) (hz : v<‖z‖) :
    ‖-(v:ℂ)^2/z‖<v := by
  rw [norm_div,norm_neg,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hv]
  apply (div_lt_iff₀ (hv.trans hz)).mpr
  simpa only [pow_two] using mul_lt_mul_of_pos_left hz hv

theorem halfTurnSchottky_outer (v : ℝ) (hv : 0<v) (hvu : v<1/2)
    (g : Mobius.complexMobiusGroup) (hg : g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv)))
    (hne : g≠1) : g • schottkyOuter⊆schottkyInner v := by
  rw [halfTurnSchottky_zpowers_nonidentity v hv g hg hne]
  rintro w ⟨u,⟨z,hz,rfl⟩,rfl⟩
  have hzn : v<‖z‖:=lt_of_lt_of_le (hvu.trans hz) (Complex.abs_re_le_norm z)
  exact ⟨-(v:ℂ)^2/z,halfTurnSchottky_norm_bound v hv z hzn,
    (halfTurnSchottky_coe v hv z (norm_pos_iff.mp (hv.trans hzn))).symm⟩

theorem halfTurnSchottky_gap (v : ℝ) (hv : 0<v)
    (g : Mobius.complexMobiusGroup) (hg : g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv)))
    (hne : g≠1) : g • schottkyGap v⊆schottkyInner v := by
  rw [halfTurnSchottky_zpowers_nonidentity v hv g hg hne]
  rintro w ⟨u,⟨z,hz,rfl⟩,rfl⟩
  exact ⟨-(v:ℂ)^2/z,halfTurnSchottky_norm_bound v hv z hz.2,
    (halfTurnSchottky_coe v hv z (norm_pos_iff.mp (hv.trans hz.2))).symm⟩

def halfTurnSchottkyGroup
    (v : ℝ)
    (hv : 0<v) : Subgroup Mobius.complexMobiusGroup:=
  Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv)}:Set Mobius.complexMobiusGroup)

theorem halfTurnSchottkyGroup_eq_sup (v : ℝ) (hv : 0<v) :
    halfTurnSchottkyGroup v hv=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1))⊔
      Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv)) := by
  rw [Subgroup.zpowers_eq_closure,Subgroup.zpowers_eq_closure,←Subgroup.closure_union]
  congr 1

/-- The original generated whole group has a genuine open wandering gap
on the sphere; the normal-word argument controls every actual member. -/
theorem halfTurnSchottkyGroup_wandering (v : ℝ) (hv : 0<v)
    (hvu : v<1/2) (g : Mobius.complexMobiusGroup)
    (hg : g∈halfTurnSchottkyGroup v hv) (hne : g≠1) :
    Disjoint (g • schottkyGap v) (schottkyGap v) := by
  let A:=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1))
  let B:=Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv))
  let F : Bool→Type:=fun | false=>A | true=>B
  let halfTurnSchottkyFactorGroups : ∀b,Group (F b):=fun | false=>inferInstance | true=>inferInstance
  let f : ∀b,F b→*Mobius.complexMobiusGroup:=fun | false=>A.subtype | true=>B.subtype
  let R : Bool→Set Mobius.ExtendedComplex:=fun b=>if b then schottkyInner v else schottkyOuter
  have hpp : Pairwise fun i j=>∀h:F i,h≠1→f i h • R j⊆R i:=by
    intro i j hij h hh
    cases i <;> cases j
    · exact False.elim (hij rfl)
    · exact schottky_translation_inner v hvu h.val h.property (fun he=>hh (Subtype.ext he))
    · exact halfTurnSchottky_outer v hv hvu h.val h.property (fun he=>hh (Subtype.ext he))
    · exact False.elim (hij rfl)
  have hstart : ∀i (h:F i),h≠1→f i h • schottkyGap v⊆R i:=by
    intro i h hh
    cases i
    · exact schottky_translation_gap v h.val h.property (fun he=>hh (Subtype.ext he))
    · exact halfTurnSchottky_gap v hv h.val h.property (fun he=>hh (Subtype.ext he))
  have hgap : ∀i,Disjoint (R i) (schottkyGap v):=by
    intro i
    cases i
    · exact schottkyOuter_disjoint_gap v
    · exact schottkyInner_disjoint_gap v
  have hrange : (Monoid.CoprodI.lift f).range=halfTurnSchottkyGroup v hv:=by
    rw [Monoid.CoprodI.range_eq_iSup]
    change (⨆b:Bool,(f b).range)=halfTurnSchottkyGroup v hv
    rw [iSup_bool_eq]
    change B.subtype.range⊔A.subtype.range=halfTurnSchottkyGroup v hv
    rw [Subgroup.range_subtype,Subgroup.range_subtype,sup_comm,halfTurnSchottkyGroup_eq_sup]
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.pingPong_range_wandering f R (schottkyGap v) hpp hstart hgap g _ hne
  rwa [hrange]


/-- Every actual parameter c>4 gives a discrete original whole Mobius group. -/
theorem halfTurnSchottkyGroup_discrete (v : ℝ) (hv : 0<v) (hvu : v<1/2) :
    _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (halfTurnSchottkyGroup v hv) := by
  obtain ⟨x,hx⟩:=schottkyGap_real_nonempty v hv hvu
  let p : Mobius.ExtendedComplex:=(x:ℂ)
  let f : halfTurnSchottkyGroup v hv→Mobius.ExtendedComplex:=fun g=>g.val.val p
  have hcont : Continuous f:=(_root_.LowDimensionalTopology.Geometry.Mobius.mobiusLocal_eval_continuous p).comp continuous_subtype_val
  have he : f ⁻¹' schottkyGap v=({1}:Set (halfTurnSchottkyGroup v hv)):=by
    ext g
    constructor
    · intro hgp
      apply Set.mem_singleton_iff.mpr
      by_contra hg
      have hne : g.val≠1:=fun h=>hg (Subtype.ext h)
      have hd:=halfTurnSchottkyGroup_wandering v hv hvu g.val g.property hne
      exact disjoint_left.mp hd ⟨p,hx,rfl⟩ hgp
    · rintro rfl
      exact hx
  apply discreteTopology_of_isOpen_singleton_one
  rw [←he]
  exact (schottkyGap_isOpen v).preimage hcont

/-- The wandering gap is disjoint from the closure of all actual
loxodromic fixed points, hence belongs to the original ordinary set. -/
theorem halfTurnSchottkyGap_subset_ordinary (v : ℝ) (hv : 0<v) (hvu : v<1/2) : schottkyGap v⊆_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet (halfTurnSchottkyGroup v hv) := by
  have hsub : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLoxodromicFixedPointSet (halfTurnSchottkyGroup v hv)⊆(schottkyGap v)ᶜ:=by
    rintro z ⟨g,hg,hfix⟩ hz
    have hd:=halfTurnSchottkyGroup_wandering v hv hvu g.val g.property hg.1
    exact disjoint_left.mp hd ⟨z,hz,hfix⟩ hz
  have hcl : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet (halfTurnSchottkyGroup v hv)⊆(schottkyGap v)ᶜ:=
    closure_minimal hsub (schottkyGap_isOpen v).isClosed_compl
  intro z hz hlim
  exact hcl hlim hz

/-- The literal generated group preserves the original half-plane and is
discrete; its invariant-disc data are derived from the actual real lifts. -/
theorem halfTurnSchottkyGroup_data (v : ℝ) (hv : 0<v) (hvu : v<1/2) :
    HalfPlaneFuchsianGroup (halfTurnSchottkyGroup v hv) where
  preserves g:=by
    have hreal : halfTurnSchottkyGroup v hv≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range:=by
      apply (Subgroup.closure_le _).mpr
      intro f hf
      rcases hf with rfl|rfl
      · exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1,rfl⟩
      · exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv,rfl⟩
    obtain ⟨A,hA⟩:=hreal g.property
    rw [←hA]
    exact realSLMobius_image_openHalfPlane A
  discrete:=halfTurnSchottkyGroup_discrete v hv hvu

theorem halfTurnSchottkyGroup_nonElementary (v : ℝ) (hv : 0<v) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (halfTurnSchottkyGroup v hv) := by
  apply parabolic_pair_nonElementary_of_no_common_fixed _ _ quarterTranslation_parabolic
  rintro ⟨p,hTp,hHp⟩
  obtain ⟨a,ha⟩:=quarterTranslation_parabolic.2
  have hTi : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)).val ∞=∞:=by
    rw [quarterTranslation_projection]
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty 1
  have hp : p=∞:=((ha p).mp hTp).trans ((ha ∞).mp hTi).symm
  rw [hp] at hHp
  have hc:_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv 1 0=0:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff _).mp hHp
  norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL,hv.ne'] at hc

/-- The genuine original Fuchsian group is of the second kind: a real
boundary point lies in its proved ordinary gap. -/
theorem halfTurnSchottkyGroup_secondKind (v : ℝ) (hv : 0<v) (hvu : v<1/2) :
    (halfTurnSchottkyGroup_data v hv hvu).asFuchsianDisc.IsSecondKind := by
  obtain ⟨x,hx⟩:=schottkyGap_real_nonempty v hv hvu
  have hxO:=halfTurnSchottkyGap_subset_ordinary v hv hvu hx
  refine ⟨(halfTurnSchottkyGroup_data v hv hvu).asFuchsianDisc.limitSet_subset_frontier,?_⟩
  intro hfull
  have hxF : ((x:ℂ):Mobius.ExtendedComplex)∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    rw [nielsen_openHalfPlane_frontier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_halfPlaneIdealBoundary]
    simp
  have hxL:=hfull hxF
  rw [fuchsianLimitSet_eq_nonElementary (halfTurnSchottkyGroup v hv)
    (halfTurnSchottkyGroup_nonElementary v hv)] at hxL
  exact hxO hxL


/-- The literal domain in the actual upper half-plane. -/
def halfTurnSchottkyDomain (v : ℝ) : Set ℍ:=
  {z | |z.re|<1/2 ∧ v<‖(z:ℂ)‖}

/-- Its literal weak-inequality closure candidate. -/
def halfTurnSchottkyClosedDomain (v : ℝ) : Set ℍ:=
  {z | -(1/2)≤z.re ∧ z.re≤1/2 ∧ v≤‖(z:ℂ)‖}

theorem halfTurnSchottkyDomain_isOpen (v : ℝ) : IsOpen (halfTurnSchottkyDomain v) :=
  (isOpen_lt UpperHalfPlane.continuous_re.abs continuous_const).inter
    (isOpen_lt continuous_const UpperHalfPlane.continuous_coe.norm)

theorem halfTurnSchottkyClosedDomain_isClosed (v : ℝ) : IsClosed (halfTurnSchottkyClosedDomain v) :=
  (isClosed_le continuous_const UpperHalfPlane.continuous_re).inter
    ((isClosed_le UpperHalfPlane.continuous_re continuous_const).inter
      (isClosed_le continuous_const UpperHalfPlane.continuous_coe.norm))

theorem halfTurnSchottkyDomain_eq_interior (v : ℝ) :
    halfTurnSchottkyDomain v=interior (halfTurnSchottkyClosedDomain v) := by
  apply Subset.antisymm
  · apply interior_maximal _ (halfTurnSchottkyDomain_isOpen v)
    intro z hz
    exact ⟨(abs_lt.mp hz.1).1.le,(abs_lt.mp hz.1).2.le,hz.2.le⟩
  · intro z hz
    have hl : z∈interior (UpperHalfPlane.re ⁻¹' Ici (-(1/2:ℝ))):=
      interior_mono (fun x hx=>(hx : x∈halfTurnSchottkyClosedDomain v).1) hz
    have hr : z∈interior (UpperHalfPlane.re ⁻¹' Iic ((1/2:ℝ))):=
      interior_mono (fun x hx=>(hx : x∈halfTurnSchottkyClosedDomain v).2.1) hz
    have hn : z∈interior ((fun w:ℍ=>‖(w:ℂ)‖) ⁻¹' Ici v):=
      interior_mono (fun x hx=>(hx : x∈halfTurnSchottkyClosedDomain v).2.2) hz
    rw [←UpperHalfPlane.isOpenMap_re.preimage_interior_eq_interior_preimage UpperHalfPlane.continuous_re,
      interior_Ici] at hl
    rw [←UpperHalfPlane.isOpenMap_re.preimage_interior_eq_interior_preimage UpperHalfPlane.continuous_re,
      interior_Iic] at hr
    rw [←UpperHalfPlane.isOpenMap_norm.preimage_interior_eq_interior_preimage UpperHalfPlane.continuous_coe.norm,
      interior_Ici] at hn
    exact ⟨abs_lt.mpr ⟨hl,hr⟩,hn⟩

theorem halfTurnSchottkyClosedDomain_hConvex (v : ℝ) (hv : 0<v) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex (halfTurnSchottkyClosedDomain v) := by
  have hden : {z:ℍ | 1≤‖realSLDenominator (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv) z‖}=
      {z:ℍ | v≤‖(z:ℂ)‖}:=by
    ext z
    have he : ‖realSLDenominator (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv) z‖=‖(z:ℂ)‖/v:=by
      simp [realSLDenominator,UpperHalfPlane.denom,_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL,Complex.norm_real,
        Real.norm_eq_abs,abs_of_pos hv,div_eq_mul_inv,mul_comm]
    rw [mem_ofPred_eq,mem_ofPred_eq,he,le_div_iff₀ hv,one_mul]
  have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HConvex {z:ℍ | v≤‖(z:ℂ)‖}:=by
    rw [←hden]
    apply parabolicFord_denominator_ge_hConvex (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv)
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL,hv.ne']
  intro x hx y hy z hz
  exact ⟨parabolicFord_hConvex_re_ge (-(1/2)) x hx.1 y hy.1 hz,
    parabolicFord_hConvex_re_le (1/2) x hx.2.1 y hy.2.1 hz,
    hn x hx.2.2 y hy.2.2 hz⟩

theorem halfTurnSchottkyDomain_nonempty (v : ℝ) (hv : 0<v) :
    (halfTurnSchottkyDomain v).Nonempty := by
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (v+1) (by positivity),?_,?_⟩
  · change |(0:ℝ)|<1/2
    norm_num
  · have he : ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (v+1) (by positivity):ℍ):ℂ)=Complex.I*(v+1:ℝ):=by
      apply Complex.ext <;> simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
    rw [he,norm_mul]
    simp only [Complex.norm_I,Complex.norm_real,Real.norm_eq_abs,one_mul,
      abs_of_pos (by positivity : 0<v+1)]
    linarith

theorem halfTurnSchottkyDomain_closure (v : ℝ) (hv : 0<v) :
    closure (halfTurnSchottkyDomain v)=halfTurnSchottkyClosedDomain v := by
  rw [halfTurnSchottkyDomain_eq_interior]
  exact parabolicFord_closure_interior_of_hConvex (halfTurnSchottkyClosedDomain_hConvex v hv)
    (halfTurnSchottkyClosedDomain_isClosed v)
    (by rw [←halfTurnSchottkyDomain_eq_interior];exact halfTurnSchottkyDomain_nonempty v hv)

theorem halfTurnSchottkyDomain_isConnected (v : ℝ) (hv : 0<v) :
    IsConnected (halfTurnSchottkyDomain v) := by
  refine ⟨halfTurnSchottkyDomain_nonempty v hv,?_⟩
  rw [halfTurnSchottkyDomain_eq_interior]
  exact (halfTurnSchottkyClosedDomain_hConvex v hv).interior.isPreconnected

/-- Both original generators belong to the actual whole group. -/
theorem halfTurnSchottkyGroup_generators (v : ℝ) (hv : 0<v) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈halfTurnSchottkyGroup v hv ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv)∈halfTurnSchottkyGroup v hv := by
  constructor
  · rw [←realSLMobius_unitTranslation]
    exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)

/-- The half-turn's exact genuine isometric-circle denominator. -/
theorem halfTurnSchottky_denominator_norm (v : ℝ) (hv : 0<v) (z : ℍ) :
    ‖realSLDenominator (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv) z‖=‖(z:ℂ)‖/v := by
  simp [realSLDenominator,UpperHalfPlane.denom,_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL,Complex.norm_real,
    Real.norm_eq_abs,abs_of_pos hv,div_eq_mul_inv,mul_comm]

/-- Every actual original orbit reaches the literal weak source domain.
Maximal-height orbit representatives and actual integer translations are
constructed in the same original group. -/
theorem halfTurnSchottkyDomain_closure_meetsEveryOrbit (v : ℝ) (hv : 0<v) (hvu : v<1/2) :
    letI:=(halfTurnSchottkyGroup_data v hv hvu).nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.MeetsEveryOrbit (halfTurnSchottkyGroup v hv) ℍ (closure (halfTurnSchottkyDomain v)) := by
  let P:=halfTurnSchottkyGroup_data v hv hvu
  let halfTurnSchottkyOriginalAction:=P.nativeAction
  have hT:_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1∈halfTurnSchottkyGroup v hv:=(halfTurnSchottkyGroup_generators v hv).1
  intro z
  obtain ⟨B,hB,_hheight,hExt⟩:=exists_ford_exterior_orbit_representative _ P.discrete hT z
  let n:ℤ:= -round (B•z:ℍ).re
  let A:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)*B
  have hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈halfTurnSchottkyGroup v hv:=by
    dsimp only [A]
    rw [map_mul]
    exact (halfTurnSchottkyGroup v hv).mul_mem
      (unitTranslation_integer_mem _ hT n) hB
  have hext : A•z∈mobiusFordExterior (halfTurnSchottkyGroup v hv):=by
    dsimp only [A]
    rw [mul_smul]
    exact parabolicFordExterior_integer_translate _ hT _ hExt n
  have habs : |(A•z:ℍ).re|≤1/2:=by
    have hre : (A•z:ℍ).re=(B•z:ℍ).re+(n:ℝ):=by
      dsimp only [A]
      rw [mul_smul]
      change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (n:ℝ)•(B•z):ℍ):ℂ).re=_
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
      simp
    rw [hre]
    simpa only [n,Int.cast_neg,sub_eq_add_neg] using abs_sub_round (B•z:ℍ).re
  have hnorm : v≤‖((A•z:ℍ):ℂ)‖:=by
    have hh:=hext ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv,(halfTurnSchottkyGroup_generators v hv).2⟩
    change 1≤‖realSLDenominator (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv) (A•z)‖ at hh
    rw [halfTurnSchottky_denominator_norm,le_div_iff₀ hv,one_mul] at hh
    exact hh
  refine ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,hA⟩,?_⟩
  rw [P.nativeAction_realSL _ A rfl,halfTurnSchottkyDomain_closure v hv]
  exact ⟨(abs_le.mp habs).1,(abs_le.mp habs).2,hnorm⟩

/-- The proved genuine sphere wandering property gives uniqueness for
actual original native orbit points in the literal source domain. -/
theorem halfTurnSchottkyDomain_orbit_unique (v : ℝ) (hv : 0<v) (hvu : v<1/2) :
    letI:=(halfTurnSchottkyGroup_data v hv hvu).nativeAction
    ∀x∈halfTurnSchottkyDomain v,∀y∈halfTurnSchottkyDomain v,
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (halfTurnSchottkyGroup v hv) ℍ x=
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.orbitProjection (halfTurnSchottkyGroup v hv) ℍ y→x=y := by
  let P:=halfTurnSchottkyGroup_data v hv hvu
  let halfTurnSchottkyOriginalAction:=P.nativeAction
  intro x hx y hy hxy
  obtain ⟨g,hgy⟩:=(Quotient.exact hxy : MulAction.orbitRel (halfTurnSchottkyGroup v hv) ℍ x y)
  change g•y=x at hgy
  by_cases hg:g=1
  · simpa only [hg,one_smul] using hgy.symm
  · have hgn:g.val≠1:=fun h=>hg (Subtype.ext h)
    have hd:=halfTurnSchottkyGroup_wandering v hv hvu g.val g.property hgn
    have hbd:=P.nativeAction_boundary g y
    rw [hgy] at hbd
    exact False.elim (disjoint_left.mp hd
      ⟨_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint y,⟨(y:ℂ),hy,rfl⟩,hbd⟩ ⟨(x:ℂ),hx,rfl⟩)

/-- The literal circular/vertical source region is an actual fundamental
domain for the original whole group and its true hyperbolic area. -/
theorem halfTurnSchottkyDomain_fundamental (v : ℝ) (hv : 0<v) (hvu : v<1/2) :
    letI:=(halfTurnSchottkyGroup_data v hv hvu).nativeAction
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (halfTurnSchottkyGroup v hv) ℍ volume (halfTurnSchottkyDomain v) := by
  let P:=halfTurnSchottkyGroup_data v hv hvu
  let halfTurnSchottkyOriginalAction:=P.nativeAction
  refine ⟨halfTurnSchottkyDomain_isOpen v,halfTurnSchottkyDomain_isConnected v hv,?_,?_⟩
  · exact exists_fundamentalSet_between _ _ subset_closure
      (halfTurnSchottkyDomain_closure_meetsEveryOrbit v hv hvu)
      (halfTurnSchottkyDomain_orbit_unique v hv hvu)
  · apply parabolicFord_hConvex_frontier_volume_zero
    rw [halfTurnSchottkyDomain_eq_interior]
    exact (halfTurnSchottkyClosedDomain_hConvex v hv).interior

/-- Replacing the source half-turn by its product with the unit
translation leaves the actual original generated group unchanged. -/
theorem halfTurnSchottkyProductSL_pair_group (v : ℝ) (hv : 0<v) :
    Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (halfTurnSchottkyProductSL v hv)}:Set Mobius.complexMobiusGroup)=
      halfTurnSchottkyGroup v hv := by
  let T:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1)
  let U:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL v hv)
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (halfTurnSchottkyProductSL v hv)
  let K:=Subgroup.closure ({T,F}:Set Mobius.complexMobiusGroup)
  have hword:F=T*U:=by dsimp only [F,T,U,halfTurnSchottkyProductSL];exact map_mul _ _ _
  change K=Subgroup.closure ({T,U}:Set Mobius.complexMobiusGroup)
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro f hf
    rcases hf with rfl|rfl
    · exact Subgroup.subset_closure (by simp)
    · rw [hword]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  · have hTK:T∈K:=Subgroup.subset_closure (by simp)
    have hFK:F∈K:=Subgroup.subset_closure (by simp)
    have hUK:U∈K:=by
      have he:U=T⁻¹*F:=by rw [hword];group
      rw [he]
      exact K.mul_mem (K.inv_mem hTK) hFK
    exact (Subgroup.closure_le _).mpr (by
      intro f hf
      rcases hf with rfl|rfl
      · exact hTK
      · exact hUK)

/-- The literal hyperbolic source map is the stated composition of two
actual reflections, on every native upper-half-plane point. -/
theorem halfTurnSchottkyProductSL_source_reflections (v : ℝ) (hv : 0<v) :
    (halfTurnSchottkyProductSL v hv•·:ℍ→ℍ)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection (1/2) ∘ _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 v hv := by
  funext z
  apply UpperHalfPlane.ext
  change ((halfTurnSchottkyProductSL v hv•z:ℍ):ℂ)=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection (1/2) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 v hv z):ℂ)
  rw [halfTurnSchottkyProductSL_coe, _root_.LowDimensionalTopology.Geometry.Hyperbolic.verticalReflection_coe,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe]
  simp only [Complex.ofReal_zero,sub_zero,map_add,map_div₀,map_pow,map_zero,
    Complex.conj_ofReal,Complex.conj_conj]
  push_cast
  ring

/-- Original second-kind groups give genuine parabolic/hyperbolic pairs
whose true all-point infima approach one half. -/
theorem halfTurnSchottky_secondKind_approaches (ε : ℝ) (hε : 0<ε) :
    ∃v:ℝ,∃hv:0<v,∃hvu:v<1/2,
      (halfTurnSchottkyGroup_data v hv hvu).asFuchsianDisc.IsSecondKind ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (halfTurnSchottkyGroup v hv) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (halfTurnSchottkyProductSL v hv)) ∧
      1/2<_root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (halfTurnSchottkyProductSL v hv)) ∧
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.displacementP (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL 1))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (halfTurnSchottkyProductSL v hv))<1/2+ε := by
  let v:=1/(2+2*ε)
  have hv:0<v:=by dsimp only [v];positivity
  have hvu:v<1/2:=by
    dsimp only [v]
    apply (div_lt_iff₀ (by positivity:0<2+2*ε)).mpr
    linarith only [hε]
  refine ⟨v,hv,hvu,halfTurnSchottkyGroup_secondKind v hv hvu,
    halfTurnSchottkyGroup_nonElementary v hv,
    halfTurnSchottkyProductSL_hyperbolic v hv hvu,?_,?_⟩
  all_goals
    rw [halfTurnSchottkyProductSL_displacementP v hv hvu]
    have he:1/(4*v)=(1+ε)/2:=by dsimp only [v];field_simp;ring
    rw [he]
    linarith only [hε]

end LowDimensionalTopology.Geometry.Fuchsian
