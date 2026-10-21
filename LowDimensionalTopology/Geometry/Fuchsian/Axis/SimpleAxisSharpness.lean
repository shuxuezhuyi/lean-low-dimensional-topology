/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.FuchsianAxisSeparation
public import LowDimensionalTopology.Geometry.DiscreteGroups.Packing.PackingFreeProducts
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.ThreeHalfTurnTriangleGroups
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Side.HyperbolicSideNecessity
public import LowDimensionalTopology.Geometry.DiscreteGroups.Discreteness.EllipticFreeDiscreteness
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped Topology UpperHalfPlane MatrixGroups OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- A reduced two-factor word can be paired into positive blocks, with at most
one involution at either end. The first factor consists of one involution. -/
theorem two_factor_reduced_word_positive_blocks
    {G : Type*} [Group G] (M : Bool → Type*) [∀ i, Monoid (M i)]
    (φ : ∀ i, M i →* G) (x : G) (hx : x*x=1) (S : Submonoid G)
    (hfalse : ∀ a : M false, a ≠ 1 → φ false a = x)
    (htrue : ∀ a : M true, a ≠ 1 → x*φ true a ∈ S)
    {i j : Bool} (w : Monoid.CoprodI.NeWord M i j) :
    ∃ p : G, p ∈ S ∧ Monoid.CoprodI.lift φ w.prod =
      (if i then x else 1)*p*(if j then 1 else x) := by
  induction w with
  | @singleton i a ha =>
    cases i
    · refine ⟨1, S.one_mem, ?_⟩
      change φ false a = 1*1*x
      simpa only [one_mul] using hfalse a ha
    · refine ⟨x*φ true a, htrue a ha, ?_⟩
      change φ true a = x*(x*φ true a)*1
      rw [mul_one, ← mul_assoc, hx, one_mul]
  | @append i j k l a hne b ha hb =>
    obtain ⟨p,hp,he⟩ := ha
    obtain ⟨q,hq,hf⟩ := hb
    refine ⟨p*q, S.mul_mem hp hq, ?_⟩
    rw [Monoid.CoprodI.NeWord.append_prod, map_mul, he, hf]
    cases j <;> cases k
    · exact False.elim (hne rfl)
    · simp only [Bool.false_eq_true, ite_false, ite_true]
      simp only [mul_assoc, ← mul_assoc x x, hx, one_mul]
    · simp only [ite_true, Bool.false_eq_true, ite_false, mul_one, one_mul, mul_assoc]
    · exact False.elim (hne rfl)

/-- Positive block normal form in the actual generated group of an involution
and an element of order three. -/
theorem order_two_three_positive_blocks
    {G : Type*} [Group G] (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 3)
    (S : Submonoid G) (hD : x*y ∈ S) (hE : x*y^2 ∈ S)
    (g : G) (hg : g ∈ Subgroup.closure ({x,y} : Set G)) :
    ∃ i j : Bool, ∃ p : G, p ∈ S ∧ g=(if i then x else 1)*p*(if j then 1 else x) := by
  classical
  let M : Bool → Subgroup G := fun b => if b then Subgroup.zpowers y else Subgroup.zpowers x
  let φ : ∀ b, M b →* G := fun b => (M b).subtype
  let π := Monoid.CoprodI.lift φ
  have hxM : x ∈ M false := Subgroup.mem_zpowers x
  have hyM : y ∈ M true := Subgroup.mem_zpowers y
  have hRange : Subgroup.closure ({x,y} : Set G) ≤ π.range := by
    apply (Subgroup.closure_le _).mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with he | he
    · exact ⟨Monoid.CoprodI.of (⟨x,hxM⟩ : M false), he.symm⟩
    · exact ⟨Monoid.CoprodI.of (⟨y,hyM⟩ : M true), (Set.mem_singleton_iff.mp he).symm⟩
  have hxx : x*x=1 := by simpa only [pow_two,hx] using pow_orderOf_eq_one x
  have hf (a : M false) (ha : a≠1) : φ false a=x := by
    obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp a.property
    have hem : 0≤n%2 ∧ n%2<2 := ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
    have hp : x^(n%2)=a.val := by simpa only [hx,Nat.cast_ofNat] using (zpow_mod_orderOf x n).trans hn
    have hc : n%2=0 ∨ n%2=1 := by omega
    rcases hc with he|he
    · rw [he,zpow_zero] at hp
      exact False.elim (ha (Subtype.ext hp.symm))
    · change a.val=x
      simpa only [he,zpow_one] using hp.symm
  have ht (a : M true) (ha : a≠1) : x*φ true a ∈ S := by
    obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp a.property
    have hem : 0≤n%3 ∧ n%3<3 := ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
    have hp : y^(n%3)=a.val := by simpa only [hy,Nat.cast_ofNat] using (zpow_mod_orderOf y n).trans hn
    have hc : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
    rcases hc with he|he|he
    · rw [he,zpow_zero] at hp
      exact False.elim (ha (Subtype.ext hp.symm))
    · rw [he,zpow_one] at hp
      change x*a.val∈S
      rw [←hp]
      exact hD
    · rw [he,show (2:ℤ)=(2:ℕ) by norm_num,zpow_natCast] at hp
      change x*a.val∈S
      rw [←hp]
      exact hE
  obtain ⟨w,hw⟩ := hRange hg
  let v := Monoid.CoprodI.Word.equiv w
  have hv : v.prod=w := (Monoid.CoprodI.Word.equiv).symm_apply_apply w
  by_cases he : v=Monoid.CoprodI.Word.empty
  · have hg1 : g=1 := by rw [←hw,←hv,he,Monoid.CoprodI.Word.prod_empty,map_one]
    exact ⟨false,true,1,S.one_mem,by simp only [hg1,Bool.false_eq_true,ite_false,ite_true,mul_one]⟩
  · obtain ⟨i,j,u,hu⟩ := Monoid.CoprodI.NeWord.of_word v he
    obtain ⟨p,hp,hprod⟩ := two_factor_reduced_word_positive_blocks (fun b => M b) φ x hxx S hf ht u
    refine ⟨i,j,p,hp,?_⟩
    rw [←hprod]
    change g=π u.toWord.prod
    rw [hu,hv,hw]

/-- A rational hyperbolic generator for the sharp collar example. -/
def sharpCollarD : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![2,0;0,1/2],by norm_num [Matrix.det_fin_two]⟩

/-- The actual rational half-turn in the same example. -/
def sharpCollarF : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![2/3,-13/9;1,-2/3],by norm_num [Matrix.det_fin_two]⟩

/-- The second positive block is a conjugate of the inverse dilation. -/
def sharpCollarE : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![8/3,-13/9;1,-1/6],by norm_num [Matrix.det_fin_two]⟩

theorem sharpCollarF_order : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF)=2 :=
  (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_order_two_iff_trace_zero sharpCollarF
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_trace_zero_ne_one sharpCollarF (by norm_num [sharpCollarF,Matrix.trace_fin_two]))).mpr
      (by norm_num [sharpCollarF,Matrix.trace_fin_two])

theorem sharpCollarR_order : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpCollarF*sharpCollarD))=3 := by
  have htr : Matrix.trace (sharpCollarF*sharpCollarD).val=1 := by
    norm_num [sharpCollarF,sharpCollarD,Matrix.trace_fin_two,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpCollarF*sharpCollarD)≠1 := by
    intro he
    have hh:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_sq_of_projection_one (sharpCollarF*sharpCollarD) he
    rw [htr] at hh
    norm_num at hh
  apply realSL_order_of_reciprocal_cosine_trace _ hn 3 (by omega)
  rw [htr]
  norm_num [Real.cos_pi_div_three]

theorem sharpCollarE_conjugate : sharpCollarE=sharpCollarF*sharpCollarD⁻¹*sharpCollarF⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sharpCollarE,sharpCollarF,sharpCollarD,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,
      Matrix.mul_apply,Fin.sum_univ_two]

/-- A projective boundary trap, with the point at infinity retained. -/
def sharpCollarAllowed : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := {z | z=∞ ∨ ∃ x : ℝ,
  z=((x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧ (x=0 ∨ x=2/3 ∨ 13/6≤x)}

def sharpCollarNonnegative : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := {z | z=∞ ∨ ∃ x : ℝ,
  z=((x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧ 0≤x}

theorem sharpCollarAllowed_nonnegative : sharpCollarAllowed⊆sharpCollarNonnegative := by
  rintro z (he|⟨x,rfl,hx⟩)
  · exact Or.inl he
  · refine Or.inr ⟨x,rfl,?_⟩
    rcases hx with rfl|rfl|hx <;> linarith

theorem sharpCollarD_allowed : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD).val '' sharpCollarAllowed⊆sharpCollarAllowed := by
  rintro z ⟨w,(rfl|⟨x,rfl,hx⟩),rfl⟩
  · exact Or.inl (by norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_infty,sharpCollarD])
  · have he : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    sharpCollarD).val (((x:ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
        (((4*x:ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
      norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_apply,sharpCollarD]
      ring
    rw [he]
    refine Or.inr ⟨4*x,rfl,?_⟩
    rcases hx with rfl|rfl|hx
    · exact Or.inl (by ring)
    · exact Or.inr (Or.inr (by norm_num))
    · exact Or.inr (Or.inr (by linarith))

theorem sharpCollarE_allowed : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarE).val '' sharpCollarAllowed⊆sharpCollarAllowed := by
  rintro z ⟨w,(rfl|⟨x,rfl,hx⟩),rfl⟩
  · refine Or.inr ⟨8/3,?_,Or.inr (Or.inr (by norm_num))⟩
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_infty,sharpCollarE]
  · rcases hx with rfl|rfl|hx
    · refine Or.inr ⟨26/3,?_,Or.inr (Or.inr (by norm_num))⟩
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_apply]
      norm_num [sharpCollarE]
    · refine Or.inr ⟨2/3,?_,Or.inr (Or.inl rfl)⟩
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_apply]
      norm_num [sharpCollarE]
    · have hd : 0<x-1/6 := by linarith
      have he : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        sharpCollarE).val (((x:ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
          (((((8/3)*x-13/9)/(x-1/6):ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
        rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_apply]
        change (if 1*x+(-1/6:ℝ)=0 then ∞ else
          (((((8/3:ℝ)*x+(-13/9))/(1*x+(-1/6)):ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) = _
        simp only [one_mul]
        rw [ite_eq_right (by linarith : x + (-1:ℝ)/6 ≠ 0)]
        norm_num [sub_eq_add_neg]
      rw [he]
      refine Or.inr ⟨_,rfl,Or.inr (Or.inr ?_)⟩
      exact (le_div_iff₀ hd).mpr (by nlinarith only [hx])

theorem sharpCollarF_allowed_nonnegative :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF).val '' sharpCollarAllowed⊆sharpCollarNonnegative := by
  rintro z ⟨w,(rfl|⟨x,rfl,hx⟩),rfl⟩
  · refine Or.inr ⟨2/3,?_,by norm_num⟩
    norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_infty,sharpCollarF]
  · rcases hx with rfl|rfl|hx
    · refine Or.inr ⟨13/6,?_,by norm_num⟩
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_apply]
      norm_num [sharpCollarF]
    · exact Or.inl (by rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_apply]; norm_num [sharpCollarF])
    · have hd : 0<x-2/3 := by linarith
      have he : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        sharpCollarF).val (((x:ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=
          (((((2/3)*x-13/9)/(x-2/3):ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
        rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_apply]
        change (if 1*x+(-2/3:ℝ)=0 then ∞ else
          (((((2/3:ℝ)*x+(-13/9))/(1*x+(-2/3)):ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) = _
        simp only [one_mul]
        rw [ite_eq_right (by linarith : x + (-2:ℝ)/3 ≠ 0)]
        norm_num [sub_eq_add_neg]
      rw [he]
      exact Or.inr ⟨_,rfl,div_nonneg (by linarith) hd.le⟩

/-- The genuine positive-block monoid preserves the explicit boundary trap. -/
def sharpCollarPositiveBlocks : Submonoid _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup where
  carrier := {g | ∀ z∈sharpCollarAllowed, g.val z∈sharpCollarAllowed}
  one_mem' := by intro z hz; exact hz
  mul_mem' := by intro g h hg hh z hz; exact hg _ (hh z hz)

def sharpCollarGroup : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpCollarF*sharpCollarD)} : Set
      _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)

theorem sharpCollar_positive_generators :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpCollarF*sharpCollarD)∈sharpCollarPositiveBlocks ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpCollarF*sharpCollarD))^2∈sharpCollarPositiveBlocks := by
  let f:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF
  let r:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpCollarF*sharpCollarD)
  have hfo : orderOf f=2 := sharpCollarF_order
  have hro : orderOf r=3 := sharpCollarR_order
  have hrd : r=f*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD := map_mul _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius _ _
  have hf : f*f=1 := by simpa only [hfo,pow_two] using pow_orderOf_eq_one f
  have hfi : f⁻¹=f := by
    calc f⁻¹=f⁻¹*(f*f) := by rw [hf,mul_one]
         _=f := by group
  have hr : r^3=1 := by simpa only [hro] using pow_orderOf_eq_one r
  have hr2 : r^2=r⁻¹ := eq_inv_iff_mul_eq_one.mpr (by
    simpa only [←pow_succ] using hr)
  constructor
  · change f*r∈sharpCollarPositiveBlocks
    have he : f*r=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD := by
      rw [hrd]
      rw [←mul_assoc,hf,one_mul]
    rw [he]
    intro z hz
    exact sharpCollarD_allowed ⟨z,hz,rfl⟩
  · change f*r^2∈sharpCollarPositiveBlocks
    have he : f*r^2=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarE := by
      rw [hr2]
      rw [hrd]
      rw [mul_inv_rev,hfi,sharpCollarE_conjugate,map_mul,map_mul,map_inv,map_inv]
      change f*((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        sharpCollarD)⁻¹*f)=f*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD)⁻¹*f⁻¹
      rw [hfi,mul_assoc]
    rw [he]
    intro z hz
    exact sharpCollarE_allowed ⟨z,hz,rfl⟩

/-- Every original group element sends each endpoint of the simple candidate
axis to the actual nonnegative extended real boundary. -/
theorem sharpCollarGroup_endpoints_nonnegative (g :
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hg : g∈sharpCollarGroup)
    (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hz :
      z=((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∨ z=∞) :
    g.val z∈sharpCollarNonnegative := by
  obtain ⟨i,j,p,hp,he⟩ := order_two_three_positive_blocks
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      sharpCollarF) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpCollarF*sharpCollarD))
    sharpCollarF_order sharpCollarR_order sharpCollarPositiveBlocks
    sharpCollar_positive_generators.1 sharpCollar_positive_generators.2 g hg
  let b := (if j then (1:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) else
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF).val z
  have hb : b∈sharpCollarAllowed := by
    rcases hz with rfl|rfl <;> cases j
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      sharpCollarF).val (((0:ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈sharpCollarAllowed
      refine Or.inr ⟨13/6,?_,Or.inr (Or.inr le_rfl)⟩
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_apply]
      norm_num [sharpCollarF]
    · exact Or.inr ⟨0,rfl,Or.inl rfl⟩
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF).val ∞∈sharpCollarAllowed
      refine Or.inr ⟨2/3,?_,Or.inr (Or.inl rfl)⟩
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_infty]
      norm_num [sharpCollarF]
    · exact Or.inl rfl
  have hpb : p.val b∈sharpCollarAllowed := hp b hb
  rw [he]
  change (if i then _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF else
    (1:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)).val (p.val b)∈sharpCollarNonnegative
  cases i
  · exact sharpCollarAllowed_nonnegative hpb
  · exact sharpCollarF_allowed_nonnegative ⟨_,hpb,rfl⟩

/-- All actual elements admit true real determinant-one representatives. -/
theorem sharpCollarGroup_real (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hg :
  g∈sharpCollarGroup) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=g := by
  have hr : sharpCollarGroup≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius.range := by
    apply (Subgroup.closure_le _).mpr
    intro h hh
    rcases Set.mem_insert_iff.mp hh with he|he
    · exact ⟨sharpCollarF,he.symm⟩
    · exact ⟨sharpCollarF*sharpCollarD,(Set.mem_singleton_iff.mp he).symm⟩
  exact hr hg

theorem sharpCollarNonnegative_real_iff (x : ℝ) :
    (((x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈sharpCollarNonnegative) ↔ 0≤x := by
  constructor
  · rintro (he|⟨y,he,hy⟩)
    · exact False.elim ((OnePoint.coe_ne_infty (x:ℂ)) he)
    · have hxy : x=y := Complex.ofReal_injective (OnePoint.coe_injective he)
      exact hxy ▸ hy
  · intro hx
    exact Or.inr ⟨x,rfl,hx⟩

/-- Endpoint positivity is an actual projective property, independent of the
sign of a determinant-one representative. -/
theorem realSL_nonnegative_endpoints_products (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h0 : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val
      ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈sharpCollarNonnegative)
    (hi : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ∞∈sharpCollarNonnegative) :
    0≤A 0 0*A 1 0 ∧ 0≤A 0 1*A 1 1 := by
  constructor
  · by_cases hc : A 1 0=0
    · simp only [hc,mul_zero,le_refl]
    · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_infty,ite_eq_right
      hc,sharpCollarNonnegative_real_iff] at hi
      have he : A 0 0*A 1 0=(A 0 0/A 1 0)*(A 1 0)^2 := by field_simp
      rw [he]
      exact mul_nonneg hi (sq_nonneg _)
  · by_cases hd : A 1 1=0
    · simp only [hd,mul_zero,le_refl]
    · rw [axisSL_real_zero A hd,sharpCollarNonnegative_real_iff] at h0
      have he : A 0 1*A 1 1=(A 0 1/A 1 1)*(A 1 1)^2 := by field_simp
      rw [he]
      exact mul_nonneg h0 (sq_nonneg _)

/-- The explicit whole group has a genuinely stable imaginary axis. -/
theorem sharpCollarGroup_axis_stable :
    _root_.LowDimensionalTopology.Geometry.Surfaces.MobiusStableSet sharpCollarGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier) := by
  intro g hg
  obtain ⟨A,rfl⟩ := sharpCollarGroup_real g hg
  have hp := realSL_nonnegative_endpoints_products A
    (sharpCollarGroup_endpoints_nonnegative _ hg _ (Or.inl rfl))
    (sharpCollarGroup_endpoints_nonnegative _ hg _ (Or.inr rfl))
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneSpherePoint_image_realSL]
  by_cases he : (A • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
    0).carrier=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier
  · exact Or.inl (congrArg (Set.image _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedHalfPlanePoint) he)
  · right
    apply (Set.disjoint_image_iff _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneSpherePoint_injective).mpr
    apply Set.disjoint_left.mpr
    rintro z ⟨p,hpL,rfl⟩ hz
    have hn := axisSL_crossing_product_neg A he hpL hz
    exact not_lt_of_ge (mul_nonneg hp.1 hp.2) hn

theorem realSL_commutatorTrace_actual (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B)=
      ((Matrix.trace (A*B*A⁻¹*B⁻¹).val : ℝ):ℂ) := by
  trans (_root_.LowDimensionalTopology.Geometry.Mobius.Classification.specialCommutator
    (Matrix.SpecialLinearGroup.map Complex.ofRealHom A)
    (Matrix.SpecialLinearGroup.map Complex.ofRealHom
      B) : _root_.LowDimensionalTopology.Geometry.Auxiliary.Algebra.ComplexMatrix2).trace
  · exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace_representatives _ _ _ _ rfl rfl
  · simp only [_root_.LowDimensionalTopology.Geometry.Mobius.Classification.specialCommutator,Matrix.trace_fin_two,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
    simp only [Matrix.SpecialLinearGroup.map_apply_coe,RingHom.mapMatrix_apply,Matrix.map_apply]
    have hcast (x : ℝ) : Complex.ofRealHom x=(x:ℂ) := rfl
    simp only [hcast]
    push_cast
    ring

theorem sharpCollarD_commutatorTrace (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)=
      (((2-(9/4)*A 0 1*A 1 0 : ℝ):ℂ)) := by
  rw [realSL_commutatorTrace_actual]
  apply congrArg Complex.ofReal
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_commutator_trace]
  norm_num only [sharpCollarD,Matrix.trace_fin_two,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  have hd:=A.det_coe
  rw [Matrix.det_fin_two] at hd
  nlinarith only [hd]

/-- Near the identity the endpoint trap forces a real representative to be diagonal. -/
theorem sharpCollar_small_trace_diagonal (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈sharpCollarGroup)
    (hsmall : ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)-2‖<1) :
    A 0 1=0 ∧ A 1 0=0 := by
  have hp := realSL_nonnegative_endpoints_products A
    (sharpCollarGroup_endpoints_nonnegative _ hA _ (Or.inl rfl))
    (sharpCollarGroup_endpoints_nonnegative _ hA _ (Or.inr rfl))
  have hAi : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A⁻¹∈sharpCollarGroup := by
    rw [map_inv]
    exact sharpCollarGroup.inv_mem hA
  have hpi := realSL_nonnegative_endpoints_products A⁻¹
    (sharpCollarGroup_endpoints_nonnegative _ hAi _ (Or.inl rfl))
    (sharpCollarGroup_endpoints_nonnegative _ hAi _ (Or.inr rfl))
  simp only [Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] at hpi
  have he : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)-2=
      (((-(9/4)*A 0 1*A 1 0:ℝ):ℂ)) := by
    rw [sharpCollarD_commutatorTrace]
    push_cast
    ring
  rw [he,Complex.norm_real,Real.norm_eq_abs] at hsmall
  have hbc : -1<A 0 1*A 1 0 := by
    have hh:=le_abs_self (-(9/4)*A 0 1*A 1 0)
    nlinarith only [hh,hsmall]
  have hd:=A.det_coe
  rw [Matrix.det_fin_two] at hd
  have had : 0<A 0 0*A 1 1 := by linarith only [hd,hbc]
  constructor
  · by_contra hb
    have hn:=mul_pos had (sq_pos_of_ne_zero hb)
    have hx:=mul_nonneg hp.2 hpi.2
    nlinarith only [hn,hx]
  · by_contra hc
    have hn:=mul_pos had (sq_pos_of_ne_zero hc)
    have hx:=mul_nonneg hp.1 hpi.1
    nlinarith only [hn,hx]

/-- Two genuine small commutator traces isolate the identity in the original group. -/
theorem sharpCollar_two_small_traces_identity (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A∈sharpCollarGroup)
    (hsmall : ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)-2‖<1)
    (hsmallF : ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        sharpCollarF*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        A*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF)⁻¹)-2‖<1) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=1 := by
  have hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF∈sharpCollarGroup := Subgroup.subset_closure (by simp)
  have hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpCollarF*A*sharpCollarF⁻¹)∈sharpCollarGroup := by
    rw [map_mul,map_mul,map_inv]
    exact sharpCollarGroup.mul_mem (sharpCollarGroup.mul_mem hf hA) (sharpCollarGroup.inv_mem hf)
  obtain ⟨hb,hc⟩ := sharpCollar_small_trace_diagonal A hA hsmall
  have hsmallB : ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpCollarF*A*sharpCollarF⁻¹))-2‖<1 := by
    rwa [map_mul,map_mul,map_inv]
  have hBb := (sharpCollar_small_trace_diagonal _ hB hsmallB).1
  have he : A 0 0=A 1 1 := by
    simp only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
      Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] at hBb
    norm_num [sharpCollarF,hb,hc] at hBb
    linarith only [hBb]
  have hd:=A.det_coe
  rw [Matrix.det_fin_two,hb,hc,he] at hd
  have ha : A 1 1=1 ∨ A 1 1= -1 := by
    have hh : (A 1 1-1)*(A 1 1+1)=0 := by nlinarith only [hd]
    rcases mul_eq_zero.mp hh with hh|hh
    · exact Or.inl (by linarith only [hh])
    · exact Or.inr (by linarith only [hh])
  have hproj : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (1:Matrix.SpecialLinearGroup (Fin 2) ℝ) := by
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_iff_sign A 1).mpr
    rcases ha with ha|ha
    · left
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb,hc,he,ha]
    · right
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hb,hc,he,ha]
  simpa only [map_one] using hproj

/-- Actual discreteness is proved by an explicit open identity neighborhood,
not supplied by a claimed fundamental polygon. -/
theorem sharpCollarGroup_discrete : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup sharpCollarGroup := by
  let f:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF
  let d:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD
  let q (g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) := ‖_root_.LowDimensionalTopology.Geometry.Mobius.mobiusCommutatorTrace d g-2‖
  have hq : Continuous q := ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFree_commutatorTrace_continuous_right d).sub continuous_const).norm
  have hconj : Continuous (fun g : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup => f*g*f⁻¹) := by fun_prop
  let U : Set sharpCollarGroup := {g | q g.val<1 ∧ q (f*g.val*f⁻¹)<1}
  have ho : IsOpen U :=
    (isOpen_lt (hq.comp continuous_subtype_val) continuous_const).inter
      (isOpen_lt ((hq.comp hconj).comp continuous_subtype_val) continuous_const)
  have h1 : (1:sharpCollarGroup)∈U := by
    change q 1<1 ∧ q (f*1*f⁻¹)<1
    simp only [mul_one,mul_inv_cancel]
    have hq1 : q 1=0 := by
      dsimp only [q]
      rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.ellipticFree_commutatorTrace_one_right]
      norm_num
    rw [hq1]
    norm_num
  have hU : U={1} := by
    apply subset_antisymm
    · intro g hg
      obtain ⟨A,hA⟩ := sharpCollarGroup_real g.val g.property
      have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=1 := sharpCollar_two_small_traces_identity A
        (hA.symm ▸ g.property) (hA.symm ▸ hg.1) (hA.symm ▸ hg.2)
      exact Set.mem_singleton_iff.mpr (Subtype.ext (hA.symm.trans he))
    · exact Set.singleton_subset_iff.mpr h1
  apply discreteTopology_of_isOpen_singleton_one
  rw [←hU]
  exact ho

theorem sharpCollar_generators_mem : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF∈sharpCollarGroup ∧
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD∈sharpCollarGroup := by
  have hf : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF∈sharpCollarGroup := Subgroup.subset_closure (by simp)
  have hr : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpCollarF*sharpCollarD)∈sharpCollarGroup := Subgroup.subset_closure (by simp)
  have hfo : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF)^2=1 := by
    simpa only [sharpCollarF_order] using pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF)
  refine ⟨hf,?_⟩
  have h := sharpCollarGroup.mul_mem hf hr
  rw [map_mul,←mul_assoc,←pow_two,hfo,one_mul] at h
  exact h

theorem sharpCollarD_hyperbolic : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD) := by
  have ht : 4<(Matrix.trace sharpCollarD.val)^2 := by
    norm_num [sharpCollarD,Matrix.trace_fin_two]
  have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD≠1 := by
    intro he
    have hh := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_sq_of_projection_one sharpCollarD he
    linarith only [hh,ht]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ hn).mpr ht

theorem sharpCollarD_eq_log : sharpCollarD=hLogDilationSL (Real.log 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sharpCollarD,hLogDilationSL,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<2)]

theorem sharpCollarD_axis :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis sharpCollarD sharpCollarD_hyperbolic.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ sharpCollarD_hyperbolic.1.1).mp
        sharpCollarD_hyperbolic)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 := by
  symm
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_unique_invariant sharpCollarD sharpCollarD_hyperbolic.1.1
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ sharpCollarD_hyperbolic.1.1).mp
      sharpCollarD_hyperbolic)
  exact axisSL_image_axis_of_products_zero sharpCollarD (by norm_num [sharpCollarD])
    (by norm_num [sharpCollarD])

/-- Simplicity is proved for every element of the actual whole group. -/
theorem sharpCollarD_simple : IsSimple sharpCollarGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD) := by
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.isSimple_iff_native_axis_stable sharpCollarGroup sharpCollarD
    sharpCollarD_hyperbolic.1.1
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ sharpCollarD_hyperbolic.1.1).mp
      sharpCollarD_hyperbolic)
    sharpCollarGroup_real).mpr
  refine ⟨sharpCollar_generators_mem.2,?_⟩
  rw [sharpCollarD_axis]
  exact sharpCollarGroup_axis_stable

/-- The sharp group acts on the entire actual half-plane and is genuinely discrete. -/
theorem sharpCollarHalfPlaneData : HalfPlaneFuchsianGroup sharpCollarGroup where
  preserves := by
    intro g
    obtain ⟨A,hA⟩ := sharpCollarGroup_real g.val g.property
    rw [←hA]
    exact realSLMobius_image_openHalfPlane A
  discrete := sharpCollarGroup_discrete

/-- The order-three elliptic factor rules out every elementary branch in the actual group. -/
theorem sharpCollarGroup_nonElementary : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary sharpCollarGroup := by
  intro he
  let r:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpCollarF*sharpCollarD)
  have hr : r∈sharpCollarGroup := Subgroup.subset_closure (Or.inr rfl)
  have hro : orderOf r=3 := sharpCollarR_order
  have hrn : r≠1 := by intro h;rw [h,orderOf_one] at hro;omega
  have hrf : IsOfFinOrder r := orderOf_pos_iff.mp (by rw [hro];omega)
  have hrell : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic r := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic r hrn hrf
  have sharpCollarElementaryFinite : Finite sharpCollarGroup := elementary_elliptic_noninvolution_finite
    sharpCollarHalfPlaneData.asFuchsianDisc he r hr hrell (by omega)
  have hdf : IsOfFinOrder (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD) := by
    apply orderOf_pos_iff.mp
    rw [Subgroup.orderOf_coe (⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      sharpCollarD,sharpCollar_generators_mem.2⟩ : sharpCollarGroup)]
    exact (isOfFinOrder_of_finite _).orderOf_pos
  have hde := _root_.LowDimensionalTopology.Geometry.Mobius.mobius_finite_order_elliptic _ sharpCollarD_hyperbolic.1.1 hdf
  have hE := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _ hde.1).mp hde
  have hH := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
    sharpCollarD_hyperbolic.1.1).mp sharpCollarD_hyperbolic
  linarith

theorem sharpCollarF_axis_distinct : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 ≠
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ sharpCollarF) := by
  intro he
  have hp : sharpCollarF • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 1 (by norm_num)∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
    rw [he,_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 1 (by norm_num),rfl,rfl⟩
  change (sharpCollarF • _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 1 (by norm_num)).re=0 at hp
  rw [axisSL_image_re] at hp
  norm_num [sharpCollarF] at hp

/-- The actual hyperbolic generator has genuine half-translation sinh equal to three quarters. -/
theorem sharpCollarD_half_translation :
    Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD)/2)=3/4 := by
  have hc:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translation_abs_trace sharpCollarD sharpCollarD_hyperbolic.1.1
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ sharpCollarD_hyperbolic.1.1).mp
      sharpCollarD_hyperbolic)
  norm_num [sharpCollarD,Matrix.trace_fin_two] at hc
  change 5/4=Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD)/2) at hc
  have hT := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translationLength_pos sharpCollarD sharpCollarD_hyperbolic.1.1
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ sharpCollarD_hyperbolic.1.1).mp
      sharpCollarD_hyperbolic)
  have hs : 0<Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD)/2) :=
    Real.sinh_pos_iff.mpr (half_pos hT)
  nlinarith only [hc,hs,Real.cosh_sq_sub_sinh_sq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD)/2)]

/-- The exact separation of the actual original axis from its actual half-turn translate. -/
theorem sharpCollar_axis_distance_cosh :
    Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ sharpCollarF)))=17/9 := by
  have hno:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.simple_self_axis_noncrossing sharpCollarHalfPlaneData sharpCollarD
    sharpCollarD_hyperbolic.1.1
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ sharpCollarD_hyperbolic.1.1).mp
      sharpCollarD_hyperbolic)
    sharpCollarD_simple
  have hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis sharpCollarD sharpCollarD_hyperbolic.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ sharpCollarD_hyperbolic.1.1).mp
        sharpCollarD_hyperbolic) ≠
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis sharpCollarD sharpCollarD_hyperbolic.1.1
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
          sharpCollarD_hyperbolic.1.1).mp sharpCollarD_hyperbolic)).realGLMap
          (Matrix.SpecialLinearGroup.mapGL ℝ sharpCollarF) := by
    rw [sharpCollarD_axis]
    exact sharpCollarF_axis_distinct
  have hd:=_root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup.noncrossing_axis_image_hDisjoint sharpCollarHalfPlaneData
    sharpCollarD sharpCollarD sharpCollar_generators_mem.2 sharpCollar_generators_mem.2
    sharpCollarD_hyperbolic.1.1 sharpCollarD_hyperbolic.1.1
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ sharpCollarD_hyperbolic.1.1).mp
      sharpCollarD_hyperbolic)
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ sharpCollarD_hyperbolic.1.1).mp
      sharpCollarD_hyperbolic)
    hno sharpCollarF sharpCollar_generators_mem.1 hne
  have hEn := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_nontrivial_conjugation sharpCollarD sharpCollarF sharpCollarD_hyperbolic.1.1
  have hEt : 4<(Matrix.trace (sharpCollarF*sharpCollarD*sharpCollarF⁻¹).val)^2 := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_conjugation]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
      sharpCollarD_hyperbolic.1.1).mp sharpCollarD_hyperbolic
  have hdE : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis (sharpCollarF*sharpCollarD*sharpCollarF⁻¹) hEn hEt) := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation sharpCollarD sharpCollarF
      sharpCollarD_hyperbolic.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ sharpCollarD_hyperbolic.1.1).mp
        sharpCollarD_hyperbolic)]
    simpa only [sharpCollarD_axis] using hd
  have he:=hHyperbolic_axis0_distance_translation_product
    (sharpCollarF*sharpCollarD*sharpCollarF⁻¹) hEn hEt hdE
  have hediag : (sharpCollarF*sharpCollarD*sharpCollarF⁻¹) 0 0-
      (sharpCollarF*sharpCollarD*sharpCollarF⁻¹) 1 1= -(17/6:ℝ) := by
    norm_num [sharpCollarF,sharpCollarD,Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_translationLength_conjugation,sharpCollarD_half_translation,hediag,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation sharpCollarD sharpCollarF sharpCollarD_hyperbolic.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ sharpCollarD_hyperbolic.1.1).mp
        sharpCollarD_hyperbolic),
    sharpCollarD_axis] at he
  norm_num only [abs_neg,abs_of_pos (by norm_num : (0:ℝ)<17/6)] at he
  linarith only [he]

/-- A genuine simple axis in a genuinely discrete non-elementary actual group
attains exactly the one-half collar constant. -/
theorem sharpCollar_exact_bound :
    Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD)/2)*
      Real.sinh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ sharpCollarF))/2)=1/2 := by
  let d := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).realGLMap
      (Matrix.SpecialLinearGroup.mapGL ℝ sharpCollarF))
  have hc : Real.cosh d=17/9 := sharpCollar_axis_distance_cosh
  have hd : 0≤d := _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.lineDist_nonneg _ _
  have hs : 0≤Real.sinh (d/2) := Real.sinh_nonneg_iff.mpr (by linarith only [hd])
  have hc2:=Real.cosh_two_mul (d/2)
  rw [show 2*(d/2)=d by ring] at hc2
  have hid:=Real.cosh_sq_sub_sinh_sq (d/2)
  have hh : Real.sinh (d/2)=2/3 := by nlinarith only [hc,hc2,hid,hs]
  change Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry sharpCollarD)/2)*Real.sinh (d/2)=1/2
  rw [sharpCollarD_half_translation,hh]
  norm_num

/-- The actual source generators are the half-turn and the simple hyperbolic. -/
theorem sharpCollarGroup_generators : sharpCollarGroup=
    Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with hg|hg
    · rw [hg]
      exact Subgroup.subset_closure (by simp)
    · rw [Set.mem_singleton_iff] at hg
      rw [hg,map_mul]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with hg|hg
    · exact hg ▸ sharpCollar_generators_mem.1
    · exact (Set.mem_singleton_iff.mp hg) ▸ sharpCollar_generators_mem.2

/-- The original elliptic generator is a genuine half-turn at the stated physical point. -/
theorem sharpCollarF_at_center : _root_.LowDimensionalTopology.Geometry.Hyperbolic.IsHalfTurnAt sharpCollarF (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (2/3) 1 (by norm_num)) := by
  have he : sharpCollarF=_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (2/3) 1 (by norm_num)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [sharpCollarF,_root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe]
  rw [he]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.pointHalfTurnSL_at _

/-- A second actual hyperbolic generator for the very same original group. -/
def sharpCollarB : Matrix.SpecialLinearGroup (Fin 2) ℝ := sharpCollarF*sharpCollarD^2

theorem sharpCollarB_hyperbolic : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarB) := by
  have ht : Matrix.trace sharpCollarB.val=5/2 := by
    norm_num [sharpCollarB,pow_two,sharpCollarF,sharpCollarD,Matrix.trace_fin_two,
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two]
  have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarB≠1 := by
    intro he
    have hh:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_trace_sq_of_projection_one sharpCollarB he
    rw [ht] at hh
    norm_num at hh
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ hn).mpr (by rw [ht];norm_num)

theorem sharpCollarGroup_hyperbolic_generators : sharpCollarGroup=
    Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarB} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) := by
  let d:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD
  let f:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF
  let b:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarB
  let K:=Subgroup.closure ({d,b}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hbd : b=f*d^2 := by dsimp only [b,f,d,sharpCollarB];rw [map_mul,map_pow]
  have hdK : d∈K := Subgroup.subset_closure (by simp)
  have hbK : b∈K := Subgroup.subset_closure (by simp)
  have hfK : f∈K := by
    have he : f=b*(d^2)⁻¹ := by rw [hbd];group
    rw [he]
    exact K.mul_mem hbK (K.inv_mem (K.pow_mem hdK 2))
  apply le_antisymm
  · rw [sharpCollarGroup_generators]
    exact (Subgroup.closure_le _).mpr (by
      intro g hg
      rcases Set.mem_insert_iff.mp hg with he|he
      · rw [he]
        exact hfK
      · rw [Set.mem_singleton_iff] at he
        rw [he]
        exact hdK)
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with he|he
    · exact he ▸ sharpCollar_generators_mem.2
    · rw [Set.mem_singleton_iff] at he
      rw [he]
      change b∈sharpCollarGroup
      rw [hbd]
      exact sharpCollarGroup.mul_mem sharpCollar_generators_mem.1
        (sharpCollarGroup.pow_mem sharpCollar_generators_mem.2 2)

/-- The same whole group is already generated by the simple hyperbolic and
its actual half-turn conjugate; the half-turn is recovered from the order-three relation. -/
theorem sharpCollarGroup_conjugate_generators : sharpCollarGroup=
    Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpCollarF*sharpCollarD*sharpCollarF⁻¹)} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) := by
  let f:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarF
  let d:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD
  let h:=f*d*f⁻¹
  let K:=Subgroup.closure ({d,h}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hdK : d∈K := Subgroup.subset_closure (by simp)
  have hhK : h∈K := Subgroup.subset_closure (by simp)
  have hfo : f*f=1 := by
    have ho : orderOf f=2 := sharpCollarF_order
    simpa only [ho,pow_two] using pow_orderOf_eq_one f
  have hfi : f⁻¹=f := by
    calc f⁻¹=f⁻¹*(f*f) := by rw [hfo,mul_one]
         _=f := by group
  have hr : (f*d)^3=1 := by
    have ho : orderOf (f*d)=3 := by
      change orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        sharpCollarF*_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius sharpCollarD)=3
      rw [←map_mul]
      exact sharpCollarR_order
    simpa only [ho] using pow_orderOf_eq_one (f*d)
  have hfword : d*h*d=f := by
    dsimp only [h]
    rw [hfi]
    apply mul_left_cancel (a:=f)
    calc f*(d*(f*d*f)*d)=(f*d)^3 := by simp only [pow_succ,pow_zero,one_mul,mul_assoc]
         _=1 := hr
         _=f*f := hfo.symm
  have hfK : f∈K := hfword ▸ K.mul_mem (K.mul_mem hdK hhK) hdK
  rw [map_mul,map_mul,map_inv]
  change sharpCollarGroup=K
  apply le_antisymm
  · rw [sharpCollarGroup_generators]
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with he|he
    · rw [he]
      exact hfK
    · rw [Set.mem_singleton_iff] at he
      rw [he]
      exact hdK
  · apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with he|he
    · rw [he]
      exact sharpCollar_generators_mem.2
    · rw [Set.mem_singleton_iff] at he
      rw [he]
      exact sharpCollarGroup.mul_mem
        (sharpCollarGroup.mul_mem sharpCollar_generators_mem.1 sharpCollar_generators_mem.2)
        (sharpCollarGroup.inv_mem sharpCollar_generators_mem.1)

/-- Best possible in the literal two-hyperbolic-generator hypotheses, with every geometric and group hypothesis actually proved. -/
theorem exists_simple_hyperbolic_halfTurn_axis_image_with_sinh_gap_product_eq_half :
    ∃ H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, HalfPlaneFuchsianGroup H ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H ∧
    ∃ A B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
    ∃ hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1, ∃ htA : 4<(Matrix.trace A.val)^2,
    ∃ F : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      H=Subgroup.closure
        ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set
          _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∧ _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B) ∧
      IsSimple H (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        A) ∧ orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
        F)=2 ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F∈H ∧
      let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hA htA
      L≠L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ F) ∧
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry A)/2)*
          Real.sinh (L.lineDist (L.realGLMap (Matrix.SpecialLinearGroup.mapGL ℝ F))/2)=1/2 := by
  refine ⟨sharpCollarGroup,sharpCollarHalfPlaneData,sharpCollarGroup_nonElementary,
    sharpCollarD,sharpCollarF*sharpCollarD*sharpCollarF⁻¹,sharpCollarD_hyperbolic.1.1,
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
      sharpCollarD_hyperbolic.1.1).mp sharpCollarD_hyperbolic,
    sharpCollarF,sharpCollarGroup_conjugate_generators,sharpCollarD_hyperbolic,
    ?_,sharpCollarD_simple,sharpCollarF_order,sharpCollar_generators_mem.1,?_,?_⟩
  · rw [map_mul,map_mul,map_inv]
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward _ _ sharpCollarD_hyperbolic
  · simpa only [sharpCollarD_axis] using sharpCollarF_axis_distinct
  · simpa only [sharpCollarD_axis] using sharpCollar_exact_bound

end LowDimensionalTopology.Geometry.Fuchsian
