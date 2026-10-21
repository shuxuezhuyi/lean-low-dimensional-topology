/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.FuchsianDisplacementInvariants
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.OneIdealTriangleDiscreteness
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Parabolic.NonTriangleSharpness
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.Displacement.EllipticMinimizers
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.Hecke.HeckeDisplacementSharpness
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.WeakDisplacementGap
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleAxisExample
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.PureHyperbolicSharpness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped UpperHalfPlane OnePoint Pointwise MatrixGroups ComplexConjugate
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

local instance sharpEllipticEvaluationAction {X : Type*} [MetricSpace X] : MulAction (X≃ᵢX) X where
  smul g x:=g x
  one_smul _:=rfl
  mul_smul _ _ _:=rfl

def sharpEllipticCos (n : ℕ) : ℝ := Real.cos (Real.pi/(n:ℝ))
def sharpEllipticSin (n : ℕ) : ℝ := Real.sin (Real.pi/(n:ℝ))

theorem sharpElliptic_angle (n : ℕ) (hn : 2≤n) :
    0<Real.pi/(n:ℝ) ∧ Real.pi/(n:ℝ)≤Real.pi/2 := by
  have hnR : (2:ℝ)≤n:=by exact_mod_cast hn
  have hn0 : 0<(n:ℝ):=by linarith
  constructor
  · exact div_pos Real.pi_pos hn0
  · apply (div_le_iff₀ hn0).mpr
    nlinarith [Real.pi_pos]

theorem sharpEllipticSin_pos (n : ℕ) (hn : 2≤n) : 0<sharpEllipticSin n :=
  Real.sin_pos_of_pos_of_lt_pi (sharpElliptic_angle n hn).1
    ((sharpElliptic_angle n hn).2.trans_lt (by linarith [Real.pi_pos]))

theorem sharpEllipticCos_nonneg (n : ℕ) (hn : 2≤n) : 0 ≤ sharpEllipticCos n :=
  Real.cos_nonneg_of_mem_Icc ⟨by linarith [(sharpElliptic_angle n hn).1,Real.pi_pos],
    (sharpElliptic_angle n hn).2⟩

theorem sharpEllipticCos_pos (n : ℕ) (hn : 3≤n) : 0<sharpEllipticCos n := by
  exact heckeCorner_re_pos n hn

theorem sharpElliptic_trig (n : ℕ) : (sharpEllipticSin n)^2+(sharpEllipticCos n)^2=1 :=
  Real.sin_sq_add_cos_sq _

theorem sharpEllipticCornerSL_two : standardHeckeCornerSL 2=modularInversionSL := by
  ext i j
  fin_cases i <;>fin_cases j <;>
    norm_num [standardHeckeCornerSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,Matrix.mul_apply,Fin.sum_univ_two]

theorem sharpEllipticCorner_native_order (n : ℕ) (hn : 2≤n) :
    orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL n))=n := by
  by_cases he : n=2
  · subst n
    rw [sharpEllipticCornerSL_two]
    exact modularInversionSL_order_two
  · exact standardHeckeCornerSL_order n (by omega)

theorem sharpEllipticCorner_order (n : ℕ) (hn : 2≤n) :
    orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (standardHeckeCornerSL n))=n := by
  rw [realSLMobius_order_eq_native]
  exact sharpEllipticCorner_native_order n hn

theorem sharpEllipticCorner_trace (n : ℕ) :
    Matrix.trace (standardHeckeCornerSL n).val=2*sharpEllipticCos n := by
  norm_num [standardHeckeCornerSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,sharpEllipticCos,
    Matrix.trace_fin_two,Matrix.mul_apply,Fin.sum_univ_two]

theorem sharpEllipticCorner_elliptic (n : ℕ) (hn : 2≤n) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (standardHeckeCornerSL n)) := by
  have hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (standardHeckeCornerSL n)≠1:=by
    intro he
    have ho:=sharpEllipticCorner_order n hn
    rw [he,orderOf_one] at ho
    omega
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _ hne).mpr
  rw [sharpEllipticCorner_trace]
  nlinarith [sharpElliptic_trig n,sq_pos_of_pos (sharpEllipticSin_pos n hn)]

/-- The actual cyclic fundamental sector, including the genuine half-plane when n=2. -/
def sharpEllipticSector (n : ℕ) : Set ℍ :=
  {z|z.re<sharpEllipticCos n ∧ z.re<sharpEllipticCos n*Complex.normSq (z:ℂ)}

theorem sharpEllipticSector_eq_hecke (n : ℕ) (hn : 3≤n) :
    sharpEllipticSector n=heckePingPongSector n hn := by
  ext z
  rw [heckePingPongSector_mem_iff]
  rfl

theorem sharpEllipticSector_isOpen (n : ℕ) : IsOpen (sharpEllipticSector n) :=
  (isOpen_lt UpperHalfPlane.continuous_re continuous_const).inter
    (isOpen_lt UpperHalfPlane.continuous_re
      (continuous_const.mul (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)))

theorem sharpEllipticSector_contains_negative (n : ℕ) (hn : 2≤n) (z : ℍ) (hz : z.re<0) :
    z∈sharpEllipticSector n := by
  have hc:=sharpEllipticCos_nonneg n hn
  exact ⟨hz.trans_le hc,hz.trans_le (mul_nonneg hc (Complex.normSq_nonneg (z:ℂ)))⟩

theorem sharpEllipticSector_packing (n : ℕ) (hn : 2≤n)
    (g : ℍ≃ᵢℍ) (hg : g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      (standardHeckeCornerSL n))) (hne : g≠1) :
    Disjoint (g • sharpEllipticSector n) (sharpEllipticSector n) := by
  by_cases he : n=2
  · subst n
    rw [sharpEllipticCornerSL_two] at hg
    have hgS:=modularInversion_zpowers_nonidentity g hg hne
    subst g
    apply disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ hz
    have hxneg : x.re<0:=by simpa [sharpEllipticSector,sharpEllipticCos] using hx.1
    have hzneg:=hz.1
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL •
      x).re<sharpEllipticCos 2 at hzneg
    norm_num only [sharpEllipticCos,Nat.cast_ofNat,Real.cos_pi_div_two] at hzneg
    change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL x).re<0 at hzneg
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_apply] at hzneg
    have heq : (modularInversionSL • x).re= -x.re/Complex.normSq (x:ℂ):=by
      change (((modularInversionSL • x:ℍ):ℂ)).re=_
      rw [modularInversionSL_action_coe]
      simp [Complex.div_re]
    rw [heq] at hzneg
    exact (not_lt_of_ge (div_nonneg (by linarith) (Complex.normSq_nonneg _))) hzneg
  · rw [sharpEllipticSector_eq_hecke n (by omega)]
    exact heckePingPongSector_disjoint_translate n (by omega) g hg hne


def sharpEllipticMirror (t : ℝ) : ℍ≃ᵢℍ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-t))*idealTriangleAxisMirror

theorem sharpEllipticMirror_coe (t : ℝ) (z : ℍ) :
    (sharpEllipticMirror t z:ℂ)= -conj (z:ℂ)-(t:ℂ) := by
  change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-t) • idealTriangleAxisMirror z:ℍ):ℂ)=_
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe,idealTriangleAxisMirror_coe]
  simp only [Complex.ofReal_neg,sub_eq_add_neg]

theorem sharpEllipticMirror_re (t : ℝ) (z : ℍ) :
    (sharpEllipticMirror t z).re= -t-z.re := by
  have h:=congrArg Complex.re (sharpEllipticMirror_coe t z)
  simp only [Complex.sub_re,Complex.neg_re,Complex.conj_re,Complex.ofReal_re,
    UpperHalfPlane.coe_re] at h
  linarith


theorem sharpEllipticMirror_involutive (t : ℝ) (z : ℍ) :
    sharpEllipticMirror t (sharpEllipticMirror t z)=z := by
  apply UpperHalfPlane.ext
  rw [sharpEllipticMirror_coe,sharpEllipticMirror_coe]
  simp

theorem sharpEllipticMirror_inv (t : ℝ) : (sharpEllipticMirror t)⁻¹=sharpEllipticMirror t := by
  have hsq : sharpEllipticMirror t*sharpEllipticMirror t=1:=by
    apply IsometryEquiv.ext
    exact sharpEllipticMirror_involutive t
  calc
    (sharpEllipticMirror t)⁻¹=(sharpEllipticMirror t)⁻¹*1:=by simp
    _=(sharpEllipticMirror t)⁻¹*(sharpEllipticMirror t*sharpEllipticMirror t):=by rw [hsq]
    _=sharpEllipticMirror t:=by group

def sharpEllipticLeftConjugation (t : ℝ) : (ℍ≃ᵢℍ)→*(ℍ≃ᵢℍ) :=
  (MulAut.conj (sharpEllipticMirror t)).toMonoidHom

def sharpEllipticLeftCyclic (p : ℕ) (t : ℝ) : Subgroup (ℍ≃ᵢℍ) :=
  (Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL
    p))).map (sharpEllipticLeftConjugation t)

def sharpEllipticRightCyclic (q : ℕ) : Subgroup (ℍ≃ᵢℍ) :=
  Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL q))

def sharpEllipticLeftSector (p : ℕ) (t : ℝ) : Set ℍ :=
  sharpEllipticMirror t ⁻¹' sharpEllipticSector p

def sharpEllipticNativeGroup (p q : ℕ) (t : ℝ) : Subgroup (ℍ≃ᵢℍ) :=
  sharpEllipticLeftCyclic p t⊔sharpEllipticRightCyclic q

def sharpEllipticNativeGap (p q : ℕ) (t : ℝ) : Set ℍ :=
  sharpEllipticLeftSector p t∩sharpEllipticSector q

theorem sharpEllipticLeftSector_packing (p : ℕ) (hp : 2≤p) (t : ℝ)
    (g : ℍ≃ᵢℍ) (hg : g∈sharpEllipticLeftCyclic p t) (hne : g≠1) :
    Disjoint (g • sharpEllipticLeftSector p t) (sharpEllipticLeftSector p t) := by
  obtain ⟨a,ha,he⟩:=hg
  have ha1 : a≠1:=by
    intro h
    rw [h,map_one] at he
    exact hne he.symm
  have hdis:=sharpEllipticSector_packing p hp a ha ha1
  apply disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ hz
  apply disjoint_left.mp hdis
  · refine ⟨sharpEllipticMirror t x,hx,?_⟩
    change a (sharpEllipticMirror t x)=sharpEllipticMirror t (g x)
    rw [←he]
    change _=sharpEllipticMirror t (sharpEllipticMirror t (a ((sharpEllipticMirror t)⁻¹ x)))
    rw [sharpEllipticMirror_involutive,sharpEllipticMirror_inv]
  · exact hz

theorem sharpElliptic_sectors_cover (p q : ℕ) (hp : 2≤p) (hq : 2≤q) (t : ℝ) (ht : 0<t) :
    sharpEllipticLeftSector p t∪sharpEllipticSector q=univ := by
  apply eq_univ_of_forall
  intro z
  by_cases hx : z.re<0
  · exact Or.inr (sharpEllipticSector_contains_negative q hq z hx)
  · apply Or.inl
    apply sharpEllipticSector_contains_negative p hp
    rw [sharpEllipticMirror_re]
    linarith [not_lt.mp hx]

theorem sharpEllipticNativeGap_isOpen (p q : ℕ) (t : ℝ) :
    IsOpen (sharpEllipticNativeGap p q t) :=
  ((sharpEllipticSector_isOpen p).preimage (sharpEllipticMirror t).continuous).inter
    (sharpEllipticSector_isOpen q)

theorem sharpEllipticNativeGap_strip (p q : ℕ) (hp : 2≤p) (hq : 2≤q) (t : ℝ)
    (z : ℍ) (hz : -t<z.re ∧ z.re<0) : z∈sharpEllipticNativeGap p q t := by
  constructor
  · apply sharpEllipticSector_contains_negative p hp
    rw [sharpEllipticMirror_re]
    linarith [hz.1]
  · exact sharpEllipticSector_contains_negative q hq z hz.2

theorem sharpEllipticNativeGap_nonempty (p q : ℕ) (hp : 2≤p) (hq : 2≤q) (t : ℝ) (ht : 0<t) :
    (sharpEllipticNativeGap p q t).Nonempty := by
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-t/2) 1 (by norm_num),sharpEllipticNativeGap_strip p q hp hq t _ ?_⟩
  change -t< -t/2 ∧ -t/2<0
  constructor <;> linarith

theorem sharpEllipticNativeGap_wandering (p q : ℕ) (hp : 2≤p) (hq : 2≤q) (t : ℝ) (ht : 0<t)
    (g : ℍ≃ᵢℍ) (hg : g∈sharpEllipticNativeGroup p q t) (hne : g≠1) :
    Disjoint (g • sharpEllipticNativeGap p q t) (sharpEllipticNativeGap p q t) :=
  two_packing_domains_wandering (sharpEllipticLeftCyclic p t) (sharpEllipticRightCyclic q)
    (sharpEllipticLeftSector p t) (sharpEllipticSector q)
    (sharpEllipticLeftSector_packing p hp t) (sharpEllipticSector_packing q hq)
    (sharpElliptic_sectors_cover p q hp hq t ht) g hg hne

theorem sharpEllipticNativeGroup_discrete (p q : ℕ) (hp : 2≤p) (hq : 2≤q) (t : ℝ) (ht : 0<t) :
    DiscreteTopology (sharpEllipticNativeGroup p q t) := by
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteTopology_of_wandering_open (sharpEllipticNativeGap
    p q t)
    (sharpEllipticNativeGap_isOpen p q t) (sharpEllipticNativeGap_nonempty p q hp hq t ht)
  intro g hne
  apply sharpEllipticNativeGap_wandering p q hp hq t ht g.val g.property
  intro he
  exact hne (Subtype.ext he)

def sharpEllipticLeftSL (p : ℕ) (t : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-t)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-2*sharpEllipticCos p)*modularInversionSL)*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t

theorem sharpElliptic_translation_inv (t : ℝ) : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-t))⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL t := by
  apply inv_eq_of_mul_eq_one_right
  ext i j
  fin_cases i <;>fin_cases j <;>
    simp [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,Matrix.mul_apply,Fin.sum_univ_two]

theorem sharpEllipticLeftConjugation_corner (p : ℕ) (t : ℝ) :
    sharpEllipticLeftConjugation t (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL
      p))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpEllipticLeftSL p t) := by
  change sharpEllipticMirror t*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL
    p)*(sharpEllipticMirror t)⁻¹=_
  have he : sharpEllipticMirror t*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL
    p)*(sharpEllipticMirror t)⁻¹=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-t))*
        (idealTriangleAxisMirror*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL
          p)*idealTriangleAxisMirror⁻¹)*
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-t)))⁻¹:=by
    dsimp [sharpEllipticMirror]
    group
  rw [he]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-t))*
    idealTriangleLeftConjugation (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL
      p))*
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-t)))⁻¹=_
  rw [idealTriangleLeftConjugation_corner]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-t))*
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-2*sharpEllipticCos p)*modularInversionSL)*
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-t)))⁻¹=_
  rw [←map_inv,sharpElliptic_translation_inv,←map_mul,←map_mul]
  rfl

theorem sharpEllipticNativeGroup_generators (p q : ℕ) (t : ℝ) :
    sharpEllipticNativeGroup p q t=Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpEllipticLeftSL p t),_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL q)}:Set (ℍ≃ᵢℍ)) := by
  let K:=Subgroup.closure
    ({
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpEllipticLeftSL p t),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL q)}:Set (ℍ≃ᵢℍ))
  have hA : sharpEllipticLeftCyclic p t≤K:=by
    rintro g ⟨a,ha,rfl⟩
    obtain ⟨k,rfl⟩:=Subgroup.mem_zpowers_iff.mp ha
    rw [map_zpow,sharpEllipticLeftConjugation_corner]
    exact K.zpow_mem (Subgroup.subset_closure (by left;rfl)) k
  have hB : sharpEllipticRightCyclic q≤K:=Subgroup.zpowers_le.mpr
    (Subgroup.subset_closure (by right;rfl))
  apply le_antisymm (sup_le hA hB)
  apply (Subgroup.closure_le _).mpr
  rintro g (rfl|rfl)
  · apply (show sharpEllipticLeftCyclic p t≤ sharpEllipticNativeGroup p q t from le_sup_left)
    exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL p),Subgroup.mem_zpowers
      _,
      sharpEllipticLeftConjugation_corner p t⟩
  · exact (show sharpEllipticRightCyclic q≤ sharpEllipticNativeGroup p q t from le_sup_right)
      (Subgroup.mem_zpowers _)

theorem sharpEllipticNativeGroup_conformal (p q : ℕ) (t : ℝ) :
    sharpEllipticNativeGroup p q t≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  rw [sharpEllipticNativeGroup_generators]
  apply (Subgroup.closure_le _).mpr
  rintro g (rfl|rfl)
  · exact ⟨_,rfl⟩
  · exact ⟨_,rfl⟩

def sharpEllipticMobiusGroup (p q : ℕ) (t :
  ℝ) : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  (nativeConformalSubgroupMobiusHom (sharpEllipticNativeGroup p q t)
    (sharpEllipticNativeGroup_conformal p q t)).range

theorem sharpEllipticMobiusData (p q : ℕ) (hp : 2≤p) (hq : 2≤q) (t : ℝ) (ht : 0<t) :
    HalfPlaneFuchsianGroup (sharpEllipticMobiusGroup p q t) := by
  let : DiscreteTopology (sharpEllipticNativeGroup p q t):=sharpEllipticNativeGroup_discrete p q hp hq t ht
  exact nativeConformalSubgroup_halfPlaneData _ _

theorem sharpEllipticMobiusGroup_generators (p q : ℕ) (t : ℝ) :
    sharpEllipticMobiusGroup p q t=Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpEllipticLeftSL p t),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (standardHeckeCornerSL q)}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) := by
  let N:=sharpEllipticNativeGroup p q t
  let M:=nativeConformalSubgroupMobiusHom N (sharpEllipticNativeGroup_conformal p q t)
  have hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpEllipticLeftSL p t)∈N:=by
    rw [show N=Subgroup.closure _ from sharpEllipticNativeGroup_generators p q t]
    exact Subgroup.subset_closure (by left;rfl)
  have hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL q)∈N:=by
    rw [show N=Subgroup.closure _ from sharpEllipticNativeGroup_generators p q t]
    exact Subgroup.subset_closure (by right;rfl)
  have hMA : M ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpEllipticLeftSL p
    t),hA⟩=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpEllipticLeftSL p t):=
    nativeConformalSubgroupMobiusHom_matrix _ _ _ _
  have hMB : M ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL
    q),hB⟩=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (standardHeckeCornerSL q):=
    nativeConformalSubgroupMobiusHom_matrix _ _ _ _
  apply le_antisymm
  · rintro g ⟨f,rfl⟩
    have hf : f.val∈Subgroup.closure
        ({
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpEllipticLeftSL p t),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL q)}:Set (ℍ≃ᵢℍ)):=
      (sharpEllipticNativeGroup_generators p q t) ▸ f.property
    have hi : ∀g (hg:g∈Subgroup.closure
        ({
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpEllipticLeftSL p t),
          _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL q)}:Set (ℍ≃ᵢℍ))),
        M ⟨g,by change g∈sharpEllipticNativeGroup p q t;rw [sharpEllipticNativeGroup_generators];exact hg⟩∈
          Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpEllipticLeftSL p t),_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (standardHeckeCornerSL q)}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        rcases hx with rfl|rfl
        · rw [hMA];exact Subgroup.subset_closure (by left;rfl)
        · rw [hMB];exact Subgroup.subset_closure (by right;rfl)
      | one => exact (map_one M) ▸ Subgroup.one_mem _
      | mul a b ha hb iha ihb =>
        have haN : a∈N:=by change a∈sharpEllipticNativeGroup p q t;rw [sharpEllipticNativeGroup_generators];exact ha
        have hbN : b∈N:=by change b∈sharpEllipticNativeGroup p q t;rw [sharpEllipticNativeGroup_generators];exact hb
        change M ((⟨a,haN⟩:N)*⟨b,hbN⟩)∈_
        rw [map_mul]
        exact Subgroup.mul_mem _ iha ihb
      | inv a ha iha =>
        have haN : a∈N:=by change a∈sharpEllipticNativeGroup p q t;rw [sharpEllipticNativeGroup_generators];exact ha
        change M (⟨a,haN⟩:N)⁻¹∈_
        rw [map_inv]
        exact Subgroup.inv_mem _ iha
    exact hi f.val hf
  · apply (Subgroup.closure_le _).mpr
    rintro g (rfl|rfl)
    · exact ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (sharpEllipticLeftSL p t),hA⟩,hMA⟩
    · exact ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL q),hB⟩,hMB⟩

/-- A genuine open sphere gap whose native trace wanders cannot contain
any true hyperbolic endpoint of the original half-plane group. -/
theorem halfPlane_native_wandering_gap_ordinary {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : HalfPlaneFuchsianGroup H) (U : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hU : IsOpen
      U)
    (hpack : letI:=P.nativeAction
      ∀g : H,g≠1→Disjoint (g • (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹'
        U)) (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' U)) :
    U⊆_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet H := by
  let :=P.nativeAction
  have hsub : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLoxodromicFixedPointSet H⊆Uᶜ:=by
    rintro x ⟨g,hg,hfix⟩ hxU
    change g.val.val x=x at hfix
    have hxF:=_root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_fixed_mem_disc_frontier g.val
      (P.asFuchsianDisc.loxodromic_hyperbolic g hg) P.asFuchsianDisc.isDisc
        (P.asFuchsianDisc.image_eq g) hfix
    have hxC : x∈closure _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=frontier_subset_closure hxF
    have hW : IsOpen (U∩g.val.val ⁻¹' U):=hU.inter (hU.preimage
      (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph g.val).continuous)
    have hxpre : x∈g.val.val ⁻¹' U:=by
      change g.val.val x∈U
      rw [hfix]
      exact hxU
    obtain ⟨y,hyW,hyH⟩:=mem_closure_iff.mp hxC (U∩g.val.val ⁻¹' U) hW ⟨hxU,hxpre⟩
    have hyr : y∈Set.range _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint:=by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneBoundaryPoint_range]
    obtain ⟨z,rfl⟩:=hyr
    have hz : z∈_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' U:=hyW.1
    have hgz : g • z∈_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' U:=by
      change _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint (g • z)∈U
      rw [←P.nativeAction_boundary]
      exact hyW.2
    exact disjoint_left.mp (hpack g (fun he=>hg.1 (congrArg Subtype.val he))) ⟨z,hz,rfl⟩ hgz
  have hcl : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusLimitSet H⊆Uᶜ:=closure_minimal hsub hU.isClosed_compl
  intro x hx hlim
  exact hcl hlim hx

def sharpEllipticPlaneSector (n : ℕ) : Set ℂ :=
  {z|z.re<sharpEllipticCos n ∧ z.re<sharpEllipticCos n*Complex.normSq z}

def sharpEllipticPlaneMirror (t : ℝ) (z : ℂ) : ℂ := -conj z-(t:ℂ)

def sharpEllipticPlaneGap (p q : ℕ) (t : ℝ) : Set ℂ :=
  sharpEllipticPlaneMirror t ⁻¹' sharpEllipticPlaneSector p∩sharpEllipticPlaneSector q

def sharpEllipticSphereGap (p q : ℕ) (t : ℝ) : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  ((↑):ℂ→_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) '' sharpEllipticPlaneGap p q t

theorem sharpEllipticPlaneSector_isOpen (n : ℕ) : IsOpen (sharpEllipticPlaneSector n) :=
  (isOpen_lt Complex.continuous_re continuous_const).inter
    (isOpen_lt Complex.continuous_re (continuous_const.mul Complex.continuous_normSq))

theorem sharpEllipticPlaneGap_isOpen (p q : ℕ) (t : ℝ) : IsOpen (sharpEllipticPlaneGap p q t) :=
  ((sharpEllipticPlaneSector_isOpen p).preimage (by unfold sharpEllipticPlaneMirror;fun_prop)).inter
    (sharpEllipticPlaneSector_isOpen q)

theorem sharpEllipticSphereGap_isOpen (p q : ℕ) (t : ℝ) : IsOpen (sharpEllipticSphereGap p q t) :=
  OnePoint.isOpenEmbedding_coe.isOpenMap _ (sharpEllipticPlaneGap_isOpen p q t)

theorem sharpEllipticSphereGap_mem (p q : ℕ) (t : ℝ) (z : ℂ) :
    (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈sharpEllipticSphereGap p q t ↔ z∈sharpEllipticPlaneGap p q t := by
  constructor
  · rintro ⟨w,hw,he⟩
    exact (OnePoint.coe_injective he) ▸ hw
  · intro hz
    exact ⟨z,hz,rfl⟩

theorem sharpEllipticSphereGap_native_trace (p q : ℕ) (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' sharpEllipticSphereGap p q t=sharpEllipticNativeGap p q t := by
  ext z
  change ((z:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈sharpEllipticSphereGap p q t ↔ _
  rw [sharpEllipticSphereGap_mem]
  change sharpEllipticPlaneMirror t (z:ℂ)∈sharpEllipticPlaneSector p ∧
    (z:ℂ)∈sharpEllipticPlaneSector q ↔ _
  rw [show sharpEllipticPlaneMirror t (z:ℂ)=(sharpEllipticMirror t z:ℂ) from
    (sharpEllipticMirror_coe t z).symm]
  rfl

theorem sharpEllipticSphereGap_real_midpoint (p q : ℕ) (hp : 2≤p) (hq : 2≤q) (t : ℝ) (ht : 0<t) :
    (((-t/2:ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈sharpEllipticSphereGap p q t := by
  rw [sharpEllipticSphereGap_mem]
  have hm : sharpEllipticPlaneMirror t ((-t/2:ℝ):ℂ)=((-t/2:ℝ):ℂ):=by
    rw [sharpEllipticPlaneMirror,Complex.conj_ofReal]
    push_cast
    ring
  have hc₁:=sharpEllipticCos_nonneg p hp
  have hc₂:=sharpEllipticCos_nonneg q hq
  change sharpEllipticPlaneMirror t ((-t/2:ℝ):ℂ)∈sharpEllipticPlaneSector p ∧
    ((-t/2:ℝ):ℂ)∈sharpEllipticPlaneSector q
  rw [hm]
  constructor <;> constructor
  all_goals change -t/2<_
  · linarith
  · exact (by linarith : -t/2<0).trans_le (mul_nonneg hc₁ (Complex.normSq_nonneg _))
  · linarith
  · exact (by linarith : -t/2<0).trans_le (mul_nonneg hc₂ (Complex.normSq_nonneg _))

theorem sharpEllipticSphereGap_ordinary (p q : ℕ) (hp : 2≤p) (hq : 2≤q) (t : ℝ) (ht : 0<t) :
    sharpEllipticSphereGap p q t⊆_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusOrdinarySet (sharpEllipticMobiusGroup p q t) := by
  let P:=sharpEllipticMobiusData p q hp hq t ht
  let N:=sharpEllipticNativeGroup p q t
  let M:=nativeConformalSubgroupMobiusHom N (sharpEllipticNativeGroup_conformal p q t)
  let :=P.nativeAction
  apply halfPlane_native_wandering_gap_ordinary P _ (sharpEllipticSphereGap_isOpen p q t)
  change ∀g : sharpEllipticMobiusGroup p q t,g≠1→
    Disjoint (g • (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' sharpEllipticSphereGap p q
      t))
      (_root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint ⁻¹' sharpEllipticSphereGap p q t)
  intro g hg
  obtain ⟨f,hf⟩:=g.property
  have hfne : f.val≠1:=by
    intro h
    have hf1 : f=1:=Subtype.ext h
    apply hg
    apply Subtype.ext
    rw [←hf,hf1,map_one]
    rfl
  have he (z : ℍ) : g • z=f.val z:=by
    apply _root_.LowDimensionalTopology.Geometry.Mobius.halfPlaneBoundaryPoint_injective
    rw [←P.nativeAction_boundary,←hf]
    exact nativeConformalSubgroupMobiusHom_action N (sharpEllipticNativeGroup_conformal p q t) f z
  rw [sharpEllipticSphereGap_native_trace]
  have hset : g • sharpEllipticNativeGap p q t=f.val '' sharpEllipticNativeGap p q t:=by
    apply image_congr
    intro z _
    exact he z
  rw [hset]
  exact sharpEllipticNativeGap_wandering p q hp hq t ht f.val f.property hfne

theorem sharpEllipticLeft_order (p : ℕ) (hp : 2≤p) (t : ℝ) :
    orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpEllipticLeftSL p t))=p := by
  rw [realSLMobius_order_eq_native,←sharpEllipticLeftConjugation_corner]
  exact ((MulAut.conj (sharpEllipticMirror t)).orderOf_eq _).trans
    (sharpEllipticCorner_native_order p hp)

theorem sharpEllipticLeft_trace (p : ℕ) (t : ℝ) :
    Matrix.trace (sharpEllipticLeftSL p t).val= -2*sharpEllipticCos p := by
  norm_num [sharpEllipticLeftSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,Matrix.trace_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two]

theorem sharpEllipticLeft_elliptic (p : ℕ) (hp : 2≤p) (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpEllipticLeftSL p t)) := by
  have hn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpEllipticLeftSL p t)≠1:=by
    intro h
    have ho:=sharpEllipticLeft_order p hp t
    rw [h,orderOf_one] at ho
    omega
  apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _ hn).mpr
  rw [sharpEllipticLeft_trace]
  nlinarith [sharpElliptic_trig p,sq_pos_of_pos (sharpEllipticSin_pos p hp)]

theorem sharpEllipticLeft_mem (p q : ℕ) (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (sharpEllipticLeftSL p t)∈sharpEllipticMobiusGroup p q t := by
  rw [sharpEllipticMobiusGroup_generators]
  exact Subgroup.subset_closure (by left;rfl)

theorem sharpEllipticRight_mem (p q : ℕ) (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (standardHeckeCornerSL q)∈sharpEllipticMobiusGroup p q t := by
  rw [sharpEllipticMobiusGroup_generators]
  exact Subgroup.subset_closure (by right;rfl)

theorem sharpEllipticProduct_trace (p q : ℕ) (t : ℝ) :
    Matrix.trace ((sharpEllipticLeftSL p t)⁻¹*standardHeckeCornerSL q).val=
      2+2*(sharpEllipticCos p+sharpEllipticCos q)*t+t^2 := by
  norm_num [sharpEllipticLeftSL,standardHeckeCornerSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,modularInversionSL,
    Matrix.SpecialLinearGroup.coe_inv,Matrix.adjugate_fin_two,Matrix.trace_fin_two,
    Matrix.mul_apply,Fin.sum_univ_two,sharpEllipticCos]
  ring

theorem sharpEllipticProduct_hyperbolic (p q : ℕ) (hp : 2≤p) (hq : 2≤q) (t : ℝ) (ht : 0<t) :
    _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius ((sharpEllipticLeftSL p t)⁻¹*standardHeckeCornerSL q)) := by
  have hpq : 0≤2*(sharpEllipticCos p+sharpEllipticCos q)*t:=by
    exact mul_nonneg (mul_nonneg (by norm_num)
      (add_nonneg (sharpEllipticCos_nonneg p hp) (sharpEllipticCos_nonneg q hq))) ht.le
  have htr : 2<Matrix.trace ((sharpEllipticLeftSL p t)⁻¹*standardHeckeCornerSL q).val:=by
    rw [sharpEllipticProduct_trace]
    nlinarith [sq_pos_of_pos ht]
  have hsq : 4<(Matrix.trace ((sharpEllipticLeftSL p t)⁻¹*standardHeckeCornerSL q).val)^2:=by
    nlinarith
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
    (realSLMobius_ne_one_of_trace_sq_gt_four _ hsq)).mpr hsq

theorem sharpEllipticMobiusGroup_nonElementary (p q : ℕ) (hp : 2≤p) (hq : 2≤q)
    (hpq : p≠2 ∨ q≠2) (t : ℝ) (ht : 0<t) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (sharpEllipticMobiusGroup p q t) := by
  let H:=sharpEllipticMobiusGroup p q t
  let P:=sharpEllipticMobiusData p q hp hq t ht
  have hprod : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius ((sharpEllipticLeftSL p t)⁻¹*standardHeckeCornerSL q)∈H:=by
    rw [map_mul,map_inv]
    exact H.mul_mem (H.inv_mem (sharpEllipticLeft_mem p q t)) (sharpEllipticRight_mem p q t)
  intro hE
  have hfin : Finite H:=by
    rcases hpq with hp'|hq'
    · exact elementary_elliptic_noninvolution_finite P.asFuchsianDisc hE _
        (sharpEllipticLeft_mem p q t) (sharpEllipticLeft_elliptic p hp t)
        (by rw [sharpEllipticLeft_order p hp t];exact hp')
    · exact elementary_elliptic_noninvolution_finite P.asFuchsianDisc hE _
        (sharpEllipticRight_mem p q t) (sharpEllipticCorner_elliptic q hq)
        (by rw [sharpEllipticCorner_order q hq];exact hq')
  let :=hfin
  have ho : IsOfFinOrder (⟨_,hprod⟩:H):=isOfFinOrder_of_finite _
  obtain ⟨n,hn,he⟩:=ho.exists_pow_eq_one
  have ho' : IsOfFinOrder (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius ((sharpEllipticLeftSL p
    t)⁻¹*standardHeckeCornerSL q)):=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,congrArg Subtype.val he⟩
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_parabolic_or_loxodromic_not_isOfFinOrder _
    (Or.inr (sharpEllipticProduct_hyperbolic p q hp hq t ht).1) ho'

theorem sharpEllipticMobiusGroup_secondKind (p q : ℕ) (hp : 2≤p) (hq : 2≤q)
    (hpq : p≠2 ∨ q≠2) (t : ℝ) (ht : 0<t) :
    (sharpEllipticMobiusData p q hp hq t ht).asFuchsianDisc.IsSecondKind := by
  let P:=sharpEllipticMobiusData p q hp hq t ht
  have hx:=sharpEllipticSphereGap_ordinary p q hp hq t ht
    (sharpEllipticSphereGap_real_midpoint p q hp hq t ht)
  refine ⟨P.asFuchsianDisc.limitSet_subset_frontier,?_⟩
  intro hfull
  have hfront : (((-t/2:ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈frontier _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet:=by
    rw [nielsen_openHalfPlane_frontier,_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_halfPlaneIdealBoundary]
    simp
  have hlim:=hfull hfront
  rw [fuchsianLimitSet_eq_nonElementary _ (sharpEllipticMobiusGroup_nonElementary p q hp hq hpq t ht)] at hlim
  exact hx hlim

theorem sharpEllipticMobiusGroup_not_triangle (p q : ℕ) (hp : 2≤p) (hq : 2≤q)
    (hpq : p≠2 ∨ q≠2) (t : ℝ) (ht : 0<t) :
    ¬IsMobiusTriangleGroup (sharpEllipticMobiusGroup p q t) :=
  secondKind_not_mobiusTriangleGroup (sharpEllipticMobiusData p q hp hq t ht).asFuchsianDisc
    (sharpEllipticMobiusGroup_nonElementary p q hp hq hpq t ht)
    (sharpEllipticMobiusGroup_secondKind p q hp hq hpq t ht)

end LowDimensionalTopology.Geometry.Fuchsian
