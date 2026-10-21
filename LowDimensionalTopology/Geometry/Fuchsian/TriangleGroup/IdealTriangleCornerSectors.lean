/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.IdealTriangleDirichletGeometry
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.NativeTriangleProperness
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane Pointwise ComplexConjugate
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

/-- The genuine right corner transformation for any source angle, including zero. -/
def idealCornerSL (θ : ℝ) : Matrix.SpecialLinearGroup (Fin 2) ℝ:=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (2*Real.cos θ)*modularInversionSL

/-- The open sector between the actual tangent circle and vertical line. -/
def idealCornerSector (θ : ℝ) : Set ℍ:=
  {z | z.re<Real.cos θ ∧ z.re<Real.cos θ*Complex.normSq (z:ℂ)}

/-- At a zero angle a genuine finite cusp chart turns the sector into a unit-width strip. -/
def idealParabolicNormalizerSL : Matrix.SpecialLinearGroup (Fin 2) ℝ:=
  modularInversionSL*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)

theorem idealParabolicNormalizer_coe (z : ℍ) :
    ((idealParabolicNormalizerSL • z:ℍ):ℂ)= -1/((z:ℂ)-1) := by
  rw [idealParabolicNormalizerSL,mul_smul]
  rw [modularInversionSL_action_coe,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe]
  simp only [Complex.ofReal_neg,Complex.ofReal_one,sub_eq_add_neg]

theorem idealParabolicNormalizer_intertwines :
    idealParabolicNormalizerSL*idealCornerSL 0=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)*idealParabolicNormalizerSL := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [idealParabolicNormalizerSL,idealCornerSL,modularInversionSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem idealParabolicNormalizer_sector (z : ℍ) :
    z∈idealCornerSector 0 ↔ (idealParabolicNormalizerSL • z).re∈Ioo (0:ℝ) 1 := by
  have hd : 0<Complex.normSq ((z:ℂ)-1):=by
    apply Complex.normSq_pos.mpr
    intro he
    have hh:=congrArg Complex.im (sub_eq_zero.mp he)
    have hp:=z.im_pos
    norm_num at hh
    linarith
  have hf:=congrArg Complex.re (idealParabolicNormalizer_coe z)
  norm_num [Complex.div_re] at hf
  change (z.re<Real.cos 0 ∧ z.re<Real.cos 0*Complex.normSq (z:ℂ)) ↔ _
  rw [Real.cos_zero,one_mul,show (idealParabolicNormalizerSL • z).re=(1-z.re)/Complex.normSq ((z:ℂ)-1) from hf]
  simp only [mem_Ioo]
  rw [div_pos_iff_of_pos_right hd,div_lt_one hd]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
    UpperHalfPlane.coe_re,UpperHalfPlane.coe_im,sub_zero]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨by linarith,by nlinarith⟩
  · rintro ⟨h1,h2⟩
    exact ⟨by linarith,by nlinarith⟩


/-- The actual cusp chart conjugates the zero-angle corner to translation by minus one. -/
theorem idealParabolicNormalizer_conjugation :
    (MulAut.conj (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry idealParabolicNormalizerSL))
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (idealCornerSL 0))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)) := by
  have he : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry idealParabolicNormalizerSL*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (idealCornerSL 0)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1))*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry idealParabolicNormalizerSL:=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _*_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom _
    rw [←map_mul,←map_mul,idealParabolicNormalizer_intertwines]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry idealParabolicNormalizerSL*_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (idealCornerSL 0)*
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry idealParabolicNormalizerSL)⁻¹=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1))
  rw [he]
  group

theorem idealParabolicNormalizer_zpow (k : ℤ) (z : ℍ) :
    idealParabolicNormalizerSL • ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (idealCornerSL 0)^k) z)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-(k:ℝ)) • (idealParabolicNormalizerSL • z) := by
  let F:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry idealParabolicNormalizerSL
  let U:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (idealCornerSL 0)
  have hp : (MulAut.conj F) (U^k)=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)))^k:=by
    rw [map_zpow,idealParabolicNormalizer_conjugation]
  change F*U^k*F⁻¹=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryHom (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-1)))^k at hp
  rw [←map_zpow,hTranslationSL_zpow] at hp
  have hh : (k:ℝ)*(-1)= -(k:ℝ):=by ring
  rw [hh] at hp
  calc
    _ = (F*U^k*F⁻¹) (F z) := by
      change F ((U^k) z)=F ((U^k) (F⁻¹ (F z)))
      rw [IsometryEquiv.inv_apply_self]
    _ = _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-(k:ℝ)) • (idealParabolicNormalizerSL • z) := by rw [hp];rfl

/-- The genuine parabolic corner's cyclic translates of its physical open sector are disjoint. -/
theorem idealCornerSector_zero_disjoint (g : ℍ≃ᵢℍ)
    (hg : g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (idealCornerSL 0)))
    (hne : g≠1) :
    Disjoint (g • idealCornerSector 0) (idealCornerSector 0) := by
  rcases hg with ⟨k,rfl⟩
  have hk : k≠0:=by
    intro he
    apply hne
    simp only [he,zpow_zero]
  apply disjoint_left.mpr
  rintro _ ⟨z,hz,rfl⟩ hgz
  have h1:=(idealParabolicNormalizer_sector z).mp hz
  have h2:=(idealParabolicNormalizer_sector _).mp hgz
  change (idealParabolicNormalizerSL • ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (idealCornerSL 0)^k) z)).re∈Ioo (0:ℝ) 1 at h2
  have he:=congrArg UpperHalfPlane.re (idealParabolicNormalizer_zpow k z)
  change _=((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL (-(k:ℝ)) • (idealParabolicNormalizerSL • z):ℍ):ℂ).re at he
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL_coe] at he
  simp only [Complex.add_re,Complex.ofReal_re,UpperHalfPlane.coe_re] at he
  have hl : (-1:ℝ)<(k:ℝ):=by linarith [h1.1,h1.2,h2.1,h2.2]
  have hu : (k:ℝ)<1:=by linarith [h1.1,h1.2,h2.1,h2.2]
  have hl' : (-1:ℤ)<k:=by exact_mod_cast hl
  have hu' : k<(1:ℤ):=by exact_mod_cast hu
  exact hk (by omega)

/-- The right-angle sector is the literal negative half-plane. -/
theorem idealCornerSector_pi_div_two :
    idealCornerSector (Real.pi/2)={z:ℍ | z.re<0} := by
  ext z
  simp [idealCornerSector]

theorem idealCornerSL_pi_div_two : idealCornerSL (Real.pi/2)=modularInversionSL := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [idealCornerSL, _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationSL, modularInversionSL,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem idealCornerSector_pi_div_two_disjoint (g : ℍ≃ᵢℍ)
    (hg : g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (idealCornerSL (Real.pi/2)))) (hne : g≠1) :
    Disjoint (g • idealCornerSector (Real.pi/2)) (idealCornerSector (Real.pi/2)) := by
  rw [idealCornerSL_pi_div_two] at hg
  rw [modularInversion_zpowers_nonidentity g hg hne,idealCornerSector_pi_div_two]
  apply disjoint_left.mpr
  rintro _ ⟨z,hz,rfl⟩ hgz
  have hp : 0<(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modularInversionSL z).re:=by
    change 0<((modularInversionSL • z:ℍ):ℂ).re
    rw [modularInversionSL_action_coe]
    simp only [Complex.div_re,Complex.neg_re,Complex.one_re,Complex.neg_im,Complex.one_im,
      zero_mul,neg_zero,zero_div,add_zero,neg_mul,one_mul,UpperHalfPlane.coe_re]
    exact div_pos (neg_pos.mpr hz) (Complex.normSq_pos.mpr z.ne_zero)
  exact (not_lt_of_ge hp.le) hgz


theorem idealCornerSector_nat_eq_hecke (n : ℕ) (hn : 3≤n) :
    idealCornerSector (Real.pi/(n:ℝ))=heckePingPongSector n hn := by
  ext z
  rw [heckePingPongSector_mem_iff]
  rfl

/-- Every genuine integral corner, finite or ideal, has a physical cyclic open sector. -/
theorem idealCornerSector_disjoint (θ : ℝ) (hθ : IsIntegralTriangleAngle θ)
    (g : ℍ≃ᵢℍ)
    (hg : g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (idealCornerSL θ)))
    (hne : g≠1) :
    Disjoint (g • idealCornerSector θ) (idealCornerSector θ) := by
  rw [IsIntegralTriangleAngle] at hθ
  rcases hθ with rfl|⟨n,hn,rfl⟩
  · exact idealCornerSector_zero_disjoint g hg hne
  · by_cases hn2 : n=2
    · subst n
      norm_num only [Nat.cast_ofNat] at hg ⊢
      exact idealCornerSector_pi_div_two_disjoint g hg hne
    · have hn3 : 3≤n:=by omega
      change g∈Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (standardHeckeCornerSL n)) at hg
      rw [idealCornerSector_nat_eq_hecke n hn3]
      exact heckePingPongSector_disjoint_translate n hn3 g hg hne

theorem IsIntegralTriangleAngle.cos_nonneg {θ : ℝ} (hθ : IsIntegralTriangleAngle θ) :
    0≤Real.cos θ := by
  rw [IsIntegralTriangleAngle] at hθ
  rcases hθ with rfl|⟨n,hn,rfl⟩
  · norm_num
  · have hn0 : 0<(n:ℝ):=by positivity
    have hn2 : (2:ℝ)≤(n:ℝ):=by exact_mod_cast hn
    apply Real.cos_nonneg_of_mem_Icc
    constructor
    · have hpos : 0<Real.pi/(n:ℝ):=div_pos Real.pi_pos hn0
      linarith [Real.pi_pos]
    · apply (div_le_iff₀ hn0).mpr
      nlinarith [Real.pi_pos]

theorem idealCornerSector_contains_negative (θ : ℝ) (hc : 0≤Real.cos θ)
    (z : ℍ) (hz : z.re<0) : z∈idealCornerSector θ := by
  exact ⟨hz.trans_le hc,hz.trans_le (mul_nonneg hc (Complex.normSq_nonneg _))⟩

/-- The physical unit-circle reflection interchanges the two bounding inequalities of every sector. -/
theorem idealCornerSector_circleReflection_iff (θ : ℝ) (z : ℍ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z∈idealCornerSector θ ↔ z∈idealCornerSector θ := by
  have hn : 0<‖(z:ℂ)‖^2:=sq_pos_of_pos (norm_pos_iff.mpr z.ne_zero)
  change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z).re<Real.cos θ ∧
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z).re<Real.cos θ*Complex.normSq (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z:ℂ)) ↔
    (z.re<Real.cos θ ∧ z.re<Real.cos θ*Complex.normSq (z:ℂ))
  rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq,
    unitCircleReflection_re,unitCircleReflection_norm_sq]
  have h1 : z.re/‖(z:ℂ)‖^2<Real.cos θ ↔ z.re<Real.cos θ*‖(z:ℂ)‖^2:=div_lt_iff₀ hn
  have h2 : z.re/‖(z:ℂ)‖^2<Real.cos θ*(‖(z:ℂ)‖^2)⁻¹ ↔ z.re<Real.cos θ:=by
    rw [←div_eq_mul_inv,div_lt_div_iff_of_pos_right hn]
  rw [h1,h2]
  exact and_comm

theorem idealTriangleAxisMirror_circleReflection (z : ℍ) :
    idealTriangleAxisMirror (_root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one z)=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection 0 1 zero_lt_one (idealTriangleAxisMirror z) := by
  apply UpperHalfPlane.ext
  rw [idealTriangleAxisMirror_coe, _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.circleReflection_coe, idealTriangleAxisMirror_coe]
  simp

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open scoped Pointwise
theorem two_pingPong_wandering
    {G : Type*} [Group G]
    {X : Type*} [MulAction G X]
    (A B : Subgroup G) (P Q U : Set X)
    (hA : ∀g∈A,g≠1→g • Q⊆P) (hB : ∀g∈B,g≠1→g • P⊆Q)
    (hAU : ∀g∈A,g≠1→g • U⊆P) (hBU : ∀g∈B,g≠1→g • U⊆Q)
    (hPU : Disjoint P U) (hQU : Disjoint Q U)
    (g : G) (hg : g∈A⊔B) (hne : g≠1) : Disjoint (g • U) U := by
  let H : Bool→Type _:=fun | false=>A | true=>B
  let : ∀b,Group (H b):=fun | false=>inferInstance | true=>inferInstance
  let f : ∀b,H b→*G:=fun | false=>A.subtype | true=>B.subtype
  let R : Bool→Set X:=fun b=>if b then Q else P
  have hpp : Pairwise fun i j=>∀h : H i,h≠1→f i h • R j⊆R i:=by
    intro i j hij h hh
    cases i <;> cases j
    · exact False.elim (hij rfl)
    · exact hA (h:A).val (h:A).property (fun he=>hh (Subtype.ext he))
    · exact hB (h:B).val (h:B).property (fun he=>hh (Subtype.ext he))
    · exact False.elim (hij rfl)
  have hstart : ∀i (h : H i),h≠1→f i h • U⊆R i:=by
    intro i h hh
    cases i
    · exact hAU (h:A).val (h:A).property (fun he=>hh (Subtype.ext he))
    · exact hBU (h:B).val (h:B).property (fun he=>hh (Subtype.ext he))
  have hgap : ∀i,Disjoint (R i) U:=by
    intro i
    cases i
    · exact hPU
    · exact hQU
  have hrange : (Monoid.CoprodI.lift f).range=A⊔B:=by
    rw [Monoid.CoprodI.range_eq_iSup]
    change (⨆b : Bool,(f b).range)=A⊔B
    rw [iSup_bool_eq]
    change B.subtype.range⊔A.subtype.range=A⊔B
    rw [Subgroup.range_subtype,Subgroup.range_subtype,sup_comm]
  rw [←hrange] at hg
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.pingPong_range_wandering f R U hpp hstart hgap g hg hne

end LowDimensionalTopology.Geometry.Fuchsian

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

theorem IsIntegralTriangleAngle.nonneg {θ : ℝ} (hθ : IsIntegralTriangleAngle θ) : 0≤θ := by
  rw [IsIntegralTriangleAngle] at hθ
  rcases hθ with rfl|⟨n,hn,rfl⟩
  · exact le_rfl
  · positivity

def idealTwoCornerLeftSector (θ : ℝ) : Set ℍ:=idealTriangleAxisMirror ⁻¹' idealCornerSector θ

def idealTwoCornerGap (α β : ℝ) : Set ℍ:=idealTwoCornerLeftSector α∩idealCornerSector β

def idealTwoCornerLeftGroup (θ : ℝ) : Subgroup (ℍ≃ᵢℍ):=
  (Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (idealCornerSL θ))).map idealTriangleLeftConjugation

def idealTwoCornerGroup (α β : ℝ) : Subgroup (ℍ≃ᵢℍ):=
  idealTwoCornerLeftGroup α⊔Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (idealCornerSL β))

theorem idealTwoCornerLeftSector_disjoint (θ : ℝ) (hθ : IsIntegralTriangleAngle θ)
    (g : ℍ≃ᵢℍ) (hg : g∈idealTwoCornerLeftGroup θ) (hne : g≠1) :
    Disjoint (g • idealTwoCornerLeftSector θ) (idealTwoCornerLeftSector θ) := by
  obtain ⟨a,ha,he⟩:=hg
  have ha1 : a≠1:=by
    intro h1
    rw [h1,map_one] at he
    exact hne he.symm
  have hdis:=idealCornerSector_disjoint θ hθ a ha ha1
  apply disjoint_left.mpr
  rintro _ ⟨x,hx,rfl⟩ hzx
  apply disjoint_left.mp hdis
  · refine ⟨idealTriangleAxisMirror x,hx,?_⟩
    change a (idealTriangleAxisMirror x)=idealTriangleAxisMirror (g x)
    rw [←he,idealTriangleLeftConjugation_mirror]
  · exact hzx

/-- The genuine two sectors cover H whenever the source angle sum is less than pi. -/
theorem idealTwoCornerSector_union (α β : ℝ) (hα : IsIntegralTriangleAngle α)
    (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi) :
    idealTwoCornerLeftSector α∪idealCornerSector β=univ := by
  have ha:=hα.cos_nonneg
  have hb:=hβ.cos_nonneg
  have hp:=angle_pair_cosine_sum_pos α β hα.nonneg hβ.nonneg hs
  apply eq_univ_of_forall
  intro z
  rcases lt_trichotomy z.re 0 with hz|hz|hz
  · exact Or.inr (idealCornerSector_contains_negative β hb z hz)
  · by_cases hap : 0<Real.cos α
    · left
      change (idealTriangleAxisMirror z).re<Real.cos α ∧
        (idealTriangleAxisMirror z).re<Real.cos α*Complex.normSq (idealTriangleAxisMirror z:ℂ)
      rw [idealTriangleAxisMirror_re,hz,neg_zero]
      exact ⟨hap,mul_pos hap (Complex.normSq_pos.mpr (idealTriangleAxisMirror z).ne_zero)⟩
    · right
      have hbp : 0<Real.cos β:=by linarith
      change z.re<Real.cos β ∧ z.re<Real.cos β*Complex.normSq (z:ℂ)
      rw [hz]
      exact ⟨hbp,mul_pos hbp (Complex.normSq_pos.mpr z.ne_zero)⟩
  · left
    apply idealCornerSector_contains_negative α ha (idealTriangleAxisMirror z)
    rw [idealTriangleAxisMirror_re]
    linarith

/-- Every nontrivial element of the original two-corner generated group moves its genuine middle gap away. -/
theorem idealTwoCornerGap_wandering (α β : ℝ) (hα : IsIntegralTriangleAngle α)
    (hβ : IsIntegralTriangleAngle β) (hs : α+β<Real.pi)
    (g : ℍ≃ᵢℍ) (hg : g∈idealTwoCornerGroup α β) (hne : g≠1) :
    Disjoint (g • idealTwoCornerGap α β) (idealTwoCornerGap α β) := by
  have hu (z : ℍ) : z∈idealTwoCornerLeftSector α ∨ z∈idealCornerSector β:=by
    change z∈idealTwoCornerLeftSector α∪idealCornerSector β
    rw [idealTwoCornerSector_union α β hα hβ hs]
    trivial
  apply two_pingPong_wandering (idealTwoCornerLeftGroup α)
    (Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (idealCornerSL β)))
    (idealTwoCornerLeftSector α)ᶜ (idealCornerSector β)ᶜ (idealTwoCornerGap α β)
    ?_ ?_ ?_ ?_ ?_ ?_ g hg hne
  · intro f hf hf1
    rintro _ ⟨x,hx,rfl⟩ hfx
    have hxL:=(hu x).resolve_right hx
    exact disjoint_left.mp (idealTwoCornerLeftSector_disjoint α hα f hf hf1) ⟨x,hxL,rfl⟩ hfx
  · intro f hf hf1
    rintro _ ⟨x,hx,rfl⟩ hfx
    have hxR:=(hu x).resolve_left hx
    exact disjoint_left.mp (idealCornerSector_disjoint β hβ f hf hf1) ⟨x,hxR,rfl⟩ hfx
  · intro f hf hf1
    rintro _ ⟨x,hx,rfl⟩ hfx
    exact disjoint_left.mp (idealTwoCornerLeftSector_disjoint α hα f hf hf1) ⟨x,hx.1,rfl⟩ hfx
  · intro f hf hf1
    rintro _ ⟨x,hx,rfl⟩ hfx
    exact disjoint_left.mp (idealCornerSector_disjoint β hβ f hf hf1) ⟨x,hx.2,rfl⟩ hfx
  · exact disjoint_left.mpr (fun _ hnot hin=>hnot hin.1)
  · exact disjoint_left.mpr (fun _ hnot hin=>hnot hin.2)

end LowDimensionalTopology.Geometry.Fuchsian
