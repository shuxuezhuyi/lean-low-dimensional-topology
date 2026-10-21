/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.TwoParabolicEllipticProducts
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

theorem realSL_finite_order_trace_cosine (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1)
    (hfin : IsOfFinOrder (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) :
    ∃r m : ℕ, r=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) ∧ 2≤r ∧ 0<m ∧ m<r ∧ m.Coprime r ∧
      (Matrix.trace A.val)^2=4*(Real.cos (Real.pi*(m:ℝ)/r))^2 := by
  let r := orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)
  have hr : 0<r := orderOf_pos_iff.mpr hfin
  have hr1 : r≠1 := by
    intro he
    exact hA (orderOf_eq_one_iff.mp he)
  have hr2 : 2≤r := by omega
  obtain ⟨u,m,hm,hcop,_hconj,_hexp,htrace⟩ :=
    _root_.LowDimensionalTopology.Geometry.Mobius.mobius_exact_order_angle_squaredTrace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) hA r hr rfl
  have hm0 : 0<m := by
    by_contra hn
    have hmz : m=0 := by omega
    have he : r=1 := by simpa [hmz] using hcop
    exact hr1 he
  refine ⟨r,m,rfl,hr2,hm0,hm,hcop,?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_squaredTrace] at htrace
  exact Complex.ofReal_injective htrace

/-- Finite order makes the positive parameter an actual cosine at an integer index. -/
theorem twoParabolic_parameter_cosine_index (c : ℝ) (hc : 0<c) (h4 : c<4)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (twoParabolicCanonicalGroup c)) :
    ∃r k : ℕ, r=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicCornerSL c)) ∧
      2≤r ∧ 0<k ∧ k<r ∧ c=2+2*Real.cos (Real.pi*(k:ℝ)/r) := by
  obtain ⟨r,m,hr,hr2,hm0,hmr,_hcop,htr⟩ := realSL_finite_order_trace_cosine
    (twoParabolicCornerSL c) (twoParabolicCornerSL_ne_one c hc.ne')
    (twoParabolicCornerSL_finiteOrder c hc h4 hd)
  rw [twoParabolicCornerSL_trace] at htr
  have he : (c-2-2*Real.cos (Real.pi*(m:ℝ)/r))*
      (c-2+2*Real.cos (Real.pi*(m:ℝ)/r))=0 := by nlinarith [htr]
  rcases mul_eq_zero.mp he with he|he
  · exact ⟨r,m,hr,hr2,hm0,hmr,by linarith⟩
  · have hk0 : 0<r-m := Nat.sub_pos_of_lt hmr
    have hkr : r-m<r := Nat.sub_lt (by omega) hm0
    have hrR : (0:ℝ)<r := by exact_mod_cast (by omega : 0<r)
    have ha : Real.pi*((r-m:ℕ):ℝ)/r=Real.pi-Real.pi*(m:ℝ)/r := by
      rw [Nat.cast_sub hmr.le]
      field_simp
    refine ⟨r,r-m,hr,hr2,hk0,hkr,?_⟩
    rw [ha,Real.cos_pi_sub]
    linarith

/-- The actual sharp height inequality rules out every integer index above two. -/
theorem twoParabolic_cosine_index_le_two (c : ℝ) (r k : ℕ)
    (hr : 2≤r) (hk0 : 0<k) (hkr : k<r)
    (hc : c=2+2*Real.cos (Real.pi*(k:ℝ)/r))
    (hlower : 4*(Real.cos (Real.pi/(r:ℝ)))^2≤c) : k≤2 := by
  have hrR : (0:ℝ)<r := by exact_mod_cast (by omega : 0<r)
  have hr2R : (2:ℝ)≤r := by exact_mod_cast hr
  have hkR : (0:ℝ)<k := by exact_mod_cast hk0
  have hkrR : (k:ℝ)<r := by exact_mod_cast hkr
  have hdouble : Real.cos (2*Real.pi/(r:ℝ))=2*(Real.cos (Real.pi/(r:ℝ)))^2-1 := by
    rw [show 2*Real.pi/(r:ℝ)=2*(Real.pi/(r:ℝ)) by ring,Real.cos_two_mul]
  have hbound : Real.cos (2*Real.pi/(r:ℝ))≤Real.cos (Real.pi*(k:ℝ)/r) := by
    rw [hc] at hlower
    nlinarith [hdouble,hlower]
  by_contra hn
  have hk2R : (2:ℝ)<k := by exact_mod_cast (by omega : 2<k)
  have hleft : 0≤2*Real.pi/(r:ℝ) := by positivity
  have hright : 2*Real.pi/(r:ℝ)≤Real.pi :=
    (div_le_iff₀ hrR).mpr (by nlinarith [Real.pi_pos])
  have hkleft : 0≤Real.pi*(k:ℝ)/r := by positivity
  have hkright : Real.pi*(k:ℝ)/r≤Real.pi := by
    apply (div_le_iff₀ hrR).mpr
    nlinarith [Real.pi_pos]
  have hangle : 2*Real.pi/(r:ℝ)<Real.pi*(k:ℝ)/r :=
    div_lt_div_of_pos_right (by nlinarith [Real.pi_pos]) hrR
  have hstrict := Real.strictAntiOn_cos ⟨hleft,hright⟩ ⟨hkleft,hkright⟩ hangle
  exact (not_lt_of_ge hbound) hstrict

/-- All genuine discrete small positive models have one of the two source cosine parameters. -/
theorem twoParabolic_small_parameter_classification (c : ℝ) (hc : 1≤c) (h4 : c<4)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (twoParabolicCanonicalGroup c)) :
    ∃r : ℕ, 2≤r ∧ r=orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (twoParabolicCornerSL c)) ∧
      (c=2+2*Real.cos (Real.pi/(r:ℝ)) ∨ c=2+2*Real.cos (2*Real.pi/(r:ℝ))) := by
  have hc0 : 0<c := by linarith
  obtain ⟨r,k,hr,hr2,hk0,hkr,hcform⟩ := twoParabolic_parameter_cosine_index c hc0 h4 hd
  have hlower : 4*(Real.cos (Real.pi/(r:ℝ)))^2≤c := by
    by_cases hr3 : 3≤r
    · rw [hr]
      exact twoParabolic_parameter_order_lower c hc0 h4 hd (by rwa [←hr])
    · have hrval : r=2 := by omega
      norm_num [hrval,Real.cos_pi_div_two]
      exact hc0.le
  have hk2 := twoParabolic_cosine_index_le_two c r k hr2 hk0 hkr hcform hlower
  refine ⟨r,hr2,hr,?_⟩
  rcases (show k=1 ∨ k=2 by omega) with hk|hk
  · exact Or.inl (by simpa only [hk,Nat.cast_one,mul_one] using hcform)
  · exact Or.inr (by simpa only [hk,Nat.cast_ofNat,mul_comm Real.pi (2:ℝ)] using hcform)

/-- The two cosine parameter branches give the exact original commutator trace
alternatives, without assuming a normalizer or a canonical model. -/
theorem two_parabolic_commutator_trace_alternatives (A B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A)) (hB : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B))
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup)))
    (hne : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary (Subgroup.closure
      ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B} : Set Mobius.complexMobiusGroup))) :
    18≤Matrix.trace (A*B*A⁻¹*B⁻¹).val ∨
      (∃r : ℕ,3≤r ∧ Matrix.trace (A*B*A⁻¹*B⁻¹).val=
        2+16*(Real.cos (Real.pi/(r:ℝ)))^4) ∨
      (∃r : ℕ,2≤r ∧ Matrix.trace (A*B*A⁻¹*B⁻¹).val=
        2+16*(Real.cos (Real.pi/(2*(r:ℝ))))^4) := by
  by_cases hlarge : 18≤Matrix.trace (A*B*A⁻¹*B⁻¹).val
  · exact Or.inl hlarge
  have hsmall := lt_of_not_ge hlarge
  obtain ⟨q,c,hc,_hq,htrace,hdc,_hnec⟩ :=
    two_parabolic_discrete_positive_normal_form A B hA hB hd hne
  have h4 : c<4 := (twoParabolic_small_trace_parameter c hc).mp (by rwa [←htrace])
  obtain ⟨r,hr,_horder,hcform⟩ := twoParabolic_small_parameter_classification c hc h4 hdc
  rcases hcform with hcform|hcform
  · right
    right
    refine ⟨r,hr,?_⟩
    have hdouble := Real.cos_two_mul (Real.pi/(2*(r:ℝ)))
    rw [show 2*(Real.pi/(2*(r:ℝ)))=Real.pi/(r:ℝ) by ring] at hdouble
    have he : c=4*(Real.cos (Real.pi/(2*(r:ℝ))))^2 := by nlinarith [hcform,hdouble]
    rw [htrace,he]
    ring
  · have hr3 : 3≤r := by
      by_contra hn
      have hrval : r=2 := by omega
      norm_num [hrval,Real.cos_pi] at hcform
      linarith
    right
    left
    refine ⟨r,hr3,?_⟩
    have hdouble := Real.cos_two_mul (Real.pi/(r:ℝ))
    rw [show 2*(Real.pi/(r:ℝ))=2*Real.pi/(r:ℝ) by ring] at hdouble
    have he : c=4*(Real.cos (Real.pi/(r:ℝ)))^2 := by nlinarith [hcform,hdouble]
    rw [htrace,he]
    ring

end LowDimensionalTopology.Geometry.Fuchsian
