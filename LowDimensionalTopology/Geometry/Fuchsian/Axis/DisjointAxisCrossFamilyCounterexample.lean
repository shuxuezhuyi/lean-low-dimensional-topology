module
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleAxisExample
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.ThreeHalfTurns.Classification
public import LowDimensionalTopology.Geometry.Fuchsian.Collar.HyperbolicCollarSeparation
public import LowDimensionalTopology.Geometry.Fuchsian.Axis.SimpleAxisSharpness
public import LowDimensionalTopology.Geometry.Fuchsian.Displacement.Elliptic.EllipticNontriangleFamilies
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalConstruction
public import LowDimensionalTopology.Geometry.Fuchsian.Generation.TwoParabolics.TwoParabolicTriangleModels
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Topology
open scoped UpperHalfPlane MatrixGroups OnePoint Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyDiscreteness
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

local instance crossFamilyDiscreteEvaluationAction {X : Type*} [MetricSpace X] : MulAction (X≃ᵢX) X where
  smul g x:=g x
  one_smul _:=rfl
  mul_smul _ _ _:=rfl

def halfTurn : ℍ≃ᵢℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (1/3) (by norm_num))
def center : ℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (1/3) (by norm_num)
def outer : Set ℍ := {z | 1/9<Complex.normSq (z:ℂ)}
def cell (R : ℍ≃ᵢℍ) : Set ℍ :=
  {z | ∀g∈Subgroup.zpowers R,g≠1→dist z center<dist z (g center)}

theorem order_four_strict_cell_iff (R : ℍ≃ᵢℍ) (hR : orderOf R=4) (w z : ℍ) :
    (∀g∈Subgroup.zpowers R,g≠1→dist z w<dist z (g w)) ↔
      dist z w<dist z (R w) ∧ dist z w<dist z ((R^2) w) ∧ dist z w<dist z ((R^3) w) := by
  have hne (k : ℕ) (hk : k=1 ∨ k=2 ∨ k=3) : R^k≠1 := by
    intro he
    have hd:=orderOf_dvd_of_pow_eq_one he
    rw [hR] at hd
    rcases hk with rfl|rfl|rfl <;> norm_num at hd
  constructor
  · intro h
    refine ⟨?_,h (R^2) ((Subgroup.zpowers R).pow_mem (Subgroup.mem_zpowers R) 2) (hne 2 (by simp)),
      h (R^3) ((Subgroup.zpowers R).pow_mem (Subgroup.mem_zpowers R) 3) (hne 3 (by simp))⟩
    simpa only [pow_one] using h (R^1) ((Subgroup.zpowers R).pow_mem (Subgroup.mem_zpowers R) 1) (hne 1 (by simp))
  · rintro ⟨h1,h2,h3⟩ g hg hg1
    obtain ⟨k,hk⟩:=Subgroup.mem_zpowers_iff.mp hg
    have hp : R^(k%4)=g := by
      simpa only [hR,Nat.cast_ofNat] using (zpow_mod_orderOf R k).trans hk
    have hrem : k%4=0 ∨ k%4=1 ∨ k%4=2 ∨ k%4=3 := by
      have h0:=Int.emod_nonneg k (by norm_num : (4:ℤ)≠0)
      have h4:=Int.emod_lt_of_pos k (by norm_num : (0:ℤ)<4)
      omega
    rcases hrem with he|he|he|he
    · rw [he,zpow_zero] at hp
      exact False.elim (hg1 hp.symm)
    · rw [he,zpow_one] at hp
      rwa [←hp]
    · rw [he,show (2:ℤ)=(2:ℕ) by norm_num,zpow_natCast] at hp
      rwa [←hp]
    · rw [he,show (3:ℤ)=(3:ℕ) by norm_num,zpow_natCast] at hp
      rwa [←hp]

theorem cell_contains_inner (R : ℍ≃ᵢℍ) (hR : orderOf R=4)
    (h1 : R center=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (4/5) (3/5) (by norm_num))
    (h2 : (R^2) center=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 3 (by norm_num))
    (h3 : (R^3) center=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-4/5) (3/5) (by norm_num))
    (z : ℍ) (hz : Complex.normSq (z:ℂ)+2*|z.re|<1) : z∈cell R := by
  change (∀g∈Subgroup.zpowers R,g≠1→dist z center<dist z (g center))
  rw [order_four_strict_cell_iff R hR,h1,h2,h3]
  change dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (1/3)
    _)<_ ∧ dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (1/3) _)<_ ∧
    dist z (_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (1/3) _)<_
  rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.metricProbe_dist_lt_iff,_root_.LowDimensionalTopology.Geometry.Fuchsian.metricProbe_dist_lt_iff,_root_.LowDimensionalTopology.Geometry.Fuchsian.metricProbe_dist_lt_iff]
  have hp:=le_abs_self z.re
  have hn:=neg_le_abs z.re
  have ha:=abs_nonneg z.re
  constructor
  · nlinarith only [hz,hp]
  constructor
  · nlinarith only [hz,ha]
  · nlinarith only [hz,hn]

theorem outer_packing (g : ℍ≃ᵢℍ) (hg : g∈Subgroup.zpowers halfTurn) (hne : g≠1) :
    Disjoint (g • outer) outer := by
  have horder : orderOf halfTurn=2 := by
    rw [halfTurn,←_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_order_eq_native]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at (1/3) (by norm_num)).1
  obtain ⟨k,hk⟩:=Subgroup.mem_zpowers_iff.mp hg
  have hp : halfTurn^(k%2)=g := by
    simpa only [horder,Nat.cast_ofNat] using (zpow_mod_orderOf halfTurn k).trans hk
  have hrem : k%2=1 := by
    have h0:=Int.emod_nonneg k (by norm_num : (2:ℤ)≠0)
    have h2:=Int.emod_lt_of_pos k (by norm_num : (0:ℤ)<2)
    have hc : k%2=0 ∨ k%2=1:=by omega
    rcases hc with hc|hc
    · rw [hc,zpow_zero] at hp
      exact False.elim (hne hp.symm)
    · exact hc
  rw [hrem,zpow_one] at hp
  rw [←hp]
  apply disjoint_left.mpr
  rintro _ ⟨z,hz,rfl⟩ hEz
  change 1/9<Complex.normSq (z:ℂ) at hz
  change 1/9<Complex.normSq ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (1/3) _ • z:ℍ):ℂ) at hEz
  have hn:=(_root_.LowDimensionalTopology.Geometry.Fuchsian.halfTurnIdealFold_axis_coordinates (1/3) (by norm_num) z).2
  rw [hn] at hEz
  have hpos : 0<Complex.normSq (z:ℂ) := lt_trans (by norm_num) hz
  have hm:=(lt_div_iff₀ hpos).mp hEz
  norm_num at hm
  nlinarith only [hm,hz]

/-- A genuine open wandering gap proves the actual entire native group discrete.
The only input data about the order-four map are its exact order and three
actual images of the specified physical center. -/
theorem actual_two_four_native_discrete (R : ℍ≃ᵢℍ) (hR : orderOf R=4)
    (h1 : R center=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (4/5) (3/5) (by norm_num))
    (h2 : (R^2) center=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 3 (by norm_num))
    (h3 : (R^3) center=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-4/5) (3/5) (by norm_num)) :
    DiscreteTopology (Subgroup.zpowers halfTurn ⊔ Subgroup.zpowers R : Subgroup (ℍ≃ᵢℍ)) := by
  have hO : IsOpen outer := isOpen_lt continuous_const
    (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  have hC : IsOpen (cell R) := by
    have he : cell R={z | dist z center<dist z (R center)} ∩
      ({z | dist z center<dist z ((R^2) center)} ∩ {z | dist z center<dist z ((R^3) center)}) := by
      ext z
      exact order_four_strict_cell_iff R hR center z
    rw [he]
    exact (isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)).inter
      ((isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)).inter
        (isOpen_lt (continuous_id.dist continuous_const) (continuous_id.dist continuous_const)))
  have hcover : outer∪cell R=univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : 1/9<Complex.normSq (z:ℂ)
    · exact Or.inl hz
    · apply Or.inr
      apply cell_contains_inner R hR h1 h2 h3
      have hn : Complex.normSq (z:ℂ)≤1/9:=le_of_not_gt hz
      have hx : z.re^2≤Complex.normSq (z:ℂ) := by
        simp only [Complex.normSq_apply,UpperHalfPlane.coe_re,UpperHalfPlane.coe_im]
        nlinarith only [sq_nonneg z.im]
      have habs : |z.re|≤1/3 := by
        rw [abs_le]
        constructor <;> nlinarith only [hn,hx,sq_nonneg (z.re+1/3),sq_nonneg (z.re-1/3)]
      linarith only [hn,habs]
  have hne : (outer∩cell R).Nonempty := by
    refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 (1/2) (by norm_num),?_,?_⟩
    · norm_num [outer,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.normSq_apply]
    · apply cell_contains_inner R hR h1 h2 h3
      norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.normSq_apply]
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.discreteTopology_of_wandering_open (outer∩cell
    R) (hO.inter hC) hne
  intro g hg
  apply _root_.LowDimensionalTopology.Geometry.Fuchsian.two_packing_domains_wandering (Subgroup.zpowers
    halfTurn) (Subgroup.zpowers R)
    outer (cell R) outer_packing (fun a ha
      hane=>_root_.LowDimensionalTopology.Geometry.Fuchsian.strict_isometry_dirichlet_wandering _ center a ha hane)
    hcover g.val g.property
  intro he
  exact hg (Subtype.ext he)

end LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyDiscreteness

namespace LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyCounterexample
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.Inversive
  LowDimensionalTopology.Geometry.DiscreteGroups.Action LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace


/-- The strict off-diagonal sign is also sufficient for genuine disjointness
from the imaginary axis, including its two ideal endpoints. -/
theorem hyperbolic_axis0_hDisjoint_of_offdiagonal_product_neg
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ≠
      1)
    (htB : 4 < (Matrix.trace B.val)^2) (hbc : B 0 1 * B 1 0 < 0) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).HDisjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB) := by
  have hfin : Disjoint (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB).carrier := by
    apply Set.disjoint_left.mpr
    intro z hzL hzM
    have hz : z.re = 0 := hzL
    have he := (_root_.LowDimensionalTopology.Geometry.Fuchsian.hyperbolic_axis_quadratic_zero B hB htB z).mp hzM
    change B 1 0 * (z.re^2+z.im^2) + (B 1 1-B 0 0)*z.re-B 0 1 = 0 at he
    rw [hz] at he
    have hh := congrArg (fun x : ℝ => x * B 1 0) he
    nlinarith only [hh, hbc, sq_nonneg (B 1 0 * z.im)]
  have hne : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 ≠ _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB := by
    intro he
    obtain ⟨x, _y, hx, _hy, _hxy⟩ := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB
      htB).exists_two_points
    rw [he] at hfin
    exact Set.disjoint_left.mp hfin hx hx
  refine ⟨hne, Set.disjoint_left.mpr ?_, hfin⟩
  intro p hpL hpM
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.vertical_idealEndpoints] at hpL
  simp only [Complex.ofReal_zero, Set.mem_insert_iff, Set.mem_singleton_iff] at hpL
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints] at hpM
  rcases hpL with rfl | rfl
  · have he := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSL_fixed_real_polynomial B 0 hpM
    norm_num only [zero_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_zero, sub_zero, zero_add, sub_eq_zero] at he
    have hb : B 0 1 = 0 := by linarith only [he]
    rw [hb, zero_mul] at hbc
    exact lt_irrefl 0 hbc
  · have hc := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_fixed_infty_iff B).mp hpM
    rw [hc, mul_zero] at hbc
    exact lt_irrefl 0 hbc

/-- Exact trace/metric diagnostic for a rotation followed by a positive dilation.
Discreteness and the source global noncrossing condition are deliberately not asserted. -/
theorem rotation_dilation_disjoint_axis_signed_gap
    (r s t : ℝ) (hr : 0 < r) (hu : r^2+s^2=1) (ht : 0 < t)
    (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL t) ≠ 1)
    (htA : 4 < (Matrix.trace (_root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL t).val)^2)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL r s hu *
      _root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL t) ≠ 1)
    (htB : 4 < (Matrix.trace (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL r s hu *
      _root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL t).val)^2)
    (hd : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).HDisjoint
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL r s hu *
        _root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL t) hB htB)) :
    Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      (_root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL t)) / 2) *
        Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL r s hu *
          _root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL t)) / 2) -
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
        (_root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL t)) / 2) *
        Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis
          (_root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL t) hA htA).lineDist
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis
            (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL r s hu *
            _root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL t) hB htB)) *
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL r s hu * _root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL t)) / 2) = r := by
  let B := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL r s hu * _root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL t
  have hAt := _root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL_sinh_half_translation t ht hA htA
  have hAh : _root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry (_root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL t)) / 2 = t :=
    Real.sinh_injective hAt
  have hBtr : Matrix.trace B.val = 2*r*Real.cosh t := by
    simp only [B, Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two]
    change r*Real.exp t+s*0+(-s*0+r*Real.exp (-t))=2*r*Real.cosh t
    rw [Real.cosh_eq]
    ring
  have hBd : B 0 0-B 1 1 = 2*r*Real.sinh t := by
    simp only [B, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    change (r*Real.exp t+s*0)-(-s*0+r*Real.exp (-t))=2*r*Real.sinh t
    rw [Real.sinh_eq]
    ring
  have hcB := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translation_abs_trace B hB htB
  rw [hBtr, abs_of_pos (by positivity : 0 < 2*r*Real.cosh t)] at hcB
  have hdB := _root_.LowDimensionalTopology.Geometry.Fuchsian.hHyperbolic_axis0_distance_translation_product B hB htB hd
  rw [hBd, abs_of_pos (mul_pos (by positivity : 0 < 2*r) (Real.sinh_pos_iff.mpr ht))] at hdB
  rw [hAh, _root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL_hyperbolic_axis t ht hA htA]
  change Real.cosh t * Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) / 2) -
    Real.sinh t * Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).lineDist
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis B hB htB)) *
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry B) / 2) = r
  have hid := Real.cosh_sq_sub_sinh_sq t
  have hcScaled := congrArg (fun x : ℝ => Real.cosh t*x) hcB
  have hdScaled := congrArg (fun x : ℝ => Real.sinh t*x) hdB
  nlinarith only [hcScaled, hdScaled, congrArg (fun x : ℝ => x*r) hid]


/-- A strict hyperbolic real trace cannot project to the identity. -/
theorem realSL_nontrivial_of_trace_sq_gt_four
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ht : 4 < (Matrix.trace A.val)^2) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ≠ 1 := by
  intro he
  have he' : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) := by
    simpa only [map_one] using he
  rcases (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_eq_iff_sign A 1).mp he' with hm | hm
  all_goals
    have hh := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) ℝ => Matrix.trace M.val) hm
    norm_num [Matrix.trace_fin_two] at hh
    rw [Matrix.trace_fin_two] at ht
    nlinarith only [ht, hh]

def orderFourDiagnosticRotation : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL (Real.sqrt 2 / 2) (Real.sqrt 2 / 2) (by
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))])

def orderFourDiagnosticA : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  _root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL (Real.log 3)

def orderFourDiagnosticB : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  orderFourDiagnosticRotation * orderFourDiagnosticA

theorem orderFourDiagnosticA_trace : Matrix.trace orderFourDiagnosticA.val = 10 / 3 := by
  norm_num [orderFourDiagnosticA, _root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL, Matrix.trace_fin_two,
    Real.exp_neg,
    Real.exp_log (by norm_num : (0 : ℝ) < 3)]

theorem orderFourDiagnosticB_trace : Matrix.trace orderFourDiagnosticB.val = 5 * Real.sqrt 2 / 3 := by
  norm_num [orderFourDiagnosticB, orderFourDiagnosticRotation, orderFourDiagnosticA,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL, _root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL, Matrix.trace_fin_two, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply, Fin.sum_univ_two, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  ring

theorem orderFourDiagnosticB_offdiagonal : orderFourDiagnosticB 0 1 * orderFourDiagnosticB 1 0 = -(1 : ℝ) / 2 := by
  norm_num [orderFourDiagnosticB, orderFourDiagnosticRotation, orderFourDiagnosticA,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL, _root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
    Fin.sum_univ_two, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]

theorem orderFourDiagnosticA_hyperbolic : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticA) := by
  have ht : 4 < (Matrix.trace orderFourDiagnosticA.val)^2 := by rw [orderFourDiagnosticA_trace]; norm_num
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
    (realSL_nontrivial_of_trace_sq_gt_four _ ht)).mpr ht

theorem orderFourDiagnosticB_hyperbolic : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticB) := by
  have ht : 4 < (Matrix.trace orderFourDiagnosticB.val)^2 := by
    rw [orderFourDiagnosticB_trace]
    nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
    (realSL_nontrivial_of_trace_sq_gt_four _ ht)).mpr ht

theorem orderFourDiagnostic_axes_hDisjoint :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticA
      orderFourDiagnosticA_hyperbolic.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
        orderFourDiagnosticA_hyperbolic.1.1).mp orderFourDiagnosticA_hyperbolic)).HDisjoint
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticB
      orderFourDiagnosticB_hyperbolic.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _ orderFourDiagnosticB_hyperbolic.1.1).mp orderFourDiagnosticB_hyperbolic)) := by
  rw [show _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticA
    orderFourDiagnosticA_hyperbolic.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
        orderFourDiagnosticA_hyperbolic.1.1).mp orderFourDiagnosticA_hyperbolic) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 from _root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL_hyperbolic_axis (Real.log 3)
        (Real.log_pos (by norm_num)) _ _]
  apply hyperbolic_axis0_hDisjoint_of_offdiagonal_product_neg
  rw [orderFourDiagnosticB_offdiagonal]
  norm_num

/-- The metric expression has an exact gap larger than one half. This is a diagnostic
for interpreting the global noncrossing hypothesis, not a claim of such a group hypothesis. -/
theorem orderFourDiagnostic_metric_gap :
    Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry orderFourDiagnosticA) / 2) *
        Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry orderFourDiagnosticB) / 2) -
      Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry orderFourDiagnosticA) / 2) *
        Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticA
          orderFourDiagnosticA_hyperbolic.1.1
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
            orderFourDiagnosticA_hyperbolic.1.1).mp orderFourDiagnosticA_hyperbolic)).lineDist
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticB
            orderFourDiagnosticB_hyperbolic.1.1
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
            orderFourDiagnosticB_hyperbolic.1.1).mp orderFourDiagnosticB_hyperbolic))) *
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry orderFourDiagnosticB) / 2) = Real.sqrt 2 / 2 := by
  have hd := orderFourDiagnostic_axes_hDisjoint
  rw [show _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticA
    orderFourDiagnosticA_hyperbolic.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
        orderFourDiagnosticA_hyperbolic.1.1).mp orderFourDiagnosticA_hyperbolic) =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 from _root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL_hyperbolic_axis (Real.log 3)
        (Real.log_pos (by norm_num)) _ _] at hd
  exact rotation_dilation_disjoint_axis_signed_gap (Real.sqrt 2 / 2) (Real.sqrt 2 / 2) (Real.log 3)
    (by positivity) _ (Real.log_pos (by norm_num)) _ _ _ _ hd


/-- The diagnostic rotation is genuinely order four in the actual Mobius group. -/
theorem orderFourDiagnosticRotation_order : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticRotation) = 4 := by
  have hs : orderFourDiagnosticRotation^2 = -(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 (by norm_num)) := by
    ext i j
    all_goals fin_cases i <;> fin_cases j
    all_goals norm_num [pow_two, orderFourDiagnosticRotation,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    all_goals nlinarith [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  have hp : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticRotation)^2 =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 (by norm_num)) := by
    rw [← map_pow, hs, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg]
  have hn : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticRotation)^2 ≠ 1 := by
    rw [hp]
    exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSL_trace_zero_ne_one _ (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_trace 1 (by norm_num))
  have hf : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticRotation)^4 = 1 := by
    rw [show 4 = 2*2 by norm_num, pow_mul, hp]
    have he := pow_orderOf_eq_one (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL 1 (by norm_num)))
    rwa [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at 1 (by norm_num)).1] at he
  exact orderOf_eq_prime_pow (p := 2) (n := 1) hn hf

/-- The order-four model strictly exceeds the proposed one-half signed gap. -/
theorem orderFourDiagnostic_gap_gt_half : (1 : ℝ) / 2 < Real.sqrt 2 / 2 := by
  have hs := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
  have hn := Real.sqrt_nonneg (2 : ℝ)
  nlinarith only [hs, hn]



/-- Actual C2/C4 positive blocks; no free-product injectivity is assumed. -/
theorem order_two_four_positive_blocks
    {G : Type*} [Group G] (x y : G) (hx : orderOf x = 2) (hy : orderOf y = 4)
    (S : Submonoid G) (hD : x*y ∈ S) (hE : x*y^2 ∈ S) (hF : x*y^3 ∈ S)
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
    have hem : 0≤n%4 ∧ n%4<4 := ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩
    have hp : y^(n%4)=a.val := by simpa only [hy,Nat.cast_ofNat] using (zpow_mod_orderOf y n).trans hn
    have hc : n%4=0 ∨ n%4=1 ∨ n%4=2 ∨ n%4=3 := by omega
    rcases hc with he|he|he|he
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
    · rw [he,show (3:ℤ)=(3:ℕ) by norm_num,zpow_natCast] at hp
      change x*a.val∈S
      rw [←hp]
      exact hF
  obtain ⟨w,hw⟩ := hRange hg
  let v := Monoid.CoprodI.Word.equiv w
  have hv : v.prod=w := (Monoid.CoprodI.Word.equiv).symm_apply_apply w
  by_cases he : v=Monoid.CoprodI.Word.empty
  · have hg1 : g=1 := by rw [←hw,←hv,he,Monoid.CoprodI.Word.prod_empty,map_one]
    exact ⟨false,true,1,S.one_mem,by simp only [hg1,Bool.false_eq_true,ite_false,ite_true,mul_one]⟩
  · obtain ⟨i,j,u,hu⟩ := Monoid.CoprodI.NeWord.of_word v he
    obtain ⟨p,hp,hprod⟩ := _root_.LowDimensionalTopology.Geometry.Fuchsian.two_factor_reduced_word_positive_blocks (fun
      b => M b) φ x hxx S hf ht u
    refine ⟨i,j,p,hp,?_⟩
    rw [←hprod]
    change g=π u.toWord.prod
    rw [hu,hv,hw]


/-- The actual half-turn at the second center. -/
def modelHalfTurn : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  orderFourDiagnosticRotation^2*orderFourDiagnosticA

def modelGroup : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius modelHalfTurn,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticRotation} : Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)

theorem modelHalfTurn_eq : modelHalfTurn= -(_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL (1/3) (by norm_num)) := by
  ext i j
  all_goals fin_cases i <;> fin_cases j
  all_goals norm_num [modelHalfTurn,pow_two,orderFourDiagnosticRotation,
    orderFourDiagnosticA,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL,_root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL,_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL,
    Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two,
    Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<3)]
  all_goals nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]

theorem modelHalfTurn_order : orderOf (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius modelHalfTurn)=2 := by
  rw [modelHalfTurn_eq,_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_neg]
  exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL_at (1/3) (by norm_num)).1

def smallRadius : ℝ := (4-Real.sqrt 7)/9
def largeRadius : ℝ := (4+Real.sqrt 7)/9

theorem radii_properties :
    0<smallRadius ∧ smallRadius<1 ∧ 1/9≤ smallRadius ∧
    0<largeRadius ∧ smallRadius*largeRadius=1/9 ∧
    9*smallRadius*(1-smallRadius)=1+smallRadius := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤7)
  have hn:=Real.sqrt_nonneg (7:ℝ)
  dsimp only [smallRadius,largeRadius]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

def smallBoundaryTrap : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := {z|z=∞ ∨
  ∃x:ℝ,z=((x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧ |x|≤ smallRadius}

def wholeBoundaryTrap : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := {z|z=∞ ∨
  ∃x:ℝ,z=((x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧ (|x|≤ smallRadius ∨ largeRadius≤|x|)}

theorem smallBoundaryTrap_subset : smallBoundaryTrap⊆wholeBoundaryTrap := by
  rintro z (h|⟨x,rfl,hx⟩)
  · exact Or.inl h
  · exact Or.inr ⟨x,rfl,Or.inl hx⟩

theorem small_fraction_bounds (x:ℝ) (hx:|x|≤ smallRadius) :
    |(x-1)/(9*(x+1))|≤ smallRadius ∧
    |x/9|≤ smallRadius ∧ |(x+1)/(9*(1-x))|≤ smallRadius := by
  have hr:=radii_properties
  obtain ⟨hl,hu⟩:=abs_le.mp hx
  have hp:0<x+1:=by linarith [hr.1,hr.2.1]
  have hm:0<1-x:=by linarith [hr.1,hr.2.1]
  have hroot:=hr.2.2.2.2.2
  constructor
  · rw [abs_div,abs_of_neg (by linarith : x-1<0),abs_of_pos (by positivity)]
    apply (div_le_iff₀ (by positivity : 0<9*(x+1))).mpr
    nlinarith [mul_nonneg hr.1.le (show 0≤x+smallRadius by linarith)]
  constructor
  · rw [abs_div]
    norm_num
    nlinarith [hr.1]
  · rw [abs_div,abs_of_pos hp,abs_of_pos (by positivity)]
    apply (div_le_iff₀ (by positivity : 0<9*(1-x))).mpr
    nlinarith [mul_nonneg hr.1.le (show 0≤ smallRadius-x by linarith)]

theorem positive_block_entries (j:ℕ) (hj:j=1 ∨ j=2 ∨ j=3) :
    (modelHalfTurn*orderFourDiagnosticRotation^j).val=
      if j=1 then !![-Real.sqrt 2/6,Real.sqrt 2/6;-3*Real.sqrt 2/2,-3*Real.sqrt 2/2]
      else if j=2 then !![-1/3,0;0,-3]
      else !![-Real.sqrt 2/6,-Real.sqrt 2/6;3*Real.sqrt 2/2,-3*Real.sqrt 2/2] := by
  have hs:=Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  rcases hj with rfl|rfl|rfl
  all_goals ext i k
  all_goals fin_cases i <;> fin_cases k
  all_goals norm_num [modelHalfTurn_eq,_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL,orderFourDiagnosticRotation,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL,pow_succ,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two]
  all_goals nlinarith [congrArg (fun x:ℝ=>x*Real.sqrt 2) hs]

/-- Each of the three genuine positive blocks preserves a concrete closed boundary trap. -/
theorem positive_blocks_trap (j:ℕ) (hj:j=1 ∨ j=2 ∨ j=3) :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      (modelHalfTurn*orderFourDiagnosticRotation^j)).val ''
      smallBoundaryTrap⊆smallBoundaryTrap := by
  have hq:Real.sqrt 2≠0:=(Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)).ne'
  have he:=positive_block_entries j hj
  rintro z ⟨w,(rfl|⟨x,rfl,hx⟩),rfl⟩
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_infty]
    change (if ((modelHalfTurn*orderFourDiagnosticRotation^j).val) 1 0=0 then ∞ else
      (((((modelHalfTurn*orderFourDiagnosticRotation^j).val) 0 0/
        ((modelHalfTurn*orderFourDiagnosticRotation^j).val) 1 0:ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))∈_
    rw [he]
    rcases hj with rfl|rfl|rfl
    all_goals norm_num [hq]
    · refine Or.inr ⟨1/9,?_,?_⟩
      · congr 2
        push_cast
        field_simp [hq]
        norm_num
      · norm_num
        exact radii_properties.2.2.1
    · exact Or.inl rfl
    · refine Or.inr ⟨-1/9,?_,?_⟩
      · congr 2
        push_cast
        field_simp [hq]
        norm_num
      · norm_num
        exact radii_properties.2.2.1
  · have hr:=radii_properties
    obtain ⟨hl,hu⟩:=abs_le.mp hx
    have hp:0<x+1:=by linarith [hr.2.1]
    have hm:0<1-x:=by linarith [hr.2.1]
    have hb:=small_fraction_bounds x hx
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_apply]
    change (if ((modelHalfTurn*orderFourDiagnosticRotation^j).val) 1 0*x+
      ((modelHalfTurn*orderFourDiagnosticRotation^j).val) 1 1=0 then ∞ else
      (((((((modelHalfTurn*orderFourDiagnosticRotation^j).val) 0 0*x+
        ((modelHalfTurn*orderFourDiagnosticRotation^j).val) 0 1)/
        (((modelHalfTurn*orderFourDiagnosticRotation^j).val) 1 0*x+
        ((modelHalfTurn*orderFourDiagnosticRotation^j).val) 1 1)):ℝ):ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))∈_
    rw [he]
    rcases hj with rfl|rfl|rfl
    all_goals norm_num only [ite_true,ite_false,Matrix.of_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one,Fin.isValue]
    · rw [ite_eq_right (by nlinarith [Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)] :
        -3*Real.sqrt 2/2*x+-3*Real.sqrt 2/2≠0)]
      refine Or.inr ⟨(x-1)/(9*(x+1)),?_,hb.1⟩
      apply congrArg (fun y:ℝ=>((y:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
      field_simp [hq,hp.ne',show -1-x≠0 by linarith]
      ring_nf
      field_simp [show -1-x≠0 by linarith]
      ring
    · norm_num
      refine Or.inr ⟨x/9,?_,hb.2.1⟩
      congr 2
      push_cast
      ring
    · rw [ite_eq_right (by nlinarith [Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)] :
        3*Real.sqrt 2/2*x+-3*Real.sqrt 2/2≠0)]
      refine Or.inr ⟨(x+1)/(9*(1-x)),?_,hb.2.2⟩
      apply congrArg (fun y:ℝ=>((y:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))
      field_simp [hq,hm.ne',show -1+x≠0 by linarith]
      ring_nf
      field_simp [show -1+x≠0 by linarith]
      ring

/-- The genuine half-turn sends the small trap to the complementary large trap. -/
theorem halfTurn_trap : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius modelHalfTurn).val '' smallBoundaryTrap⊆wholeBoundaryTrap := by
  rintro z ⟨w,(rfl|⟨x,rfl,hx⟩),rfl⟩
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_infty]
    norm_num [modelHalfTurn_eq,_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL]
    exact Or.inr ⟨0,rfl,Or.inl (by simpa using radii_properties.1.le)⟩
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_apply]
    norm_num only [modelHalfTurn_eq,_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL,Matrix.SpecialLinearGroup.coe_neg,
      Matrix.neg_apply,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_fin_one,Fin.isValue,neg_zero,mul_zero,zero_add,add_zero]
    by_cases hx0:x=0
    · subst x
      norm_num
      exact Or.inl rfl
    · rw [ite_eq_right (by intro h;apply hx0;linarith [h] : -3*x≠0)]
      refine Or.inr ⟨-1/(9*x),?_,Or.inr ?_⟩
      · congr 2
        field_simp
        ring
      · rw [abs_div,abs_neg,abs_one,abs_mul]
        norm_num
        rw [show |x|⁻¹*(1/9)=1/(9*|x|) by field_simp]
        apply (le_div_iff₀ (by positivity : 0<9*|x|)).mpr
        have hr:=radii_properties
        have hmul:=mul_le_mul_of_nonneg_left hx hr.2.2.2.1.le
        nlinarith [hr.2.2.2.2.1]

def trapBlocks : Submonoid _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup where
  carrier:={g|∀z∈smallBoundaryTrap,g.val z∈smallBoundaryTrap}
  one_mem':=by intro z hz;exact hz
  mul_mem':=by intro g h hg hh z hz;exact hg _ (hh z hz)

/-- Every genuine whole-group word sends the two actual endpoints of A outside
both of the two explicit complementary intervals. No ambient discreteness or
noncrossing condition is supplied to this word argument. -/
theorem wholeGroup_axis_endpoints_trap (g:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hg:g∈modelGroup)
    (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hz:z=((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∨ z=∞) :
    g.val z∈wholeBoundaryTrap := by
  have hblock (j:ℕ) (hj:j=1 ∨ j=2 ∨ j=3) :
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius modelHalfTurn*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticRotation)^j∈trapBlocks := by
    rw [←map_pow,←map_mul]
    intro w hw
    exact positive_blocks_trap j hj ⟨w,hw,rfl⟩
  obtain ⟨i,j,p,hp,he⟩:=order_two_four_positive_blocks
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      modelHalfTurn) (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticRotation)
    modelHalfTurn_order orderFourDiagnosticRotation_order trapBlocks
    (hblock 1 (Or.inl rfl)) (hblock 2 (Or.inr (Or.inl rfl)))
    (hblock 3 (Or.inr (Or.inr rfl))) g hg
  let b:=(if j then (1:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) else
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius modelHalfTurn).val z
  have hb:b∈smallBoundaryTrap := by
    rcases hz with rfl|rfl <;> cases j
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      modelHalfTurn).val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈smallBoundaryTrap
      have hzero:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_apply modelHalfTurn (0:ℝ)
      norm_num [modelHalfTurn_eq,_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL] at hzero
      have hzero' : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius modelHalfTurn).val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=∞ := by
        simpa [modelHalfTurn_eq,_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL] using hzero
      rw [hzero']
      exact Or.inl rfl
    · exact Or.inr ⟨0,rfl,by simpa using radii_properties.1.le⟩
    · change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius modelHalfTurn).val ∞∈smallBoundaryTrap
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_infty]
      norm_num [modelHalfTurn_eq,_root_.LowDimensionalTopology.Geometry.Hyperbolic.axisHalfTurnSL]
      exact Or.inr ⟨0,rfl,by simpa using radii_properties.1.le⟩
    · exact Or.inl rfl
  have hpb:p.val b∈smallBoundaryTrap:=hp b hb
  rw [he]
  change (if i then _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius modelHalfTurn else
    (1:_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)).val
    (p.val b)∈wholeBoundaryTrap
  cases i
  · exact smallBoundaryTrap_subset hpb
  · exact halfTurn_trap ⟨_,hpb,rfl⟩

theorem radii_order : smallRadius<largeRadius := by
  dsimp only [smallRadius,largeRadius]
  have hp:=Real.sqrt_pos.2 (by norm_num : (0:ℝ)<7)
  linarith

def boundaryNormalizer : Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  ⟨!![-1,-largeRadius;1/(largeRadius-smallRadius),
      smallRadius/(largeRadius-smallRadius)],by
    norm_num [Matrix.det_fin_two]
    field_simp [(sub_pos.mpr radii_order).ne']
    ring⟩

def nonpositiveBoundary : Set _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := {z|z=∞ ∨
  ∃x:ℝ,z=((x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∧ x≤0}

theorem trap_fraction_nonpositive (x:ℝ)
    (hx:|x|≤ smallRadius ∨ largeRadius≤|x|) :
    (-x-largeRadius)/(x+smallRadius)≤0 := by
  have hr:=radii_properties
  rcases hx with hx|hx
  · have hb:=abs_le.mp hx
    exact div_nonpos_of_nonpos_of_nonneg (by linarith [radii_order]) (by linarith)
  · by_cases hxn:0≤x
    · rw [abs_of_nonneg hxn] at hx
      exact div_nonpos_of_nonpos_of_nonneg (by linarith [hr.2.2.2.1])
        (by linarith [hr.1])
    · rw [abs_of_neg (lt_of_not_ge hxn)] at hx
      exact div_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith [radii_order])

theorem normalizer_trap :
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius boundaryNormalizer).val '' wholeBoundaryTrap⊆nonpositiveBoundary := by
  have hd:0<largeRadius-smallRadius:=sub_pos.mpr radii_order
  rintro z ⟨w,(rfl|⟨x,rfl,hx⟩),rfl⟩
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_infty]
    norm_num [boundaryNormalizer,hd.ne']
    refine Or.inr ⟨-(largeRadius-smallRadius),?_,by linarith⟩
    congr 2
    push_cast
    field_simp [hd.ne']
    ring
  · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_apply]
    norm_num only [boundaryNormalizer,Matrix.of_apply,Matrix.cons_val_zero,
      Matrix.cons_val_one,Matrix.cons_val_fin_one,Fin.isValue]
    by_cases hz:x+smallRadius=0
    · rw [ite_eq_left (by field_simp;linarith :
        1/(largeRadius-smallRadius)*x+smallRadius/(largeRadius-smallRadius)=0)]
      exact Or.inl rfl
    · rw [ite_eq_right (by
        intro he
        apply hz
        field_simp [hd.ne'] at he
        linarith : 1/(largeRadius-smallRadius)*x+
          smallRadius/(largeRadius-smallRadius)≠0)]
      refine Or.inr ⟨(largeRadius-smallRadius)*((-x-largeRadius)/(x+smallRadius)),?_,
        mul_nonpos_of_nonneg_of_nonpos hd.le (trap_fraction_nonpositive x hx)⟩
      congr 2
      field_simp [hd.ne',hz]
      ring

theorem nonpositive_endpoints_products (F:Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (h0:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F).val
      ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈nonpositiveBoundary)
    (hi:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F).val ∞∈nonpositiveBoundary) :
    F 0 0*F 1 0≤0 ∧ F 0 1*F 1 1≤0 := by
  have hfinite (x:ℝ) : (((x:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)∈nonpositiveBoundary)↔x≤0 := by
    constructor
    · rintro (he|⟨y,he,hy⟩)
      · exact False.elim ((OnePoint.coe_ne_infty (x:ℂ)) he)
      · have hxy:x=y:=Complex.ofReal_injective (OnePoint.coe_injective he)
        exact hxy.symm ▸ hy
    · intro hx
      exact Or.inr ⟨x,rfl,hx⟩
  constructor
  · by_cases hc:F 1 0=0
    · simp only [hc,mul_zero,le_refl]
    · rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_infty,ite_eq_right hc,hfinite] at hi
      have he:F 0 0*F 1 0=(F 0 0/F 1 0)*(F 1 0)^2:=by field_simp
      rw [he]
      exact mul_nonpos_of_nonpos_of_nonneg hi (sq_nonneg _)
  · by_cases hd:F 1 1=0
    · simp only [hd,mul_zero,le_refl]
    · rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.axisSL_real_zero F hd,hfinite] at h0
      have he:F 0 1*F 1 1=(F 0 1/F 1 1)*(F 1 1)^2:=by field_simp
      rw [he]
      exact mul_nonpos_of_nonpos_of_nonneg h0 (sq_nonneg _)

theorem normalizer_conjugate_offdiagonal :
    (boundaryNormalizer*orderFourDiagnosticB*boundaryNormalizer⁻¹) 0 1=0 ∧
    (boundaryNormalizer*orderFourDiagnosticB*boundaryNormalizer⁻¹) 1 0=0 := by
  have h7:=Real.sq_sqrt (by norm_num : (0:ℝ)≤7)
  have h7q:=congrArg (fun x:ℝ=>x*Real.sqrt 2) h7
  have h7ne:Real.sqrt 7≠0:=(Real.sqrt_pos.2 (by norm_num : (0:ℝ)<7)).ne'
  constructor
  all_goals norm_num [boundaryNormalizer,smallRadius,largeRadius,
    orderFourDiagnosticB,orderFourDiagnosticRotation,orderFourDiagnosticA,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL,_root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL,Real.exp_neg,Real.exp_log (by norm_num : (0:ℝ)<3),
    Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two,Matrix.mul_apply,Fin.sum_univ_two]
  all_goals field_simp [h7ne]
  all_goals nlinarith

theorem hyperbolic_axis_of_offdiagonal_zero
    (F:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hF:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F≠1)
    (ht:4<(Matrix.trace F.val)^2) (hb:F 0 1=0) (hc:F 1 0=0) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis F hF ht=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 := by
  have hdet:=F.det_coe
  rw [Matrix.det_fin_two,hb,hc] at hdet
  have hd:F 1 1≠0:=by intro he;rw [he] at hdet;norm_num at hdet
  have hzero:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F).val ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)=((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex):=by
    rw [_root_.LowDimensionalTopology.Geometry.Fuchsian.axisSL_real_zero F hd,hb]
    simp
  have hinf:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F).val ∞=∞:=by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_real_infty,ite_eq_left hc]
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.idealEndpoints_injective
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints,_root_.LowDimensionalTopology.Geometry.Hyperbolic.vertical_idealEndpoints]
  ext z
  change (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    F).val z=z ↔ z∈{((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),∞}
  constructor
  · intro hz
    by_cases hz0:z=((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    · exact Or.inl hz0
    by_cases hzi:z=∞
    · exact Or.inr hzi
    exact False.elim (hF (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_eq_one_of_three_fixed
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F)
      ((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∞ z (OnePoint.coe_ne_infty (0:ℂ)) (Ne.symm
        hz0)
      (Ne.symm hzi) hzero hinf hz))
  · rintro (rfl|rfl)
    · exact hzero
    · exact hinf

theorem normalizer_axis_image :
    (boundaryNormalizer • · : ℍ→ℍ) ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticB
        orderFourDiagnosticB_hyperbolic.1.1
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
          orderFourDiagnosticB_hyperbolic.1.1).mp
          orderFourDiagnosticB_hyperbolic)).carrier=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
  have hb:=orderFourDiagnosticB_hyperbolic.1.1
  have ht:4<(Matrix.trace orderFourDiagnosticB.val)^2:=
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
      hb).mp orderFourDiagnosticB_hyperbolic
  have himage : ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticB hb
    ht).realGLMap
      (Matrix.SpecialLinearGroup.mapGL ℝ boundaryNormalizer)).carrier=
      (boundaryNormalizer • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticB hb ht).carrier := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    rfl
  rw [←himage,←_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_conjugation]
  rw [hyperbolic_axis_of_offdiagonal_zero _ _ _
    normalizer_conjugate_offdiagonal.1 normalizer_conjugate_offdiagonal.2]


/-- Every actual whole-group translate of A is equal or disjoint from B's axis. -/
theorem wholeGroup_translated_axis_or_disjoint
    (F:Matrix.SpecialLinearGroup (Fin 2) ℝ) (hF:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
      F∈modelGroup) :
    (F • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticB
        orderFourDiagnosticB_hyperbolic.1.1
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
          orderFourDiagnosticB_hyperbolic.1.1).mp
          orderFourDiagnosticB_hyperbolic)).carrier ∨
    Disjoint ((F • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticB
        orderFourDiagnosticB_hyperbolic.1.1
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
          orderFourDiagnosticB_hyperbolic.1.1).mp
          orderFourDiagnosticB_hyperbolic)).carrier := by
  have htrap (z:_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) (hz:z=((0:ℂ):_root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∨ z=∞) :
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius (boundaryNormalizer*F)).val z∈nonpositiveBoundary := by
    rw [map_mul]
    exact normalizer_trap ⟨_,wholeGroup_axis_endpoints_trap _ hF z hz,rfl⟩
  have hp:=nonpositive_endpoints_products (boundaryNormalizer*F)
    (htrap _ (Or.inl rfl)) (htrap _ (Or.inr rfl))
  have hcomp : (boundaryNormalizer • · : ℍ→ℍ) ''
      ((F • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier)=
      ((boundaryNormalizer*F) • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier := by
    rw [image_image]
    congr 1
    funext z
    exact (mul_smul boundaryNormalizer F z).symm
  by_cases he:((boundaryNormalizer*F) • · : ℍ→ℍ) ''
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical
        0).carrier=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier
  · left
    apply (isometry_smul ℍ boundaryNormalizer).injective.image_injective
    rw [hcomp,he,normalizer_axis_image]
  · right
    apply (Set.disjoint_image_iff (isometry_smul ℍ boundaryNormalizer).injective).mp
    rw [hcomp,normalizer_axis_image]
    apply Set.disjoint_left.mpr
    rintro z ⟨p,hpL,rfl⟩ hz
    have hn:=_root_.LowDimensionalTopology.Geometry.Fuchsian.axisSL_crossing_product_neg (boundaryNormalizer*F) he hpL hz
    exact not_lt_of_ge (mul_nonneg_of_nonpos_of_nonpos hp.1 hp.2) hn

/-- Literal cross-family-only noncrossing for the entire original actual group. -/
theorem modelGroup_crossFamily_noncrossing :
    _root_.LowDimensionalTopology.Geometry.Fuchsian.HyperbolicAxisFamiliesNoncrossing modelGroup
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticA
        orderFourDiagnosticA_hyperbolic.1.1
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
          orderFourDiagnosticA_hyperbolic.1.1).mp
          orderFourDiagnosticA_hyperbolic))
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticB
        orderFourDiagnosticB_hyperbolic.1.1
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
          orderFourDiagnosticB_hyperbolic.1.1).mp
          orderFourDiagnosticB_hyperbolic)) := by
  rw [show _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticA
    orderFourDiagnosticA_hyperbolic.1.1
      ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
        orderFourDiagnosticA_hyperbolic.1.1).mp
        orderFourDiagnosticA_hyperbolic)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0 from
      _root_.LowDimensionalTopology.Geometry.Fuchsian.hLogDilationSL_hyperbolic_axis (Real.log 3) (Real.log_pos (by norm_num)) _ _]
  intro F hF
  have hFi:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius F⁻¹∈modelGroup:=by rw [map_inv];exact modelGroup.inv_mem hF
  have himage (S:Set ℍ) : (F • · : ℍ→ℍ) '' ((F⁻¹ • · : ℍ→ℍ) '' S)=S := by
    rw [image_image]
    simp only [smul_inv_smul]
    exact Set.image_id S
  rcases wholeGroup_translated_axis_or_disjoint F⁻¹ hFi with he|hd
  · left
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.carrier_injective
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    exact (himage _).symm.trans (congrArg (Set.image (F • · : ℍ→ℍ)) he)
  · right
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    have hh:Disjoint ((F • · : ℍ→ℍ) ''
        ((F⁻¹ • · : ℍ→ℍ) '' (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier))
        ((F • · : ℍ→ℍ) '' _):=
      (Set.disjoint_image_iff (isometry_smul ℍ F).injective).mpr hd
    rwa [himage] at hh

theorem modelRotation_coe (z:ℍ) :
    ((orderFourDiagnosticRotation • z:ℍ):ℂ)=((z:ℂ)+1)/(1-(z:ℂ)) := by
  have hq:((Real.sqrt 2:ℝ):ℂ)≠0:=Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.2 (by norm_num : (0:ℝ)<2)).ne'
  have hz:1-(z:ℂ)≠0:=by
    intro he
    have him:=congrArg Complex.im he
    simp only [Complex.sub_im,Complex.one_im,UpperHalfPlane.coe_im,Complex.zero_im] at him
    linarith [z.im_pos]
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  norm_num [orderFourDiagnosticRotation,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL]
  field_simp [hq,hz]
  ring_nf
  field_simp [hz]
  ring

theorem modelRotation_center_images :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry orderFourDiagnosticRotation _root_.LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyDiscreteness.center=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (4/5) (3/5) (by norm_num) ∧
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      orderFourDiagnosticRotation)^2) _root_.LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyDiscreteness.center=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 3 (by norm_num) ∧
    ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
      orderFourDiagnosticRotation)^3) _root_.LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyDiscreteness.center=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (-4/5) (3/5) (by norm_num) := by
  have h1:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry orderFourDiagnosticRotation _root_.LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyDiscreteness.center=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (4/5) (3/5) (by norm_num):=by
    apply UpperHalfPlane.ext
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_apply,modelRotation_coe]
    apply Complex.ext <;>
      norm_num [_root_.LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyDiscreteness.center,_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.div_re,Complex.div_im,
        Complex.normSq_apply]
  have h2:((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry
    orderFourDiagnosticRotation)^2) _root_.LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyDiscreteness.center=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe 0 3 (by norm_num):=by
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry orderFourDiagnosticRotation
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry orderFourDiagnosticRotation
        _root_.LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyDiscreteness.center)=_
    rw [h1]
    apply UpperHalfPlane.ext
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_apply,modelRotation_coe]
    apply Complex.ext <;> norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.div_re,Complex.div_im,Complex.normSq_apply]
  refine ⟨h1,h2,?_⟩
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry orderFourDiagnosticRotation
    (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry orderFourDiagnosticRotation)^2)
      _root_.LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyDiscreteness.center)=_
  rw [h2]
  apply UpperHalfPlane.ext
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_apply,modelRotation_coe]
  apply Complex.ext <;> norm_num [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe,Complex.div_re,Complex.div_im,Complex.normSq_apply]

def modelNativeGroup : Subgroup (ℍ≃ᵢℍ) :=
  Subgroup.closure
    ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modelHalfTurn,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry orderFourDiagnosticRotation} : Set (ℍ≃ᵢℍ))

theorem modelNativeGroup_conformal : modelNativeGroup≤_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneConformalIsometryGroup := by
  apply (Subgroup.closure_le _).mpr
  rintro f (rfl|rfl)
  · exact ⟨modelHalfTurn,rfl⟩
  · exact ⟨orderFourDiagnosticRotation,rfl⟩

theorem modelNativeGroup_discrete : DiscreteTopology modelNativeGroup := by
  have he:_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry modelHalfTurn=_root_.LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyDiscreteness.halfTurn:=by
    rw [modelHalfTurn_eq,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry_neg]
    rfl
  have hgroup:modelNativeGroup=
      Subgroup.zpowers _root_.LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyDiscreteness.halfTurn ⊔
        Subgroup.zpowers (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry orderFourDiagnosticRotation) := by
    rw [Subgroup.zpowers_eq_closure,Subgroup.zpowers_eq_closure,←Subgroup.closure_union]
    change Subgroup.closure _=Subgroup.closure _
    congr 1
    ext f
    simp only [Set.mem_union,Set.mem_singleton_iff,Set.mem_insert_iff,he]
  rw [hgroup]
  exact _root_.LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyDiscreteness.actual_two_four_native_discrete _
    (by rw [←_root_.LowDimensionalTopology.Geometry.Fuchsian.realSLMobius_order_eq_native];exact orderFourDiagnosticRotation_order)
    modelRotation_center_images.1 modelRotation_center_images.2.1 modelRotation_center_images.2.2

theorem modelGroup_halfPlaneData : _root_.LowDimensionalTopology.Geometry.Fuchsian.HalfPlaneFuchsianGroup modelGroup := by
  let : DiscreteTopology modelNativeGroup:=modelNativeGroup_discrete
  have hP:=_root_.LowDimensionalTopology.Geometry.Fuchsian.nativeConformalSubgroup_halfPlaneData modelNativeGroup modelNativeGroup_conformal
  have he:=_root_.LowDimensionalTopology.Geometry.Fuchsian.native_matrix_pair_mobius_image modelHalfTurn orderFourDiagnosticRotation
    modelNativeGroup_conformal
  have he' : (_root_.LowDimensionalTopology.Geometry.Fuchsian.nativeConformalSubgroupMobiusHom modelNativeGroup
      modelNativeGroup_conformal).range=modelGroup := by
    simpa only [modelNativeGroup,modelGroup] using he
  exact he' ▸ hP

theorem modelGroup_hyperbolic_generators : modelGroup=
    Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticA,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticB}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) := by
  let K:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticA,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticB}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
  have hE:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius modelHalfTurn∈modelGroup:=Subgroup.subset_closure (by left;rfl)
  have hR:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticRotation∈modelGroup:=Subgroup.subset_closure (by right;rfl)
  have hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticA∈modelGroup:=by
    have hh:=modelGroup.mul_mem (modelGroup.inv_mem (modelGroup.pow_mem hR 2)) hE
    have hid:(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticRotation)^2 *
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticA=_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius modelHalfTurn:=by
      rw [←map_pow,←map_mul]
      rfl
    rw [←hid,inv_mul_cancel_left] at hh
    exact hh
  have hB:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticB∈modelGroup:=by
    rw [orderFourDiagnosticB,map_mul]
    exact modelGroup.mul_mem hR hA
  have hAK:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticA∈K:=Subgroup.subset_closure (by left;rfl)
  have hBK:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticB∈K:=Subgroup.subset_closure (by right;rfl)
  have hRK:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticRotation∈K:=by
    have hh:=K.mul_mem hBK (K.inv_mem hAK)
    rw [orderFourDiagnosticB,map_mul,mul_inv_cancel_right] at hh
    exact hh
  change modelGroup=K
  apply le_antisymm
  · apply (Subgroup.closure_le K).mpr
    rintro f (rfl|rfl)
    · rw [modelHalfTurn,map_mul,map_pow]
      exact K.mul_mem (K.pow_mem hRK 2) hAK
    · exact hRK
  · exact (Subgroup.closure_le modelGroup).mpr (by rintro f (rfl|rfl);exact hA;exact hB)

theorem modelGroup_nonElementary : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary modelGroup := by
  have hR:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticRotation∈modelGroup:=Subgroup.subset_closure (by right;rfl)
  have hA:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticA∈modelGroup:=by
    rw [modelGroup_hyperbolic_generators]
    exact Subgroup.subset_closure (by left;rfl)
  have hell:_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticRotation):=by
    have hn:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticRotation≠1:=by
      intro he
      have ho:=orderFourDiagnosticRotation_order
      rw [he,orderOf_one] at ho
      omega
    apply (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_elliptic_iff _ hn).mpr
    norm_num [orderFourDiagnosticRotation,_root_.LowDimensionalTopology.Geometry.Hyperbolic.hRotationSL,Matrix.trace_fin_two]
  intro hE
  let : Finite modelGroup:=_root_.LowDimensionalTopology.Geometry.Fuchsian.elementary_elliptic_noninvolution_finite
    modelGroup_halfPlaneData.asFuchsianDisc hE _ hR hell
    (by rw [orderFourDiagnosticRotation_order];decide)
  have ho:IsOfFinOrder (⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius
    orderFourDiagnosticA,hA⟩:modelGroup):=isOfFinOrder_of_finite _
  obtain ⟨n,hn,he⟩:=ho.exists_pow_eq_one
  have hfin:IsOfFinOrder (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticA):=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨n,hn,congrArg Subtype.val he⟩
  exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_parabolic_or_loxodromic_not_isOfFinOrder _
    (Or.inr orderFourDiagnosticA_hyperbolic.1) hfin

/-- The same literal whole group has a real self-family transverse crossing. -/
theorem modelGroup_self_family_crosses :
    ¬_root_.LowDimensionalTopology.Geometry.Fuchsian.HyperbolicAxisFamiliesNoncrossing modelGroup (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0)
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0) := by
  intro h
  have hR:_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticRotation∈modelGroup:=
    Subgroup.subset_closure (by right;rfl)
  have hfix:orderFourDiagnosticRotation • UpperHalfPlane.I=UpperHalfPlane.I:=by
    apply UpperHalfPlane.ext
    rw [modelRotation_coe]
    apply Complex.ext <;> norm_num [UpperHalfPlane.coe_I,Complex.div_re,Complex.div_im,
      Complex.normSq_apply]
  rcases h orderFourDiagnosticRotation hR with he|hd
  · have hcenter:_root_.LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyDiscreteness.center∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier:=by
      change (0:ℝ)=0
      rfl
    have him:orderFourDiagnosticRotation • _root_.LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyDiscreteness.center∈
        ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).realGLMap
          (Matrix.SpecialLinearGroup.mapGL ℝ orderFourDiagnosticRotation)).carrier:=by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
      exact mem_image_of_mem _ hcenter
    rw [←he] at him
    have hec:orderFourDiagnosticRotation • _root_.LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyDiscreteness.center=
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe (4/5) (3/5) (by norm_num):=modelRotation_center_images.1
    rw [hec] at him
    change (4/5:ℝ)=0 at him
    norm_num at him
  · apply Set.disjoint_left.mp hd (show
    UpperHalfPlane.I∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.vertical 0).carrier from rfl)
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.realGLMap_carrier]
    exact ⟨UpperHalfPlane.I,rfl,hfix⟩

/-- The strictly cross-family-only reading does not imply the proposed weak bound:
the literal two hyperbolics generate a genuine discrete non-elementary group,
their two whole-group axis families do not cross, and their exact gap is larger
than one half. All group and noncrossing hypotheses are proved above. -/
theorem actual_crossFamily_weak_bound_counterexample :
    let G:=Subgroup.closure ({_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticA,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticB}:Set _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup G ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary G ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticA) ∧
      _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius orderFourDiagnosticB) ∧
      _root_.LowDimensionalTopology.Geometry.Fuchsian.HyperbolicAxisFamiliesNoncrossing G
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticA
          orderFourDiagnosticA_hyperbolic.1.1
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
            orderFourDiagnosticA_hyperbolic.1.1).mp
            orderFourDiagnosticA_hyperbolic))
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticB
          orderFourDiagnosticB_hyperbolic.1.1
          ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
            orderFourDiagnosticB_hyperbolic.1.1).mp
            orderFourDiagnosticB_hyperbolic)) ∧
      (1:ℝ)/2<Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
        (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry orderFourDiagnosticA)/2)*
          Real.cosh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
            (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry orderFourDiagnosticB)/2)-
        Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength
          (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry orderFourDiagnosticA)/2)*
          Real.cosh ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticA
            orderFourDiagnosticA_hyperbolic.1.1
            ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
              orderFourDiagnosticA_hyperbolic.1.1).mp
              orderFourDiagnosticA_hyperbolic)).lineDist
            (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis orderFourDiagnosticB
              orderFourDiagnosticB_hyperbolic.1.1
            ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff _
              orderFourDiagnosticB_hyperbolic.1.1).mp
              orderFourDiagnosticB_hyperbolic)))*
          Real.sinh (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hTranslationLength (_root_.LowDimensionalTopology.Geometry.Hyperbolic.hSLIsometry orderFourDiagnosticB)/2) := by
  dsimp only
  rw [←modelGroup_hyperbolic_generators]
  refine ⟨modelGroup_halfPlaneData.discrete,modelGroup_nonElementary,
    orderFourDiagnosticA_hyperbolic,orderFourDiagnosticB_hyperbolic,
    modelGroup_crossFamily_noncrossing,?_⟩
  rw [orderFourDiagnostic_metric_gap]
  exact orderFourDiagnostic_gap_gt_half

end LowDimensionalTopology.Geometry.Fuchsian.CrossFamilyCounterexample
