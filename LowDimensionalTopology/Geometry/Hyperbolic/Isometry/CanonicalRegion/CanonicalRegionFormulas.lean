/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.CanonicalRegions.CanonicalGeometry
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicHalfTurns
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Inversive LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The original analytic formula, with the already defined order-two exception explicit. -/
theorem canonical_region_analytic (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hn : realSLMobius A≠1) (ho : orderOf (realSLMobius A)≠2) :
    hCanonicalRegion A={z : ℍ | hSinhDisplacement (hSLIsometry A) z< |Matrix.trace A.val|/2} :=
  hCanonicalRegion_of_order_ne_two A hn ho

/-- The canonical-region identity holds for every actual parabolic transformation. -/
theorem canonical_region_parabolic (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusParabolic (realSLMobius A)) :
    hCanonicalRegion A={z : ℍ | hSinhDisplacement (hSLIsometry A) z<1} := by
  have ht:=(realSLMobius_parabolic_iff A hA.1).mp hA
  have hn : Matrix.trace A.val≠0 := by intro he;rw [he] at ht;norm_num at ht
  have ha : |Matrix.trace A.val|=2 := by nlinarith [abs_nonneg (Matrix.trace A.val),sq_abs (Matrix.trace A.val)]
  rw [hCanonicalRegion_of_trace_ne_zero A hn]
  ext z
  change Real.sinh (dist z (A•z)/2)< |Matrix.trace A.val|/2 ↔
    Real.sinh (dist z (A•z)/2)<1
  rw [ha]
  norm_num

/-- The strict cosh and sinh strip inequalities are exactly equivalent. -/
theorem canonical_strip_scalar (d t : ℝ) (hd : 0≤d) (ht : 0<t) :
    Real.cosh d*Real.sinh t<Real.cosh t ↔ Real.sinh d*Real.sinh t<1 := by
  have ha : 0≤Real.cosh d*Real.sinh t := mul_nonneg (Real.cosh_pos d).le (Real.sinh_nonneg_iff.mpr ht.le)
  have hb : 0≤Real.sinh d*Real.sinh t := mul_nonneg (Real.sinh_nonneg_iff.mpr hd) (Real.sinh_nonneg_iff.mpr ht.le)
  have he : (Real.cosh d*Real.sinh t)^2-(Real.cosh t)^2=
      (Real.sinh d*Real.sinh t)^2-1 := by
    linear_combination (Real.sinh t)^2*(Real.cosh_sq_sub_sinh_sq d)-
      (Real.cosh_sq_sub_sinh_sq t)
  constructor
  · intro h
    have hs:=(sq_lt_sq₀ ha (Real.cosh_pos t).le).mpr h
    nlinarith [sq_nonneg (Real.sinh d*Real.sinh t-1)]
  · intro h
    have hs:=(sq_lt_sq₀ hb (by norm_num : (0:ℝ)≤1)).mpr h
    apply (sq_lt_sq₀ ha (Real.cosh_pos t).le).mp
    nlinarith [he,hs]

/-- The canonical-region formulas use the genuine invariant axis and translation infimum. -/
theorem canonical_region_hyperbolic (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hA : Mobius.MobiusHyperbolic (realSLMobius A)) :
    let ht:=(realSLMobius_hyperbolic_iff A hA.1.1).mp hA
    let L:=hHyperbolicAxis A hA.1.1 ht
    let T:=hTranslationLength (hSLIsometry A)/2
    hCanonicalRegion A={z : ℍ | Real.sinh (L.pointDist z)*Real.sinh T<1} ∧
      ∀ z : ℍ,hSinhDisplacement (hSLIsometry A) z=Real.cosh (L.pointDist z)*Real.sinh T := by
  dsimp only
  let ht:=(realSLMobius_hyperbolic_iff A hA.1.1).mp hA
  have hn : Matrix.trace A.val≠0 := by intro he;rw [he] at ht;norm_num at ht
  have hT : 0<hTranslationLength (hSLIsometry A)/2 := by
    linarith [hHyperbolic_translationLength_pos A hA.1.1 ht]
  refine ⟨?_,hyperbolic_half_displacement A hA.1.1 ht⟩
  rw [hCanonicalRegion_of_trace_ne_zero A hn]
  ext z
  change Real.sinh (dist z (A•z)/2)< |Matrix.trace A.val|/2 ↔ _
  rw [hyperbolic_half_displacement A hA.1.1 ht,hHyperbolic_translation_abs_trace A hA.1.1 ht]
  exact canonical_strip_scalar _ _ Metric.infDist_nonneg hT

/-- At order two the actual canonical region is its singleton center, whereas the displayed
strict trace inequality is empty. This is the necessary inherited exception to the source formula. -/
theorem canonical_region_halfturn_exception (A : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (p : ℍ) (hA : IsHalfTurnAt A p) :
    hCanonicalRegion A={p} ∧
      {z : ℍ | hSinhDisplacement (hSLIsometry A) z< |Matrix.trace A.val|/2}=∅ := by
  have ht:=(realSLMobius_order_two_iff_trace_zero A hA.ne_one).mp hA.1
  refine ⟨?_,?_⟩
  · rw [hCanonicalRegion_halfTurn A ht,←(hSL_trace_zero_fixed_iff A ht p).mp hA.2]
  · apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    rw [ht] at hz
    norm_num only [abs_zero,zero_div,Set.mem_ofPred_eq] at hz
    exact (hSinhDisplacement_nonneg (hSLIsometry A) z).not_gt hz

end LowDimensionalTopology.Geometry.Hyperbolic
