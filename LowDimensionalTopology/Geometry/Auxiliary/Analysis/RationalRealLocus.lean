/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.Complex.OpenMapping
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Push

/-!
# Real loci of nonconstant rational functions

A nonzero bivariate complex polynomial vanishes on a null subset of the real
coordinate plane. Applying this to the rational real-value equation proves that
a nonconstant rational function is real-valued only on a set of complex volume zero.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory Filter Polynomial
open scoped ENNReal Topology
namespace LowDimensionalTopology.Geometry.Auxiliary.Analysis

def complexBivariateEval (P : Polynomial (Polynomial ℂ)) (x y : ℝ) : ℂ:=
  (P.map (Polynomial.evalRingHom (y:ℂ))).eval (x:ℂ)

theorem complexBivariateEval_continuous (P : Polynomial (Polynomial ℂ)) :
    Continuous (fun u : ℝ×ℝ=>complexBivariateEval P u.2 u.1) := by
  simp only [complexBivariateEval,Polynomial.eval_map,Polynomial.eval₂_eq_sum,Polynomial.sum,Polynomial.coe_evalRingHom]
  fun_prop

theorem complex_polynomial_real_roots_finite (p : Polynomial ℂ) (hp : p≠0) :
    {x : ℝ | p.eval (x:ℂ)=0}.Finite := by
  have h : {z : ℂ | p.eval z=0}.Finite:=Polynomial.finite_setOfPred_isRoot hp
  exact h.preimage Complex.ofReal_injective.injOn

theorem complexBivariateEval_ae_ne_zero (P : Polynomial (Polynomial ℂ)) (hP : P≠0) :
    ∀ᵐ u : ℝ×ℝ ∂volume.prod volume,complexBivariateEval P u.2 u.1≠0 := by
  have hex : ∃i,P.coeff i≠0:=by
    by_contra hn
    push Not at hn
    apply hP
    apply Polynomial.ext
    intro i
    simpa only [Polynomial.coeff_zero] using hn i
  obtain ⟨i,hi⟩:=hex
  apply (MeasureTheory.Measure.ae_prod_iff_ae_ae
    (isClosed_eq (complexBivariateEval_continuous P) continuous_const).measurableSet.compl).mpr
  have hy : ∀ᵐ y : ℝ ∂volume,(P.coeff i).eval (y:ℂ)≠0:=by
    simpa only [Set.mem_ofPred_eq] using
      (complex_polynomial_real_roots_finite (P.coeff i) hi).countable.ae_notMem volume
  filter_upwards [hy] with y hy
  have hPy : P.map (Polynomial.evalRingHom (y:ℂ))≠0:=by
    intro he
    have hc:=congrArg (fun p : Polynomial ℂ=>p.coeff i) he
    simp only [Polynomial.coeff_map,Polynomial.coeff_zero] at hc
    exact hy hc
  simpa only [complexBivariateEval,Set.mem_ofPred_eq] using
    (complex_polynomial_real_roots_finite _ hPy).countable.ae_notMem volume


def complexPlaneVariable : Polynomial (Polynomial ℂ):=
  C (X : Polynomial ℂ)+C (C Complex.I)*X

def complexPlaneConjugateVariable : Polynomial (Polynomial ℂ):=
  C (X : Polynomial ℂ)-C (C Complex.I)*X

theorem complexBivariateEval_lift_comp (p : Polynomial ℂ) (W : Polynomial (Polynomial ℂ)) (x y : ℝ) :
    complexBivariateEval ((p.map Polynomial.C).comp W) x y=p.eval (complexBivariateEval W x y) := by
  simp only [complexBivariateEval,Polynomial.map_comp,Polynomial.eval_comp,Polynomial.map_map]
  have he : (Polynomial.evalRingHom (y:ℂ)).comp (Polynomial.C : ℂ→+*Polynomial ℂ)=RingHom.id ℂ:=by
    ext c
    simp
  rw [he,Polynomial.map_id]

theorem complexBivariateEval_plane (z : ℂ) :
    complexBivariateEval complexPlaneVariable z.im z.re=z := by
  simp only [complexBivariateEval,complexPlaneVariable,Polynomial.map_add,Polynomial.map_C,
    Polynomial.map_mul,Polynomial.map_X,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X,
    Polynomial.eval_mul,Polynomial.coe_evalRingHom]
  rw [mul_comm Complex.I]
  exact Complex.re_add_im z

theorem complexBivariateEval_conjugatePlane (z : ℂ) :
    complexBivariateEval complexPlaneConjugateVariable z.im z.re=starRingEnd ℂ z := by
  simp [complexBivariateEval,complexPlaneConjugateVariable]
  apply Complex.ext <;> simp

theorem polynomial_conjugate_eval (p : Polynomial ℂ) (z : ℂ) :
    (p.map (starRingEnd ℂ)).eval (starRingEnd ℂ z)=starRingEnd ℂ (p.eval z) := by
  rw [Polynomial.eval_map]
  exact Polynomial.eval₂_at_apply _ _

def rationalRealEquation (p q : Polynomial ℂ) : Polynomial (Polynomial ℂ):=
  ((p.map Polynomial.C).comp complexPlaneVariable)*
    (((q.map (starRingEnd ℂ)).map Polynomial.C).comp complexPlaneConjugateVariable)-
  (((p.map (starRingEnd ℂ)).map Polynomial.C).comp complexPlaneConjugateVariable)*
    ((q.map Polynomial.C).comp complexPlaneVariable)

theorem rationalRealEquation_eval (p q : Polynomial ℂ) (z : ℂ) :
    complexBivariateEval (rationalRealEquation p q) z.im z.re=
      p.eval z*starRingEnd ℂ (q.eval z)-starRingEnd ℂ (p.eval z)*q.eval z := by
  have hmul (A B : Polynomial (Polynomial ℂ)) :
      complexBivariateEval (A*B) z.im z.re=complexBivariateEval A z.im z.re*complexBivariateEval B z.im z.re:=by
    simp only [complexBivariateEval,Polynomial.map_mul,Polynomial.eval_mul]
  have hsub (A B : Polynomial (Polynomial ℂ)) :
      complexBivariateEval (A-B) z.im z.re=complexBivariateEval A z.im z.re-complexBivariateEval B z.im z.re:=by
    simp only [complexBivariateEval,Polynomial.map_sub,Polynomial.eval_sub]
  rw [rationalRealEquation,hsub,hmul,hmul]
  simp only [complexBivariateEval_lift_comp,complexBivariateEval_plane,
    complexBivariateEval_conjugatePlane,polynomial_conjugate_eval]


theorem complex_div_im_zero_iff_cross (a b : ℂ) :
    (a/b).im=0 ↔ a*starRingEnd ℂ b-starRingEnd ℂ a*b=0 := by
  have hc : a*starRingEnd ℂ b-starRingEnd ℂ a*b=0 ↔ a.im*b.re-a.re*b.im=0:=by
    constructor
    · intro he
      have hi:=congrArg Complex.im he
      simp [Complex.mul_im] at hi
      nlinarith
    · intro h
      apply Complex.ext
      · simp [Complex.mul_re]
      · simp [Complex.mul_im]
        nlinarith
  rw [hc,Complex.div_im,←sub_div]
  by_cases hb : b=0
  · subst b
    simp
  · have hn : Complex.normSq b≠0:=by
      intro hz
      exact hb (Complex.normSq_eq_zero.mp hz)
    exact div_eq_zero_iff.trans (or_iff_left hn)

theorem rational_nonconstant_has_nonreal_value (p q : Polynomial ℂ) (hq : q≠0)
    (hnonconstant : ¬∃c : ℂ,p=C c*q) : ∃z : ℂ,(p.eval z/q.eval z).im≠0 := by
  by_contra hn
  push Not at hn
  obtain ⟨z₀,hz₀⟩:=(Polynomial.finite_setOfPred_isRoot hq).exists_notMem
  have hz₀q : q.eval z₀≠0:=hz₀
  have hN : {z : ℂ | q.eval z≠0}∈𝓝 z₀:=(isClosed_eq q.continuous continuous_const).isOpen_compl.mem_nhds hz₀q
  obtain ⟨r,hr,hball⟩:=Metric.mem_nhds_iff.mp hN
  have hR : AnalyticOnNhd ℂ (fun z : ℂ=>p.eval z/q.eval z) (Metric.ball z₀ r):=by
    intro z hz
    exact ((AnalyticOnNhd.eval_polynomial p) z (mem_univ z)).div
      ((AnalyticOnNhd.eval_polynomial q) z (mem_univ z)) (hball hz)
  obtain ⟨c,hc⟩:=hR.eq_const_of_im_eq_const (fun z _=>hn z) Metric.isOpen_ball
    ((convex_ball z₀ r).isConnected (Metric.nonempty_ball.mpr hr))
  have hevent : ∀ᶠ z in 𝓝 z₀,(p-C c*q).eval z=0:=by
    filter_upwards [Metric.ball_mem_nhds z₀ hr] with z hz
    rw [Polynomial.eval_sub,Polynomial.eval_mul,Polynomial.eval_C]
    exact sub_eq_zero.mpr ((div_eq_iff (hball hz)).mp (hc z hz))
  have hall:=((AnalyticOnNhd.eval_polynomial (p-C c*q) :
    AnalyticOnNhd ℂ (fun z : ℂ=>(p-C c*q).eval z) univ)).eqOn_of_preconnected_of_eventuallyEq
      analyticOnNhd_const isPreconnected_univ (mem_univ z₀) hevent
  have hpoly : p-C c*q=0:=by
    apply Polynomial.funext
    intro z
    simpa only [Polynomial.eval_zero] using hall (mem_univ z)
  exact hnonconstant ⟨c,sub_eq_zero.mp hpoly⟩

theorem rationalRealEquation_ne_zero (p q : Polynomial ℂ) (hq : q≠0)
    (hnonconstant : ¬∃c : ℂ,p=C c*q) : rationalRealEquation p q≠0 := by
  intro hzero
  obtain ⟨z,hz⟩:=rational_nonconstant_has_nonreal_value p q hq hnonconstant
  apply hz
  apply (complex_div_im_zero_iff_cross _ _).mpr
  rw [←rationalRealEquation_eval,hzero]
  simp [complexBivariateEval]


/--
For genuine nonconstant complex rational functions.
The total quotient convention at polynomial denominator zeros is included.
-/
theorem rational_real_locus_volume_zero (p q : Polynomial ℂ) (hq : q≠0)
    (hnonconstant : ¬∃c : ℂ,p=C c*q) :
    volume {z : ℂ | (p.eval z/q.eval z).im=0}=0 := by
  let P:=rationalRealEquation p q
  have hP : P≠0:=rationalRealEquation_ne_zero p q hq hnonconstant
  have hpair:=complexBivariateEval_ae_ne_zero P hP
  have hm : Measure.map Complex.measurableEquivRealProd (volume : Measure ℂ)=
      (volume : Measure ℝ).prod volume:=Complex.volume_preserving_equiv_real_prod.map_eq
  have hmap : ∀ᵐu : ℝ×ℝ ∂Measure.map Complex.measurableEquivRealProd (volume : Measure ℂ),
      complexBivariateEval P u.2 u.1≠0:=by
    rw [hm]
    exact hpair
  have hZ:=MeasureTheory.ae_of_ae_map Complex.measurableEquivRealProd.measurable.aemeasurable hmap
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hZ] with z hz hr
  apply hz
  change complexBivariateEval (rationalRealEquation p q) z.im z.re=0
  rw [rationalRealEquation_eval]
  exact (complex_div_im_zero_iff_cross _ _).mp hr

end LowDimensionalTopology.Geometry.Auxiliary.Analysis
