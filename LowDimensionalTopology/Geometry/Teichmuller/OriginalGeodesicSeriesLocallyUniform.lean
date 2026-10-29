module

public import LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeriesRealMobius
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistPeterssonSeriesReflection
public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistOriginalCollarSupport
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Order.Filter.AtTopBot.Finset

/-!
# Local uniform convergence for the original simple geodesic series

An original simple geodesic supplies its actual full-period covering matrix
and a normalized angular collar. The already convergent normalized series is
transported by the actual right-coset equivalence and the same real Möbius
map. Finite partial sums transform term by term; continuous division by the
nonzero fourth denominator preserves local uniform convergence.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeries

open Surfaces GammaMeasurableBeltrami

private theorem squaredLogDerivative_continuousOn (B : Deck) :
    ContinuousOn (fun w : ℂ =>
      (deriv (LiZhongQC.h36p_m B) w / LiZhongQC.h36p_m B w) ^ 2) LiZhongQC.upperHalf := by
  have hmob : ContinuousOn (LiZhongQC.h36p_m B) LiZhongQC.upperHalf :=
    fun _ hz => (LiZhongQC.h36p_m_hasDerivAt B hz).continuousAt.continuousWithinAt
  have hden : Continuous (fun w : ℂ => ((B 1 0 : ℂ) * w + B 1 1) ^ 2) := by
    fun_prop
  have hd : ContinuousOn (deriv (LiZhongQC.h36p_m B)) LiZhongQC.upperHalf := by
    apply (continuousOn_const.div hden.continuousOn
      (fun z hz => pow_ne_zero _ (denominator_ne_zero B ⟨z, hz⟩))).congr
    intro z hz
    exact (LiZhongQC.h36p_m_hasDerivAt B hz).deriv
  have hm0 : ∀ z ∈ LiZhongQC.upperHalf, LiZhongQC.h36p_m B z ≠ 0 := by
    intro z hz he
    have him := LiZhongQC.h36p_m_mem B hz
    change 0 < (LiZhongQC.h36p_m B z).im at him
    simp only [he, Complex.zero_im, lt_self_iff_false] at him
  exact (hd.div hmob hm0).pow 2

/-- The original simple geodesic has a full-period covering whose actual
endpoint series converges locally uniformly for every original coset section. -/
theorem originalClosedGeodesic_exists_locallyUniform_petersson
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {M : HyperbolicSurfaceModel R.toRiemannSurface} (q : OriginalClosedGeodesic M)
    {Γ : Subgroup Deck}
    (hp : let := R.toRiemannAtlas.toChartedSpace;
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (hcircle : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) :
    ∃ (A : Deck) (hA : Hyperbolic.realSLMobius A ≠ 1)
      (ht : 4 < (Matrix.trace A.val) ^ 2), A ∈ Γ ∧
      LiZhongQC.Covers M.halfPlaneCover A q.toLoop ∧
      let SA := Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
        (Subgroup.zpowers (Hyperbolic.realSLMobius A))
      let CA := Quotient (QuotientGroup.rightRel SA)
      ∀ (ρ : CA → Γ), (∀ u : CA, Quotient.mk _ (ρ u) = u) →
        TendstoLocallyUniformlyOn
          (fun (E : Finset CA) (z : ℂ) => ∑ u ∈ E,
            seed (Hyperbolic.hHyperbolicAxis A hA ht) (LiZhongQC.h36p_m (ρ u).val z) *
              (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2)
          (fun z : ℂ => ∑' u : CA,
            seed (Hyperbolic.hHyperbolicAxis A hA ht) (LiZhongQC.h36p_m (ρ u).val z) *
              (deriv (LiZhongQC.h36p_m (ρ u).val) z) ^ 2)
          (atTop : Filter (Finset CA)) LiZhongQC.upperHalf := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  obtain ⟨A, Q, s, hs, hAΓ, hcov, hQA, hsep⟩ :=
    AngularTwist.originalClosedGeodesic_exists_normalized_angular_one_support q hp hcircle
  let k : ℂˣ := Units.mk0 (Real.exp (2 * s) : ℂ)
    (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  have hlam : 1 < Real.exp (2 * s) := Real.one_lt_exp_iff.mpr (mul_pos zero_lt_two hs)
  have hk1 : (k : ℂ) ≠ 1 := by
    change (Real.exp (2 * s) : ℂ) ≠ 1
    exact_mod_cast (ne_of_gt hlam)
  have hn : Hyperbolic.realSLMobius (Q * A * Q⁻¹) = Mobius.mobiusStandardElement k :=
    hQA.trans ((Fuchsian.realSLMobius_logDilation s).trans
      ((Fuchsian.realSLMobius_verticalDilation (Real.exp (2 * s)) (Real.exp_pos _)).trans
        (DiscreteGroups.mobiusScaling_eq_standard k hk1)))
  have hnorm : Mobius.MobiusHyperbolic (Hyperbolic.realSLMobius (Q * A * Q⁻¹)) := by
    rw [hn]
    apply Mobius.mobiusStandardElement_positive_isHyperbolic k
    · exact Complex.ofReal_im _
    · exact Real.exp_pos _
    · change ‖(Real.exp (2 * s) : ℂ)‖ ≠ 1
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact ne_of_gt hlam
  have hhyper : Mobius.MobiusHyperbolic (Hyperbolic.realSLMobius A) :=
    (Mobius.mobiusHyperbolic_conjugation (Hyperbolic.realSLMobius A)
      (Hyperbolic.realSLMobius Q)).mp (by simpa only [map_mul, map_inv] using hnorm)
  let hA := hhyper.1.1
  let ht := (Hyperbolic.realSLMobius_hyperbolic_iff A hA).mp hhyper
  refine ⟨A, hA, ht, hAΓ, hcov, ?_⟩
  dsimp only
  intro ρ hρ
  let ΓQ := LiZhongQC.conjGroup Γ Q
  let pQ := LiZhongQC.adjustProjection M.halfPlaneCover Q
  have hpQ : LiZhongQC.IsUniformization ΓQ pQ := LiZhongQC.adjustProjection_isUniformization hp Q
  have hcount : (ΓQ : Set Deck).Countable :=
    LiZhongQC.h36p_countable (LiZhongQC.utm_x2_isFuchsian hpQ)
  let : Countable ΓQ := hcount.to_subtype
  let SA := Subgroup.comap (Hyperbolic.realSLMobius.comp Γ.subtype)
    (Subgroup.zpowers (Hyperbolic.realSLMobius A))
  let CA := Quotient (QuotientGroup.rightRel SA)
  let CQ := Quotient (QuotientGroup.rightRel (AngularTwist.projectiveDilationSubgroup ΓQ s))
  obtain ⟨e, ρQ, _hmk, hρtransport, hρQ, hseries⟩ :=
    geodesicSeries_realMobius_conjugate Γ A hA ht Q s hs hQA ρ hρ
  let termQ : CQ → ℂ → ℂ := fun v w =>
    (deriv (LiZhongQC.h36p_m (ρQ v).val) w / LiZhongQC.h36p_m (ρQ v).val w) ^ 2
  let ΘQ : ℂ → ℂ := fun w => ∑' v : CQ, termQ v w
  obtain ⟨_hpoint, hlocal⟩ := AngularTwist.rightCosetPeterssonSeries_upperHalf
    (AngularTwist.canonicalBandWidth s hs) ΓQ s hsep ρQ hρQ
  have hefin : Tendsto (fun E : Finset CA => E.image e) atTop atTop :=
    tendsto_finset_image_atTop_atTop (i := e.symm) (j := e) e.apply_symm_apply
  have hlocalE : TendstoLocallyUniformlyOn
      (fun (E : Finset CA) (w : ℂ) => ∑ v ∈ E.image e, termQ v w)
      ΘQ atTop LiZhongQC.upperHalf := by
    intro U hU w hw
    obtain ⟨T, hT, h⟩ := hlocal U hU w hw
    exact ⟨T, hT, hefin.eventually h⟩
  have hΘQcont : ContinuousOn ΘQ LiZhongQC.upperHalf := by
    apply hlocal.continuousOn
    exact (Eventually.of_forall fun E =>
      continuousOn_finsetSum E (fun v _hv => squaredLogDerivative_continuousOn (ρQ v).val)).frequently
  have hQcont : ContinuousOn (LiZhongQC.h36p_m Q) LiZhongQC.upperHalf :=
    fun _ hz => (LiZhongQC.h36p_m_hasDerivAt Q hz).continuousAt.continuousWithinAt
  have hmap : MapsTo (LiZhongQC.h36p_m Q) LiZhongQC.upperHalf LiZhongQC.upperHalf :=
    fun _ hz => LiZhongQC.h36p_m_mem Q hz
  have hpre := hlocalE.comp (LiZhongQC.h36p_m Q) hmap hQcont
  let d : ℂ → ℂ := fun z => ((Q 1 0 : ℂ) * z + Q 1 1) ^ 4
  have hdcont : ContinuousOn d LiZhongQC.upperHalf := by fun_prop
  have hd0 : ∀ z ∈ LiZhongQC.upperHalf, d z ≠ 0 :=
    fun z hz => pow_ne_zero _ (denominator_ne_zero Q ⟨z, hz⟩)
  have hconstant : TendstoLocallyUniformlyOn (fun _ : Finset CA => d) d atTop
      LiZhongQC.upperHalf := by
    intro U hU z _hz
    exact ⟨LiZhongQC.upperHalf, self_mem_nhdsWithin,
      Eventually.of_forall fun _ _ _ => refl_mem_uniformity hU⟩
  have hdiv := hpre.div₀ hconstant (hΘQcont.comp hQcont hmap) hdcont hd0
  refine (hdiv.congr ?_).congr_right ?_
  · intro E z hz
    change (∑ v ∈ E.image e, termQ v (LiZhongQC.h36p_m Q z)) / d z = _
    rw [Finset.sum_image e.injective.injOn, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro u _hu
    rw [show termQ (e u) (LiZhongQC.h36p_m Q z) =
      (deriv (LiZhongQC.h36p_m (ρQ (e u)).val) (LiZhongQC.h36p_m Q z) /
        LiZhongQC.h36p_m (ρQ (e u)).val (LiZhongQC.h36p_m Q z)) ^ 2 from rfl,
      hρtransport]
    exact (normalized_term A hA ht Q s hs hQA (ρ u).val hz).symm
  · intro z hz
    exact (hseries z hz).symm

end LowDimensionalTopology.Geometry.Teichmuller.GeodesicSeries
