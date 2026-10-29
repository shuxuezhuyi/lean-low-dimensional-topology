module

public import LowDimensionalTopology.Geometry.Surfaces.SimpleGeodesicIterates
public import LowDimensionalTopology.Geometry.Surfaces.ShortSimpleGeodesicCounting
public import LowDimensionalTopology.Geometry.Surfaces.PeriodicFreeClassReduction
public import LowDimensionalTopology.Geometry.Surfaces.EssentialSimpleCircleRangeClass
public import LowDimensionalTopology.Geometry.Teichmuller.CircleNullHomotopyDescent
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A geodesic length bound for irreducible quasiconformal maps

An orbit of simple geodesic representatives which stayed below the short
geodesic cutoff would contain a repeated geometric image. Its actual
free-class period supplies a disjoint admissible multicurve and hence a
reduction. The independent simple-representative, cardinality, circle, and
straightening inputs remain explicit.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped unitInterval

namespace LowDimensionalTopology.Geometry.Surfaces

open LowDimensionalTopology.Geometry.Teichmuller

private theorem original_geodesic_has_essential_circle
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (M : HyperbolicSurfaceModel R.toRiemannSurface) (q : OriginalClosedGeodesic M)
    (hq : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) :
    ∃ c : EssentialSimpleCircle X,
      range c.val = range q.curve ∧
        LiZhongQC.FreelyHomotopic (circleRepresentativeLoop c.val) q.toLoop := by
  let := R.compactSpace
  let e : AddCircle (1 : ℝ) ≃ₜ Circle := AddCircle.homeomorphCircle one_ne_zero
  have hcont : Continuous (q.periodic.lift : AddCircle (1 : ℝ) → X) :=
    continuous_coinduced_dom.2 q.continuous
  let c : C(Circle, X) :=
    ⟨fun z => q.periodic.lift (e.symm z), hcont.comp e.symm.continuous⟩
  have hexp (t : unitInterval) : e ((t : ℝ) : AddCircle (1 : ℝ)) = Circle.expLoop t := by
    dsimp only [e]
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_apply_mk, Circle.expLoop_apply]
    simp only [div_one]
  have hfree : LiZhongQC.FreelyHomotopic (circleRepresentativeLoop c) q.toLoop := by
    apply LiZhongQC.s30b_fh_of_eq
    intro t
    change q.periodic.lift (e.symm (Circle.expLoop t)) = q.curve (t : ℝ)
    simpa only [← hexp t, e.symm_apply_apply] using q.periodic.lift_coe (t : ℝ)
  have hrange : range c = range q.curve := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      have hmem (w : AddCircle (1 : ℝ)) : q.periodic.lift w ∈ range q.curve := by
        induction w using QuotientAddGroup.induction_on with
        | H t => exact ⟨t, rfl⟩
      exact hmem (e.symm z)
    · rintro ⟨t, rfl⟩
      refine ⟨e (t : AddCircle (1 : ℝ)), ?_⟩
      change q.periodic.lift (e.symm (e (t : AddCircle (1 : ℝ)))) = q.curve t
      simpa only [e.symm_apply_apply] using q.periodic.lift_coe t
  have hnon : ¬ c.Nullhomotopic := by
    intro hc
    obtain ⟨x, hx⟩ := circleRepresentativeLoop_null_of_null hc
    exact q.not_isNullHomotopicLoop
      ⟨x, LiZhongQC.s30b_fh_trans (LiZhongQC.s30b_fh_symm hfree) hx⟩
  exact ⟨⟨c, hq.comp e.symm.injective, hnon⟩, hrange, hfree⟩

/-- The full-period length of any actual simple closed geodesic bounds the
same supplied QC constant of an original irreducible homeomorphism. -/
theorem shortCutoff_le_pow_mul_length_of_irreducible
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (hSimple : LowDimensionalTopology.Unproved.Surfaces.SimpleClosedGeodesicRepresentatives R g M)
    (hCard : LowDimensionalTopology.Unproved.Surfaces.ClosedDecomposingSystemCardinalities
      R hg hgenus M)
    (hCircle : LowDimensionalTopology.Unproved.Topology.CircleHomeomorphHomotopyDichotomy)
    (hStraight : LowDimensionalTopology.Unproved.Surfaces.SimultaneousAdmissibleCurveStraightening
      R g)
    (f : X ≃ₜ X) {K : ℝ}
    (hf : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsKQCRS f K)
    (hirred : IsIrreducible f) (q : OriginalClosedGeodesic M)
    (hq : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) :
    shortClosedGeodesicCutoff ≤ K ^ (3 * g - 3) * q.length.toReal := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.compactSpace
  let : T2Space X := R.t2Space
  by_contra hnot
  have hsmall : K ^ (3 * g - 3) * q.length.toReal < shortClosedGeodesicCutoff :=
    lt_of_not_ge hnot
  obtain ⟨c, _hcRange, hcFree⟩ := original_geodesic_has_essential_circle R M q hq
  obtain ⟨qs, _hzeroTrace, hqs⟩ :=
    EssentialSimpleCircle.exists_simple_wolpert_iterates
      R hg hgenus M hSimple c q hcFree f hf
  have hshort (n : ℕ) (hn : n ≤ 3 * g - 3) :
      (qs n).length.toReal < shortClosedGeodesicCutoff :=
    (hqs n).2.2.trans_lt
      ((mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hf.1 hn)
        q.length_toReal_pos.le).trans_lt hsmall)
  obtain ⟨i, j, hij, htrace⟩ :=
    exists_equal_geodesic_trace_of_short_simple_list R hg hgenus M hCard
      (fun n => qs n.val) (fun n => (hqs n.val).2.1)
      (fun n => hshort n.val (by omega))
  choose cs hcsRange hcsFree using fun n : ℕ =>
    original_geodesic_has_essential_circle R M (qs n) (hqs n).2.1
  let T := essentialSimpleFreeClassEquiv f
  let a := c.freeClass
  have horbit (n : ℕ) :
      (((EssentialSimpleCircle.mapHomeomorph f)^[n]) c).freeClass = (T^[n]) a := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simpa only [Function.iterate_succ_apply',
          ← essentialSimpleFreeClassEquiv_apply_freeClass] using congrArg T ih
  have hclasses (n : ℕ) : (cs n).freeClass = (T^[n]) a := by
    refine Eq.trans ?_ (horbit n)
    apply (EssentialSimpleCircle.freeClass_eq_iff _ _).2
    exact Or.inl ((circleRepresentativeLoop_freelyHomotopic_iff _ _).mp
      (LiZhongQC.s30b_fh_trans (hcsFree n) (LiZhongQC.s30b_fh_symm (hqs n).1)))
  have hclassEq : (cs i.val).freeClass = (cs j.val).freeClass :=
    EssentialSimpleCircle.freeClass_eq_of_range_eq_of_circleHomeomorphHomotopyDichotomy
      hCircle (cs i.val) (cs j.val)
      ((hcsRange i.val).trans (htrace.trans (hcsRange j.val).symm))
  have horbitEq : (T^[i.val]) a = (T^[j.val]) a :=
    (hclasses i.val).symm.trans (hclassEq.trans (hclasses j.val))
  let m := j.val - i.val
  have hmpos : 0 < m := by dsimp only [m]; omega
  have hmle : m ≤ 3 * g - 3 := by dsimp only [m]; omega
  have hperiod : Function.IsPeriodicPt T m a := by
    change (T^[m]) a = a
    apply T.injective.iterate i.val
    rw [← Function.iterate_add_apply, show i.val + m = j.val by dsimp only [m]; omega]
    exact horbitEq.symm
  have hdisjoint (u v : Fin m) :
      (cs u.val).freeClass ≠ (cs v.val).freeClass →
        Disjoint (range (cs u.val).val) (range (cs v.val).val) := by
    intro hneq
    rcases (qs u.val).trace_eq_or_disjoint_of_length_lt_shortCutoff (qs v.val)
      (hshort u.val (u.isLt.le.trans hmle))
      (hshort v.val (v.isLt.le.trans hmle)) with heq | hd
    · exact False.elim (hneq
        (EssentialSimpleCircle.freeClass_eq_of_range_eq_of_circleHomeomorphHomotopyDichotomy
          hCircle (cs u.val) (cs v.val)
          ((hcsRange u.val).trans (heq.trans (hcsRange v.val).symm))))
    · simpa only [hcsRange u.val, hcsRange v.val] using hd
  exact hirred (isReducible_of_disjoint_periodic_freeClass_orbit
    R (by omega) hgenus hStraight f a hmpos hperiod
    (fun n : Fin m => cs n.val) (fun n => hclasses n.val) hdisjoint)

/-- The literal original maximal dilatation satisfies the simple-geodesic
length bound, with every independent classical geometric input explicit. -/
theorem maximalDilatation_rpow_lower_of_irreducible
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    {g : ℕ} (hg : 2 ≤ g) (hgenus : R.HasGenus g)
    (M : HyperbolicSurfaceModel R.toRiemannSurface)
    (hSimple : LowDimensionalTopology.Unproved.Surfaces.SimpleClosedGeodesicRepresentatives R g M)
    (hCard : LowDimensionalTopology.Unproved.Surfaces.ClosedDecomposingSystemCardinalities
      R hg hgenus M)
    (hCircle : LowDimensionalTopology.Unproved.Topology.CircleHomeomorphHomotopyDichotomy)
    (hStraight : LowDimensionalTopology.Unproved.Surfaces.SimultaneousAdmissibleCurveStraightening
      R g)
    (f : X ≃ₜ X)
    (hf : letI := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsQCRS f)
    (hirred : IsIrreducible f) (q : OriginalClosedGeodesic M)
    (hq : Function.Injective (q.periodic.lift : AddCircle (1 : ℝ) → X)) :
    letI := R.toRiemannAtlas.toChartedSpace
    (shortClosedGeodesicCutoff / q.length.toReal) ^ (1 / ((3 * g - 3 : ℕ) : ℝ)) ≤
      (LiZhongQC.maxDilatationRS f).toReal := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.connectedSpace
  have hfK := LiZhongQC.s29_m_isKQCRS_maxDil hf
  have hbound := shortCutoff_le_pow_mul_length_of_irreducible
    R hg hgenus M hSimple hCard hCircle hStraight f hfK hirred q hq
  have hN : 0 < ((3 * g - 3 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 3 * g - 3 by omega)
  rw [one_div]
  apply (Real.rpow_inv_le_iff_of_pos
    (div_nonneg shortClosedGeodesicCutoff_pos.le q.length_toReal_pos.le)
    (zero_le_one.trans hfK.1) hN).2
  rw [Real.rpow_natCast]
  exact (div_le_iff₀ q.length_toReal_pos).2 hbound

end LowDimensionalTopology.Geometry.Surfaces
