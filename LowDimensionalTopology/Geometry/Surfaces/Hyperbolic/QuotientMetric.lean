module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Auxiliary.Measure.CompatibleMeasure
public import LowDimensionalTopology.Geometry.Surfaces.Covering.DiscUniversalDeck
public import LowDimensionalTopology.Geometry.Hyperbolic.Metric.HyperbolicBalls
@[expose] public section
noncomputable section
open Set Filter Topology MeasureTheory
open scoped OnePoint ComplexConjugate ENNReal
namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- The genuine disc line element applied to a coordinate tangent vector. -/
def discHyperbolicTangentNorm (z : Complex.UnitDisc) (v : ℂ) : ℝ :=
  2 * ‖v‖ / (1 - ‖(z : ℂ)‖ ^ 2)

theorem discHyperbolicTangentNorm_nonneg (z : Complex.UnitDisc) (v : ℂ) :
    0 ≤ discHyperbolicTangentNorm z v := by
  have hz : 0 < 1 - ‖(z : ℂ)‖ ^ 2 := by nlinarith [z.norm_lt_one, norm_nonneg (z : ℂ)]
  exact div_nonneg (by positivity) hz.le

theorem normalizedDisc_analyticAt (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1)
    (z : Complex.UnitDisc) : AnalyticAt ℂ (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c) (z : ℂ) := by
  exact (analyticAt_const.mul analyticAt_id |>.add analyticAt_const).div
    (analyticAt_const.mul analyticAt_id |>.add analyticAt_const)
    (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractional_den_ne_zero hdet z.norm_lt_one.le)

/-- The actual normalized Mobius differential preserves the prescribed disc line element. -/
theorem normalizedDisc_tangentNorm (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1)
    (z : Complex.UnitDisc) (v : ℂ) :
    discHyperbolicTangentNorm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hdet z)
      (deriv (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c) (z : ℂ) * v) = discHyperbolicTangentNorm z v := by
  have hd := _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractional_den_ne_zero hdet z.norm_lt_one.le
  have hn : ‖deriv (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c) (z : ℂ)‖ ≠ 0 :=
    (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractional_deriv_norm_pos hdet hd).ne'
  change 2 * ‖deriv (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c) (z : ℂ) * v‖ /
    (1 - ‖_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c z‖ ^ 2) = 2 * ‖v‖ / (1 - ‖(z :
      ℂ)‖ ^ 2)
  rw [norm_mul, _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractional_defect_deriv hdet hd]
  field_simp

/-- A normalized disc Mobius map acts on actual continuously differentiable pieces,
including their genuine endpoint derivatives. -/
def discC1PieceMap (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1)
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece where
  a := p.a
  b := p.b
  ordered := p.ordered
  curve t := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hdet (p.curve t)
  velocity t := deriv (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c) (p.curve t :
    ℂ) * p.velocity t
  continuous_curve := (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c
    hdet).continuous.comp_continuousOn p.continuous_curve
  continuous_velocity := by
    have hD : Continuous (fun z : Complex.UnitDisc => deriv (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c) (z : ℂ)) := by
      rw [continuous_iff_continuousAt]
      intro z
      exact (normalizedDisc_analyticAt a c hdet z).deriv.continuousAt.comp
        Complex.UnitDisc.continuous_coe.continuousAt
    exact (hD.comp_continuousOn p.continuous_curve).mul p.continuous_velocity
  hasDerivWithin t ht := by
    have hcomp := (normalizedDisc_analyticAt a c hdet (p.curve t)).differentiableAt.hasDerivAt.scomp_hasDerivWithinAt
      t (p.hasDerivWithin t ht)
    change HasDerivWithinAt (fun s => _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c
      (p.curve s : ℂ)) _ _ _
    simpa only [Function.comp_def, smul_eq_mul, mul_comm] using hcomp

theorem discC1PieceMap_speed (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1)
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece) (t : ℝ) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discWeightedSpeed (discC1PieceMap a c hdet
      p).curve (discC1PieceMap a c hdet p).velocity t =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discWeightedSpeed p.curve p.velocity t :=
  normalizedDisc_tangentNorm a c hdet (p.curve t) (p.velocity t)

/-- The actual weighted integral length is invariant under every normalized disc Mobius map. -/
theorem discC1PieceMap_length (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1)
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece) : (discC1PieceMap a c hdet p).length = p.length := by
  apply intervalIntegral.integral_congr
  intro t _ht
  exact discC1PieceMap_speed a c hdet p t

/-- The real differential governing the area change of variables. -/
def normalizedDiscRealFDeriv (a c z : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.toSpanSingleton ℂ (deriv
    (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c) z)).restrictScalars ℝ

theorem normalizedDisc_hasFDerivAt_real (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1)
    (z : Complex.UnitDisc) : HasFDerivAt (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a
      c) (normalizedDiscRealFDeriv a c z) (z : ℂ) :=
  (normalizedDisc_analyticAt a c hdet z).differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ

theorem normalizedDiscRealFDeriv_det (a c z : ℂ) :
    (normalizedDiscRealFDeriv a c z).det = ‖deriv (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c) z‖ ^ 2 := by
  simp only [normalizedDiscRealFDeriv, ContinuousLinearMap.det,
    ContinuousLinearMap.coe_restrictScalars, LinearMap.det_restrictScalars,
    ContinuousLinearMap.det_toSpanSingleton, Algebra.norm_complex_eq]
  exact Complex.normSq_eq_norm_sq _

/-- The actual Euclidean Jacobian cancels precisely against the squared line-element
weight used by the existing density-weighted Lebesgue area. -/
theorem normalizedDisc_area_density (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1)
    (z : Complex.UnitDisc) :
    |(normalizedDiscRealFDeriv a c z).det| * _root_.LowDimensionalTopology.Geometry.Hyperbolic.discAreaDensity (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c z) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discAreaDensity z := by
  rw [normalizedDiscRealFDeriv_det, abs_of_nonneg (sq_nonneg _)]
  have h := congrArg (fun x : ℝ => x ^ 2) (normalizedDisc_tangentNorm a c hdet z 1)
  change (2 * ‖deriv (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c) (z : ℂ) * 1‖ /
      (1 - ‖_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c z‖ ^ 2)) ^ 2 =
    (2 * ‖(1 : ℂ)‖ / (1 - ‖(z : ℂ)‖ ^ 2)) ^ 2 at h
  simp only [norm_one, mul_one, mul_pow, div_pow] at h
  dsimp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discAreaDensity]
  convert h using 1 <;> ring

/-- Actual density-weighted planar areas of arbitrary measurable disc sets are invariant
under normalized Mobius maps; this is a measure theorem, not just a scalar covariance. -/
theorem normalizedDisc_hyperbolicArea (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1)
    (s : Set Complex.UnitDisc) (hs : MeasurableSet s) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hdet '' s) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea s := by
  let E := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hdet
  let S := ((↑) : Complex.UnitDisc → ℂ) '' s
  have hS : MeasurableSet S := _root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_measurableEmbedding_coe.measurableSet_image.mpr hs
  have hES : MeasurableSet (((↑) : Complex.UnitDisc → ℂ) '' (E '' s)) :=
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_measurableEmbedding_coe.measurableSet_image.mpr (E.measurableEmbedding.measurableSet_image.mpr hs)
  have him : ((↑) : Complex.UnitDisc → ℂ) '' (E '' s) = _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c '' S := by
    rw [Set.image_image, Set.image_image]
    rfl
  have hinj : Set.InjOn (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c) S := by
    rintro _ ⟨z, _hz, rfl⟩ _ ⟨w, _hw, rfl⟩ heq
    have hzw : E z = E w := Subtype.ext heq
    exact congrArg ((↑) : Complex.UnitDisc → ℂ) (E.injective hzw)
  have hmain := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hS
    (f := _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c) (f' :=
      normalizedDiscRealFDeriv a c)
    (Set.forall_mem_image.mpr fun z _ => (normalizedDisc_hasFDerivAt_real a c hdet z).hasFDerivWithinAt)
    hinj (fun z : ℂ => ENNReal.ofReal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discAreaDensity z))
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discAreaMeasure,
    withDensity_apply _ hES, withDensity_apply _ hS, him, hmain]
  apply setLIntegral_congr_fun hS
  rintro _ ⟨z, _hz, rfl⟩
  change ENNReal.ofReal |(normalizedDiscRealFDeriv a c (z : ℂ)).det| *
    ENNReal.ofReal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discAreaDensity
      (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c
      z)) = ENNReal.ofReal (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discAreaDensity z)
  rw [← ENNReal.ofReal_mul (abs_nonneg _), normalizedDisc_area_density a c hdet z]

/-- The actual boundary representative of the standard finite-disc coordinate. -/
theorem discFiniteHomeomorph_symm_coe (z : Complex.UnitDisc) :
    (discFiniteHomeomorph.symm z).val = ((z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  have h := congrArg ((↑) : Complex.UnitDisc → ℂ) (discFiniteHomeomorph.apply_symm_apply z)
  change discFiniteChart (discFiniteHomeomorph.symm z) = (z : ℂ) at h
  rw [← discFiniteChart_coe, h]

/-- The original orbit projection expressed in the genuine finite unit-disc coordinate. -/
def discQuotientProjection {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    Complex.UnitDisc → MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv) :=
  mobiusDomainProjection (unitDiscMobiusInvariantDomain H hInv) ∘ discFiniteHomeomorph.symm

theorem discQuotientProjection_covering {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic
      f) : IsCoveringMap (discQuotientProjection hInv) :=
  (mobiusDomain_noElliptic_covering (unitDiscMobiusInvariantDomain H hInv) hD hno).isCoveringMap.comp_homeomorph
    discFiniteHomeomorph.symm

/-- Every element of an actual invariant-domain group preserves that domain as a set. -/
theorem mobiusInvariantDomain_image_eq {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain H) (g : H) : g.val.val '' D.carrier = D.carrier := by
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact D.invariant g z hz
  · intro z hz
    refine ⟨g⁻¹ • z, D.invariant g⁻¹ z hz, ?_⟩
    exact smul_inv_smul g z

/-- Actual Mobius-related disc points have the same original quotient projection. -/
theorem discQuotientProjection_eq_of_mobius {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (g : H) (z w : Complex.UnitDisc)
    (h : g.val.val ((z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((w : ℂ) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) :
    discQuotientProjection hInv w = discQuotientProjection hInv z := by
  let D := unitDiscMobiusInvariantDomain H hInv
  let u : D.carrier := discFiniteHomeomorph.symm z
  let v : D.carrier := ⟨g.val.val u.val, D.invariant g u.val u.property⟩
  have hw : (discFiniteHomeomorph.symm w : D.carrier) = v := by
    apply Subtype.ext
    change (discFiniteHomeomorph.symm w).val = g.val.val (discFiniteHomeomorph.symm z).val
    rw [discFiniteHomeomorph_symm_coe, discFiniteHomeomorph_symm_coe]
    exact h.symm
  change mobiusDomainProjection D (discFiniteHomeomorph.symm w) =
    mobiusDomainProjection D (discFiniteHomeomorph.symm z)
  exact (congrArg (mobiusDomainProjection D) hw).trans (mobiusDomainProjection_smul D g u)

theorem discQuotientProjection_eq_iff {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (z w : Complex.UnitDisc) : discQuotientProjection hInv z = discQuotientProjection hInv w ↔
      ∃ g : H, g.val.val ((z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = ((w : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  constructor
  · intro h
    have hh : mobiusDomainProjection (unitDiscMobiusInvariantDomain H hInv) (discFiniteHomeomorph.symm w) =
        mobiusDomainProjection (unitDiscMobiusInvariantDomain H hInv) (discFiniteHomeomorph.symm z) := h.symm
    obtain ⟨g, hg⟩ := Quotient.exact hh
    have hv := congrArg Subtype.val hg
    change g.val.val (discFiniteHomeomorph.symm z).val = (discFiniteHomeomorph.symm w).val at hv
    rw [discFiniteHomeomorph_symm_coe, discFiniteHomeomorph_symm_coe] at hv
    exact ⟨g, hv⟩
  · rintro ⟨g, hg⟩
    exact (discQuotientProjection_eq_of_mobius hInv g z w hg).symm

/-- A normalized actual Mobius map acts on the same genuine disc points as the native
complex fractional homeomorphism. -/
theorem discFractionalHomeomorph_actual (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (a c : ℂ)
    (hdet : Complex.normSq a - Complex.normSq c = 1)
    (hform : f.val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.normalizedDiscTransformation a c hdet) (z :
      Complex.UnitDisc) :
    f.val ((z : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
      (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hdet z : Complex.UnitDisc) : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  rw [hform]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.normalizedDiscTransformation_of_closedDisc a c z hdet z.norm_lt_one.le

/-- Two continuous lifts from a connected parameter space with the same actual quotient
projection differ by one actual group element, with its genuine normalized disc coordinate. -/
theorem discQuotient_lifts_related {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    {T : Type*} [TopologicalSpace T] [PreconnectedSpace T] (α β : T → Complex.UnitDisc)
    (hα : Continuous α) (hβ : Continuous β) (t₀ : T)
    (hπ : ∀ t, discQuotientProjection hInv (α t) = discQuotientProjection hInv (β t)) :
    ∃ (g : H) (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1),
      g.val.val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.normalizedDiscTransformation a c hdet ∧
        ∀ t, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hdet (α t) = β t := by
  obtain ⟨g, hg⟩ := (discQuotientProjection_eq_iff hInv (α t₀) (β t₀)).mp (hπ t₀)
  obtain ⟨a, c, hdet, hform⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.complexMobius_disc_normal_form g.val
    (mobiusInvariantDomain_image_eq (unitDiscMobiusInvariantDomain H hInv) g)
  let E := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hdet
  have hstart : E (α t₀) = β t₀ := Complex.UnitDisc.coe_injective
    (OnePoint.coe_injective ((discFractionalHomeomorph_actual g.val a c hdet hform (α t₀)).symm.trans hg))
  have heq : E ∘ α = β := (discQuotientProjection_covering hInv hD hno).eq_of_comp_eq
    (E.continuous.comp hα) hβ (by
      funext t
      exact (discQuotientProjection_eq_of_mobius hInv g (α t) (E (α t))
        (discFractionalHomeomorph_actual g.val a c hdet hform (α t))).trans (hπ t)) t₀ hstart
  exact ⟨g, a, c, hdet, hform, fun t => congrFun heq t⟩

/-- The genuine density-weighted areas computed in two continuous lifts of the same
connected patch agree, for every measurable image region in the disc. -/
theorem discQuotient_lifts_area_eq {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    {T : Type*} [TopologicalSpace T] [PreconnectedSpace T] (α β : T → Complex.UnitDisc)
    (hα : Continuous α) (hβ : Continuous β) (t₀ : T)
    (hπ : ∀ t, discQuotientProjection hInv (α t) = discQuotientProjection hInv (β t))
    (s : Set T) (hs : MeasurableSet (α '' s)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (β '' s) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (α '' s) := by
  obtain ⟨_g, a, c, hdet, _hform, hrel⟩ := discQuotient_lifts_related hInv hD hno α β hα hβ t₀ hπ
  have him : β '' s = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hdet '' (α '' s) := by
    rw [Set.image_image]
    exact Set.image_congr (fun t _ht => (hrel t).symm)
  rw [him]
  exact normalizedDisc_hyperbolicArea a c hdet (α '' s) hs

/-- Equal actual C1 curves on their common interval have equal weighted integral lengths;
endpoint velocities are compared using genuine one-sided differentiability. -/
theorem discC1Piece_length_eq_of_curve_eq (p q : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece)
    (ha : p.a = q.a) (hb : p.b = q.b)
    (heq : ∀ t ∈ Icc p.a p.b, p.curve t = q.curve t) : p.length = q.length := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece.length,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece.length, ← ha, ← hb]
  by_cases hab : p.a = p.b
  · rw [hab, intervalIntegral.integral_same, intervalIntegral.integral_same]
  · have hlt : p.a < p.b := lt_of_le_of_ne p.ordered hab
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Icc p.a p.b := by simpa only [uIcc_of_le p.ordered] using ht
    have hpd : HasDerivWithinAt (fun s => (q.curve s : ℂ)) (p.velocity t) (Icc p.a p.b) t :=
      (p.hasDerivWithin t htI).congr_of_mem
        (fun s hs => congrArg ((↑) : Complex.UnitDisc → ℂ) (heq s hs).symm) htI
    have hqd : HasDerivWithinAt (fun s => (q.curve s : ℂ)) (q.velocity t) (Icc p.a p.b) t := by
      simpa only [ha, hb] using q.hasDerivWithin t (by simpa only [← ha, ← hb] using htI)
    have hv : p.velocity t = q.velocity t := UniqueDiffWithinAt.eq_deriv _
      ((uniqueDiffOn_Icc hlt) t htI) hpd hqd
    simp only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discWeightedSpeed, heq t htI, hv]

/-- The actual C1 integral length of a quotient curve is independent of its continuously
chosen disc lift, not merely of a formal tangent representative. -/
theorem discQuotient_curve_length_lift_independent {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (p q : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece) (ha : p.a = q.a) (hb : p.b = q.b)
    (hπ : ∀ t ∈ Icc p.a p.b,
      discQuotientProjection hInv (p.curve t) = discQuotientProjection hInv (q.curve t)) :
    p.length = q.length := by
  let : PreconnectedSpace (Icc p.a p.b) := Subtype.preconnectedSpace isPreconnected_Icc
  let α : Icc p.a p.b → Complex.UnitDisc := fun t => p.curve t.val
  let β : Icc p.a p.b → Complex.UnitDisc := fun t => q.curve t.val
  have hα : Continuous α := p.continuous_curve.domRestrict
  have hβ : Continuous β := by
    have hq : ContinuousOn q.curve (Icc p.a p.b) := by simpa only [ha, hb] using q.continuous_curve
    exact hq.domRestrict
  let t₀ : Icc p.a p.b := ⟨p.a, le_rfl, p.ordered⟩
  obtain ⟨_g, a, c, hdet, _hform, hrel⟩ := discQuotient_lifts_related hInv hD hno α β hα hβ t₀
    (fun t => hπ t.val t.property)
  calc
    p.length = (discC1PieceMap a c hdet p).length := (discC1PieceMap_length a c hdet p).symm
    _ = q.length := discC1Piece_length_eq_of_curve_eq _ q ha hb
      (fun t ht => hrel ⟨t, ht⟩)

theorem discQuotientProjection_surjective {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    Function.Surjective (discQuotientProjection hInv) :=
  (mobiusDomainProjection_surjective _).comp discFiniteHomeomorph.symm.surjective

/-- A genuine connected open region of the original quotient, equipped with a continuous
local inverse of the actual disc covering. -/
structure DiscQuotientAreaPatch {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) where
  carrier : Set (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))
  isOpen : IsOpen carrier
  isConnected : IsConnected carrier
  lift : carrier → Complex.UnitDisc
  continuous_lift : Continuous lift
  projects : ∀ x, discQuotientProjection hInv (lift x) = x.val

/-- Such genuine connected patches cover the entire original quotient surface. -/
theorem discQuotientAreaPatch_cover {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (x : MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv)) :
    ∃ P : DiscQuotientAreaPatch hInv, x ∈ P.carrier := by
  obtain ⟨z, hz⟩ := discQuotientProjection_surjective hInv x
  obtain ⟨l, hzl, hl⟩ := (discQuotientProjection_covering hInv hD hno).isLocalHomeomorph z
  have hxl : x ∈ l.target := by
    have he : l z = x := (congrFun hl z).symm.trans hz
    exact he ▸ l.map_source hzl
  let R := mobiusQuotientRiemannSurface (unitDiscMobiusInvariantDomain H hInv) hD
  obtain ⟨U, hUo, hxU, hUl, hUS⟩ := R.toRiemannAtlas.exists_simplyConnected_open_subset
    x l.target l.open_target hxl
  let : SimplyConnectedSpace U := hUS
  have hUc : IsConnected U := isConnected_iff_connectedSpace.mpr inferInstance
  let σ : U → Complex.UnitDisc := fun u => l.symm u.val
  have hσ : Continuous σ := l.continuousOn_symm.comp_continuous continuous_subtype_val
    (fun u => hUl u.property)
  have hσp (u : U) : discQuotientProjection hInv (σ u) = u.val :=
    (congrFun hl (l.symm u.val)).trans (l.right_inv (hUl u.property))
  exact ⟨⟨U, hUo, hUc, σ, hσ, hσp⟩, hxU⟩

/-- The local inverse is an actual open embedding; measurability of lifted Borel regions
is a proved consequence of the covering, not an additional area assumption. -/
theorem DiscQuotientAreaPatch.lift_isOpenEmbedding {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    (P : DiscQuotientAreaPatch hInv) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn
      H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) : Topology.IsOpenEmbedding P.lift := by
  apply (discQuotientProjection_covering hInv hD hno).isLocalHomeomorph.isOpenEmbedding_of_comp
    ?_ P.continuous_lift
  have he : discQuotientProjection hInv ∘ P.lift = (Subtype.val : P.carrier → _) := funext P.projects
  rw [he]
  exact P.isOpen.isOpenEmbedding_subtypeVal

/-- The native disc area is the existing density-weighted Lebesgue measure pulled back
through the genuine inclusion, not a newly prescribed numerical area formula. -/
def discNativeAreaMeasure : Measure Complex.UnitDisc :=
  Measure.comap ((↑) : Complex.UnitDisc → ℂ) _root_.LowDimensionalTopology.Geometry.Hyperbolic.discAreaMeasure

theorem discNativeAreaMeasure_apply (s : Set Complex.UnitDisc) (hs : MeasurableSet s) :
    discNativeAreaMeasure s = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea s := by
  rw [discNativeAreaMeasure, Measure.comap_apply _ Complex.UnitDisc.coe_injective
    (fun t ht => _root_.LowDimensionalTopology.Geometry.Hyperbolic.disc_measurableEmbedding_coe.measurableSet_image.mpr
      ht) _ hs]
  rfl

/-- An actual local quotient region has the pulled-back hyperbolic area measure. -/
def DiscQuotientAreaPatch.measure {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    [MeasurableSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    (P : DiscQuotientAreaPatch hInv) : Measure P.carrier :=
  Measure.comap P.lift discNativeAreaMeasure

theorem DiscQuotientAreaPatch.measure_apply {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    [MeasurableSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    [BorelSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    (P : DiscQuotientAreaPatch hInv) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn
      H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) (s : Set P.carrier) (hs :
      MeasurableSet s) :
    P.measure s = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (P.lift '' s) := by
  have he := (P.lift_isOpenEmbedding hD hno).measurableEmbedding
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientAreaPatch.measure, Measure.comap_apply _ he.injective
    (fun t ht => he.measurableSet_image.mpr ht) _ hs, discNativeAreaMeasure_apply _ (he.measurableSet_image.mpr hs)]

/-- Every choice of continuous local inverse on a connected quotient region gives exactly
the same genuine area measure on that intrinsic region. -/
theorem DiscQuotientAreaPatch.measure_independent {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    [MeasurableSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    [BorelSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    (P : DiscQuotientAreaPatch hInv) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn
      H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (β : P.carrier → Complex.UnitDisc) (hβ : Continuous β)
    (hβp : ∀ x, discQuotientProjection hInv (β x) = x.val) :
    P.measure = Measure.comap β discNativeAreaMeasure := by
  let : PreconnectedSpace P.carrier := Subtype.preconnectedSpace P.isConnected.isPreconnected
  have hβe : Topology.IsOpenEmbedding β := by
    apply (discQuotientProjection_covering hInv hD hno).isLocalHomeomorph.isOpenEmbedding_of_comp ?_ hβ
    have he : discQuotientProjection hInv ∘ β = (Subtype.val : P.carrier → _) := funext hβp
    rw [he]
    exact P.isOpen.isOpenEmbedding_subtypeVal
  let t₀ : P.carrier := ⟨P.isConnected.nonempty.some, P.isConnected.nonempty.some_mem⟩
  apply Measure.ext
  intro s hs
  rw [P.measure_apply hD hno s hs, Measure.comap_apply _ hβe.injective
    (fun t ht => hβe.measurableEmbedding.measurableSet_image.mpr ht) _ hs,
    discNativeAreaMeasure_apply _ (hβe.measurableEmbedding.measurableSet_image.mpr hs)]
  exact discQuotient_lifts_area_eq hInv hD hno β P.lift hβ P.continuous_lift t₀
    (fun t => (hβp t).trans (P.projects t).symm) s
    (hβe.measurableEmbedding.measurableSet_image.mpr hs)

theorem discQuotientProjection_continuous {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    Continuous (discQuotientProjection hInv) :=
  (mobiusDomainProjection_continuous _).comp discFiniteHomeomorph.symm.continuous

open scoped unitInterval

/-- An actual quotient curve segment, continuous on the unit interval and C1 in the genuine
covering coordinates. The lift is existential data, rather than a choice in the curve itself. -/
structure DiscQuotientC1CurvePiece {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) where
  curve : C(I, MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))
  hasC1Lift : ∃ p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece, p.a = 0 ∧ p.b = 1 ∧
    ∀ t : I, discQuotientProjection hInv (p.curve t) = curve t

/-- A selected lift used only to evaluate the representative-independent length. -/
def DiscQuotientC1CurvePiece.lift {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    (p : DiscQuotientC1CurvePiece
      hInv) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece := p.hasC1Lift.choose

theorem DiscQuotientC1CurvePiece.lift_spec {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    (p : DiscQuotientC1CurvePiece hInv) : p.lift.a = 0 ∧ p.lift.b = 1 ∧
      ∀ t : I, discQuotientProjection hInv (p.lift.curve t) = p.curve t := p.hasC1Lift.choose_spec

/-- The actual weighted line integral defines a length on the original quotient curve. -/
def DiscQuotientC1CurvePiece.length {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    (p : DiscQuotientC1CurvePiece hInv) : ℝ := p.lift.length

/-- Computing in any other genuine C1 disc lift gives this same quotient-curve length. -/
theorem DiscQuotientC1CurvePiece.length_eq_of_lift {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    (p : DiscQuotientC1CurvePiece hInv) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (q : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece) (hqa : q.a = 0) (hqb : q.b = 1)
    (hq : ∀ t : I, discQuotientProjection hInv (q.curve t) = p.curve t) : p.length = q.length := by
  apply discQuotient_curve_length_lift_independent hInv hD hno p.lift q
    (p.lift_spec.1.trans hqa.symm) (p.lift_spec.2.1.trans hqb.symm)
  intro t ht
  have htI : t ∈ Icc (0 : ℝ) 1 := by simpa only [p.lift_spec.1, p.lift_spec.2.1] using ht
  exact (p.lift_spec.2.2 ⟨t, htI⟩).trans (hq ⟨t, htI⟩).symm

/-- Each genuine quotient segment is in particular an actual topological path. -/
def DiscQuotientC1CurvePiece.toPath {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    (p : DiscQuotientC1CurvePiece hInv) : Path (p.curve 0) (p.curve 1) where
  toContinuousMap := p.curve
  source' := rfl
  target' := rfl

/-- Finite concatenations of genuine C1 segments on the original quotient surface. -/
inductive DiscQuotientPiecewiseC1Curve {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv) →
      MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv) → Type
  | nil (x) : DiscQuotientPiecewiseC1Curve hInv x x
  | cons (p : DiscQuotientC1CurvePiece hInv) {w}
      (tail : DiscQuotientPiecewiseC1Curve hInv (p.curve 1) w) :
      DiscQuotientPiecewiseC1Curve hInv (p.curve 0) w

/-- The finite-piece curve has a genuine continuous realization with its stated endpoints. -/
def DiscQuotientPiecewiseC1Curve.toPath {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    {x y : MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv)} :
    DiscQuotientPiecewiseC1Curve hInv x y → Path x y
  | .nil x => Path.refl x
  | .cons p tail => p.toPath.trans tail.toPath

/-- Segment lengths add along finite-piece curves, as prescribed by the descended line element. -/
def DiscQuotientPiecewiseC1Curve.length {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    {x y : MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv)} :
    DiscQuotientPiecewiseC1Curve hInv x y → ℝ
  | .nil _ => 0
  | .cons p tail => p.length + tail.length

/-- Concatenation of actual finite-piece quotient curves. -/
def DiscQuotientPiecewiseC1Curve.append {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    {x y z : MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv)} :
    DiscQuotientPiecewiseC1Curve hInv x y → DiscQuotientPiecewiseC1Curve hInv y z →
      DiscQuotientPiecewiseC1Curve hInv x z
  | .nil _, q => q
  | .cons p tail, q => .cons p (tail.append q)

theorem DiscQuotientPiecewiseC1Curve.length_append {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    {x y z : MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv)}
    (p : DiscQuotientPiecewiseC1Curve hInv x y) (q : DiscQuotientPiecewiseC1Curve hInv y z) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil _ => simp [_root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve.append,
    _root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve.length]
  | cons p tail ih =>
    change p.length + (tail.append q).length = (p.length + tail.length) + q.length
    rw [ih, add_assoc]

/-- Each constituent length can be computed in any disc lift of the segment, with the same
value in the finite-piece quotient curve. -/
theorem DiscQuotientPiecewiseC1Curve.length_cons_of_lift {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (p : DiscQuotientC1CurvePiece hInv) {w}
    (tail : DiscQuotientPiecewiseC1Curve hInv (p.curve 1) w)
    (q : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece) (hqa : q.a = 0) (hqb : q.b = 1)
    (hq : ∀ t : I, discQuotientProjection hInv (q.curve t) = p.curve t) :
    (_root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientPiecewiseC1Curve.cons p tail).length = q.length + tail.length := by
  change p.length + tail.length = q.length + tail.length
  rw [p.length_eq_of_lift hD hno q hqa hqb hq]




/-- The actual disc quotient is second countable because its genuine projection is an open
surjective quotient of the ordinary disc; no global countability axiom is added for surfaces. -/
theorem discQuotient_secondCountable {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    SecondCountableTopology (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv)) :=
  ((mobiusDomainProjection_isOpenQuotientMap (unitDiscMobiusInvariantDomain H hInv)).comp
    discFiniteHomeomorph.symm.isOpenQuotientMap).secondCountableTopology

/-- A local intrinsic area measure, regarded as a measure on the whole quotient and
supported on its genuine open patch. -/
def DiscQuotientAreaPatch.ambientMeasure {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    [MeasurableSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    (P : DiscQuotientAreaPatch hInv) : Measure (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv)) :=
  Measure.map Subtype.val P.measure

theorem DiscQuotientAreaPatch.ambientMeasure_apply {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    [MeasurableSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    [BorelSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    (P : DiscQuotientAreaPatch hInv) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn
      H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (s : Set (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))) (hs : MeasurableSet s) :
    P.ambientMeasure s = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (P.lift '' (Subtype.val ⁻¹' s)) := by
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.DiscQuotientAreaPatch.ambientMeasure, Measure.map_apply
    measurable_subtype_coe hs,
    P.measure_apply hD hno _ (hs.preimage measurable_subtype_coe)]

/-- Local area measures agree on every genuine connected open region lying in two patches. -/
theorem DiscQuotientAreaPatch.ambientMeasure_small_overlap {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    [MeasurableSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    [BorelSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    (P Q : DiscQuotientAreaPatch hInv) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (U : Set (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv)))
    (hUo : IsOpen U) (hUc : IsConnected U) (hUP : U ⊆ P.carrier) (hUQ : U ⊆ Q.carrier) :
    P.ambientMeasure.restrict U = Q.ambientMeasure.restrict U := by
  let α : U → Complex.UnitDisc := fun u => P.lift ⟨u.val, hUP u.property⟩
  let β : U → Complex.UnitDisc := fun u => Q.lift ⟨u.val, hUQ u.property⟩
  have hα : Continuous α := P.continuous_lift.comp (continuous_subtype_val.subtype_mk _)
  have hβ : Continuous β := Q.continuous_lift.comp (continuous_subtype_val.subtype_mk _)
  have hαp (u : U) : discQuotientProjection hInv (α u) = u.val := P.projects _
  have hβp (u : U) : discQuotientProjection hInv (β u) = u.val := Q.projects _
  have hαe : Topology.IsOpenEmbedding α := by
    apply (discQuotientProjection_covering hInv hD hno).isLocalHomeomorph.isOpenEmbedding_of_comp ?_ hα
    have he : discQuotientProjection hInv ∘ α = (Subtype.val : U → _) := funext hαp
    rw [he]
    exact hUo.isOpenEmbedding_subtypeVal
  let : PreconnectedSpace U := Subtype.preconnectedSpace hUc.isPreconnected
  let t₀ : U := ⟨hUc.nonempty.some, hUc.nonempty.some_mem⟩
  apply Measure.ext
  intro s hs
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
    P.ambientMeasure_apply hD hno _ (hs.inter hUo.measurableSet),
    Q.ambientMeasure_apply hD hno _ (hs.inter hUo.measurableSet)]
  have hP : P.lift '' (Subtype.val ⁻¹' (s ∩ U)) = α '' (Subtype.val ⁻¹' s) := by
    ext z
    constructor
    · rintro ⟨u, ⟨hus, huU⟩, rfl⟩
      exact ⟨⟨u.val, huU⟩, hus, rfl⟩
    · rintro ⟨u, hus, rfl⟩
      exact ⟨⟨u.val, hUP u.property⟩, ⟨hus, u.property⟩, rfl⟩
  have hQ : Q.lift '' (Subtype.val ⁻¹' (s ∩ U)) = β '' (Subtype.val ⁻¹' s) := by
    ext z
    constructor
    · rintro ⟨u, ⟨hus, huU⟩, rfl⟩
      exact ⟨⟨u.val, huU⟩, hus, rfl⟩
    · rintro ⟨u, hus, rfl⟩
      exact ⟨⟨u.val, hUQ u.property⟩, ⟨hus, u.property⟩, rfl⟩
  rw [hP, hQ]
  exact (discQuotient_lifts_area_eq hInv hD hno α β hα hβ t₀
    (fun t => (hαp t).trans (hβp t).symm) (Subtype.val ⁻¹' s)
    (hαe.measurableEmbedding.measurableSet_image.mpr (hs.preimage measurable_subtype_coe))).symm

/-- The local area measures agree on their full overlap, even when that overlap is
not connected. Countable locality extends agreement from connected coordinate neighborhoods. -/
theorem DiscQuotientAreaPatch.ambientMeasure_overlap {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    [MeasurableSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    [BorelSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    (P Q : DiscQuotientAreaPatch hInv) (hD :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) :
    P.ambientMeasure.restrict (P.carrier ∩ Q.carrier) =
      Q.ambientMeasure.restrict (P.carrier ∩ Q.carrier) := by
  let : SecondCountableTopology (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv)) :=
    discQuotient_secondCountable hInv
  apply _root_.LowDimensionalTopology.Geometry.Auxiliary.Measure.measure_restrict_eq_of_locally_eq
  intro x hx
  let R := mobiusQuotientRiemannSurface (unitDiscMobiusInvariantDomain H hInv) hD
  obtain ⟨U, hUo, hxU, hUS, hUc⟩ := R.toRiemannAtlas.exists_simplyConnected_open_subset
    x (P.carrier ∩ Q.carrier) (P.isOpen.inter Q.isOpen) hx
  let : SimplyConnectedSpace U := hUc
  have hconn : IsConnected U := isConnected_iff_connectedSpace.mpr inferInstance
  exact ⟨U, hUo, hxU, hUS, P.ambientMeasure_small_overlap Q hD hno U hUo hconn
    (fun z hz => (hUS hz).1) (fun z hz => (hUS hz).2)⟩

/-- The actual hyperbolic quotient carries a unique global Borel area measure agreeing
with the intrinsic hyperbolic area in every genuine local covering patch. -/
theorem discQuotient_existsUnique_areaMeasure {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    [MeasurableSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    [BorelSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) :
    ∃! μ : Measure (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv)),
      ∀ P : DiscQuotientAreaPatch hInv,
        μ.restrict P.carrier = P.ambientMeasure.restrict P.carrier := by
  let : SecondCountableTopology (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv)) :=
    discQuotient_secondCountable hInv
  have hcover : ⋃ P : DiscQuotientAreaPatch hInv, P.carrier = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨P, hx⟩ := discQuotientAreaPatch_cover hInv hD hno x
    exact Set.mem_iUnion.mpr ⟨P, hx⟩
  have hNon : Nonempty (DiscQuotientAreaPatch hInv) := by
    obtain ⟨P, _hx⟩ := discQuotientAreaPatch_cover hInv hD hno
      (mobiusDomainProjection (unitDiscMobiusInvariantDomain H hInv)
        (discFiniteHomeomorph.symm 0))
    exact ⟨P⟩
  let : Nonempty (DiscQuotientAreaPatch hInv) := hNon
  exact _root_.LowDimensionalTopology.Geometry.Auxiliary.Measure.existsUnique_measure_of_secondCountable_open_cover (fun
    P : DiscQuotientAreaPatch hInv => P.carrier)
    (fun P => P.isOpen) hcover (fun P => P.ambientMeasure)
    (fun P Q => P.ambientMeasure_overlap Q hD hno)


/-- The global hyperbolic area measure on the genuine quotient. -/
def discQuotientAreaMeasure {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    [MeasurableSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    [BorelSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) :
    Measure (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv)) :=
  (discQuotient_existsUnique_areaMeasure hInv hD hno).exists.choose

theorem discQuotientAreaMeasure_restrict {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    [MeasurableSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    [BorelSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) (P : DiscQuotientAreaPatch
      hInv) :
    (discQuotientAreaMeasure hInv hD hno).restrict P.carrier =
      P.ambientMeasure.restrict P.carrier :=
  (discQuotient_existsUnique_areaMeasure hInv hD hno).exists.choose_spec P

/-- The global area of a measurable set inside any covering patch is computed by the
prescribed disc density on its actual lift. -/
theorem discQuotientAreaMeasure_apply_patch {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    [MeasurableSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    [BorelSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv))]
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f) (P : DiscQuotientAreaPatch
      hInv)
    (s : Set (MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv)))
    (hs : MeasurableSet s) (hsP : s ⊆ P.carrier) :
    discQuotientAreaMeasure hInv hD hno s =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (P.lift '' (Subtype.val ⁻¹' s)) := by
  have he := congrArg (fun μ : Measure _ => μ s)
    (discQuotientAreaMeasure_restrict hInv hD hno P)
  rw [Measure.restrict_apply hs, Measure.restrict_apply hs, Set.inter_eq_left.mpr hsP] at he
  exact he.trans (P.ambientMeasure_apply hD hno s hs)

/-- The density along every genuine C1 disc piece is continuous up to both endpoints. -/
theorem discC1Piece_speed_continuousOn (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece) :
    ContinuousOn (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discWeightedSpeed p.curve p.velocity) (Icc p.a p.b) := by
  have hc : ContinuousOn (fun t => (p.curve t : ℂ)) (Icc p.a p.b) :=
    Complex.UnitDisc.continuous_coe.comp_continuousOn p.continuous_curve
  exact (continuousOn_const.mul p.continuous_velocity.norm).div
    (continuousOn_const.sub (hc.norm.pow 2)) (fun t _ht => by
      have hz := (p.curve t).norm_lt_one
      nlinarith [norm_nonneg (p.curve t : ℂ)])

/-- Restricting a genuine C1 piece preserves its curve and one-sided derivatives. -/
def discC1PieceRestrict (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece) (a b : ℝ) (hab : a ≤ b)
    (hsub : Icc a b ⊆ Icc p.a p.b) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece where
  a := a
  b := b
  ordered := hab
  curve := p.curve
  velocity := p.velocity
  continuous_curve := p.continuous_curve.mono hsub
  continuous_velocity := p.continuous_velocity.mono hsub
  hasDerivWithin t ht := (p.hasDerivWithin t (hsub ht)).mono hsub

/-- Inserting a cut into a genuine C1 piece leaves the computed length unchanged. -/
theorem discC1Piece_length_split (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece) (t : ℝ) (ht :
  t ∈ Icc p.a p.b) :
    p.length =
      (discC1PieceRestrict p p.a t ht.1 (fun _ hx => ⟨hx.1, hx.2.trans ht.2⟩)).length +
      (discC1PieceRestrict p t p.b ht.2 (fun _ hx => ⟨ht.1.trans hx.1, hx.2⟩)).length := by
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((discC1Piece_speed_continuousOn p).mono (fun _ hx => ⟨hx.1, hx.2.trans ht.2⟩)
      |>.intervalIntegrable_of_Icc ht.1)
    ((discC1Piece_speed_continuousOn p).mono (fun _ hx => ⟨ht.1.trans hx.1, hx.2⟩)
      |>.intervalIntegrable_of_Icc ht.2)).symm

/-- Subdivision and independent choices of covering lifts on each subinterval give the
same true integral length as a single C1 lift of the quotient curve. -/
theorem discQuotient_curve_partition_length {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn H
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hno : ∀ f ∈ H, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece) (n : ℕ) (t : ℕ → ℝ) (ht : Monotone t)
    (ht₀ : t 0 = p.a) (htn : t n = p.b) (q : ℕ → _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece)
    (hqa : ∀ i < n, (q i).a = t i) (hqb : ∀ i < n, (q i).b = t (i + 1))
    (hπ : ∀ i < n, ∀ s ∈ Icc (t i) (t (i + 1)),
      discQuotientProjection hInv ((q i).curve s) = discQuotientProjection hInv (p.curve s)) :
    ∑ i ∈ Finset.range n, (q i).length = p.length := by
  have hsub (i : ℕ) (hi : i < n) : Icc (t i) (t (i + 1)) ⊆ Icc p.a p.b := by
    intro s hs
    exact ⟨ht₀ ▸ (ht (Nat.zero_le i)).trans hs.1,
      htn ▸ hs.2.trans (ht (Nat.add_one_le_iff.mpr hi))⟩
  calc
    ∑ i ∈ Finset.range n, (q i).length =
        ∑ i ∈ Finset.range n, ∫ s in t i..t (i + 1), _root_.LowDimensionalTopology.Geometry.Hyperbolic.discWeightedSpeed p.curve p.velocity s := by
      apply Finset.sum_congr rfl
      intro i hi
      have hin : i < n := Finset.mem_range.mp hi
      exact discQuotient_curve_length_lift_independent hInv hD hno (q i)
        (discC1PieceRestrict p (t i) (t (i + 1)) (ht (Nat.le_succ i)) (hsub i hin))
        (hqa i hin) (hqb i hin) (fun s hs => hπ i hin s (by simpa only [← hqa i hin, ← hqb i hin] using hs))
    _ = p.length := by
      have he := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (fun i hi =>
        ((discC1Piece_speed_continuousOn p).mono (hsub i hi)).intervalIntegrable_of_Icc (ht (Nat.le_succ i)))
      simpa only [ht₀, htn, _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece.length] using he

theorem discC1Piece_length_nonneg (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece) : 0 ≤ p.length := by
  apply intervalIntegral.integral_nonneg_of_forall p.ordered
  intro t
  exact discHyperbolicTangentNorm_nonneg (p.curve t) (p.velocity t)

theorem DiscQuotientC1CurvePiece.length_nonneg {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    (p : DiscQuotientC1CurvePiece hInv) : 0 ≤ p.length :=
  discC1Piece_length_nonneg p.lift

theorem DiscQuotientPiecewiseC1Curve.length_nonneg {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    {hInv : ∀ (g : H) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc}
    {x y : MobiusDomainQuotient (unitDiscMobiusInvariantDomain H hInv)}
    (p : DiscQuotientPiecewiseC1Curve hInv x y) : 0 ≤ p.length := by
  induction p with
  | nil _x => exact le_rfl
  | cons p _tail ih => exact add_nonneg p.length_nonneg ih


/-- A specified conformal disc-quotient presentation, without a claim that different
presentations have already been identified metrically. -/
structure HyperbolicSurfaceModel {X : Type*} [TopologicalSpace X] (R : RiemannSurface X) where
  group : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup
  invariant : ∀ (g : group) z, z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → g • z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
  discontinuous : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn group _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
  no_elliptic : ∀ f ∈ group, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f
  homeomorph : X ≃ₜ MobiusDomainQuotient (unitDiscMobiusInvariantDomain group invariant)
  analytic : RiemannAnalyticMap R.toRiemannAtlas
    (mobiusQuotientRiemannSurface (unitDiscMobiusInvariantDomain group invariant) discontinuous).toRiemannAtlas
    homeomorph

theorem isHyperbolicType_iff_nonempty_model {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) : IsHyperbolicType R ↔ Nonempty (HyperbolicSurfaceModel R) := by
  constructor
  · rintro ⟨H, hInv, hD, hno, f, hf, hbij⟩
    exact ⟨⟨H, hInv, hD, hno, hf.toHomeomorph hbij, hf⟩⟩
  · rintro ⟨M⟩
    exact ⟨M.group, M.invariant, M.discontinuous, M.no_elliptic,
      M.homeomorph, M.analytic, M.homeomorph.bijective⟩

/-- Transport of the genuine quotient area to the original surface through the specified
analytic homeomorphism. -/
def HyperbolicSurfaceModel.areaMeasure {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {R : RiemannSurface X} (M : HyperbolicSurfaceModel R) : Measure X := by
  letI : MeasurableSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain M.group M.invariant)) :=
    borel _
  letI : BorelSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain M.group M.invariant)) := ⟨rfl⟩
  exact Measure.map M.homeomorph.symm (discQuotientAreaMeasure M.invariant M.discontinuous M.no_elliptic)

theorem HyperbolicSurfaceModel.areaMeasure_apply {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {R : RiemannSurface X} (M : HyperbolicSurfaceModel R)
    (s : Set X) (hs : MeasurableSet s) :
    M.areaMeasure s =
      (letI : MeasurableSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain M.group M.invariant)) := borel _
       let : BorelSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain M.group M.invariant)) := ⟨rfl⟩
       discQuotientAreaMeasure M.invariant M.discontinuous M.no_elliptic (M.homeomorph '' s)) := by
  let : MeasurableSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain M.group M.invariant)) :=
    borel _
  let : BorelSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain M.group M.invariant)) := ⟨rfl⟩
  rw [_root_.LowDimensionalTopology.Geometry.Surfaces.HyperbolicSurfaceModel.areaMeasure, Measure.map_apply
    M.homeomorph.symm.continuous.measurable hs,
    M.homeomorph.preimage_symm]

/-- Areas on the original surface are computed in any actual covering coordinate patch
by the prescribed disc density. -/
theorem HyperbolicSurfaceModel.areaMeasure_apply_patch {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {R : RiemannSurface X} (M : HyperbolicSurfaceModel R)
    (P : DiscQuotientAreaPatch M.invariant) (s : Set X) (hs : MeasurableSet s)
    (hsP : M.homeomorph '' s ⊆ P.carrier) :
    M.areaMeasure s = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (P.lift '' (Subtype.val ⁻¹' (M.homeomorph '' s))) := by
  let : MeasurableSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain M.group M.invariant)) :=
    borel _
  let : BorelSpace (MobiusDomainQuotient (unitDiscMobiusInvariantDomain M.group M.invariant)) := ⟨rfl⟩
  exact (M.areaMeasure_apply s hs).trans (discQuotientAreaMeasure_apply_patch M.invariant
    M.discontinuous M.no_elliptic P _ (M.homeomorph.measurableEmbedding.measurableSet_image.mpr hs) hsP)

/-- A genuine curve on the original surface which is C1 in the specified covering coordinates. -/
structure HyperbolicSurfaceC1CurvePiece {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} (M : HyperbolicSurfaceModel R) where
  curve : C(I, X)
  hasC1Lift : ∃ p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece, p.a = 0 ∧ p.b = 1 ∧
    ∀ t : I, discQuotientProjection M.invariant (p.curve t) = M.homeomorph (curve t)

def HyperbolicSurfaceC1CurvePiece.toQuotient {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} {M : HyperbolicSurfaceModel R}
    (p : HyperbolicSurfaceC1CurvePiece M) : DiscQuotientC1CurvePiece M.invariant where
  curve := ⟨fun t => M.homeomorph (p.curve t), M.homeomorph.continuous.comp p.curve.continuous⟩
  hasC1Lift := p.hasC1Lift

def HyperbolicSurfaceC1CurvePiece.length {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} {M : HyperbolicSurfaceModel R}
    (p : HyperbolicSurfaceC1CurvePiece M) : ℝ := p.toQuotient.length

/-- Any actual C1 lift computes the transported curve length. -/
theorem HyperbolicSurfaceC1CurvePiece.length_eq_of_lift {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} {M : HyperbolicSurfaceModel R}
    (p : HyperbolicSurfaceC1CurvePiece M) (q : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece) (hqa
      : q.a = 0) (hqb : q.b = 1)
    (hq : ∀ t : I, discQuotientProjection M.invariant (q.curve t) = M.homeomorph (p.curve t)) :
    p.length = q.length :=
  p.toQuotient.length_eq_of_lift M.discontinuous M.no_elliptic q hqa hqb hq

def HyperbolicSurfaceC1CurvePiece.toPath {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} {M : HyperbolicSurfaceModel R}
    (p : HyperbolicSurfaceC1CurvePiece M) : Path (p.curve 0) (p.curve 1) where
  toContinuousMap := p.curve
  source' := rfl
  target' := rfl

theorem HyperbolicSurfaceC1CurvePiece.length_nonneg {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} {M : HyperbolicSurfaceModel R}
    (p : HyperbolicSurfaceC1CurvePiece M) : 0 ≤ p.length := p.toQuotient.length_nonneg


/-- The actual analytic disc covering of the original surface supplied by a specified model. -/
def HyperbolicSurfaceModel.discCover {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} (M : HyperbolicSurfaceModel
      R) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X :=
  M.homeomorph.symm ∘ mobiusDomainProjection (unitDiscMobiusInvariantDomain M.group M.invariant)

theorem HyperbolicSurfaceModel.discCover_covering {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} (M : HyperbolicSurfaceModel R) : IsCoveringMap M.discCover :=
  (mobiusDomain_noElliptic_covering (unitDiscMobiusInvariantDomain M.group M.invariant)
    M.discontinuous M.no_elliptic).isCoveringMap.homeomorph_comp M.homeomorph.symm

theorem HyperbolicSurfaceModel.discCover_surjective {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} (M : HyperbolicSurfaceModel R) : Function.Surjective M.discCover :=
  M.homeomorph.symm.surjective.comp
    (mobiusDomainProjection_surjective (unitDiscMobiusInvariantDomain M.group M.invariant))

theorem HyperbolicSurfaceModel.discCover_analytic {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} (M : HyperbolicSurfaceModel R) :
    RiemannAnalyticMap discRiemannSurface.toRiemannAtlas R.toRiemannAtlas M.discCover :=
  (riemannAnalyticMap_homeomorph_symm M.homeomorph M.analytic).comp
    (mobiusDomainProjection_analytic (unitDiscMobiusInvariantDomain M.group M.invariant) M.discontinuous)

/-- Two analytic simply connected disc covers of the same surface differ by a genuine
analytic disc homeomorphism, with any specified common-fiber anchor. -/
theorem analytic_discCovers_exists_homeomorph {X : Type*} [TopologicalSpace X]
    (R : RiemannAtlas X) (p q : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp :
      IsCoveringMap p) (hq : IsCoveringMap q)
    (hpa : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas R p)
    (hqa : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas R q)
    (a b : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) (hab : p a = q b) :
    ∃ F : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ≃ₜ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc, F a = b ∧ q ∘ F = p ∧
      RiemannAnalyticMap discRiemannSurface.toRiemannAtlas discRiemannSurface.toRiemannAtlas F := by
  let : SimplyConnectedSpace _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := discRiemannSurface_simplyConnected
  let : LocallyPathConnectedSpace _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := discRiemannSurface.toRiemannAtlas.locallyPathConnectedSpace
  obtain ⟨F, ⟨hFa, hqF⟩, _hFu⟩ := hq.existsUnique_continuousMap_lifts ⟨p, hp.continuous⟩ a b hab.symm
  obtain ⟨G, ⟨hGb, hpG⟩, _hGu⟩ := hp.existsUnique_continuousMap_lifts ⟨q, hq.continuous⟩ b a hab
  have hGF : (G ∘ F : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc →
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) = id := hp.eq_of_comp_eq
    (G.continuous.comp F.continuous) continuous_id
    (by funext z; exact (congrFun hpG (F z)).trans (congrFun hqF z)) a (by simp [hFa, hGb])
  have hFG : (F ∘ G : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc →
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) = id := hq.eq_of_comp_eq
    (F.continuous.comp G.continuous) continuous_id
    (by funext z; exact (congrFun hqF (G z)).trans (congrFun hpG z)) b (by simp [hFa, hGb])
  let E : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ≃ₜ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc :=
    { toFun := F
      invFun := G
      left_inv := fun z => congrFun hGF z
      right_inv := fun z => congrFun hFG z
      continuous_toFun := F.continuous
      continuous_invFun := G.continuous }
  refine ⟨E, hFa, hqF, ?_⟩
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_localHomeomorph hqa hq.isLocalHomeomorph E.continuous
  change RiemannAnalyticMap _ _ (q ∘ F)
  rw [hqF]
  exact hpa

/-- Changes between actual analytic disc covers are actual normalized Mobius
transformations, rather than arbitrary homeomorphisms of a coordinate surrogate. -/
theorem analytic_discCovers_exists_normalized {X : Type*} [TopologicalSpace X]
    (R : RiemannAtlas X) (p q : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp :
      IsCoveringMap p) (hq : IsCoveringMap q)
    (hpa : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas R p)
    (hqa : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas R q)
    (a b : Complex.UnitDisc) (hab : p (discFiniteHomeomorph.symm a) = q (discFiniteHomeomorph.symm b)) :
    ∃ (u c : ℂ) (hdet : Complex.normSq u - Complex.normSq c = 1),
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph u c hdet a = b ∧
      ∀ z, q (discFiniteHomeomorph.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph u c
        hdet z)) =
        p (discFiniteHomeomorph.symm z) := by
  obtain ⟨F, hFa, hqF, hF⟩ := analytic_discCovers_exists_homeomorph R p q hp hq hpa hqa
    (discFiniteHomeomorph.symm a) (discFiniteHomeomorph.symm b) hab
  let M := discAnalyticAutomorphismMobius F hF
  obtain ⟨u, c, hdet, hform⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.complexMobius_disc_normal_form M (discAnalyticAutomorphismMobius_preserves F hF)
  have he (z : Complex.UnitDisc) :
      discFiniteHomeomorph.symm (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph u c hdet z) = F (discFiniteHomeomorph.symm z) := by
    apply Subtype.ext
    rw [discFiniteHomeomorph_symm_coe]
    exact (discFractionalHomeomorph_actual M u c hdet hform z).symm.trans
      (by rw [← discFiniteHomeomorph_symm_coe]; exact discAnalyticAutomorphismMobius_apply F hF _)
  refine ⟨u, c, hdet, ?_, fun z => ?_⟩
  · apply discFiniteHomeomorph.symm.injective
    exact (he a).trans hFa
  · exact (congrArg q (he z)).trans (congrFun hqF (discFiniteHomeomorph.symm z))


/-- Any two continuous lifts into two analytic disc covers differ by one actual normalized
Mobius map on each connected parameter space. -/
theorem analytic_discCovers_lifts_related {X : Type*} [TopologicalSpace X]
    (R : RiemannAtlas X) (p q : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp :
      IsCoveringMap p) (hq : IsCoveringMap q)
    (hpa : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas R p)
    (hqa : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas R q)
    {T : Type*} [TopologicalSpace T] [PreconnectedSpace T] (α β : T → Complex.UnitDisc)
    (hα : Continuous α) (hβ : Continuous β) (t₀ : T)
    (hπ : ∀ t, p (discFiniteHomeomorph.symm (α t)) = q (discFiniteHomeomorph.symm (β t))) :
    ∃ (u c : ℂ) (hdet : Complex.normSq u - Complex.normSq c = 1),
      ∀ t, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph u c hdet (α t) = β t := by
  obtain ⟨u, c, hdet, hstart, hchange⟩ := analytic_discCovers_exists_normalized
    R p q hp hq hpa hqa (α t₀) (β t₀) (hπ t₀)
  let E := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph u c hdet
  have he : E ∘ α = β := (hq.comp_homeomorph discFiniteHomeomorph.symm).eq_of_comp_eq
    (E.continuous.comp hα) hβ (by
      funext t
      exact (hchange (α t)).trans (hπ t)) t₀ hstart
  exact ⟨u, c, hdet, fun t => congrFun he t⟩

/-- True density-weighted areas agree in continuous lifts into any two analytic disc
covers of the same surface. -/
theorem analytic_discCovers_lifts_area_eq {X : Type*} [TopologicalSpace X]
    (R : RiemannAtlas X) (p q : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp :
      IsCoveringMap p) (hq : IsCoveringMap q)
    (hpa : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas R p)
    (hqa : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas R q)
    {T : Type*} [TopologicalSpace T] [PreconnectedSpace T] (α β : T → Complex.UnitDisc)
    (hα : Continuous α) (hβ : Continuous β) (t₀ : T)
    (hπ : ∀ t, p (discFiniteHomeomorph.symm (α t)) = q (discFiniteHomeomorph.symm (β t)))
    (s : Set T) (hs : MeasurableSet (α '' s)) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (β '' s) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (α '' s) := by
  obtain ⟨u, c, hdet, hrel⟩ := analytic_discCovers_lifts_related R p q hp hq hpa hqa α β hα hβ t₀ hπ
  have him : β '' s = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph u c hdet '' (α '' s) := by
    rw [Set.image_image]
    exact Set.image_congr (fun t _ht => (hrel t).symm)
  rw [him]
  exact normalizedDisc_hyperbolicArea u c hdet (α '' s) hs

/-- The genuine integral lengths computed from arbitrary C1 lifts into different analytic
disc covers of the same original surface agree. -/
theorem analytic_discCovers_curve_length_eq {X : Type*} [TopologicalSpace X]
    (R : RiemannAtlas X) (p q : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp :
      IsCoveringMap p) (hq : IsCoveringMap q)
    (hpa : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas R p)
    (hqa : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas R q)
    (u v : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscC1CurvePiece) (ha : u.a = v.a) (hb : u.b = v.b)
    (hπ : ∀ t ∈ Icc u.a u.b,
      p (discFiniteHomeomorph.symm (u.curve t)) = q (discFiniteHomeomorph.symm (v.curve t))) :
    u.length = v.length := by
  let : PreconnectedSpace (Icc u.a u.b) := Subtype.preconnectedSpace isPreconnected_Icc
  let α : Icc u.a u.b → Complex.UnitDisc := fun t => u.curve t.val
  let β : Icc u.a u.b → Complex.UnitDisc := fun t => v.curve t.val
  have hα : Continuous α := u.continuous_curve.domRestrict
  have hβ : Continuous β := by
    have hv : ContinuousOn v.curve (Icc u.a u.b) := by simpa only [ha, hb] using v.continuous_curve
    exact hv.domRestrict
  let t₀ : Icc u.a u.b := ⟨u.a, le_rfl, u.ordered⟩
  obtain ⟨a, c, hdet, hrel⟩ := analytic_discCovers_lifts_related R p q hp hq hpa hqa
    α β hα hβ t₀ (fun t => hπ t.val t.property)
  exact (discC1PieceMap_length a c hdet u).symm.trans
    (discC1Piece_length_eq_of_curve_eq _ v ha hb (fun t ht => hrel ⟨t, ht⟩))

/-- The covering-coordinate length on an original surface is independent of its chosen
conformal disc-quotient presentation. -/
theorem HyperbolicSurfaceC1CurvePiece.length_independent_model {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} {M N : HyperbolicSurfaceModel R}
    (p : HyperbolicSurfaceC1CurvePiece M) (q : HyperbolicSurfaceC1CurvePiece N)
    (hpq : p.curve = q.curve) : p.length = q.length := by
  have hprojM (t : I) : M.discCover (discFiniteHomeomorph.symm (p.toQuotient.lift.curve t)) = p.curve t := by
    change M.homeomorph.symm (discQuotientProjection M.invariant (p.toQuotient.lift.curve t)) = p.curve t
    rw [p.toQuotient.lift_spec.2.2]
    exact M.homeomorph.symm_apply_apply _
  have hprojN (t : I) : N.discCover (discFiniteHomeomorph.symm (q.toQuotient.lift.curve t)) = q.curve t := by
    change N.homeomorph.symm (discQuotientProjection N.invariant (q.toQuotient.lift.curve t)) = q.curve t
    rw [q.toQuotient.lift_spec.2.2]
    exact N.homeomorph.symm_apply_apply _
  apply analytic_discCovers_curve_length_eq R.toRiemannAtlas M.discCover N.discCover
    M.discCover_covering N.discCover_covering M.discCover_analytic N.discCover_analytic
    p.toQuotient.lift q.toQuotient.lift
    (p.toQuotient.lift_spec.1.trans q.toQuotient.lift_spec.1.symm)
    (p.toQuotient.lift_spec.2.1.trans q.toQuotient.lift_spec.2.1.symm)
  intro t ht
  have htI : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [p.toQuotient.lift_spec.1, p.toQuotient.lift_spec.2.1] using ht
  exact (hprojM ⟨t, htI⟩).trans ((congrArg (fun γ : C(I, X) => γ ⟨t, htI⟩) hpq).trans
    (hprojN ⟨t, htI⟩).symm)


/-- A curve which is C1 in one hyperbolic presentation is C1 in every other presentation. -/
def HyperbolicSurfaceC1CurvePiece.rebase {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} {M : HyperbolicSurfaceModel R}
    (p : HyperbolicSurfaceC1CurvePiece M) (N : HyperbolicSurfaceModel R) : HyperbolicSurfaceC1CurvePiece N := by
  refine ⟨p.curve, ?_⟩
  obtain ⟨v, hva, hvb, hvl⟩ := p.hasC1Lift
  obtain ⟨b, hb⟩ := N.discCover_surjective (p.curve 0)
  have hvp (t : I) : M.discCover (discFiniteHomeomorph.symm (v.curve t)) = p.curve t := by
    change M.homeomorph.symm (discQuotientProjection M.invariant (v.curve t)) = p.curve t
    rw [hvl]
    exact M.homeomorph.symm_apply_apply _
  obtain ⟨u, c, hdet, _hstart, hchange⟩ := analytic_discCovers_exists_normalized R.toRiemannAtlas
    M.discCover N.discCover M.discCover_covering N.discCover_covering M.discCover_analytic N.discCover_analytic
    (v.curve 0) (discFiniteHomeomorph b) ((hvp 0).trans (by simpa using hb.symm))
  refine ⟨discC1PieceMap u c hdet v, hva, hvb, ?_⟩
  intro t
  have he := (hchange (v.curve t)).trans (hvp t)
  have he' := congrArg N.homeomorph he
  change N.homeomorph (N.homeomorph.symm
    (discQuotientProjection N.invariant ((discC1PieceMap u c hdet v).curve t))) = _ at he'
  exact (N.homeomorph.apply_symm_apply _).symm.trans he'

theorem HyperbolicSurfaceC1CurvePiece.rebase_curve {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} {M : HyperbolicSurfaceModel R}
    (p : HyperbolicSurfaceC1CurvePiece M) (N : HyperbolicSurfaceModel R) : (p.rebase N).curve = p.curve := rfl

theorem HyperbolicSurfaceC1CurvePiece.rebase_length {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} {M : HyperbolicSurfaceModel R}
    (p : HyperbolicSurfaceC1CurvePiece M) (N : HyperbolicSurfaceModel R) : (p.rebase N).length = p.length :=
  (p.rebase N).length_independent_model p (p.rebase_curve N)

/-- The genuine local disc coordinate on a patch of the original surface. -/
def HyperbolicSurfaceModel.patchLift {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} (M : HyperbolicSurfaceModel R) (P : DiscQuotientAreaPatch M.invariant)
    (U : Set X) (hU : ∀ x ∈ U, M.homeomorph x ∈ P.carrier) : U → Complex.UnitDisc :=
  fun x => P.lift ⟨M.homeomorph x.val, hU x.val x.property⟩

theorem HyperbolicSurfaceModel.patchLift_continuous {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} (M : HyperbolicSurfaceModel R) (P : DiscQuotientAreaPatch M.invariant)
    (U : Set X) (hU : ∀ x ∈ U, M.homeomorph x ∈ P.carrier) : Continuous (M.patchLift P U hU) :=
  P.continuous_lift.comp ((M.homeomorph.continuous.comp continuous_subtype_val).subtype_mk _)

theorem HyperbolicSurfaceModel.patchLift_projects {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} (M : HyperbolicSurfaceModel R) (P : DiscQuotientAreaPatch M.invariant)
    (U : Set X) (hU : ∀ x ∈ U, M.homeomorph x ∈ P.carrier) (x : U) :
    M.discCover (discFiniteHomeomorph.symm (M.patchLift P U hU x)) = x.val := by
  change M.homeomorph.symm (discQuotientProjection M.invariant (P.lift _)) = x.val
  rw [P.projects]
  exact M.homeomorph.symm_apply_apply _

theorem HyperbolicSurfaceModel.patchLift_isOpenEmbedding {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} (M : HyperbolicSurfaceModel R) (P : DiscQuotientAreaPatch M.invariant)
    (U : Set X) (hUo : IsOpen U) (hU : ∀ x ∈ U, M.homeomorph x ∈ P.carrier) :
    Topology.IsOpenEmbedding (M.patchLift P U hU) := by
  apply (M.discCover_covering.comp_homeomorph discFiniteHomeomorph.symm).isLocalHomeomorph.isOpenEmbedding_of_comp
    ?_ (M.patchLift_continuous P U hU)
  have he : (M.discCover ∘ discFiniteHomeomorph.symm) ∘ M.patchLift P U hU = (Subtype.val : U → X) :=
    funext (M.patchLift_projects P U hU)
  rw [he]
  exact hUo.isOpenEmbedding_subtypeVal

/-- Area of a measurable region inside an actual coordinate patch is the area of its
continuous disc lift, expressed directly on the original surface. -/
theorem HyperbolicSurfaceModel.areaMeasure_apply_patchLift {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {R : RiemannSurface X} (M : HyperbolicSurfaceModel R)
    (P : DiscQuotientAreaPatch M.invariant) (U : Set X) (hUo : IsOpen U)
    (hU : ∀ x ∈ U, M.homeomorph x ∈ P.carrier) (s : Set X) (hs : MeasurableSet s) :
    M.areaMeasure (s ∩ U) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (M.patchLift P U hU '' (Subtype.val ⁻¹' s)) := by
  rw [M.areaMeasure_apply_patch P (s ∩ U) (hs.inter hUo.measurableSet)
    (by rintro _ ⟨x, hx, rfl⟩; exact hU x hx.2)]
  apply congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea
  ext z
  constructor
  · rintro ⟨v, ⟨x, ⟨hxs, hxU⟩, hEx⟩, rfl⟩
    exact ⟨⟨x, hxU⟩, hxs, congrArg P.lift (Subtype.ext hEx)⟩
  · rintro ⟨x, hxs, rfl⟩
    exact ⟨⟨M.homeomorph x.val, hU x.val x.property⟩, ⟨x.val, ⟨hxs, x.property⟩, rfl⟩, rfl⟩

/-- The full global area measure on the original surface is independent of the chosen
conformal disc-quotient presentation. -/
theorem HyperbolicSurfaceModel.areaMeasure_independent {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {R : RiemannSurface X} (M N : HyperbolicSurfaceModel R) :
    M.areaMeasure = N.areaMeasure := by
  let : SecondCountableTopology (MobiusDomainQuotient (unitDiscMobiusInvariantDomain M.group M.invariant)) :=
    discQuotient_secondCountable M.invariant
  let : SecondCountableTopology X := M.homeomorph.secondCountableTopology
  have he : M.areaMeasure.restrict Set.univ = N.areaMeasure.restrict Set.univ := by
    apply _root_.LowDimensionalTopology.Geometry.Auxiliary.Measure.measure_restrict_eq_of_locally_eq
    intro x _hx
    obtain ⟨P, hxP⟩ := discQuotientAreaPatch_cover M.invariant M.discontinuous M.no_elliptic (M.homeomorph x)
    obtain ⟨Q, hxQ⟩ := discQuotientAreaPatch_cover N.invariant N.discontinuous N.no_elliptic (N.homeomorph x)
    obtain ⟨U, hUo, hxU, hUW, hUc⟩ := R.toRiemannAtlas.exists_simplyConnected_open_subset x
      (M.homeomorph ⁻¹' P.carrier ∩ N.homeomorph ⁻¹' Q.carrier)
      ((P.isOpen.preimage M.homeomorph.continuous).inter (Q.isOpen.preimage N.homeomorph.continuous)) ⟨hxP, hxQ⟩
    have hUP : ∀ u ∈ U, M.homeomorph u ∈ P.carrier := fun _ hu => (hUW hu).1
    have hUQ : ∀ u ∈ U, N.homeomorph u ∈ Q.carrier := fun _ hu => (hUW hu).2
    let : SimplyConnectedSpace U := hUc
    refine ⟨U, hUo, hxU, Set.subset_univ _, ?_⟩
    apply Measure.ext
    intro s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs,
      M.areaMeasure_apply_patchLift P U hUo hUP s hs, N.areaMeasure_apply_patchLift Q U hUo hUQ s hs]
    exact (analytic_discCovers_lifts_area_eq R.toRiemannAtlas M.discCover N.discCover
      M.discCover_covering N.discCover_covering M.discCover_analytic N.discCover_analytic
      (M.patchLift P U hUP) (N.patchLift Q U hUQ)
      (M.patchLift_continuous P U hUP) (N.patchLift_continuous Q U hUQ) ⟨x, hxU⟩
      (fun u => (M.patchLift_projects P U hUP u).trans (N.patchLift_projects Q U hUQ u).symm)
      (Subtype.val ⁻¹' s) ((M.patchLift_isOpenEmbedding P U hUo hUP).measurableEmbedding.measurableSet_image.mpr
        (hs.preimage measurable_subtype_coe))).symm
  simpa only [Measure.restrict_univ] using he


/-- The presentation-independent hyperbolic area measure on the original surface. -/
def IsHyperbolicType.areaMeasure {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {R : RiemannSurface X} (hR : IsHyperbolicType R) : Measure X :=
  ((isHyperbolicType_iff_nonempty_model R).mp hR).some.areaMeasure

theorem IsHyperbolicType.areaMeasure_eq_model {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {R : RiemannSurface X} (hR : IsHyperbolicType R)
    (M : HyperbolicSurfaceModel R) : hR.areaMeasure = M.areaMeasure :=
  ((isHyperbolicType_iff_nonempty_model R).mp hR).some.areaMeasure_independent M

/-- Every conformal disc-quotient presentation computes this same intrinsic global measure
by the original squared line-element density in local disc coordinates. -/
theorem IsHyperbolicType.areaMeasure_apply_patch {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] {R : RiemannSurface X} (hR : IsHyperbolicType R)
    (M : HyperbolicSurfaceModel R) (P : DiscQuotientAreaPatch M.invariant)
    (s : Set X) (hs : MeasurableSet s) (hsP : M.homeomorph '' s ⊆ P.carrier) :
    hR.areaMeasure s = _root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicArea (P.lift '' (Subtype.val ⁻¹' (M.homeomorph '' s))) := by
  rw [hR.areaMeasure_eq_model M]
  exact M.areaMeasure_apply_patch P s hs hsP

end LowDimensionalTopology.Geometry.Surfaces
