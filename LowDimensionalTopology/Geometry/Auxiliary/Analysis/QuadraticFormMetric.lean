/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.DensityMetric
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Quadratic-form path metrics

A continuous field of pointwise positive quadratic forms gives a genuine length metric on any
connected open Euclidean domain. Its topology is the original Euclidean subspace topology.
Quadratic forms are represented by their symmetric bilinear polarizations. The coefficient
continuity is an explicit regularity condition; no smoothness
or global uniform ellipticity assumption is imposed.
-/

@[expose] public section
open scoped Topology
open Set Metric
namespace LowDimensionalTopology.Geometry.Auxiliary.Analysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A positive definite continuous bilinear form controls the background squared norm. -/
theorem quadraticForm_coercive (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E, v ≠ 0 → 0 < B v v) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : E, c * ‖v‖ ^ 2 ≤ B v v := by
  have hcont : Continuous (fun v : E => B v v) := by fun_prop
  obtain ⟨c, hc, hbound⟩ := (isCompact_sphere (0 : E) 1).exists_forall_le'
    hcont.continuousOn (a := 0) (fun v hv => hB v (by
      intro hv0
      simp [hv0] at hv))
  refine ⟨c, hc, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hunit : (‖v‖⁻¹ : ℝ) • v ∈ sphere (0 : E) 1 := by
    simp [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), hnorm.ne']
  have h := hbound _ hunit
  simp only [map_smul, smul_apply, smul_eq_mul] at h
  have heq : ‖v‖⁻¹ * (‖v‖⁻¹ * B v v) = B v v / ‖v‖ ^ 2 := by
    simp only [div_eq_mul_inv, pow_two]
    ring
  rw [heq] at h
  exact (le_div_iff₀ (sq_pos_of_pos hnorm)).mp h

/-- Positive definite quadratic unit balls are bounded in the original topology. -/
theorem quadraticForm_isVonNBounded (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hB : ∀ v : E, v ≠ 0 → 0 < B v v) :
    Bornology.IsVonNBounded ℝ {v : E | B v v < 1} := by
  obtain ⟨c, hc, hbound⟩ := quadraticForm_coercive B hB
  apply NormedSpace.isVonNBounded_of_isBounded ℝ
  refine (isBounded_closedBall (x := (0 : E)) (r := 1 + c⁻¹)).subset ?_
  intro v hv
  change B v v < 1 at hv
  rw [mem_closedBall, dist_zero_right]
  have h := hbound v
  have hc' : 0 < c⁻¹ := inv_pos.mpr hc
  have hsmall : ‖v‖ ^ 2 < c⁻¹ := by
    have hmul : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
    exact (mul_lt_mul_iff_right₀ hc).mp (by nlinarith [h.trans_lt hv])
  nlinarith [norm_nonneg v, sq_nonneg (‖v‖ - 1), sq_nonneg (c⁻¹)]

end LowDimensionalTopology.Geometry.Auxiliary.Analysis

namespace LowDimensionalTopology.Geometry.Auxiliary.Analysis
open Bundle Bornology Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A continuous field of positive definite symmetric quadratic forms, represented bilinearly. -/
structure PositiveQuadraticField (D : TopologicalSpace.Opens E) where
  bilinear : D → E →L[ℝ] E →L[ℝ] ℝ
  continuous : Continuous bilinear
  symmetric : ∀ x v w, bilinear x v w = bilinear x w v
  positive : ∀ x v, v ≠ 0 → 0 < bilinear x v v

/-- Evaluation of the coordinate quadratic form. -/
def PositiveQuadraticField.quadratic {D : TopologicalSpace.Opens E}
    (Q : PositiveQuadraticField D) (x : D) (v : E) : ℝ := Q.bilinear x v v

omit [FiniteDimensional ℝ E] in
/-- Each form is nonnegative, including at the zero vector. -/
theorem PositiveQuadraticField.nonnegative {D : TopologicalSpace.Opens E}
    (Q : PositiveQuadraticField D) (x : D) (v : E) : 0 ≤ Q.quadratic x v := by
  by_cases hv : v = 0
  · simp [PositiveQuadraticField.quadratic, hv]
  · exact (Q.positive x v hv).le

omit [FiniteDimensional ℝ E] in
/-- Continuity is imposed only on the coefficients, not their derivatives. -/
theorem PositiveQuadraticField.continuous_quadratic {D : TopologicalSpace.Opens E}
    (Q : PositiveQuadraticField D) : Continuous (fun p : D × E => Q.quadratic p.1 p.2) := by
  unfold PositiveQuadraticField.quadratic
  exact (Q.continuous.comp continuous_fst).clm_apply continuous_snd |>.clm_apply continuous_snd

/-- Every point has a positive coercivity constant; no uniform global constant is assumed. -/
theorem PositiveQuadraticField.coercive {D : TopologicalSpace.Opens E}
    (Q : PositiveQuadraticField D) (x : D) :
    ∃ c : ℝ, 0 < c ∧ ∀ v : E, c * ‖v‖ ^ 2 ≤ Q.quadratic x v :=
  quadraticForm_coercive (Q.bilinear x) (Q.positive x)

omit [FiniteDimensional ℝ E] in
/-- A continuous bilinear form has the expected quadratic operator bound. -/
theorem quadraticForm_abs_le (B : E →L[ℝ] E →L[ℝ] ℝ) (v : E) :
    |B v v| ≤ ‖B‖ * ‖v‖ ^ 2 := by
  calc
    |B v v| = ‖B v v‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖B v‖ * ‖v‖ := (B v).le_opNorm v
    _ ≤ (‖B‖ * ‖v‖) * ‖v‖ := mul_le_mul_of_nonneg_right (B.le_opNorm v) (norm_nonneg v)
    _ = ‖B‖ * ‖v‖ ^ 2 := by ring


end
end LowDimensionalTopology.Geometry.Auxiliary.Analysis

namespace LowDimensionalTopology.Geometry.Auxiliary.Analysis
open Bundle Bornology Manifold MeasureTheory
open scoped Manifold ContDiff ENNReal
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
set_option backward.isDefEq.respectTransparency false

def PositiveQuadraticField.riemannianMetric {D : TopologicalSpace.Opens E}
    (Q : PositiveQuadraticField D) :
    ContinuousRiemannianMetric E (fun x : D => TangentSpace 𝓘(ℝ, E) x) where
  inner x := by
    letI : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
      inferInstanceAs (NormedAddCommGroup E)
    letI : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) := inferInstanceAs (NormedSpace ℝ E)
    exact (Q.bilinear x).bilinearComp
      (tangentSpaceCastModel 𝓘(ℝ, E) x).toContinuousLinearMap
      (tangentSpaceCastModel 𝓘(ℝ, E) x).toContinuousLinearMap
  symm x v w := by
    change Q.bilinear x v w = Q.bilinear x w v
    exact Q.symmetric x _ _
  pos x v hv := by
    change 0 < Q.bilinear x ((tangentSpaceCastModel 𝓘(ℝ, E) x) v)
      ((tangentSpaceCastModel 𝓘(ℝ, E) x) v)
    exact Q.positive x _ (by simpa using hv)
  isVonNBounded x := by
    change IsVonNBounded ℝ {v : E | Q.bilinear x v v < 1}
    exact quadraticForm_isVonNBounded (Q.bilinear x) (Q.positive x)
  continuous := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [continuousAt_hom_bundle]
    refine ⟨continuousAt_id, ?_⟩
    convert Q.continuous.continuousAt using 1
    ext y v w
    rw [inCoordinates_apply_eq₂]
    · have hv (u : E) :
          (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).symm y u =
            (tangentSpaceCastModel 𝓘(ℝ, E) y).symm u := by
        have h := congrArg (fun A => A u) (openDomain_tangent_inverse_trivialization D x y)
        have hb : y ∈ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).baseSet := by
          rw [TangentBundle.trivializationAt_baseSet]
          exact openDomain_chart_source D x y
        simpa only [Trivialization.symmL_apply _ hb, ContinuousLinearMap.coe_coe,
          ContinuousLinearEquiv.coe_coe] using h
      simp [ContinuousLinearMap.bilinearComp_apply, hv, tangentSpaceCastModel]
    · exact openDomain_chart_source D x y
    · exact openDomain_chart_source D x y
    · simp


@[instance_reducible]
def PositiveQuadraticField.eMetricSpace {D : TopologicalSpace.Opens E}
    (Q : PositiveQuadraticField D) : EMetricSpace D :=
  letI : RiemannianBundle (fun x : D => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨Q.riemannianMetric.toRiemannianMetric⟩
  EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) D

/-- The quadratic length construction retains the domain's Euclidean subspace topology. -/
theorem PositiveQuadraticField.eMetricSpace_topology {D : TopologicalSpace.Opens E}
    (Q : PositiveQuadraticField D) :
    Q.eMetricSpace.toPseudoEMetricSpace.toUniformSpace.toTopologicalSpace = (inferInstance : TopologicalSpace D) := rfl

open scoped Bundle in
/-- The tangent norm is the square root of the prescribed coordinate quadratic form. -/
theorem PositiveQuadraticField.tangent_norm {D : TopologicalSpace.Opens E}
    (Q : PositiveQuadraticField D) (x : D) (v : TangentSpace 𝓘(ℝ, E) x) :
    letI : RiemannianBundle (fun y : D => TangentSpace 𝓘(ℝ, E) y) :=
      ⟨Q.riemannianMetric.toRiemannianMetric⟩
    ‖v‖ = Real.sqrt (Q.quadratic x ((tangentSpaceCastModel 𝓘(ℝ, E) x) v)) := by
  let : RiemannianBundle (fun y : D => TangentSpace 𝓘(ℝ, E) y) :=
    ⟨Q.riemannianMetric.toRiemannianMetric⟩
  rw [norm_eq_sqrt_real_inner]
  rfl

/-- The length of one curve piece is the integral of the square root of its quadratic speed. -/
def PositiveQuadraticField.pieceLength {D : TopologicalSpace.Opens E}
    (Q : PositiveQuadraticField D) (γ : ℝ → D) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc a b, ENNReal.ofReal (Real.sqrt (Q.quadratic (γ t)
    ((tangentSpaceCastModel 𝓘(ℝ, E) (γ t)) (mfderiv[Icc a b] γ t 1))))


open scoped Bundle in
theorem PositiveQuadraticField.pieceLength_eq_pathELength {D : TopologicalSpace.Opens E}
    (Q : PositiveQuadraticField D) (γ : ℝ → D) (a b : ℝ) :
    letI : RiemannianBundle (fun x : D => TangentSpace 𝓘(ℝ, E) x) :=
      ⟨Q.riemannianMetric.toRiemannianMetric⟩
    Q.pieceLength γ a b = pathELength 𝓘(ℝ, E) γ a b := by
  let : RiemannianBundle (fun x : D => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨Q.riemannianMetric.toRiemannianMetric⟩
  rw [pathELength_eq_lintegral_mfderivWithin_Icc]
  unfold PositiveQuadraticField.pieceLength
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [← Q.tangent_norm]
  exact ofReal_norm _

/-- The quadratic integral length of a finite chain. -/
def PositiveQuadraticField.chainLength {D : TopologicalSpace.Opens E}
    (Q : PositiveQuadraticField D) {x y : D} : RiemannianC1Chain 𝓘(ℝ, E) D x y → ℝ≥0∞
  | .nil _ => 0
  | .cons γ a b _ _ _ _ tail => Q.pieceLength γ a b + Q.chainLength tail

/-- infimum of lengths of finite piecewise C1 curves. -/
def PositiveQuadraticField.piecewiseEDist {D : TopologicalSpace.Opens E}
    (Q : PositiveQuadraticField D) (x y : D) : ℝ≥0∞ :=
  ⨅ c : RiemannianC1Chain 𝓘(ℝ, E) D x y, Q.chainLength c

open scoped Bundle in
theorem PositiveQuadraticField.chainLength_eq {D : TopologicalSpace.Opens E}
    (Q : PositiveQuadraticField D) {x y : D} (c : RiemannianC1Chain 𝓘(ℝ, E) D x y) :
    letI : RiemannianBundle (fun x : D => TangentSpace 𝓘(ℝ, E) x) :=
      ⟨Q.riemannianMetric.toRiemannianMetric⟩
    Q.chainLength c = c.length := by
  let : RiemannianBundle (fun x : D => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨Q.riemannianMetric.toRiemannianMetric⟩
  induction c with
  | nil x => rfl
  | cons γ a b hab hc ha hb tail ih =>
      simp only [PositiveQuadraticField.chainLength, RiemannianC1Chain.length,
        Q.pieceLength_eq_pathELength, ih]

open scoped Bundle in
theorem PositiveQuadraticField.piecewiseEDist_eq_riemannianEDist {D : TopologicalSpace.Opens E}
    (Q : PositiveQuadraticField D) (x y : D) :
    letI : RiemannianBundle (fun x : D => TangentSpace 𝓘(ℝ, E) x) :=
      ⟨Q.riemannianMetric.toRiemannianMetric⟩
    Q.piecewiseEDist x y = riemannianEDist 𝓘(ℝ, E) x y := by
  let : RiemannianBundle (fun x : D => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨Q.riemannianMetric.toRiemannianMetric⟩
  change (⨅ c : RiemannianC1Chain 𝓘(ℝ, E) D x y, Q.chainLength c) = _
  simp_rw [Q.chainLength_eq]
  exact piecewiseC1EDist_eq_riemannianEDist x y

theorem PositiveQuadraticField.eMetricSpace_edist {D : TopologicalSpace.Opens E}
    (Q : PositiveQuadraticField D) (x y : D) :
    @edist D Q.eMetricSpace.toEDist x y = Q.piecewiseEDist x y := by
  exact (Q.piecewiseEDist_eq_riemannianEDist x y).symm

/-- On a connected open domain the quadratic path distance is finite. -/
theorem PositiveQuadraticField.piecewiseEDist_ne_top {D : TopologicalSpace.Opens E}
    [PreconnectedSpace D] (Q : PositiveQuadraticField D) (x y : D) :
    Q.piecewiseEDist x y ≠ ⊤ := by
  let := Q.eMetricSpace
  rw [← Q.eMetricSpace_edist]
  exact connected_edist_ne_top x y

/-- The genuine finite metric associated to a continuous pointwise positive quadratic field. -/
@[instance_reducible]
def PositiveQuadraticField.metricSpace {D : TopologicalSpace.Opens E} [PreconnectedSpace D]
    (Q : PositiveQuadraticField D) : MetricSpace D :=
  letI := Q.eMetricSpace
  connectedEMetricToMetric D

/-- The length-infimum metric has precisely the Euclidean subspace topology. -/
theorem PositiveQuadraticField.metricSpace_topology {D : TopologicalSpace.Opens E}
    [PreconnectedSpace D] (Q : PositiveQuadraticField D) :
    Q.metricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace D) := rfl

/-- The metric is exactly the finite real value of the piecewise quadratic length infimum. -/
theorem PositiveQuadraticField.metricSpace_dist {D : TopologicalSpace.Opens E}
    [PreconnectedSpace D] (Q : PositiveQuadraticField D) (x y : D) :
    @dist D Q.metricSpace.toDist x y = (Q.piecewiseEDist x y).toReal := by
  change (Q.eMetricSpace.toEDist.edist x y).toReal = _
  rw [Q.eMetricSpace_edist]


omit [FiniteDimensional ℝ E] in
/-- For open Euclidean domains, tangent velocities are the ordinary coordinate derivative. -/
theorem quadratic_openDomain_velocity {D : TopologicalSpace.Opens E} {γ : ℝ → D}
    {a b t : ℝ} (hγ : CMDiff[Icc a b] 1 γ) (ht : t ∈ Icc a b) :
    (tangentSpaceCastModel 𝓘(ℝ, E) (γ t)) (mfderiv[Icc a b] γ t 1) =
      derivWithin (fun s => (γ s : E)) (Icc a b) t := by
  have hm := (hγ.mdifferentiableOn one_ne_zero) t ht
  rw [hm.mfderivWithin]
  simp only [mfld_simps, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rw [← fderivWithin_derivWithin]
  rfl


omit [FiniteDimensional ℝ E] in
/-- The quadratic line integral in ordinary Euclidean coordinates. -/
theorem PositiveQuadraticField.pieceLength_eq_coordinate_integral {D : TopologicalSpace.Opens E}
    (Q : PositiveQuadraticField D) (γ : ℝ → D) (a b : ℝ)
    (hγ : CMDiff[Icc a b] 1 γ) :
    Q.pieceLength γ a b = ∫⁻ t in Icc a b,
      ENNReal.ofReal (Real.sqrt (Q.quadratic (γ t)
        (derivWithin (fun s => (γ s : E)) (Icc a b) t))) := by
  unfold PositiveQuadraticField.pieceLength
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [quadratic_openDomain_velocity hγ ht]

end
end LowDimensionalTopology.Geometry.Auxiliary.Analysis
