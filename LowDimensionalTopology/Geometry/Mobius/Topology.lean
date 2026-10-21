/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Mobius.Metric.ChordalIsometries
public import LowDimensionalTopology.Geometry.Mobius.Trace.MobiusInvariants
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.UniformSpace.HeineCantor

public import LowDimensionalTopology.Geometry.Mobius.CrossRatio.MobiusTriples
public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.DiscreteSubset
public import Mathlib.Topology.Algebra.Group.Neighborhood

public import LowDimensionalTopology.Geometry.DiscreteGroups.Matrix
public import Mathlib.Topology.Covering.Basic

/-!
# Uniform and quotient topologies on the complex Möbius group

The chordal supremum metric agrees with the quotient topology from
determinant-one matrices. A continuous local section near the identity
provides the open projection and the two-sheeted covering, whose fibers
are the two signed representatives. Norm sublevel compactness gives
countability and norm divergence for discrete subgroups. Three-point
convergence recovers local matrix representatives and group convergence.
-/

@[expose] public section

open Set Filter
open scoped Topology OnePoint

namespace LowDimensionalTopology.Geometry.Mobius

noncomputable section

local instance mobiusTopologyChordalMetric : MetricSpace ExtendedComplex := complexChordalMetricSpace

/-- The original actual Mobius action bundled as a continuous map on the compact chordal sphere. -/
def complexMobiusContinuousMap (f : complexMobiusGroup) : C(ExtendedComplex, ExtendedComplex) :=
  ⟨(f : Equiv.Perm ExtendedComplex), by
    obtain ⟨A, rfl⟩ := mobiusMatrixProjection_surjective f
    exact continuous_fractionalLinear A⟩

theorem complexMobiusContinuousMap_injective : Function.Injective complexMobiusContinuousMap := by
  intro f g h
  apply Subtype.ext
  apply Equiv.ext
  intro z
  exact congrArg (fun k : C(ExtendedComplex, ExtendedComplex) => k z) h

/-- The canonical uniform chordal metric on the actual complex Mobius group. -/
instance complexMobiusMetricSpace : MetricSpace complexMobiusGroup :=
  MetricSpace.induced complexMobiusContinuousMap complexMobiusContinuousMap_injective inferInstance

theorem complexMobiusContinuousMap_isometry : Isometry complexMobiusContinuousMap :=
  MetricSpace.isometry_induced complexMobiusContinuousMap complexMobiusContinuousMap_injective

/-- The uniform-convergence topology. -/
@[instance_reducible]
def mobiusUniformTopology : TopologicalSpace complexMobiusGroup := inferInstance

/-- The quotient topology induced by the actual determinant-one matrix projection. -/
@[instance_reducible]
def mobiusQuotientTopology : TopologicalSpace complexMobiusGroup :=
  TopologicalSpace.coinduced mobiusSpecialLinearProjection inferInstance

/-- The source's supremum displacement metric. -/
def mobiusUniformDist (f g : complexMobiusGroup) : ℝ := dist f g

theorem mobiusUniformDist_eq_iSup (f g : complexMobiusGroup) :
    mobiusUniformDist f g =
      ⨆ z : ExtendedComplex, complexChordalDist ((f : Equiv.Perm ExtendedComplex) z)
        ((g : Equiv.Perm ExtendedComplex) z) :=
  ContinuousMap.dist_eq_iSup

theorem mobiusUniformDist_mul_right (f g h : complexMobiusGroup) :
    mobiusUniformDist (f * h) (g * h) = mobiusUniformDist f g := by
  apply le_antisymm
  · change dist (complexMobiusContinuousMap (f * h)) (complexMobiusContinuousMap (g * h)) ≤
      dist (complexMobiusContinuousMap f) (complexMobiusContinuousMap g)
    apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro z
    exact ContinuousMap.dist_apply_le_dist (f := complexMobiusContinuousMap f)
      (g := complexMobiusContinuousMap g) ((h : Equiv.Perm ExtendedComplex) z)
  · change dist (complexMobiusContinuousMap f) (complexMobiusContinuousMap g) ≤
      dist (complexMobiusContinuousMap (f * h)) (complexMobiusContinuousMap (g * h))
    apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro z
    have hp := ContinuousMap.dist_apply_le_dist (f := complexMobiusContinuousMap (f * h))
      (g := complexMobiusContinuousMap (g * h)) ((h : Equiv.Perm ExtendedComplex).symm z)
    change dist ((f : Equiv.Perm ExtendedComplex)
      ((h : Equiv.Perm ExtendedComplex) ((h : Equiv.Perm ExtendedComplex).symm z)))
      ((g : Equiv.Perm ExtendedComplex)
        ((h : Equiv.Perm ExtendedComplex) ((h : Equiv.Perm ExtendedComplex).symm z))) ≤ _ at hp
    simpa only [complexMobiusContinuousMap, ContinuousMap.coe_mk, Equiv.apply_symm_apply] using hp

theorem mobiusUniformDist_eq_mul_inv (f g : complexMobiusGroup) :
    mobiusUniformDist f g = mobiusUniformDist (f * g⁻¹) 1 := by
  simpa only [mul_inv_cancel] using (mobiusUniformDist_mul_right f g g⁻¹).symm

theorem complexMobius_tendsto_iff_tendstoUniformly {α : Type*} {p : Filter α}
    (F : α → complexMobiusGroup) (f : complexMobiusGroup) :
    Tendsto F p (𝓝 f) ↔
      TendstoUniformly (fun i z => (F i : Equiv.Perm ExtendedComplex) z)
        (fun z => (f : Equiv.Perm ExtendedComplex) z) p := by
  rw [complexMobiusContinuousMap_isometry.isEmbedding.isInducing.tendsto_nhds_iff]
  exact ContinuousMap.tendsto_iff_tendstoUniformly

theorem complexMobius_uniform_continuous_mul :
    Continuous (fun p : complexMobiusGroup × complexMobiusGroup => p.1 * p.2) := by
  apply complexMobiusContinuousMap_isometry.comp_continuous_iff.mp
  have h : Continuous (fun p : complexMobiusGroup × complexMobiusGroup =>
      (complexMobiusContinuousMap p.2, complexMobiusContinuousMap p.1)) :=
    (complexMobiusContinuousMap_isometry.continuous.comp continuous_snd).prodMk
      (complexMobiusContinuousMap_isometry.continuous.comp continuous_fst)
  exact ContinuousMap.continuous_comp'.comp h

theorem complexMobius_uniform_continuous_inv :
    Continuous (fun f : complexMobiusGroup => f⁻¹) := by
  rw [continuous_iff_continuousAt]
  intro g
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have hu : UniformContinuous (fun z => (g : Equiv.Perm ExtendedComplex).symm z) :=
    CompactSpace.uniformContinuous_of_continuous (complexMobiusContinuousMap g⁻¹).continuous
  obtain ⟨δ, hδ, hprop⟩ := Metric.uniformContinuous_iff.mp hu ε hε
  refine ⟨δ, hδ, ?_⟩
  intro f hf
  change dist (complexMobiusContinuousMap f⁻¹) (complexMobiusContinuousMap g⁻¹) < ε
  apply ContinuousMap.dist_lt_iff_of_nonempty.mpr
  intro z
  change dist ((f : Equiv.Perm ExtendedComplex).symm z)
    ((g : Equiv.Perm ExtendedComplex).symm z) < ε
  have hpoint : dist ((f : Equiv.Perm ExtendedComplex) ((f : Equiv.Perm ExtendedComplex).symm z))
      ((g : Equiv.Perm ExtendedComplex) ((f : Equiv.Perm ExtendedComplex).symm z)) < δ :=
    (ContinuousMap.dist_apply_le_dist (f := complexMobiusContinuousMap f)
      (g := complexMobiusContinuousMap g) ((f : Equiv.Perm ExtendedComplex).symm z)).trans_lt hf
  have hh := hprop hpoint
  simpa only [Equiv.symm_apply_apply, Equiv.apply_symm_apply, dist_comm] using hh

instance complexMobius_isTopologicalGroup : IsTopologicalGroup complexMobiusGroup where
  continuous_mul := complexMobius_uniform_continuous_mul
  continuous_inv := complexMobius_uniform_continuous_inv

/-- A source-discrete subgroup uses the induced topology of the actual uniform Mobius metric. -/
def IsDiscreteMobiusSubgroup (H : Subgroup complexMobiusGroup) : Prop := DiscreteTopology H

theorem mobius_projection_isQuotientMap_for_quotientTopology :
    @Topology.IsQuotientMap Auxiliary.Algebra.SpecialLinear2 complexMobiusGroup inferInstance
      mobiusQuotientTopology mobiusSpecialLinearProjection := by
  let mobiusProjectionQuotientTopology : TopologicalSpace complexMobiusGroup := mobiusQuotientTopology
  exact ⟨⟨rfl⟩, mobiusSpecialLinearProjection_surjective⟩



theorem complexProjectivePoint_reciprocal_chart (v : Fin 2 → ℂ) (h0 : v 0 ≠ 0) :
    complexProjectivePoint v = reciprocal ((v 1 / v 0 : ℂ) : ExtendedComplex) := by
  by_cases h1 : v 1 = 0
  · simp [complexProjectivePoint, h1, reciprocal_zero]
  · rw [complexProjectivePoint, ite_eq_right h1,
      reciprocal_coe _ (div_ne_zero h1 h0), inv_div]

/-- The homogeneous chart is jointly continuous on the entire nonzero two-vector space,
including the vectors representing infinity. -/
theorem complexProjectivePoint_continuousAt {v : Fin 2 → ℂ} (hv : v ≠ 0) :
    ContinuousAt complexProjectivePoint v := by
  by_cases h1 : v 1 = 0
  · have h0 : v 0 ≠ 0 := by
      intro h0
      exact hv (by ext i; fin_cases i <;> simp [h0, h1])
    have hq : ContinuousAt (fun w : Fin 2 → ℂ => w 1 / w 0) v :=
      (continuous_apply 1).continuousAt.div (continuous_apply 0).continuousAt h0
    have hc := continuous_reciprocal.continuousAt.comp
      (OnePoint.continuous_coe.continuousAt.comp hq)
    apply hc.congr_of_eventuallyEq
    filter_upwards [(continuous_apply 0).continuousAt.eventually_ne h0] with w hw
    exact complexProjectivePoint_reciprocal_chart w hw
  · have hq : ContinuousAt (fun w : Fin 2 → ℂ => w 0 / w 1) v :=
      (continuous_apply 0).continuousAt.div (continuous_apply 1).continuousAt h1
    have hc := OnePoint.continuous_coe.continuousAt.comp hq
    apply hc.congr_of_eventuallyEq
    filter_upwards [(continuous_apply 1).continuousAt.eventually_ne h1] with w hw
    simp only [complexProjectivePoint, ite_eq_right hw, Function.comp_apply]

theorem complexProjectivePoint_nonzero_continuous :
    Continuous (fun v : {v : Fin 2 → ℂ // v ≠ 0} => complexProjectivePoint v.val) := by
  rw [continuous_iff_continuousAt]
  intro v
  exact (complexProjectivePoint_continuousAt v.property).comp continuous_subtype_val.continuousAt

theorem complexProjectivePoint_scalar (c : ℂ) (hc : c ≠ 0) (v : Fin 2 → ℂ) :
    complexProjectivePoint (c • v) = complexProjectivePoint v := by
  by_cases h1 : v 1 = 0
  · simp [complexProjectivePoint, Pi.smul_apply, smul_eq_mul, h1]
  · simp only [complexProjectivePoint, Pi.smul_apply, smul_eq_mul,
      ite_eq_right (mul_ne_zero hc h1), ite_eq_right h1]
    congr 1
    field_simp

/-- A compact Euclidean normalization of homogeneous complex coordinates. -/
abbrev ComplexCompactPair := {v : Fin 2 → ℂ // complexVectorQuadratic v = 1}

instance complexCompactPair_compactSpace : CompactSpace ComplexCompactPair := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_univ_pi (fun _ : Fin 2 => isCompact_closedBall (0 : ℂ) 1)).of_isClosed_subset
  · apply isClosed_eq _ continuous_const
    unfold complexVectorQuadratic
    fun_prop
  · intro v hv i _
    rw [Metric.mem_closedBall, dist_zero_right]
    have hh := hv
    change ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 = 1 at hh
    fin_cases i
    · change ‖v 0‖ ≤ 1
      nlinarith [norm_nonneg (v 0), sq_nonneg ‖v 1‖]
    · change ‖v 1‖ ≤ 1
      nlinarith [norm_nonneg (v 1), sq_nonneg ‖v 0‖]

theorem complexCompactPair_ne_zero (v : ComplexCompactPair) : v.val ≠ 0 := by
  intro hv
  have hh := v.property
  simp only [hv, complexVectorQuadratic, Pi.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0),
    zero_add] at hh
  norm_num at hh

def complexCompactPairPoint (v : ComplexCompactPair) : ExtendedComplex :=
  complexProjectivePoint v.val

theorem complexCompactPairPoint_continuous : Continuous complexCompactPairPoint := by
  rw [continuous_iff_continuousAt]
  intro v
  exact (complexProjectivePoint_continuousAt (complexCompactPair_ne_zero v)).comp
    continuous_subtype_val.continuousAt

theorem complexCompactPairPoint_surjective : Function.Surjective complexCompactPairPoint := by
  intro z
  let v := complexProjectiveVector z
  have hv : v ≠ 0 := complexProjectiveVector_ne_zero z
  have hvn : 0 < complexVectorQuadratic v := complexVectorQuadratic_pos hv
  let r : ℝ := Real.sqrt (complexVectorQuadratic v)
  have hr : 0 < r := Real.sqrt_pos.mpr hvn
  have hrsq : r ^ 2 = complexVectorQuadratic v := Real.sq_sqrt hvn.le
  let c : ℂ := ((r⁻¹ : ℝ) : ℂ)
  have hc : c ≠ 0 := by
    dsimp only [c]
    exact_mod_cast inv_ne_zero hr.ne'
  have hn : complexVectorQuadratic (c • v) = 1 := by
    rw [complexVectorQuadratic_smul]
    dsimp only [c]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), ← hrsq]
    field_simp
  refine ⟨⟨c • v, hn⟩, ?_⟩
  exact (complexProjectivePoint_scalar c hc v).trans (complexProjectivePoint_vector z)

local instance projectiveContinuityChordalMetric : MetricSpace ExtendedComplex := complexChordalMetricSpace

def complexCompactPairEvaluation (f : complexMobiusGroup) : C(ComplexCompactPair, ExtendedComplex) :=
  ⟨fun v => (f : Equiv.Perm ExtendedComplex) (complexCompactPairPoint v),
    (complexMobiusContinuousMap f).continuous.comp complexCompactPairPoint_continuous⟩

theorem complexCompactPairEvaluation_isometry : Isometry complexCompactPairEvaluation := by
  rw [isometry_iff_dist_eq]
  intro f g
  apply le_antisymm
  · change dist (complexCompactPairEvaluation f) (complexCompactPairEvaluation g) ≤
      dist (complexMobiusContinuousMap f) (complexMobiusContinuousMap g)
    apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro v
    exact ContinuousMap.dist_apply_le_dist (f := complexMobiusContinuousMap f)
      (g := complexMobiusContinuousMap g) (complexCompactPairPoint v)
  · change dist (complexMobiusContinuousMap f) (complexMobiusContinuousMap g) ≤
      dist (complexCompactPairEvaluation f) (complexCompactPairEvaluation g)
    apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro z
    obtain ⟨v, rfl⟩ := complexCompactPairPoint_surjective z
    exact ContinuousMap.dist_apply_le_dist (f := complexCompactPairEvaluation f)
      (g := complexCompactPairEvaluation g) v

theorem specialLinear_compactPair_point (A : Auxiliary.Algebra.SpecialLinear2) (v : ComplexCompactPair) :
    (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) (complexCompactPairPoint v) =
      complexProjectivePoint (Matrix.SpecialLinearGroup.toGL A • v.val) := by
  have hp := congrArg (fun f : fractionalLinearGroup => (f : Equiv.Perm ExtendedComplex))
    (mobiusSpecialLinearProjection_equiv A)
  change (complexMobiusEquivFractionalLinear (mobiusSpecialLinearProjection A) :
    Equiv.Perm ExtendedComplex) = fractionalLinear (Matrix.SpecialLinearGroup.toGL A) at hp
  rw [complexMobiusEquivFractionalLinear_apply] at hp
  rw [hp]
  exact (complexProjectivePoint_smul _ _ (complexCompactPair_ne_zero v)).symm

theorem specialLinear_compactPair_joint_continuous :
    Continuous (fun p : Auxiliary.Algebra.SpecialLinear2 × ComplexCompactPair =>
      complexProjectivePoint (Matrix.SpecialLinearGroup.toGL p.1 • p.2.val)) := by
  have ha (i j : Fin 2) : Continuous (fun p : Auxiliary.Algebra.SpecialLinear2 × ComplexCompactPair =>
      p.1 i j) := (continuous_apply j).comp
      (Matrix.SpecialLinearGroup.continuous_apply Prod.fst continuous_fst i)
  have hb (i : Fin 2) : Continuous (fun p : Auxiliary.Algebra.SpecialLinear2 × ComplexCompactPair =>
      p.2.val i) := (continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)
  have hv : Continuous (fun p : Auxiliary.Algebra.SpecialLinear2 × ComplexCompactPair =>
      Matrix.SpecialLinearGroup.toGL p.1 • p.2.val) := by
    simp only [Matrix.GeneralLinearGroup.fin_two_smul]
    apply continuous_pi
    intro i
    fin_cases i
    · change Continuous (fun p : Auxiliary.Algebra.SpecialLinear2 × ComplexCompactPair =>
        p.1 0 0 * p.2.val 0 + p.1 0 1 * p.2.val 1)
      exact ((ha 0 0).mul (hb 0)).add ((ha 0 1).mul (hb 1))
    · change Continuous (fun p : Auxiliary.Algebra.SpecialLinear2 × ComplexCompactPair =>
        p.1 1 0 * p.2.val 0 + p.1 1 1 * p.2.val 1)
      exact ((ha 1 0).mul (hb 0)).add ((ha 1 1).mul (hb 1))
  rw [continuous_iff_continuousAt]
  intro p
  exact ContinuousAt.comp (f := fun p : Auxiliary.Algebra.SpecialLinear2 × ComplexCompactPair =>
      Matrix.SpecialLinearGroup.toGL p.1 • p.2.val) (g := complexProjectivePoint) (x := p)
    (complexProjectivePoint_continuousAt
    ((smul_ne_zero_iff_ne (Matrix.SpecialLinearGroup.toGL p.1)).mpr
      (complexCompactPair_ne_zero p.2))) hv.continuousAt

/-- Continuity of the actual SL2 projection for the uniform chordal topology,
proved through a compact homogeneous-coordinate model without a quantitative weakening. -/
theorem mobiusSpecialLinearProjection_continuous : Continuous mobiusSpecialLinearProjection := by
  apply complexCompactPairEvaluation_isometry.comp_continuous_iff.mp
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : Auxiliary.Algebra.SpecialLinear2 × ComplexCompactPair =>
    complexCompactPairEvaluation (mobiusSpecialLinearProjection p.1) p.2)
  have he : (fun p : Auxiliary.Algebra.SpecialLinear2 × ComplexCompactPair =>
      complexCompactPairEvaluation (mobiusSpecialLinearProjection p.1) p.2) =
      (fun p => complexProjectivePoint (Matrix.SpecialLinearGroup.toGL p.1 • p.2.val)) := by
    funext p
    exact specialLinear_compactPair_point p.1 p.2
  rw [he]
  exact specialLinear_compactPair_joint_continuous



open Matrix
open scoped Matrix.Norms.Frobenius

/-- The two-dimensional complex wedge is bounded by the two Euclidean quadratic norms. -/
theorem complex_wedge_norm_sq_le (u w : Fin 2 → ℂ) :
    ‖u 0 * w 1 - u 1 * w 0‖ ^ 2 ≤
      complexVectorQuadratic u * complexVectorQuadratic w := by
  have ht := norm_sub_le (u 0 * w 1) (u 1 * w 0)
  rw [norm_mul, norm_mul] at ht
  have hsq : ‖u 0 * w 1 - u 1 * w 0‖ ^ 2 ≤
      (‖u 0‖ * ‖w 1‖ + ‖u 1‖ * ‖w 0‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr ht
  unfold complexVectorQuadratic
  nlinarith [sq_nonneg (‖u 0‖ * ‖w 0‖ - ‖u 1‖ * ‖w 1‖)]

/-- A two-term complex row obeys the Euclidean Cauchy--Schwarz inequality. -/
theorem complex_row_norm_sq_le (a b x y : ℂ) :
    ‖a * x + b * y‖ ^ 2 ≤ (‖a‖ ^ 2 + ‖b‖ ^ 2) * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
  have ht := norm_add_le (a * x) (b * y)
  rw [norm_mul, norm_mul] at ht
  have hsq : ‖a * x + b * y‖ ^ 2 ≤ (‖a‖ * ‖x‖ + ‖b‖ * ‖y‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr ht
  nlinarith [sq_nonneg (‖a‖ * ‖y‖ - ‖b‖ * ‖x‖)]

theorem complexVectorQuadratic_mulVec_le (A : Auxiliary.Algebra.ComplexMatrix2) (v : Fin 2 → ℂ) :
    complexVectorQuadratic (A *ᵥ v) ≤ Auxiliary.Algebra.matrixNorm A ^ 2 * complexVectorQuadratic v := by
  have h0 := complex_row_norm_sq_le (A 0 0) (A 0 1) (v 0) (v 1)
  have h1 := complex_row_norm_sq_le (A 1 0) (A 1 1) (v 0) (v 1)
  rw [Auxiliary.Algebra.matrixNorm_sq]
  simp only [complexVectorQuadratic, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  nlinarith

theorem complexProjectivePoint_displacement_bound (A : FractionalLinearMatrix)
    (v : ComplexCompactPair) :
    complexChordalDist (complexProjectivePoint (A • v.val)) (complexProjectivePoint v.val) ≤
      2 * Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) := by
  let u : Fin 2 → ℂ := A • v.val
  let w : Fin 2 → ℂ := v.val - u
  have hu : u ≠ 0 := (smul_ne_zero_iff_ne A).mpr (complexCompactPair_ne_zero v)
  have hqu : 0 < complexVectorQuadratic u := complexVectorQuadratic_pos hu
  have hwedge : u 0 * v.val 1 - u 1 * v.val 0 = u 0 * w 1 - u 1 * w 0 := by
    dsimp only [w, Pi.sub_apply]
    ring
  have hwedgebound := complex_wedge_norm_sq_le u w
  rw [← hwedge] at hwedgebound
  have hw : w = -(((A : Auxiliary.Algebra.ComplexMatrix2) - 1) *ᵥ v.val) := by
    dsimp only [w, u]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [Units.smul_def, Matrix.smul_eq_mulVec]
    abel
  have hmul := complexVectorQuadratic_mulVec_le ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) v.val
  rw [← complexVectorQuadratic_neg, ← hw, v.property, mul_one] at hmul
  have hdist := complexChordalDist_projective_sq u v.val hu (complexCompactPair_ne_zero v)
  change complexChordalDist (complexProjectivePoint u) (complexProjectivePoint v.val) ^ 2 =
    4 * ‖u 0 * v.val 1 - u 1 * v.val 0‖ ^ 2 /
      (complexVectorQuadratic u * complexVectorQuadratic v.val) at hdist
  rw [v.property, mul_one] at hdist
  have hs : complexChordalDist (complexProjectivePoint u) (complexProjectivePoint v.val) ^ 2 ≤
      4 * Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) ^ 2 := by
    rw [hdist]
    apply (div_le_iff₀ hqu).mpr
    nlinarith [mul_le_mul_of_nonneg_left hmul hqu.le]
  have hn := Auxiliary.Algebra.matrixNorm_nonneg ((A : Auxiliary.Algebra.ComplexMatrix2) - 1)
  exact (sq_le_sq₀ (complexChordalDist_nonneg _ _) (by positivity)).mp (by nlinarith)


local instance displacementChordalMetric : MetricSpace ExtendedComplex := complexChordalMetricSpace

/-- A homogeneous-coordinate estimate improves the source constant to two. -/
theorem mobiusSpecialLinear_displacement_le_two (A : Auxiliary.Algebra.SpecialLinear2) :
    mobiusUniformDist (mobiusSpecialLinearProjection A) 1 ≤
      2 * Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) := by
  change dist (complexMobiusContinuousMap (mobiusSpecialLinearProjection A))
    (complexMobiusContinuousMap 1) ≤ _
  apply (ContinuousMap.dist_le (mul_nonneg (by norm_num)
    (Auxiliary.Algebra.matrixNorm_nonneg _))).mpr
  intro z
  obtain ⟨v, rfl⟩ := complexCompactPairPoint_surjective z
  change complexChordalDist
    ((mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) (complexCompactPairPoint v))
    (complexCompactPairPoint v) ≤ _
  rw [specialLinear_compactPair_point]
  exact complexProjectivePoint_displacement_bound (Matrix.SpecialLinearGroup.toGL A) v

/-- With the exact stated constant. -/
theorem mobiusUniformDist_projection_one_le_matrixNorm (A : Auxiliary.Algebra.SpecialLinear2) :
    mobiusUniformDist (mobiusSpecialLinearProjection A) 1 ≤
      Real.sqrt 6 * Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - 1) := by
  apply (mobiusSpecialLinear_displacement_le_two A).trans
  have hs : 2 ≤ Real.sqrt 6 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 6 by norm_num), Real.sqrt_nonneg (6 : ℝ)]
  exact mul_le_mul_of_nonneg_right hs (Auxiliary.Algebra.matrixNorm_nonneg _)

/-- The Frobenius norm of the inverse of a determinant-one two by two matrix. -/
theorem specialLinear_matrixNorm_inv (B : Auxiliary.Algebra.SpecialLinear2) :
    Auxiliary.Algebra.matrixNorm ((B⁻¹ : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) =
      Auxiliary.Algebra.matrixNorm (B : Auxiliary.Algebra.ComplexMatrix2) := by
  rw [Matrix.SpecialLinearGroup.coe_inv, Auxiliary.Algebra.matrixNorm_adjugate]

/-- The exact matrix-pair displacement estimate. -/
theorem mobiusSpecialLinear_displacement_pair (A B : Auxiliary.Algebra.SpecialLinear2) :
    mobiusUniformDist (mobiusSpecialLinearProjection A) (mobiusSpecialLinearProjection B) ≤
      Real.sqrt 6 * Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - B) *
        Auxiliary.Algebra.matrixNorm (B : Auxiliary.Algebra.ComplexMatrix2) := by
  rw [mobiusUniformDist_eq_mul_inv, ← map_inv, ← map_mul]
  have h := mobiusUniformDist_projection_one_le_matrixNorm (A * B⁻¹)
  have hm : ((A * B⁻¹ : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) - 1 =
      ((A : Auxiliary.Algebra.ComplexMatrix2) - B) *
        ((B⁻¹ : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, sub_mul]
    have hi := congrArg (fun C : Auxiliary.Algebra.SpecialLinear2 => (C : Auxiliary.Algebra.ComplexMatrix2))
      (mul_inv_cancel B)
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] at hi
    rw [hi]
  rw [hm] at h
  apply h.trans
  have hm' := Auxiliary.Algebra.matrixNorm_mul_le ((A : Auxiliary.Algebra.ComplexMatrix2) - B)
    ((B⁻¹ : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2)
  rw [specialLinear_matrixNorm_inv] at hm'
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hm' (Real.sqrt_nonneg 6)


local instance discreteMobiusChordalMetric : MetricSpace ExtendedComplex := complexChordalMetricSpace

instance complexMobius_secondCountableTopology : SecondCountableTopology complexMobiusGroup :=
  complexMobiusContinuousMap_isometry.isEmbedding.secondCountableTopology

theorem discreteMobius_countable (H : Subgroup complexMobiusGroup)
    (hH : IsDiscreteMobiusSubgroup H) : Countable H := by
  let : DiscreteTopology H := hH
  exact (TopologicalSpace.separableSpace_iff_countable).mp inferInstance

theorem specialLinear_norm_sublevel_isCompact (R : ℝ) :
    IsCompact {A : Auxiliary.Algebra.SpecialLinear2 | Auxiliary.Algebra.matrixNorm A ≤ R} := by
  have he : Topology.IsClosedEmbedding
      (fun A : Auxiliary.Algebra.SpecialLinear2 => (A : Auxiliary.Algebra.ComplexMatrix2)) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val
  simpa [Auxiliary.Algebra.matrixNorm, Metric.closedBall, dist_eq_norm] using
    he.isCompact_preimage (isCompact_closedBall (0 : Auxiliary.Algebra.ComplexMatrix2) R)

theorem mobius_norm_sublevel_isCompact (R : ℝ) :
    IsCompact {f : complexMobiusGroup | mobiusNormalizedNorm f ≤ R} := by
  have he : {f : complexMobiusGroup | mobiusNormalizedNorm f ≤ R} =
      mobiusSpecialLinearProjection '' {A : Auxiliary.Algebra.SpecialLinear2 | Auxiliary.Algebra.matrixNorm A ≤ R} := by
    ext f
    constructor
    · intro hf
      obtain ⟨A, rfl⟩ := mobiusSpecialLinearProjection_surjective f
      refine ⟨A, ?_, rfl⟩
      change mobiusNormalizedNorm (mobiusSpecialLinearProjection A) ≤ R at hf
      rwa [mobiusNormalizedNorm_specialLinearProjection] at hf
    · rintro ⟨A, hA, rfl⟩
      change mobiusNormalizedNorm (mobiusSpecialLinearProjection A) ≤ R
      rwa [mobiusNormalizedNorm_specialLinearProjection]
  rw [he]
  exact (specialLinear_norm_sublevel_isCompact R).image mobiusSpecialLinearProjection_continuous

theorem discreteMobius_norm_sublevel_finite (H : Subgroup complexMobiusGroup)
    (hH : IsDiscreteMobiusSubgroup H) (R : ℝ) :
    {f : H | mobiusNormalizedNorm f.val ≤ R}.Finite := by
  let : DiscreteTopology H := hH
  have hclosed : IsClosed (H : Set complexMobiusGroup) := Subgroup.isClosed_of_discreteTopology
  have hc := hclosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    (mobius_norm_sublevel_isCompact R)
  exact hc.finite_of_discrete

theorem discreteMobius_norm_tendsto_cofinite (H : Subgroup complexMobiusGroup)
    (hH : IsDiscreteMobiusSubgroup H) :
    Tendsto (fun f : H => mobiusNormalizedNorm f.val) cofinite atTop := by
  apply tendsto_atTop.mpr
  intro R
  have hf := discreteMobius_norm_sublevel_finite H hH R
  filter_upwards [hf.compl_mem_cofinite] with f hf
  exact le_of_lt (lt_of_not_ge hf)

theorem discreteMobius_injective_sequence_norm_tendsto (H : Subgroup complexMobiusGroup)
    (hH : IsDiscreteMobiusSubgroup H) (f : ℕ → H) (hf : Function.Injective f) :
    Tendsto (fun n => mobiusNormalizedNorm (f n).val) atTop atTop := by
  exact (discreteMobius_norm_tendsto_cofinite H hH).comp
    (hf.tendsto_cofinite.mono_left Filter.atTop_le_cofinite)


open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups
open scoped MatrixGroups

local instance mobiusLocalLiftChordalMetric : MetricSpace ExtendedComplex := complexChordalMetricSpace

def mobiusLocalFinite (z : ExtendedComplex) : ℂ := z.elim 0 id

theorem mobiusLocalFinite_coe (z : ℂ) : mobiusLocalFinite (z : ExtendedComplex) = z := rfl

theorem mobiusLocalFinite_coe_eq {z : ExtendedComplex} (hz : z ≠ ∞) :
    (mobiusLocalFinite z : ExtendedComplex) = z := by
  induction z using OnePoint.rec with
  | infty => exact (hz rfl).elim
  | coe z => rfl

theorem mobiusLocalFinite_continuousAt (z : ℂ) :
    ContinuousAt mobiusLocalFinite (z : ExtendedComplex) := by
  apply OnePoint.continuousAt_coe.mpr
  exact continuousAt_id

theorem mobiusLocal_eval_continuous (z : ExtendedComplex) :
    Continuous (fun g : complexMobiusGroup => (g : Equiv.Perm ExtendedComplex) z) := by
  change Continuous (fun g : complexMobiusGroup => complexMobiusContinuousMap g z)
  exact (continuous_eval_const z).comp complexMobiusContinuousMap_isometry.continuous

def mobiusLocalX (g : complexMobiusGroup) : ℂ :=
  mobiusLocalFinite ((g : Equiv.Perm ExtendedComplex) (0 : ℂ))

def mobiusLocalY (g : complexMobiusGroup) : ℂ :=
  mobiusLocalFinite ((g : Equiv.Perm ExtendedComplex) (1 : ℂ))

def mobiusLocalV (g : complexMobiusGroup) : ℂ :=
  mobiusLocalFinite (reciprocal ((g : Equiv.Perm ExtendedComplex) ∞))

theorem mobiusLocal_coordinates_one :
    mobiusLocalX 1 = 0 ∧ mobiusLocalY 1 = 1 ∧ mobiusLocalV 1 = 0 := by
  simp [mobiusLocalX, mobiusLocalY, mobiusLocalV, reciprocal_infty, mobiusLocalFinite]

theorem mobiusLocalX_continuousAt : ContinuousAt mobiusLocalX (1 : complexMobiusGroup) := by
  change Tendsto mobiusLocalX (𝓝 (1 : complexMobiusGroup)) (𝓝 (0 : ℂ))
  exact (mobiusLocalFinite_continuousAt 0).tendsto.comp
    (mobiusLocal_eval_continuous (0 : ℂ)).continuousAt

theorem mobiusLocalY_continuousAt : ContinuousAt mobiusLocalY (1 : complexMobiusGroup) := by
  change Tendsto mobiusLocalY (𝓝 (1 : complexMobiusGroup)) (𝓝 (1 : ℂ))
  exact (mobiusLocalFinite_continuousAt 1).tendsto.comp
    (mobiusLocal_eval_continuous (1 : ℂ)).continuousAt

theorem mobiusLocalV_continuousAt : ContinuousAt mobiusLocalV (1 : complexMobiusGroup) := by
  have hr : ContinuousAt (fun g : complexMobiusGroup =>
      reciprocal ((g : Equiv.Perm ExtendedComplex) ∞)) 1 :=
    (continuous_reciprocal.comp (mobiusLocal_eval_continuous ∞)).continuousAt
  have ht : Tendsto (fun g : complexMobiusGroup => reciprocal ((g : Equiv.Perm ExtendedComplex) ∞))
      (𝓝 1) (𝓝 ((0 : ℂ) : ExtendedComplex)) := by
    simpa only [show ((1 : complexMobiusGroup) : Equiv.Perm ExtendedComplex) ∞ = ∞ from rfl,
      reciprocal_infty] using hr.tendsto
  change Tendsto mobiusLocalV (𝓝 (1 : complexMobiusGroup)) (𝓝 (mobiusLocalV 1))
  rw [mobiusLocal_coordinates_one.2.2]
  exact (mobiusLocalFinite_continuousAt 0).tendsto.comp ht

def mobiusLocalA (g : complexMobiusGroup) : ℂ :=
  (mobiusLocalY g - mobiusLocalX g) / (1 - mobiusLocalV g * mobiusLocalY g)

def mobiusLocalMatrix (g : complexMobiusGroup) : Auxiliary.Algebra.ComplexMatrix2 :=
  !![mobiusLocalA g, mobiusLocalX g; mobiusLocalV g * mobiusLocalA g, 1]

theorem mobiusLocalA_one : mobiusLocalA 1 = 1 := by
  simp [mobiusLocalA, mobiusLocal_coordinates_one.1, mobiusLocal_coordinates_one.2.1,
    mobiusLocal_coordinates_one.2.2]

theorem mobiusLocalMatrix_one : mobiusLocalMatrix 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mobiusLocalMatrix, mobiusLocalA_one, mobiusLocal_coordinates_one.1,
      mobiusLocal_coordinates_one.2.2]

theorem mobiusLocalA_continuousAt : ContinuousAt mobiusLocalA (1 : complexMobiusGroup) := by
  apply (mobiusLocalY_continuousAt.sub mobiusLocalX_continuousAt).div
    (continuousAt_const.sub (mobiusLocalV_continuousAt.mul mobiusLocalY_continuousAt))
  simp [mobiusLocal_coordinates_one.2.2]

theorem mobiusLocalMatrix_continuousAt : ContinuousAt mobiusLocalMatrix (1 : complexMobiusGroup) := by
  apply continuousAt_pi.mpr
  intro i
  apply continuousAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact mobiusLocalA_continuousAt
  · exact mobiusLocalX_continuousAt
  · exact mobiusLocalV_continuousAt.mul mobiusLocalA_continuousAt
  · exact continuousAt_const

theorem complexSqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  exact Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)

theorem complexSqrt_ne_zero {z : ℂ} (hz : z ≠ 0) : Complex.sqrt z ≠ 0 := by
  intro hs
  have h := complexSqrt_sq z
  rw [hs, zero_pow (by norm_num)] at h
  exact hz h.symm

def mobiusLocalNormalize (M : Auxiliary.Algebra.ComplexMatrix2) (hM : M.det ≠ 0) : Auxiliary.Algebra.SpecialLinear2 :=
  ⟨(Complex.sqrt M.det)⁻¹ • M, by
    rw [Matrix.det_smul, Fintype.card_fin, inv_pow, complexSqrt_sq]
    exact inv_mul_cancel₀ hM⟩

theorem mobiusLocalNormalize_projection (M : Auxiliary.Algebra.ComplexMatrix2) (hM : M.det ≠ 0) :
    mobiusSpecialLinearProjection (mobiusLocalNormalize M hM) =
      mobiusMatrixProjection (Matrix.GeneralLinearGroup.mkOfDetNeZero M hM) := by
  apply complexMobiusEquivFractionalLinear.injective
  rw [mobiusSpecialLinearProjection_equiv, mobiusMatrixProjection_equiv]
  change matrixProjection (Matrix.SpecialLinearGroup.toGL (mobiusLocalNormalize M hM)) =
    matrixProjection (Matrix.GeneralLinearGroup.mkOfDetNeZero M hM)
  symm
  apply (matrixProjection_eq_iff _ _).mpr
  refine ⟨Units.mk0 (Complex.sqrt M.det)⁻¹ (inv_ne_zero (complexSqrt_ne_zero hM)), ?_⟩
  apply Units.ext
  rw [generalLinear_mul_scalar_val]
  rfl

def mobiusLocalLift (g : complexMobiusGroup) : Auxiliary.Algebra.SpecialLinear2 :=
  if h : (mobiusLocalMatrix g).det ≠ 0 then mobiusLocalNormalize (mobiusLocalMatrix g) h else 1

theorem mobiusLocalLift_one : mobiusLocalLift 1 = 1 := by
  apply Subtype.ext
  simp [mobiusLocalLift, mobiusLocalMatrix_one, mobiusLocalNormalize]

theorem mobiusLocal_det_continuousAt :
    ContinuousAt (fun g => (mobiusLocalMatrix g).det) (1 : complexMobiusGroup) :=
  continuous_id.matrix_det.continuousAt.comp (f := mobiusLocalMatrix) mobiusLocalMatrix_continuousAt

theorem mobiusLocal_eventually_det_ne_zero :
    ∀ᶠ g in 𝓝 (1 : complexMobiusGroup), (mobiusLocalMatrix g).det ≠ 0 :=
  mobiusLocal_det_continuousAt.eventually_ne (by simp [mobiusLocalMatrix_one])

theorem mobiusLocalLift_continuousAt : ContinuousAt mobiusLocalLift (1 : complexMobiusGroup) := by
  have hs : ContinuousAt (fun g => Complex.sqrt (mobiusLocalMatrix g).det)
      (1 : complexMobiusGroup) := by
    apply (Complex.continuousAt_sqrt (z := (mobiusLocalMatrix 1).det) ?_).comp
      (f := fun g => (mobiusLocalMatrix g).det) mobiusLocal_det_continuousAt
    simp [mobiusLocalMatrix_one]
  have hn : Complex.sqrt (mobiusLocalMatrix 1).det ≠ 0 := by simp [mobiusLocalMatrix_one]
  have hraw : ContinuousAt (fun g => (Complex.sqrt (mobiusLocalMatrix g).det)⁻¹ •
      mobiusLocalMatrix g) (1 : complexMobiusGroup) :=
    (hs.inv₀ hn).smul mobiusLocalMatrix_continuousAt
  have he : (fun g => (mobiusLocalLift g : Auxiliary.Algebra.ComplexMatrix2)) =ᶠ[𝓝 (1 : complexMobiusGroup)]
      (fun g => (Complex.sqrt (mobiusLocalMatrix g).det)⁻¹ • mobiusLocalMatrix g) := by
    filter_upwards [mobiusLocal_eventually_det_ne_zero] with g hg
    simp [mobiusLocalLift, hg, mobiusLocalNormalize]
  exact tendsto_subtype_rng.mpr (hraw.congr_of_eventuallyEq he)

theorem mobiusLocal_eventually_coordinates :
    ∀ᶠ (g : complexMobiusGroup) in 𝓝 (1 : complexMobiusGroup),
      (g : Equiv.Perm ExtendedComplex) (0 : ℂ) = (mobiusLocalX g : ℂ) ∧
      (g : Equiv.Perm ExtendedComplex) (1 : ℂ) = (mobiusLocalY g : ℂ) ∧
      reciprocal ((g : Equiv.Perm ExtendedComplex) ∞) = (mobiusLocalV g : ℂ) := by
  have h0 : ∀ᶠ (g : complexMobiusGroup) in 𝓝 (1 : complexMobiusGroup),
      (g : Equiv.Perm ExtendedComplex) (0 : ℂ) ≠ ∞ :=
    (mobiusLocal_eval_continuous (0 : ℂ)).continuousAt.eventually_ne (OnePoint.coe_ne_infty 0)
  have h1 : ∀ᶠ (g : complexMobiusGroup) in 𝓝 (1 : complexMobiusGroup),
      (g : Equiv.Perm ExtendedComplex) (1 : ℂ) ≠ ∞ :=
    (mobiusLocal_eval_continuous (1 : ℂ)).continuousAt.eventually_ne (OnePoint.coe_ne_infty 1)
  have hr : ContinuousAt (fun g : complexMobiusGroup =>
      reciprocal ((g : Equiv.Perm ExtendedComplex) ∞)) 1 :=
    (continuous_reciprocal.comp (mobiusLocal_eval_continuous ∞)).continuousAt
  have hi := hr.eventually_ne (y := ∞) (by
    change reciprocal ∞ ≠ ∞
    rw [reciprocal_infty]
    exact OnePoint.coe_ne_infty 0)
  filter_upwards [h0, h1, hi] with g hg0 hg1 hgi
  exact ⟨(mobiusLocalFinite_coe_eq hg0).symm, (mobiusLocalFinite_coe_eq hg1).symm,
    (mobiusLocalFinite_coe_eq hgi).symm⟩

theorem mobiusLocalMatrix_projection_eq (g : complexMobiusGroup)
    (hM : (mobiusLocalMatrix g).det ≠ 0)
    (hd : 1 - mobiusLocalV g * mobiusLocalY g ≠ 0)
    (h1 : mobiusLocalV g * mobiusLocalA g + 1 ≠ 0)
    (h0g : (g : Equiv.Perm ExtendedComplex) (0 : ℂ) = (mobiusLocalX g : ℂ))
    (h1g : (g : Equiv.Perm ExtendedComplex) (1 : ℂ) = (mobiusLocalY g : ℂ))
    (hig : reciprocal ((g : Equiv.Perm ExtendedComplex) ∞) = (mobiusLocalV g : ℂ)) :
    mobiusMatrixProjection (Matrix.GeneralLinearGroup.mkOfDetNeZero (mobiusLocalMatrix g) hM) = g := by
  have ha : mobiusLocalA g ≠ 0 := by
    intro hz
    apply hM
    simp [mobiusLocalMatrix, Matrix.det_fin_two, hz]
  apply mobius_eq_of_agree_triple _ g (0 : ℂ) (1 : ℂ) ∞
    (by simp [TripleDistinct])
  · rw [h0g, mobiusMatrixProjection_apply, fractionalLinear_coe]
    simp [mobiusLocalMatrix]
  · rw [h1g, mobiusMatrixProjection_apply, fractionalLinear_coe]
    change (if mobiusLocalV g * mobiusLocalA g * 1 + 1 = 0 then ∞ else
      (((mobiusLocalA g * 1 + mobiusLocalX g) / (mobiusLocalV g * mobiusLocalA g * 1 + 1) : ℂ) :
        ExtendedComplex)) = _
    simp only [mul_one, ite_eq_right h1]
    apply congrArg OnePoint.some
    apply (div_eq_iff h1).mpr
    have he : mobiusLocalA g * (1 - mobiusLocalV g * mobiusLocalY g) =
        mobiusLocalY g - mobiusLocalX g := div_mul_cancel₀ _ hd
    linear_combination he
  · apply reciprocal.injective
    rw [hig, mobiusMatrixProjection_apply, fractionalLinear_infty]
    change reciprocal (if mobiusLocalV g * mobiusLocalA g = 0 then ∞ else
      (mobiusLocalA g / (mobiusLocalV g * mobiusLocalA g) : ℂ)) = _
    by_cases hv : mobiusLocalV g = 0
    · simp [hv, reciprocal_infty]
    · rw [ite_eq_right (mul_ne_zero hv ha), reciprocal_coe _ (div_ne_zero ha (mul_ne_zero hv ha))]
      apply congrArg OnePoint.some
      field_simp

theorem mobiusLocalLift_eventually_projection :
    ∀ᶠ (g : complexMobiusGroup) in 𝓝 (1 : complexMobiusGroup),
      mobiusSpecialLinearProjection (mobiusLocalLift g) = g := by
  have hdcont : ContinuousAt (fun g : complexMobiusGroup => 1 - mobiusLocalV g * mobiusLocalY g) 1 :=
    continuousAt_const.sub (mobiusLocalV_continuousAt.mul mobiusLocalY_continuousAt)
  have hd := hdcont.eventually_ne (y := 0) (by simp [mobiusLocal_coordinates_one.2.2])
  have h1cont : ContinuousAt (fun g : complexMobiusGroup => mobiusLocalV g * mobiusLocalA g + 1) 1 :=
    (mobiusLocalV_continuousAt.mul mobiusLocalA_continuousAt).add continuousAt_const
  have h1n := h1cont.eventually_ne (y := 0) (by simp [mobiusLocal_coordinates_one.2.2])
  filter_upwards [mobiusLocal_eventually_det_ne_zero, hd, h1n, mobiusLocal_eventually_coordinates]
    with g hg hgd hg1 hcoords
  have hs : mobiusLocalLift g = mobiusLocalNormalize (mobiusLocalMatrix g) hg := by
    simp [mobiusLocalLift, hg]
  rw [hs, mobiusLocalNormalize_projection]
  exact mobiusLocalMatrix_projection_eq g hg hgd hg1 hcoords.1 hcoords.2.1 hcoords.2.2

theorem mobius_identity_continuous_local_section :
    ∃ s : complexMobiusGroup → Auxiliary.Algebra.SpecialLinear2, s 1 = 1 ∧ ContinuousAt s 1 ∧
      ∀ᶠ (g : complexMobiusGroup) in 𝓝 (1 : complexMobiusGroup),
        mobiusSpecialLinearProjection (s g) = g :=
  ⟨mobiusLocalLift, mobiusLocalLift_one, mobiusLocalLift_continuousAt,
    mobiusLocalLift_eventually_projection⟩



theorem mobiusProjection_isOpenMap_of_local_section
    (hlocal : ∃ s : complexMobiusGroup → Auxiliary.Algebra.SpecialLinear2,
      s 1 = 1 ∧ ContinuousAt s 1 ∧
        ∀ᶠ g in 𝓝 1, mobiusSpecialLinearProjection (s g) = g) :
    IsOpenMap mobiusSpecialLinearProjection := by
  obtain ⟨s, hs1, hs, hsec⟩ := hlocal
  apply IsTopologicalGroup.isOpenMap_iff_nhds_one.mpr
  intro S hS
  change mobiusSpecialLinearProjection ⁻¹' S ∈ 𝓝 (1 : Auxiliary.Algebra.SpecialLinear2) at hS
  have ht : Tendsto s (𝓝 1) (𝓝 (1 : Auxiliary.Algebra.SpecialLinear2)) := by
    change Tendsto s (𝓝 1) (𝓝 (s 1)) at hs
    rwa [hs1] at hs
  filter_upwards [ht.eventually hS, hsec] with g hg he
  change mobiusSpecialLinearProjection (s g) ∈ S at hg
  rwa [he] at hg


theorem mobiusSpecialLinearProjection_isOpenMap : IsOpenMap mobiusSpecialLinearProjection :=
  mobiusProjection_isOpenMap_of_local_section mobius_identity_continuous_local_section

theorem mobiusSpecialLinearProjection_isQuotientMap :
    Topology.IsQuotientMap mobiusSpecialLinearProjection :=
  mobiusSpecialLinearProjection_isOpenMap.isQuotientMap
    mobiusSpecialLinearProjection_continuous mobiusSpecialLinearProjection_surjective

/-- The determinant-one quotient and uniform chordal topologies agree. -/
theorem mobius_quotientTopology_eq_uniformTopology :
    mobiusQuotientTopology = mobiusUniformTopology :=
  mobiusSpecialLinearProjection_isQuotientMap.eq_coinduced.symm



def specialLinearSignChange (A : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.SpecialLinear2 :=
  ⟨-(A : Auxiliary.Algebra.ComplexMatrix2), by rw [Matrix.det_neg, Fintype.card_fin, A.det_coe]; norm_num⟩

theorem specialLinearSignChange_involutive : Function.Involutive specialLinearSignChange := by
  intro A
  apply Subtype.ext
  exact neg_neg (A : Auxiliary.Algebra.ComplexMatrix2)

theorem specialLinearSignChange_continuous : Continuous specialLinearSignChange := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val.neg

theorem specialLinear_sameMobius_iff (A B : Auxiliary.Algebra.SpecialLinear2) :
    mobiusSpecialLinearProjection A = mobiusSpecialLinearProjection B ↔
      B = A ∨ B = specialLinearSignChange A := by
  rw [← complexMobiusEquivFractionalLinear.injective.eq_iff,
    mobiusSpecialLinearProjection_equiv, mobiusSpecialLinearProjection_equiv,
    specialLinear_same_projection_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem specialLinear_matrixNorm_lower (A : Auxiliary.Algebra.SpecialLinear2) :
    Real.sqrt 2 ≤ Auxiliary.Algebra.matrixNorm (A : Auxiliary.Algebra.ComplexMatrix2) := by
  have hd := Auxiliary.Algebra.determinant_norm_le (A : Auxiliary.Algebra.ComplexMatrix2)
  rw [A.det_coe, norm_one] at hd
  nlinarith [Auxiliary.Algebra.matrixNorm_nonneg (A : Auxiliary.Algebra.ComplexMatrix2),
    Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]

theorem specialLinear_sign_separation (A : Auxiliary.Algebra.SpecialLinear2) :
    2 * Real.sqrt 2 ≤ Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) -
      specialLinearSignChange A) := by
  have he : (A : Auxiliary.Algebra.ComplexMatrix2) - specialLinearSignChange A = (2 : ℂ) • (A :
    Auxiliary.Algebra.ComplexMatrix2) := by
    change (A : Auxiliary.Algebra.ComplexMatrix2) - -(A : Auxiliary.Algebra.ComplexMatrix2) = _
    simp only [sub_neg_eq_add, two_smul ℂ]
  rw [he, Auxiliary.Algebra.matrixNorm_scalar]
  norm_num only [Complex.norm_ofNat]
  exact mul_le_mul_of_nonneg_left (specialLinear_matrixNorm_lower A) (by norm_num)

/-- Frobenius balls are taken in the actual determinant-one matrix subspace. -/
def specialLinearFrobeniusBall (C : Auxiliary.Algebra.SpecialLinear2) : Set Auxiliary.Algebra.SpecialLinear2 :=
  {A | Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - C) < Real.sqrt 2}

theorem specialLinearFrobeniusBall_isOpen (C : Auxiliary.Algebra.SpecialLinear2) :
    IsOpen (specialLinearFrobeniusBall C) := by
  have hc : Continuous (fun A : Auxiliary.Algebra.SpecialLinear2 => (A : Auxiliary.Algebra.ComplexMatrix2)) :=
    continuous_subtype_val
  exact isOpen_lt (Auxiliary.Algebra.matrixNorm_continuous.comp (hc.sub continuous_const)) continuous_const

theorem mobiusProjection_injOn_frobeniusBall (C : Auxiliary.Algebra.SpecialLinear2) :
    Set.InjOn mobiusSpecialLinearProjection (specialLinearFrobeniusBall C) := by
  intro A hA B hB he
  rcases (specialLinear_sameMobius_iff A B).mp he with h | h
  · exact h.symm
  · have hs := specialLinear_sign_separation A
    rw [← h] at hs
    have ht : Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - B) ≤
        Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - C) + Auxiliary.Algebra.matrixNorm
          ((B : Auxiliary.Algebra.ComplexMatrix2) - C) := by
      calc
        _ = Auxiliary.Algebra.matrixNorm (((A : Auxiliary.Algebra.ComplexMatrix2) - C) + ((C :
          Auxiliary.Algebra.ComplexMatrix2) - B)) := by congr 1; abel
        _ ≤ Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - C) +
          Auxiliary.Algebra.matrixNorm ((C : Auxiliary.Algebra.ComplexMatrix2) - B) :=
          Auxiliary.Algebra.matrixNorm_add_le _ _
        _ = _ := by rw [show Auxiliary.Algebra.matrixNorm ((C : Auxiliary.Algebra.ComplexMatrix2) - B) =
          Auxiliary.Algebra.matrixNorm ((B : Auxiliary.Algebra.ComplexMatrix2) - C) from norm_sub_rev _ _]
    change Auxiliary.Algebra.matrixNorm ((A : Auxiliary.Algebra.ComplexMatrix2) - C) < Real.sqrt 2 at hA
    change Auxiliary.Algebra.matrixNorm ((B : Auxiliary.Algebra.ComplexMatrix2) - C) < Real.sqrt 2 at hB
    linarith

theorem mobiusProjection_frobeniusBall_isOpenEmbedding (C : Auxiliary.Algebra.SpecialLinear2) :
    Topology.IsOpenEmbedding ((specialLinearFrobeniusBall C).domRestrict mobiusSpecialLinearProjection) := by
  apply (Topology.isOpenEmbedding_iff_continuous_injective_isOpenMap).mpr
  refine ⟨mobiusSpecialLinearProjection_continuous.comp continuous_subtype_val,
    (Set.injOn_iff_injective).mp (mobiusProjection_injOn_frobeniusBall C), ?_⟩
  exact mobiusSpecialLinearProjection_isOpenMap.domRestrict (specialLinearFrobeniusBall_isOpen C)

def mobiusProjection_frobeniusBall_homeomorph (C : Auxiliary.Algebra.SpecialLinear2) :
    specialLinearFrobeniusBall C ≃ₜ
      Set.range ((specialLinearFrobeniusBall C).domRestrict mobiusSpecialLinearProjection) :=
  (mobiusProjection_frobeniusBall_isOpenEmbedding C).isEmbedding.toHomeomorph

theorem mobiusProjection_isLocalHomeomorph : IsLocalHomeomorph mobiusSpecialLinearProjection := by
  apply isLocalHomeomorph_iff_isOpenEmbedding_restrict.mpr
  intro C
  refine ⟨specialLinearFrobeniusBall C, (specialLinearFrobeniusBall_isOpen C).mem_nhds ?_,
    mobiusProjection_frobeniusBall_isOpenEmbedding C⟩
  change Auxiliary.Algebra.matrixNorm ((C : Auxiliary.Algebra.ComplexMatrix2) - C) < Real.sqrt 2
  simpa only [sub_self, Auxiliary.Algebra.matrixNorm, norm_zero] using Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num)


theorem mobiusProjection_saturated_set (S : Set Auxiliary.Algebra.SpecialLinear2) :
    mobiusSpecialLinearProjection ⁻¹' (mobiusSpecialLinearProjection '' S) =
      S ∪ specialLinearSignChange ⁻¹' S := by
  ext A
  constructor
  · rintro ⟨B, hB, hBA⟩
    rcases (specialLinear_sameMobius_iff B A).mp hBA with h | h
    · exact Or.inl (h.symm ▸ hB)
    · right
      change specialLinearSignChange A ∈ S
      rw [h, specialLinearSignChange_involutive B]
      exact hB
  · rintro (hA | hA)
    · exact ⟨A, hA, rfl⟩
    · exact ⟨specialLinearSignChange A, hA,
        ((specialLinear_sameMobius_iff A (specialLinearSignChange A)).mpr (Or.inr rfl)).symm⟩

theorem mobiusProjection_isClosedMap : IsClosedMap mobiusSpecialLinearProjection := by
  intro S hS
  apply mobiusSpecialLinearProjection_isQuotientMap.isCoinducing.isClosed_preimage.mp
  rw [mobiusProjection_saturated_set]
  exact hS.union (hS.preimage specialLinearSignChange_continuous)

theorem mobiusProjection_fiber_pair (f : complexMobiusGroup) :
    ∃ A B : Auxiliary.Algebra.SpecialLinear2, A ≠ B ∧ mobiusSpecialLinearProjection ⁻¹' {f} = {A, B} := by
  obtain ⟨A, B, hAB, _, _, hC⟩ := mobiusSpecialLinear_exactly_two_representatives f
  refine ⟨A, B, hAB, ?_⟩
  ext C
  exact hC C

theorem mobiusProjection_isCoveringMap : IsCoveringMap mobiusSpecialLinearProjection := by
  rw [isCoveringMap_iff_isCoveringMapOn_univ]
  apply mobiusProjection_isClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn
  · intro f _
    obtain ⟨A, B, _, he⟩ := mobiusProjection_fiber_pair f
    rw [he]
    exact (Set.finite_singleton B).insert A
  · exact mobiusProjection_isLocalHomeomorph.isLocalHomeomorphOn



local instance mobiusThreePointChordalMetric : MetricSpace ExtendedComplex := complexChordalMetricSpace

-- BEGIN three-point convergence extension

theorem mobiusLocalLift_tendsto_of_three {α : Type*} {l : Filter α}
    (g : α → complexMobiusGroup)
    (h0 : Tendsto (fun i => (g i : Equiv.Perm ExtendedComplex) (0 : ℂ)) l (𝓝 (0 : ℂ)))
    (h1 : Tendsto (fun i => (g i : Equiv.Perm ExtendedComplex) (1 : ℂ)) l (𝓝 (1 : ℂ)))
    (hi : Tendsto (fun i => (g i : Equiv.Perm ExtendedComplex) ∞) l (𝓝 ∞)) :
    Tendsto (fun i => mobiusLocalLift (g i)) l (𝓝 (1 : Auxiliary.Algebra.SpecialLinear2)) ∧
      ∀ᶠ i in l, mobiusSpecialLinearProjection (mobiusLocalLift (g i)) = g i := by
  have hx : Tendsto (fun i => mobiusLocalX (g i)) l (𝓝 0) :=
    (mobiusLocalFinite_continuousAt 0).tendsto.comp h0
  have hy : Tendsto (fun i => mobiusLocalY (g i)) l (𝓝 1) :=
    (mobiusLocalFinite_continuousAt 1).tendsto.comp h1
  have hri : Tendsto (fun i => reciprocal ((g i : Equiv.Perm ExtendedComplex) ∞)) l
      (𝓝 ((0 : ℂ) : ExtendedComplex)) := by
    simpa only [reciprocal_infty, Function.comp_def] using (continuous_reciprocal.tendsto ∞).comp hi
  have hv : Tendsto (fun i => mobiusLocalV (g i)) l (𝓝 0) :=
    (mobiusLocalFinite_continuousAt 0).tendsto.comp hri
  have hden : Tendsto (fun i => 1 - mobiusLocalV (g i) * mobiusLocalY (g i)) l (𝓝 (1 : ℂ)) := by
    simpa only [zero_mul, sub_zero] using
      (tendsto_const_nhds.sub (hv.mul hy) :
        Tendsto (fun i => (1 : ℂ) - mobiusLocalV (g i) * mobiusLocalY (g i)) l (𝓝 (1 - 0 * 1)))
  have ha : Tendsto (fun i => mobiusLocalA (g i)) l (𝓝 1) := by
    convert (hy.sub hx).div hden (by norm_num : (1 : ℂ) ≠ 0) using 1 <;> first | rfl | norm_num
  have hM : Tendsto (fun i => mobiusLocalMatrix (g i)) l (𝓝 (1 : Auxiliary.Algebra.ComplexMatrix2)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    fin_cases i <;> fin_cases j
    · exact ha
    · exact hx
    · change Tendsto (fun i => mobiusLocalV (g i) * mobiusLocalA (g i)) l (𝓝 (0 : ℂ))
      simpa only [zero_mul] using hv.mul ha
    · exact tendsto_const_nhds
  have hdet : Tendsto (fun i => (mobiusLocalMatrix (g i)).det) l (𝓝 (1 : ℂ)) := by
    simpa only [Matrix.det_one, Function.comp_def] using
      ((show Continuous (fun M : Auxiliary.Algebra.ComplexMatrix2 => M.det) from continuous_id.matrix_det).tendsto
        1).comp hM
  have hdn := hdet.eventually (eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ 0))
  have hsqrt : Tendsto (fun i => Complex.sqrt (mobiusLocalMatrix (g i)).det) l (𝓝 (1 : ℂ)) := by
    simpa only [Complex.sqrt_one, Function.comp_def] using
      (Complex.continuousAt_sqrt (z := 1) (Or.inl (by norm_num))).tendsto.comp hdet
  have hnorm : Tendsto (fun i => (Complex.sqrt (mobiusLocalMatrix (g i)).det)⁻¹ •
      mobiusLocalMatrix (g i)) l (𝓝 (1 : Auxiliary.Algebra.ComplexMatrix2)) := by
    simpa only [inv_one, one_smul] using (hsqrt.inv₀ (by norm_num : (1 : ℂ) ≠ 0)).smul hM
  have hraw : (fun i => (mobiusLocalLift (g i) : Auxiliary.Algebra.ComplexMatrix2)) =ᶠ[l]
      (fun i => (Complex.sqrt (mobiusLocalMatrix (g i)).det)⁻¹ • mobiusLocalMatrix (g i)) := by
    filter_upwards [hdn] with i hid
    simp [mobiusLocalLift, hid, mobiusLocalNormalize]
  constructor
  · exact tendsto_subtype_rng.mpr (hnorm.congr' hraw.symm)
  · have h0n := h0.eventually (eventually_ne_nhds (OnePoint.coe_ne_infty (0 : ℂ)))
    have h1n := h1.eventually (eventually_ne_nhds (OnePoint.coe_ne_infty (1 : ℂ)))
    have hin := hri.eventually (eventually_ne_nhds (OnePoint.coe_ne_infty (0 : ℂ)))
    have hdenn := hden.eventually (eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ 0))
    have hone : Tendsto (fun i => mobiusLocalV (g i) * mobiusLocalA (g i) + 1) l (𝓝 (1 : ℂ)) := by
      simpa only [zero_mul, zero_add] using (hv.mul ha).add tendsto_const_nhds
    have honen := hone.eventually (eventually_ne_nhds (by norm_num : (1 : ℂ) ≠ 0))
    filter_upwards [hdn, h0n, h1n, hin, hdenn, honen] with i hid hi0 hi1 hii hidd hion
    have he : mobiusLocalLift (g i) = mobiusLocalNormalize (mobiusLocalMatrix (g i)) hid := by
      simp [mobiusLocalLift, hid]
    rw [he, mobiusLocalNormalize_projection]
    exact mobiusLocalMatrix_projection_eq (g i) hid hidd hion
      (mobiusLocalFinite_coe_eq hi0).symm (mobiusLocalFinite_coe_eq hi1).symm
      (mobiusLocalFinite_coe_eq hii).symm

theorem mobius_three_point_SL2_representatives
    (g : ℕ → complexMobiusGroup)
    (h0 : Tendsto (fun i => (g i : Equiv.Perm ExtendedComplex) (0 : ℂ)) atTop (𝓝 (0 : ℂ)))
    (h1 : Tendsto (fun i => (g i : Equiv.Perm ExtendedComplex) (1 : ℂ)) atTop (𝓝 (1 : ℂ)))
    (hi : Tendsto (fun i => (g i : Equiv.Perm ExtendedComplex) ∞) atTop (𝓝 ∞)) :
    ∃ A : ℕ → Auxiliary.Algebra.SpecialLinear2, (∀ i, mobiusSpecialLinearProjection (A i) = g i) ∧
      Tendsto A atTop (𝓝 (1 : Auxiliary.Algebra.SpecialLinear2)) := by
  classical
  obtain ⟨ht, hp⟩ := mobiusLocalLift_tendsto_of_three g h0 h1 hi
  let A (i : ℕ) := if mobiusSpecialLinearProjection (mobiusLocalLift (g i)) = g i then
    mobiusLocalLift (g i) else Classical.choose (mobiusSpecialLinearProjection_surjective (g i))
  refine ⟨A, fun i => ?_, ?_⟩
  · dsimp only [A]
    split_ifs with he
    · exact he
    · exact Classical.choose_spec (mobiusSpecialLinearProjection_surjective (g i))
  · apply ht.congr'
    filter_upwards [hp] with i hi
    simp [A, hi]

theorem mobius_tendsto_one_of_three {α : Type*} {l : Filter α}
    (g : α → complexMobiusGroup)
    (h0 : Tendsto (fun i => (g i : Equiv.Perm ExtendedComplex) (0 : ℂ)) l (𝓝 (0 : ℂ)))
    (h1 : Tendsto (fun i => (g i : Equiv.Perm ExtendedComplex) (1 : ℂ)) l (𝓝 (1 : ℂ)))
    (hi : Tendsto (fun i => (g i : Equiv.Perm ExtendedComplex) ∞) l (𝓝 ∞)) :
    Tendsto g l (𝓝 (1 : complexMobiusGroup)) := by
  obtain ⟨ht, hp⟩ := mobiusLocalLift_tendsto_of_three g h0 h1 hi
  have hs := (mobiusSpecialLinearProjection_continuous.tendsto 1).comp ht
  rw [map_one] at hs
  exact hs.congr' hp



theorem mobiusNormalizedNorm_continuous : Continuous mobiusNormalizedNorm := by
  apply mobiusSpecialLinearProjection_isQuotientMap.continuous_iff.mpr
  have h : Continuous (fun A : Auxiliary.Algebra.SpecialLinear2 => Auxiliary.Algebra.matrixNorm (A :
    Auxiliary.Algebra.ComplexMatrix2)) :=
    Auxiliary.Algebra.matrixNorm_continuous.comp continuous_subtype_val
  simpa only [Function.comp_def, mobiusNormalizedNorm_specialLinearProjection] using h

theorem discreteMobius_of_finite_norm_sublevel (H : Subgroup complexMobiusGroup)
    (hfinite : ∀ R : ℝ, 0 < R → {f : H | mobiusNormalizedNorm f.val ≤ R}.Finite) :
    IsDiscreteMobiusSubgroup H := by
  apply discreteTopology_of_isOpen_singleton_one
  let R := mobiusNormalizedNorm 1 + 1
  have hnorm : 0 ≤ mobiusNormalizedNorm 1 := by
    have h := mobiusNormalizedNorm_specialLinearProjection (1 : Auxiliary.Algebra.SpecialLinear2)
    rw [map_one] at h
    rw [h]
    exact Auxiliary.Algebra.matrixNorm_nonneg _
  have hR : 0 < R := by dsimp only [R]; linarith
  have hc : Continuous (fun f : H => mobiusNormalizedNorm f.val) :=
    mobiusNormalizedNorm_continuous.comp continuous_subtype_val
  have hn : {f : H | mobiusNormalizedNorm f.val ≤ R} ∈ 𝓝 (1 : H) := by
    apply mem_of_superset ((hc.tendsto (1 : H)).eventually (Iio_mem_nhds ?_))
    · exact fun f hf => le_of_lt hf
    · change mobiusNormalizedNorm 1 < mobiusNormalizedNorm 1 + 1
      linarith
  exact isOpen_singleton_of_finite_mem_nhds (1 : H) hn (hfinite R hR)

theorem discreteMobius_iff_finite_norm_sublevel (H : Subgroup complexMobiusGroup) :
    IsDiscreteMobiusSubgroup H ↔
      ∀ R : ℝ, 0 < R → {f : H | mobiusNormalizedNorm f.val ≤ R}.Finite := by
  exact ⟨fun h R _ => discreteMobius_norm_sublevel_finite H h R,
    discreteMobius_of_finite_norm_sublevel H⟩

theorem discreteSpecialLinear_image (K : Subgroup Auxiliary.Algebra.SpecialLinear2) [DiscreteTopology K] :
    IsDiscreteMobiusSubgroup (K.map mobiusSpecialLinearProjection) := by
  apply discreteMobius_of_finite_norm_sublevel
  intro R _
  let F : K → K.map mobiusSpecialLinearProjection := fun A =>
    ⟨mobiusSpecialLinearProjection A.val, Subgroup.mem_map.mpr ⟨A.val, A.property, rfl⟩⟩
  apply ((DiscreteGroups.MatrixGroups.finite_norm_bounded K R).image F).subset
  intro g hg
  obtain ⟨A, hA, hAg⟩ := Subgroup.mem_map.mp g.property
  refine ⟨⟨A, hA⟩, ?_, ?_⟩
  · change Auxiliary.Algebra.matrixNorm (A : Auxiliary.Algebra.ComplexMatrix2) ≤ R
    change mobiusNormalizedNorm g.val ≤ R at hg
    rw [← hAg, mobiusNormalizedNorm_specialLinearProjection] at hg
    exact hg
  · exact Subtype.ext hAg

theorem discreteMobius_preimage_of_localHomeomorph
    (hlocal : IsLocalHomeomorph mobiusSpecialLinearProjection)
    (H : Subgroup complexMobiusGroup) (hH : IsDiscreteMobiusSubgroup H) :
    DiscreteTopology (H.comap mobiusSpecialLinearProjection) := by
  let S : Set Auxiliary.Algebra.SpecialLinear2 := (H.comap mobiusSpecialLinearProjection : Set
    Auxiliary.Algebra.SpecialLinear2)
  have he : mobiusSpecialLinearProjection '' S = (H : Set complexMobiusGroup) := by
    ext f
    constructor
    · rintro ⟨A, hA, rfl⟩
      exact hA
    · intro hf
      obtain ⟨A, rfl⟩ := mobiusSpecialLinearProjection_surjective f
      exact ⟨A, hf, rfl⟩
  let : DiscreteTopology (mobiusSpecialLinearProjection '' S) := by
    rw [he]
    exact hH
  exact (hlocal.isLocalHomeomorphOn (s := S)).discreteTopology_of_image


/-- Discreteness lifts through the actual two-sheeted determinant-one covering. -/
theorem discreteMobius_preimage (H : Subgroup complexMobiusGroup)
    (hH : IsDiscreteMobiusSubgroup H) :
    DiscreteTopology (H.comap mobiusSpecialLinearProjection) :=
  discreteMobius_preimage_of_localHomeomorph mobiusProjection_isLocalHomeomorph H hH

end
end LowDimensionalTopology.Geometry.Mobius
