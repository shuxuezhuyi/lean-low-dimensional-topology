/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier

public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.PoissonKernel
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.CayleyHalfPlaneDisk
public import LowDimensionalTopology.Geometry.Mobius.MatrixRepresentation
public import LowDimensionalTopology.Geometry.Mobius.ReflectionEquivalence
public import Mathlib.Tactic

/-!
# The upper-half-plane density and its Möbius isometries
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped UpperHalfPlane MatrixGroups Topology ComplexConjugate OnePoint Complex.UnitDisc

namespace LowDimensionalTopology.Geometry.Hyperbolic

noncomputable section

/-- Real coefficients with positive determinant give an invertible matrix. -/
def positiveDetRealMobiusMatrix (a b c d : ℝ) (hdet : 0 < a * d - b * c) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d]
    (by simpa [Matrix.det_fin_two] using hdet.ne')

theorem positiveDetRealMobiusMatrix_det (a b c d : ℝ) (hdet : 0 < a * d - b * c) :
    (positiveDetRealMobiusMatrix a b c d hdet).val.det = a * d - b * c := by
  simp [positiveDetRealMobiusMatrix, Matrix.det_fin_two]

/-- The real fractional linear map on the actual upper half-plane. -/
def realMobiusMap (a b c d : ℝ) (hdet : 0 < a * d - b * c) (z : ℍ) : ℍ :=
  positiveDetRealMobiusMatrix a b c d hdet • z

theorem realMobiusMap_coe (a b c d : ℝ) (hdet : 0 < a * d - b * c) (z : ℍ) :
    (realMobiusMap a b c d hdet z : ℂ) =
      Auxiliary.Analysis.fractionalLinearMap a b c d z := by
  have hg : 0 < (positiveDetRealMobiusMatrix a b c d hdet).det.val := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, positiveDetRealMobiusMatrix_det]
    exact hdet
  rw [realMobiusMap, UpperHalfPlane.coe_smul_of_det_pos hg]
  simp [positiveDetRealMobiusMatrix, UpperHalfPlane.num, UpperHalfPlane.denom, Auxiliary.Analysis.fractionalLinearMap]

/-- The action is onto as well as one-to-one; no extra normalization of determinant is required. -/
theorem realMobiusMap_bijective (a b c d : ℝ) (hdet : 0 < a * d - b * c) :
    Function.Bijective (realMobiusMap a b c d hdet) :=
  (MulAction.toPerm (positiveDetRealMobiusMatrix a b c d hdet)).bijective

theorem realMobiusMap_den_ne_zero (a b c d : ℝ)
    (hdet : 0 < a * d - b * c) (z : ℍ) : (c : ℂ) * z + d ≠ 0 := by
  simpa [positiveDetRealMobiusMatrix, UpperHalfPlane.denom] using
    UpperHalfPlane.denom_ne_zero (positiveDetRealMobiusMatrix a b c d hdet) z

/-- The derivative here is the ordinary complex derivative of the fractional linear formula. -/
theorem realMobiusMap_hasDerivAt (a b c d : ℝ)
    (hdet : 0 < a * d - b * c) (z : ℍ) :
    HasDerivAt (Auxiliary.Analysis.fractionalLinearMap a b c d)
      (((a * d - b * c : ℝ) : ℂ) / ((c : ℂ) * z + d) ^ 2) (z : ℂ) := by
  convert Auxiliary.Analysis.fractionalLinearMap_hasDerivAt (a : ℂ) b c d z
    (realMobiusMap_den_ne_zero a b c d hdet z) using 1
  simp [Auxiliary.Analysis.fractionalLinearDerivative]

/-- The imaginary part transforms by the norm of the ordinary complex derivative. -/
theorem realMobiusMap_im_derivative (a b c d : ℝ)
    (hdet : 0 < a * d - b * c) (z : ℍ) :
    (realMobiusMap a b c d hdet z).im =
      z.im * ‖deriv (Auxiliary.Analysis.fractionalLinearMap a b c d) (z : ℂ)‖ := by
  rw [(realMobiusMap_hasDerivAt a b c d hdet z).deriv]
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hdet]
  rw [realMobiusMap, UpperHalfPlane.im_smul_eq_div_normSq,
    Matrix.GeneralLinearGroup.val_det_apply, positiveDetRealMobiusMatrix_det,
    abs_of_pos hdet, Complex.normSq_eq_norm_sq]
  simp [positiveDetRealMobiusMatrix, UpperHalfPlane.denom, mul_div_assoc, mul_comm]
  ring

/-- The hyperbolic density on the upper half-plane. -/
def hyperbolicDensity (z : ℍ) : ℝ := 1 / z.im

theorem hyperbolicDensity_pos (z : ℍ) : 0 < hyperbolicDensity z :=
  one_div_pos.mpr z.im_pos

theorem continuous_hyperbolicDensity : Continuous hyperbolicDensity :=
  continuous_const.div UpperHalfPlane.continuous_im (fun z => z.im_ne_zero)

/-- The geometric multiplicative density relation holds with the actual derivative scale. -/
theorem realMobiusMap_hyperbolicDensity_covariance (a b c d : ℝ)
    (hdet : 0 < a * d - b * c) (z : ℍ) :
    hyperbolicDensity (realMobiusMap a b c d hdet z) *
      ‖deriv (Auxiliary.Analysis.fractionalLinearMap a b c d) (z : ℂ)‖ = hyperbolicDensity z := by
  have hn : ‖deriv (Auxiliary.Analysis.fractionalLinearMap a b c d) (z : ℂ)‖ ≠ 0 := by
    intro h
    have hpos := (realMobiusMap a b c d hdet z).im_pos
    rw [realMobiusMap_im_derivative, h, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  unfold hyperbolicDensity
  rw [realMobiusMap_im_derivative]
  field_simp

/-- The density-weighted ordinary coordinate length of a single C¹ piece. -/
def hyperbolicPieceLength (p : C1CurvePiece) : ℝ :=
  ∫ t in p.a..p.b, hyperbolicDensity (p.curve t) * ‖p.velocity t‖

theorem hyperbolicPieceLength_eq_length (p : C1CurvePiece) :
    hyperbolicPieceLength p = p.length := by
  apply intervalIntegral.integral_congr
  intro t _
  simp only [hyperbolicDensity, _root_.LowDimensionalTopology.Geometry.Hyperbolic.weightedSpeed]
  ring

/-- Finite C¹ joins use the sum of the actual density integrals. -/
def hyperbolicChainLength {z w : ℍ} : _root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve z w → ℝ
  | .nil _ => 0
  | .cons p tail => hyperbolicPieceLength p + hyperbolicChainLength tail

theorem hyperbolicChainLength_eq_length {z w : ℍ} (p :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve z w) :
    hyperbolicChainLength p = p.length := by
  induction p with
  | nil z => rfl
  | cons p tail ih =>
    change hyperbolicPieceLength p + hyperbolicChainLength tail = p.length + tail.length
    rw [hyperbolicPieceLength_eq_length, ih]

/-- The hyperbolic distance is the infimum of density-weighted curve lengths. -/
def hyperbolicPathDistance (z w : ℍ) : ℝ :=
  sInf (Set.range (fun p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.PiecewiseC1Curve z w =>
    hyperbolicChainLength p))

/-- This comparison identifies actual curve integrals before comparing their infima. -/
theorem hyperbolicPathDistance_eq_piecewisePathDist (z w : ℍ) :
    hyperbolicPathDistance z w = _root_.LowDimensionalTopology.Geometry.Hyperbolic.piecewisePathDist z w := by
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.piecewisePathDist_eq_sInf_lengths]
  simp only [hyperbolicPathDistance, hyperbolicChainLength_eq_length]

/-- The independently proved curve-infimum bridge identifies the standard hyperbolic metric. -/
theorem hyperbolicPathDistance_eq_dist (z w : ℍ) : hyperbolicPathDistance z w = dist z w := by
  rw [hyperbolicPathDistance_eq_piecewisePathDist,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.piecewisePathDist_eq_metric]

/-- The density construction satisfies the genuine metric axioms. -/
theorem hyperbolicPathDistance_metric_axioms (z w u : ℍ) :
    0 ≤ hyperbolicPathDistance z w ∧
    (hyperbolicPathDistance z w = 0 ↔ z = w) ∧
    hyperbolicPathDistance z w = hyperbolicPathDistance w z ∧
    hyperbolicPathDistance z u ≤ hyperbolicPathDistance z w + hyperbolicPathDistance w u := by
  simp only [hyperbolicPathDistance_eq_dist]
  exact ⟨dist_nonneg, dist_eq_zero, dist_comm _ _, dist_triangle _ _ _⟩

/-- Every real positive-determinant Möbius transformation preserves this path metric. -/
theorem realMobiusMap_path_distance (a b c d : ℝ) (hdet : 0 < a * d - b * c)
    (z w : ℍ) : hyperbolicPathDistance (realMobiusMap a b c d hdet z)
      (realMobiusMap a b c d hdet w) = hyperbolicPathDistance z w := by
  simp only [hyperbolicPathDistance_eq_piecewisePathDist, realMobiusMap]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.path_distance_gl_pos _
    ((positiveDetRealMobiusMatrix_det a b c d hdet).symm ▸ hdet) z w

/-- The real fractional linear action is an isometry for the actual hyperbolic metric. -/
theorem realMobiusMap_isometry (a b c d : ℝ) (hdet : 0 < a * d - b * c) :
    Isometry (realMobiusMap a b c d hdet) := by
  apply Isometry.of_dist_eq
  intro z w
  simpa only [hyperbolicPathDistance_eq_dist] using realMobiusMap_path_distance a b c d hdet z w

section DiscNormalForm
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius






theorem unitCircle_mem_closure_extendedUnitDisc {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    (ζ : Mobius.ExtendedComplex) ∈ closure extendedUnitDisc := by
  apply mem_closure_of_tendsto
    (OnePoint.continuous_coe.continuousAt.tendsto.comp (Auxiliary.Analysis.poissonRadialSequence_tendsto ζ))
  exact Eventually.of_forall fun n =>
    ⟨Auxiliary.Analysis.poissonRadialSequence ζ n, Auxiliary.Analysis.poissonRadialSequence_mem_disc hζ n, rfl⟩

/-- A disc-preserving extended homeomorphism preserves its finite boundary circle. -/
theorem disc_preserver_maps_circle (f : Mobius.ExtendedComplex ≃ₜ Mobius.ExtendedComplex)
    (hpres : f '' extendedUnitDisc = extendedUnitDisc) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ f ζ = w := by
  have hsub : extendedUnitDisc ⊆ f ⁻¹' extendedClosedUnitDisc := by
    intro z hz
    apply extendedUnitDisc_subset_closed
    rw [← hpres]
    exact Set.mem_image_of_mem f hz
  have hcl : closure extendedUnitDisc ⊆ f ⁻¹' extendedClosedUnitDisc :=
    closure_minimal hsub (isClosed_extendedClosedUnitDisc.preimage f.continuous)
  obtain ⟨w, hw, hfw⟩ := hcl (unitCircle_mem_closure_extendedUnitDisc hζ)
  refine ⟨w, ?_, hfw.symm⟩
  apply le_antisymm hw
  by_contra hnot
  have hwin : (w : Mobius.ExtendedComplex) ∈ extendedUnitDisc :=
    (coe_mem_extendedUnitDisc w).mpr (lt_of_not_ge hnot)
  rw [← hpres] at hwin
  obtain ⟨z, hz, heq⟩ := hwin
  have hzz : z = (ζ : Mobius.ExtendedComplex) := f.injective (heq.trans hfw)
  rw [hzz] at hz
  have hlt := (coe_mem_extendedUnitDisc ζ).mp hz
  exact (ne_of_lt hlt) hζ

/-- The denominator cannot vanish on the unit circle of a disc-preserving transformation. -/
theorem disc_preserver_boundary_norm (g : Mobius.FractionalLinearMatrix)
    (hpres : Mobius.fractionalLinear g '' extendedUnitDisc = extendedUnitDisc)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    g 1 0 * ζ + g 1 1 ≠ 0 ∧ ‖g 0 0 * ζ + g 0 1‖ = ‖g 1 0 * ζ + g 1 1‖ := by
  obtain ⟨w, hw, hgw⟩ := disc_preserver_maps_circle (Mobius.fractionalLinearHomeomorph g) hpres hζ
  change Mobius.fractionalLinear g (ζ : Mobius.ExtendedComplex) = (w : Mobius.ExtendedComplex) at hgw
  have hden : g 1 0 * ζ + g 1 1 ≠ 0 := by
    intro heq
    have hp : Mobius.fractionalLinear g ζ = ∞ := by simp [Mobius.fractionalLinear_coe, heq]
    have he : (w : Mobius.ExtendedComplex) = ∞ := hgw.symm.trans hp
    exact (OnePoint.coe_ne_infty w) he
  refine ⟨hden, ?_⟩
  have hq : (g 0 0 * ζ + g 0 1) / (g 1 0 * ζ + g 1 1) = w := by
    apply OnePoint.coe_injective
    simpa only [Mobius.fractionalLinear_coe, ite_eq_right hden] using hgw
  have hn : ‖g 0 0 * ζ + g 0 1‖ / ‖g 1 0 * ζ + g 1 1‖ = 1 := by
    simpa only [← norm_div, hq] using hw
  exact (div_eq_one_iff_eq (norm_ne_zero_iff.mpr hden)).mp hn

/-- The four boundary test points determine the Hermitian coefficient relations. -/
theorem disc_boundary_coefficient_relations (a b c d : ℂ)
    (hboundary : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖a * ζ + b‖ = ‖c * ζ + d‖) :
    Complex.normSq a + Complex.normSq b = Complex.normSq c + Complex.normSq d ∧
      a * conj b = c * conj d := by
  have h1 := congrArg (fun r : ℝ => r ^ 2) (hboundary 1 (by simp))
  have hm := congrArg (fun r : ℝ => r ^ 2) (hboundary (-1) (by simp))
  have hi := congrArg (fun r : ℝ => r ^ 2) (hboundary Complex.I (by simp))
  have hmi := congrArg (fun r : ℝ => r ^ 2) (hboundary (-Complex.I) (by simp))
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.one_re, Complex.one_im, Complex.neg_re, Complex.neg_im,
    Complex.I_re, Complex.I_im] at h1 hm hi hmi
  constructor
  · simp only [Complex.normSq_apply]
    nlinarith
  · apply Complex.ext
    · simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      nlinarith
    · simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
      nlinarith

/-- A determinant-one disc-preserving coefficient matrix has the SU(1,1) shape. -/
theorem disc_coefficients_normalized (a b c d : ℂ)
    (hdet : a * d - b * c = 1)
    (hboundary : ∀ ζ : ℂ, ‖ζ‖ = 1 → ‖a * ζ + b‖ = ‖c * ζ + d‖)
    (hzero : ‖b‖ < ‖d‖) :
    b = conj c ∧ d = conj a ∧ Complex.normSq a - Complex.normSq c = 1 := by
  obtain ⟨hsum, hcross⟩ := disc_boundary_coefficient_relations a b c d hboundary
  let t : ℝ := Complex.normSq d - Complex.normSq b
  have ht : 0 < t := by
    dsimp [t]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    exact sub_pos.mpr ((sq_lt_sq₀ (norm_nonneg b) (norm_nonneg d)).mpr hzero)
  have hdiff : Complex.normSq a - Complex.normSq c = t := by dsimp [t]; linarith
  have htc : (t : ℂ) = d * conj d - b * conj b := by
    simp only [Complex.mul_conj, ← Complex.ofReal_sub]
    rfl
  have hd : conj d = (t : ℂ) * a := by
    calc
      conj d = (a * d - b * c) * conj d := by rw [hdet, one_mul]
      _ = (t : ℂ) * a := by rw [htc]; linear_combination b * hcross
  have hb : conj b = (t : ℂ) * c := by
    calc
      conj b = (a * d - b * c) * conj b := by rw [hdet, one_mul]
      _ = (t : ℂ) * c := by rw [htc]; linear_combination d * hcross
  have hdiffc : a * conj a - c * conj c = (t : ℂ) := by
    rw [Complex.mul_conj, Complex.mul_conj, ← Complex.ofReal_sub, hdiff]
  have hdetc := congrArg (starRingEnd ℂ) hdet
  simp only [map_sub, map_mul, map_one] at hdetc
  rw [hd, hb] at hdetc
  have ht2c : (t : ℂ) ^ 2 = 1 := by
    calc
      (t : ℂ) ^ 2 = (t : ℂ) * (a * conj a - c * conj c) := by rw [hdiffc]; ring
      _ = conj a * ((t : ℂ) * a) - ((t : ℂ) * c) * conj c := by ring
      _ = 1 := hdetc
  have ht2 : t ^ 2 = 1 := by exact_mod_cast ht2c
  have ht1 : t = 1 := by nlinarith
  refine ⟨?_, ?_, by simpa only [ht1] using hdiff⟩
  · have h := congrArg (starRingEnd ℂ) hb
    simpa [ht1] using h
  · have h := congrArg (starRingEnd ℂ) hd
    simpa [ht1] using h

/-- The extended normalized disc transformation, including its pole and infinity. -/
def normalizedDiscTransformation (a c : ℂ)
    (hdet : Complex.normSq a - Complex.normSq c = 1) : Equiv.Perm Mobius.ExtendedComplex :=
  Mobius.fractionalLinearOfCoefficients a (conj c) c (conj a)
    (by rw [Auxiliary.Analysis.discFractional_determinant hdet]; norm_num)

theorem normalizedDiscTransformation_coe (a c z : ℂ)
    (hdet : Complex.normSq a - Complex.normSq c = 1) :
    normalizedDiscTransformation a c hdet (z : Mobius.ExtendedComplex) =
      if c * z + conj a = 0 then ∞ else (Auxiliary.Analysis.discFractionalMap a c z : Mobius.ExtendedComplex) := by
  simp only [normalizedDiscTransformation, Mobius.fractionalLinearOfCoefficients_coe,
    Auxiliary.Analysis.discFractionalMap, Auxiliary.Analysis.fractionalLinearMap]

theorem normalizedDiscTransformation_of_closedDisc (a c z : ℂ)
    (hdet : Complex.normSq a - Complex.normSq c = 1) (hz : ‖z‖ ≤ 1) :
    normalizedDiscTransformation a c hdet (z : Mobius.ExtendedComplex) =
      (Auxiliary.Analysis.discFractionalMap a c z : Mobius.ExtendedComplex) := by
  rw [normalizedDiscTransformation_coe, ite_eq_right (Auxiliary.Analysis.discFractional_den_ne_zero hdet hz)]

theorem normalizedDiscTransformation_infty (a c : ℂ)
    (hdet : Complex.normSq a - Complex.normSq c = 1) :
    normalizedDiscTransformation a c hdet ∞ =
      if c = 0 then ∞ else ((a / c : ℂ) : Mobius.ExtendedComplex) := by
  exact Mobius.fractionalLinearOfCoefficients_infty _ _ _ _ _

/-- The determinant-one representative of an arbitrary disc preserver has conjugate entries. -/
theorem specialLinear_disc_coefficients (A : Auxiliary.Algebra.SpecialLinear2)
    (hpres : Mobius.fractionalLinear (Matrix.SpecialLinearGroup.toGL A) '' extendedUnitDisc =
      extendedUnitDisc) :
    A 0 1 = conj (A 1 0) ∧ A 1 1 = conj (A 0 0) ∧
      Complex.normSq (A 0 0) - Complex.normSq (A 1 0) = 1 := by
  let g : Mobius.FractionalLinearMatrix := Matrix.SpecialLinearGroup.toGL A
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.det_coe
  have hboundary (ζ : ℂ) (hζ : ‖ζ‖ = 1) :
      ‖A 0 0 * ζ + A 0 1‖ = ‖A 1 0 * ζ + A 1 1‖ :=
    (disc_preserver_boundary_norm g hpres hζ).2
  have hzero : Mobius.fractionalLinear g ((0 : ℂ) : Mobius.ExtendedComplex) ∈ extendedUnitDisc := by
    rw [← hpres]
    exact mem_image_of_mem (Mobius.fractionalLinear g) ((coe_mem_extendedUnitDisc 0).mpr (by simp))
  obtain ⟨w, hw, hweq⟩ := hzero
  have hgw : Mobius.fractionalLinear g ((0 : ℂ) : Mobius.ExtendedComplex) = (w : Mobius.ExtendedComplex) := hweq.symm
  have hd : A 1 1 ≠ 0 := by
    intro hd
    have hp : Mobius.fractionalLinear g ((0 : ℂ) : Mobius.ExtendedComplex) = ∞ := by
      simp [Mobius.fractionalLinear_coe, g, hd]
    exact (OnePoint.coe_ne_infty w) (hgw.symm.trans hp)
  have hquot : A 0 1 / A 1 1 = w := by
    apply OnePoint.coe_injective
    rw [Mobius.fractionalLinear_coe] at hgw
    change (if A 1 0 * 0 + A 1 1 = 0 then ∞ else
        (((A 0 0 * 0 + A 0 1) / (A 1 0 * 0 + A 1 1) : ℂ) : Mobius.ExtendedComplex)) =
      (w : Mobius.ExtendedComplex) at hgw
    simpa only [mul_zero, zero_add, ite_eq_right hd] using hgw
  have hlt : ‖A 0 1‖ < ‖A 1 1‖ := by
    apply (div_lt_one (norm_pos_iff.mpr hd)).mp
    rw [← norm_div, hquot]
    exact hw
  exact disc_coefficients_normalized _ _ _ _ hdet hboundary hlt

/-- Every disc-preserving fractional linear map has the normalized form. -/
theorem fractionalLinear_disc_normal_form (f : Mobius.fractionalLinearGroup)
    (hpres : (f : Equiv.Perm Mobius.ExtendedComplex) '' extendedUnitDisc = extendedUnitDisc) :
    ∃ a c : ℂ, ∃ hdet : Complex.normSq a - Complex.normSq c = 1,
      (f : Equiv.Perm Mobius.ExtendedComplex) = normalizedDiscTransformation a c hdet := by
  obtain ⟨A, hA⟩ := Mobius.specialLinearProjection_surjective f
  have hAg : Mobius.fractionalLinear (Matrix.SpecialLinearGroup.toGL A) =
      (f : Equiv.Perm Mobius.ExtendedComplex) := congrArg Subtype.val hA
  have hpresA : Mobius.fractionalLinear (Matrix.SpecialLinearGroup.toGL A) '' extendedUnitDisc =
      extendedUnitDisc := by rw [hAg]; exact hpres
  obtain ⟨hb, hd, hdet⟩ := specialLinear_disc_coefficients A hpresA
  refine ⟨A 0 0, A 1 0, hdet, ?_⟩
  rw [← hAg]
  apply congrArg Mobius.fractionalLinear
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Mobius.coefficientMatrix, hb, hd]

/-- The same classification applies to the actual orientation-preserving complex Möbius group. -/
theorem complexMobius_disc_normal_form (f : Mobius.complexMobiusGroup)
    (hpres : (f : Equiv.Perm Mobius.ExtendedComplex) '' extendedUnitDisc = extendedUnitDisc) :
    ∃ a c : ℂ, ∃ hdet : Complex.normSq a - Complex.normSq c = 1,
      (f : Equiv.Perm Mobius.ExtendedComplex) = normalizedDiscTransformation a c hdet := by
  let g : Mobius.fractionalLinearGroup := ⟨(f : Equiv.Perm Mobius.ExtendedComplex), by
    rw [← Mobius.complexMobiusGroup_eq_fractionalLinearGroup]
    exact f.property⟩
  exact fractionalLinear_disc_normal_form g hpres

end DiscNormalForm

section DiscFamily
open LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
/-- The inverse coefficients retain the unit indefinite determinant. -/
theorem discFractional_inverse_determinant {a c : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1) :
    Complex.normSq (conj a) - Complex.normSq (-c) = 1 := by
  simpa only [Complex.normSq_conj, Complex.normSq_neg] using hdet

/-- The normalized family has the expected inverse at every point of the closed unit disc. -/
theorem discFractional_left_inverse {a c z : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1) (hz : ‖z‖ ≤ 1) :
    Auxiliary.Analysis.discFractionalMap (conj a) (-c) (Auxiliary.Analysis.discFractionalMap a c z) = z := by
  have hd := Auxiliary.Analysis.discFractional_den_ne_zero hdet hz
  have h := Auxiliary.Analysis.discFractional_determinant hdet
  have hi : -c * ((a * z + conj c) / (c * z + conj a)) + a ≠ 0 := by
    intro hn
    have hn' : -c * (a * z + conj c) + a * (c * z + conj a) = 0 := by
      simpa only [map_neg, Complex.conj_conj] using (div_eq_zero_iff.mp
        (show (-c * (a * z + conj c) + a * (c * z + conj a)) /
          (c * z + conj a) = 0 by
            rw [add_div, mul_div_assoc, mul_div_cancel_right₀ a hd]
            exact hn)).resolve_right hd
    have heq : -c * (a * z + conj c) + a * (c * z + conj a) = 1 := by
      linear_combination h
    exact one_ne_zero (heq.symm.trans hn')
  unfold Auxiliary.Analysis.discFractionalMap Auxiliary.Analysis.fractionalLinearMap
  simp only [map_neg, Complex.conj_conj]
  apply (div_eq_iff hi).mpr
  have hd' : z * c + conj a ≠ 0 := by simpa only [mul_comm c z] using hd
  field_simp [hd, hd']
  ring

/-- The same explicit inverse is also a right inverse on the closed unit disc. -/
theorem discFractional_right_inverse {a c z : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1) (hz : ‖z‖ ≤ 1) :
    Auxiliary.Analysis.discFractionalMap a c (Auxiliary.Analysis.discFractionalMap (conj a) (-c) z) = z := by
  simpa only [Complex.conj_conj, neg_neg] using
    discFractional_left_inverse (discFractional_inverse_determinant hdet) hz

/-- Every normalized coefficient pair maps the open unit disc bijectively onto itself. -/
theorem discFractional_bijOn {a c : ℂ}
    (hdet : Complex.normSq a - Complex.normSq c = 1) :
    Set.BijOn (Auxiliary.Analysis.discFractionalMap a c) {z : ℂ | ‖z‖ < 1} {z : ℂ | ‖z‖ < 1} := by
  refine ⟨fun z hz => Auxiliary.Analysis.discFractional_maps_disc hdet hz, ?_, ?_⟩
  · intro z hz w hw hzw
    have h := congrArg (Auxiliary.Analysis.discFractionalMap (conj a) (-c)) hzw
    rw [discFractional_left_inverse hdet hz.le, discFractional_left_inverse hdet hw.le] at h
    exact h
  · intro z hz
    refine ⟨Auxiliary.Analysis.discFractionalMap (conj a) (-c) z,
      Auxiliary.Analysis.discFractional_maps_disc (discFractional_inverse_determinant hdet) hz,
      discFractional_right_inverse hdet hz.le⟩

/-- The normalized fractional formula is a genuine equivalence of the actual unit-disc type. -/
def discFractionalEquiv (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1) : 𝔻 ≃ 𝔻 where
  toFun z := Complex.UnitDisc.mk (Auxiliary.Analysis.discFractionalMap a c z)
    (Auxiliary.Analysis.discFractional_maps_disc hdet z.norm_lt_one)
  invFun z := Complex.UnitDisc.mk (Auxiliary.Analysis.discFractionalMap (conj a) (-c) z)
    (Auxiliary.Analysis.discFractional_maps_disc (discFractional_inverse_determinant hdet) z.norm_lt_one)
  left_inv z := Complex.UnitDisc.coe_injective
    (discFractional_left_inverse hdet z.norm_lt_one.le)
  right_inv z := Complex.UnitDisc.coe_injective
    (discFractional_right_inverse hdet z.norm_lt_one.le)

/-- The normalized fractional formula is continuous throughout the unit disc. -/
theorem continuous_discFractionalEquiv (a c : ℂ)
    (hdet : Complex.normSq a - Complex.normSq c = 1) : Continuous (discFractionalEquiv a c hdet) := by
  apply Complex.UnitDisc.isEmbedding_coe.continuous_iff.mpr
  change Continuous (fun z : 𝔻 => (a * (z : ℂ) + conj c) / (c * (z : ℂ) + conj a))
  exact ((continuous_const.mul Complex.UnitDisc.continuous_coe).add continuous_const).div
    ((continuous_const.mul Complex.UnitDisc.continuous_coe).add continuous_const)
    (fun z => Auxiliary.Analysis.discFractional_den_ne_zero hdet z.norm_lt_one.le)

/-- The entire normalized family consists of actual unit-disc homeomorphisms. -/
def discFractionalHomeomorph (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1) :
    𝔻 ≃ₜ 𝔻 where
  toEquiv := discFractionalEquiv a c hdet
  continuous_toFun := continuous_discFractionalEquiv a c hdet
  continuous_invFun := continuous_discFractionalEquiv (conj a) (-c)
    (discFractional_inverse_determinant hdet)

/-- Every normalized extended transformation preserves the open unit disc onto itself. -/
theorem normalizedDiscTransformation_preserves_disc (a c : ℂ)
    (hdet : Complex.normSq a - Complex.normSq c = 1) :
    normalizedDiscTransformation a c hdet '' extendedUnitDisc = extendedUnitDisc := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [normalizedDiscTransformation_of_closedDisc a c z hdet hz.le]
    exact ⟨Auxiliary.Analysis.discFractionalMap a c z, Auxiliary.Analysis.discFractional_maps_disc hdet hz, rfl⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨w, hw, hzw⟩ := (discFractional_bijOn hdet).surjOn hz
    refine ⟨(w : Mobius.ExtendedComplex), ⟨w, hw, rfl⟩, ?_⟩
    rw [normalizedDiscTransformation_of_closedDisc a c w hdet hw.le, hzw]

/-- The normalized family exactly describes the disc-preserving fractional linear maps. -/
theorem fractionalLinear_preserves_disc_iff_normal_form (f : Mobius.fractionalLinearGroup) :
    (f : Equiv.Perm Mobius.ExtendedComplex) '' extendedUnitDisc = extendedUnitDisc ↔
      ∃ a c : ℂ, ∃ hdet : Complex.normSq a - Complex.normSq c = 1,
        (f : Equiv.Perm Mobius.ExtendedComplex) = normalizedDiscTransformation a c hdet := by
  refine ⟨fractionalLinear_disc_normal_form f, ?_⟩
  rintro ⟨a, c, hdet, hf⟩
  rw [hf]
  exact normalizedDiscTransformation_preserves_disc a c hdet

/-- The normal form is equivalent to preservation by an actual complex Möbius map. -/
theorem complexMobius_preserves_disc_iff_normal_form (f : Mobius.complexMobiusGroup) :
    (f : Equiv.Perm Mobius.ExtendedComplex) '' extendedUnitDisc = extendedUnitDisc ↔
      ∃ a c : ℂ, ∃ hdet : Complex.normSq a - Complex.normSq c = 1,
        (f : Equiv.Perm Mobius.ExtendedComplex) = normalizedDiscTransformation a c hdet := by
  refine ⟨complexMobius_disc_normal_form f, ?_⟩
  rintro ⟨a, c, hdet, hf⟩
  rw [hf]
  exact normalizedDiscTransformation_preserves_disc a c hdet

end DiscFamily

end
end LowDimensionalTopology.Geometry.Hyperbolic
