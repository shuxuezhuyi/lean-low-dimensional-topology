/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Mobius.Topology
public import Mathlib.Topology.MetricSpace.Thickening

/-!
# Quantitative contraction from two omitted values

Roots of the two matrix rows represent the preimages of zero and infinity.
Their chordal separation from a compact subset gives a lower bound for
homogeneous quadratic norms. This controls the chordal image diameter by
the inverse squared normalized matrix norm; norm divergence then yields
shrinking images for injective sequences in a discrete subgroup.
-/

@[expose] public section

open Set Filter Matrix
open scoped Topology OnePoint MatrixGroups

namespace LowDimensionalTopology.Geometry.Mobius

open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.DiscreteGroups

noncomputable section

local instance mobiusOmittedChordalMetric : MetricSpace ExtendedComplex := complexChordalMetricSpace

def complexRowRootVector (r : Fin 2 → ℂ) : Fin 2 → ℂ := ![-r 1, r 0]

theorem complexRowRootVector_ne_zero {r : Fin 2 → ℂ} (hr : r ≠ 0) :
    complexRowRootVector r ≠ 0 := by
  intro hz
  apply hr
  have h0 := congrFun hz 0
  have h1 := congrFun hz 1
  ext i
  fin_cases i
  · simpa [complexRowRootVector] using h1
  · have he : -r 1 = 0 := by simpa [complexRowRootVector] using h0
    exact neg_eq_zero.mp he

theorem complexRowRootVector_quadratic (r : Fin 2 → ℂ) :
    complexVectorQuadratic (complexRowRootVector r) = complexVectorQuadratic r := by
  simp [complexRowRootVector, complexVectorQuadratic, add_comm]

theorem complexRowEvaluation_chordal_sq (r v : Fin 2 → ℂ) (hr : r ≠ 0) (hv : v ≠ 0) :
    complexChordalDist (complexProjectivePoint v) (complexProjectivePoint (complexRowRootVector r)) ^ 2 *
        (complexVectorQuadratic v * complexVectorQuadratic r) =
      4 * ‖r 0 * v 0 + r 1 * v 1‖ ^ 2 := by
  have hd := complexChordalDist_projective_sq v (complexRowRootVector r) hv
    (complexRowRootVector_ne_zero hr)
  change complexChordalDist (complexProjectivePoint v) (complexProjectivePoint (complexRowRootVector r)) ^ 2 =
    4 * ‖v 0 * (complexRowRootVector r) 1 - v 1 * (complexRowRootVector r) 0‖ ^ 2 /
      (complexVectorQuadratic v * complexVectorQuadratic (complexRowRootVector r)) at hd
  rw [complexRowRootVector_quadratic] at hd
  have he : v 0 * (complexRowRootVector r) 1 - v 1 * (complexRowRootVector r) 0 =
      r 0 * v 0 + r 1 * v 1 := by simp only [complexRowRootVector, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]; ring
  rw [he] at hd
  exact (eq_div_iff (mul_pos (complexVectorQuadratic_pos hv) (complexVectorQuadratic_pos hr)).ne').mp hd

theorem specialLinear_row_ne_zero (A : Auxiliary.Algebra.SpecialLinear2) (i : Fin 2) :
    (fun j => A i j) ≠ 0 := by
  intro hz
  have h0 := congrFun hz 0
  have h1 := congrFun hz 1
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.det_coe
  fin_cases i
  · change A 0 0 = 0 at h0
    change A 0 1 = 0 at h1
    rw [h0, h1] at hdet
    norm_num at hdet
  · change A 1 0 = 0 at h0
    change A 1 1 = 0 at h1
    rw [h0, h1] at hdet
    norm_num at hdet

theorem specialLinear_projective_point (A : Auxiliary.Algebra.SpecialLinear2) (v : Fin 2 → ℂ) (hv : v ≠ 0) :
    (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) (complexProjectivePoint v) =
      complexProjectivePoint (Matrix.SpecialLinearGroup.toGL A • v) := by
  have hp := congrArg (fun f : fractionalLinearGroup => (f : Equiv.Perm ExtendedComplex))
    (mobiusSpecialLinearProjection_equiv A)
  change (complexMobiusEquivFractionalLinear (mobiusSpecialLinearProjection A) :
    Equiv.Perm ExtendedComplex) = fractionalLinear (Matrix.SpecialLinearGroup.toGL A) at hp
  rw [complexMobiusEquivFractionalLinear_apply] at hp
  rw [hp]
  exact (complexProjectivePoint_smul _ _ hv).symm

theorem specialLinear_vector_formula (A : Auxiliary.Algebra.SpecialLinear2) (v : Fin 2 → ℂ) :
    Matrix.SpecialLinearGroup.toGL A • v =
      ![A 0 0 * v 0 + A 0 1 * v 1, A 1 0 * v 0 + A 1 1 * v 1] := by
  rw [Matrix.GeneralLinearGroup.fin_two_smul]
  rfl

theorem specialLinear_rowRoot_image (A : Auxiliary.Algebra.SpecialLinear2) (i : Fin 2) :
    (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex)
      (complexProjectivePoint (complexRowRootVector (fun j => A i j))) =
        if i = 0 then ((0 : ℂ) : ExtendedComplex) else ∞ := by
  rw [specialLinear_projective_point A _ (complexRowRootVector_ne_zero (specialLinear_row_ne_zero A i))]
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.det_coe
  fin_cases i
  · change complexProjectivePoint (Matrix.SpecialLinearGroup.toGL A •
      complexRowRootVector (fun j => A 0 j)) = ((0 : ℂ) : ExtendedComplex)
    have he : Matrix.SpecialLinearGroup.toGL A • complexRowRootVector (fun j => A 0 j) =
        ![0, 1] := by
      rw [specialLinear_vector_formula]
      ext j
      fin_cases j
      · change A 0 0 * (-A 0 1) + A 0 1 * A 0 0 = 0
        ring
      · change A 1 0 * (-A 0 1) + A 1 1 * A 0 0 = 1
        linear_combination hdet
    rw [he]
    simp [complexProjectivePoint]
  · change complexProjectivePoint (Matrix.SpecialLinearGroup.toGL A •
      complexRowRootVector (fun j => A 1 j)) = ∞
    have he : Matrix.SpecialLinearGroup.toGL A • complexRowRootVector (fun j => A 1 j) =
        ![-1, 0] := by
      rw [specialLinear_vector_formula]
      ext j
      fin_cases j
      · change A 0 0 * (-A 1 1) + A 0 1 * A 1 0 = -1
        linear_combination -hdet
      · change A 1 0 * (-A 1 1) + A 1 1 * A 1 0 = 0
        ring
    rw [he]
    simp [complexProjectivePoint]

theorem compact_open_chordal_separation {D K : Set ExtendedComplex}
    (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ K, ∀ w ∉ D, ε ≤ complexChordalDist z w := by
  obtain ⟨ε, hε, hsub⟩ := hK.exists_thickening_subset_open hD hKD
  refine ⟨ε, hε, fun z hz w hw => ?_⟩
  by_contra! hd
  apply hw
  apply hsub
  exact Metric.mem_thickening_iff.mpr ⟨z, hz, by simpa [dist_comm, complexChordalMetricSpace_dist] using hd⟩

theorem specialLinear_rowRoots_not_mem {D : Set ExtendedComplex} (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : ∀ z ∈ D,
      (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) z ≠ ((0 : ℂ) : ExtendedComplex) ∧
      (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) z ≠ ∞)
    (i : Fin 2) : complexProjectivePoint (complexRowRootVector (fun j => A i j)) ∉ D := by
  intro hi
  have hn := hA _ hi
  have hm := specialLinear_rowRoot_image A i
  by_cases hi0 : i = 0
  · exact hn.1 (by simpa only [ite_eq_left hi0] using hm)
  · exact hn.2 (by simpa only [ite_eq_right hi0] using hm)

theorem specialLinear_quadratic_lower_of_omitted_values
    {D K : Set ExtendedComplex} {ε : ℝ} (hε : 0 < ε)
    (hsep : ∀ z ∈ K, ∀ w ∉ D, ε ≤ complexChordalDist z w)
    (A : Auxiliary.Algebra.SpecialLinear2)
    (hA : ∀ z ∈ D,
      (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) z ≠ ((0 : ℂ) : ExtendedComplex) ∧
      (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) z ≠ ∞)
    (v : Fin 2 → ℂ) (hv : v ≠ 0) (hz : complexProjectivePoint v ∈ K) :
    ε ^ 2 * Auxiliary.Algebra.matrixNorm (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 * complexVectorQuadratic v ≤
      4 * complexVectorQuadratic (Matrix.SpecialLinearGroup.toGL A • v) := by
  have hrow (i : Fin 2) :
      ε ^ 2 * (complexVectorQuadratic v * complexVectorQuadratic (fun j => A i j)) ≤
        4 * ‖A i 0 * v 0 + A i 1 * v 1‖ ^ 2 := by
    have hs := hsep _ hz _ (specialLinear_rowRoots_not_mem A hA i)
    have hsq : ε ^ 2 ≤ complexChordalDist (complexProjectivePoint v)
        (complexProjectivePoint (complexRowRootVector (fun j => A i j))) ^ 2 :=
      (sq_le_sq₀ hε.le (complexChordalDist_nonneg _ _)).mpr hs
    exact (mul_le_mul_of_nonneg_right hsq
      (mul_pos (complexVectorQuadratic_pos hv)
        (complexVectorQuadratic_pos (specialLinear_row_ne_zero A i))).le).trans_eq
      (complexRowEvaluation_chordal_sq _ v (specialLinear_row_ne_zero A i) hv)
  have h0 := hrow 0
  have h1 := hrow 1
  rw [Auxiliary.Algebra.matrixNorm_sq, specialLinear_vector_formula]
  change ε ^ 2 * (‖A 0 0‖ ^ 2 + ‖A 0 1‖ ^ 2 + ‖A 1 0‖ ^ 2 + ‖A 1 1‖ ^ 2) *
    complexVectorQuadratic v ≤
      4 * (‖A 0 0 * v 0 + A 0 1 * v 1‖ ^ 2 + ‖A 1 0 * v 0 + A 1 1 * v 1‖ ^ 2)
  dsimp only [complexVectorQuadratic] at h0 h1 ⊢
  nlinarith only [h0, h1]


/-- Positive homogeneous denominator bounds yield the exact chordal contraction estimate. -/
theorem fractionalLinear_chordal_bound_of_quadratic_lower (G : FractionalLinearMatrix)
    (hdet : (G : Auxiliary.Algebra.ComplexMatrix2).det = 1) {ε : ℝ} (hε : 0 < ε)
    (v w : Fin 2 → ℂ) (hv : v ≠ 0) (hw : w ≠ 0)
    (hz : ε ^ 2 * Auxiliary.Algebra.matrixNorm (G : Auxiliary.Algebra.ComplexMatrix2) ^ 2 * complexVectorQuadratic v ≤
      4 * complexVectorQuadratic (G • v))
    (hw' : ε ^ 2 * Auxiliary.Algebra.matrixNorm (G : Auxiliary.Algebra.ComplexMatrix2) ^ 2 * complexVectorQuadratic w ≤
      4 * complexVectorQuadratic (G • w)) :
    complexChordalDist (fractionalLinear G (complexProjectivePoint v))
      (fractionalLinear G (complexProjectivePoint w)) ≤
        (4 / ε ^ 2) * complexChordalDist (complexProjectivePoint v) (complexProjectivePoint w) /
          Auxiliary.Algebra.matrixNorm (G : Auxiliary.Algebra.ComplexMatrix2) ^ 2 := by
  let a := complexChordalDist (fractionalLinear G (complexProjectivePoint v))
    (fractionalLinear G (complexProjectivePoint w))
  let b := complexChordalDist (complexProjectivePoint v) (complexProjectivePoint w)
  let M := Auxiliary.Algebra.matrixNorm (G : Auxiliary.Algebra.ComplexMatrix2)
  have hM : 0 < M ^ 2 := by
    have hd := Auxiliary.Algebra.determinant_norm_le (G : Auxiliary.Algebra.ComplexMatrix2)
    rw [hdet, norm_one] at hd
    dsimp only [M]
    linarith
  have heps : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hqv := complexVectorQuadratic_pos hv
  have hqw := complexVectorQuadratic_pos hw
  have hqGv := complexVectorQuadratic_pos ((smul_ne_zero_iff_ne G).mpr hv)
  have hqGw := complexVectorQuadratic_pos ((smul_ne_zero_iff_ne G).mpr hw)
  have hA := fractionalLinear_homogeneous_chordal_sq G v w hv hw
  rw [hdet, norm_one, one_pow, mul_one] at hA
  have hB := complexChordalDist_projective_sq v w hv hw
  change a ^ 2 = 4 * ‖v 0 * w 1 - v 1 * w 0‖ ^ 2 /
    (complexVectorQuadratic (G • v) * complexVectorQuadratic (G • w)) at hA
  change b ^ 2 = 4 * ‖v 0 * w 1 - v 1 * w 0‖ ^ 2 /
    (complexVectorQuadratic v * complexVectorQuadratic w) at hB
  have hcross : a ^ 2 * (complexVectorQuadratic (G • v) * complexVectorQuadratic (G • w)) =
      b ^ 2 * (complexVectorQuadratic v * complexVectorQuadratic w) :=
    ((eq_div_iff (mul_pos hqGv hqGw).ne').mp hA).trans
      ((eq_div_iff (mul_pos hqv hqw).ne').mp hB).symm
  have hprod := mul_le_mul hz hw' (by positivity) (by positivity)
  have hc : (a * (ε ^ 2 * M ^ 2)) ^ 2 * (complexVectorQuadratic v * complexVectorQuadratic w) ≤
      (4 * b) ^ 2 * (complexVectorQuadratic v * complexVectorQuadratic w) := by
    calc
      _ = a ^ 2 * ((ε ^ 2 * M ^ 2 * complexVectorQuadratic v) *
        (ε ^ 2 * M ^ 2 * complexVectorQuadratic w)) := by ring
      _ ≤ a ^ 2 * ((4 * complexVectorQuadratic (G • v)) *
        (4 * complexVectorQuadratic (G • w))) :=
          mul_le_mul_of_nonneg_left hprod (sq_nonneg a)
      _ = 16 * (a ^ 2 * (complexVectorQuadratic (G • v) *
        complexVectorQuadratic (G • w))) := by ring
      _ = 16 * (b ^ 2 * (complexVectorQuadratic v * complexVectorQuadratic w)) := by rw [hcross]
      _ = _ := by ring
  have hs := (mul_le_mul_iff_left₀ (mul_pos hqv hqw)).mp hc
  have ha : 0 ≤ a := complexChordalDist_nonneg _ _
  have hb : 0 ≤ b := complexChordalDist_nonneg _ _
  have hl : a * (ε ^ 2 * M ^ 2) ≤ 4 * b :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hs
  change a ≤ (4 / ε ^ 2) * b / M ^ 2
  apply (le_div_iff₀ hM).mpr
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ heps).mpr
  nlinarith only [hl]


theorem specialLinear_projection_coe (A : Auxiliary.Algebra.SpecialLinear2) :
    (mobiusSpecialLinearProjection A : Equiv.Perm ExtendedComplex) =
      fractionalLinear (Matrix.SpecialLinearGroup.toGL A) := by
  have hp := congrArg (fun f : fractionalLinearGroup => (f : Equiv.Perm ExtendedComplex))
    (mobiusSpecialLinearProjection_equiv A)
  change (complexMobiusEquivFractionalLinear (mobiusSpecialLinearProjection A) :
    Equiv.Perm ExtendedComplex) = fractionalLinear (Matrix.SpecialLinearGroup.toGL A) at hp
  simpa only [complexMobiusEquivFractionalLinear_apply] using hp

/-- The compact-subset chordal estimate for transformations omitting two values. -/
theorem chordal_dist_le_norm_inv_sq_of_omits_zero_infty {D K : Set ExtendedComplex}
    (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ m : ℝ, 0 < m ∧ ∀ g : complexMobiusGroup,
      (∀ z ∈ D, (g : Equiv.Perm ExtendedComplex) z ≠ ((0 : ℂ) : ExtendedComplex) ∧
        (g : Equiv.Perm ExtendedComplex) z ≠ ∞) →
      ∀ z ∈ K, ∀ w ∈ K,
        complexChordalDist ((g : Equiv.Perm ExtendedComplex) z)
          ((g : Equiv.Perm ExtendedComplex) w) ≤
          m * complexChordalDist z w / mobiusNormalizedNorm g ^ 2 := by
  obtain ⟨ε, hε, hsep⟩ := compact_open_chordal_separation hD hK hKD
  refine ⟨4 / ε ^ 2, by positivity, fun g hgo z hz w hw => ?_⟩
  obtain ⟨A, rfl⟩ := mobiusSpecialLinearProjection_surjective g
  let v := complexProjectiveVector z
  let u := complexProjectiveVector w
  have hv : v ≠ 0 := complexProjectiveVector_ne_zero z
  have hu : u ≠ 0 := complexProjectiveVector_ne_zero w
  have hz' : complexProjectivePoint v ∈ K := by
    simpa only [v, complexProjectivePoint_vector] using hz
  have hw' : complexProjectivePoint u ∈ K := by
    simpa only [u, complexProjectivePoint_vector] using hw
  have hzq := specialLinear_quadratic_lower_of_omitted_values hε hsep A hgo v hv hz'
  have hwq := specialLinear_quadratic_lower_of_omitted_values hε hsep A hgo u hu hw'
  have hdet : (Matrix.SpecialLinearGroup.toGL A : Auxiliary.Algebra.ComplexMatrix2).det = 1 := A.det_coe
  have hc := fractionalLinear_chordal_bound_of_quadratic_lower
    (Matrix.SpecialLinearGroup.toGL A) hdet hε v u hv hu hzq hwq
  simpa only [v, u, complexProjectivePoint_vector,
    mobiusNormalizedNorm_specialLinearProjection, specialLinear_projection_coe,
    Matrix.SpecialLinearGroup.coe_GL_coe_matrix] using hc

/-- Diameter measured in the chordal metric of the extended complex plane. -/
def complexChordalDiameter (S : Set ExtendedComplex) : ℝ := Metric.diam S

/-- A uniform chordal Lipschitz bound controls the diameter of a compact image. -/
theorem complexChordalDiameter_image_le {K : Set ExtendedComplex} (hK : IsCompact K)
    (g : complexMobiusGroup) {C : ℝ} (hC : 0 ≤ C)
    (hg : ∀ z ∈ K, ∀ w ∈ K,
      complexChordalDist ((g : Equiv.Perm ExtendedComplex) z)
        ((g : Equiv.Perm ExtendedComplex) w) ≤ C * complexChordalDist z w) :
    complexChordalDiameter ((g : Equiv.Perm ExtendedComplex) '' K) ≤
      C * complexChordalDiameter K := by
  apply Metric.diam_le_of_forall_dist_le (mul_nonneg hC Metric.diam_nonneg)
  rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩
  exact (hg z hz w hw).trans
    (mul_le_mul_of_nonneg_left (Metric.dist_le_diam_of_mem hK.isBounded hz hw) hC)

/-- The same compact-set constant gives a diameter bound for every omitted-values map. -/
theorem chordal_diameter_le_norm_inv_sq_of_omits_zero_infty {D K : Set ExtendedComplex}
    (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D) :
    ∃ m : ℝ, 0 < m ∧ ∀ g : complexMobiusGroup,
      (∀ z ∈ D, (g : Equiv.Perm ExtendedComplex) z ≠ ((0 : ℂ) : ExtendedComplex) ∧
        (g : Equiv.Perm ExtendedComplex) z ≠ ∞) →
      complexChordalDiameter ((g : Equiv.Perm ExtendedComplex) '' K) ≤
        m * complexChordalDiameter K / mobiusNormalizedNorm g ^ 2 := by
  obtain ⟨m, hm, hbound⟩ := chordal_dist_le_norm_inv_sq_of_omits_zero_infty hD hK hKD
  refine ⟨m, hm, fun g hg => ?_⟩
  have hC : 0 ≤ m / mobiusNormalizedNorm g ^ 2 := div_nonneg hm.le (sq_nonneg _)
  calc
    _ ≤ (m / mobiusNormalizedNorm g ^ 2) * complexChordalDiameter K :=
      complexChordalDiameter_image_le hK g hC (fun z hz w hw => by
        simpa only [div_mul_eq_mul_div] using hbound g hg z hz w hw)
    _ = _ := by ring

/-- Omitted-values images shrink when the normalized matrix norms diverge. -/
theorem mobius_omitted_values_diameter_tendsto_zero {D K : Set ExtendedComplex}
    (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D)
    (f : ℕ → complexMobiusGroup)
    (hf : ∀ n, ∀ z ∈ D,
      (f n : Equiv.Perm ExtendedComplex) z ≠ ((0 : ℂ) : ExtendedComplex) ∧
        (f n : Equiv.Perm ExtendedComplex) z ≠ ∞)
    (hnorm : Tendsto (fun n => mobiusNormalizedNorm (f n)) atTop atTop) :
    Tendsto (fun n => complexChordalDiameter ((f n : Equiv.Perm ExtendedComplex) '' K))
      atTop (𝓝 0) := by
  obtain ⟨m, _, hm⟩ := chordal_diameter_le_norm_inv_sq_of_omits_zero_infty hD hK hKD
  have hinv : Tendsto (fun n => (mobiusNormalizedNorm (f n))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hnorm
  have hbound : Tendsto
      (fun n => m * complexChordalDiameter K / mobiusNormalizedNorm (f n) ^ 2)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, zero_pow (by decide : 2 ≠ 0), mul_zero]
      using (tendsto_const_nhds.mul (hinv.pow 2))
  exact squeeze_zero (fun _ => Metric.diam_nonneg) (fun n => hm (f n) (hf n)) hbound

/-- The compact omitted-values images of distinct elements in a discrete subgroup shrink. -/
theorem discreteMobius_omitted_values_diameter_tendsto_zero
    (H : Subgroup complexMobiusGroup) (hH : IsDiscreteMobiusSubgroup H)
    {D K : Set ExtendedComplex} (hD : IsOpen D) (hK : IsCompact K) (hKD : K ⊆ D)
    (f : ℕ → H) (hf : Function.Injective f)
    (homit : ∀ n, ∀ z ∈ D,
      ((f n).val : Equiv.Perm ExtendedComplex) z ≠ ((0 : ℂ) : ExtendedComplex) ∧
        ((f n).val : Equiv.Perm ExtendedComplex) z ≠ ∞) :
    Tendsto (fun n => complexChordalDiameter (((f n).val : Equiv.Perm ExtendedComplex) '' K))
      atTop (𝓝 0) := by
  exact mobius_omitted_values_diameter_tendsto_zero hD hK hKD
    (fun n => (f n).val) homit (discreteMobius_injective_sequence_norm_tendsto H hH f hf)

end
end LowDimensionalTopology.Geometry.Mobius
