/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Fractional linear transformations

The carrier is the standard one-point compactification of the complex plane.
The projective-line action supplies the exceptional values and the exact composition law.
Comparison with the reflection-generated Möbius group is a separate result.
-/

@[expose] public section

namespace LowDimensionalTopology.Geometry.Mobius

open scoped OnePoint Topology
open Filter

/-- The extended complex plane with its standard compactification topology. -/
abbrev ExtendedComplex := OnePoint ℂ
/-- An invertible complex matrix representing a fractional linear map. -/
abbrev FractionalLinearMatrix := Matrix.GeneralLinearGroup (Fin 2) ℂ

/-- The standard coordinate identification with the compactified Euclidean plane. -/
noncomputable def extendedComplexEuclideanHomeomorph :
    ExtendedComplex ≃ₜ OnePoint (EuclideanSpace ℝ (Fin 2)) :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.onePointCongr

/-- The coordinate identification agrees with the real and imaginary coordinates at finite points. -/
theorem extendedComplexEuclideanHomeomorph_coe (z : ℂ) :
    extendedComplexEuclideanHomeomorph z =
      (Complex.orthonormalBasisOneI.repr z : OnePoint (EuclideanSpace ℝ (Fin 2))) := rfl

/-- The coordinate identification preserves infinity. -/
theorem extendedComplexEuclideanHomeomorph_infty :
    extendedComplexEuclideanHomeomorph ∞ = ∞ := rfl

/-- matrix multiplication acts by composition on the extended plane. -/
noncomputable def fractionalLinearHom : FractionalLinearMatrix →* Equiv.Perm ExtendedComplex :=
  MulAction.toPermHom _ _

/-- The extended fractional linear bijection represented by an invertible matrix. -/
noncomputable def fractionalLinear (g : FractionalLinearMatrix) : Equiv.Perm ExtendedComplex :=
  fractionalLinearHom g

/-- The projective-line action is the underlying fractional linear map. -/
theorem fractionalLinear_apply (g : FractionalLinearMatrix) (z : ExtendedComplex) :
    fractionalLinear g z = g • z := rfl

/-- equation: the finite-point formula including the pole. -/
theorem fractionalLinear_coe (g : FractionalLinearMatrix) (z : ℂ) :
    fractionalLinear g z = if g 1 0 * z + g 1 1 = 0 then ∞
      else ((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) : ℂ) :=
  OnePoint.smul_some_eq_ite

/-- The prescribed value at infinity. -/
theorem fractionalLinear_infty (g : FractionalLinearMatrix) :
    fractionalLinear g ∞ = if g 1 0 = 0 then ∞ else (g 0 0 / g 1 0 : ℂ) :=
  OnePoint.smul_infty_eq_ite g

/-- equations: a nonsingular coefficient matrix. -/
noncomputable def coefficientMatrix (a b c d : ℂ) (h : a * d - b * c ≠ 0) :
    FractionalLinearMatrix := Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d]
      (by simpa [Matrix.det_fin_two] using h)

/-- The matrix constructor retains the original four coefficients. -/
theorem coefficientMatrix_val (a b c d : ℂ) (h : a * d - b * c ≠ 0) :
    (coefficientMatrix a b c d h : Matrix (Fin 2) (Fin 2) ℂ) = !![a, b; c, d] := rfl

/-- equations: the map associated with four coefficients. -/
noncomputable def fractionalLinearOfCoefficients (a b c d : ℂ)
    (h : a * d - b * c ≠ 0) : Equiv.Perm ExtendedComplex :=
  fractionalLinear (coefficientMatrix a b c d h)

/-- The coefficient formula for every finite input, including its exceptional branch. -/
theorem fractionalLinearOfCoefficients_coe (a b c d z : ℂ) (h : a * d - b * c ≠ 0) :
    fractionalLinearOfCoefficients a b c d h z =
      if c * z + d = 0 then ∞ else ((a * z + b) / (c * z + d) : ℂ) :=
  fractionalLinear_coe _ _

/-- The coefficient formula at infinity. -/
theorem fractionalLinearOfCoefficients_infty (a b c d : ℂ) (h : a * d - b * c ≠ 0) :
    fractionalLinearOfCoefficients a b c d h ∞ =
      if c = 0 then ∞ else (a / c : ℂ) :=
  fractionalLinear_infty _

/-- The unique pole when the lower-left coefficient is nonzero. -/
theorem denominator_eq_zero_iff (c d z : ℂ) (hc : c ≠ 0) :
    c * z + d = 0 ↔ z = -d / c := by
  constructor
  · intro hz
    apply (eq_div_iff hc).mpr
    linear_combination hz
  · rintro rfl
    field_simp
    ring

/-- The pole maps to infinity. -/
theorem fractionalLinearOfCoefficients_pole (a b c d : ℂ)
    (h : a * d - b * c ≠ 0) (hc : c ≠ 0) :
    fractionalLinearOfCoefficients a b c d h (-d / c : ℂ) = ∞ := by
  rw [fractionalLinearOfCoefficients_coe]
  simp [(denominator_eq_zero_iff c d _ hc).mpr rfl]

/-- Away from the pole, the map agrees with the complex quotient. -/
theorem fractionalLinearOfCoefficients_finite (a b c d z : ℂ)
    (h : a * d - b * c ≠ 0) (hz : c * z + d ≠ 0) :
    fractionalLinearOfCoefficients a b c d h z = ((a * z + b) / (c * z + d) : ℂ) := by
  rw [fractionalLinearOfCoefficients_coe, ite_eq_right hz]

/-- The affine case is defined at every finite point. -/
theorem fractionalLinearOfCoefficients_affine (a b d z : ℂ)
    (h : a * d - b * 0 ≠ 0) :
    fractionalLinearOfCoefficients a b 0 d h z = ((a * z + b) / d : ℂ) := by
  have hd : d ≠ 0 := by intro hd; simp [hd] at h
  simp [fractionalLinearOfCoefficients_coe, hd]

/-- The affine case fixes infinity. -/
theorem fractionalLinearOfCoefficients_affine_infty (a b d : ℂ)
    (h : a * d - b * 0 ≠ 0) :
    fractionalLinearOfCoefficients a b 0 d h ∞ = ∞ := by
  simp [fractionalLinearOfCoefficients_infty]

/-- Only a vanishing denominator can send a finite point to infinity. -/
theorem fractionalLinearOfCoefficients_eq_infty_iff (a b c d z : ℂ)
    (h : a * d - b * c ≠ 0) :
    fractionalLinearOfCoefficients a b c d h z = ∞ ↔ c * z + d = 0 := by
  rw [fractionalLinearOfCoefficients_coe]
  split_ifs <;> simp_all

/-- The extended coefficient map is bijective. -/
theorem fractionalLinearOfCoefficients_bijective (a b c d : ℂ)
    (h : a * d - b * c ≠ 0) :
    Function.Bijective (fractionalLinearOfCoefficients a b c d h) :=
  (fractionalLinearOfCoefficients a b c d h).bijective

/-- Every invertible-matrix action is bijective. -/
theorem fractionalLinear_bijective (g : FractionalLinearMatrix) :
    Function.Bijective (fractionalLinear g) := (fractionalLinear g).bijective

/-- The identity matrix induces the identity transformation. -/
theorem fractionalLinear_one : fractionalLinear 1 = Equiv.refl ExtendedComplex :=
  fractionalLinearHom.map_one

/-- The composition law holds at all extended points. -/
theorem fractionalLinear_mul (g h : FractionalLinearMatrix) (z : ExtendedComplex) :
    fractionalLinear (g * h) z = fractionalLinear g (fractionalLinear h z) :=
  mul_smul g h z

/-- The inverse matrix induces the inverse transformation. -/
theorem fractionalLinear_inv (g : FractionalLinearMatrix) :
    fractionalLinear g⁻¹ = (fractionalLinear g).symm :=
  fractionalLinearHom.map_inv g

/-- The inverse law holds at finite points, poles and infinity alike. -/
theorem fractionalLinear_inv_apply (g : FractionalLinearMatrix) (z : ExtendedComplex) :
    fractionalLinear g⁻¹ (fractionalLinear g z) = z := by
  exact inv_smul_smul g z

/-- The group of actual fractional linear permutations. -/
noncomputable def fractionalLinearGroup : Subgroup (Equiv.Perm ExtendedComplex) :=
  fractionalLinearHom.range

/-- Every member of the transformation group has an invertible-matrix representative. -/
theorem mem_fractionalLinearGroup (f : Equiv.Perm ExtendedComplex) :
    f ∈ fractionalLinearGroup ↔ ∃ g : FractionalLinearMatrix, fractionalLinear g = f := Iff.rfl

/-- An arbitrary matrix representative also has the explicit four-coefficient form. -/
theorem fractionalLinear_matrix_coefficients (g : FractionalLinearMatrix) :
    ∃ h : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0,
      fractionalLinearOfCoefficients (g 0 0) (g 0 1) (g 1 0) (g 1 1) h =
        fractionalLinear g := by
  refine ⟨by simpa [Matrix.det_fin_two] using g.det_ne_zero, ?_⟩
  apply congrArg fractionalLinear
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The transformation group consists exactly of the nonsingular coefficient maps. -/
theorem mem_fractionalLinearGroup_iff_coefficients (f : Equiv.Perm ExtendedComplex) :
    f ∈ fractionalLinearGroup ↔ ∃ a b c d : ℂ, ∃ h : a * d - b * c ≠ 0,
      fractionalLinearOfCoefficients a b c d h = f := by
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨h, heq⟩ := fractionalLinear_matrix_coefficients g
    exact ⟨g 0 0, g 0 1, g 1 0, g 1 1, h, heq.trans hg⟩
  · rintro ⟨a, b, c, d, h, rfl⟩
    exact ⟨coefficientMatrix a b c d h, rfl⟩

/-- Reciprocal transformation with zero and infinity interchanged. -/
noncomputable def reciprocal : Equiv.Perm ExtendedComplex :=
  fractionalLinearOfCoefficients 0 1 1 0 (by norm_num)

/-- The reciprocal transformation maps zero to infinity. -/
theorem reciprocal_zero : reciprocal (0 : ℂ) = ∞ := by
  simp [reciprocal, fractionalLinearOfCoefficients_coe]

/-- The reciprocal transformation maps infinity to zero. -/
theorem reciprocal_infty : reciprocal ∞ = (0 : ℂ) := by
  simp [reciprocal, fractionalLinearOfCoefficients_infty]

/-- The reciprocal transformation agrees with inversion away from zero. -/
theorem reciprocal_coe (z : ℂ) (hz : z ≠ 0) :
    reciprocal z = (z⁻¹ : ℂ) := by
  simp [reciprocal, fractionalLinearOfCoefficients_coe, hz]

/-- Reciprocal is continuous in the one-point topology, including both exceptional points. -/
theorem continuous_reciprocal : Continuous reciprocal := by
  rw [continuous_iff_continuousAt]
  intro z
  induction z using OnePoint.rec with
  | infty =>
    apply OnePoint.continuousAt_infty'.mpr
    rw [reciprocal_infty]
    have ht : Tendsto (fun z : ℂ => ((z⁻¹ : ℂ) : ExtendedComplex))
        (coclosedCompact ℂ) (𝓝 ((0 : ℂ) : ExtendedComplex)) := by
      apply OnePoint.continuous_coe.continuousAt.tendsto.comp
      simpa [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
        using (Filter.tendsto_inv₀_cobounded : Tendsto (Inv.inv : ℂ → ℂ) _ _)
    apply ht.congr'
    have hn : ∀ᶠ z : ℂ in coclosedCompact ℂ, z ≠ 0 := by
      simpa [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
        using (Bornology.eventually_ne_cobounded (0 : ℂ))
    filter_upwards [hn] with z hz
    exact (reciprocal_coe z hz).symm
  | coe z =>
    apply OnePoint.continuousAt_coe.mpr
    by_cases hz : z = 0
    · subst z
      have ht : Tendsto (fun z : ℂ => ((z⁻¹ : ℂ) : ExtendedComplex))
          (𝓝[≠] 0) (𝓝 (∞ : ExtendedComplex)) := by
        apply OnePoint.tendsto_coe_infty.comp
        simpa [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
          using (Filter.tendsto_inv₀_nhdsNE_zero : Tendsto (Inv.inv : ℂ → ℂ) _ _)
      have hw : ContinuousWithinAt (fun z : ℂ => reciprocal z) ({0}ᶜ) 0 := by
        rw [ContinuousWithinAt, reciprocal_zero]
        apply ht.congr'
        filter_upwards [self_mem_nhdsWithin] with z hz
        exact (reciprocal_coe z hz).symm
      have hu := hw.insert
      simpa [Function.comp_def] using hu
    · have ht : ContinuousAt (fun z : ℂ => ((z⁻¹ : ℂ) : ExtendedComplex)) z :=
        OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hz)
      apply ht.congr
      filter_upwards [eventually_ne_nhds hz] with w hw
      exact (reciprocal_coe w hw).symm

/-- An invertible complex affine map extended to a homeomorphism fixing infinity. -/
noncomputable def affineHomeomorph (a b : ℂ) (ha : a ≠ 0) :
    ExtendedComplex ≃ₜ ExtendedComplex :=
  ((Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight b)).onePointCongr

/-- The extended affine homeomorphism has the expected finite-point formula. -/
theorem affineHomeomorph_coe (a b z : ℂ) (ha : a ≠ 0) :
    affineHomeomorph a b ha z = (a * z + b : ℂ) := rfl

/-- The extended affine homeomorphism fixes infinity. -/
theorem affineHomeomorph_infty (a b : ℂ) (ha : a ≠ 0) :
    affineHomeomorph a b ha ∞ = ∞ := rfl

/-- continuity, proved by an affine–reciprocal–affine decomposition. -/
theorem continuous_fractionalLinearOfCoefficients (a b c d : ℂ)
    (h : a * d - b * c ≠ 0) : Continuous (fractionalLinearOfCoefficients a b c d h) := by
  by_cases hc : c = 0
  · subst c
    have ha : a ≠ 0 := by intro ha; simp [ha] at h
    have hd : d ≠ 0 := by intro hd; simp [hd] at h
    let f := affineHomeomorph (a / d) (b / d) (div_ne_zero ha hd)
    apply f.continuous.congr
    intro z
    induction z using OnePoint.rec with
    | infty => simp [f, fractionalLinearOfCoefficients_infty, affineHomeomorph_infty]
    | coe z =>
      rw [fractionalLinearOfCoefficients_affine, affineHomeomorph_coe]
      congr 1
      field_simp
  · have hα : -(a * d - b * c) / c ^ 2 ≠ 0 :=
      div_ne_zero (neg_ne_zero.mpr h) (pow_ne_zero 2 hc)
    let f := affineHomeomorph 1 (d / c) one_ne_zero
    let k := affineHomeomorph (-(a * d - b * c) / c ^ 2) (a / c) hα
    have hcont : Continuous (fun z => k (reciprocal (f z))) :=
      k.continuous.comp (continuous_reciprocal.comp f.continuous)
    apply hcont.congr
    intro z
    induction z using OnePoint.rec with
    | infty =>
      simp [f, k, affineHomeomorph_infty, reciprocal_infty,
        affineHomeomorph_coe, fractionalLinearOfCoefficients_infty, hc]
    | coe z =>
      by_cases hz : c * z + d = 0
      · have hp := (denominator_eq_zero_iff c d z hc).mp hz
        subst z
        have hzero : -d / c + d / c = 0 := by ring
        simp only [f, k, affineHomeomorph_coe, one_mul, hzero, reciprocal_zero,
          affineHomeomorph_infty, fractionalLinearOfCoefficients_coe, hz, ite_true]
      · have hden : z + d / c ≠ 0 := by
          rw [ne_eq, add_eq_zero_iff_eq_neg]
          simpa [neg_div] using (denominator_eq_zero_iff c d z hc).not.mp hz
        simp only [f, k, affineHomeomorph_coe, one_mul, reciprocal_coe _ hden,
          fractionalLinearOfCoefficients_coe, ite_eq_right hz]
        congr 1
        field_simp
        ring

/-- continuity of every invertible-matrix action. -/
theorem continuous_fractionalLinear (g : FractionalLinearMatrix) :
    Continuous (fractionalLinear g) := by
  obtain ⟨h, heq⟩ := fractionalLinear_matrix_coefficients g
  rw [← heq]
  exact continuous_fractionalLinearOfCoefficients _ _ _ _ h

/-- The fractional linear bijection and its inverse are continuous. -/
noncomputable def fractionalLinearHomeomorph (g : FractionalLinearMatrix) :
    ExtendedComplex ≃ₜ ExtendedComplex where
  __ := fractionalLinear g
  continuous_toFun := continuous_fractionalLinear g
  continuous_invFun := by
    change Continuous ((fractionalLinear g).symm : ExtendedComplex → ExtendedComplex)
    rw [← fractionalLinear_inv]
    exact continuous_fractionalLinear g⁻¹

end LowDimensionalTopology.Geometry.Mobius
