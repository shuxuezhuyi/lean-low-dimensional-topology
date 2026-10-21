/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Mobius.MatrixRepresentation
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# The standard forms

The parameter is nonzero. Its value `1` denotes a translation, while every other
value denotes the corresponding multiplication map.
-/

@[expose] public section

open scoped OnePoint

namespace LowDimensionalTopology.Geometry.Mobius.Classification

/-- A matrix representative of the standard form with a nonzero complex parameter. -/
noncomputable def standardMatrix (k : ℂˣ) : Mobius.FractionalLinearMatrix :=
  Mobius.coefficientMatrix k (if (k : ℂ) = 1 then 1 else 0) 0 1 (by simp)

/-- `m₁` is translation by one; `m_k` otherwise multiplies by `k`. -/
noncomputable def standardForm (k : ℂˣ) : Equiv.Perm Mobius.ExtendedComplex :=
  Mobius.fractionalLinear (standardMatrix k)

/-- The standard form as an element of the fractional linear transformation group. -/
noncomputable def standardElement (k : ℂˣ) : Mobius.fractionalLinearGroup :=
  Mobius.matrixProjection (standardMatrix k)

theorem standardElement_apply (k : ℂˣ) (z : Mobius.ExtendedComplex) :
    (standardElement k : Equiv.Perm Mobius.ExtendedComplex) z = standardForm k z := rfl

/-- The finite-point formulas in the definition of the standard forms. -/
theorem standardForm_coe (k : ℂˣ) (z : ℂ) :
    standardForm k z = ((if (k : ℂ) = 1 then z + 1 else (k : ℂ) * z) : ℂ) := by
  change Mobius.fractionalLinear (standardMatrix k) z = _
  rw [Mobius.fractionalLinear_coe]
  by_cases hk : (k : ℂ) = 1 <;>
    simp [standardMatrix, Mobius.coefficientMatrix, hk]

/-- Every standard form fixes infinity. -/
theorem standardForm_infty (k : ℂˣ) : standardForm k ∞ = ∞ := by
  change Mobius.fractionalLinear (standardMatrix k) ∞ = _
  rw [Mobius.fractionalLinear_infty]
  simp [standardMatrix, Mobius.coefficientMatrix]

/-- The translation standard form has exactly one fixed point. -/
theorem standardForm_one_fixed_iff (z : Mobius.ExtendedComplex) :
    standardForm 1 z = z ↔ z = ∞ := by
  cases z using OnePoint.rec with
  | infty => simp [standardForm_infty]
  | coe z => simp [standardForm_coe]

/-- The multiplication standard form has exactly the two boundary fixed points. -/
theorem standardForm_fixed_iff (k : ℂˣ) (hk : (k : ℂ) ≠ 1) (z : Mobius.ExtendedComplex) :
    standardForm k z = z ↔ z = ((0 : ℂ) : Mobius.ExtendedComplex) ∨ z = ∞ := by
  cases z using OnePoint.rec with
  | infty => simp [standardForm_infty]
  | coe z =>
    simp only [standardForm_coe, ite_eq_right hk, OnePoint.coe_eq_coe, OnePoint.coe_ne_infty,
      or_false]
    constructor
    · intro h
      by_contra hz
      exact hk ((mul_eq_right₀ hz).mp h)
    · rintro rfl
      simp

/-- None of the chosen standard forms is the identity transformation. -/
theorem standardForm_ne_one (k : ℂˣ) : standardForm k ≠ 1 := by
  intro h
  by_cases hk : (k : ℂ) = 1
  · have h0 := congrArg (fun f : Equiv.Perm Mobius.ExtendedComplex => f (0 : ℂ)) h
    simp [standardForm_coe, hk] at h0
  · have h1 := congrArg (fun f : Equiv.Perm Mobius.ExtendedComplex => f (1 : ℂ)) h
    simp [standardForm_coe, hk] at h1

/-- equation, evaluated on the standard matrix representative. -/
theorem standardMatrix_squaredTrace (k : ℂˣ) :
    Mobius.matrixSquaredTrace (standardMatrix k) = (k : ℂ) + (k : ℂ)⁻¹ + 2 := by
  simp [Mobius.matrixSquaredTrace, standardMatrix, Mobius.coefficientMatrix, Matrix.trace_fin_two,
    Matrix.det_fin_two]
  field_simp [k.ne_zero]
  ring

/-- The finite fixed points satisfy the quadratic equation of the matrix action. -/
theorem fractionalLinear_fixed_coe_iff (g : Mobius.FractionalLinearMatrix) (z : ℂ) :
    Mobius.fractionalLinear g z = z ↔
      g 1 0 * (z * z) + (g 1 1 - g 0 0) * z + (-g 0 1) = 0 := by
  simpa [Mobius.fractionalLinear_apply, Matrix.GeneralLinearGroup.fixpointPolynomial, sq, sub_eq_add_neg] using
    (Matrix.GeneralLinearGroup.fixpointPolynomial_aeval_eq_zero_iff (g := g) (c := z)).symm

/-- Every nonidentity fractional linear map has a fixed set with one or two points.
The two displayed points are allowed to coincide. -/
theorem fractionalLinear_fixedPoint_pair (g : Mobius.FractionalLinearMatrix)
    (hg : Mobius.fractionalLinear g ≠ 1) :
    ∃ a b : Mobius.ExtendedComplex, ∀ z : Mobius.ExtendedComplex,
      Mobius.fractionalLinear g z = z ↔ z = a ∨ z = b := by
  classical
  by_cases hc : g 1 0 = 0
  · have hd : g 1 1 ≠ 0 := by
      have hdet := g.det_ne_zero
      rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
      exact (mul_ne_zero_iff.mp hdet).2
    by_cases ha : g 0 0 = g 1 1
    · have hb : g 0 1 ≠ 0 := by
        intro hb
        apply hg
        apply Equiv.ext
        intro z
        cases z using OnePoint.rec with
        | infty => simp [Mobius.fractionalLinear_infty, hc]
        | coe z => simp [Mobius.fractionalLinear_coe, hc, ha, hb, hd, mul_comm]
      refine ⟨∞, ∞, ?_⟩
      intro z
      cases z using OnePoint.rec with
      | infty => simp [Mobius.fractionalLinear_infty, hc]
      | coe z => simp [fractionalLinear_fixed_coe_iff, hc, ha, hb]
    · have hda : g 1 1 - g 0 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
      refine ⟨∞, ((g 0 1 / (g 1 1 - g 0 0) : ℂ) : Mobius.ExtendedComplex), ?_⟩
      intro z
      cases z using OnePoint.rec with
      | infty => simp [Mobius.fractionalLinear_infty, hc]
      | coe z =>
        simp only [fractionalLinear_fixed_coe_iff, hc, zero_mul, zero_add,
          OnePoint.coe_ne_infty, OnePoint.coe_eq_coe, false_or]
        rw [add_neg_eq_zero, mul_comm, ← eq_div_iff hda]
  · obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq
      (discrim (g 1 0) (g 1 1 - g 0 0) (-g 0 1)) (n := 2) (by decide)
    have hdisc : discrim (g 1 0) (g 1 1 - g 0 0) (-g 0 1) = s * s := by
      simpa only [sq] using hs.symm
    refine ⟨(((-(g 1 1 - g 0 0) + s) / (2 * g 1 0) : ℂ) : Mobius.ExtendedComplex),
      (((-(g 1 1 - g 0 0) - s) / (2 * g 1 0) : ℂ) : Mobius.ExtendedComplex), ?_⟩
    intro z
    cases z using OnePoint.rec with
    | infty => simp [Mobius.fractionalLinear_infty, hc]
    | coe z =>
      rw [fractionalLinear_fixed_coe_iff]
      simpa only [OnePoint.coe_eq_coe] using quadratic_eq_zero_iff hc hdisc z

/-- A nonidentity transformation has exactly one or exactly two fixed points. -/
theorem nonidentity_fixedPoint_dichotomy (f : Mobius.fractionalLinearGroup) (hf : f ≠ 1) :
    (∃ a : Mobius.ExtendedComplex, ∀ z : Mobius.ExtendedComplex,
      (f : Equiv.Perm Mobius.ExtendedComplex) z = z ↔ z = a) ∨
    (∃ a b : Mobius.ExtendedComplex, a ≠ b ∧ ∀ z : Mobius.ExtendedComplex,
      (f : Equiv.Perm Mobius.ExtendedComplex) z = z ↔ z = a ∨ z = b) := by
  obtain ⟨g, rfl⟩ := Mobius.matrixProjection_surjective f
  have hg : Mobius.fractionalLinear g ≠ 1 := by
    intro h
    exact hf (Subtype.ext h)
  obtain ⟨a, b, hab⟩ := fractionalLinear_fixedPoint_pair g hg
  by_cases h : a = b
  · exact Or.inl ⟨a, fun z => by simpa [Mobius.matrixProjection_apply, h] using hab z⟩
  · exact Or.inr ⟨a, b, h, fun z => by simpa [Mobius.matrixProjection_apply] using hab z⟩

/-- equation, for the descended transformation invariant. -/
theorem standardElement_squaredTrace (k : ℂˣ) :
    Mobius.fractionalSquaredTrace (standardElement k) = (k : ℂ) + (k : ℂ)⁻¹ + 2 := by
  rw [standardElement, Mobius.fractionalSquaredTrace_projection, standardMatrix_squaredTrace]

/-- A fractional linear change of coordinates sends any prescribed point to infinity. -/
theorem exists_send_to_infty (a : Mobius.ExtendedComplex) :
    ∃ q : Mobius.fractionalLinearGroup, (q : Equiv.Perm Mobius.ExtendedComplex) a = ∞ := by
  cases a using OnePoint.rec with
  | infty => exact ⟨1, rfl⟩
  | coe a =>
    refine ⟨Mobius.matrixProjection (Mobius.coefficientMatrix 0 1 1 (-a) (by simp)), ?_⟩
    rw [Mobius.matrixProjection_apply, Mobius.fractionalLinear_coe]
    simp [Mobius.coefficientMatrix]

/-- The action of a matrix fixing infinity is an affine map on finite points. -/
theorem fractionalLinear_affine_of_lowerLeft_zero (g : Mobius.FractionalLinearMatrix)
    (hc : g 1 0 = 0) (z : ℂ) :
    Mobius.fractionalLinear g z = ((g 0 0 / g 1 1 * z + g 0 1 / g 1 1 : ℂ) : Mobius.ExtendedComplex) := by
  have hd : g 1 1 ≠ 0 := by
    have hdet := g.det_ne_zero
    rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
    exact (mul_ne_zero_iff.mp hdet).2
  rw [Mobius.fractionalLinear_coe]
  simp [hc, hd, add_div, div_mul_eq_mul_div]

/-- The affine coordinate functions retain their exact complex parameters. -/
noncomputable def affineMatrix (a : ℂˣ) (b : ℂ) : Mobius.FractionalLinearMatrix :=
  Mobius.coefficientMatrix a b 0 1 (by simp)

theorem affineMatrix_coe (a : ℂˣ) (b z : ℂ) :
    Mobius.fractionalLinear (affineMatrix a b) z = (((a : ℂ) * z + b : ℂ) : Mobius.ExtendedComplex) := by
  rw [Mobius.fractionalLinear_coe]
  simp [affineMatrix, Mobius.coefficientMatrix]

theorem affineMatrix_infty (a : ℂˣ) (b : ℂ) :
    Mobius.fractionalLinear (affineMatrix a b) ∞ = ∞ := by
  rw [Mobius.fractionalLinear_infty]
  simp [affineMatrix, Mobius.coefficientMatrix]

/-- A nonidentity affine transformation is conjugate to a standard form. -/
theorem affine_conjugate_standard (a : ℂˣ) (b : ℂ)
    (hf : Mobius.matrixProjection (affineMatrix a b) ≠ 1) :
    ∃ k : ℂˣ, IsConj (Mobius.matrixProjection (affineMatrix a b)) (standardElement k) := by
  classical
  by_cases ha : (a : ℂ) = 1
  · have hb : b ≠ 0 := by
      intro hb
      apply hf
      apply Subtype.ext
      apply Equiv.ext
      intro z
      cases z using OnePoint.rec with
      | infty => simp [Mobius.matrixProjection_apply, affineMatrix_infty]
      | coe z => simp [Mobius.matrixProjection_apply, affineMatrix_coe, ha, hb]
    refine ⟨1, isConj_iff.mpr ?_⟩
    refine ⟨Mobius.matrixProjection (affineMatrix (Units.mk0 b hb)⁻¹ 0), ?_⟩
    apply (mul_inv_eq_iff_eq_mul).mpr
    apply Subtype.ext
    apply Equiv.ext
    intro z
    change Mobius.fractionalLinear (affineMatrix (Units.mk0 b hb)⁻¹ 0)
      (Mobius.fractionalLinear (affineMatrix a b) z) =
      standardForm 1 (Mobius.fractionalLinear (affineMatrix (Units.mk0 b hb)⁻¹ 0) z)
    cases z using OnePoint.rec with
    | infty => simp [affineMatrix_infty, standardForm_infty]
    | coe z => simp [affineMatrix_coe, standardForm_coe, ha, hb, mul_add]
  · refine ⟨a, isConj_iff.mpr ?_⟩
    let t : ℂ := b / ((a : ℂ) - 1)
    refine ⟨Mobius.matrixProjection (affineMatrix 1 t), ?_⟩
    apply (mul_inv_eq_iff_eq_mul).mpr
    apply Subtype.ext
    apply Equiv.ext
    intro z
    change Mobius.fractionalLinear (affineMatrix 1 t) (Mobius.fractionalLinear (affineMatrix a b) z) =
      standardForm a (Mobius.fractionalLinear (affineMatrix 1 t) z)
    cases z using OnePoint.rec with
    | infty => simp [affineMatrix_infty, standardForm_infty]
    | coe z =>
      simp only [affineMatrix_coe, Units.val_one, one_mul, standardForm_coe, ite_eq_right ha,
        OnePoint.coe_eq_coe]
      dsimp [t]
      field_simp [sub_ne_zero.mpr ha]
      ring

/-- A fractional linear transformation fixing infinity has an affine representative. -/
theorem affine_of_fixes_infty (f : Mobius.fractionalLinearGroup)
    (hfix : (f : Equiv.Perm Mobius.ExtendedComplex) ∞ = ∞) :
    ∃ a : ℂˣ, ∃ b : ℂ, f = Mobius.matrixProjection (affineMatrix a b) := by
  obtain ⟨g, rfl⟩ := Mobius.matrixProjection_surjective f
  have hc : g 1 0 = 0 := OnePoint.smul_infty_eq_self_iff.mp hfix
  have hdet := g.det_ne_zero
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hdet
  obtain ⟨ha, hd⟩ := mul_ne_zero_iff.mp hdet
  refine ⟨Units.mk0 (g 0 0 / g 1 1) (div_ne_zero ha hd), g 0 1 / g 1 1, ?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro z
  cases z using OnePoint.rec with
  | infty =>
    simp only [Mobius.matrixProjection_apply, affineMatrix_infty]
    simp [Mobius.fractionalLinear_infty, hc]
  | coe z =>
    simpa only [Mobius.matrixProjection_apply, affineMatrix_coe, Units.val_mk0] using
      fractionalLinear_affine_of_lowerLeft_zero g hc z

/-- Every nonidentity fractional linear transformation has a standard form. -/
theorem nonidentity_conjugate_standard (f : Mobius.fractionalLinearGroup) (hf : f ≠ 1) :
    ∃ k : ℂˣ, IsConj f (standardElement k) := by
  classical
  obtain ⟨g, hg⟩ := Mobius.matrixProjection_surjective f
  have hg' : Mobius.fractionalLinear g ≠ 1 := by
    intro h
    apply hf
    rw [← hg]
    exact Subtype.ext h
  obtain ⟨a, b, hab⟩ := fractionalLinear_fixedPoint_pair g hg'
  have hfixed : (f : Equiv.Perm Mobius.ExtendedComplex) a = a := by
    rw [← hg, Mobius.matrixProjection_apply]
    exact (hab a).mpr (Or.inl rfl)
  obtain ⟨q, hqa⟩ := exists_send_to_infty a
  let h : Mobius.fractionalLinearGroup := q * f * q⁻¹
  have hconj : IsConj f h := isConj_iff.mpr ⟨q, rfl⟩
  have hne : h ≠ 1 := by
    intro he
    exact hf (isConj_one_left.mp (he ▸ hconj))
  have hqinv : ((q⁻¹ : Mobius.fractionalLinearGroup) : Equiv.Perm Mobius.ExtendedComplex) ∞ = a := by
    change (q : Equiv.Perm Mobius.ExtendedComplex).symm ∞ = a
    rw [← hqa]
    exact Equiv.symm_apply_apply _ _
  have hinfty : (h : Equiv.Perm Mobius.ExtendedComplex) ∞ = ∞ := by
    change (q : Equiv.Perm Mobius.ExtendedComplex)
      ((f : Equiv.Perm Mobius.ExtendedComplex) (((q⁻¹ : Mobius.fractionalLinearGroup) : Equiv.Perm
        Mobius.ExtendedComplex) ∞)) = ∞
    rw [hqinv, hfixed, hqa]
  obtain ⟨α, β, he⟩ := affine_of_fixes_infty h hinfty
  obtain ⟨k, hk⟩ := affine_conjugate_standard α β (by rw [← he]; exact hne)
  exact ⟨k, hconj.trans (he ▸ hk)⟩

/-- Inverting the nonzero standard parameter preserves the conjugacy class. -/
theorem standard_conjugate_inverse (k : ℂˣ) :
    IsConj (standardElement k) (standardElement k⁻¹) := by
  classical
  by_cases hk : (k : ℂ) = 1
  · have h : k = 1 := Units.ext hk
    subst k
    exact IsConj.refl _
  · let q : Mobius.FractionalLinearMatrix := Mobius.coefficientMatrix 0 1 1 0 (by simp)
    apply isConj_iff.mpr
    refine ⟨Mobius.matrixProjection q, ?_⟩
    apply mul_inv_eq_iff_eq_mul.mpr
    change Mobius.matrixProjection q * Mobius.matrixProjection (standardMatrix k) =
      Mobius.matrixProjection (standardMatrix k⁻¹) * Mobius.matrixProjection q
    rw [← map_mul, ← map_mul]
    apply (Mobius.matrixProjection_eq_iff _ _).mpr
    refine ⟨k⁻¹, ?_⟩
    apply Units.ext
    rw [Mobius.generalLinear_mul_scalar_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [q, standardMatrix, Mobius.coefficientMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        hk, k.ne_zero]

/-- Equal standard-form trace parameters agree up to inversion. -/
theorem standardTrace_eq_iff (p q : ℂˣ) :
    (p : ℂ) + (p : ℂ)⁻¹ + 2 = (q : ℂ) + (q : ℂ)⁻¹ + 2 ↔
      p = q ∨ p = q⁻¹ := by
  constructor
  · intro h
    have he : ((p : ℂ) - (q : ℂ)) * ((p : ℂ) - (q : ℂ)⁻¹) = 0 := by
      calc
        _ = (p : ℂ) * (((p : ℂ) + (p : ℂ)⁻¹ + 2) -
          ((q : ℂ) + (q : ℂ)⁻¹ + 2)) := by
            field_simp [p.ne_zero, q.ne_zero]
            ring
        _ = 0 := by rw [h]; ring
    rcases mul_eq_zero.mp he with h | h
    · exact Or.inl (Units.ext (sub_eq_zero.mp h))
    · exact Or.inr (Units.ext (by simpa only [Units.val_inv_eq_inv_val] using sub_eq_zero.mp h))
  · rintro (rfl | rfl) <;> simp [add_comm]

/-- Conjugate fractional linear transformations have the same squared trace. -/
theorem squaredTrace_eq_of_isConj {f g : Mobius.fractionalLinearGroup} (h : IsConj f g) :
    Mobius.fractionalSquaredTrace f = Mobius.fractionalSquaredTrace g := by
  obtain ⟨q, rfl⟩ := isConj_iff.mp h
  exact (Mobius.fractionalSquaredTrace_conjugation f q).symm

/-- squared trace completely classifies nonidentity conjugacy classes. -/
theorem fractional_isConj_iff_squaredTrace_eq (f g : Mobius.fractionalLinearGroup) (hf : f ≠ 1) (hg : g ≠ 1) :
    IsConj f g ↔ Mobius.fractionalSquaredTrace f = Mobius.fractionalSquaredTrace g := by
  constructor
  · exact squaredTrace_eq_of_isConj
  · intro he
    obtain ⟨p, hp⟩ := nonidentity_conjugate_standard f hf
    obtain ⟨q, hq⟩ := nonidentity_conjugate_standard g hg
    have htrace : (p : ℂ) + (p : ℂ)⁻¹ + 2 = (q : ℂ) + (q : ℂ)⁻¹ + 2 := by
      rw [← standardElement_squaredTrace, ← standardElement_squaredTrace,
        ← squaredTrace_eq_of_isConj hp, ← squaredTrace_eq_of_isConj hq, he]
    rcases (standardTrace_eq_iff p q).mp htrace with h | h
    · subst q
      exact hp.trans hq.symm
    · subst p
      exact hp.trans ((standard_conjugate_inverse q).symm.trans hq.symm)

/-- The square of a standard form is the identity exactly at parameter minus one. -/
theorem standardElement_sq_eq_one_iff (k : ℂˣ) :
    standardElement k ^ 2 = 1 ↔ (k : ℂ) = -1 := by
  classical
  constructor
  · intro h
    by_cases hk : (k : ℂ) = 1
    · have h0 := congrArg
        (fun f : Mobius.fractionalLinearGroup => (f : Equiv.Perm Mobius.ExtendedComplex) (0 : ℂ)) h
      change standardForm k (standardForm k (0 : ℂ)) = (0 : ℂ) at h0
      simp [standardForm_coe, hk] at h0
    · have h1 := congrArg
        (fun f : Mobius.fractionalLinearGroup => (f : Equiv.Perm Mobius.ExtendedComplex) (1 : ℂ)) h
      change standardForm k (standardForm k (1 : ℂ)) = (1 : ℂ) at h1
      have hkk : (k : ℂ) * (k : ℂ) = 1 := by
        simpa [standardForm_coe, hk] using h1
      have he : ((k : ℂ) - 1) * ((k : ℂ) + 1) = 0 := by
        linear_combination hkk
      rcases mul_eq_zero.mp he with he | he
      · exact False.elim (hk (sub_eq_zero.mp he))
      · exact eq_neg_of_add_eq_zero_left he
  · intro hk
    apply Subtype.ext
    apply Equiv.ext
    intro z
    change standardForm k (standardForm k z) = z
    cases z using OnePoint.rec with
    | infty => simp [standardForm_infty]
    | coe z => norm_num [standardForm_coe, hk]

/-- Zero squared trace is equivalent to the standard parameter minus one. -/
theorem standardElement_squaredTrace_eq_zero_iff (k : ℂˣ) :
    Mobius.fractionalSquaredTrace (standardElement k) = 0 ↔ (k : ℂ) = -1 := by
  rw [standardElement_squaredTrace]
  constructor
  · intro h
    have he : ((k : ℂ) + 1) ^ 2 = 0 := by
      calc
        _ = (k : ℂ) * ((k : ℂ) + (k : ℂ)⁻¹ + 2) := by
          field_simp [k.ne_zero]
          ring
        _ = 0 := by rw [h]; simp
    exact eq_neg_of_add_eq_zero_left (sq_eq_zero_iff.mp he)
  · intro hk
    norm_num [hk]

/-- A nonidentity transformation has order two exactly at squared trace zero. -/
theorem orderOf_eq_two_iff_squaredTrace_eq_zero (f : Mobius.fractionalLinearGroup) (hf : f ≠ 1) :
    orderOf f = 2 ↔ Mobius.fractionalSquaredTrace f = 0 := by
  obtain ⟨k, hk⟩ := nonidentity_conjugate_standard f hf
  have hpow : f ^ 2 = 1 ↔ standardElement k ^ 2 = 1 := by
    constructor
    · intro h
      exact isConj_one_right.mp (h ▸ hk.pow 2)
    · intro h
      exact isConj_one_left.mp (h ▸ hk.pow 2)
  rw [orderOf_eq_prime_iff, and_iff_left hf, hpow, standardElement_sq_eq_one_iff,
    squaredTrace_eq_of_isConj hk, standardElement_squaredTrace_eq_zero_iff]

/-- A determinant-one representative used only to define the sign-independent commutator trace. -/
noncomputable def specialRepresentative (f : Mobius.fractionalLinearGroup) : Auxiliary.Algebra.SpecialLinear2 :=
  Classical.choose (Mobius.specialLinearProjection_surjective f)

theorem specialRepresentative_projection (f : Mobius.fractionalLinearGroup) :
    Mobius.specialLinearProjection (specialRepresentative f) = f :=
  Classical.choose_spec (Mobius.specialLinearProjection_surjective f)

/-- The group commutator in the stated order. -/
noncomputable def commutatorElement (f g : Mobius.fractionalLinearGroup) : Mobius.fractionalLinearGroup := f * g *
    f⁻¹ * g⁻¹

/-- The commutator of determinant-one representatives in the same order. -/
def specialCommutator (A B : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.SpecialLinear2 :=
  A * B * A⁻¹ * B⁻¹

/-- The trace, rather than squared trace, of the determinant-one commutator. -/
noncomputable def commutatorTrace (f g : Mobius.fractionalLinearGroup) : ℂ :=
  ((specialCommutator (specialRepresentative f) (specialRepresentative g) :
    Auxiliary.Algebra.ComplexMatrix2)).trace

section Signs

local instance : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩

theorem specialCommutator_neg_left (A B : Auxiliary.Algebra.SpecialLinear2) :
    specialCommutator (-A) B = specialCommutator A B := by
  simp [specialCommutator]

theorem specialCommutator_neg_right (A B : Auxiliary.Algebra.SpecialLinear2) :
    specialCommutator A (-B) = specialCommutator A B := by
  simp [specialCommutator]

/-- Changing the sign of either lift does not change its commutator. -/
theorem specialCommutator_eq_left (A B C : Auxiliary.Algebra.SpecialLinear2)
    (h : Mobius.specialLinearProjection A = Mobius.specialLinearProjection C) :
    specialCommutator A B = specialCommutator C B := by
  rcases (Mobius.specialLinear_same_projection_iff A C).mp h with h | h
  · rw [show C = A from Subtype.ext h]
  · rw [show C = -A from Subtype.ext h, specialCommutator_neg_left]

theorem specialCommutator_eq_right (A B D : Auxiliary.Algebra.SpecialLinear2)
    (h : Mobius.specialLinearProjection B = Mobius.specialLinearProjection D) :
    specialCommutator A B = specialCommutator A D := by
  rcases (Mobius.specialLinear_same_projection_iff B D).mp h with h | h
  · rw [show D = B from Subtype.ext h]
  · rw [show D = -B from Subtype.ext h, specialCommutator_neg_right]

end Signs

/-- The matrix commutator represents the transformation commutator. -/
theorem specialCommutator_projection (A B : Auxiliary.Algebra.SpecialLinear2) :
    Mobius.specialLinearProjection (specialCommutator A B) =
      commutatorElement (Mobius.specialLinearProjection A) (Mobius.specialLinearProjection B) := by
  simp [specialCommutator, commutatorElement]

/-- any determinant-one representatives give the same commutator trace. -/
theorem commutatorTrace_representatives (f g : Mobius.fractionalLinearGroup)
    (A B : Auxiliary.Algebra.SpecialLinear2) (hA : Mobius.specialLinearProjection A = f)
    (hB : Mobius.specialLinearProjection B = g) :
    commutatorTrace f g = (specialCommutator A B : Auxiliary.Algebra.ComplexMatrix2).trace := by
  unfold commutatorTrace
  rw [specialCommutator_eq_left _ _ A ((specialRepresentative_projection f).trans hA.symm),
    specialCommutator_eq_right _ _ B ((specialRepresentative_projection g).trans hB.symm)]

/-- The square of the commutator trace is the squared trace of the commutator transformation. -/
theorem commutatorTrace_sq (f g : Mobius.fractionalLinearGroup) :
    commutatorTrace f g ^ 2 = Mobius.fractionalSquaredTrace (commutatorElement f g) := by
  unfold commutatorTrace
  rw [← Mobius.fractionalSquaredTrace_specialLinearProjection, specialCommutator_projection,
    specialRepresentative_projection, specialRepresentative_projection]

/-- Simultaneous conjugation conjugates the determinant-one matrix commutator. -/
theorem specialCommutator_conjugation (A B C : Auxiliary.Algebra.SpecialLinear2) :
    specialCommutator (C * A * C⁻¹) (C * B * C⁻¹) = C * specialCommutator A B * C⁻¹ := by
  simp [specialCommutator, mul_assoc]

/-- The trace of a determinant-one matrix is invariant under conjugation. -/
theorem specialLinear_trace_conjugation (A C : Auxiliary.Algebra.SpecialLinear2) :
    (C * A * C⁻¹ : Auxiliary.Algebra.SpecialLinear2).val.trace = A.val.trace := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [Matrix.trace_mul_cycle]
  change ((C⁻¹ * C * A : Auxiliary.Algebra.SpecialLinear2) : Auxiliary.Algebra.ComplexMatrix2).trace = _
  simp

/-- The commutator trace is invariant under simultaneous conjugation. -/
theorem commutatorTrace_conjugation (f g q : Mobius.fractionalLinearGroup) :
    commutatorTrace (q * f * q⁻¹) (q * g * q⁻¹) = commutatorTrace f g := by
  let A := specialRepresentative f
  let B := specialRepresentative g
  let C := specialRepresentative q
  rw [commutatorTrace_representatives _ _ (C * A * C⁻¹) (C * B * C⁻¹)
    (by simp [A, C, specialRepresentative_projection])
    (by simp [B, C, specialRepresentative_projection]),
    specialCommutator_conjugation, specialLinear_trace_conjugation]
  rfl

/-- The triangular determinant-one computation used in the fixed-point trace criterion. -/
theorem specialCommutator_trace_triangular (A B : Auxiliary.Algebra.SpecialLinear2)
    (hc : A 1 0 = 0) :
    (specialCommutator A B : Auxiliary.Algebra.ComplexMatrix2).trace =
      2 + (A 0 1) ^ 2 * (B 1 0) ^ 2 +
        A 0 1 * (A 0 0 - A 1 1) * B 1 0 * (B 0 0 - B 1 1) -
        (A 0 0 - A 1 1) ^ 2 * B 1 0 * B 0 1 := by
  have hA := A.det_coe
  have hB := B.det_coe
  rw [Matrix.det_fin_two, hc, mul_zero, sub_zero] at hA
  rw [Matrix.det_fin_two] at hB
  simp only [specialCommutator, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, Matrix.trace_fin_two,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, hc, zero_mul, mul_zero, add_zero, zero_add,
    neg_zero]
  linear_combination 2 * (B 0 0 * B 1 1 - B 0 1 * B 1 0) * hA + 2 * hB

/-- The entries of any determinant-one representative of a standard form share one nonzero scalar. -/
theorem specialStandard_lift (k : ℂˣ) :
    ∃ A : Auxiliary.Algebra.SpecialLinear2, Mobius.specialLinearProjection A = standardElement k ∧
      ∃ u : ℂˣ, A 0 0 = (u : ℂ) * (k : ℂ) ∧
        A 0 1 = (u : ℂ) * (if (k : ℂ) = 1 then 1 else 0) ∧
        A 1 0 = 0 ∧ A 1 1 = (u : ℂ) := by
  obtain ⟨A, hA⟩ := Mobius.specialLinearProjection_surjective (standardElement k)
  have hp : Mobius.matrixProjection (standardMatrix k) =
      Mobius.matrixProjection (Matrix.SpecialLinearGroup.toGL A) := hA.symm
  obtain ⟨u, hu⟩ := (Mobius.matrixProjection_eq_iff _ _).mp hp
  have hv := congrArg (fun g : Mobius.FractionalLinearMatrix => (g : Auxiliary.Algebra.ComplexMatrix2)) hu
  rw [Mobius.generalLinear_mul_scalar_val] at hv
  refine ⟨A, hA, u, ?_, ?_, ?_, ?_⟩
  · simpa [standardMatrix, Mobius.coefficientMatrix] using (congrArg (fun M => M 0 0) hv).symm
  · simpa [standardMatrix, Mobius.coefficientMatrix] using (congrArg (fun M => M 0 1) hv).symm
  · simpa [standardMatrix, Mobius.coefficientMatrix] using (congrArg (fun M => M 1 0) hv).symm
  · simpa [standardMatrix, Mobius.coefficientMatrix] using (congrArg (fun M => M 1 1) hv).symm

/-- The assertion that two transformations have a common boundary fixed point. -/
def CommonFixedPoint (f g : Mobius.fractionalLinearGroup) : Prop :=
  ∃ z : Mobius.ExtendedComplex, (f : Equiv.Perm Mobius.ExtendedComplex) z = z ∧
    (g : Equiv.Perm Mobius.ExtendedComplex) z = z

theorem exists_fixedPoint (f : Mobius.fractionalLinearGroup) :
    ∃ z : Mobius.ExtendedComplex, (f : Equiv.Perm Mobius.ExtendedComplex) z = z := by
  by_cases hf : f = 1
  · exact ⟨∞, by simp [hf]⟩
  · rcases nonidentity_fixedPoint_dichotomy f hf with ⟨a, ha⟩ | ⟨a, b, _, hab⟩
    · exact ⟨a, (ha a).mpr rfl⟩
    · exact ⟨a, (hab a).mpr (Or.inl rfl)⟩

theorem commonFixedPoint_conjugation (f g q : Mobius.fractionalLinearGroup) :
    CommonFixedPoint (q * f * q⁻¹) (q * g * q⁻¹) ↔ CommonFixedPoint f g := by
  constructor
  · rintro ⟨z, hf, hg⟩
    refine ⟨(q : Equiv.Perm Mobius.ExtendedComplex).symm z, ?_, ?_⟩
    · have h := congrArg (fun w => (q : Equiv.Perm Mobius.ExtendedComplex).symm w) hf
      change (q : Equiv.Perm Mobius.ExtendedComplex).symm
        ((q : Equiv.Perm Mobius.ExtendedComplex) ((f : Equiv.Perm Mobius.ExtendedComplex)
          ((q : Equiv.Perm Mobius.ExtendedComplex).symm z))) = _ at h
      simpa only [Equiv.symm_apply_apply] using h
    · have h := congrArg (fun w => (q : Equiv.Perm Mobius.ExtendedComplex).symm w) hg
      change (q : Equiv.Perm Mobius.ExtendedComplex).symm
        ((q : Equiv.Perm Mobius.ExtendedComplex) ((g : Equiv.Perm Mobius.ExtendedComplex)
          ((q : Equiv.Perm Mobius.ExtendedComplex).symm z))) = _ at h
      simpa only [Equiv.symm_apply_apply] using h
  · rintro ⟨z, hf, hg⟩
    refine ⟨(q : Equiv.Perm Mobius.ExtendedComplex) z, ?_, ?_⟩
    · change (q : Equiv.Perm Mobius.ExtendedComplex) ((f : Equiv.Perm Mobius.ExtendedComplex)
        ((q : Equiv.Perm Mobius.ExtendedComplex).symm ((q : Equiv.Perm Mobius.ExtendedComplex) z))) = _
      rw [Equiv.symm_apply_apply, hf]
    · change (q : Equiv.Perm Mobius.ExtendedComplex) ((g : Equiv.Perm Mobius.ExtendedComplex)
        ((q : Equiv.Perm Mobius.ExtendedComplex).symm ((q : Equiv.Perm Mobius.ExtendedComplex) z))) = _
      rw [Equiv.symm_apply_apply, hg]

theorem specialLinear_fixes_infty_iff (A : Auxiliary.Algebra.SpecialLinear2) :
    (Mobius.specialLinearProjection A : Equiv.Perm Mobius.ExtendedComplex) ∞ = ∞ ↔ A 1 0 = 0 :=
  OnePoint.smul_infty_eq_self_iff

theorem specialLinear_fixes_zero_iff (A : Auxiliary.Algebra.SpecialLinear2) :
    (Mobius.specialLinearProjection A : Equiv.Perm Mobius.ExtendedComplex) (0 : ℂ) = (0 : ℂ) ↔ A 0 1 = 0 := by
  change Mobius.fractionalLinear (Matrix.SpecialLinearGroup.toGL A) (0 : ℂ) = (0 : ℂ) ↔ _
  rw [fractionalLinear_fixed_coe_iff]
  simp

/-- The common fixed-point test with one transformation in standard form. -/
theorem commonFixedPoint_standard (k : ℂˣ) (B : Auxiliary.Algebra.SpecialLinear2) :
    CommonFixedPoint (standardElement k) (Mobius.specialLinearProjection B) ↔
      if (k : ℂ) = 1 then B 1 0 = 0 else B 0 1 = 0 ∨ B 1 0 = 0 := by
  classical
  by_cases hk : (k : ℂ) = 1
  · have hk' : k = 1 := Units.ext hk
    subst k
    simp only [Units.val_one, ite_true]
    constructor
    · rintro ⟨z, hz, hB⟩
      have hz' := (standardForm_one_fixed_iff z).mp hz
      subst z
      exact (specialLinear_fixes_infty_iff B).mp hB
    · intro hB
      exact ⟨∞, standardForm_infty 1, (specialLinear_fixes_infty_iff B).mpr hB⟩
  · rw [ite_eq_right hk]
    constructor
    · rintro ⟨z, hz, hB⟩
      rcases (standardForm_fixed_iff k hk z).mp hz with hz | hz
      · subst z
        exact Or.inl ((specialLinear_fixes_zero_iff B).mp hB)
      · subst z
        exact Or.inr ((specialLinear_fixes_infty_iff B).mp hB)
    · rintro (hB | hB)
      · exact ⟨(0 : ℂ), (standardForm_fixed_iff k hk (0 : ℂ)).mpr (Or.inl rfl),
          (specialLinear_fixes_zero_iff B).mpr hB⟩
      · exact ⟨∞, standardForm_infty k, (specialLinear_fixes_infty_iff B).mpr hB⟩

/-- The commutator trace detects a common fixed point when the first map is standard. -/
theorem commutatorTrace_standard_eq_two_iff (k : ℂˣ) (B : Auxiliary.Algebra.SpecialLinear2) :
    commutatorTrace (standardElement k) (Mobius.specialLinearProjection B) = 2 ↔
      CommonFixedPoint (standardElement k) (Mobius.specialLinearProjection B) := by
  classical
  rw [commonFixedPoint_standard]
  obtain ⟨A, hA, u, ha, hb, hc, hd⟩ := specialStandard_lift k
  rw [commutatorTrace_representatives _ _ A B hA rfl,
    specialCommutator_trace_triangular A B hc]
  by_cases hk : (k : ℂ) = 1
  · simp [hk, ha, hb, hd, u.ne_zero]
  · have had : (u : ℂ) * (k : ℂ) - (u : ℂ) ≠ 0 := by
      intro he
      apply hk
      apply mul_left_cancel₀ u.ne_zero
      simpa using sub_eq_zero.mp he
    simp [hk, ha, hb, hd, had, mul_eq_zero, or_comm]

/-- The trace-two commutator criterion. -/
theorem fractional_commonFixedPoint_iff_commutatorTrace_eq_two (f g : Mobius.fractionalLinearGroup) :
    CommonFixedPoint f g ↔ commutatorTrace f g = 2 := by
  classical
  by_cases hf : f = 1
  · subst f
    obtain ⟨z, hz⟩ := exists_fixedPoint g
    have hcommon : CommonFixedPoint 1 g := ⟨z, rfl, hz⟩
    have htrace : commutatorTrace 1 g = 2 := by
      rw [commutatorTrace_representatives _ _ 1 (specialRepresentative g)
        (by simp) (specialRepresentative_projection g)]
      simp [specialCommutator]
    exact iff_of_true hcommon htrace
  · obtain ⟨k, hk⟩ := nonidentity_conjugate_standard f hf
    obtain ⟨q, hq⟩ := isConj_iff.mp hk
    obtain ⟨B, hB⟩ := Mobius.specialLinearProjection_surjective (q * g * q⁻¹)
    rw [← commonFixedPoint_conjugation f g q, hq, ← hB,
      ← commutatorTrace_standard_eq_two_iff, hB, ← hq, commutatorTrace_conjugation]

/-- Equality of boundary fixed-point sets. -/
def SameFixedPoints (f g : Mobius.fractionalLinearGroup) : Prop :=
  ∀ z : Mobius.ExtendedComplex, (f : Equiv.Perm Mobius.ExtendedComplex) z = z ↔
    (g : Equiv.Perm Mobius.ExtendedComplex) z = z

theorem conjugate_fixed_iff (f q : Mobius.fractionalLinearGroup) (z : Mobius.ExtendedComplex) :
    ((q * f * q⁻¹ : Mobius.fractionalLinearGroup) : Equiv.Perm Mobius.ExtendedComplex) z = z ↔
      (f : Equiv.Perm Mobius.ExtendedComplex) ((q : Equiv.Perm Mobius.ExtendedComplex).symm z) =
        (q : Equiv.Perm Mobius.ExtendedComplex).symm z := by
  constructor
  · intro h
    have h' := congrArg (fun w => (q : Equiv.Perm Mobius.ExtendedComplex).symm w) h
    change (q : Equiv.Perm Mobius.ExtendedComplex).symm
      ((q : Equiv.Perm Mobius.ExtendedComplex) ((f : Equiv.Perm Mobius.ExtendedComplex)
        ((q : Equiv.Perm Mobius.ExtendedComplex).symm z))) = _ at h'
    simpa only [Equiv.symm_apply_apply] using h'
  · intro h
    change (q : Equiv.Perm Mobius.ExtendedComplex) ((f : Equiv.Perm Mobius.ExtendedComplex)
      ((q : Equiv.Perm Mobius.ExtendedComplex).symm z)) = z
    rw [h]
    exact Equiv.apply_symm_apply _ _

theorem sameFixedPoints_conjugation (f g q : Mobius.fractionalLinearGroup) :
    SameFixedPoints (q * f * q⁻¹) (q * g * q⁻¹) ↔ SameFixedPoints f g := by
  constructor
  · intro h z
    have hz := h ((q : Equiv.Perm Mobius.ExtendedComplex) z)
    rw [conjugate_fixed_iff, conjugate_fixed_iff] at hz
    simpa only [Equiv.symm_apply_apply] using hz
  · intro h z
    rw [conjugate_fixed_iff, conjugate_fixed_iff]
    exact h _

/-- A standard form commutes with any transformation having the same boundary fixed set. -/
theorem standard_commute_of_sameFixedPoints (k : ℂˣ) (B : Auxiliary.Algebra.SpecialLinear2)
    (h : SameFixedPoints (standardElement k) (Mobius.specialLinearProjection B)) :
    Commute (standardElement k) (Mobius.specialLinearProjection B) := by
  classical
  have hc : B 1 0 = 0 :=
    (specialLinear_fixes_infty_iff B).mp ((h ∞).mp (standardForm_infty k))
  by_cases hk : (k : ℂ) = 1
  · have ha : B 0 0 = B 1 1 := by
      by_contra ha
      have hd : B 1 1 - B 0 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
      let z : ℂ := B 0 1 / (B 1 1 - B 0 0)
      have hz : (Mobius.specialLinearProjection B : Equiv.Perm Mobius.ExtendedComplex) z = z := by
        change Mobius.fractionalLinear (Matrix.SpecialLinearGroup.toGL B) z = z
        rw [fractionalLinear_fixed_coe_iff]
        simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, hc, zero_mul, zero_add]
        dsimp [z]
        field_simp
        ring
      have hk' : k = 1 := Units.ext hk
      have hz' := (h z).mpr hz
      rw [hk'] at hz'
      exact (OnePoint.coe_ne_infty z) ((standardForm_one_fixed_iff z).mp hz')
    change Mobius.matrixProjection (standardMatrix k) * Mobius.matrixProjection (Matrix.SpecialLinearGroup.toGL B) =
      Mobius.matrixProjection (Matrix.SpecialLinearGroup.toGL B) * Mobius.matrixProjection (standardMatrix k)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [standardMatrix, Mobius.coefficientMatrix, Matrix.mul_apply, Fin.sum_univ_two, hk, hc, ha, add_comm]
  · have hb : B 0 1 = 0 := (specialLinear_fixes_zero_iff B).mp
      ((h (0 : ℂ)).mp ((standardForm_fixed_iff k hk (0 : ℂ)).mpr (Or.inl rfl)))
    change Mobius.matrixProjection (standardMatrix k) * Mobius.matrixProjection (Matrix.SpecialLinearGroup.toGL B) =
      Mobius.matrixProjection (Matrix.SpecialLinearGroup.toGL B) * Mobius.matrixProjection (standardMatrix k)
    rw [← map_mul, ← map_mul]
    congr 1
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [standardMatrix, Mobius.coefficientMatrix, Matrix.mul_apply, Fin.sum_univ_two, hk, hc, hb,
        mul_comm]

/-- Nonidentity transformations with the same boundary fixed set commute. -/
theorem commute_of_sameFixedPoints (f g : Mobius.fractionalLinearGroup) (hf : f ≠ 1)
    (h : SameFixedPoints f g) : Commute f g := by
  obtain ⟨k, hk⟩ := nonidentity_conjugate_standard f hf
  obtain ⟨q, hq⟩ := isConj_iff.mp hk
  obtain ⟨B, hB⟩ := Mobius.specialLinearProjection_surjective (q * g * q⁻¹)
  have hsame := (sameFixedPoints_conjugation f g q).mpr h
  rw [hq, ← hB] at hsame
  have hcomm := (standard_commute_of_sameFixedPoints k B hsame).eq
  rw [hB, ← hq] at hcomm
  have he := congrArg (fun x : Mobius.fractionalLinearGroup => q⁻¹ * x * q) hcomm
  change f * g = g * f
  simpa [mul_assoc] using he

/-- A commuting map fixing one point of a one- or two-point fixed set fixes the whole set. -/
theorem fixedPoints_subset_of_commute (f g : Mobius.fractionalLinearGroup) (hf : f ≠ 1)
    (hcomm : Commute f g) (hcommon : CommonFixedPoint f g) :
    ∀ x : Mobius.ExtendedComplex, (f : Equiv.Perm Mobius.ExtendedComplex) x = x →
      (g : Equiv.Perm Mobius.ExtendedComplex) x = x := by
  obtain ⟨p, hfp, hgp⟩ := hcommon
  have hpair : ∃ a b : Mobius.ExtendedComplex, ∀ z : Mobius.ExtendedComplex,
      (f : Equiv.Perm Mobius.ExtendedComplex) z = z ↔ z = a ∨ z = b := by
    rcases nonidentity_fixedPoint_dichotomy f hf with ⟨a, ha⟩ | ⟨a, b, _, hab⟩
    · exact ⟨a, a, fun z => by simpa using ha z⟩
    · exact ⟨a, b, hab⟩
  obtain ⟨a, b, hab⟩ := hpair
  intro x hx
  by_cases hxp : x = p
  · simpa [hxp] using hgp
  have hfgx : (f : Equiv.Perm Mobius.ExtendedComplex) ((g : Equiv.Perm Mobius.ExtendedComplex) x) =
      (g : Equiv.Perm Mobius.ExtendedComplex) x := by
    have he := congrArg (fun h : Mobius.fractionalLinearGroup => (h : Equiv.Perm Mobius.ExtendedComplex) x) hcomm.eq
    change (f : Equiv.Perm Mobius.ExtendedComplex) ((g : Equiv.Perm Mobius.ExtendedComplex) x) =
      (g : Equiv.Perm Mobius.ExtendedComplex) ((f : Equiv.Perm Mobius.ExtendedComplex) x) at he
    rwa [hx] at he
  have hnot : (g : Equiv.Perm Mobius.ExtendedComplex) x ≠ p := by
    intro he
    apply hxp
    exact (g : Equiv.Perm Mobius.ExtendedComplex).injective (he.trans hgp.symm)
  rcases (hab p).mp hfp with hp | hp <;>
    rcases (hab x).mp hx with hx' | hx' <;>
    rcases (hab ((g : Equiv.Perm Mobius.ExtendedComplex) x)).mp hfgx with hg | hg <;> aesop

/-- Commuting nonidentity maps sharing one fixed point have identical boundary fixed sets. -/
theorem sameFixedPoints_of_commute (f g : Mobius.fractionalLinearGroup) (hf : f ≠ 1) (hg : g ≠ 1)
    (hcommon : CommonFixedPoint f g) (hcomm : Commute f g) : SameFixedPoints f g := by
  intro z
  refine ⟨fixedPoints_subset_of_commute f g hf hcomm hcommon z,
    fixedPoints_subset_of_commute g f hg hcomm.symm ?_ z⟩
  obtain ⟨p, hfp, hgp⟩ := hcommon
  exact ⟨p, hgp, hfp⟩

theorem standardElement_ne_one (k : ℂˣ) : standardElement k ≠ 1 := by
  intro h
  apply standardForm_ne_one k
  exact congrArg Subtype.val h

/-- A conjugate of the translation standard form has a unique boundary fixed point. -/
theorem uniqueFixedPoint_of_conjugate_translation (f : Mobius.fractionalLinearGroup)
    (h : IsConj f (standardElement 1)) :
    ∃ a : Mobius.ExtendedComplex, ∀ z : Mobius.ExtendedComplex,
      (f : Equiv.Perm Mobius.ExtendedComplex) z = z ↔ z = a := by
  obtain ⟨q, hq⟩ := isConj_iff.mp h
  refine ⟨(q : Equiv.Perm Mobius.ExtendedComplex).symm ∞, fun z => ?_⟩
  have he := conjugate_fixed_iff f q ((q : Equiv.Perm Mobius.ExtendedComplex) z)
  rw [hq] at he
  have he' : (f : Equiv.Perm Mobius.ExtendedComplex) z = z ↔
      standardForm 1 ((q : Equiv.Perm Mobius.ExtendedComplex) z) = (q : Equiv.Perm Mobius.ExtendedComplex) z := by
    simpa only [Equiv.symm_apply_apply, standardElement_apply] using he.symm
  rw [he', standardForm_one_fixed_iff]
  constructor
  · intro hz
    rw [← hz]
    exact (Equiv.symm_apply_apply _ _).symm
  · intro hz
    rw [hz]
    exact Equiv.apply_symm_apply _ _

/-- With the parabolic conclusion in its equivalent standard-form form. -/
theorem commutator_standard_dichotomy (f g : Mobius.fractionalLinearGroup) (hf : f ≠ 1) (hg : g ≠ 1)
    (hcommon : CommonFixedPoint f g) :
    (commutatorElement f g = 1 ∧ SameFixedPoints f g) ∨
    (IsConj (commutatorElement f g) (standardElement 1) ∧
      commutatorElement f g ≠ 1 ∧ ¬ SameFixedPoints f g) := by
  classical
  by_cases hc : commutatorElement f g = 1
  · left
    refine ⟨hc, sameFixedPoints_of_commute f g hf hg hcommon ?_⟩
    change f * g = g * f
    have he : f * g * f⁻¹ = g := (mul_inv_eq_iff_eq_mul.mp hc)
    exact (mul_inv_eq_iff_eq_mul.mp he)
  · right
    have htrace := (fractional_commonFixedPoint_iff_commutatorTrace_eq_two f g).mp hcommon
    have hsq : Mobius.fractionalSquaredTrace (commutatorElement f g) = 4 := by
      rw [← commutatorTrace_sq, htrace]
      norm_num
    refine ⟨(fractional_isConj_iff_squaredTrace_eq _ _ hc (standardElement_ne_one 1)).mpr ?_, hc, ?_⟩
    · rw [hsq, standardElement_squaredTrace]
      norm_num
    · intro hsame
      have hcomm := (commute_of_sameFixedPoints f g hf hsame).eq
      apply hc
      unfold commutatorElement
      rw [hcomm]
      simp [mul_assoc]

/-- A nonidentity map with exactly one boundary fixed point. -/
def BoundaryParabolic (f : Mobius.fractionalLinearGroup) : Prop :=
  f ≠ 1 ∧ ∃ a : Mobius.ExtendedComplex, ∀ z : Mobius.ExtendedComplex,
    (f : Equiv.Perm Mobius.ExtendedComplex) z = z ↔ z = a

/-- The identity or parabolic commutator alternatives. -/
theorem fractional_commonFixedPoint_commutator_dichotomy (f g : Mobius.fractionalLinearGroup) (hf : f ≠ 1) (hg : g ≠ 1)
    (hcommon : CommonFixedPoint f g) :
    (commutatorElement f g = 1 ∧ Commute f g ∧ SameFixedPoints f g) ∨
    (BoundaryParabolic (commutatorElement f g) ∧ ¬ Commute f g ∧ ¬ SameFixedPoints f g) := by
  rcases commutator_standard_dichotomy f g hf hg hcommon with ⟨hc, hs⟩ | ⟨hp, hc, hs⟩
  · left
    exact ⟨hc, commute_of_sameFixedPoints f g hf hs, hs⟩
  · right
    refine ⟨⟨hc, uniqueFixedPoint_of_conjugate_translation _ hp⟩, ?_, hs⟩
    intro hcomm
    apply hc
    unfold commutatorElement
    rw [hcomm.eq]
    simp [mul_assoc]

/-- The boundary definition of parabolic is equivalent to conjugacy to the translation standard form. -/
theorem boundaryParabolic_iff_conjugate_translation (f : Mobius.fractionalLinearGroup) (hf : f ≠ 1) :
    BoundaryParabolic f ↔ IsConj f (standardElement 1) := by
  constructor
  · rintro ⟨_, a, ha⟩
    obtain ⟨k, hk⟩ := nonidentity_conjugate_standard f hf
    have hk1 : (k : ℂ) = 1 := by
      by_contra hk1
      obtain ⟨q, hq⟩ := isConj_iff.mp hk
      have hfix (z : Mobius.ExtendedComplex) (hz : standardForm k z = z) :
          (f : Equiv.Perm Mobius.ExtendedComplex) ((q : Equiv.Perm Mobius.ExtendedComplex).symm z) =
            (q : Equiv.Perm Mobius.ExtendedComplex).symm z := by
        apply (conjugate_fixed_iff f q z).mp
        simpa only [hq, standardElement_apply] using hz
      have hzero := (ha _).mp (hfix (0 : ℂ)
        ((standardForm_fixed_iff k hk1 (0 : ℂ)).mpr (Or.inl rfl)))
      have hinfty := (ha _).mp (hfix ∞ (standardForm_infty k))
      have he : ((0 : ℂ) : Mobius.ExtendedComplex) = ∞ :=
        (q : Equiv.Perm Mobius.ExtendedComplex).symm.injective (hzero.trans hinfty.symm)
      exact (OnePoint.coe_ne_infty (0 : ℂ)) he
    have hk' : k = 1 := Units.ext hk1
    simpa only [hk'] using hk
  · intro hp
    exact ⟨hf, uniqueFixedPoint_of_conjugate_translation f hp⟩

/-- parabolic transformations have squared trace four, and conversely. -/
theorem fractional_parabolic_iff_squaredTrace_eq_four (f : Mobius.fractionalLinearGroup) (hf : f ≠ 1) :
    BoundaryParabolic f ↔ Mobius.fractionalSquaredTrace f = 4 := by
  rw [boundaryParabolic_iff_conjugate_translation f hf,
    fractional_isConj_iff_squaredTrace_eq f (standardElement 1) hf (standardElement_ne_one 1),
    standardElement_squaredTrace]
  norm_num

/-- The finite-point formulas for every natural power of a standard form. -/
theorem standardElement_pow_coe (k : ℂˣ) (n : ℕ) (z : ℂ) :
    ((standardElement k ^ n : Mobius.fractionalLinearGroup) : Equiv.Perm Mobius.ExtendedComplex) z =
      ((if (k : ℂ) = 1 then z + (n : ℂ) else (k : ℂ) ^ n * z : ℂ) : Mobius.ExtendedComplex) := by
  induction n generalizing z with
  | zero => by_cases hk : (k : ℂ) = 1 <;> simp [hk]
  | succ n ih =>
    rw [pow_succ']
    change standardForm k (((standardElement k ^ n : Mobius.fractionalLinearGroup) :
      Equiv.Perm Mobius.ExtendedComplex) z) = _
    rw [ih, standardForm_coe]
    by_cases hk : (k : ℂ) = 1
    · simp [hk, Nat.cast_add, add_assoc]
    · simp only [ite_eq_right hk, pow_succ]
      congr 1
      ring

theorem standardElement_pow_infty (k : ℂˣ) (n : ℕ) :
    ((standardElement k ^ n : Mobius.fractionalLinearGroup) : Equiv.Perm Mobius.ExtendedComplex) ∞ = ∞ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ']
    change standardForm k (((standardElement k ^ n : Mobius.fractionalLinearGroup) :
      Equiv.Perm Mobius.ExtendedComplex) ∞) = ∞
    rw [ih, standardForm_infty]

/-- The positive powers that become identity are precisely powers of the nontranslation parameter. -/
theorem standardElement_pow_eq_one_iff (k : ℂˣ) (n : ℕ) (hn : 0 < n) :
    standardElement k ^ n = 1 ↔ (k : ℂ) ≠ 1 ∧ (k : ℂ) ^ n = 1 := by
  constructor
  · intro h
    have hk : (k : ℂ) ≠ 1 := by
      intro hk
      have h0 := congrArg
        (fun f : Mobius.fractionalLinearGroup => (f : Equiv.Perm Mobius.ExtendedComplex) (0 : ℂ)) h
      have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
      change ((standardElement k ^ n : Mobius.fractionalLinearGroup) : Equiv.Perm Mobius.ExtendedComplex) (0 : ℂ)
        = (0 : ℂ) at h0
      rw [standardElement_pow_coe] at h0
      simp [hk, hn'] at h0
    refine ⟨hk, ?_⟩
    have h1 := congrArg
      (fun f : Mobius.fractionalLinearGroup => (f : Equiv.Perm Mobius.ExtendedComplex) (1 : ℂ)) h
    change ((standardElement k ^ n : Mobius.fractionalLinearGroup) : Equiv.Perm Mobius.ExtendedComplex) (1 : ℂ) =
      (1 : ℂ) at h1
    rw [standardElement_pow_coe] at h1
    simpa [hk] using h1
  · rintro ⟨hk, hp⟩
    apply Subtype.ext
    apply Equiv.ext
    intro z
    change ((standardElement k ^ n : Mobius.fractionalLinearGroup) : Equiv.Perm Mobius.ExtendedComplex) z = z
    cases z using OnePoint.rec with
    | infty => exact standardElement_pow_infty k n
    | coe z => rw [standardElement_pow_coe]; simp [hk, hp]

/-- A nonidentity map of finite order has a standard parameter of unit modulus. -/
theorem finite_order_conjugate_unit_standard (f : Mobius.fractionalLinearGroup) (hf : f ≠ 1)
    (hfin : IsOfFinOrder f) :
    ∃ k : ℂˣ, (k : ℂ) ≠ 1 ∧ ‖(k : ℂ)‖ = 1 ∧ IsConj f (standardElement k) := by
  obtain ⟨k, hk⟩ := nonidentity_conjugate_standard f hf
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have hp : standardElement k ^ n = 1 := isConj_one_right.mp (hpow ▸ hk.pow n)
  obtain ⟨hk1, hkn⟩ := (standardElement_pow_eq_one_iff k n hn).mp hp
  exact ⟨k, hk1, Complex.norm_eq_one_of_pow_eq_one hkn hn.ne', hk⟩

/-- The order of an element is invariant under conjugation. -/
theorem orderOf_eq_of_isConj {f g : Mobius.fractionalLinearGroup} (h : IsConj f g) :
    orderOf f = orderOf g := by
  apply orderOf_eq_orderOf_iff.mpr
  intro n
  exact ⟨fun hf => isConj_one_right.mp (hf ▸ h.pow n),
    fun hg => isConj_one_left.mp (hg ▸ h.pow n)⟩

/-- For a multiplication standard form, its exact order is the order of its complex parameter. -/
theorem orderOf_standardElement (k : ℂˣ) (hk : (k : ℂ) ≠ 1) :
    orderOf (standardElement k) = orderOf (k : ℂ) := by
  apply orderOf_eq_orderOf_iff.mpr
  intro n
  by_cases hn : n = 0
  · simp [hn]
  · exact ⟨fun h => ((standardElement_pow_eq_one_iff k n (Nat.pos_of_ne_zero hn)).mp h).2,
      fun h => (standardElement_pow_eq_one_iff k n (Nat.pos_of_ne_zero hn)).mpr ⟨hk, h⟩⟩

/-- An exact finite order supplies a primitive complex root as the standard parameter. -/
theorem exact_order_standard_primitive (f : Mobius.fractionalLinearGroup) (hf : f ≠ 1)
    (n : ℕ) (hn : 0 < n) (ho : orderOf f = n) :
    ∃ k : ℂˣ, (k : ℂ) ≠ 1 ∧ IsConj f (standardElement k) ∧ IsPrimitiveRoot (k : ℂ) n := by
  obtain ⟨k, hk⟩ := nonidentity_conjugate_standard f hf
  have hp : standardElement k ^ n = 1 := by
    apply isConj_one_right.mp
    have he : f ^ n = 1 := by rw [← ho]; exact pow_orderOf_eq_one f
    exact he ▸ hk.pow n
  obtain ⟨hk1, _⟩ := (standardElement_pow_eq_one_iff k n hn).mp hp
  have horder : n = orderOf (k : ℂ) :=
    ho.symm.trans ((orderOf_eq_of_isConj hk).trans (orderOf_standardElement k hk1))
  refine ⟨k, hk1, hk, ?_⟩
  rw [horder]
  exact IsPrimitiveRoot.orderOf _

/-- The standard parameter of an exact finite order has a coprime rational rotation angle. -/
theorem exact_order_standard_angle (f : Mobius.fractionalLinearGroup) (hf : f ≠ 1)
    (n : ℕ) (hn : 0 < n) (ho : orderOf f = n) :
    ∃ k : ℂˣ, ∃ m < n, m.Coprime n ∧ IsConj f (standardElement k) ∧
      Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) / n)) = (k : ℂ) := by
  obtain ⟨k, _, hk, hp⟩ := exact_order_standard_primitive f hf n hn ho
  obtain ⟨m, hm, hmn, he⟩ := (Complex.isPrimitiveRoot_iff (k : ℂ) n hn.ne').mp hp
  exact ⟨k, m, hm, hmn, hk, he⟩

/-- The trigonometric squared-trace formula for a standard rotation parameter. -/
theorem standardElement_squaredTrace_exp (k : ℂˣ) (θ : ℂ)
    (hk : (k : ℂ) = Complex.exp (θ * Complex.I)) :
    Mobius.fractionalSquaredTrace (standardElement k) = 4 * Complex.cos (θ / 2) ^ 2 := by
  rw [standardElement_squaredTrace, hk, ← Complex.exp_neg,
    show -(θ * Complex.I) = (-θ) * Complex.I by ring,
    Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  have hc := Complex.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hc
  linear_combination 2 * hc

/-- The real rotation-angle formula for squared trace. -/
theorem standardElement_squaredTrace_real_angle (k : ℂˣ) (θ : ℝ)
    (hk : (k : ℂ) = Complex.exp ((θ : ℂ) * Complex.I)) :
    Mobius.fractionalSquaredTrace (standardElement k) = ((4 * Real.cos (θ / 2) ^ 2 : ℝ) : ℂ) := by
  rw [standardElement_squaredTrace_exp k θ hk]
  push_cast
  rfl

/-- The exact finite-order rotation parameter and its cosine squared-trace formula. -/
theorem exact_order_angle_squaredTrace (f : Mobius.fractionalLinearGroup) (hf : f ≠ 1)
    (n : ℕ) (hn : 0 < n) (ho : orderOf f = n) :
    ∃ k : ℂˣ, ∃ m < n, m.Coprime n ∧ IsConj f (standardElement k) ∧
      Complex.exp (2 * Real.pi * Complex.I * ((m : ℂ) / n)) = (k : ℂ) ∧
      Mobius.fractionalSquaredTrace f = ((4 * Real.cos (Real.pi * m / n) ^ 2 : ℝ) : ℂ) := by
  obtain ⟨k, m, hm, hmn, hk, he⟩ := exact_order_standard_angle f hf n hn ho
  refine ⟨k, m, hm, hmn, hk, he, ?_⟩
  rw [squaredTrace_eq_of_isConj hk]
  have hparam : (k : ℂ) =
      Complex.exp (((2 * Real.pi * (m : ℝ) / n : ℝ) : ℂ) * Complex.I) := by
    rw [← he]
    congr 1
    push_cast
    ring
  rw [standardElement_squaredTrace_real_angle k _ hparam]
  rw [show (2 * Real.pi * (m : ℝ) / n) / 2 = Real.pi * m / n by ring]

/-- A cosine-square maximum on an interval symmetric about the midpoint of `[0, π]`. -/
theorem cosine_sq_interval_bound (a x : ℝ) (ha : 0 ≤ a) (ha2 : a ≤ Real.pi / 2)
    (hax : a ≤ x) (hxa : x ≤ Real.pi - a) :
    Real.cos x ^ 2 ≤ Real.cos a ^ 2 ∧
      (Real.cos x ^ 2 = Real.cos a ^ 2 ↔ x = a ∨ x = Real.pi - a) := by
  have hap : a ≤ Real.pi := by linarith [Real.pi_pos]
  have hx0 : 0 ≤ x := ha.trans hax
  have hxp : x ≤ Real.pi := by linarith
  have hca : 0 ≤ Real.cos a :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) ha2
  have hu : Real.cos x ≤ Real.cos a :=
    Real.cos_le_cos_of_nonneg_of_le_pi ha hxp hax
  have hl : -Real.cos a ≤ Real.cos x := by
    have h := Real.cos_le_cos_of_nonneg_of_le_pi hx0 (by linarith : Real.pi - a ≤ Real.pi) hxa
    simpa only [Real.cos_pi_sub] using h
  constructor
  · have hp := mul_nonneg (sub_nonneg.mpr hu) (by linarith : 0 ≤ Real.cos a + Real.cos x)
    nlinarith
  · constructor
    · intro he
      have hp : (Real.cos x - Real.cos a) * (Real.cos x + Real.cos a) = 0 := by nlinarith
      rcases mul_eq_zero.mp hp with hp | hp
      · exact Or.inl (Real.injOn_cos ⟨hx0, hxp⟩ ⟨ha, hap⟩ (sub_eq_zero.mp hp))
      · right
        apply Real.injOn_cos ⟨hx0, hxp⟩ ⟨by linarith, by linarith⟩
        rw [Real.cos_pi_sub]
        linarith
    · rintro (rfl | rfl) <;> simp [Real.cos_pi_sub]

/-- The cosine-square bound and its two equality indices for an exact finite-order rotation. -/
theorem cosine_sq_nat_angle_bound (n m : ℕ) (hn : 2 ≤ n) (hm1 : 1 ≤ m) (hm : m < n) :
    Real.cos (Real.pi * m / n) ^ 2 ≤ Real.cos (Real.pi / n) ^ 2 ∧
      (Real.cos (Real.pi * m / n) ^ 2 = Real.cos (Real.pi / n) ^ 2 ↔
        m = 1 ∨ m + 1 = n) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn2R : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hm1R : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hmnR : (m : ℝ) + 1 ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
  have ha0 : 0 ≤ Real.pi / n := div_nonneg Real.pi_pos.le hnR.le
  have ha2 : Real.pi / n ≤ Real.pi / 2 := by
    apply (div_le_iff₀ hnR).mpr
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hn2R)]
  have hax : Real.pi / n ≤ Real.pi * m / n := by
    apply div_le_div_of_nonneg_right _ hnR.le
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hm1R)]
  have hxa : Real.pi * m / n ≤ Real.pi - Real.pi / n := by
    apply (le_sub_iff_add_le).mpr
    rw [← add_div]
    apply (div_le_iff₀ hnR).mpr
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hmnR)]
  obtain ⟨hb, he⟩ := cosine_sq_interval_bound (Real.pi / n) (Real.pi * m / n)
    ha0 ha2 hax hxa
  refine ⟨hb, he.trans ?_⟩
  constructor
  · rintro (h | h)
    · left
      have hh : Real.pi * (m : ℝ) = Real.pi := (div_left_inj' hnR.ne').mp h
      have hval : (m : ℝ) = 1 := by
        apply mul_left_cancel₀ Real.pi_ne_zero
        simpa using hh
      exact_mod_cast hval
    · right
      have hangle : Real.pi - Real.pi / n = Real.pi * ((n : ℝ) - 1) / n := by
        field_simp
      rw [hangle] at h
      have hh : Real.pi * (m : ℝ) = Real.pi * ((n : ℝ) - 1) := (div_left_inj' hnR.ne').mp h
      have hval := mul_left_cancel₀ Real.pi_ne_zero hh
      exact_mod_cast (show (m : ℝ) + 1 = n by linarith)
  · rintro (rfl | h)
    · left
      simp
    · right
      have hR : (m : ℝ) + 1 = n := by exact_mod_cast h
      field_simp
      linarith

/-- The last nontrivial rational rotation is the negative first rotation. -/
theorem exp_last_rotation (n : ℕ) (hn : n ≠ 0) :
    Complex.exp (2 * Real.pi * Complex.I * (((n : ℂ) - 1) / n)) =
      Complex.exp (-(2 * Real.pi * Complex.I / n)) := by
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (((n : ℂ) - 1) / n) =
    -(2 * Real.pi * Complex.I / n) + 2 * Real.pi * Complex.I by field_simp; ring,
    Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

/-- The sharp trace bound with its two rotation parameters. -/
theorem fractional_finiteOrder_standard_conjugate_and_squaredTrace_bound_with_equality (f :
    Mobius.fractionalLinearGroup) (hf : f ≠ 1)
    (n : ℕ) (hn : 0 < n) (ho : orderOf f = n) :
    ∃ k : ℂˣ, IsConj f (standardElement k) ∧
      (Mobius.fractionalSquaredTrace f).im = 0 ∧
      (Mobius.fractionalSquaredTrace f).re ≤ 4 * Real.cos (Real.pi / n) ^ 2 ∧
      ((Mobius.fractionalSquaredTrace f).re = 4 * Real.cos (Real.pi / n) ^ 2 ↔
        (k : ℂ) = Complex.exp (2 * Real.pi * Complex.I / n) ∨
        (k : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I / n))) := by
  classical
  have hn2 : 2 ≤ n := by
    by_contra hn2
    have hn1 : n = 1 := by omega
    exact hf (orderOf_eq_one_iff.mp (ho.trans hn1))
  obtain ⟨k, m, hm, hmn, hk, he, htrace⟩ := exact_order_angle_squaredTrace f hf n hn ho
  have hm1 : 1 ≤ m := by
    by_contra hm1
    have hm0 : m = 0 := by omega
    subst m
    have hn1 : n = 1 := by simpa using hmn
    omega
  obtain ⟨hb, heq⟩ := cosine_sq_nat_angle_bound n m hn2 hm1 hm
  have hre : (Mobius.fractionalSquaredTrace f).re = 4 * Real.cos (Real.pi * m / n) ^ 2 := by
    rw [htrace]
    rfl
  refine ⟨k, hk, ?_, ?_, ?_⟩
  · rw [htrace]
    rfl
  · rw [hre]
    linarith
  · constructor
    · intro h
      have hend : m = 1 ∨ m + 1 = n := heq.mp (by rw [hre] at h; linarith)
      rcases hend with h | h
      · left
        rw [← he, h]
        congr 1
        simp only [Nat.cast_one]
        ring
      · right
        have hC : (m : ℂ) = (n : ℂ) - 1 := by
          have hh : (m : ℂ) + 1 = n := by exact_mod_cast h
          linear_combination hh
        rw [← he, hC, exp_last_rotation n hn.ne']
    · rintro (h | h)
      · have hparam : (k : ℂ) =
            Complex.exp (((2 * Real.pi / n : ℝ) : ℂ) * Complex.I) := by
          rw [h]
          congr 1
          push_cast
          ring
        rw [squaredTrace_eq_of_isConj hk, standardElement_squaredTrace_real_angle k _ hparam]
        rw [show (2 * Real.pi / n : ℝ) / 2 = Real.pi / n by ring]
        rfl
      · have hparam : (k : ℂ) =
            Complex.exp (((-(2 * Real.pi / n) : ℝ) : ℂ) * Complex.I) := by
          rw [h]
          congr 1
          push_cast
          ring
        rw [squaredTrace_eq_of_isConj hk, standardElement_squaredTrace_real_angle k _ hparam]
        rw [show (-(2 * Real.pi / n) : ℝ) / 2 = -(Real.pi / n) by ring, Real.cos_neg]
        rfl

end LowDimensionalTopology.Geometry.Mobius.Classification
