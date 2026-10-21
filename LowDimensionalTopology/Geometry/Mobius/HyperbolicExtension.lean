/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc

public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfSpace.UpperHalfSpace
public import LowDimensionalTopology.Geometry.Inversive.Group
public import LowDimensionalTopology.Geometry.Hyperbolic.ModelMaps.PoincareExtension
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfSpace.PathMetric
public import LowDimensionalTopology.Geometry.Inversive.UnitBall.NormalForm
public import LowDimensionalTopology.Geometry.Mobius.Metric.ChordalIsometries
public import LowDimensionalTopology.Geometry.Auxiliary.Algebra.UnitaryMatrix
public import LowDimensionalTopology.Geometry.Mobius.MatrixRepresentation
public import LowDimensionalTopology.Geometry.Mobius.Trace.MobiusInvariants

/-!
# Upper-half-space and ball coordinates

The matrix formula gives a continuous action on the actual quaternion H3.
The Cayley transformation is the specified composition of two real reflections;
it identifies H3 with the actual Euclidean unit ball and agrees with the
stereographic map on the entire boundary. The fixed-j subgroup
is characterized by unitary representatives and normalized Frobenius norm.
The matrix action is the canonical real geometric Poincare extension.
The complete five-way equivalence is proved using the
genuine Cayley ball conjugate and the original sphere-induced chordal metric.
-/

@[expose] public section

namespace LowDimensionalTopology.Geometry.Mobius

noncomputable section

open LowDimensionalTopology.Geometry.Auxiliary.Algebra
open scoped Quaternion ComplexConjugate OnePoint RealInnerProductSpace
open EuclideanGeometry

/-- The real denominator. -/
def poincareDenominator (A : Auxiliary.Algebra.ComplexMatrix2) (z : ℂ) (t : ℝ) : ℝ :=
  ‖A 1 0 * z + A 1 1‖ ^ 2 + ‖A 1 0‖ ^ 2 * t ^ 2

/-- The horizontal complex coordinate. -/
def poincareHorizontal (A : Auxiliary.Algebra.ComplexMatrix2) (z : ℂ) (t : ℝ) : ℂ :=
  ((A 0 0 * z + A 0 1) * conj (A 1 0 * z + A 1 1) +
    A 0 0 * conj (A 1 0) * (t : ℂ) ^ 2) / (poincareDenominator A z t : ℂ)

/-- The vertical coordinate. -/
def poincareHeight (A : Auxiliary.Algebra.ComplexMatrix2) (z : ℂ) (t : ℝ) : ℝ :=
  ‖A.det‖ * t / poincareDenominator A z t

/-- The coordinate expression on quaternion Euclidean three-space. -/
def poincareCoordinate (A : Auxiliary.Algebra.ComplexMatrix2) (q :
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace :=
  Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (poincareHorizontal A
    (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q) (Hyperbolic.QuaternionHalfSpace.quaternionHeight q))
    (poincareHeight A (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q)
      (Hyperbolic.QuaternionHalfSpace.quaternionHeight q))

/-- Nonsingularity prevents the denominator from vanishing at a positive-height point. -/
theorem poincareDenominator_pos (A : Auxiliary.Algebra.ComplexMatrix2) (hA : A.det ≠ 0)
    (z : ℂ) (t : ℝ) (ht : 0 < t) : 0 < poincareDenominator A z t := by
  by_cases hc : A 1 0 = 0
  · have hd : A 1 1 ≠ 0 := by
      intro hd
      apply hA
      simp [Matrix.det_fin_two, hc, hd]
    simpa [poincareDenominator, hc] using sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hd)
  · have hcn := norm_pos_iff.mpr hc
    have hcz := sq_nonneg ‖A 1 0 * z + A 1 1‖
    dsimp [poincareDenominator]
    positivity

theorem poincareHeight_pos (A : Auxiliary.Algebra.ComplexMatrix2) (hA : A.det ≠ 0)
    (z : ℂ) (t : ℝ) (ht : 0 < t) : 0 < poincareHeight A z t :=
  div_pos (mul_pos (norm_pos_iff.mpr hA) ht) (poincareDenominator_pos A hA z t ht)

/-- The formula really lands in H3; the input's positive height is retained. -/
def poincareMatrixMap (A : FractionalLinearMatrix) (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
  Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint (poincareHorizontal (A : Auxiliary.Algebra.ComplexMatrix2)
    (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val) (Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val))
    (poincareHeight (A : Auxiliary.Algebra.ComplexMatrix2) (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal
      q.val) (Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val))
    (poincareHeight_pos (A : Auxiliary.Algebra.ComplexMatrix2) A.det_ne_zero _ _ q.property)

@[simp] theorem poincareMatrixMap_horizontal (A : FractionalLinearMatrix) (q :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    Hyperbolic.QuaternionHalfSpace.quaternionHorizontal (poincareMatrixMap A q).val =
      poincareHorizontal (A : Auxiliary.Algebra.ComplexMatrix2)
        (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val)
        (Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val) :=
  Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint _ _

@[simp] theorem poincareMatrixMap_height (A : FractionalLinearMatrix) (q :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    Hyperbolic.QuaternionHalfSpace.quaternionHeight (poincareMatrixMap A q).val =
      poincareHeight (A : Auxiliary.Algebra.ComplexMatrix2) (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal
        q.val) (Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val) := rfl

/-- Multiplying every coefficient by a scalar changes the denominator by its squared modulus. -/
theorem poincareDenominator_scalar (A : Auxiliary.Algebra.ComplexMatrix2) (c : ℂ) (z : ℂ) (t : ℝ) :
    poincareDenominator (c • A) z t = ‖c‖ ^ 2 * poincareDenominator A z t := by
  have h : (c * A 1 0) * z + c * A 1 1 = c * (A 1 0 * z + A 1 1) := by ring
  simp only [poincareDenominator, Matrix.smul_apply, smul_eq_mul, h, norm_mul, mul_pow]
  ring

/-- The vertical coordinate does not depend on the nonzero scalar matrix representative. -/
theorem poincareHeight_scalar (A : Auxiliary.Algebra.ComplexMatrix2) (c : ℂ) (hc : c ≠ 0) (z : ℂ) (t : ℝ) :
    poincareHeight (c • A) z t = poincareHeight A z t := by
  unfold poincareHeight
  rw [Matrix.det_smul, Fintype.card_fin, norm_mul, norm_pow, poincareDenominator_scalar]
  rw [mul_assoc]
  exact mul_div_mul_left _ _ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hc))

/-- A norm-square cast is exactly the complex product with the conjugate. -/
theorem complex_norm_sq_coe (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * conj z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- The horizontal coordinate is also independent of the nonzero scalar representative. -/
theorem poincareHorizontal_scalar (A : Auxiliary.Algebra.ComplexMatrix2) (c : ℂ) (hc : c ≠ 0) (z : ℂ) (t : ℝ) :
    poincareHorizontal (c • A) z t = poincareHorizontal A z t := by
  have hn :
      ((c * A 0 0) * z + c * A 0 1) * conj ((c * A 1 0) * z + c * A 1 1) +
        (c * A 0 0) * conj (c * A 1 0) * (t : ℂ) ^ 2 =
      (c * conj c) * ((A 0 0 * z + A 0 1) * conj (A 1 0 * z + A 1 1) +
        A 0 0 * conj (A 1 0) * (t : ℂ) ^ 2) := by
    simp only [map_add, map_mul]
    ring
  unfold poincareHorizontal
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [hn, poincareDenominator_scalar, Complex.ofReal_mul, complex_norm_sq_coe]
  exact mul_div_mul_left _ _ (mul_ne_zero hc ((map_ne_zero (starRingEnd ℂ)).2 hc))

/-- The complete quaternion coordinate expression descends under nonzero scalar multiplication. -/
theorem poincareCoordinate_scalar (A : Auxiliary.Algebra.ComplexMatrix2) (c : ℂ) (hc : c ≠ 0)
    (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) : poincareCoordinate (c • A) q = poincareCoordinate
      A q := by
  simp only [poincareCoordinate, poincareHorizontal_scalar A c hc,
    poincareHeight_scalar A c hc]

@[simp] theorem poincareHeight_zero (A : Auxiliary.Algebra.ComplexMatrix2) (z : ℂ) :
    poincareHeight A z 0 = 0 := by simp [poincareHeight]

/-- At each finite nonpole boundary point, the displayed formula is the original complex map. -/
theorem poincareHorizontal_zero (A : Auxiliary.Algebra.ComplexMatrix2) (z : ℂ) (hz : A 1 0 * z + A 1 1 ≠ 0) :
    poincareHorizontal A z 0 = (A 0 0 * z + A 0 1) / (A 1 0 * z + A 1 1) := by
  simp only [poincareHorizontal, poincareDenominator]
  norm_num only [Complex.ofReal_zero, zero_pow, mul_zero, add_zero]
  rw [complex_norm_sq_coe]
  exact mul_div_mul_right _ _ ((map_ne_zero (starRingEnd ℂ)).2 hz)

/-- The raw formula at height zero therefore agrees with the complex fractional expression. -/
theorem poincareCoordinate_boundary (A : Auxiliary.Algebra.ComplexMatrix2) (z : ℂ)
    (hz : A 1 0 * z + A 1 1 ≠ 0) :
    poincareCoordinate A (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z 0) =
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint ((A 0 0 * z + A 0 1) / (A 1 0 * z + A 1 1)) 0 := by
  simp only [poincareCoordinate, Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint,
    Hyperbolic.QuaternionHalfSpace.quaternionHeight_threePoint,
    poincareHorizontal_zero A z hz, poincareHeight_zero]

/-- The real denominator is exactly the norm-square of the quaternion denominator. -/
theorem quaternion_matrix_denominator_normSq (A : Auxiliary.Algebra.ComplexMatrix2) (z : ℂ) (t : ℝ) :
    Quaternion.normSq ((A 1 0 : ℍ) * (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z t : ℍ) + (A 1 1 : ℍ)) =
      poincareDenominator A z t := by
  simp [Quaternion.normSq_def', Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, poincareDenominator,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- Quaternion multiplication explains both the real and imaginary determinant contributions. -/
theorem quaternion_matrix_numerator (A : Auxiliary.Algebra.ComplexMatrix2) (z : ℂ) (t : ℝ) :
    ((A 0 0 : ℍ) * (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z t : ℍ) + (A 0 1 : ℍ)) *
      star ((A 1 0 : ℍ) * (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z t : ℍ) + (A 1 1 : ℍ)) =
    (⟨((A 0 0 * z + A 0 1) * conj (A 1 0 * z + A 1 1) +
          A 0 0 * conj (A 1 0) * (t : ℂ) ^ 2).re,
       ((A 0 0 * z + A 0 1) * conj (A 1 0 * z + A 1 1) +
          A 0 0 * conj (A 1 0) * (t : ℂ) ^ 2).im,
       A.det.re * t, A.det.im * t⟩ : ℍ) := by
  apply Quaternion.ext <;> simp [Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, Matrix.det_fin_two, ←
    Complex.ofReal_pow] <;> ring

/-- The literal quaternion fractional expression, without silently restricting its determinant. -/
def quaternionMatrixExpression (A : Auxiliary.Algebra.ComplexMatrix2) (q :
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) : ℍ :=
  ((A 0 0 : ℍ) * (q : ℍ) + (A 0 1 : ℍ)) *
    ((A 1 0 : ℍ) * (q : ℍ) + (A 1 1 : ℍ))⁻¹

/-- The full quaternion expression has a k coordinate unless the determinant is real. -/
theorem quaternionMatrixExpression_coordinates (A : Auxiliary.Algebra.ComplexMatrix2) (z : ℂ) (t : ℝ) :
    quaternionMatrixExpression A (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z t) =
      (⟨(poincareHorizontal A z t).re, (poincareHorizontal A z t).im,
        A.det.re * t / poincareDenominator A z t,
        A.det.im * t / poincareDenominator A z t⟩ : ℍ) := by
  unfold quaternionMatrixExpression
  rw [Quaternion.inv_def, quaternion_matrix_denominator_normSq,
    Algebra.mul_smul_comm, quaternion_matrix_numerator]
  apply Quaternion.ext <;>
    simp only [Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
      smul_eq_mul, poincareHorizontal, Complex.div_ofReal_re, Complex.div_ofReal_im] <;> ring

/-- For positive real determinant, the source's quaternion expression is exactly. -/
theorem poincareCoordinate_quaternion_positive_det (A : Auxiliary.Algebra.ComplexMatrix2) (r : ℝ)
    (hr : 0 < r) (hdet : A.det = (r : ℂ)) (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    quaternionMatrixExpression A q = (poincareCoordinate A q : ℍ) := by
  rw [← Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates q, quaternionMatrixExpression_coordinates]
  simp only [poincareCoordinate, Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint,
    Hyperbolic.QuaternionHalfSpace.quaternionHeight_threePoint]
  apply Quaternion.ext <;>
    simp [Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, poincareHeight, hdet,
      Real.norm_eq_abs, abs_of_pos hr]

/-- The quaternion denominator is nonzero throughout the genuine upper half-space. -/
theorem quaternionMatrixDenominator_ne_zero (A : Auxiliary.Algebra.ComplexMatrix2) (hA : A.det ≠ 0)
    (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (A 1 0 : ℍ) * (q.val : ℍ) + (A 1 1 : ℍ) ≠ 0 := by
  have hs := quaternion_matrix_denominator_normSq A
    (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val) (Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val)
  rw [Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates] at hs
  intro hz
  rw [hz, map_zero] at hs
  exact (ne_of_gt (poincareDenominator_pos A hA _ _ q.property)) hs.symm

/-- The noncommutative fractional composition identity is valid wherever the inner denominator
is nonzero. No commutativity of the ambient quaternions is assumed. -/
theorem quaternion_fractional_comp (a b c d e f g h w : ℍ) (hy : g * w + h ≠ 0) :
    (a * ((e * w + f) * (g * w + h)⁻¹) + b) *
      (c * ((e * w + f) * (g * w + h)⁻¹) + d)⁻¹ =
    ((a * e + b * g) * w + (a * f + b * h)) *
      ((c * e + d * g) * w + (c * f + d * h))⁻¹ := by
  have hs (α β : ℍ) :
      α * ((e * w + f) * (g * w + h)⁻¹) + β =
      (α * (e * w + f) + β * (g * w + h)) * (g * w + h)⁻¹ := by
    calc
      _ = α * (e * w + f) * (g * w + h)⁻¹ + β := by noncomm_ring
      _ = α * (e * w + f) * (g * w + h)⁻¹ + β * ((g * w + h) * (g * w + h)⁻¹) := by
        rw [mul_inv_cancel₀ hy, mul_one]
      _ = _ := by noncomm_ring
  rw [hs a b, hs c d, mul_inv_rev, inv_inv]
  have hn : a * (e * w + f) + b * (g * w + h) =
      (a * e + b * g) * w + (a * f + b * h) := by noncomm_ring
  have hd : c * (e * w + f) + d * (g * w + h) =
      (c * e + d * g) * w + (c * f + d * h) := by noncomm_ring
  calc
    _ = (a * (e * w + f) + b * (g * w + h)) *
        (((g * w + h)⁻¹ * (g * w + h)) *
          (c * (e * w + f) + d * (g * w + h))⁻¹) := by noncomm_ring
    _ = (a * (e * w + f) + b * (g * w + h)) *
        (c * (e * w + f) + d * (g * w + h))⁻¹ := by
      rw [inv_mul_cancel₀ hy, one_mul]
    _ = _ := by rw [hn, hd]

/-- Determinant-one matrices act on the genuine upper half-space by the displayed formula. -/
def poincareSpecialLinearMap (A : Auxiliary.Algebra.SpecialLinear2) (q :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
  poincareMatrixMap (Matrix.SpecialLinearGroup.toGL A) q

/-- This action is literally the quaternion fractional expression for determinant one. -/
theorem poincareSpecialLinearMap_quaternion (A : Auxiliary.Algebra.SpecialLinear2) (q :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    ((poincareSpecialLinearMap A q).val : ℍ) =
      quaternionMatrixExpression (A : Auxiliary.Algebra.ComplexMatrix2) q.val := by
  change (poincareCoordinate (A : Auxiliary.Algebra.ComplexMatrix2) q.val : ℍ) = _
  exact (poincareCoordinate_quaternion_positive_det (A : Auxiliary.Algebra.ComplexMatrix2) 1 zero_lt_one
    (by simp) q.val).symm

/-- The coordinate maps obey the exact matrix multiplication law. -/
theorem poincareSpecialLinearMap_mul (A B : Auxiliary.Algebra.SpecialLinear2) (q :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    poincareSpecialLinearMap (A * B) q = poincareSpecialLinearMap A (poincareSpecialLinearMap B q) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [poincareSpecialLinearMap_quaternion, poincareSpecialLinearMap_quaternion]
  unfold quaternionMatrixExpression
  rw [poincareSpecialLinearMap_quaternion]
  unfold quaternionMatrixExpression
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
    Quaternion.coeComplex_add, Quaternion.coeComplex_mul]
  have h := quaternion_fractional_comp
    ((A : Auxiliary.Algebra.ComplexMatrix2) 0 0 : ℍ) ((A : Auxiliary.Algebra.ComplexMatrix2) 0 1 : ℍ) ((A :
      Auxiliary.Algebra.ComplexMatrix2) 1 0 : ℍ) ((A : Auxiliary.Algebra.ComplexMatrix2) 1 1 : ℍ)
    ((B : Auxiliary.Algebra.ComplexMatrix2) 0 0 : ℍ) ((B : Auxiliary.Algebra.ComplexMatrix2) 0 1 : ℍ) ((B :
      Auxiliary.Algebra.ComplexMatrix2) 1 0 : ℍ) ((B : Auxiliary.Algebra.ComplexMatrix2) 1 1 : ℍ) (q.val : ℍ)
    (quaternionMatrixDenominator_ne_zero (B : Auxiliary.Algebra.ComplexMatrix2) (by simp) q)
  convert h.symm using 1

@[simp] theorem poincareSpecialLinearMap_one (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    poincareSpecialLinearMap 1 q = q := by
  apply Subtype.ext
  apply Subtype.ext
  rw [poincareSpecialLinearMap_quaternion]
  simp [quaternionMatrixExpression]

/-- The coordinate action is bijective; its inverse is the inverse matrix action. -/
def poincareSpecialLinearPerm (A : Auxiliary.Algebra.SpecialLinear2) : Equiv.Perm
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace where
  toFun := poincareSpecialLinearMap A
  invFun := poincareSpecialLinearMap A⁻¹
  left_inv := by
    intro q
    rw [← poincareSpecialLinearMap_mul, inv_mul_cancel, poincareSpecialLinearMap_one]
  right_inv := by
    intro q
    rw [← poincareSpecialLinearMap_mul, mul_inv_cancel, poincareSpecialLinearMap_one]

/-- A genuine group homomorphism to permutations of H3, not just a family of formulas. -/
def poincareSpecialLinearHom : Auxiliary.Algebra.SpecialLinear2 →* Equiv.Perm
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace where
  toFun := poincareSpecialLinearPerm
  map_one' := by
    apply Equiv.ext
    intro q
    exact poincareSpecialLinearMap_one q
  map_mul' := by
    intro A B
    apply Equiv.ext
    intro q
    exact poincareSpecialLinearMap_mul A B q

/-- Equal boundary transformations give equal coordinate maps on H3. -/
theorem poincareMatrixMap_eq_of_projection_eq (A B : FractionalLinearMatrix)
    (h : matrixProjection A = matrixProjection B) (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    poincareMatrixMap A q = poincareMatrixMap B q := by
  apply Subtype.ext
  change poincareCoordinate (A : Auxiliary.Algebra.ComplexMatrix2) q.val =
    poincareCoordinate (B : Auxiliary.Algebra.ComplexMatrix2) q.val
  obtain ⟨u, rfl⟩ := (matrixProjection_eq_iff A B).mp h
  rw [generalLinear_mul_scalar_val, poincareCoordinate_scalar _ _ u.ne_zero]

/-- The central ambiguity in the determinant-one representative acts trivially on H3. -/
theorem poincareSpecialLinearHom_kernel :
    mobiusSpecialLinearProjection.ker ≤ poincareSpecialLinearHom.ker := by
  intro A hA
  change poincareSpecialLinearPerm A = 1
  apply Equiv.ext
  intro q
  change poincareSpecialLinearMap A q = q
  have h := congrArg complexMobiusEquivFractionalLinear
    (show mobiusSpecialLinearProjection A = 1 from hA)
  have hproj : matrixProjection (Matrix.SpecialLinearGroup.toGL A) = matrixProjection 1 := by
    simpa only [mobiusSpecialLinearProjection_equiv, map_one, specialLinearProjection,
      MonoidHom.comp_apply] using h
  calc
    _ = poincareMatrixMap 1 q := poincareMatrixMap_eq_of_projection_eq _ _ hproj q
    _ = q := by
      change poincareSpecialLinearMap 1 q = q
      exact poincareSpecialLinearMap_one q

/-- The coordinate action descends to the actual geometric complex Möbius group. -/
def mobiusPoincareHom : complexMobiusGroup →* Equiv.Perm Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
  mobiusSpecialLinearProjection.liftOfSurjective mobiusSpecialLinearProjection_surjective
    ⟨poincareSpecialLinearHom, poincareSpecialLinearHom_kernel⟩

theorem mobiusPoincareHom_specialLinearProjection (A : Auxiliary.Algebra.SpecialLinear2) :
    mobiusPoincareHom (mobiusSpecialLinearProjection A) = poincareSpecialLinearHom A := by
  simp only [mobiusPoincareHom, MonoidHom.liftOfSurjective,
    MonoidHom.liftOfRightInverse_comp_apply]

/-- The descended action agrees with the original formula for every nonsingular matrix. -/
theorem mobiusPoincareHom_matrixProjection_apply (A : FractionalLinearMatrix) (q :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    mobiusPoincareHom (mobiusMatrixProjection A) q = poincareMatrixMap A q := by
  obtain ⟨B, hB⟩ := mobiusSpecialLinearProjection_surjective (mobiusMatrixProjection A)
  rw [← hB, mobiusPoincareHom_specialLinearProjection]
  have hproj : matrixProjection (Matrix.SpecialLinearGroup.toGL B) = matrixProjection A := by
    have h := congrArg complexMobiusEquivFractionalLinear hB
    simpa only [mobiusSpecialLinearProjection_equiv, mobiusMatrixProjection_equiv,
      specialLinearProjection, MonoidHom.comp_apply] using h
  exact poincareMatrixMap_eq_of_projection_eq _ _ hproj q

/-- General nonsingular matrix coordinates obey the exact composition law as well. -/
theorem poincareMatrixMap_mul (A B : FractionalLinearMatrix) (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    poincareMatrixMap (A * B) q = poincareMatrixMap A (poincareMatrixMap B q) := by
  calc
    _ = mobiusPoincareHom (mobiusMatrixProjection (A * B)) q :=
      (mobiusPoincareHom_matrixProjection_apply _ _).symm
    _ = (mobiusPoincareHom (mobiusMatrixProjection A) *
        mobiusPoincareHom (mobiusMatrixProjection B)) q := by rw [map_mul, map_mul]
    _ = poincareMatrixMap A (poincareMatrixMap B q) := by
      change mobiusPoincareHom (mobiusMatrixProjection A)
        (mobiusPoincareHom (mobiusMatrixProjection B) q) = _
      rw [mobiusPoincareHom_matrixProjection_apply, mobiusPoincareHom_matrixProjection_apply]

/-- The real upper-half-space carrier now has the actual complex Möbius group action. -/
instance mobiusUpperHalfSpaceMulAction : MulAction complexMobiusGroup Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
  MulAction.compHom Hyperbolic.QuaternionHalfSpace.UpperHalfSpace mobiusPoincareHom

@[simp] theorem mobiusUpperHalfSpace_smul (f : complexMobiusGroup) (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    f • q = mobiusPoincareHom f q := rfl

/-- The determinant-one maps are continuous for the genuine Euclidean subspace topology. -/
theorem continuous_poincareSpecialLinearMap (A : Auxiliary.Algebra.SpecialLinear2) :
    Continuous (poincareSpecialLinearMap A) := by
  have hq : Continuous (fun q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => (q.val : ℍ)) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hn : Continuous (fun q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
      (A 0 0 : ℍ) * (q.val : ℍ) + (A 0 1 : ℍ)) :=
    (continuous_const.mul hq).add continuous_const
  have hd : Continuous (fun q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
      (A 1 0 : ℍ) * (q.val : ℍ) + (A 1 1 : ℍ)) :=
    (continuous_const.mul hq).add continuous_const
  have he : Continuous (fun q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace =>
      quaternionMatrixExpression (A : Auxiliary.Algebra.ComplexMatrix2) q.val) := by
    have h := hn.mul
      (hd.inv₀ (quaternionMatrixDenominator_ne_zero (A : Auxiliary.Algebra.ComplexMatrix2) (by simp)))
    convert h using 1
    funext q
    rfl
  apply continuous_induced_rng.mpr
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, poincareSpecialLinearMap_quaternion] using he

/-- The inverse matrix provides a continuous inverse as well. -/
def poincareSpecialLinearHomeomorph (A : Auxiliary.Algebra.SpecialLinear2) :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace ≃ₜ Hyperbolic.QuaternionHalfSpace.UpperHalfSpace where
  __ := poincareSpecialLinearPerm A
  continuous_toFun := continuous_poincareSpecialLinearMap A
  continuous_invFun := continuous_poincareSpecialLinearMap A⁻¹

@[simp] theorem poincareSpecialLinearHomeomorph_apply (A : Auxiliary.Algebra.SpecialLinear2) (q :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    poincareSpecialLinearHomeomorph A q = poincareSpecialLinearMap A q := rfl

/-- Every actual complex Möbius group element acts continuously on H3. -/
theorem continuous_mobiusPoincareHom (f : complexMobiusGroup) :
    Continuous (mobiusPoincareHom f) := by
  obtain ⟨A, rfl⟩ := mobiusSpecialLinearProjection_surjective f
  rw [mobiusPoincareHom_specialLinearProjection]
  exact continuous_poincareSpecialLinearMap A

/-- The actual Möbius group acts by homeomorphisms of H3. -/
def mobiusPoincareHomeomorph (f : complexMobiusGroup) : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace ≃ₜ
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace where
  __ := mobiusPoincareHom f
  continuous_toFun := continuous_mobiusPoincareHom f
  continuous_invFun := by
    have h := continuous_mobiusPoincareHom f⁻¹
    simpa only [map_inv, Equiv.Perm.coe_inv, Equiv.invFun_as_coe] using h

@[simp] theorem mobiusPoincareHomeomorph_apply (f : complexMobiusGroup) (q :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    mobiusPoincareHomeomorph f q = f • q := rfl

/-- The positive denominator in the quaternion Cayley transform. -/
def cayleyDenominator (z : ℂ) (t : ℝ) : ℝ := ‖z‖ ^ 2 + (t + 1) ^ 2

/-- as a literal quaternion expression. -/
def quaternionCayleyExpression (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) : ℍ :=
  ((q : ℍ) - Hyperbolic.QuaternionHalfSpace.quaternionJ) * ((q : ℍ) +
    Hyperbolic.QuaternionHalfSpace.quaternionJ)⁻¹ * Hyperbolic.QuaternionHalfSpace.quaternionJ

/-- In the actual quaternion three-space. -/
def cayleyCoordinate (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace :=
  Hyperbolic.QuaternionHalfSpace.quaternionThreePoint
    (2 * Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q / (cayleyDenominator
      (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q) (Hyperbolic.QuaternionHalfSpace.quaternionHeight q) : ℂ))
    ((‖Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q‖ ^ 2 +
      Hyperbolic.QuaternionHalfSpace.quaternionHeight q ^ 2 - 1) /
      cayleyDenominator (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q)
        (Hyperbolic.QuaternionHalfSpace.quaternionHeight q))

@[simp] theorem quaternionJ_norm : ‖Hyperbolic.QuaternionHalfSpace.quaternionJ‖ = 1 := by
  have h : ‖Hyperbolic.QuaternionHalfSpace.quaternionJ‖ ^ 2 = 1 := by
    rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self]
    norm_num [Hyperbolic.QuaternionHalfSpace.quaternionJ, Quaternion.normSq_def']
  nlinarith [norm_nonneg Hyperbolic.QuaternionHalfSpace.quaternionJ]

theorem quaternion_cayley_denominator_normSq (z : ℂ) (t : ℝ) :
    Quaternion.normSq ((Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z t : ℍ) +
      Hyperbolic.QuaternionHalfSpace.quaternionJ) =
      cayleyDenominator z t := by
  unfold cayleyDenominator
  rw [← Complex.normSq_eq_norm_sq]
  simp [Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, Hyperbolic.QuaternionHalfSpace.quaternionJ,
    Quaternion.normSq_def', Complex.normSq_apply, pow_two]

/-- The numerator is an identity in the quaternion algebra, not a coordinate definition. -/
theorem quaternion_cayley_numerator (z : ℂ) (t : ℝ) :
    ((Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z t : ℍ) - Hyperbolic.QuaternionHalfSpace.quaternionJ) *
      star ((Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z t : ℍ) +
        Hyperbolic.QuaternionHalfSpace.quaternionJ) * Hyperbolic.QuaternionHalfSpace.quaternionJ =
      (⟨2 * z.re, 2 * z.im, ‖z‖ ^ 2 + t ^ 2 - 1, 0⟩ : ℍ) := by
  apply Quaternion.ext <;>
    simp [Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, Hyperbolic.QuaternionHalfSpace.quaternionJ, ←
      Complex.normSq_eq_norm_sq,
      Complex.normSq_apply] <;> ring

/-- is exactly the actual quaternion fractional expression. -/
theorem quaternionCayleyExpression_coordinates (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    quaternionCayleyExpression q = (cayleyCoordinate q : ℍ) := by
  rw [← Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates q]
  simp only [quaternionCayleyExpression, cayleyCoordinate,
    Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint,
    Hyperbolic.QuaternionHalfSpace.quaternionHeight_threePoint]
  rw [Quaternion.inv_def, quaternion_cayley_denominator_normSq,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc, quaternion_cayley_numerator]
  apply Quaternion.ext <;>
    simp only [Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, Quaternion.re_smul, Quaternion.imI_smul,
      Quaternion.imJ_smul, Quaternion.imK_smul, smul_eq_mul,
      Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.mul_re, Complex.mul_im,
      Complex.re_ofNat, Complex.im_ofNat, mul_zero] <;> ring

/-- The norm comparison uses the genuine multiplicative quaternion norm. -/
theorem quaternionCayleyExpression_norm_sq (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    ‖quaternionCayleyExpression q‖ ^ 2 =
      ‖(q : ℍ) - Hyperbolic.QuaternionHalfSpace.quaternionJ‖ ^ 2 / ‖(q : ℍ) +
        Hyperbolic.QuaternionHalfSpace.quaternionJ‖ ^ 2 := by
  simp only [quaternionCayleyExpression, norm_mul, norm_inv, quaternionJ_norm, mul_one,
    mul_pow, div_eq_mul_inv, inv_pow]

/-- The lower numerator norm-square is the Euclidean coordinate expression. -/
theorem quaternion_cayley_lower_norm_sq (z : ℂ) (t : ℝ) :
    ‖(Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z t : ℍ) - Hyperbolic.QuaternionHalfSpace.quaternionJ‖ ^
      2 = ‖z‖ ^ 2 + (t - 1) ^ 2 := by
  rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self]
  rw [← Complex.normSq_eq_norm_sq]
  simp [Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, Hyperbolic.QuaternionHalfSpace.quaternionJ,
    Quaternion.normSq_def', Complex.normSq_apply, pow_two]

/-- At every finite nonpole point, entering the unit ball is equivalent to positive height. -/
theorem cayleyCoordinate_norm_lt_one_iff (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)
    (hq : (q : ℍ) + Hyperbolic.QuaternionHalfSpace.quaternionJ ≠ 0) : ‖cayleyCoordinate q‖ < 1 ↔ 0 <
      Hyperbolic.QuaternionHalfSpace.quaternionHeight q := by
  have hd : 0 < cayleyDenominator (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q)
    (Hyperbolic.QuaternionHalfSpace.quaternionHeight q) := by
    rw [← quaternion_cayley_denominator_normSq, Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates]
    exact lt_of_le_of_ne Quaternion.normSq_nonneg
      (Ne.symm (Quaternion.normSq_ne_zero.mpr hq))
  have hnorm := quaternionCayleyExpression_norm_sq q
  rw [quaternionCayleyExpression_coordinates] at hnorm
  have hu : ‖(q : ℍ) + Hyperbolic.QuaternionHalfSpace.quaternionJ‖ ^ 2 =
      cayleyDenominator (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q)
        (Hyperbolic.QuaternionHalfSpace.quaternionHeight q) := by
    rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self,
      ← quaternion_cayley_denominator_normSq, Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates]
  have hl : ‖(q : ℍ) - Hyperbolic.QuaternionHalfSpace.quaternionJ‖ ^ 2 =
      ‖Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q‖ ^ 2 +
        (Hyperbolic.QuaternionHalfSpace.quaternionHeight q - 1) ^ 2 := by
    simpa only [Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates] using
      quaternion_cayley_lower_norm_sq (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q)
        (Hyperbolic.QuaternionHalfSpace.quaternionHeight q)
  rw [hu, hl] at hnorm
  change ‖(cayleyCoordinate q : ℍ)‖ < 1 ↔ _
  rw [← sq_lt_sq₀ (norm_nonneg _) zero_le_one, hnorm, one_pow, div_lt_one hd]
  dsimp [cayleyDenominator]
  constructor <;> intro h <;> nlinarith

@[simp] theorem upperHalfSpaceJ_quaternion : (Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val : ℍ) =
    Hyperbolic.QuaternionHalfSpace.quaternionJ := rfl

/-- The quaternion j is the third Euclidean unit vector used by the source reflections. -/
theorem euclideanThreeQuaternion_northPole :
    Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion (Inversive.northPole 2) =
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val := by
  apply Subtype.ext
  apply Quaternion.ext <;>
    simp [Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion, Inversive.northPole,
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ,
      Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint, Hyperbolic.QuaternionHalfSpace.quaternionThreePoint]

/-- The first reflection in the source Cayley construction reverses exactly the height. -/
theorem cayley_plane_reflection_coordinates (x : Inversive.Euclidean 3) :
    Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion (Inversive.planeReflectionFinite (Inversive.northPole
      2) 0 x) =
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal
        (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x))
        (-Hyperbolic.QuaternionHalfSpace.quaternionHeight (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion
          x)) := by
  apply Subtype.ext
  apply Quaternion.ext <;>
    simp [Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion, Inversive.planeReflectionFinite, Inversive.northPole,
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, Hyperbolic.QuaternionHalfSpace.quaternionHorizontal,
        Hyperbolic.QuaternionHalfSpace.quaternionHeight,
      EuclideanSpace.inner_single_right]
  ring

/-- The genuine three-dimensional Cayley transformation is the prescribed pair of reflections. -/
def cayleyEuclideanHomeomorph : Inversive.ExtendedHomeomorph 3 :=
  Inversive.sphereInversionHomeomorph (Inversive.northPole 2) (Real.sqrt 2)
    (Real.sqrt_pos.mpr (by norm_num)).ne' *
  Inversive.planeReflectionHomeomorph (Inversive.northPole 2) 0
    (by intro h; have hn := Inversive.norm_northPole 2; rw [h, norm_zero] at hn; norm_num at hn)

/-- This is an actual finite composition of valid sphere and plane reflections. -/
theorem cayleyEuclideanHomeomorph_mem_generalMobiusGroup :
    cayleyEuclideanHomeomorph ∈ Inversive.generalMobiusGroup 3 := by
  apply (Inversive.generalMobiusGroup 3).mul_mem
  · exact (Inversive.sphereInversion_isReflection _ _ (Real.sqrt_pos.mpr (by norm_num))).mem_generalMobiusGroup
  · exact (Inversive.planeReflection_isReflection _ _ _).mem_generalMobiusGroup

/-- The actual Euclidean Cayley homeomorphism in the isometric quaternion coordinates. -/
def cayleyExtendedHomeomorph :
    OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace ≃ₜ OnePoint
      Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace :=
  Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.symm.trans
    (cayleyEuclideanHomeomorph.trans Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion)

/-- The literal quaternion action fixes j precisely for matrices in the quaternion subalgebra. -/
theorem quaternionMatrixExpression_fixJ_iff (A : Auxiliary.Algebra.ComplexMatrix2) (hA : A.det ≠ 0) :
    quaternionMatrixExpression A Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val =
      Hyperbolic.QuaternionHalfSpace.quaternionJ ↔
      A ∈ Set.range Auxiliary.Algebra.quaternionMatrix := by
  have hd := quaternionMatrixDenominator_ne_zero A hA Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ
  rw [quaternionMatrixExpression, mul_inv_eq_iff_eq_mul₀ hd, Auxiliary.Algebra.quaternionMatrix_range_iff_entries]
  simp only [QuaternionAlgebra.ext_iff, Complex.ext_iff]
  simp [Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ, Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint,
    Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, Hyperbolic.QuaternionHalfSpace.quaternionJ]
  constructor
  · rintro ⟨hbr, hbi, har, hai⟩
    constructor <;> constructor <;> linarith
  · rintro ⟨⟨hdr, hdi⟩, ⟨hcr, hci⟩⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The determinant-one coordinate action fixes j exactly for unitary matrices. -/
theorem poincareSpecialLinearMap_fixJ_iff (A : Auxiliary.Algebra.SpecialLinear2) :
    poincareSpecialLinearMap A Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ =
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ↔
      Auxiliary.Algebra.UnitaryMatrix (A : Auxiliary.Algebra.ComplexMatrix2) := by
  have hq : (poincareSpecialLinearMap A Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ =
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) ↔
      quaternionMatrixExpression (A : Auxiliary.Algebra.ComplexMatrix2)
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val = Hyperbolic.QuaternionHalfSpace.quaternionJ := by
    constructor
    · intro h
      have hh := congrArg (fun q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace => (q.val : ℍ)) h
      simpa only [poincareSpecialLinearMap_quaternion, upperHalfSpaceJ_quaternion] using hh
    · intro h
      apply Subtype.ext
      apply Subtype.ext
      simpa only [poincareSpecialLinearMap_quaternion, upperHalfSpaceJ_quaternion] using h
  rw [hq, quaternionMatrixExpression_fixJ_iff _ (by simp)]
  exact ((Auxiliary.Algebra.specialLinear_unitary_iff_norm_iff_quaternion (A : Auxiliary.Algebra.ComplexMatrix2)
    A.det_coe).1.trans
    (Auxiliary.Algebra.specialLinear_unitary_iff_norm_iff_quaternion (A : Auxiliary.Algebra.ComplexMatrix2)
      A.det_coe).2).symm

/-- The fixed-j condition is stated for the actual complex Möbius group action. -/
theorem mobiusSpecialLinearProjection_fixJ_iff (A : Auxiliary.Algebra.SpecialLinear2) :
    mobiusSpecialLinearProjection A • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ =
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ↔
      Auxiliary.Algebra.UnitaryMatrix (A : Auxiliary.Algebra.ComplexMatrix2) := by
  rw [mobiusUpperHalfSpace_smul, mobiusPoincareHom_specialLinearProjection]
  exact poincareSpecialLinearMap_fixJ_iff A

/-- fixing j is equivalent to normalized squared Frobenius norm two. -/
theorem mobiusSpecialLinearProjection_fixJ_iff_norm (A : Auxiliary.Algebra.SpecialLinear2) :
    mobiusSpecialLinearProjection A • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ =
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ↔
      mobiusNormalizedNorm (mobiusSpecialLinearProjection A) ^ 2 = 2 := by
  rw [mobiusSpecialLinearProjection_fixJ_iff, mobiusNormalizedNorm_specialLinearProjection]
  exact (Auxiliary.Algebra.specialLinear_unitary_iff_norm_iff_quaternion (A : Auxiliary.Algebra.ComplexMatrix2)
    A.det_coe).1

/-- The fixed-j criterion is independent of every choice of matrix representative. -/
theorem mobius_fixJ_iff_norm (f : complexMobiusGroup) :
    f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ↔
      mobiusNormalizedNorm f ^ 2 = 2 := by
  obtain ⟨A, rfl⟩ := mobiusSpecialLinearProjection_surjective f
  exact mobiusSpecialLinearProjection_fixJ_iff_norm A

/-- The fixed-j subgroup consists precisely of the transformations represented by SU(2). -/
theorem mobius_fixJ_iff_unitary_representative (f : complexMobiusGroup) :
    f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ ↔
      ∃ A : Auxiliary.Algebra.SpecialLinear2, mobiusSpecialLinearProjection A = f ∧
        Auxiliary.Algebra.UnitaryMatrix (A : Auxiliary.Algebra.ComplexMatrix2) := by
  constructor
  · intro hf
    obtain ⟨A, hA⟩ := mobiusSpecialLinearProjection_surjective f
    refine ⟨A, hA, (mobiusSpecialLinearProjection_fixJ_iff A).mp ?_⟩
    simpa only [hA] using hf
  · rintro ⟨A, rfl, hA⟩
    exact (mobiusSpecialLinearProjection_fixJ_iff A).mpr hA

/-- The reflected distance to the sphere centre is exactly the quaternion Cayley denominator norm. -/
theorem cayley_reflection_residual_norm (x : Inversive.Euclidean 3) :
    ‖Inversive.planeReflectionFinite (Inversive.northPole 2) 0 x - Inversive.northPole 2‖ =
      ‖(Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x : ℍ) +
        Hyperbolic.QuaternionHalfSpace.quaternionJ‖ := by
  rw [← Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.norm_map
    (Inversive.planeReflectionFinite (Inversive.northPole 2) 0 x - Inversive.northPole 2)]
  simp only [map_sub, cayley_plane_reflection_coordinates, euclideanThreeQuaternion_northPole]
  change ‖(Hyperbolic.QuaternionHalfSpace.quaternionThreePoint
    (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x))
    (-Hyperbolic.QuaternionHalfSpace.quaternionHeight (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x))
      : ℍ) - Hyperbolic.QuaternionHalfSpace.quaternionJ‖ = _
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self,
    pow_two, ← Quaternion.normSq_eq_norm_mul_self]
  simp [Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, Hyperbolic.QuaternionHalfSpace.quaternionHorizontal,
    Hyperbolic.QuaternionHalfSpace.quaternionHeight,
    Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion, Hyperbolic.QuaternionHalfSpace.quaternionJ,
      Quaternion.normSq_def']
  ring

/-- The sphere reflection in the genuine Cayley construction has the displayed finite formula. -/
theorem cayley_inversion_coordinates (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)
    (hq : (q : ℍ) + Hyperbolic.QuaternionHalfSpace.quaternionJ ≠ 0) :
    Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion (inversion (Inversive.northPole 2) (Real.sqrt 2)
      (Inversive.planeReflectionFinite (Inversive.northPole 2) 0
        (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q))) = cayleyCoordinate q := by
  have hd : 0 < cayleyDenominator (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q)
    (Hyperbolic.QuaternionHalfSpace.quaternionHeight q) := by
    rw [← quaternion_cayley_denominator_normSq, Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates]
    exact lt_of_le_of_ne Quaternion.normSq_nonneg
      (Ne.symm (Quaternion.normSq_ne_zero.mpr hq))
  have hnorm : ‖Inversive.planeReflectionFinite (Inversive.northPole 2) 0
      (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q) - Inversive.northPole 2‖ ^ 2 =
      cayleyDenominator (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q)
        (Hyperbolic.QuaternionHalfSpace.quaternionHeight q) := by
    rw [cayley_reflection_residual_norm, Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply,
      pow_two, ← Quaternion.normSq_eq_norm_mul_self,
      ← quaternion_cayley_denominator_normSq, Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates]
  rw [Inversive.inversion_formula, map_add, map_smul, map_sub,
    euclideanThreeQuaternion_northPole, cayley_plane_reflection_coordinates,
    Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply, div_pow, Real.sq_sqrt (by norm_num),
      hnorm]
  apply Subtype.ext
  apply Quaternion.ext <;>
    simp [Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ, Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint,
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, cayleyCoordinate,
      Complex.div_ofReal_re, Complex.div_ofReal_im] <;>
    field_simp [ne_of_gt hd]
  simp only [cayleyDenominator]
  ring


/-- The geometric composition agrees with the quaternion coordinates at every finite non-pole. -/
theorem cayleyExtendedHomeomorph_coe (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)
    (hq : (q : ℍ) + Hyperbolic.QuaternionHalfSpace.quaternionJ ≠ 0) :
    cayleyExtendedHomeomorph (q : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
      (cayleyCoordinate q : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) := by
  have hn : Inversive.planeReflectionFinite (Inversive.northPole 2) 0
      (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q) ≠ Inversive.northPole 2 := by
    intro h
    have hh := cayley_reflection_residual_norm (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q)
    rw [h, sub_self, norm_zero, Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply] at hh
    exact hq (norm_eq_zero.mp hh.symm)
  change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion
    (cayleyEuclideanHomeomorph
      (Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.symm (q : OnePoint
        Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace))) = _
  change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion
    (cayleyEuclideanHomeomorph ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q :
      Inversive.Euclidean 3) :
      OnePoint (Inversive.Euclidean 3))) = _
  unfold cayleyEuclideanHomeomorph
  rw [Homeomorph.mul_apply]
  rw [Inversive.planeReflectionHomeomorph_apply, Inversive.planeReflection_coe,
    Inversive.sphereInversionHomeomorph_apply, Inversive.sphereInversion_coe _ _ hn]
  change (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion _ : OnePoint
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) = _
  rw [cayley_inversion_coordinates q hq]

@[simp] theorem cayleyExtendedHomeomorph_infty :
    cayleyExtendedHomeomorph ∞ = (Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val : OnePoint
      Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) := by
  change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion (cayleyEuclideanHomeomorph ∞) = _
  unfold cayleyEuclideanHomeomorph
  rw [Homeomorph.mul_apply]
  rw [Inversive.planeReflectionHomeomorph_apply, Inversive.planeReflection_infty,
    Inversive.sphereInversionHomeomorph_apply, Inversive.sphereInversion_infty]
  change (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion _ : OnePoint
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) = _
  rw [euclideanThreeQuaternion_northPole]

/-- The finite pole of the Cayley transformation is -j. -/
theorem cayleyExtendedHomeomorph_pole (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)
    (hq : (q : ℍ) + Hyperbolic.QuaternionHalfSpace.quaternionJ = 0) :
    cayleyExtendedHomeomorph (q : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) = ∞ := by
  have hn : Inversive.planeReflectionFinite (Inversive.northPole 2) 0
      (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q) = Inversive.northPole 2 := by
    apply sub_eq_zero.mp
    apply norm_eq_zero.mp
    rw [cayley_reflection_residual_norm, Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply, hq,
      norm_zero]
  change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion
    (cayleyEuclideanHomeomorph ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q :
      Inversive.Euclidean 3) :
      OnePoint (Inversive.Euclidean 3))) = _
  unfold cayleyEuclideanHomeomorph
  rw [Homeomorph.mul_apply]
  rw [Inversive.planeReflectionHomeomorph_apply, Inversive.planeReflection_coe, hn,
    Inversive.sphereInversionHomeomorph_apply, Inversive.sphereInversion_center]
  rfl

/-- The unit ball uses exactly the Euclidean norm already inherited by quaternion three-space. -/
def quaternionBallSet : Set Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace := Metric.ball 0 1

/-- The finite unit ball regarded inside the same one-point compactification. -/
def extendedQuaternionBallSet : Set (OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :=
  (fun q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace => (q : OnePoint
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)) '' quaternionBallSet

/-- The actual two-reflection Cayley transformation sends exactly H3 into the unit ball. -/
theorem cayleyExtendedHomeomorph_preimage_ball :
    Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet = cayleyExtendedHomeomorph ⁻¹'
      extendedQuaternionBallSet := by
  ext q
  induction q using OnePoint.rec with
  | infty =>
    simp only [Set.mem_preimage, cayleyExtendedHomeomorph_infty]
    have hj : Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val ∉ quaternionBallSet := by
      change ¬dist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val 0 < 1
      rw [dist_zero_right]
      change ¬‖(Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val : ℍ)‖ < 1
      rw [upperHalfSpaceJ_quaternion, quaternionJ_norm]
      exact lt_irrefl 1
    simpa [Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet, extendedQuaternionBallSet] using hj
  | coe q =>
    by_cases hq : (q : ℍ) + Hyperbolic.QuaternionHalfSpace.quaternionJ = 0
    · rw [Set.mem_preimage, cayleyExtendedHomeomorph_pole q hq]
      have ht : Hyperbolic.QuaternionHalfSpace.quaternionHeight q = -1 := by
        have hh := congrArg (fun w : ℍ => w.imJ) hq
        simp [Hyperbolic.QuaternionHalfSpace.quaternionHeight, Hyperbolic.QuaternionHalfSpace.quaternionJ] at hh ⊢
        linarith
      simp [Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet, extendedQuaternionBallSet,
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceSet, ht]
    · rw [Set.mem_preimage, cayleyExtendedHomeomorph_coe q hq]
      simpa [Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet, extendedQuaternionBallSet,
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceSet,
        quaternionBallSet, Metric.mem_ball, dist_zero_right] using
          (cayleyCoordinate_norm_lt_one_iff q hq).symm

/-- The genuine Cayley transformation identifies H3 homeomorphically with B3. -/
def upperHalfSpaceBallHomeomorph : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace ≃ₜ quaternionBallSet :=
  (OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage Hyperbolic.QuaternionHalfSpace.upperHalfSpaceSet).trans
    ((cayleyExtendedHomeomorph.sets cayleyExtendedHomeomorph_preimage_ball).trans
      (OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage quaternionBallSet).symm)


/-- The pole -j cannot lie in positive-height space. -/
theorem quaternionCayley_denominator_ne_zero (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (q.val : ℍ) + Hyperbolic.QuaternionHalfSpace.quaternionJ ≠ 0 := by
  intro h
  have hh := congrArg (fun w : ℍ => w.imJ) h
  change Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val + 1 = 0 at hh
  have ht := q.property
  change 0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val at ht
  linarith

/-- The genuine ball homeomorphism has the source's displayed coordinate formula. -/
theorem upperHalfSpaceBallHomeomorph_apply (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (upperHalfSpaceBallHomeomorph q).val = cayleyCoordinate q.val := by
  apply OnePoint.coe_injective
  have h : ((upperHalfSpaceBallHomeomorph q).val : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
      cayleyExtendedHomeomorph (q.val : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) := by
    exact congrArg Subtype.val
      ((OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage quaternionBallSet).apply_symm_apply
        ((cayleyExtendedHomeomorph.sets cayleyExtendedHomeomorph_preimage_ball)
          ((OnePoint.isOpenEmbedding_coe.isEmbedding.homeomorphImage
            Hyperbolic.QuaternionHalfSpace.upperHalfSpaceSet) q)))
  rw [h, cayleyExtendedHomeomorph_coe _ (quaternionCayley_denominator_ne_zero q)]

@[simp] theorem cayleyCoordinate_j : cayleyCoordinate Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val = 0 := by
  simp only [cayleyCoordinate, Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ_horizontal,
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ_height,
    norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, zero_div]
  apply Subtype.ext
  apply Quaternion.ext <;> norm_num [cayleyDenominator, Hyperbolic.QuaternionHalfSpace.quaternionThreePoint]

/-- The distinguished positive-height point j becomes the centre of the ball model. -/
@[simp] theorem upperHalfSpaceBallHomeomorph_j :
    (upperHalfSpaceBallHomeomorph Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).val = 0 := by
  rw [upperHalfSpaceBallHomeomorph_apply, cayleyCoordinate_j]


/-- The complex boundary plane is exactly the equatorial Euclidean coordinate plane. -/
theorem euclideanThreeQuaternion_equatorial_complex (z : ℂ) :
    Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion
      (Inversive.equatorialEmbedding 2 (Complex.orthonormalBasisOneI.repr z)) =
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z 0 := by
  apply Subtype.ext
  apply Quaternion.ext <;>
    simp [Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion, Inversive.equatorialEmbedding,
      Complex.orthonormalBasisOneI_repr_apply, Hyperbolic.QuaternionHalfSpace.quaternionThreePoint]

/-- The Cayley boundary restriction agrees with the stereographic coordinate map. -/
theorem cayleyExtendedHomeomorph_boundary (z : ExtendedComplex) :
    cayleyExtendedHomeomorph (Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding z) =
      ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion
        (Inversive.stereographicHomeomorph 2 (extendedComplexEuclideanHomeomorph z))) :
          OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) := by
  induction z using OnePoint.rec with
  | infty =>
    rw [Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding_infty, cayleyExtendedHomeomorph_infty,
      extendedComplexEuclideanHomeomorph_infty, Inversive.stereographicHomeomorph_infty,
      euclideanThreeQuaternion_northPole]
  | coe z =>
    have hn : ((Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z 0 :
      Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) : ℍ) + Hyperbolic.QuaternionHalfSpace.quaternionJ ≠ 0 := by
      intro h
      have hh := congrArg (fun w : ℍ => w.imJ) h
      norm_num [Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, Hyperbolic.QuaternionHalfSpace.quaternionJ] at hh
    rw [Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding_coe,
      cayleyExtendedHomeomorph_coe _ hn, extendedComplexEuclideanHomeomorph_coe,
      Inversive.stereographicHomeomorph_coe, map_smul, map_add, map_smul, map_smul,
      euclideanThreeQuaternion_equatorial_complex, euclideanThreeQuaternion_northPole,
      Complex.orthonormalBasisOneI.repr.norm_map]
    congr 1
    apply Subtype.ext
    apply Quaternion.ext <;>
      simp [cayleyCoordinate, Hyperbolic.QuaternionHalfSpace.quaternionThreePoint,
        Hyperbolic.QuaternionHalfSpace.quaternionHorizontal,
        Hyperbolic.QuaternionHalfSpace.quaternionHeight, Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ,
          Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint, Complex.div_ofReal_re,
        Complex.div_ofReal_im] <;>
      simp [cayleyDenominator, div_eq_mul_inv] <;> ring



theorem quaternionThreePoint_norm_sq (z : ℂ) (t : ℝ) :
    ‖Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z t‖ ^ 2 = ‖z‖ ^ 2 + t ^ 2 := by
  change ‖(Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z t : ℍ)‖ ^ 2 = _
  rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self, ← Complex.normSq_eq_norm_sq]
  simp [Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, Quaternion.normSq_def', Complex.normSq_apply, pow_two]

def quaternionComplexRotation (u : ℂ) (hu : ‖u‖ = 1) :
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace →ₗᵢ[ℝ] Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace where
  toFun q := Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (u *
    Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q) (Hyperbolic.QuaternionHalfSpace.quaternionHeight q)
  map_add' q r := by
    apply Subtype.ext
    apply Quaternion.ext <;>
      simp [Hyperbolic.QuaternionHalfSpace.quaternionThreePoint,
        Hyperbolic.QuaternionHalfSpace.quaternionHorizontal, Hyperbolic.QuaternionHalfSpace.quaternionHeight,
        mul_add] <;> ring
  map_smul' t q := by
    apply Subtype.ext
    apply Quaternion.ext <;>
      simp [Hyperbolic.QuaternionHalfSpace.quaternionThreePoint,
        Hyperbolic.QuaternionHalfSpace.quaternionHorizontal, Hyperbolic.QuaternionHalfSpace.quaternionHeight,
        Complex.mul_re,
        Complex.mul_im] <;> ring
  norm_map' q := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (u *
      Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q) (Hyperbolic.QuaternionHalfSpace.quaternionHeight q)‖
      ^ 2 = ‖q‖ ^ 2
    rw [quaternionThreePoint_norm_sq, norm_mul, hu, one_mul]
    conv_rhs => rw [← Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates q, quaternionThreePoint_norm_sq]

def complexRotationThree (u : ℂ) (hu : ‖u‖ = 1) : Inversive.Euclidean 3 → Inversive.Euclidean 3 :=
  fun x => Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm (quaternionComplexRotation u hu
    (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x))

theorem complexRotationThree_isometry (u : ℂ) (hu : ‖u‖ = 1) :
    Isometry (complexRotationThree u hu) :=
  Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm.isometry.comp
    ((quaternionComplexRotation u hu).isometry.comp Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.isometry)

/-- A genuine Euclidean similarity extending the complex affine map. -/
def affineThreeHomeomorph (a b : ℂ) (ha : a ≠ 0) : Inversive.ExtendedHomeomorph 3 :=
  Inversive.translationHomeomorph (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm
    (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint b 0)) *
  Inversive.dilationHomeomorph ‖a‖ (norm_ne_zero_iff.mpr ha) *
  Inversive.euclideanIsometryHomeomorph (complexRotationThree (a / (‖a‖ : ℂ))
    (by simp [norm_ne_zero_iff.mpr ha]))
    (complexRotationThree_isometry _ (by simp [norm_ne_zero_iff.mpr ha]))

theorem affineThreeHomeomorph_mem (a b : ℂ) (ha : a ≠ 0) :
    affineThreeHomeomorph a b ha ∈ Inversive.generalMobiusGroup 3 := by
  apply (Inversive.generalMobiusGroup 3).mul_mem
  · exact (Inversive.generalMobiusGroup 3).mul_mem
      (Inversive.translation_mem_generalMobiusGroup _)
      (Inversive.dilation_mem_generalMobiusGroup _ (norm_pos_iff.mpr ha))
  · exact Inversive.euclideanIsometry_mem_generalMobiusGroup _ _

theorem affineThreeHomeomorph_coe (a b : ℂ) (ha : a ≠ 0) (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    affineThreeHomeomorph a b ha
      ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q : Inversive.Euclidean 3) :
        Inversive.ExtendedEuclidean 3) =
    ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm
      (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (a *
        Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q + b) (‖a‖ *
        Hyperbolic.QuaternionHalfSpace.quaternionHeight q)) :
        Inversive.Euclidean 3) : Inversive.ExtendedEuclidean 3) := by
  simp only [affineThreeHomeomorph, Homeomorph.mul_apply,
    Inversive.euclideanIsometryHomeomorph_coe, Inversive.dilationHomeomorph_coe,
    Inversive.translationHomeomorph_coe]
  congr 1
  apply Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.injective
  simp only [map_add, map_smul, complexRotationThree,
    LinearIsometryEquiv.apply_symm_apply, quaternionComplexRotation]
  apply Subtype.ext
  apply Quaternion.ext <;>
    simp [Hyperbolic.QuaternionHalfSpace.quaternionThreePoint,
      Hyperbolic.QuaternionHalfSpace.quaternionHorizontal, Hyperbolic.QuaternionHalfSpace.quaternionHeight,
      Complex.div_ofReal_re, Complex.div_ofReal_im, Complex.mul_re, Complex.mul_im]
    <;> field_simp [norm_ne_zero_iff.mpr ha]


@[simp] theorem affineThreeHomeomorph_infty (a b : ℂ) (ha : a ≠ 0) :
    affineThreeHomeomorph a b ha ∞ = ∞ := by
  simp [affineThreeHomeomorph]

/-- The horizontal complex chart is the exact boundary chart for the native extension. -/
theorem extendedEuclideanThreeQuaternion_equatorial (z : ExtendedComplex) :
    Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion
      (Inversive.extendedEquatorialEmbedding 2 (extendedComplexEuclideanHomeomorph z)) =
      Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding z := by
  induction z using OnePoint.rec with
  | infty => rfl
  | coe z =>
    change (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion
      (Inversive.equatorialEmbedding 2 (Complex.orthonormalBasisOneI.repr z)) :
        OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) = _
    rw [euclideanThreeQuaternion_equatorial_complex]
    rfl

/-- The affine coordinate matrix, bundled in the actual complex Mobius group. -/
def affineMobius (a b : ℂ) (ha : a ≠ 0) : complexMobiusGroup :=
  mobiusMatrixProjection (coefficientMatrix a b 0 1 (by simpa using ha))

@[simp] theorem affineMobius_coe (a b : ℂ) (ha : a ≠ 0) :
    (affineMobius a b ha : Equiv.Perm ExtendedComplex) = (affineHomeomorph a b ha).toEquiv := by
  change fractionalLinearOfCoefficients a b 0 1 _ = _
  rw [fractionalLinearOfCoefficients_affine_eq]
  simp

/-- The upper-half-space action of an affine complex map has the exact similarity formula. -/
theorem affineMobius_smul (a b : ℂ) (ha : a ≠ 0) (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (affineMobius a b ha • q).val =
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (a * Hyperbolic.QuaternionHalfSpace.quaternionHorizontal
        q.val + b) (‖a‖ * Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val) := by
  rw [mobiusUpperHalfSpace_smul, affineMobius, mobiusPoincareHom_matrixProjection_apply]
  apply Subtype.ext
  apply Quaternion.ext <;>
    simp [poincareMatrixMap, poincareHorizontal, poincareHeight, poincareDenominator,
      coefficientMatrix_val, Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint,
        Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, Matrix.det_fin_two]


/-- The native Euclidean homeomorphism in the fixed quaternion coordinates. -/
def quaternionConjugateHom : Inversive.ExtendedHomeomorph 3 →*
    (OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace ≃ₜ OnePoint
      Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) where
  toFun F := Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.symm.trans
    (F.trans Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion)
  map_one' := by ext q; simp
  map_mul' F G := by ext q; simp

/-- Exact boundary and interior agreement with a genuine real Mobius transformation. -/
def GeometricPoincareAction (f : complexMobiusGroup) (F : Inversive.ExtendedHomeomorph 3) : Prop :=
  F ∈ Inversive.generalMobiusGroup 3 ∧
    (∀ z : ExtendedComplex, quaternionConjugateHom F (Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding z) =
      Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding ((f : Equiv.Perm ExtendedComplex) z)) ∧
    (∀ q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace, quaternionConjugateHom F (q.val : OnePoint
      Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
      ((f • q).val : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace))

theorem GeometricPoincareAction.mul {f g : complexMobiusGroup}
    {F G : Inversive.ExtendedHomeomorph 3}
    (hF : GeometricPoincareAction f F) (hG : GeometricPoincareAction g G) :
    GeometricPoincareAction (f * g) (F * G) := by
  refine ⟨(Inversive.generalMobiusGroup 3).mul_mem hF.1 hG.1, ?_, ?_⟩
  · intro z
    rw [map_mul, Homeomorph.mul_apply, hG.2.1, hF.2.1]
    rfl
  · intro q
    rw [map_mul, Homeomorph.mul_apply, hG.2.2, hF.2.2, mul_smul]

theorem affineThreeHomeomorph_geometric (a b : ℂ) (ha : a ≠ 0) :
    GeometricPoincareAction (affineMobius a b ha) (affineThreeHomeomorph a b ha) := by
  refine ⟨affineThreeHomeomorph_mem a b ha, ?_, ?_⟩
  · intro z
    rw [affineMobius_coe]
    induction z using OnePoint.rec with
    | infty =>
      change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion (affineThreeHomeomorph a b ha ∞) = _
      rw [affineThreeHomeomorph_infty]
      rfl
    | coe z =>
      change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion (affineThreeHomeomorph a b ha
        ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm
          (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z 0) : Inversive.Euclidean 3) :
          Inversive.ExtendedEuclidean 3)) = _
      rw [affineThreeHomeomorph_coe]
      change (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (a * z + b) (‖a‖ * 0) : OnePoint
        Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) = _
      simp only [mul_zero, affineHomeomorph_coe, Homeomorph.coe_toEquiv,
        Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding_coe]
  · intro q
    change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion (affineThreeHomeomorph a b ha
      ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val : Inversive.Euclidean 3) :
        Inversive.ExtendedEuclidean 3)) = _
    rw [affineThreeHomeomorph_coe]
    change (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (a *
      Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val + b)
      (‖a‖ * Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val) : OnePoint
        Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) = _
    rw [affineMobius_smul]

/-- Reflection in the plane reversing just the imaginary complex coordinate. -/
def imaginaryReflectionNormal : Inversive.Euclidean 3 := EuclideanSpace.single 1 1

theorem imaginaryReflectionNormal_norm : ‖imaginaryReflectionNormal‖ = 1 := by
  simp [imaginaryReflectionNormal]

theorem imaginaryReflectionNormal_ne_zero : imaginaryReflectionNormal ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [imaginaryReflectionNormal_norm]; exact one_ne_zero)

theorem imaginaryReflection_coordinates (x : Inversive.Euclidean 3) :
    Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion (Inversive.planeReflectionFinite
      imaginaryReflectionNormal 0 x) =
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (conj
        (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal
        (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x)))
        (Hyperbolic.QuaternionHalfSpace.quaternionHeight (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion
          x)) := by
  apply Subtype.ext
  apply Quaternion.ext <;>
    simp [Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion, Inversive.planeReflectionFinite,
      imaginaryReflectionNormal,
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, Hyperbolic.QuaternionHalfSpace.quaternionHorizontal,
        Hyperbolic.QuaternionHalfSpace.quaternionHeight,
      EuclideanSpace.inner_single_right]
  ring

/-- The reciprocal extends as a genuine plane reflection followed by sphere inversion. -/
def reciprocalThreeHomeomorph : Inversive.ExtendedHomeomorph 3 :=
  Inversive.sphereInversionHomeomorph 0 1 one_ne_zero *
    Inversive.planeReflectionHomeomorph imaginaryReflectionNormal 0 imaginaryReflectionNormal_ne_zero




theorem quaternionThreePoint_smul (r : ℝ) (z : ℂ) (t : ℝ) :
    r • Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z t =
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint ((r : ℂ) * z) (r * t) := by
  apply Subtype.ext
  apply Quaternion.ext <;> simp [Hyperbolic.QuaternionHalfSpace.quaternionThreePoint]

theorem quaternionThreePoint_div (d : ℝ) (z : ℂ) (t : ℝ) :
    (1 / d) • Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z t =
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (z / (d : ℂ)) (t / d) := by
  rw [quaternionThreePoint_smul]
  congr 1
  · simp [div_eq_mul_inv, mul_comm]
  · ring

theorem reciprocalThreeHomeomorph_coe (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) (hq : q ≠ 0) :
    quaternionConjugateHom reciprocalThreeHomeomorph (q : OnePoint
      Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
      (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (conj
        (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q) / (‖q‖ ^ 2 : ℝ))
        (Hyperbolic.QuaternionHalfSpace.quaternionHeight q / ‖q‖ ^ 2) : OnePoint
          Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) := by
  have hn2 : ‖Inversive.planeReflectionFinite imaginaryReflectionNormal 0
      (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q)‖ ^ 2 = ‖q‖ ^ 2 := by
    rw [← Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.norm_map, imaginaryReflection_coordinates,
      Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply, quaternionThreePoint_norm_sq,
        Complex.norm_conj]
    conv_rhs => rw [← Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates q, quaternionThreePoint_norm_sq]
  have hn : Inversive.planeReflectionFinite imaginaryReflectionNormal 0
      (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q) ≠ 0 := by
    intro h
    rw [h, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hn2
    exact (pow_ne_zero 2 (norm_ne_zero_iff.mpr hq)) hn2.symm
  change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion (reciprocalThreeHomeomorph
    ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q : Inversive.Euclidean 3) :
      Inversive.ExtendedEuclidean 3)) = _
  rw [reciprocalThreeHomeomorph, Homeomorph.mul_apply,
    Inversive.planeReflectionHomeomorph_apply, Inversive.planeReflection_coe,
    Inversive.sphereInversionHomeomorph_apply, Inversive.sphereInversion_coe _ _ hn]
  change (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion _ : OnePoint
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) = _
  congr 1
  rw [Inversive.inversion_formula, zero_add, sub_zero, map_smul,
    imaginaryReflection_coordinates, Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply,
    div_pow, one_pow, hn2]
  rw [quaternionThreePoint_div]

theorem reciprocalMobius_smul (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (reciprocalMobius • q).val =
      Hyperbolic.QuaternionHalfSpace.quaternionThreePoint (conj
        (Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val) / (‖q.val‖ ^ 2 : ℝ))
        (Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val / ‖q.val‖ ^ 2) := by
  rw [mobiusUpperHalfSpace_smul, reciprocalMobius, mobiusPoincareHom_matrixProjection_apply]
  have hn : ‖q.val‖ ^ 2 = ‖Hyperbolic.QuaternionHalfSpace.quaternionHorizontal q.val‖ ^ 2 +
    Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val ^ 2 := by
    conv_lhs => rw [← Hyperbolic.QuaternionHalfSpace.quaternionThreePoint_coordinates q.val,
      quaternionThreePoint_norm_sq]
  rw [hn]
  apply Subtype.ext
  apply Quaternion.ext <;>
    simp [poincareMatrixMap, poincareHorizontal, poincareHeight, poincareDenominator,
      coefficientMatrix_val, Hyperbolic.QuaternionHalfSpace.upperHalfSpacePoint,
        Hyperbolic.QuaternionHalfSpace.quaternionThreePoint, Matrix.det_fin_two]


theorem reciprocalThreeHomeomorph_geometric :
    GeometricPoincareAction reciprocalMobius reciprocalThreeHomeomorph := by
  refine ⟨(Inversive.generalMobiusGroup 3).mul_mem
    ((Inversive.sphereInversion_isReflection 0 1 zero_lt_one).mem_generalMobiusGroup)
    ((Inversive.planeReflection_isReflection _ _ _).mem_generalMobiusGroup), ?_, ?_⟩
  · intro z
    rw [reciprocalMobius_coe]
    induction z using OnePoint.rec with
    | infty =>
      change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion (reciprocalThreeHomeomorph ∞) = _
      rw [reciprocalThreeHomeomorph, Homeomorph.mul_apply,
        Inversive.planeReflectionHomeomorph_apply, Inversive.planeReflection_infty,
        Inversive.sphereInversionHomeomorph_apply, Inversive.sphereInversion_infty,
        reciprocal_infty, Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding_coe]
      change (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion 0 : OnePoint
        Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) = _
      rw [map_zero]
      rfl
    | coe z =>
      by_cases hz : z = 0
      · subst z
        rw [reciprocal_zero]
        change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion (reciprocalThreeHomeomorph
          (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm
            (Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 0) :
            Inversive.ExtendedEuclidean 3)) = ∞
        have hp : Hyperbolic.QuaternionHalfSpace.quaternionThreePoint 0 0 = 0 := by
          apply Subtype.ext
          apply Quaternion.ext <;> rfl
        rw [hp, map_zero, reciprocalThreeHomeomorph, Homeomorph.mul_apply,
          Inversive.planeReflectionHomeomorph_apply, Inversive.planeReflection_coe]
        simp [Inversive.planeReflectionFinite, Inversive.sphereInversionHomeomorph_apply]
        rfl
      · have hq : Hyperbolic.QuaternionHalfSpace.quaternionThreePoint z 0 ≠ 0 := by
          intro h
          have hh := congrArg Hyperbolic.QuaternionHalfSpace.quaternionHorizontal h
          exact hz (by simpa only [Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint,
            show Hyperbolic.QuaternionHalfSpace.quaternionHorizontal 0 = 0 from rfl] using hh)
        rw [Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding_coe, reciprocalThreeHomeomorph_coe _ hq,
          reciprocal_coe z hz, Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding_coe]
        congr 1
        rw [quaternionThreePoint_norm_sq]
        simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero,
          Hyperbolic.QuaternionHalfSpace.quaternionHorizontal_threePoint,
            Hyperbolic.QuaternionHalfSpace.quaternionHeight_threePoint, zero_div]
        congr 1
        rw [RCLike.inv_def]
        simp [div_eq_mul_inv]
  · intro q
    have hq : q.val ≠ 0 := by
      intro h
      have ht := q.property
      change 0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight q.val at ht
      rw [h] at ht
      simp [Hyperbolic.QuaternionHalfSpace.quaternionHeight] at ht
    rw [reciprocalThreeHomeomorph_coe _ hq, reciprocalMobius_smul]


/-- The affine/reciprocal normal form supplies a genuine geometric extension for every Mobius map. -/
theorem exists_geometricPoincareAction (f : complexMobiusGroup) :
    ∃ F : Inversive.ExtendedHomeomorph 3, GeometricPoincareAction f F := by
  obtain ⟨A, rfl⟩ := mobiusMatrixProjection_surjective f
  obtain ⟨h, he⟩ := fractionalLinear_matrix_coefficients A
  by_cases hc : A 1 0 = 0
  · have hd : A 1 1 ≠ 0 := by intro hd; simp [hc, hd] at h
    have ha : A 0 0 ≠ 0 := by intro ha; simp [hc, ha] at h
    have hf : mobiusMatrixProjection A =
        affineMobius (A 0 0 / A 1 1) (A 0 1 / A 1 1) (div_ne_zero ha hd) := by
      apply Subtype.ext
      rw [mobiusMatrixProjection_coe, ← he, affineMobius_coe]
      simpa only [hc] using fractionalLinearOfCoefficients_affine_eq
        (A 0 0) (A 0 1) (A 1 1) (by simpa only [hc] using h)
    rw [hf]
    exact ⟨_, affineThreeHomeomorph_geometric _ _ _⟩
  · let u := -(A 0 0 * A 1 1 - A 0 1 * A 1 0) / A 1 0 ^ 2
    have hu : u ≠ 0 := div_ne_zero (neg_ne_zero.mpr h) (pow_ne_zero 2 hc)
    have hf : mobiusMatrixProjection A =
        affineMobius u (A 0 0 / A 1 0) hu * reciprocalMobius *
          affineMobius 1 (A 1 1 / A 1 0) one_ne_zero := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, affineMobius_coe, reciprocalMobius_coe]
      rw [mobiusMatrixProjection_coe, ← he]
      exact fractionalLinearOfCoefficients_nonaffine_eq _ _ _ _ h hc
    rw [hf]
    exact ⟨_, ((affineThreeHomeomorph_geometric _ _ _).mul
      reciprocalThreeHomeomorph_geometric).mul (affineThreeHomeomorph_geometric _ _ _)⟩


/-- The uniquely corresponding actual real M2 transformation, with unchanged point action. -/
def mobiusRealRepresentative (f : complexMobiusGroup) : Inversive.GM 2 :=
  ⟨(mobiusEquivFractionalLinear.symm (complexMobiusEquivFractionalLinear f) :
      Inversive.ExtendedHomeomorph 2),
    (mobiusEquivFractionalLinear.symm (complexMobiusEquivFractionalLinear f)).property.1⟩

theorem mobiusRealRepresentative_coordinates (f : complexMobiusGroup) :
    euclideanToComplexHom (mobiusRealRepresentative f) = (f : Equiv.Perm ExtendedComplex) := by
  have h := congrArg (fun g : fractionalLinearGroup => (g : Equiv.Perm ExtendedComplex))
    (mobiusEquivFractionalLinear.apply_symm_apply (complexMobiusEquivFractionalLinear f))
  exact h

/-- The canonical genuine three-dimensional extension of the actual complex Mobius group. -/
def mobiusGeometricPoincare (f : complexMobiusGroup) : Inversive.GM 3 :=
  Hyperbolic.poincareExtension (mobiusRealRepresentative f)


/-- Agreement in the quaternion chart is agreement in the native real upper half-space. -/
theorem GeometricPoincareAction.apply {f : complexMobiusGroup}
    {F : Inversive.ExtendedHomeomorph 3} (hF : GeometricPoincareAction f F)
    (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    F ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val : Inversive.Euclidean 3) :
      Inversive.ExtendedEuclidean 3) =
    ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm (f • q).val : Inversive.Euclidean 3) :
      Inversive.ExtendedEuclidean 3) := by
  apply Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.injective
  exact hF.2.2 q

/-- The geometric extension recovers the actual real boundary transformation. -/
theorem GeometricPoincareAction.extendsBoundary {f : complexMobiusGroup}
    {F : Inversive.ExtendedHomeomorph 3} (hF : GeometricPoincareAction f F) :
    Hyperbolic.ExtendsBoundary (mobiusRealRepresentative f) F := by
  intro z
  let w := extendedComplexEuclideanHomeomorph.symm z
  have hleft : Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.symm
    (Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding w) =
      Inversive.extendedEquatorialEmbedding 2 z := by
    rw [← extendedEuclideanThreeQuaternion_equatorial,
      Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.symm_apply_apply,
      extendedComplexEuclideanHomeomorph.apply_symm_apply]
  have hf := congrArg (fun k : Equiv.Perm ExtendedComplex =>
      extendedComplexEuclideanHomeomorph (k w)) (mobiusRealRepresentative_coordinates f)
  simp only [euclideanToComplexHom_apply,
    extendedComplexEuclideanHomeomorph.apply_symm_apply] at hf
  have hright : Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding ((f : Equiv.Perm ExtendedComplex) w) =
      Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion
        (Inversive.extendedEquatorialEmbedding 2
          ((mobiusRealRepresentative f : Inversive.ExtendedHomeomorph 2) z)) := by
    rw [← extendedEuclideanThreeQuaternion_equatorial, ← hf]
    simp only [w, extendedComplexEuclideanHomeomorph.apply_symm_apply]
  apply Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.injective
  have hh := hF.2.1 w
  change Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion
    (F (Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.symm
      (Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding w))) = _ at hh
  rw [hleft, hright] at hh
  exact hh

/-- The native last coordinate is exactly the quaternion height. -/
theorem euclideanThreeQuaternion_symm_height (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q) (Fin.last 2) =
      Hyperbolic.QuaternionHalfSpace.quaternionHeight q := by
  have h := Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion_height
    (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q)
  rw [Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply] at h
  exact h.symm

/-- Exact coordinate agreement with a bijective H3 action gives the full upper-half-space image. -/
theorem GeometricPoincareAction.preservesUpperHalfSpace {f : complexMobiusGroup}
    {F : Inversive.ExtendedHomeomorph 3} (hF : GeometricPoincareAction f F) :
    F '' Hyperbolic.poincareHalfSpaceSet 2 1 = Hyperbolic.poincareHalfSpaceSet 2 1 := by
  apply Set.Subset.antisymm
  · rintro z ⟨w, ⟨x, hx, rfl⟩, rfl⟩
    let q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
      ⟨Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x, by
      change 0 < x 2
      simpa only [one_mul, show (Fin.last 2 : Fin 3) = 2 from rfl] using hx⟩
    have he := hF.apply q
    have hi : Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val = x :=
      Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm_apply_apply x
    rw [hi] at he
    rw [he]
    refine ⟨Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm (f • q).val, ?_, rfl⟩
    rw [one_mul, euclideanThreeQuaternion_symm_height]
    exact (f • q).property
  · rintro z ⟨x, hx, rfl⟩
    let q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace :=
      ⟨Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x, by
      change 0 < x 2
      simpa only [one_mul, show (Fin.last 2 : Fin 3) = 2 from rfl] using hx⟩
    let p : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace := f⁻¹ • q
    refine ⟨(Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm p.val : Inversive.ExtendedEuclidean 3),
      ⟨Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm p.val, ?_, rfl⟩, ?_⟩
    · rw [one_mul, euclideanThreeQuaternion_symm_height]
      exact p.property
    · rw [hF.apply p]
      simp only [p, smul_inv_smul, q, Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm_apply_apply]

/-- The coordinate action is exactly the canonical geometric Poincare extension. -/
theorem mobiusGeometricPoincare_geometric (f : complexMobiusGroup) :
    GeometricPoincareAction f (mobiusGeometricPoincare f) := by
  obtain ⟨F, hF⟩ := exists_geometricPoincareAction f
  have he : (mobiusGeometricPoincare f : Inversive.ExtendedHomeomorph 3) = F := by
    apply Hyperbolic.poincareExtension_unique (mobiusRealRepresentative f)
      _ _ (mobiusGeometricPoincare f).property hF.1
      (Hyperbolic.poincareExtension_extendsBoundary _) hF.extendsBoundary
      (Hyperbolic.poincareExtension_preservesHalfSpaces _ 1) hF.preservesUpperHalfSpace
  rw [he]
  exact hF

/-- Exact native finite-point action for the actual geometric extension. -/
theorem mobiusGeometricPoincare_apply (f : complexMobiusGroup) (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (mobiusGeometricPoincare f : Inversive.ExtendedHomeomorph 3)
      ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q.val : Inversive.Euclidean 3) :
        Inversive.ExtendedEuclidean 3) =
    ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm (f • q).val : Inversive.Euclidean 3) :
      Inversive.ExtendedEuclidean 3) :=
  (mobiusGeometricPoincare_geometric f).apply q


/-- The canonical real representative respects multiplication. -/
def mobiusRealRepresentativeHom : complexMobiusGroup →* Inversive.GM 2 :=
  (Subgroup.inclusion (show Inversive.orientationPreservingMobiusGroup 2 ≤
      Inversive.generalMobiusGroup 2 from fun _ h => h.1)).comp
    (mobiusEquivFractionalLinear.symm.toMonoidHom.comp
      complexMobiusEquivFractionalLinear.toMonoidHom)

@[simp] theorem mobiusRealRepresentativeHom_apply (f : complexMobiusGroup) :
    mobiusRealRepresentativeHom f = mobiusRealRepresentative f := rfl

/-- The actual complex Mobius group embeds into the genuine three-dimensional geometric group. -/
def mobiusGeometricPoincareHom : complexMobiusGroup →* Inversive.GM 3 :=
  Hyperbolic.poincareExtensionHom.comp mobiusRealRepresentativeHom

@[simp] theorem mobiusGeometricPoincareHom_apply (f : complexMobiusGroup) :
    mobiusGeometricPoincareHom f = mobiusGeometricPoincare f := rfl

/-- is the coordinate action of the genuine geometric Poincare extension. -/
theorem poincareExtension_matrix_formula (A : FractionalLinearMatrix) (q :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    quaternionConjugateHom (mobiusGeometricPoincare (mobiusMatrixProjection A))
      (q.val : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
    (poincareCoordinate (A : Auxiliary.Algebra.ComplexMatrix2) q.val : OnePoint
      Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) := by
  have h := (mobiusGeometricPoincare_geometric (mobiusMatrixProjection A)).2.2 q
  rw [mobiusUpperHalfSpace_smul, mobiusPoincareHom_matrixProjection_apply] at h
  exact h

/-- With positive real determinant, the same genuine extension is the literal quaternion quotient. -/
theorem poincareExtension_quaternion_formula (A : FractionalLinearMatrix) (r : ℝ)
    (hr : 0 < r) (hA : (A : Auxiliary.Algebra.ComplexMatrix2).det = (r : ℂ)) (q :
      Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    quaternionConjugateHom (mobiusGeometricPoincare (mobiusMatrixProjection A))
        (q.val : OnePoint Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
      (poincareCoordinate (A : Auxiliary.Algebra.ComplexMatrix2) q.val : OnePoint
        Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) ∧
    quaternionMatrixExpression (A : Auxiliary.Algebra.ComplexMatrix2) q.val =
      (poincareCoordinate (A : Auxiliary.Algebra.ComplexMatrix2) q.val : ℍ) := by
  exact ⟨poincareExtension_matrix_formula A q,
    poincareCoordinate_quaternion_positive_det (A : Auxiliary.Algebra.ComplexMatrix2) r hr hA q.val⟩


theorem mobiusGeometricPoincareHom_injective : Function.Injective mobiusGeometricPoincareHom := by
  intro f g h
  have hr : mobiusRealRepresentative f = mobiusRealRepresentative g :=
    Hyperbolic.poincareExtensionHom_injective h
  apply Subtype.ext
  rw [← mobiusRealRepresentative_coordinates f, ← mobiusRealRepresentative_coordinates g, hr]

/-- The canonical geometric action agrees with the original Mobius map on the entire boundary. -/
theorem mobiusGeometricPoincare_boundary (f : complexMobiusGroup) (z : ExtendedComplex) :
    quaternionConjugateHom (mobiusGeometricPoincare f) (Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding z) =
      Hyperbolic.QuaternionHalfSpace.extendedBoundaryEmbedding ((f : Equiv.Perm ExtendedComplex) z) :=
  (mobiusGeometricPoincare_geometric f).2.1 z

theorem mobiusGeometricPoincare_preservesHalfSpaces (f : complexMobiusGroup) :
    Hyperbolic.PreservesPoincareHalfSpaces (n := 2)
      (mobiusGeometricPoincare f : Inversive.ExtendedHomeomorph 3) :=
  Hyperbolic.poincareExtension_preservesHalfSpaces _



/-- The actual Euclidean unit ball is carried to the same quaternion unit ball by the norm isometry. -/
theorem quaternionChart_preimage_ball :
    Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion ⁻¹' extendedQuaternionBallSet =
      (Inversive.extendedUnitBall : Set (Inversive.ExtendedEuclidean 3)) := by
  ext x
  induction x using OnePoint.rec with
  | infty => simp [extendedQuaternionBallSet, Inversive.extendedUnitBall,
      Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion]
  | coe x =>
    change ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x : OnePoint
      Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) ∈
      extendedQuaternionBallSet) ↔ _
    simp [extendedQuaternionBallSet, Inversive.extendedUnitBall, quaternionBallSet,
      Metric.mem_ball, dist_zero_right]
    change ‖Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x‖ < 1 ↔ ‖x‖ < 1
    rw [Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.norm_map]

/-- The native upper half-space is the exact preimage of the quaternion H3 set. -/
theorem quaternionChart_preimage_halfSpace :
    Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion ⁻¹'
      Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet =
      Hyperbolic.poincareHalfSpaceSet 2 1 := by
  ext x
  induction x using OnePoint.rec with
  | infty =>
    simp [Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet,
      Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion,
      Hyperbolic.poincareHalfSpaceSet_infty]
  | coe x =>
    change ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion x : OnePoint
      Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) ∈
      Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet) ↔ _
    rw [Hyperbolic.poincareHalfSpaceSet_coe]
    simp [Hyperbolic.QuaternionHalfSpace.extendedUpperHalfSpaceSet, Hyperbolic.QuaternionHalfSpace.upperHalfSpaceSet,
      Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion_height]

theorem cayleyEuclideanHomeomorph_preimage_ball :
    Hyperbolic.poincareHalfSpaceSet 2 1 =
      cayleyEuclideanHomeomorph ⁻¹' (Inversive.extendedUnitBall :
        Set (Inversive.ExtendedEuclidean 3)) := by
  rw [← quaternionChart_preimage_halfSpace, cayleyExtendedHomeomorph_preimage_ball,
    ← quaternionChart_preimage_ball]
  ext x
  simp only [Set.mem_preimage, cayleyExtendedHomeomorph, Homeomorph.trans_apply,
    Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.symm_apply_apply]

theorem cayleyEuclideanHomeomorph_image_halfSpace :
    cayleyEuclideanHomeomorph '' Hyperbolic.poincareHalfSpaceSet 2 1 =
      (Inversive.extendedUnitBall : Set (Inversive.ExtendedEuclidean 3)) := by
  rw [cayleyEuclideanHomeomorph_preimage_ball,
    Set.image_preimage_eq _ cayleyEuclideanHomeomorph.surjective]

/-- The source ball-model transformation is the genuine Euclidean Cayley conjugate. -/
def mobiusBallConjugate (f : complexMobiusGroup) : Inversive.ExtendedHomeomorph 3 :=
  cayleyEuclideanHomeomorph * (mobiusGeometricPoincare f : Inversive.ExtendedHomeomorph 3) *
    cayleyEuclideanHomeomorph⁻¹

theorem mobiusBallConjugate_mem (f : complexMobiusGroup) :
    mobiusBallConjugate f ∈ Inversive.generalMobiusGroup 3 :=
  (Inversive.generalMobiusGroup 3).mul_mem
    ((Inversive.generalMobiusGroup 3).mul_mem cayleyEuclideanHomeomorph_mem_generalMobiusGroup
      (mobiusGeometricPoincare f).property)
    ((Inversive.generalMobiusGroup 3).inv_mem cayleyEuclideanHomeomorph_mem_generalMobiusGroup)

theorem mobiusBallConjugate_preservesBall (f : complexMobiusGroup) :
    Inversive.PreservesUnitBall (mobiusBallConjugate f) := by
  have hi : cayleyEuclideanHomeomorph.symm '' (Inversive.extendedUnitBall :
      Set (Inversive.ExtendedEuclidean 3)) = Hyperbolic.poincareHalfSpaceSet 2 1 := by
    rw [cayleyEuclideanHomeomorph_preimage_ball]
    exact cayleyEuclideanHomeomorph.symm.image_eq_preimage_symm _
  change (cayleyEuclideanHomeomorph ∘
    (mobiusGeometricPoincare f : Inversive.ExtendedHomeomorph 3) ∘
      cayleyEuclideanHomeomorph.symm) '' Inversive.extendedUnitBall = _
  calc
    _ = cayleyEuclideanHomeomorph ''
        ((mobiusGeometricPoincare f : Inversive.ExtendedHomeomorph 3) ''
          (cayleyEuclideanHomeomorph.symm '' Inversive.extendedUnitBall)) := by
      rw [Set.image_image, Set.image_image]
      rfl
    _ = _ := by rw [hi, mobiusGeometricPoincare_preservesHalfSpaces f 1,
      cayleyEuclideanHomeomorph_image_halfSpace]


/-- The native geometric Cayley transformation sends the actual point j to zero. -/
theorem cayleyEuclideanHomeomorph_j :
    cayleyEuclideanHomeomorph
      ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val : Inversive.Euclidean 3) :
        Inversive.ExtendedEuclidean 3) = (0 : Inversive.Euclidean 3) := by
  apply Hyperbolic.QuaternionHalfSpace.extendedEuclideanThreeQuaternion.injective
  change cayleyExtendedHomeomorph (Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val : OnePoint
    Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) =
    (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion 0 : OnePoint
      Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace)
  rw [cayleyExtendedHomeomorph_coe _ (quaternionCayley_denominator_ne_zero
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ),
    cayleyCoordinate_j, map_zero]

/-- Conjugation transfers fixing j to fixing the Euclidean ball centre. -/
theorem mobiusBallConjugate_fix_zero_iff (f : complexMobiusGroup) :
    mobiusBallConjugate f (0 : Inversive.Euclidean 3) = (0 : Inversive.Euclidean 3) ↔
      f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
  have hc := cayleyEuclideanHomeomorph_j
  have hi : cayleyEuclideanHomeomorph.symm (0 : Inversive.Euclidean 3) =
      ((Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val : Inversive.Euclidean 3) :
        Inversive.ExtendedEuclidean 3) := by
    rw [← hc, cayleyEuclideanHomeomorph.symm_apply_apply]
  change cayleyEuclideanHomeomorph
    ((mobiusGeometricPoincare f : Inversive.ExtendedHomeomorph 3)
      (cayleyEuclideanHomeomorph.symm (0 : Inversive.Euclidean 3))) =
        (0 : Inversive.Euclidean 3) ↔ _
  rw [hi, mobiusGeometricPoincare_apply, ← hc, cayleyEuclideanHomeomorph.injective.eq_iff]
  constructor
  · intro h
    have he := OnePoint.coe_injective h
    apply Subtype.ext
    exact Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm.injective he
  · intro h
    rw [h]

/-- The geometric ball conjugate is orthogonal linear exactly when the original map fixes j. -/
theorem mobiusBallConjugate_orthogonal_iff_fixJ (f : complexMobiusGroup) :
    (∃ L : Inversive.Euclidean 3 ≃ₗᵢ[ℝ] Inversive.Euclidean 3,
      mobiusBallConjugate f = Inversive.cartanLinearExtensionHom L) ↔
      f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ := by
  constructor
  · rintro ⟨L, hL⟩
    apply (mobiusBallConjugate_fix_zero_iff f).mp
    rw [hL]
    change ((L 0 : Inversive.Euclidean 3) : Inversive.ExtendedEuclidean 3) = _
    rw [map_zero]
  · intro hf
    exact Inversive.ball_preserving_fix_zero_linearIsometry _ (mobiusBallConjugate_mem f)
      (mobiusBallConjugate_preservesBall f) ((mobiusBallConjugate_fix_zero_iff f).mpr hf)


/-- The fixed-j criterion is equivalent to isometry for the actual sphere-induced chordal metric. -/
theorem mobius_fixJ_iff_chordal_isometry (f : complexMobiusGroup) :
    (f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) ↔
      (letI := complexChordalMetricSpace; Isometry (f : Equiv.Perm ExtendedComplex)) := by
  obtain ⟨A, rfl⟩ := mobiusSpecialLinearProjection_surjective f
  rw [mobiusSpecialLinearProjection_fixJ_iff]
  exact unitary_iff_fractionalLinear_chordal_isometry A

/--
All five conditions, for the actual geometric Mobius group.
The ball condition is a global orthogonal real linear action of the genuine Cayley conjugate.
-/
theorem mobius_origin_stabilizer_unitary_norm_orthogonal_chordal_equivalences (f : complexMobiusGroup) :
    ((∃ A : Auxiliary.Algebra.SpecialLinear2, mobiusSpecialLinearProjection A = f ∧
      Auxiliary.Algebra.UnitaryMatrix (A : Auxiliary.Algebra.ComplexMatrix2)) ↔ f •
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) ∧
    ((f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) ↔
      mobiusNormalizedNorm f ^ 2 = 2) ∧
    ((f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) ↔
      ∃ L : Inversive.Euclidean 3 ≃ₗᵢ[ℝ] Inversive.Euclidean 3,
        mobiusBallConjugate f = Inversive.cartanLinearExtensionHom L) ∧
    ((f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ = Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ) ↔
      (letI := complexChordalMetricSpace; Isometry (f : Equiv.Perm ExtendedComplex))) := by
  exact ⟨(mobius_fixJ_iff_unitary_representative f).symm, mobius_fixJ_iff_norm f,
    (mobiusBallConjugate_orthogonal_iff_fixJ f).symm, mobius_fixJ_iff_chordal_isometry f⟩



theorem quaternion_linear_j_norm_sq (a b : ℂ) :
    ‖(a : ℍ) * Hyperbolic.QuaternionHalfSpace.quaternionJ + (b : ℍ)‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self]
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Hyperbolic.QuaternionHalfSpace.quaternionJ, Quaternion.normSq_def']
  ring

theorem quaternion_dist_j_sq (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    dist q Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val ^ 2 = ‖q‖ ^ 2 + 1 - 2 *
      Hyperbolic.QuaternionHalfSpace.quaternionHeight q := by
  rw [dist_eq_norm]
  change ‖(q : ℍ) - Hyperbolic.QuaternionHalfSpace.quaternionJ‖ ^ 2 = ‖(q : ℍ)‖ ^ 2 + 1 - 2 *
    Hyperbolic.QuaternionHalfSpace.quaternionHeight q
  rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self,
    pow_two, ← Quaternion.normSq_eq_norm_mul_self]
  simp [Hyperbolic.QuaternionHalfSpace.quaternionJ, Quaternion.normSq_def',
    Hyperbolic.QuaternionHalfSpace.quaternionHeight]
  ring

/-- The norm of the image of j follows from the multiplicative quaternion norm. -/
theorem poincareSpecialLinearMap_j_norm_sq (A : Auxiliary.Algebra.SpecialLinear2) :
    ‖(poincareSpecialLinearMap A Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).val‖ ^ 2 =
      (‖(A : Auxiliary.Algebra.ComplexMatrix2) 0 0‖ ^ 2 + ‖(A : Auxiliary.Algebra.ComplexMatrix2) 0 1‖ ^ 2) /
        (‖(A : Auxiliary.Algebra.ComplexMatrix2) 1 0‖ ^ 2 + ‖(A : Auxiliary.Algebra.ComplexMatrix2) 1 1‖ ^ 2) := by
  change ‖((poincareSpecialLinearMap A Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).val : ℍ)‖ ^ 2 = _
  rw [poincareSpecialLinearMap_quaternion]
  unfold quaternionMatrixExpression
  rw [upperHalfSpaceJ_quaternion, norm_mul, norm_inv, mul_pow, inv_pow,
    quaternion_linear_j_norm_sq, quaternion_linear_j_norm_sq]
  rfl

/-- Exact Euclidean separation from j, before invoking the hyperbolic metric formula. -/
theorem poincareSpecialLinearMap_j_separation (A : Auxiliary.Algebra.SpecialLinear2) :
    Auxiliary.Algebra.matrixNorm (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 = 2 +
      dist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val (poincareSpecialLinearMap A
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).val ^ 2 /
        Hyperbolic.QuaternionHalfSpace.quaternionHeight (poincareSpecialLinearMap A
          Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).val := by
  let D : ℝ := ‖(A : Auxiliary.Algebra.ComplexMatrix2) 1 0‖ ^ 2 + ‖(A : Auxiliary.Algebra.ComplexMatrix2) 1 1‖ ^ 2
  have hD : 0 < D := by
    have h := poincareDenominator_pos (A : Auxiliary.Algebra.ComplexMatrix2) (by simp) 0 1 zero_lt_one
    simpa [poincareDenominator, D, add_comm] using h
  have ht : Hyperbolic.QuaternionHalfSpace.quaternionHeight (poincareSpecialLinearMap A
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).val = 1 / D := by
    simp [poincareSpecialLinearMap, poincareMatrixMap_height, poincareHeight,
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ_horizontal,
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ_height, poincareDenominator, D, add_comm]
  rw [dist_comm Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val, quaternion_dist_j_sq,
    poincareSpecialLinearMap_j_norm_sq, ht, Auxiliary.Algebra.matrixNorm_sq]
  dsimp only [D] at hD ⊢
  field_simp [ne_of_gt hD]
  ring


/-- The coordinate model is the same open manifold as the generic actual hyperbolic half-space. -/
def upperHalfSpaceHyperbolicHomeomorph : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace ≃ₜ
    Hyperbolic.HyperbolicHalfSpace 2 :=
  Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm.toHomeomorph.subtype (fun q => by
    change (0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight q) ↔ 0 <
      (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm q) (Fin.last 2)
    rw [euclideanThreeQuaternion_symm_height])

@[simp] theorem upperHalfSpaceHyperbolicHomeomorph_val (q : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    (upperHalfSpaceHyperbolicHomeomorph q).val = Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm
      q.val := rfl

/-- The geometric H3 distance is the genuine reciprocal-height path metric, in quaternion coordinates. -/
def upperHalfSpacePathDist (q r : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) : ℝ :=
  Hyperbolic.halfSpacePathDist (upperHalfSpaceHyperbolicHomeomorph q)
    (upperHalfSpaceHyperbolicHomeomorph r)

/-- The Frobenius norm determines the actual Euclidean height-normalized separation at j. -/
theorem mobius_norm_sq_separation (f : complexMobiusGroup) :
    mobiusNormalizedNorm f ^ 2 = 2 + Hyperbolic.poincareSeparation
      (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val)
      (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm (f •
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).val) := by
  obtain ⟨A, rfl⟩ := mobiusSpecialLinearProjection_surjective f
  rw [mobiusNormalizedNorm_specialLinearProjection, mobiusUpperHalfSpace_smul,
    mobiusPoincareHom_specialLinearProjection]
  change Auxiliary.Algebra.matrixNorm (A : Auxiliary.Algebra.ComplexMatrix2) ^ 2 = 2 + Hyperbolic.poincareSeparation
    (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val)
    (Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.symm (poincareSpecialLinearMap A
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).val)
  unfold Hyperbolic.poincareSeparation
  rw [← Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.dist_map,
    Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply,
    Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply, euclideanThreeQuaternion_symm_height,
    euclideanThreeQuaternion_symm_height, Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ_height, one_mul]
  exact poincareSpecialLinearMap_j_separation A


/-- The quaternion Mobius action is the native geometric action on the true hyperbolic manifold. -/
theorem upperHalfSpaceHyperbolicHomeomorph_smul (f : complexMobiusGroup) (q :
    Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    upperHalfSpaceHyperbolicHomeomorph (f • q) =
      Hyperbolic.poincareHalfSpaceHomeomorph (mobiusRealRepresentative f)
        (upperHalfSpaceHyperbolicHomeomorph q) := by
  apply Subtype.ext
  apply OnePoint.coe_injective
  rw [Hyperbolic.poincareHalfSpaceHomeomorph_apply]
  exact (mobiusGeometricPoincare_apply f q).symm

/-- The actual geometric Mobius action preserves the genuine reciprocal-height path distance. -/
theorem upperHalfSpacePathDist_smul (f : complexMobiusGroup) (q r : Hyperbolic.QuaternionHalfSpace.UpperHalfSpace) :
    upperHalfSpacePathDist (f • q) (f • r) = upperHalfSpacePathDist q r := by
  unfold upperHalfSpacePathDist
  rw [upperHalfSpaceHyperbolicHomeomorph_smul, upperHalfSpaceHyperbolicHomeomorph_smul,
    Hyperbolic.poincareHalfSpaceHomeomorph_pathDist]



/-- The Cayley denominator norm is the squared distance from j plus four times the height. -/
theorem quaternion_sum_j_norm_sq (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    ‖(q : ℍ) + Hyperbolic.QuaternionHalfSpace.quaternionJ‖ ^ 2 = dist q
      Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val ^ 2 + 4 * Hyperbolic.QuaternionHalfSpace.quaternionHeight
      q := by
  rw [quaternion_dist_j_sq]
  change ‖(q : ℍ) + Hyperbolic.QuaternionHalfSpace.quaternionJ‖ ^ 2 = ‖(q : ℍ)‖ ^ 2 + 1 -
    2 * Hyperbolic.QuaternionHalfSpace.quaternionHeight q + 4 * Hyperbolic.QuaternionHalfSpace.quaternionHeight q
  rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self,
    pow_two, ← Quaternion.normSq_eq_norm_mul_self]
  simp [Hyperbolic.QuaternionHalfSpace.quaternionJ, Quaternion.normSq_def',
    Hyperbolic.QuaternionHalfSpace.quaternionHeight]
  ring

/-- The actual Cayley ball radius is determined by the separation from j. -/
theorem cayleyCoordinate_norm_sq_distance (q : Hyperbolic.QuaternionHalfSpace.quaternionThreeSpace) :
    ‖cayleyCoordinate q‖ ^ 2 = dist q Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val ^ 2 /
      (dist q Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val ^ 2 + 4 *
        Hyperbolic.QuaternionHalfSpace.quaternionHeight q) := by
  change ‖(cayleyCoordinate q : ℍ)‖ ^ 2 = _
  rw [← quaternionCayleyExpression_coordinates, quaternionCayleyExpression_norm_sq,
    quaternion_sum_j_norm_sq]
  congr 1
  rw [dist_eq_norm]
  rfl

/-- With the actual Cayley ball homeomorphism and original Mobius action. -/
theorem mobius_cayley_j_norm_sq (f : complexMobiusGroup) :
    ‖(upperHalfSpaceBallHomeomorph (f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)).val‖ ^ 2 =
      (mobiusNormalizedNorm f ^ 2 - 2) / (mobiusNormalizedNorm f ^ 2 + 2) := by
  rw [upperHalfSpaceBallHomeomorph_apply, cayleyCoordinate_norm_sq_distance]
  have hs := mobius_norm_sq_separation f
  unfold Hyperbolic.poincareSeparation at hs
  rw [← Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.dist_map,
    Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply,
    Hyperbolic.QuaternionHalfSpace.euclideanThreeQuaternion.apply_symm_apply, euclideanThreeQuaternion_symm_height,
    euclideanThreeQuaternion_symm_height, Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ_height, one_mul,
    dist_comm Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val] at hs
  rw [hs]
  have ht : 0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight (f •
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).val := (f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).property
  have hd : 0 < dist (f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).val
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ.val ^ 2 +
      4 * Hyperbolic.QuaternionHalfSpace.quaternionHeight (f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).val
        := by positivity
  field_simp [ne_of_gt ht, ne_of_gt hd]
  ring


/-- For the genuine reciprocal-height path distance on the actual H3 model. -/
theorem mobiusNormalizedNorm_sq_eq_two_cosh_origin_displacement (f : complexMobiusGroup) :
    mobiusNormalizedNorm f ^ 2 =
      2 * Real.cosh (upperHalfSpacePathDist Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ (f •
        Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ)) := by
  rw [upperHalfSpacePathDist, Hyperbolic.halfSpacePathDist_cosh (by norm_num : 1 ≤ 2),
    upperHalfSpaceHyperbolicHomeomorph_val, upperHalfSpaceHyperbolicHomeomorph_val,
    Hyperbolic.halfSpaceHeight_apply, Hyperbolic.halfSpaceHeight_apply,
    euclideanThreeQuaternion_symm_height, euclideanThreeQuaternion_symm_height,
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ_height, mul_one]
  have hs := mobius_norm_sq_separation f
  unfold Hyperbolic.poincareSeparation at hs
  rw [euclideanThreeQuaternion_symm_height, euclideanThreeQuaternion_symm_height,
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ_height, one_mul, dist_eq_norm] at hs
  rw [hs]
  have ht : 0 < Hyperbolic.QuaternionHalfSpace.quaternionHeight (f •
    Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).val := (f • Hyperbolic.QuaternionHalfSpace.upperHalfSpaceJ).property
  field_simp [ne_of_gt ht]

end
end LowDimensionalTopology.Geometry.Mobius
