module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchyTransport
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Quadratic normalization of the transported angular Cauchy integral

The difference of the two actual normalized kernels is quadratic in the
evaluation variable away from its moving pole. Three fixed nodes outside
the upper half-plane identify that quadratic. Genuine absolute
integrability permits the finite interpolation identity to be integrated.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Polynomial
open scoped Classical UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

private def forwardMap (γ : Deck) : ℂ → ℂ :=
  LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)

private def inverseMap (γ : Deck) : ℂ → ℂ :=
  LiZhongQC.mobiusFn (γ 1 1) (-(γ 0 1 : ℂ)) (-(γ 1 0 : ℂ)) (γ 0 0)

private def matrixWeight (γ : Deck) (z : ℂ) : ℂ := (γ 1 0 : ℂ) * z + γ 1 1

private def kernelDifference (γ : Deck) (z η : ℂ) : ℂ :=
  matrixWeight γ z ^ 2 * Quasiconformal.firstVariationKernel (forwardMap γ z) η -
    transportedCauchyKernel γ z η

/-- Three fixed interpolation nodes outside the upper half-plane. -/
def interpolationNodes : Finset ℂ := {0, 1, -Complex.I}

private theorem interpolationNodes_card : interpolationNodes.card = 3 := by
  norm_num [interpolationNodes, Complex.ext_iff]

private theorem interpolationNodes_not_upperHalf {r : ℂ} (hr : r ∈ interpolationNodes) :
    r ∉ LiZhongQC.upperHalf := by
  simp only [interpolationNodes, Finset.mem_insert, Finset.mem_singleton] at hr
  rcases hr with rfl | rfl | rfl <;> norm_num [LiZhongQC.upperHalf]

private theorem inverseMap_data (γ : Deck) {η : ℂ} (hη : η ∈ LiZhongQC.upperHalf) :
    (-(γ 1 0 : ℂ)) * η + γ 0 0 ≠ 0 ∧
      inverseMap γ η ∈ LiZhongQC.upperHalf ∧ forwardMap γ (inverseMap γ η) = η := by
  have hdetR : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using Matrix.SpecialLinearGroup.det_coe γ
  have hpos : 0 < γ 1 1 * γ 0 0 - (-γ 0 1) * (-γ 1 0) := by
    rw [show γ 1 1 * γ 0 0 - (-γ 0 1) * (-γ 1 0) =
      γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 by ring, hdetR]
    exact zero_lt_one
  have hden : (-(γ 1 0 : ℂ)) * η + γ 0 0 ≠ 0 := by
    simpa only [Complex.ofReal_neg] using
      (LiZhongQC.mobiusFn_den_ne_zero_real (ne_of_gt hpos) hη)
  have hmem : inverseMap γ η ∈ LiZhongQC.upperHalf := by
    simpa only [inverseMap, Complex.ofReal_neg] using
      (LiZhongQC.mobiusFn_mem_upperHalf hpos hη)
  have hdetC : (γ 1 1 : ℂ) * γ 0 0 - (-(γ 0 1 : ℂ)) * (-(γ 1 0 : ℂ)) = 1 := by
    calc _ = (γ 0 0 : ℂ) * γ 1 1 - (γ 0 1 : ℂ) * γ 1 0 := by ring
         _ = 1 := LiZhongQC.h23l_b_det γ
  refine ⟨hden, hmem, ?_⟩
  have h := LiZhongQC.mobiusFn_inv_apply
    (a := (γ 1 1 : ℂ)) (b := -(γ 0 1 : ℂ))
    (c := -(γ 1 0 : ℂ)) (d := (γ 0 0 : ℂ))
    (by rw [hdetC]; exact one_ne_zero) hden
  simpa only [forwardMap, inverseMap, neg_neg] using h

/-- The inverse real determinant-one Mobius map has a nonzero denominator
and preserves the actual upper half-plane. -/
theorem inverseMobius_halfPlane_data (γ : Deck) {η : ℂ}
    (hη : η ∈ LiZhongQC.upperHalf) :
    (-(γ 1 0 : ℂ)) * η + γ 0 0 ≠ 0 ∧
      LiZhongQC.mobiusFn (γ 1 1) (-(γ 0 1 : ℂ))
        (-(γ 1 0 : ℂ)) (γ 0 0) η ∈ LiZhongQC.upperHalf := by
  have h := inverseMap_data γ hη
  exact ⟨h.1, by simpa only [inverseMap] using h.2.1⟩

/-- A weighted normalized kernel has its fraction form, including at zero weight. -/
theorem firstVariationKernel_weighted_fraction (A q η : ℂ) (hη : η ≠ 0)
    (hη1 : η - 1 ≠ 0) (hL : q * η - A ≠ 0) :
    q ^ 2 * Quasiconformal.firstVariationKernel (A / q) η =
      q * A * (A - q) / (η * (η - 1) * (q * η - A)) := by
  by_cases hq : q = 0
  · simp [hq]
  · have he : η - A / q = (q * η - A) / q := by
      field_simp [hq]
    unfold Quasiconformal.firstVariationKernel
    rw [he]
    field_simp [hq, hη, hη1, hL]

/-- The inverse-substitution normalized kernel has its fraction form at nonzero denominators. -/
theorem firstVariationKernel_inverse_fraction (s v z : ℂ) (hs : s ≠ 0)
    (hv : v ≠ 0) (hu : v - s ≠ 0) (hL : v - s * z ≠ 0) :
    (1 / s ^ 2) ^ 2 * Quasiconformal.firstVariationKernel z (v / s) =
      z * (z - 1) / (s * v * (v - s) * (v - s * z)) := by
  have h1 : v / s - 1 = (v - s) / s := by field_simp [hs]
  have hz : v / s - z = (v - s * z) / s := by field_simp [hs]
  unfold Quasiconformal.firstVariationKernel
  rw [h1, hz]
  field_simp [hs, hv, hu, hL]

private def kernelPolynomial (s v u c d η : ℂ) : Polynomial ℂ :=
  let L : Polynomial ℂ := C v - C s * X
  let q : Polynomial ℂ := C c * X + C d
  C (-3 * c / s ^ 3) + C (3 * c ^ 2 / s ^ 3) * L - C (c ^ 3 / s ^ 3) * L ^ 2 +
    C ((v + u) / (s ^ 3 * v * u)) - C (1 / (s ^ 3 * v * u)) * L -
    C ((2 * η - 1) / (η * (η - 1))) * q ^ 2 + C (1 / (η * (η - 1))) * q * L

private theorem kernelPolynomial_natDegree_le (s v u c d η : ℂ) :
    (kernelPolynomial s v u c d η).natDegree ≤ 2 := by
  dsimp only [kernelPolynomial]
  compute_degree

private theorem kernelPolynomial_eval (s v u c d η z : ℂ) :
    (kernelPolynomial s v u c d η).eval z =
      -3 * c / s ^ 3 + 3 * c ^ 2 * (v - s * z) / s ^ 3 -
        c ^ 3 * (v - s * z) ^ 2 / s ^ 3 +
        (v + u - (v - s * z)) / (s ^ 3 * v * u) -
        (c * z + d) ^ 2 * (2 * η - 1) / (η * (η - 1)) +
        (c * z + d) * (v - s * z) / (η * (η - 1)) := by
  simp only [kernelPolynomial, Polynomial.eval_add, Polynomial.eval_sub,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X]
  ring

private theorem kernelDifference_eq_interpolation (γ : Deck) {η : ℂ}
    (hη : η ∈ LiZhongQC.upperHalf) (z : ℂ) (hz : z ≠ inverseMap γ η) :
    kernelDifference γ z η = ∑ r ∈ interpolationNodes,
      (Lagrange.basis interpolationNodes id r).eval z * kernelDifference γ r η := by
  let a : ℂ := γ 0 0
  let b : ℂ := γ 0 1
  let c : ℂ := γ 1 0
  let d : ℂ := γ 1 1
  let s : ℂ := a - c * η
  let v : ℂ := d * η - b
  let u : ℂ := v - s
  obtain ⟨hden, hSη, -⟩ := inverseMap_data γ hη
  have hs : s ≠ 0 := by
    have he : (-(γ 1 0 : ℂ)) * η + γ 0 0 = s := by dsimp only [s, a, c]; ring
    rwa [he] at hden
  have hS : inverseMap γ η = v / s := by
    dsimp only [inverseMap, LiZhongQC.mobiusFn, v, s, a, b, c, d]
    congr 1; ring
  have hS0 : inverseMap γ η ≠ 0 := by
    intro he
    have h : 0 < (inverseMap γ η).im := hSη
    rw [he] at h
    simp at h
  have hS1 : inverseMap γ η ≠ 1 := by
    intro he
    have h : 0 < (inverseMap γ η).im := hSη
    rw [he] at h
    simp at h
  have hv : v ≠ 0 := by
    intro he
    apply hS0
    rw [hS, he, zero_div]
  have hu : u ≠ 0 := by
    intro he
    have hv' : v = s := sub_eq_zero.mp he
    apply hS1
    rw [hS, hv', div_self hs]
  have hη0 : η ≠ 0 := by
    intro he
    have h : 0 < η.im := hη
    rw [he] at h
    simp at h
  have hη1 : η - 1 ≠ 0 := by
    intro he
    have h : 0 < η.im := hη
    rw [sub_eq_zero.mp he] at h
    simp at h
  have hdet : c * v + d * s = 1 := by
    calc _ = a * d - b * c := by dsimp only [v, s]; ring
         _ = 1 := LiZhongQC.h23l_b_det γ
  let p : Polynomial ℂ := kernelPolynomial s v u c d η
  have hp (w : ℂ) (hw : w ≠ inverseMap γ η) :
      kernelDifference γ w η = p.eval w := by
    let L : ℂ := v - s * w
    let q : ℂ := c * w + d
    let A : ℂ := a * w + b
    have hL : L ≠ 0 := by
      intro he
      apply hw
      rw [hS]
      apply (eq_div_iff hs).2
      have hvw : v = s * w := sub_eq_zero.mp he
      exact (mul_comm w s).trans hvw.symm
    have heL : q * η - A = L := by dsimp only [q, A, L, v, s]; ring
    have hQ := firstVariationKernel_weighted_fraction A q η hη0 hη1
      (by rw [heL]; exact hL)
    have hT : transportedCauchyKernel γ w η =
        w * (w - 1) / (s * v * u * L) := by
      change (1 / ((-(γ 1 0 : ℂ)) * η + γ 0 0) ^ 2) ^ 2 *
        Quasiconformal.firstVariationKernel w (inverseMap γ η) = _
      have he : (-(γ 1 0 : ℂ)) * η + γ 0 0 = s := by dsimp only [s, a, c]; ring
      rw [he, hS]
      exact firstVariationKernel_inverse_fraction s v w hs hv hu hL
    have hA : A = η * q - L := by dsimp only [A, q, L, v, s]; ring
    have hfrac : kernelDifference γ w η =
        q * (η * q - L) * ((η - 1) * q - L) / (η * (η - 1) * L) -
          w * (w - 1) / (s * v * u * L) := by
      change q ^ 2 * Quasiconformal.firstVariationKernel (A / q) η -
        transportedCauchyKernel γ w η = _
      rw [hQ, heL, hT, hA]
      ring
    have hq : q = (1 - c * L) / s := by
      apply (eq_div_iff hs).2
      dsimp only [q, L]
      calc (c * w + d) * s = c * s * w + d * s := by ring
           _ = 1 - c * (v - s * w) := by rw [← hdet]; ring
    have hprod : w * (w - 1) = (v - L) * (u - L) / s ^ 2 := by
      dsimp only [L, u]
      field_simp [hs]; ring
    rw [hfrac]
    dsimp only [p]
    rw [kernelPolynomial_eval]
    change q * (η * q - L) * ((η - 1) * q - L) / (η * (η - 1) * L) -
        w * (w - 1) / (s * v * u * L) =
      -3 * c / s ^ 3 + 3 * c ^ 2 * L / s ^ 3 - c ^ 3 * L ^ 2 / s ^ 3 +
        (v + u - L) / (s ^ 3 * v * u) - q ^ 2 * (2 * η - 1) / (η * (η - 1)) +
        q * L / (η * (η - 1))
    rw [hprod, hq]
    field_simp [hs, hv, hu, hL, hη0, hη1]; ring
  have hpdeg : p.degree < interpolationNodes.card := by
    have h := Polynomial.natDegree_le_iff_degree_le.mp
      (kernelPolynomial_natDegree_le s v u c d η)
    exact h.trans_lt (by rw [interpolationNodes_card]; norm_num)
  have hpnode (r : ℂ) (hr : r ∈ interpolationNodes) :
      p.eval r = kernelDifference γ r η := by
    apply (hp r ?_).symm
    intro he
    apply interpolationNodes_not_upperHalf hr
    rw [he]
    exact hSη
  have hpoly : p = Lagrange.interpolate interpolationNodes id
      (fun r => kernelDifference γ r η) :=
    Lagrange.eq_interpolate_of_eval_eq (fun r => kernelDifference γ r η)
      Function.injective_id.injOn hpdeg hpnode
  rw [hp z hz, hpoly]
  simp only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Polynomial.eval_C]
  exact Finset.sum_congr rfl (fun r _ => mul_comm _ _)

private theorem kernelDifference_eq_interpolation_ae (γ : Deck) (z : ℂ) :
    ∀ᵐ η ∂(volume.restrict LiZhongQC.upperHalf),
      kernelDifference γ z η = ∑ r ∈ interpolationNodes,
        (Lagrange.basis interpolationNodes id r).eval z * kernelDifference γ r η := by
  have hne : ∀ᵐ η : ℂ ∂volume, η ≠ forwardMap γ z := by
    simp [ae_iff, measure_singleton]
  filter_upwards [ae_restrict_mem LiZhongQC.isOpen_upperHalf.measurableSet,
    ae_restrict_of_ae hne] with η hη hηz
  apply kernelDifference_eq_interpolation γ hη z
  intro he
  apply hηz
  rw [he, (inverseMap_data γ hη).2.2]

/-- The first integral transformed as a vector field, with its zero value at a finite pole. -/
def weightedFirstCauchyTerm (θ : Width) (γ : Deck) (z : ℂ) : ℂ :=
  ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 * firstCauchyTerm θ
    (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z)

/-- The concrete quadratic interpolant of the actual normalization difference. -/
def quadraticCauchyCorrection (θ : Width) (γ : Deck) : Polynomial ℂ :=
  Lagrange.interpolate interpolationNodes id
    (fun r => weightedFirstCauchyTerm θ γ r - pullbackCauchyTerm θ γ r)

/-- The actual normalization correction has degree at most two. -/
theorem natDegree_quadraticCauchyCorrection_le_two (θ : Width) (γ : Deck) :
    (quadraticCauchyCorrection θ γ).natDegree ≤ 2 := by
  apply Polynomial.natDegree_le_iff_degree_le.mpr
  have h := Lagrange.degree_interpolate_le
    (fun r => weightedFirstCauchyTerm θ γ r - pullbackCauchyTerm θ γ r)
    (s := interpolationNodes) (v := id) Function.injective_id.injOn
  simpa only [quadraticCauchyCorrection, interpolationNodes_card] using h

private theorem integrableOn_weightedKernel (θ : Width) (γ : Deck) (z : ℂ) :
    IntegrableOn (fun η => matrixWeight γ z ^ 2 *
      (infinitesimalZeroExtension θ η * Quasiconformal.firstVariationKernel (forwardMap γ z) η))
      LiZhongQC.upperHalf (volume : Measure ℂ) :=
  ((integrable_infinitesimalZeroExtension_mul_firstVariationKernel θ (forwardMap γ z)).const_mul
    (matrixWeight γ z ^ 2)).integrableOn

private theorem integrableOn_kernelDifference (θ : Width) (γ : Deck) (z : ℂ) :
    IntegrableOn (fun η => infinitesimalZeroExtension θ η * kernelDifference γ z η)
      LiZhongQC.upperHalf (volume : Measure ℂ) := by
  have hQ := integrableOn_weightedKernel θ γ z
  have hT := (pullbackCauchyTerm_change_variables θ γ z).1
  exact (hQ.sub hT).congr_fun
    (fun η _ => by simp only [Pi.sub_apply, kernelDifference]; ring)
    LiZhongQC.isOpen_upperHalf.measurableSet

private theorem integral_kernelDifference (θ : Width) (γ : Deck) (z : ℂ) :
    weightedFirstCauchyTerm θ γ z - pullbackCauchyTerm θ γ z =
      -(1 / (Real.pi : ℂ)) * ∫ η in LiZhongQC.upperHalf,
        infinitesimalZeroExtension θ η * kernelDifference γ z η := by
  have hQ := integrableOn_weightedKernel θ γ z
  have hT := (pullbackCauchyTerm_change_variables θ γ z).1
  have heq : (fun η => infinitesimalZeroExtension θ η * kernelDifference γ z η) =
      (fun η => matrixWeight γ z ^ 2 * (infinitesimalZeroExtension θ η *
        Quasiconformal.firstVariationKernel (forwardMap γ z) η) -
        infinitesimalZeroExtension θ η * transportedCauchyKernel γ z η) := by
    funext η
    dsimp only [kernelDifference]
    ring
  change matrixWeight γ z ^ 2 * firstCauchyTerm θ (forwardMap γ z) -
    pullbackCauchyTerm θ γ z = _
  rw [firstCauchyTerm_eq_upperHalfPlane,
    (pullbackCauchyTerm_change_variables θ γ z).2, heq,
    integral_sub hQ hT, integral_const_mul]
  dsimp only [LiZhongQC.upperHalf]
  ring

/-- The actual transported integral and weighted first term differ by the concrete quadratic,
including at every finite real Möbius pole. -/
theorem weightedFirstCauchyTerm_sub_pullbackCauchyTerm_eq_polynomial
    (θ : Width) (γ : Deck) (z : ℂ) :
    weightedFirstCauchyTerm θ γ z - pullbackCauchyTerm θ γ z =
      (quadraticCauchyCorrection θ γ).eval z := by
  have hsum : (∫ η in LiZhongQC.upperHalf,
      infinitesimalZeroExtension θ η * kernelDifference γ z η) =
      ∑ r ∈ interpolationNodes, (Lagrange.basis interpolationNodes id r).eval z *
        ∫ η in LiZhongQC.upperHalf, infinitesimalZeroExtension θ η * kernelDifference γ r η := by
    calc
      _ = ∫ η in LiZhongQC.upperHalf, ∑ r ∈ interpolationNodes,
          (Lagrange.basis interpolationNodes id r).eval z *
            (infinitesimalZeroExtension θ η * kernelDifference γ r η) := by
        apply integral_congr_ae
        filter_upwards [kernelDifference_eq_interpolation_ae γ z] with η hη
        rw [hη, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun r _ => by ring)
      _ = _ := by
        rw [integral_finsetSum interpolationNodes
          (fun r _ => (integrableOn_kernelDifference θ γ r).const_mul
            ((Lagrange.basis interpolationNodes id r).eval z))]
        exact Finset.sum_congr rfl (fun r _ => integral_const_mul _ _)
  rw [integral_kernelDifference θ γ z, hsum, Finset.mul_sum]
  simp only [quadraticCauchyCorrection, Lagrange.interpolate_apply,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_congr rfl
  intro r hr
  rw [integral_kernelDifference θ γ r]
  ring

/-- Away from the real Möbius pole the weighted expression is the actual derivative quotient. -/
theorem weightedFirstCauchyTerm_eq_div_derivative (θ : Width) (γ : Deck) {z : ℂ}
    (hz : (γ 1 0 : ℂ) * z + γ 1 1 ≠ 0) :
    weightedFirstCauchyTerm θ γ z =
      firstCauchyTerm θ (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) /
        deriv (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)) z := by
  have hd := LiZhongQC.hasDerivAt_mobiusFn
    (a := (γ 0 0 : ℂ)) (b := (γ 0 1 : ℂ)) hz
  rw [LiZhongQC.h23l_b_det γ] at hd
  rw [weightedFirstCauchyTerm, hd.deriv]
  field_simp [hz]

/-- The zero-valued expression at a finite pole is the genuine continuous extension. -/
theorem continuous_weightedFirstCauchyTerm (θ : Width) (γ : Deck) :
    Continuous (weightedFirstCauchyTerm θ γ) := by
  have heq : weightedFirstCauchyTerm θ γ = fun z =>
      (quadraticCauchyCorrection θ γ).eval z + pullbackCauchyTerm θ γ z := by
    funext z
    exact sub_eq_iff_eq_add.mp
      (weightedFirstCauchyTerm_sub_pullbackCauchyTerm_eq_polynomial θ γ z)
  rw [heq]
  exact (quadraticCauchyCorrection θ γ).continuous.add (continuous_pullbackCauchyTerm θ γ)

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
