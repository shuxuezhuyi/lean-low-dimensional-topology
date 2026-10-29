module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchyPolynomial
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.ParabolicEllipticNormalForms
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Tactic.Convert
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Normalization of the angular Cauchy integrals at infinity

Inversion transfers the actual continuous weighted first integral at zero
to its quadratic quotient at infinity. A finite three-node kernel identity
identifies the same quadratic coefficient in the actual integral correction.
The resulting subquadratic normalization makes that correction unique.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set MeasureTheory Filter Polynomial Bornology Asymptotics
open scoped Classical Topology ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

private def cauchyInversion : Deck :=
  Hyperbolic.hRotationSL 0 (-1) (by norm_num)

private theorem inversion_mul_entries (γ : Deck) :
    (γ * cauchyInversion) 0 0 = γ 0 1 ∧
      (γ * cauchyInversion) 0 1 = -γ 0 0 ∧
      (γ * cauchyInversion) 1 0 = γ 1 1 ∧
      (γ * cauchyInversion) 1 1 = -γ 1 0 := by
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  simp [cauchyInversion, Hyperbolic.hRotationSL, Matrix.mul_apply, Fin.sum_univ_two]

private theorem eventually_ne_zero : ∀ᶠ w : ℂ in cobounded ℂ, w ≠ 0 := by
  have h : ({(0 : ℂ)}ᶜ : Set ℂ) ∈ cobounded ℂ :=
    isBounded_def.mp (isBounded_singleton (x := (0 : ℂ)))
  filter_upwards [h] with w hw
  simpa only [mem_compl_iff, mem_singleton_iff] using hw

private theorem weighted_div_sq_inversion (θ : Width) (γ : Deck) {w : ℂ}
    (hw : w ≠ 0) :
    weightedFirstCauchyTerm θ γ w / w ^ 2 =
      weightedFirstCauchyTerm θ (γ * cauchyInversion) (-(w⁻¹)) := by
  obtain ⟨h00, h01, h10, h11⟩ := inversion_mul_entries γ
  let a : ℂ := γ 0 0
  let b : ℂ := γ 0 1
  let c : ℂ := γ 1 0
  let d : ℂ := γ 1 1
  have hn : b * (-(w⁻¹)) - a = -(a * w + b) / w := by
    field_simp [hw]
    ring
  have hd : d * (-(w⁻¹)) - c = -(c * w + d) / w := by
    field_simp [hw]
    ring
  simp only [weightedFirstCauchyTerm, h00, h01, h10, h11, Complex.ofReal_neg]
  change (c * w + d) ^ 2 * firstCauchyTerm θ ((a * w + b) / (c * w + d)) / w ^ 2 =
    (d * (-(w⁻¹)) - c) ^ 2 *
      firstCauchyTerm θ ((b * (-(w⁻¹)) - a) / (d * (-(w⁻¹)) - c))
  rw [hn, hd, div_div_div_comm, div_self hw, div_one, neg_div_neg_eq, div_pow, neg_sq]
  ring

private theorem weighted_inversion_zero (θ : Width) (γ : Deck) :
    weightedFirstCauchyTerm θ (γ * cauchyInversion) 0 =
      (γ 1 0 : ℂ) ^ 2 * firstCauchyTerm θ ((γ 0 0 : ℂ) / γ 1 0) := by
  obtain ⟨h00, h01, h10, h11⟩ := inversion_mul_entries γ
  simp [weightedFirstCauchyTerm, LiZhongQC.mobiusFn, h00, h01, h10, h11]

/-- Every actual weighted first integral has its quadratic limit at infinity,
including when the lower-left matrix entry is zero. -/
theorem tendsto_weightedFirstCauchyTerm_div_sq (θ : Width) (γ : Deck) :
    Tendsto (fun w : ℂ => weightedFirstCauchyTerm θ γ w / w ^ 2)
      (cobounded ℂ)
      (𝓝 ((γ 1 0 : ℂ) ^ 2 * firstCauchyTerm θ ((γ 0 0 : ℂ) / γ 1 0))) := by
  have hinv : Tendsto (fun w : ℂ => -(w⁻¹)) (cobounded ℂ) (𝓝 0) := by
    simpa only [neg_zero] using (Filter.tendsto_inv₀_cobounded (α := ℂ)).neg
  have hlim := ((continuous_weightedFirstCauchyTerm θ (γ * cauchyInversion)).tendsto 0).comp hinv
  have heq : (fun w : ℂ => weightedFirstCauchyTerm θ (γ * cauchyInversion) (-(w⁻¹)))
      =ᶠ[cobounded ℂ] (fun w => weightedFirstCauchyTerm θ γ w / w ^ 2) := by
    filter_upwards [eventually_ne_zero] with w hw
    exact (weighted_div_sq_inversion θ γ hw).symm
  simpa only [weighted_inversion_zero] using hlim.congr' heq

/-- The actual first integral has subquadratic quotient at infinity. -/
theorem tendsto_firstCauchyTerm_div_sq (θ : Width) :
    Tendsto (fun w : ℂ => firstCauchyTerm θ w / w ^ 2) (cobounded ℂ) (𝓝 0) := by
  simpa [weightedFirstCauchyTerm, LiZhongQC.mobiusFn] using
    tendsto_weightedFirstCauchyTerm_div_sq θ 1

/-- The original first integral satisfies the quadratic little-o normalization. -/
theorem firstCauchyTerm_isLittleO_sq_norm (θ : Width) :
    (fun w : ℂ => firstCauchyTerm θ w) =o[cobounded ℂ] (fun w => ‖w‖ ^ 2) := by
  have hz : ∀ᶠ w : ℂ in cobounded ℂ, w ^ 2 = 0 → firstCauchyTerm θ w = 0 :=
    eventually_ne_zero.mono fun w hw h => (pow_ne_zero 2 hw h).elim
  have h := (Asymptotics.isLittleO_iff_tendsto' hz).mpr
    (tendsto_firstCauchyTerm_div_sq θ)
  simpa only [norm_pow] using h.norm_right

private theorem eval_of_natDegree_le_two (p : Polynomial ℂ) (hp : p.natDegree ≤ 2) (w : ℂ) :
    p.eval w = p.coeff 0 + p.coeff 1 * w + p.coeff 2 * w ^ 2 := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hp)]
  norm_num [Finset.sum_range_succ]

private theorem coeff_two_of_natDegree_le_two (p : Polynomial ℂ) (hp : p.natDegree ≤ 2) :
    p.coeff 2 = Complex.I * p.eval 0 + ((1 - Complex.I) / 2) * p.eval 1 -
      ((1 + Complex.I) / 2) * p.eval (-Complex.I) := by
  rw [eval_of_natDegree_le_two p hp 0, eval_of_natDegree_le_two p hp 1,
    eval_of_natDegree_le_two p hp (-Complex.I)]
  norm_num only [zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero, one_pow,
    mul_one, neg_sq, Complex.I_sq, mul_neg]
  linear_combination -(p.coeff 1 / 2) * Complex.I_sq

private theorem tendsto_polynomial_div_sq (p : Polynomial ℂ) (hp : p.natDegree ≤ 2) :
    Tendsto (fun w : ℂ => p.eval w / w ^ 2) (cobounded ℂ) (𝓝 (p.coeff 2)) := by
  have hinv := Filter.tendsto_inv₀_cobounded (α := ℂ)
  have hlim : Tendsto (fun w : ℂ => p.coeff 0 * (w⁻¹) ^ 2 + p.coeff 1 * w⁻¹ + p.coeff 2)
      (cobounded ℂ) (𝓝 (p.coeff 2)) := by
    simpa only [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add] using
      (((hinv.pow 2).const_mul (p.coeff 0)).add
        (hinv.const_mul (p.coeff 1))).add_const (p.coeff 2)
  apply hlim.congr'
  filter_upwards [eventually_ne_zero] with w hw
  rw [eval_of_natDegree_le_two p hp w]
  field_simp [hw]

private def coefficientKernel (γ : Deck) (z η : ℂ) : ℂ :=
  ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 * Quasiconformal.firstVariationKernel
    (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) η -
      transportedCauchyKernel γ z η

private theorem coefficientKernel_three_nodes (γ : Deck) {η : ℂ}
    (hη : η ∈ LiZhongQC.upperHalf) :
    Complex.I * coefficientKernel γ 0 η +
        ((1 - Complex.I) / 2) * coefficientKernel γ 1 η -
        ((1 + Complex.I) / 2) * coefficientKernel γ (-Complex.I) η =
      (γ 1 0 : ℂ) ^ 2 * Quasiconformal.firstVariationKernel
        ((γ 0 0 : ℂ) / γ 1 0) η := by
  let a : ℂ := γ 0 0
  let b : ℂ := γ 0 1
  let c : ℂ := γ 1 0
  let d : ℂ := γ 1 1
  let s : ℂ := a - c * η
  let v : ℂ := d * η - b
  let u : ℂ := v - s
  obtain ⟨hden, hmem⟩ := inverseMobius_halfPlane_data γ hη
  have heS : (-(γ 1 0 : ℂ)) * η + γ 0 0 = s := by dsimp only [s, a, c]; ring
  have hs : s ≠ 0 := by rwa [heS] at hden
  have hS : LiZhongQC.mobiusFn (γ 1 1) (-(γ 0 1 : ℂ))
      (-(γ 1 0 : ℂ)) (γ 0 0) η = v / s := by
    dsimp only [LiZhongQC.mobiusFn, v, s, a, b, c, d]
    congr 1
  have hSη : 0 < (v / s).im := by
    rw [hS] at hmem
    dsimp only [LiZhongQC.upperHalf] at hmem
    convert! hmem using 1
  have hv : v ≠ 0 := by
    intro he
    simp [he] at hSη
  have hu : u ≠ 0 := by
    intro he
    have hvs : v = s := sub_eq_zero.mp he
    rw [hvs, div_self hs] at hSη
    simp at hSη
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
  have hL (r : ℂ) (hr : r.im ≤ 0) : v - s * r ≠ 0 := by
    intro he
    have heq : v / s = r := (div_eq_iff hs).2 (by
      have hh := sub_eq_zero.mp he
      simpa only [mul_comm] using hh)
    rw [heq] at hSη
    exact (not_lt_of_ge hr) hSη
  have hG (r : ℂ) (hr : r.im ≤ 0) :
      coefficientKernel γ r η =
        (c * r + d) * (a * r + b) * (a * r + b - (c * r + d)) /
            (η * (η - 1) * (v - s * r)) -
          r * (r - 1) / (s * v * u * (v - s * r)) := by
    let L : ℂ := v - s * r
    let q : ℂ := c * r + d
    let A : ℂ := a * r + b
    have heL : q * η - A = L := by dsimp only [q, A, L, v, s]; ring
    have hQ := firstVariationKernel_weighted_fraction A q η hη0 hη1
      (by rw [heL]; exact hL r hr)
    have hT : transportedCauchyKernel γ r η =
        r * (r - 1) / (s * v * u * L) := by
      change (1 / ((-(γ 1 0 : ℂ)) * η + γ 0 0) ^ 2) ^ 2 *
        Quasiconformal.firstVariationKernel r
          (LiZhongQC.mobiusFn (γ 1 1) (-(γ 0 1 : ℂ)) (-(γ 1 0 : ℂ)) (γ 0 0) η) = _
      rw [heS, hS]
      exact firstVariationKernel_inverse_fraction s v r hs hv hu (hL r hr)
    change q ^ 2 * Quasiconformal.firstVariationKernel (A / q) η -
      transportedCauchyKernel γ r η = _
    rw [hQ, heL, hT]
  have hquad (r : ℂ) (hr : r.im ≤ 0) :
      coefficientKernel γ r η =
        -3 * c / s ^ 3 + 3 * c ^ 2 * (v - s * r) / s ^ 3 -
          c ^ 3 * (v - s * r) ^ 2 / s ^ 3 +
          (v + u - (v - s * r)) / (s ^ 3 * v * u) -
          (c * r + d) ^ 2 * (2 * η - 1) / (η * (η - 1)) +
          (c * r + d) * (v - s * r) / (η * (η - 1)) := by
    let L : ℂ := v - s * r
    let q : ℂ := c * r + d
    have hA : a * r + b = η * q - L := by dsimp only [q, L, v, s]; ring
    have hfrac : coefficientKernel γ r η =
        q * (η * q - L) * ((η - 1) * q - L) / (η * (η - 1) * L) -
          r * (r - 1) / (s * v * u * L) := by
      rw [hG r hr]
      change q * (a * r + b) * (a * r + b - q) / (η * (η - 1) * L) -
        r * (r - 1) / (s * v * u * L) = _
      rw [hA]
      ring
    have hq : q = (1 - c * L) / s := by
      apply (eq_div_iff hs).2
      dsimp only [q, L]
      linear_combination hdet
    have hprod : r * (r - 1) = (v - L) * (u - L) / s ^ 2 := by
      dsimp only [L, u]
      field_simp [hs]
      ring
    rw [hfrac]
    change q * (η * q - L) * ((η - 1) * q - L) / (η * (η - 1) * L) -
        r * (r - 1) / (s * v * u * L) =
      -3 * c / s ^ 3 + 3 * c ^ 2 * L / s ^ 3 - c ^ 3 * L ^ 2 / s ^ 3 +
        (v + u - L) / (s ^ 3 * v * u) - q ^ 2 * (2 * η - 1) / (η * (η - 1)) +
        q * L / (η * (η - 1))
    rw [hprod, hq]
    field_simp [hs, hv, hu, hL r hr, hη0, hη1]
    have hLn : L ≠ 0 := hL r hr
    apply (div_eq_iff hLn).2
    clear_value a b c d s v u L q
    ring
  have hca : c * η - a = -s := by dsimp only [s]; ring
  have hcL : c * η - a ≠ 0 := by rw [hca]; exact neg_ne_zero.mpr hs
  have ha : a = s + c * η := by dsimp only [s]; ring
  calc
    Complex.I * coefficientKernel γ 0 η +
        ((1 - Complex.I) / 2) * coefficientKernel γ 1 η -
        ((1 + Complex.I) / 2) * coefficientKernel γ (-Complex.I) η =
      -c ^ 3 / s - c ^ 2 * (2 * η - 1) / (η * (η - 1)) -
        c * s / (η * (η - 1)) := by
      rw [hquad 0 (by simp), hquad 1 (by simp), hquad (-Complex.I) (by norm_num)]
      clear_value a b c d s v u
      field_simp [hs, hv, hu, hη0, hη1]
      ring_nf (config := { zetaDelta := false })
      simp only [Complex.I_sq, Complex.I_pow_three]; ring
    _ = c ^ 2 * Quasiconformal.firstVariationKernel (a / c) η := by
      rw [firstVariationKernel_weighted_fraction a c η hη0 hη1 hcL, hca, ha]
      clear_value a b c d s v u
      field_simp [hs, hη0, hη1]
      ring

private theorem integrableOn_coefficientKernel (θ : Width) (γ : Deck) (z : ℂ) :
    IntegrableOn (fun η => infinitesimalZeroExtension θ η * coefficientKernel γ z η)
      LiZhongQC.upperHalf (volume : Measure ℂ) := by
  have hQ : IntegrableOn (fun η => ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 *
      (infinitesimalZeroExtension θ η * Quasiconformal.firstVariationKernel
        (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) η))
      LiZhongQC.upperHalf (volume : Measure ℂ) :=
    ((integrable_infinitesimalZeroExtension_mul_firstVariationKernel θ
      (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z)).const_mul
        (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2)).integrableOn
  have hT := (pullbackCauchyTerm_change_variables θ γ z).1
  exact (hQ.sub hT).congr_fun
    (fun η _ => by simp only [Pi.sub_apply, coefficientKernel]; ring)
    LiZhongQC.isOpen_upperHalf.measurableSet

private theorem weightedDiff_eq_integral (θ : Width) (γ : Deck) (z : ℂ) :
    weightedFirstCauchyTerm θ γ z - pullbackCauchyTerm θ γ z =
      -(1 / (Real.pi : ℂ)) * ∫ η in LiZhongQC.upperHalf,
        infinitesimalZeroExtension θ η * coefficientKernel γ z η := by
  have hQ : IntegrableOn (fun η => ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 *
      (infinitesimalZeroExtension θ η * Quasiconformal.firstVariationKernel
        (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) η))
      LiZhongQC.upperHalf (volume : Measure ℂ) :=
    ((integrable_infinitesimalZeroExtension_mul_firstVariationKernel θ
      (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z)).const_mul
        (((γ 1 0 : ℂ) * z + γ 1 1) ^ 2)).integrableOn
  have hT := (pullbackCauchyTerm_change_variables θ γ z).1
  have heq : (fun η => infinitesimalZeroExtension θ η * coefficientKernel γ z η) =
      (fun η => ((γ 1 0 : ℂ) * z + γ 1 1) ^ 2 *
        (infinitesimalZeroExtension θ η * Quasiconformal.firstVariationKernel
          (LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) z) η) -
        infinitesimalZeroExtension θ η * transportedCauchyKernel γ z η) := by
    funext η
    dsimp only [coefficientKernel]
    ring
  rw [weightedFirstCauchyTerm, firstCauchyTerm_eq_upperHalfPlane,
    (pullbackCauchyTerm_change_variables θ γ z).2, heq,
    integral_sub hQ hT, integral_const_mul]
  dsimp only [LiZhongQC.upperHalf]
  ring

/-- The actual quadratic correction has the same coefficient as the
quadratic limit of the weighted first integral, for every real determinant-one matrix. -/
theorem coeff_two_quadraticCauchyCorrection (θ : Width) (γ : Deck) :
    (quadraticCauchyCorrection θ γ).coeff 2 =
      (γ 1 0 : ℂ) ^ 2 * firstCauchyTerm θ ((γ 0 0 : ℂ) / γ 1 0) := by
  let α₀ : ℂ := Complex.I
  let α₁ : ℂ := (1 - Complex.I) / 2
  let α₂ : ℂ := (1 + Complex.I) / 2
  let C : ℂ := (γ 1 0 : ℂ) ^ 2
  let A : ℂ := (γ 0 0 : ℂ) / γ 1 0
  have h₀ := integrableOn_coefficientKernel θ γ 0
  have h₁ := integrableOn_coefficientKernel θ γ 1
  have h₂ := integrableOn_coefficientKernel θ γ (-Complex.I)
  have hint : (∫ η in LiZhongQC.upperHalf, infinitesimalZeroExtension θ η *
      (α₀ * coefficientKernel γ 0 η + α₁ * coefficientKernel γ 1 η -
        α₂ * coefficientKernel γ (-Complex.I) η)) =
      α₀ * (∫ η in LiZhongQC.upperHalf, infinitesimalZeroExtension θ η * coefficientKernel γ 0 η) +
        α₁ * (∫ η in LiZhongQC.upperHalf, infinitesimalZeroExtension θ η * coefficientKernel γ 1 η) -
        α₂ * (∫ η in LiZhongQC.upperHalf,
          infinitesimalZeroExtension θ η * coefficientKernel γ (-Complex.I) η) := by
    have heq : (fun η => infinitesimalZeroExtension θ η *
        (α₀ * coefficientKernel γ 0 η + α₁ * coefficientKernel γ 1 η -
          α₂ * coefficientKernel γ (-Complex.I) η)) =
        (fun η => α₀ * (infinitesimalZeroExtension θ η * coefficientKernel γ 0 η) +
          α₁ * (infinitesimalZeroExtension θ η * coefficientKernel γ 1 η) -
          α₂ * (infinitesimalZeroExtension θ η * coefficientKernel γ (-Complex.I) η)) := by
      funext η
      ring
    have hs : IntegrableOn (fun η =>
        α₀ * (infinitesimalZeroExtension θ η * coefficientKernel γ 0 η) +
          α₁ * (infinitesimalZeroExtension θ η * coefficientKernel γ 1 η))
        LiZhongQC.upperHalf (volume : Measure ℂ) :=
      IntegrableOn.congr_fun ((h₀.const_mul α₀).add (h₁.const_mul α₁))
        (fun η _ => by simp only [Pi.add_apply]) LiZhongQC.isOpen_upperHalf.measurableSet
    rw [heq, integral_sub hs (h₂.const_mul α₂),
      integral_add (h₀.const_mul α₀) (h₁.const_mul α₁)]
    simp only [integral_const_mul]
  have hk : (∫ η in LiZhongQC.upperHalf, infinitesimalZeroExtension θ η *
      (α₀ * coefficientKernel γ 0 η + α₁ * coefficientKernel γ 1 η -
        α₂ * coefficientKernel γ (-Complex.I) η)) =
      ∫ η in LiZhongQC.upperHalf,
        infinitesimalZeroExtension θ η * (C * Quasiconformal.firstVariationKernel A η) := by
    apply setIntegral_congr_fun LiZhongQC.isOpen_upperHalf.measurableSet
    intro η hη
    exact congrArg (fun u : ℂ => infinitesimalZeroExtension θ η * u)
      (coefficientKernel_three_nodes γ hη)
  calc
    (quadraticCauchyCorrection θ γ).coeff 2 = -(1 / (Real.pi : ℂ)) *
        (α₀ * (∫ η in LiZhongQC.upperHalf, infinitesimalZeroExtension θ η * coefficientKernel γ 0 η) +
          α₁ * (∫ η in LiZhongQC.upperHalf, infinitesimalZeroExtension θ η * coefficientKernel γ 1 η) -
          α₂ * (∫ η in LiZhongQC.upperHalf,
            infinitesimalZeroExtension θ η * coefficientKernel γ (-Complex.I) η)) := by
      rw [coeff_two_of_natDegree_le_two _ (natDegree_quadraticCauchyCorrection_le_two θ γ),
        ← weightedFirstCauchyTerm_sub_pullbackCauchyTerm_eq_polynomial θ γ 0,
        ← weightedFirstCauchyTerm_sub_pullbackCauchyTerm_eq_polynomial θ γ 1,
        ← weightedFirstCauchyTerm_sub_pullbackCauchyTerm_eq_polynomial θ γ (-Complex.I),
        weightedDiff_eq_integral θ γ 0, weightedDiff_eq_integral θ γ 1,
        weightedDiff_eq_integral θ γ (-Complex.I)]
      dsimp only [α₀, α₁, α₂]
      ring
    _ = -(1 / (Real.pi : ℂ)) * ∫ η in LiZhongQC.upperHalf,
        infinitesimalZeroExtension θ η * (C * Quasiconformal.firstVariationKernel A η) := by
      rw [← hint, hk]
    _ = C * firstCauchyTerm θ A := by
      rw [firstCauchyTerm_eq_upperHalfPlane]
      have heq : (fun η => infinitesimalZeroExtension θ η *
          (C * Quasiconformal.firstVariationKernel A η)) =
          (fun η => C * (infinitesimalZeroExtension θ η * Quasiconformal.firstVariationKernel A η)) := by
        funext η
        ring
      rw [heq, integral_const_mul]
      dsimp only [LiZhongQC.upperHalf]
      ring

/-- The actual transported integral has vanishing quadratic quotient at infinity. -/
theorem tendsto_pullbackCauchyTerm_div_sq (θ : Width) (γ : Deck) :
    Tendsto (fun w : ℂ => pullbackCauchyTerm θ γ w / w ^ 2)
      (cobounded ℂ) (𝓝 0) := by
  have hQ := tendsto_weightedFirstCauchyTerm_div_sq θ γ
  have hP := tendsto_polynomial_div_sq (quadraticCauchyCorrection θ γ)
    (natDegree_quadraticCauchyCorrection_le_two θ γ)
  rw [coeff_two_quadraticCauchyCorrection] at hP
  have heq : (fun w : ℂ => weightedFirstCauchyTerm θ γ w / w ^ 2 -
      (quadraticCauchyCorrection θ γ).eval w / w ^ 2) =
      (fun w => pullbackCauchyTerm θ γ w / w ^ 2) := by
    funext w
    rw [← sub_div]
    have hw : weightedFirstCauchyTerm θ γ w -
        (quadraticCauchyCorrection θ γ).eval w = pullbackCauchyTerm θ γ w := by
      linear_combination weightedFirstCauchyTerm_sub_pullbackCauchyTerm_eq_polynomial θ γ w
    rw [hw]
  have hlim := hQ.sub hP
  rw [heq] at hlim
  simpa only [sub_self] using hlim

/-- Every actual transported angular integral has the quadratic little-o normalization. -/
theorem pullbackCauchyTerm_isLittleO_sq_norm (θ : Width) (γ : Deck) :
    (fun w : ℂ => pullbackCauchyTerm θ γ w) =o[cobounded ℂ] (fun w => ‖w‖ ^ 2) := by
  have hz : ∀ᶠ w : ℂ in cobounded ℂ, w ^ 2 = 0 → pullbackCauchyTerm θ γ w = 0 :=
    eventually_ne_zero.mono fun w hw h => (pow_ne_zero 2 hw h).elim
  have h := (Asymptotics.isLittleO_iff_tendsto' hz).mpr
    (tendsto_pullbackCauchyTerm_div_sq θ γ)
  simpa only [norm_pow] using h.norm_right

private theorem correction_unique (θ : Width) (γ : Deck) (p : Polynomial ℂ)
    (hp : p.natDegree ≤ 2)
    (h0 : weightedFirstCauchyTerm θ γ 0 - p.eval 0 = 0)
    (h1 : weightedFirstCauchyTerm θ γ 1 - p.eval 1 = 0)
    (hsmall : (fun w : ℂ => weightedFirstCauchyTerm θ γ w - p.eval w)
      =o[cobounded ℂ] (fun w => ‖w‖ ^ 2)) :
    p = quadraticCauchyCorrection θ γ := by
  have hs : (fun w : ℂ => weightedFirstCauchyTerm θ γ w - p.eval w)
      =o[cobounded ℂ] (fun w => w ^ 2) := by
    rw [← Asymptotics.isLittleO_norm_right]
    simpa only [norm_pow] using hsmall
  have hpactual : Tendsto (fun w : ℂ => p.eval w / w ^ 2) (cobounded ℂ)
      (𝓝 ((γ 1 0 : ℂ) ^ 2 * firstCauchyTerm θ ((γ 0 0 : ℂ) / γ 1 0))) := by
    simpa only [sub_div, sub_sub_cancel, sub_zero] using
      (tendsto_weightedFirstCauchyTerm_div_sq θ γ).sub hs.tendsto_div_nhds_zero
  have hc2 : p.coeff 2 = (quadraticCauchyCorrection θ γ).coeff 2 := by
    have h := tendsto_nhds_unique (tendsto_polynomial_div_sq p hp) hpactual
    simpa only [coeff_two_quadraticCauchyCorrection] using h
  have he0 : p.eval 0 = (quadraticCauchyCorrection θ γ).eval 0 := by
    have hn := weightedFirstCauchyTerm_sub_pullbackCauchyTerm_eq_polynomial θ γ 0
    rw [pullbackCauchyTerm_zero, sub_zero] at hn
    exact (sub_eq_zero.mp h0).symm.trans hn
  have he1 : p.eval 1 = (quadraticCauchyCorrection θ γ).eval 1 := by
    have hn := weightedFirstCauchyTerm_sub_pullbackCauchyTerm_eq_polynomial θ γ 1
    rw [pullbackCauchyTerm_one, sub_zero] at hn
    exact (sub_eq_zero.mp h1).symm.trans hn
  have hc0 : p.coeff 0 = (quadraticCauchyCorrection θ γ).coeff 0 := by
    simpa only [← Polynomial.coeff_zero_eq_eval_zero] using he0
  have hsum : p.coeff 0 + p.coeff 1 + p.coeff 2 =
      (quadraticCauchyCorrection θ γ).coeff 0 +
        (quadraticCauchyCorrection θ γ).coeff 1 +
        (quadraticCauchyCorrection θ γ).coeff 2 := by
    simpa only [eval_of_natDegree_le_two p hp 1,
      eval_of_natDegree_le_two _ (natDegree_quadraticCauchyCorrection_le_two θ γ) 1,
      one_pow, mul_one] using he1
  have hc1 : p.coeff 1 = (quadraticCauchyCorrection θ γ).coeff 1 := by
    linear_combination hsum - hc0 - hc2
  apply Polynomial.funext
  intro w
  rw [eval_of_natDegree_le_two p hp w,
    eval_of_natDegree_le_two _ (natDegree_quadraticCauchyCorrection_le_two θ γ) w,
    hc0, hc1, hc2]

/-- The quadratic polynomial in the normalized angular integral formula. -/
def cauchyNormalizationPolynomial (θ : Width) (γ : Deck) : Polynomial ℂ :=
  Polynomial.C (2 * (Real.pi : ℂ) * Complex.I) * quadraticCauchyCorrection θ γ

/-- The normalization polynomial has degree at most two. -/
theorem natDegree_cauchyNormalizationPolynomial_le_two (θ : Width) (γ : Deck) :
    (cauchyNormalizationPolynomial θ γ).natDegree ≤ 2 := by
  calc
    _ ≤ (Polynomial.C (2 * (Real.pi : ℂ) * Complex.I)).natDegree +
        (quadraticCauchyCorrection θ γ).natDegree := Polynomial.natDegree_mul_le
    _ ≤ 2 := by
      simpa only [Polynomial.natDegree_C, zero_add] using
        natDegree_quadraticCauchyCorrection_le_two θ γ

/-- The actual integral equals the weighted first term plus its concrete
quadratic normalization, including at finite real Möbius poles. -/
theorem pullbackCauchyTerm_eq_weighted_add_polynomial (θ : Width) (γ : Deck) (z : ℂ) :
    pullbackCauchyTerm θ γ z = weightedFirstCauchyTerm θ γ z +
      (Complex.I / (2 * (Real.pi : ℂ))) * (cauchyNormalizationPolynomial θ γ).eval z := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [cauchyNormalizationPolynomial, Polynomial.eval_mul, Polynomial.eval_C,
    ← weightedFirstCauchyTerm_sub_pullbackCauchyTerm_eq_polynomial θ γ z]
  field_simp [hπ]
  ring_nf
  simp [Complex.I_sq]

/-- The actual polynomial produces both finite normalizations and subquadratic growth. -/
theorem cauchyNormalizationPolynomial_normalized (θ : Width) (γ : Deck) :
    (weightedFirstCauchyTerm θ γ 0 + (Complex.I / (2 * (Real.pi : ℂ))) *
      (cauchyNormalizationPolynomial θ γ).eval 0 = 0) ∧
    (weightedFirstCauchyTerm θ γ 1 + (Complex.I / (2 * (Real.pi : ℂ))) *
      (cauchyNormalizationPolynomial θ γ).eval 1 = 0) ∧
    (fun w : ℂ => weightedFirstCauchyTerm θ γ w + (Complex.I / (2 * (Real.pi : ℂ))) *
      (cauchyNormalizationPolynomial θ γ).eval w) =o[cobounded ℂ] (fun w => ‖w‖ ^ 2) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← pullbackCauchyTerm_eq_weighted_add_polynomial, pullbackCauchyTerm_zero]
  · rw [← pullbackCauchyTerm_eq_weighted_add_polynomial, pullbackCauchyTerm_one]
  · have heq : (fun w : ℂ => weightedFirstCauchyTerm θ γ w + (Complex.I / (2 * (Real.pi : ℂ))) *
        (cauchyNormalizationPolynomial θ γ).eval w) = pullbackCauchyTerm θ γ :=
      funext fun w => (pullbackCauchyTerm_eq_weighted_add_polynomial θ γ w).symm
    rw [heq]
    exact pullbackCauchyTerm_isLittleO_sq_norm θ γ

/-- The endpoint and quadratic little-o normalizations uniquely determine
the polynomial of degree at most two for each fixed matrix. -/
theorem cauchyNormalizationPolynomial_unique (θ : Width) (γ : Deck) (P : Polynomial ℂ)
    (hP : P.natDegree ≤ 2)
    (h0 : weightedFirstCauchyTerm θ γ 0 + (Complex.I / (2 * (Real.pi : ℂ))) * P.eval 0 = 0)
    (h1 : weightedFirstCauchyTerm θ γ 1 + (Complex.I / (2 * (Real.pi : ℂ))) * P.eval 1 = 0)
    (hsmall : (fun w : ℂ => weightedFirstCauchyTerm θ γ w +
      (Complex.I / (2 * (Real.pi : ℂ))) * P.eval w)
      =o[cobounded ℂ] (fun w => ‖w‖ ^ 2)) :
    P = cauchyNormalizationPolynomial θ γ := by
  let q : Polynomial ℂ := Polynomial.C (-(Complex.I / (2 * (Real.pi : ℂ)))) * P
  have hq : q.natDegree ≤ 2 := by
    calc
      _ ≤ (Polynomial.C (-(Complex.I / (2 * (Real.pi : ℂ))))).natDegree + P.natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 2 := by simpa only [Polynomial.natDegree_C, zero_add] using hP
  have heq (z : ℂ) : weightedFirstCauchyTerm θ γ z - q.eval z =
      weightedFirstCauchyTerm θ γ z + (Complex.I / (2 * (Real.pi : ℂ))) * P.eval z := by
    simp only [q, Polynomial.eval_mul, Polynomial.eval_C]
    ring
  have hq0 : weightedFirstCauchyTerm θ γ 0 - q.eval 0 = 0 := by rw [heq]; exact h0
  have hq1 : weightedFirstCauchyTerm θ γ 1 - q.eval 1 = 0 := by rw [heq]; exact h1
  have hqsmall : (fun w : ℂ => weightedFirstCauchyTerm θ γ w - q.eval w)
      =o[cobounded ℂ] (fun w => ‖w‖ ^ 2) := by
    simpa only [heq] using hsmall
  have hqc := correction_unique θ γ q hq hq0 hq1 hqsmall
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hscalar : (2 * (Real.pi : ℂ) * Complex.I) *
      (-(Complex.I / (2 * (Real.pi : ℂ)))) = 1 := by
    field_simp [hπ]
    ring_nf
    simp [Complex.I_sq]
  calc
    P = Polynomial.C (2 * (Real.pi : ℂ) * Complex.I) * q := by
      dsimp only [q]
      rw [← mul_assoc, ← Polynomial.C_mul, hscalar, Polynomial.C_1, one_mul]
    _ = Polynomial.C (2 * (Real.pi : ℂ) * Complex.I) * quadraticCauchyCorrection θ γ :=
      congrArg (fun r : Polynomial ℂ => Polynomial.C (2 * (Real.pi : ℂ) * Complex.I) * r) hqc
    _ = cauchyNormalizationPolynomial θ γ := rfl

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
