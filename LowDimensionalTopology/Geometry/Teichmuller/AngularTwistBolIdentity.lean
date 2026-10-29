module

public import LowDimensionalTopology.Geometry.Teichmuller.AngularTwistCauchyNormalization
public import LowDimensionalTopology.External.LiZhongQC.Ch10.S33_BersEmbedding
public import Mathlib.Analysis.Calculus.Deriv.Polynomial
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# The finite Bol identity for an angular Cauchy term

On the lower half-plane the actual real Möbius map avoids the logarithm's
cut. Its determinant-one identity reduces three derivatives of the
quadratic logarithmic product to the negative squared logarithmic derivative.
The quadratic correction in the actual Cauchy integral has zero third derivative.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Polynomial
open scoped Topology

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)
local notation "Deck" => Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- Bol's identity for the actual real determinant-one map, at every lower-half-plane point. -/
theorem iteratedDeriv_three_mobius_log (γ : Deck) {z : ℂ}
    (hz : z ∈ LiZhongQC.lowerHalf) :
    let m := LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
    iteratedDeriv 3 (fun w => (m w / deriv m w) * Complex.log (m w)) z =
      -(deriv m z / m z) ^ 2 := by
  let m : ℂ → ℂ := LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
  change iteratedDeriv 3 (fun w => (m w / deriv m w) * Complex.log (m w)) z = _
  let a : ℂ := γ 0 0
  let b : ℂ := γ 0 1
  let c : ℂ := γ 1 0
  let d : ℂ := γ 1 1
  let A : ℂ → ℂ := fun w => a * w + b
  let q : ℂ → ℂ := fun w => c * w + d
  let P : ℂ → ℂ := fun w => A w * q w
  let P₁ : ℂ → ℂ := fun w => a * q w + A w * c
  let F : ℂ → ℂ := fun w => P w * Complex.log (m w)
  let G : ℂ → ℂ := fun w => P₁ w * Complex.log (m w) + 1
  let H : ℂ → ℂ := fun w => (2 * a * c) * Complex.log (m w) + P₁ w / P w
  have hq (w : ℂ) (hw : w ∈ LiZhongQC.lowerHalf) : q w ≠ 0 :=
    LiZhongQC.bg2_a_den_ne γ hw
  have hm (w : ℂ) (hw : w ∈ LiZhongQC.lowerHalf) :
      HasDerivAt m (1 / q w ^ 2) w := by
    have h := LiZhongQC.hasDerivAt_mobiusFn
      (a := (γ 0 0 : ℂ)) (b := (γ 0 1 : ℂ)) (LiZhongQC.bg2_a_den_ne γ hw)
    rw [LiZhongQC.h23l_b_det γ] at h
    exact h
  have hA (w : ℂ) (hw : w ∈ LiZhongQC.lowerHalf) : A w ≠ 0 := by
    have hmw : (A w / q w).im < 0 := LiZhongQC.bg2_a_mem γ hw
    intro he
    simp only [he, zero_div, Complex.zero_im, lt_self_iff_false] at hmw
  have hP (w : ℂ) (hw : w ∈ LiZhongQC.lowerHalf) : P w ≠ 0 :=
    mul_ne_zero (hA w hw) (hq w hw)
  have hlog (w : ℂ) (hw : w ∈ LiZhongQC.lowerHalf) :
      HasDerivAt (fun v => Complex.log (m v)) (1 / P w) w := by
    have hslit : m w ∈ Complex.slitPlane :=
      Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_lt (LiZhongQC.bg2_a_mem γ hw)))
    have he : (1 / q w ^ 2) / m w = 1 / P w := by
      change (1 / q w ^ 2) / (A w / q w) = 1 / (A w * q w)
      field_simp [hq w hw, hA w hw]
    simpa only [he] using (hm w hw).clog hslit
  have hAd (w : ℂ) : HasDerivAt A a w := by
    change HasDerivAt (fun v : ℂ => a * v + b) a w
    apply HasDerivAt.add_const
    exact hasDerivAt_const_mul a
  have hqd (w : ℂ) : HasDerivAt q c w := by
    change HasDerivAt (fun v : ℂ => c * v + d) c w
    apply HasDerivAt.add_const
    exact hasDerivAt_const_mul c
  have hPd (w : ℂ) : HasDerivAt P (P₁ w) w := (hAd w).mul (hqd w)
  have hP₁d (w : ℂ) : HasDerivAt P₁ (2 * a * c) w := by
    convert ((hqd w).const_mul a).add ((hAd w).mul_const c) using 1
    ring
  have hFG (w : ℂ) (hw : w ∈ LiZhongQC.lowerHalf) : HasDerivAt F (G w) w := by
    convert (hPd w).mul (hlog w hw) using 1
    dsimp only [G]
    field_simp [hP w hw]
  have hGH (w : ℂ) (hw : w ∈ LiZhongQC.lowerHalf) : HasDerivAt G (H w) w := by
    convert ((hP₁d w).mul (hlog w hw)).add_const 1 using 1
    dsimp only [H]
    ring
  have hdet : a * q z - A z * c = 1 := by
    calc
      _ = a * d - b * c := by dsimp only [A, q]; ring
      _ = 1 := LiZhongQC.h23l_b_det γ
  have hbol : 4 * a * c * P z - P₁ z ^ 2 = -1 := by
    calc
      _ = -(a * q z - A z * c) ^ 2 := by dsimp only [P, P₁]; ring
      _ = -1 := by rw [hdet]; ring
  have hc : (2 * a * c) * (1 / P z) +
      ((2 * a * c) * P z - P₁ z * P₁ z) / P z ^ 2 = -(1 / P z ^ 2) := by
    calc
      _ = (4 * a * c * P z - P₁ z ^ 2) / P z ^ 2 := by
        field_simp [hP z hz]; ring
      _ = _ := by rw [hbol]; ring
  have hH : HasDerivAt H (-(1 / P z ^ 2)) z := by
    convert ((hlog z hz).const_mul (2 * a * c)).add
      ((hP₁d z).div (hPd z) (hP z hz)) using 1
    exact hc.symm
  have e1 : ∀ w ∈ LiZhongQC.lowerHalf, deriv F =ᶠ[𝓝 w] G := by
    intro w hw
    filter_upwards [LiZhongQC.isOpen_lowerHalf.mem_nhds hw] with v hv
    exact (hFG v hv).deriv
  have e2 : deriv (deriv F) =ᶠ[𝓝 z] H := by
    filter_upwards [LiZhongQC.isOpen_lowerHalf.mem_nhds hz] with w hw
    rw [(e1 w hw).deriv_eq]
    exact (hGH w hw).deriv
  have hthird : iteratedDeriv 3 F z = -(1 / P z ^ 2) := by
    have he : deriv (deriv (deriv F)) z = -(1 / P z ^ 2) := by
      rw [e2.deriv_eq, hH.deriv]
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using he
  have heq : (fun w => (m w / deriv m w) * Complex.log (m w)) =ᶠ[𝓝 z] F := by
    filter_upwards [LiZhongQC.isOpen_lowerHalf.mem_nhds hz] with w hw
    have hr : m w / deriv m w = P w := by
      rw [(hm w hw).deriv]
      change (A w / q w) / (1 / q w ^ 2) = A w * q w
      field_simp [hq w hw]
    exact congrArg (fun v : ℂ => v * Complex.log (m w)) hr
  have hr : (deriv m z / m z) ^ 2 = 1 / P z ^ 2 := by
    rw [(hm z hz).deriv]
    change ((1 / q z ^ 2) / (A z / q z)) ^ 2 = 1 / (A z * q z) ^ 2
    field_simp [hq z hz, hA z hz]
  rw [Filter.EventuallyEq.iteratedDeriv_eq 3 heq, hthird, hr]

/-- The actual transported angular Cauchy integral has its positive Bol third derivative. -/
theorem iteratedDeriv_three_pullbackCauchyTerm (θ : Width) (γ : Deck) {z : ℂ}
    (hz : z ∈ LiZhongQC.lowerHalf) :
    let m := LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
    iteratedDeriv 3 (pullbackCauchyTerm θ γ) z =
      (Complex.I / (2 * (Real.pi : ℂ))) * (deriv m z / m z) ^ 2 := by
  let m : ℂ → ℂ := LiZhongQC.mobiusFn (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1)
  let T : ℂ → ℂ := fun w => (m w / deriv m w) * Complex.log (m w)
  let p : Polynomial ℂ := cauchyNormalizationPolynomial θ γ
  let k : ℂ := Complex.I / (2 * (Real.pi : ℂ))
  change iteratedDeriv 3 (pullbackCauchyTerm θ γ) z = k * (deriv m z / m z) ^ 2
  have hm (w : ℂ) (hw : w ∈ LiZhongQC.lowerHalf) :
      HasDerivAt m (1 / ((γ 1 0 : ℂ) * w + γ 1 1) ^ 2) w := by
    have h := LiZhongQC.hasDerivAt_mobiusFn
      (a := (γ 0 0 : ℂ)) (b := (γ 0 1 : ℂ)) (LiZhongQC.bg2_a_den_ne γ hw)
    rw [LiZhongQC.h23l_b_det γ] at h
    exact h
  have hmd : DifferentiableOn ℂ m LiZhongQC.lowerHalf :=
    fun w hw => (hm w hw).differentiableAt.differentiableWithinAt
  have hdm : ∀ w ∈ LiZhongQC.lowerHalf, deriv m w ≠ 0 := by
    intro w hw
    rw [(hm w hw).deriv]
    exact one_div_ne_zero (pow_ne_zero 2 (LiZhongQC.bg2_a_den_ne γ hw))
  have hlog : DifferentiableOn ℂ (fun w => Complex.log (m w)) LiZhongQC.lowerHalf :=
    hmd.clog fun w hw => Complex.mem_slitPlane_iff.mpr
      (Or.inr (ne_of_lt (LiZhongQC.bg2_a_mem γ hw)))
  have hT : DifferentiableOn ℂ T LiZhongQC.lowerHalf :=
    (hmd.div (hmd.deriv LiZhongQC.isOpen_lowerHalf) hdm).mul hlog
  have hT₃ : ContDiffAt ℂ 3 T z :=
    (hT.contDiffOn LiZhongQC.isOpen_lowerHalf).contDiffAt
      (LiZhongQC.isOpen_lowerHalf.mem_nhds hz)
  have hp₃ : ContDiffAt ℂ 3 (fun w => p.eval w) z :=
    p.differentiable.contDiff.contDiffAt
  have hkT : ContDiffAt ℂ 3 (fun w => -k * T w) z := contDiffAt_const.mul hT₃
  have hkp : ContDiffAt ℂ 3 (fun w => k * p.eval w) z := contDiffAt_const.mul hp₃
  have hpzero : p.derivative.derivative.derivative = 0 := by
    simpa only [Function.iterate_succ_apply, Function.iterate_zero_apply] using
      (Polynomial.iterate_derivative_eq_zero (p := p) (x := 3)
        (Nat.lt_succ_of_le (natDegree_cauchyNormalizationPolynomial_le_two θ γ)))
  have heval (r : Polynomial ℂ) :
      deriv (fun w => r.eval w) = fun w => r.derivative.eval w :=
    funext fun w => r.deriv
  have hpderiv : iteratedDeriv 3 (fun w => p.eval w) z = 0 := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero, heval, hpzero, Polynomial.eval_zero]
  have heq : pullbackCauchyTerm θ γ =ᶠ[𝓝 z]
      (fun w => -k * T w + k * p.eval w) := by
    filter_upwards [LiZhongQC.isOpen_lowerHalf.mem_nhds hz] with w hw
    have harg : Complex.arg (m w) ≤ 0 :=
      (Complex.arg_neg_iff.mpr (LiZhongQC.bg2_a_mem γ hw)).le
    rw [pullbackCauchyTerm_eq_weighted_add_polynomial,
      weightedFirstCauchyTerm_eq_div_derivative θ γ (LiZhongQC.bg2_a_den_ne γ hw),
      firstCauchyTerm_eq_closedForm]
    change -m w * ((angularPrimitive θ (Complex.arg (m w)) : ℂ) +
        k * Complex.log (m w)) / deriv m w + k * p.eval w = -k * T w + k * p.eval w
    rw [angularPrimitive_eq_zero_of_nonpos θ harg]
    simp only [Complex.ofReal_zero, zero_add]
    dsimp only [T]
    ring
  rw [Filter.EventuallyEq.iteratedDeriv_eq 3 heq,
    iteratedDeriv_fun_add hkT hkp,
    iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field, hpderiv]
  have hbol := iteratedDeriv_three_mobius_log γ hz
  change iteratedDeriv 3 T z = -(deriv m z / m z) ^ 2 at hbol
  rw [hbol]
  ring

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
