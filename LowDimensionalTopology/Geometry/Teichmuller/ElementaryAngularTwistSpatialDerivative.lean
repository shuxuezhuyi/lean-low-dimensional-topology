module

public import LowDimensionalTopology.Geometry.Teichmuller.ElementaryAngularTwist
public import LowDimensionalTopology.External.LiZhongQC.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Spatial derivatives of the same elementary angular map

The literal upper-half-plane map is read as a plane-valued function at its
interior points. On its three open angular pieces it has the original real
derivative, Wirtinger derivatives and coefficient quotient. The two boundary
rays and any whole-domain quasiconformality assertion are outside this leaf.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Set Filter Topology Complex
open scoped UpperHalfPlane ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.AngularTwist

local notation "Width" => Set.Ioo (0 : ℝ) (Real.pi / 2)

open scoped Classical in
/-- Plane values of the same elementary map, extended by zero outside H. -/
def elementaryMapPlane (θ : Width) (t : ℝ) (ζ : ℂ) : ℂ :=
  if hζ : 0 < ζ.im then (elementaryMap θ t (⟨ζ, hζ⟩ : ℍ) : ℂ) else 0

/-- At every original upper-half-plane point the value is exactly elementaryMap. -/
theorem elementaryMapPlane_coe (θ : Width) (t : ℝ) (z : ℍ) :
    elementaryMapPlane θ t (z : ℂ) = (elementaryMap θ t z : ℂ) := by
  classical
  unfold elementaryMapPlane
  exact dite_eq_left z.im_pos

private theorem hasFDerivAt_arg_upper (z : ℍ) :
    HasFDerivAt Complex.arg
      (Complex.imCLM.comp ((z : ℂ)⁻¹ • (1 : ℂ →L[ℝ] ℂ))) (z : ℂ) := by
  have hs : (z : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr z.im_pos.ne')
  simpa only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] using
    Complex.imCLM.hasFDerivAt.comp (z : ℂ)
      (Complex.hasStrictFDerivAt_log_real hs).hasFDerivAt

/-- Below the lower ray the same map has the identity spatial derivative. -/
theorem elementaryMapPlane_spatial_below
    (θ : Width) (t : ℝ) (z : ℍ)
    (hz : Complex.arg (z : ℂ) < Real.pi / 2 - (θ : ℝ)) :
    let W := elementaryMapPlane θ t
    HasFDerivAt W (1 : ℂ →L[ℝ] ℂ) (z : ℂ) ∧
      LiZhongQC.dz W (z : ℂ) = 1 ∧
      LiZhongQC.dzbar W (z : ℂ) = 0 ∧
      LiZhongQC.dz W (z : ℂ) ≠ 0 ∧
      LiZhongQC.complexDilatation W (z : ℂ) = coefficientCurve θ t z := by
  classical
  let W := elementaryMapPlane θ t
  have hs : (z : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr z.im_pos.ne')
  have him : ∀ᶠ ζ : ℂ in 𝓝 (z : ℂ), 0 < ζ.im :=
    (Complex.continuous_im.tendsto _).eventually (isOpen_Ioi.mem_nhds z.im_pos)
  have hang : ∀ᶠ ζ : ℂ in 𝓝 (z : ℂ), Complex.arg ζ < Real.pi / 2 - (θ : ℝ) :=
    (Complex.continuousAt_arg hs).eventually (isOpen_Iio.mem_nhds hz)
  have he : W =ᶠ[𝓝 (z : ℂ)] fun ζ : ℂ => ζ := by
    filter_upwards [him, hang] with ζ hζ harg
    change elementaryMapPlane θ t ζ = ζ
    rw [elementaryMapPlane, dite_eq_left hζ, coe_elementaryMap, ite_eq_left harg]
  have hD : HasFDerivAt W (ContinuousLinearMap.id ℝ ℂ) (z : ℂ) :=
    (hasFDerivAt_id (z : ℂ)).congr_of_eventuallyEq he
  have hdz : LiZhongQC.dz W (z : ℂ) = 1 := by
    rw [LiZhongQC.dz, hD.fderiv]
    simp only [ContinuousLinearMap.id_apply, Complex.I_mul_I]
    ring
  have hdzbar : LiZhongQC.dzbar W (z : ℂ) = 0 := by
    rw [LiZhongQC.dzbar, hD.fderiv]
    simp only [ContinuousLinearMap.id_apply, Complex.I_mul_I]
    ring
  have hnot : Complex.arg (z : ℂ) ∉ interval θ := by
    intro h
    exact (not_le_of_gt hz) h.1
  have hc : coefficientCurve θ t z = 0 := by
    simp only [coefficientCurve, ite_eq_right hnot]
  refine ⟨hD, hdz, hdzbar, ?_, ?_⟩
  · rw [hdz]
    exact one_ne_zero
  · calc
      _ = (0 : ℂ) / 1 := congrArg₂ (fun a b : ℂ => a / b) hdzbar hdz
      _ = 0 := zero_div _
      _ = coefficientCurve θ t z := hc.symm

/-- On the open middle piece the genuine spatial derivatives give the same tau. -/
theorem elementaryMapPlane_spatial_middle
    (θ : Width) (t : ℝ) (z : ℍ)
    (hlo : Real.pi / 2 - (θ : ℝ) < Complex.arg (z : ℂ))
    (hhi : Complex.arg (z : ℂ) < Real.pi / 2 + (θ : ℝ)) :
    let W := elementaryMapPlane θ t
    let ε := shear θ t
    let F : ℂ := (Real.exp
      (ε * (Complex.arg (z : ℂ) - Real.pi / 2 + (θ : ℝ))) : ℂ)
    let A : ℂ := F * (1 - Complex.I * (ε : ℂ) / 2)
    let B : ℂ := (z : ℂ) * F * (Complex.I * (ε : ℂ)) /
      (2 * conj (z : ℂ))
    HasFDerivAt W
        (A • (1 : ℂ →L[ℝ] ℂ) + B • (Complex.conjCLE : ℂ →L[ℝ] ℂ))
        (z : ℂ) ∧
      LiZhongQC.dz W (z : ℂ) = A ∧
      LiZhongQC.dzbar W (z : ℂ) = B ∧
      LiZhongQC.dz W (z : ℂ) ≠ 0 ∧
      LiZhongQC.complexDilatation W (z : ℂ) = coefficientCurve θ t z := by
  classical
  let W := elementaryMapPlane θ t
  let ε := shear θ t
  let F : ℂ := (Real.exp
    (ε * (Complex.arg (z : ℂ) - Real.pi / 2 + (θ : ℝ))) : ℂ)
  let A : ℂ := F * (1 - Complex.I * (ε : ℂ) / 2)
  let B : ℂ := (z : ℂ) * F * (Complex.I * (ε : ℂ)) / (2 * conj (z : ℂ))
  let L : ℂ →L[ℝ] ℝ :=
    Complex.imCLM.comp ((z : ℂ)⁻¹ • (ContinuousLinearMap.id ℝ ℂ))
  have hs : (z : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr z.im_pos.ne')
  have him : ∀ᶠ ζ : ℂ in 𝓝 (z : ℂ), 0 < ζ.im :=
    (Complex.continuous_im.tendsto _).eventually (isOpen_Ioi.mem_nhds z.im_pos)
  have hlow : ∀ᶠ ζ : ℂ in 𝓝 (z : ℂ),
      Real.pi / 2 - (θ : ℝ) < Complex.arg ζ :=
    (Complex.continuousAt_arg hs).eventually (isOpen_Ioi.mem_nhds hlo)
  have hhigh : ∀ᶠ ζ : ℂ in 𝓝 (z : ℂ),
      Complex.arg ζ < Real.pi / 2 + (θ : ℝ) :=
    (Complex.continuousAt_arg hs).eventually (isOpen_Iio.mem_nhds hhi)
  have he : W =ᶠ[𝓝 (z : ℂ)] fun ζ : ℂ =>
      ζ * (Real.exp (ε * (Complex.arg ζ - Real.pi / 2 + (θ : ℝ))) : ℂ) := by
    filter_upwards [him, hlow, hhigh] with ζ hζ hζlo hζhi
    change elementaryMapPlane θ t ζ = _
    rw [elementaryMapPlane, dite_eq_left hζ, coe_elementaryMap,
      ite_eq_right (not_lt.mpr hζlo.le), ite_eq_left hζhi.le]
  have harg : HasFDerivAt Complex.arg L (z : ℂ) := hasFDerivAt_arg_upper z
  have hreal := (((harg.sub_const (Real.pi / 2)).add_const (θ : ℝ)).const_mul ε).exp
  have hcomplex := Complex.ofRealCLM.hasFDerivAt.comp (z : ℂ) hreal
  have hproduct := (hasFDerivAt_id (z : ℂ)).mul hcomplex
  have hcz : conj (z : ℂ) ≠ 0 := by simpa using z.ne_zero
  have hbranch : HasFDerivAt
      (fun ζ : ℂ => ζ * (Real.exp
        (ε * (Complex.arg ζ - Real.pi / 2 + (θ : ℝ))) : ℂ))
      (A • ContinuousLinearMap.id ℝ ℂ + B • (Complex.conjCLE : ℂ →L[ℝ] ℂ))
      (z : ℂ) := by
    apply hproduct.congr_fderiv
    ext h
    simp only [id_eq, Function.comp_apply, add_apply, smul_apply,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, Complex.ofRealCLM_apply, L,
      Complex.imCLM_apply, smul_eq_mul, ContinuousLinearEquiv.coe_coe,
      Complex.conjCLE_apply, Complex.ofReal_mul]
    rw [show ((((z : ℂ)⁻¹ * h).im : ℝ) : ℂ) =
      Complex.I * (conj ((z : ℂ)⁻¹ * h) - (z : ℂ)⁻¹ * h) / 2 from
        RCLike.im_eq_conj_sub _]
    simp only [map_mul, map_inv₀]
    dsimp only [A, B, F]
    field_simp [z.ne_zero, hcz]
    ring
  have hD : HasFDerivAt W
      (A • ContinuousLinearMap.id ℝ ℂ + B • (Complex.conjCLE : ℂ →L[ℝ] ℂ))
      (z : ℂ) := hbranch.congr_of_eventuallyEq he
  have hdz : LiZhongQC.dz W (z : ℂ) = A := by
    rw [LiZhongQC.dz, hD.fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one, Complex.conj_I]
    linear_combination ((B - A) / 2) * Complex.I_sq
  have hdzbar : LiZhongQC.dzbar W (z : ℂ) = B := by
    rw [LiZhongQC.dzbar, hD.fderiv]
    simp only [add_apply, smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul,
      ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, map_one, Complex.conj_I]
    linear_combination ((A - B) / 2) * Complex.I_sq
  have hF : F ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  have hfac : (1 : ℂ) - Complex.I * (ε : ℂ) / 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.sub_re, Complex.mul_re, Complex.div_re] at hre
  have hden : (2 : ℂ) - Complex.I * (ε : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.sub_re, Complex.mul_re] at hre
  have hA : A ≠ 0 := mul_ne_zero hF hfac
  have hc : coefficientCurve θ t z =
      (Complex.I * (ε : ℂ)) / (2 - Complex.I * (ε : ℂ)) *
        ((z : ℂ) / conj (z : ℂ)) := by
    rw [coefficientCurve_eq_source, ite_eq_left (show Complex.arg (z : ℂ) ∈ interval θ from
      ⟨hlo.le, hhi.le⟩)]
  refine ⟨hD, hdz, hdzbar, ?_, ?_⟩
  · rw [hdz]
    exact hA
  · calc
      _ = B / A := congrArg₂ (fun a b : ℂ => a / b) hdzbar hdz
      _ = coefficientCurve θ t z := by
        rw [hc]
        dsimp only [A, B]
        field_simp [hF, hcz, hfac, hden]

/-- Above the upper ray the spatial derivative is the source exp(-t) dilation. -/
theorem elementaryMapPlane_spatial_above
    (θ : Width) (t : ℝ) (z : ℍ)
    (hz : Real.pi / 2 + (θ : ℝ) < Complex.arg (z : ℂ)) :
    let W := elementaryMapPlane θ t
    let c : ℂ := (Real.exp (-t) : ℂ)
    HasFDerivAt W (c • (1 : ℂ →L[ℝ] ℂ)) (z : ℂ) ∧
      LiZhongQC.dz W (z : ℂ) = c ∧
      LiZhongQC.dzbar W (z : ℂ) = 0 ∧
      LiZhongQC.dz W (z : ℂ) ≠ 0 ∧
      LiZhongQC.complexDilatation W (z : ℂ) = coefficientCurve θ t z := by
  classical
  let W := elementaryMapPlane θ t
  let c : ℂ := (Real.exp (-t) : ℂ)
  have hs : (z : ℂ) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr z.im_pos.ne')
  have him : ∀ᶠ ζ : ℂ in 𝓝 (z : ℂ), 0 < ζ.im :=
    (Complex.continuous_im.tendsto _).eventually (isOpen_Ioi.mem_nhds z.im_pos)
  have hang : ∀ᶠ ζ : ℂ in 𝓝 (z : ℂ),
      Real.pi / 2 + (θ : ℝ) < Complex.arg ζ :=
    (Complex.continuousAt_arg hs).eventually (isOpen_Ioi.mem_nhds hz)
  have he : W =ᶠ[𝓝 (z : ℂ)] fun ζ : ℂ => ζ * c := by
    filter_upwards [him, hang] with ζ hζ harg
    have hnot : ¬ Complex.arg ζ < Real.pi / 2 - (θ : ℝ) := by
      linarith [θ.property.1]
    change elementaryMapPlane θ t ζ = ζ * c
    rw [elementaryMapPlane, dite_eq_left hζ, coe_elementaryMap,
      ite_eq_right hnot, ite_eq_right (not_le.mpr harg)]
  have hD : HasFDerivAt W (c • ContinuousLinearMap.id ℝ ℂ) (z : ℂ) :=
    ((hasFDerivAt_id (z : ℂ)).mul_const c).congr_of_eventuallyEq he
  have hdz : LiZhongQC.dz W (z : ℂ) = c := by
    rw [LiZhongQC.dz, hD.fderiv]
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
    rw [mul_left_comm Complex.I c Complex.I, Complex.I_mul_I]
    ring
  have hdzbar : LiZhongQC.dzbar W (z : ℂ) = 0 := by
    rw [LiZhongQC.dzbar, hD.fderiv]
    simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul, mul_one]
    rw [mul_left_comm Complex.I c Complex.I, Complex.I_mul_I]
    ring
  have hc : coefficientCurve θ t z = 0 := by
    have hnot : Complex.arg (z : ℂ) ∉ interval θ := by
      intro h
      exact (not_le_of_gt hz) h.2
    simp only [coefficientCurve, ite_eq_right hnot]
  refine ⟨hD, hdz, hdzbar, ?_, ?_⟩
  · rw [hdz]
    exact Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)
  · calc
      _ = (0 : ℂ) / c := congrArg₂ (fun a b : ℂ => a / b) hdzbar hdz
      _ = 0 := zero_div _
      _ = coefficientCurve θ t z := hc.symm

end LowDimensionalTopology.Geometry.Teichmuller.AngularTwist
