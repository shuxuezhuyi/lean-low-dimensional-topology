module

public import LowDimensionalTopology.External.LiZhongQC.Ch10.S33_BersEmbedding
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Fixed reflection of the actual raw Bers function

The reflection is minus complex conjugation, which preserves each half-plane.
The original nonsymmetric plane solution is retained, including its necessary
affine normalization at one. The final identity concerns its actual Schwarzian
with the original lower-plane zero extension.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter
open scoped ENNReal ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller.BersWeighted

/-- The fixed reflection preserves the actual plane measure. -/
theorem fixedBersReflection_measurePreserving :
    MeasurePreserving (fun z : ℂ => -conj z) volume volume :=
  (Measure.measurePreserving_neg (volume : Measure ℂ)).comp
    LiZhongQC.gzE_conj_measurePreserving

/-- The same raw coefficient, reflected within the upper and lower half-planes. -/
def fixedBersReflectionCoefficient (μ : LiZhongQC.BeltramiH) : LiZhongQC.BeltramiH := by
  refine ⟨fun z => conj (μ.val (-conj z)), ?_⟩
  obtain ⟨⟨k, hk0, hk1, hμ⟩, hzero⟩ := μ.property
  rw [LiZhongQC.IsBeltramiCoeff, Measure.restrict_univ] at hμ
  refine ⟨⟨k, hk0, hk1, ?_⟩, ?_⟩
  · rw [LiZhongQC.IsBeltramiCoeff, Measure.restrict_univ]
    refine ⟨Complex.continuous_conj.comp_aestronglyMeasurable
      (hμ.1.comp_measurePreserving fixedBersReflection_measurePreserving), ?_⟩
    filter_upwards [fixedBersReflection_measurePreserving.quasiMeasurePreserving.ae hμ.2]
      with z hz
    simpa only [Complex.norm_conj] using hz
  · intro z hz
    change conj (μ.val (-conj z)) = 0
    simpa only [map_zero] using congrArg conj (hzero (-conj z) (by simpa using hz))

/-- The reflected raw coefficient has the literal original pointwise values. -/
@[simp] theorem fixedBersReflectionCoefficient_apply (μ : LiZhongQC.BeltramiH) (z : ℂ) :
    (fixedBersReflectionCoefficient μ).val z = conj (μ.val (-conj z)) := rfl

/-- Double reflection of a plane function, with the same fixed minus sign. -/
def fixedBersReflectedPlaneFunction (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  conj (f (-conj z))

/-- Negation contributes no complex-dilatation phase. -/
theorem fixedBersReflection_dilatation_neg (f : ℂ → ℂ) (z : ℂ) :
    LiZhongQC.complexDilatation (fun w => f (-w)) z =
      LiZhongQC.complexDilatation f (-z) := by
  have h := LiZhongQC.s23_dilatation_comp_right (g := f)
    (T := fun w : ℂ => -w) (S := fun w : ℂ => -w)
    (z := z) (by fun_prop) (by fun_prop)
    (Eventually.of_forall fun w => neg_neg w)
    (Eventually.of_forall fun w => neg_neg w)
  simpa only [Function.comp_def, deriv_neg'', map_neg, map_one,
    neg_div_neg_eq, div_self one_ne_zero, mul_one] using h

/-- The actual complex dilatation of the reflected plane map is the reflected one. -/
theorem fixedBersReflectedPlaneFunction_dilatation (f : ℂ → ℂ) (z : ℂ) :
    LiZhongQC.complexDilatation (fixedBersReflectedPlaneFunction f) z =
      conj (LiZhongQC.complexDilatation f (-conj z)) := by
  change LiZhongQC.complexDilatation (fun w : ℂ => conj (f (-conj w))) z =
    conj (LiZhongQC.complexDilatation f (-conj z))
  have h := LiZhongQC.bg_dilatation_conj (fun w => f (-w)) z
  simpa only [fixedBersReflection_dilatation_neg] using h

/-- The same QC constant works for the actual fixed-reflected plane function. -/
theorem fixedBersReflectedPlaneFunction_isKQC {f : ℂ → ℂ} {K : ℝ}
    (hf : LiZhongQC.IsKQC f univ K) :
    LiZhongQC.IsKQC (fixedBersReflectedPlaneFunction f) univ K := by
  have hneg : LiZhongQC.IsConformalOnto (fun z : ℂ => -z) univ univ := by
    simpa only [sub_zero, div_neg, div_one] using
      (LiZhongQC.nxE_affine_isConformalOnto (a := (-1 : ℂ)) (b := 0) (by norm_num))
  have hcomp := LiZhongQC.thm7_1_comp
    (LiZhongQC.isKQC_one_of_conformal isOpen_univ hneg) hf (subset_univ _)
  have hcomp' : LiZhongQC.IsKQC (fun z : ℂ => f (-z)) univ K := by
    simpa only [one_mul, Function.comp_def] using hcomp
  change LiZhongQC.IsKQC (fun z : ℂ => conj (f (-conj z))) univ K
  simpa only [preimage_univ] using
    LiZhongQC.abR_x_isKQC_conj hcomp'

/-- Reflection keeps the original onto plane map onto. -/
theorem fixedBersReflectedPlaneFunction_surjective {f : ℂ → ℂ}
    (hf : f '' univ = univ) : fixedBersReflectedPlaneFunction f '' univ = univ := by
  apply eq_univ_of_forall
  intro w
  have hw : conj w ∈ f '' univ := by rw [hf]; exact mem_univ _
  obtain ⟨z, _, hz⟩ := hw
  refine ⟨-conj z, mem_univ _, ?_⟩
  simp only [fixedBersReflectedPlaneFunction, map_neg, Complex.conj_conj, neg_neg, hz]

/-- The actual affine normalization denominator is nonzero by original injectivity. -/
theorem fixedBersReflection_normalizer_ne_zero (μ : LiZhongQC.BeltramiH) :
    conj (LiZhongQC.normalizedSolution μ.val (-1)) ≠ 0 := by
  obtain ⟨⟨K, hK⟩, _, h0, _, _⟩ := LiZhongQC.ut_spec μ
  have hne : LiZhongQC.normalizedSolution μ.val (-1) ≠ 0 := by
    intro h
    have hx := hK.2.2.1.2.1 (mem_univ (-1 : ℂ)) (mem_univ (0 : ℂ)) (h.trans h0.symm)
    norm_num at hx
  intro h
  apply hne
  simpa only [Complex.conj_conj, map_zero] using congrArg conj h

/-- The same raw nonsymmetric normalized solution has its necessary affine denominator. -/
theorem normalizedSolution_fixedBersReflection (μ : LiZhongQC.BeltramiH) (z : ℂ) :
    LiZhongQC.normalizedSolution (fixedBersReflectionCoefficient μ).val z =
      conj (LiZhongQC.normalizedSolution μ.val (-conj z)) /
        conj (LiZhongQC.normalizedSolution μ.val (-1)) := by
  obtain ⟨⟨K, hK⟩, hs, h0, _, hd⟩ := LiZhongQC.ut_spec μ
  have hG := fixedBersReflectedPlaneFunction_isKQC hK
  have hGs := fixedBersReflectedPlaneFunction_surjective hs
  have hdil : ∀ᵐ w, LiZhongQC.complexDilatation
      (fixedBersReflectedPlaneFunction (LiZhongQC.normalizedSolution μ.val)) w =
        (fixedBersReflectionCoefficient μ).val w := by
    filter_upwards [fixedBersReflection_measurePreserving.quasiMeasurePreserving.ae hd]
      with w hw
    rw [fixedBersReflectedPlaneFunction_dilatation, hw, fixedBersReflectionCoefficient_apply]
  have hn := LiZhongQC.bg2_normalize (fixedBersReflectionCoefficient μ) hG hGs hdil z
  simpa only [fixedBersReflectedPlaneFunction, map_zero, map_one, neg_zero,
    h0, sub_zero] using hn

/-- Complex derivatives of the same fixed-reflected function have the expected sign. -/
theorem fixedBersReflectedPlaneFunction_deriv (f : ℂ → ℂ) (z : ℂ) :
    deriv (fixedBersReflectedPlaneFunction f) z =
      -fixedBersReflectedPlaneFunction (deriv f) z := by
  change deriv (fun w : ℂ => conj (f (-conj w))) z =
    -conj (deriv f (-conj z))
  have h := congrFun (deriv_conj_conj (f := fun w : ℂ => f (-w))) z
  simpa only [Function.comp_def, deriv_comp_neg, map_neg] using h

/-- The holomorphic Schwarzian transforms under this fixed reflection. -/
theorem fixedBersReflectedPlaneFunction_schwarzianHol (f : ℂ → ℂ) (z : ℂ) :
    LiZhongQC.schwarzianHol (fixedBersReflectedPlaneFunction f) z =
      conj (LiZhongQC.schwarzianHol f (-conj z)) := by
  have hd : deriv (fixedBersReflectedPlaneFunction f) =
      fun w => -fixedBersReflectedPlaneFunction (deriv f) w :=
    funext (fixedBersReflectedPlaneFunction_deriv f)
  have hdd : deriv (deriv (fixedBersReflectedPlaneFunction f)) =
      fixedBersReflectedPlaneFunction (deriv (deriv f)) := by
    funext w
    rw [hd, deriv.fun_neg, fixedBersReflectedPlaneFunction_deriv, neg_neg]
  have hr : (fun w => deriv (deriv (fixedBersReflectedPlaneFunction f)) w /
      deriv (fixedBersReflectedPlaneFunction f) w) =
        fun w => -fixedBersReflectedPlaneFunction (fun v => deriv (deriv f) v / deriv f v) w := by
    funext w
    rw [hdd, hd]
    simp only [fixedBersReflectedPlaneFunction, map_div₀, div_neg]
  unfold LiZhongQC.schwarzianHol
  rw [hr, deriv.fun_neg, fixedBersReflectedPlaneFunction_deriv, hdd, hd]
  simp [fixedBersReflectedPlaneFunction, map_sub, map_mul, map_div₀, map_pow,
    map_ofNat, div_neg]

/-- The actual raw lower-plane Schwarzian has the same fixed-reflection covariance. -/
theorem schwarzian_normalizedSolution_fixedBersReflection
    (μ : LiZhongQC.BeltramiH) {z : ℂ} (hz : z ∈ LiZhongQC.lowerHalf) :
    LiZhongQC.schwarzian
      (LiZhongQC.normalizedSolution (fixedBersReflectionCoefficient μ).val) z =
        conj (LiZhongQC.schwarzian (LiZhongQC.normalizedSolution μ.val) (-conj z)) := by
  let W := LiZhongQC.normalizedSolution μ.val
  let G := fixedBersReflectedPlaneFunction W
  let d := conj (W (-1))
  have hd : d ≠ 0 := fixedBersReflection_normalizer_ne_zero μ
  have hn : LiZhongQC.normalizedSolution (fixedBersReflectionCoefficient μ).val =
      fun w => (G w - 0) / d := by
    funext w
    simpa only [G, d, W, fixedBersReflectedPlaneFunction, sub_zero] using
      normalizedSolution_fixedBersReflection μ w
  have hG : G = fun w => d * LiZhongQC.normalizedSolution
      (fixedBersReflectionCoefficient μ).val w := by
    funext w
    have hw := congrFun hn w
    rw [sub_zero] at hw
    exact ((eq_div_iff hd).mp hw).symm.trans (mul_comm _ _)
  have hGhol : DifferentiableOn ℂ G LiZhongQC.lowerHalf := by
    rw [hG]
    exact ((LiZhongQC.ut_conformal_lowerHalf
      (fixedBersReflectionCoefficient μ)).1).const_mul d
  obtain ⟨⟨K, hK⟩, _, _, _, _⟩ := LiZhongQC.ut_spec μ
  have hGinj : InjOn G LiZhongQC.lowerHalf :=
    (fixedBersReflectedPlaneFunction_isKQC hK).2.2.1.2.1.mono (subset_univ _)
  have hσz : -conj z ∈ LiZhongQC.lowerHalf := by simpa [LiZhongQC.lowerHalf] using hz
  have hWa := (LiZhongQC.ut_conformal_lowerHalf μ).1.analyticAt
    (LiZhongQC.isOpen_lowerHalf.mem_nhds hσz)
  calc
    LiZhongQC.schwarzian
        (LiZhongQC.normalizedSolution (fixedBersReflectionCoefficient μ).val) z =
      LiZhongQC.schwarzian G z := by
        rw [hn]
        exact LiZhongQC.bB_l_schwarzian_affine hGhol hGinj 0 hd hz
    _ = conj (LiZhongQC.schwarzian W (-conj z)) := by
      rw [LiZhongQC.schwarzian_of_analyticAt
        (hGhol.analyticAt (LiZhongQC.isOpen_lowerHalf.mem_nhds hz)),
        LiZhongQC.schwarzian_of_analyticAt hWa]
      exact fixedBersReflectedPlaneFunction_schwarzianHol W z

/-- The original raw Bers function, including its zero extension, transforms literally. -/
theorem rawBers_fixedBersReflection (μ : LiZhongQC.BeltramiH) :
    LiZhongQC.bersFunction (fixedBersReflectionCoefficient μ).val =
      fun z : ℂ => conj (LiZhongQC.bersFunction μ.val (-conj z)) := by
  funext z
  by_cases hz : z ∈ LiZhongQC.lowerHalf
  · have hσz : -conj z ∈ LiZhongQC.lowerHalf := by simpa [LiZhongQC.lowerHalf] using hz
    rw [LiZhongQC.bersFunction, indicator_of_mem hz,
      LiZhongQC.bersFunction, indicator_of_mem hσz]
    exact schwarzian_normalizedSolution_fixedBersReflection μ hz
  · have hσz : -conj z ∉ LiZhongQC.lowerHalf := by simpa [LiZhongQC.lowerHalf] using hz
    rw [LiZhongQC.bersFunction, indicator_of_notMem hz,
      LiZhongQC.bersFunction, indicator_of_notMem hσz, map_zero]

end LowDimensionalTopology.Geometry.Teichmuller.BersWeighted
