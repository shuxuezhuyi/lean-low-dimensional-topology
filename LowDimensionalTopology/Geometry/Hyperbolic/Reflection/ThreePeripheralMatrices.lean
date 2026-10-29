module
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularBoundaryClassInjection
public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.ReflectionProductTraces
public import LowDimensionalTopology.Geometry.Hyperbolic.Isometry.HyperbolicAxes
@[expose] public section
namespace LowDimensionalTopology.Geometry.Hyperbolic
open Fuchsian
open scoped UpperHalfPlane
noncomputable section

/-- The original three peripheral lifts, in the free-word order (01,20,12). -/
def annularPeripheralMatrix (E r x : ℝ) (hE : 0 < E) (hr : 0 < r) :
    Fin 3 → Matrix.SpecialLinearGroup (Fin 2) ℝ :=
  let C0 := HalfPlaneLine.circle 0 1 zero_lt_one
  let CE := HalfPlaneLine.circle 0 E hE
  let Cs := HalfPlaneLine.circle x r hr
  ![reflectionProductSL C0 CE, reflectionProductSL Cs C0, reflectionProductSL CE Cs]

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
  (hin : 1 + r < x) (hout : x + r < E)
local notation "C0" => HalfPlaneLine.circle 0 1 zero_lt_one
local notation "CE" => HalfPlaneLine.circle 0 E (zero_lt_one.trans hE)
local notation "Cs" => HalfPlaneLine.circle x r hr
local notation "A" => annularPeripheralMatrix E r x (zero_lt_one.trans hE) hr

/-- Every lift has exactly the original native word action, including the inverse third word. -/
theorem annularPeripheralMatrix_native (i : Fin 3) :
    (annularPairReflectionFreeEquiv E r x hE hr hin hout (pantsThreeFreeWords i) : ℍ ≃ᵢ ℍ) =
      hSLIsometry (A i) := by
  fin_cases i
  · simpa [pantsThreeFreeWords, annularPeripheralMatrix] using
      (annularPairReflectionFreeEquiv_of_zero E r x hE hr hin hout).trans
        (Fuchsian.reflectionProductSL_native C0 CE)
  · simpa [pantsThreeFreeWords, annularPeripheralMatrix] using
      (annularPairReflectionFreeEquiv_of_one E r x hE hr hin hout).trans
        (Fuchsian.reflectionProductSL_native Cs C0)
  · change (annularPairReflectionFreeEquiv E r x hE hr hin hout
      ((FreeGroup.of (1 : Fin 2) * FreeGroup.of 0)⁻¹) : ℍ ≃ᵢ ℍ) =
        hSLIsometry (reflectionProductSL CE Cs)
    rw [annularPairReflectionFreeEquiv_coe]
    simp only [map_inv, map_mul, FreeGroup.lift_apply_of]
    rw [← Fuchsian.reflectionProductSL_native]
    apply IsometryEquiv.ext
    intro z
    change (CE).reflection ((C0).reflection ((C0).reflection ((Cs).reflection z))) =
      (CE).reflection ((Cs).reflection z)
    rw [(C0).reflection_involutive]

/-- Cayley conjugation gives the same actual original disc-group peripheral word. -/
theorem annularPeripheralMatrix_disc (i : Fin 3) :
    cayleyMobius * realSLMobius (A i) * cayleyMobius⁻¹ =
      (annularDiscPeripheralWord E r x hE hr hin hout i).val := by
  let K := annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
  let hK := annularPairReflectionGroup_le_conformal E r x (zero_lt_one.trans hE) hr
  let F := Fuchsian.nativeConformalSubgroupMobiusHom K hK
  let w : K := annularPairReflectionFreeEquiv E r x hE hr hin hout (pantsThreeFreeWords i)
  have hw : (w : ℍ ≃ᵢ ℍ) = hSLIsometry (A i) :=
    annularPeripheralMatrix_native E r x hE hr hin hout i
  have hm : hSLIsometry (A i) ∈ K := by rw [← hw]; exact w.property
  have hs : w = (⟨hSLIsometry (A i), hm⟩ : K) := Subtype.ext hw
  rw [annularDiscPeripheralWord, annularPairReflectionDiscFreeEquiv_coe]
  change cayleyMobius * realSLMobius (A i) * cayleyMobius⁻¹ =
    cayleyMobius * F w * cayleyMobius⁻¹
  rw [hs]
  simp only [F, Fuchsian.nativeConformalSubgroupMobiusHom_matrix]

/-- The genuine reflection lifts have the prescribed whole native translation lengths.
The input half-widths are in book order, while the word indices have order (a1,a3,a2). -/
theorem annularPeripheralMatrix_type_length (a1 a2 a3 : ℝ)
    (h01 : (C0).HDisjoint CE) (h02 : (C0).HDisjoint Cs) (h12 : (CE).HDisjoint Cs)
    (l01 : (C0).lineDist CE = a1 / 2) (l02 : (C0).lineDist Cs = a3 / 2)
    (l12 : (CE).lineDist Cs = a2 / 2) :
    ∀ i : Fin 3, Mobius.MobiusHyperbolic (realSLMobius (A i)) ∧
      hTranslationLength (hSLIsometry (A i)) = ![a1, a3, a2] i := by
  have pair (L M : HalfPlaneLine) (hd : L.HDisjoint M) :
      Mobius.MobiusHyperbolic (realSLMobius (reflectionProductSL L M)) ∧
      hTranslationLength (hSLIsometry (reflectionProductSL L M)) = 2 * L.lineDist M := by
    let B := reflectionProductSL L M
    have hn : realSLMobius B ≠ 1 := Fuchsian.reflectionProductSL_nonidentity L M hd.1
    have hyp : Mobius.MobiusHyperbolic (realSLMobius B) :=
      realSL_disjoint_reflections_hyperbolic B hn M L
        ⟨hd.1.symm, hd.2.1.symm, hd.2.2.symm⟩ (funext (reflectionProductSL_action L M))
    have ht := (realSLMobius_hyperbolic_iff B hn).mp hyp
    refine ⟨hyp, ?_⟩
    have hc : Real.cosh (hTranslationLength (hSLIsometry B) / 2) =
        Real.cosh (L.lineDist M) :=
      (hHyperbolic_translation_abs_trace B hn ht).symm.trans
        ((reflectionProductSL_abs_trace L M).symm.trans
          (halfPlane_inversiveProduct_eq_cosh_lineDist L M hd))
    have he := Real.cosh_strictMonoOn.injOn
      (le_of_lt (div_pos (hHyperbolic_translationLength_pos B hn ht) (by norm_num)))
      (L.lineDist_nonneg M) hc
    linarith
  have t0 := pair C0 CE h01
  have t1 := pair Cs C0 ⟨h02.1.symm, h02.2.1.symm, h02.2.2.symm⟩
  have t2 := pair CE Cs h12
  rw [(Cs).lineDist_comm C0] at t1
  have hdouble (a : ℝ) : 2 * (a / 2) = a := by ring
  intro i
  fin_cases i
  · simpa [annularPeripheralMatrix, l01, hdouble] using t0
  · simpa [annularPeripheralMatrix, l02, hdouble] using t1
  · simpa [annularPeripheralMatrix, l12, hdouble] using t2

/-- The matrix hyperbolicity is the actual original disc word's hyperbolicity. -/
theorem annularDiscPeripheralWord_hyperbolic (i : Fin 3)
    (h : Mobius.MobiusHyperbolic (realSLMobius (A i))) :
    Mobius.MobiusHyperbolic (annularDiscPeripheralWord E r x hE hr hin hout i).val :=
  (Mobius.mobiusHyperbolic_isConj
    (isConj_iff.mpr ⟨cayleyMobius, annularPeripheralMatrix_disc E r x hE hr hin hout i⟩)).mp h

end
end LowDimensionalTopology.Geometry.Hyperbolic
