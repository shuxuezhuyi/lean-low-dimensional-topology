module

public import LowDimensionalTopology.Unproved.Quasiconformal.RectangleExtremalBeltrami

/-!
# Affine extremality on a closed rectangle

The lower bound and affine attainment reuse the existing general
quasiconformal rectangle APIs. Unique extremality is conditional on the
explicit almost-everywhere equality step in
`Unproved.Quasiconformal.RectangleExtremalBeltrami`.

The equality statement uses the literal maximal dilatation. A supplied
quasiconformal upper bound need not be optimal, even for the affine map.
Boundary values are those of the actual homeomorphic extension.

The reused analytic results are due to Wu Xiaobin, from the fixed
Apache-2.0 Li-Zhong-QC-formalization source recorded in
`External/LiZhongQC/UPSTREAM.json`; see `THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set Filter Topology MeasureTheory LiZhongQC
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller

/-- The affine Beltrami parameter for the rectangles of widths `r` and `s`
and common height one. -/
def rectangleStretchParameter (r s : ℝ) : ℝ :=
  (s / r - 1) / (s / r + 1)

/-- The source affine parameter belongs to the Beltrami unit interval. -/
theorem rectangleStretchParameter_mem_Ico {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    rectangleStretchParameter r s ∈ Ico (0 : ℝ) 1 := by
  have hK : 1 ≤ s / r := (le_div_iff₀ hr).2 (by simpa using hrs)
  have hden : 0 < s / r + 1 := by linarith
  constructor
  · exact div_nonneg (sub_nonneg.mpr hK) hden.le
  · exact (div_lt_one hden).2 (by linarith)

/-- The parameter gives exactly the ratio `K = s/r` in the notes. -/
theorem rectangleStretchParameter_dilatation {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    (1 + rectangleStretchParameter r s) / (1 - rectangleStretchParameter r s) = s / r := by
  have hk := (rectangleStretchParameter_mem_Ico hr hrs).2
  have hK : 1 ≤ s / r := (le_div_iff₀ hr).2 (by simpa using hrs)
  have hdef : rectangleStretchParameter r s * (s / r + 1) = s / r - 1 := by
    exact div_mul_cancel₀ _ (show s / r + 1 ≠ 0 by linarith)
  apply (div_eq_iff (show 1 - rectangleStretchParameter r s ≠ 0 by linarith)).2
  nlinarith

/-- The existing affine rectangle map is literally the normalized affine
formula in the notes. -/
theorem affineStretch_eq_teichStretch {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    affineStretch r s = teichStretch (rectangleStretchParameter r s) := by
  funext z
  obtain ⟨hre, him⟩ := s26u_teichStretch_real_form
    (rectangleStretchParameter_mem_Ico hr hrs).2 z
  apply Complex.ext
  · rw [(s26g_affine_re_im r s z).1, hre, rectangleStretchParameter_dilatation hr hrs]
  · exact (s26g_affine_re_im r s z).2.trans him.symm

/-- The general quasiconformal bound in the notes' `k` parameter. This
holds for every supplied admissible quasiconformal upper bound. -/
theorem rectangle_competitor_parameter_bound {r s k₁ : ℝ} (hr : 0 < r) (hrs : r ≤ s)
    (hk₁ : k₁ < 1) {h : ℂ → ℂ}
    (hqc : IsKQC h (rectangle r 1) ((1 + k₁) / (1 - k₁)))
    (himg : h '' rectangle r 1 = rectangle s 1) {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h (rectangle r 1) (rectangle s 1) H)
    (hv : ∀ i, H (rectVert r 1 i) = rectVert s 1 i) :
    rectangleStretchParameter r s ≤ k₁ := by
  have hs : 0 < s := hr.trans_le hrs
  have hbound := (le_max_left (s / r) (r / s)).trans
    (s26g_rect_bound hr hs hqc himg hH hv)
  have hK : 1 ≤ s / r := (le_div_iff₀ hr).2 (by simpa using hrs)
  apply (div_le_iff₀ (show 0 < s / r + 1 by linarith)).2
  have hmul := (le_div_iff₀ (show 0 < 1 - k₁ by linarith)).1 hbound
  nlinarith

private theorem rectangle_nonempty {r : ℝ} (hr : 0 < r) : (rectangle r 1).Nonempty := by
  exact ⟨⟨r / 2, 1 / 2⟩, half_pos hr, half_lt_self hr, by norm_num, by norm_num⟩

private theorem affine_rectangle_qc {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    IsKQC (affineStretch r s) (rectangle r 1) (s / r) := by
  have hs : 0 < s := hr.trans_le hrs
  have hinv : r / s ≤ s / r := (div_le_div_iff₀ hs hr).2 (by nlinarith)
  have h := ac_t_isKQC_restrict (s26g_affine_isKQC hr hs)
    (isOpen_rectangle r 1) (subset_univ _)
  rwa [max_eq_left hinv] at h

private theorem affine_rectangle_extension {r s : ℝ} (hr : 0 < r) (hs : 0 < s) :
    IsHomeoExtension (affineStretch r s) (rectangle r 1) (rectangle s 1)
      (OnePoint.map (affineStretch r s)) := by
  have h := s26g_isHomeoExtension_map (s26g_affine_continuous r s)
    (s26g_affine_injective hr hs) (isBounded_rectangle r 1)
  rwa [s26g_affine_image hr hs] at h

/-- The literal maximal dilatation of every admissible rectangle map is
at least the affine value. -/
theorem rectangle_maxDilatation_lower {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    {h : ℂ → ℂ} (hqc : IsQuasiconformal h (rectangle r 1))
    (himg : h '' rectangle r 1 = rectangle s 1) {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h (rectangle r 1) (rectangle s 1) H)
    (hv : ∀ i, H (rectVert r 1 i) = rectVert s 1 i) :
    ENNReal.ofReal (s / r) ≤ maxDilatation h (rectangle r 1) := by
  obtain ⟨K, hK⟩ := hqc
  obtain ⟨_, hsharp⟩ := UniversalTeichmuller.ut_md_isKQC_toReal hK (rectangle_nonempty hr)
  have hbound := (le_max_left (s / r) (r / s)).trans
    (s26g_rect_bound hr hs hsharp himg hH hv)
  have hfin : maxDilatation h (rectangle r 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (isKQC_maxDilatation_le hK).1
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal hbound

/-- The actual affine map attains the lower bound, with no missing premise. -/
theorem rectangle_affine_maxDilatation {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) :
    maxDilatation (affineStretch r s) (rectangle r 1) = ENNReal.ofReal (s / r) := by
  have hs : 0 < s := hr.trans_le hrs
  have hqc := affine_rectangle_qc hr hrs
  exact le_antisymm (isKQC_maxDilatation_le hqc).1
    (rectangle_maxDilatation_lower hr hs ⟨_, hqc⟩ (s26g_affine_image hr hs)
      (affine_rectangle_extension hr hs) (s26g_affine_vert hr))

private theorem rectangle_three_vertices_injective {r : ℝ} (hr : 0 < r) :
    Function.Injective (![(((0 : ℂ)) : ExtPlane), (((r : ℝ) : ℂ) : ExtPlane),
      ((I : ℂ) : ExtPlane)] : Fin 3 → ExtPlane) := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · have h : (0 : ℂ) = (r : ℂ) := OnePoint.coe_injective hij
    have hh := congrArg Complex.re h
    simp only [zero_re, ofReal_re] at hh
    linarith
  · have h : (0 : ℂ) = I := OnePoint.coe_injective hij
    have hh := congrArg Complex.im h
    norm_num at hh
  · have h : (r : ℂ) = 0 := OnePoint.coe_injective hij
    have hh := congrArg Complex.re h
    simp only [zero_re, ofReal_re] at hh
    linarith
  · rfl
  · have h : (r : ℂ) = I := OnePoint.coe_injective hij
    have hh := congrArg Complex.im h
    norm_num at hh
  · have h : I = (0 : ℂ) := OnePoint.coe_injective hij
    have hh := congrArg Complex.im h
    norm_num at hh
  · have h : I = (r : ℂ) := OnePoint.coe_injective hij
    have hh := congrArg Complex.im h
    norm_num at hh
  · rfl

private theorem rectangle_eq_affine_of_beltrami {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s)
    {h : ℂ → ℂ} (hqc : IsQuasiconformal h (rectangle r 1))
    (himg : h '' rectangle r 1 = rectangle s 1) {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h (rectangle r 1) (rectangle s 1) H)
    (hv : ∀ i, H (rectVert r 1 i) = rectVert s 1 i)
    (hμ : ∀ᵐ z ∂(volume.restrict (rectangle r 1)),
      complexDilatation h z = (rectangleStretchParameter r s : ℂ)) :
    EqOn h (affineStretch r s) (rectangle r 1) := by
  have hs : 0 < s := hr.trans_le hrs
  have hA := affine_rectangle_qc hr hrs
  have hAext := affine_rectangle_extension hr hs
  have hμA : ∀ z, complexDilatation (affineStretch r s) z =
      (rectangleStretchParameter r s : ℂ) := by
    rw [affineStretch_eq_teichStretch hr hrs]
    exact s26b_teichStretch_dilatation (rectangleStretchParameter_mem_Ico hr hrs).2
  apply thm13_4_uniqueness (isTopQuad_rectangle hr one_pos).1
    (isTopQuad_rectangle hs one_pos).1 hqc ⟨_, hA⟩ himg (s26g_affine_image hr hs)
    (hμ.mono fun z hz => hz.trans (hμA z).symm) hH hAext
    (p := ![(((0 : ℂ)) : ExtPlane), (((r : ℝ) : ℂ) : ExtPlane), ((I : ℂ) : ExtPlane)])
    (rectangle_three_vertices_injective hr)
  · intro i
    fin_cases i
    · exact (isTopQuad_rectangle hr one_pos).2.1 0
    · exact (isTopQuad_rectangle hr one_pos).2.1 1
    · simpa [rectVert] using (isTopQuad_rectangle hr one_pos).2.1 3
  · intro i
    fin_cases i
    · exact (hv 0).trans (s26g_affine_vert hr 0).symm
    · exact (hv 1).trans (s26g_affine_vert hr 1).symm
    · simpa [rectVert] using (hv 3).trans (s26g_affine_vert hr 3).symm

private theorem rectangle_maxDilatation_congr {r : ℝ} {h g : ℂ → ℂ}
    (heq : EqOn h g (rectangle r 1)) :
    maxDilatation h (rectangle r 1) = maxDilatation g (rectangle r 1) := by
  unfold maxDilatation
  apply essSup_congr_ae
  filter_upwards [ae_restrict_mem (isOpen_rectangle r 1).measurableSet] with z hz
  have hder := (Filter.eventuallyEq_of_mem ((isOpen_rectangle r 1).mem_nhds hz)
    heq).fderiv_eq (𝕜 := ℝ)
  simp only [dz, dzbar, hder]

/-- The full source extremal property, with unique extremality conditional
only on the named a.e. Beltrami equality step. Equality of the actual
maximal dilatation is equivalent to equality of the actual closed maps. -/
theorem rectangle_unique_extremal
    (hEquality : Unproved.Quasiconformal.RectangleExtremalBeltrami)
    {r s : ℝ} (hr : 0 < r) (hrs : r ≤ s) {h : ℂ → ℂ}
    (hqc : IsQuasiconformal h (rectangle r 1))
    (himg : h '' rectangle r 1 = rectangle s 1) {H : ExtPlane → ExtPlane}
    (hH : IsHomeoExtension h (rectangle r 1) (rectangle s 1) H)
    (hv : ∀ i, H (rectVert r 1 i) = rectVert s 1 i) :
    ENNReal.ofReal (s / r) ≤ maxDilatation h (rectangle r 1) ∧
      (maxDilatation h (rectangle r 1) = ENNReal.ofReal (s / r) ↔
        EqOn H (OnePoint.map (affineStretch r s)) (closure (toExt (rectangle r 1)))) := by
  have hs : 0 < s := hr.trans_le hrs
  have hAext := affine_rectangle_extension hr hs
  refine ⟨rectangle_maxDilatation_lower hr hs hqc himg hH hv, ?_⟩
  constructor
  · intro hmax
    obtain ⟨K, hK⟩ := hqc
    have hsharp := (UniversalTeichmuller.ut_md_isKQC_toReal hK (rectangle_nonempty hr)).2
    have hreal : (maxDilatation h (rectangle r 1)).toReal = s / r := by
      rw [hmax, ENNReal.toReal_ofReal (div_nonneg hs.le hr.le)]
    rw [hreal] at hsharp
    have hμ := hEquality r s hr hrs h H hsharp himg hH hv
    have heq := rectangle_eq_affine_of_beltrami hr hrs ⟨K, hK⟩ himg hH hv hμ
    have hext : EqOn H (OnePoint.map (affineStretch r s)) (toExt (rectangle r 1)) := by
      rintro _ ⟨z, hz, rfl⟩
      rw [hH.1 z hz, OnePoint.map_some]
      exact congrArg (fun w : ℂ => (w : ExtPlane)) (heq hz)
    exact hext.of_subset_closure hH.2.1 hAext.2.1 subset_closure subset_rfl
  · intro hext
    have heq : EqOn h (affineStretch r s) (rectangle r 1) := by
      intro z hz
      apply OnePoint.coe_injective
      have he := hext (subset_closure (mem_image_of_mem _ hz))
      rw [hH.1 z hz, OnePoint.map_some] at he
      exact he
    exact (rectangle_maxDilatation_congr heq).trans (rectangle_affine_maxDilatation hr hrs)

end LowDimensionalTopology.Geometry.Teichmuller
