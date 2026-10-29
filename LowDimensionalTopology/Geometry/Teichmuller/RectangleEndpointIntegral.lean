module

public import LowDimensionalTopology.Geometry.Teichmuller.RectangleSideIntegralLimit

/-!
# The horizontal endpoint integral for a quasiconformal rectangle map

Green's formula on interior rectangles, followed by exhaustion to the
actual closed sides, gives the horizontal derivative integral bound.
The quasiconformal constant is arbitrary; the genuine homeomorphic
boundary extension and its four ordered vertices remain in the producer.
The general QC and boundary-descent APIs are reused from Wu Xiaobin's
attributed LiZhongQC library; see its source manifest and third-party notices.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open Complex Set MeasureTheory Filter Topology LiZhongQC
open scoped ENNReal

namespace LowDimensionalTopology.Geometry.Teichmuller

private theorem rectangle_inner_side_norm_bound {r K : ℝ} {h G : ℂ → ℂ}
    (hqc : IsKQC h (rectangle r 1) K) (hGh : EqOn G h (rectangle r 1))
    {t : ℝ} (ht0 : 0 < t) (htr : 2 * t < r) (ht1 : 2 * t < 1) :
    ENNReal.ofReal ‖
      (∫ y in t..(1 - t), G (((r - t : ℝ) : ℂ) + (y : ℂ) * I)) -
      (∫ y in t..(1 - t), G ((t : ℂ) + (y : ℂ) * I))‖ ≤
        ∫⁻ z in rectangle r 1, ENNReal.ofReal ‖dz h z + dzbar h z‖ := by
  have htx : t < r - t := by linarith
  have hty : t < 1 - t := by linarith
  have hR : closedRect t (r - t) t (1 - t) ⊆ rectangle r 1 := by
    intro z hz
    obtain ⟨hx0, hxr, hy0, hy1⟩ := hz
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hloc : ∀ C ⊆ rectangle r 1, IsCompact C → IntegrableOn (partialX h) C := by
    intro C hCD hC
    let : IsFiniteMeasure (volume.restrict C) :=
      isFiniteMeasure_restrict.2 hC.measure_lt_top.ne
    exact MemLp.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      ((thm9_5_L2_derivatives hqc).1.1 C hCD hC).1
  have hside (u : ℝ) (hu : u ∈ Icc t (r - t)) :
      (∫ y in t..(1 - t), G ((u : ℂ) + (y : ℂ) * I)) =
        ∫ y in t..(1 - t), h ((u : ℂ) + (y : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    have hy' : y ∈ Icc t (1 - t) := by simpa [uIcc_of_le hty.le] using hy
    apply hGh
    apply hR
    simpa [closedRect] using (show t ≤ u ∧ u ≤ r - t ∧ t ≤ y ∧ y ≤ 1 - t from
      ⟨hu.1, hu.2, hy'.1, hy'.2⟩)
  have hgreen := eq9_10_green (thm9_1_isACL hqc) hloc htx hty hR
  rw [hside (r - t) ⟨htx.le, le_rfl⟩, hside t ⟨le_rfl, htx.le⟩, hgreen]
  calc ENNReal.ofReal ‖∫ z in openRect t (r - t) t (1 - t), partialX h z‖
      = ‖∫ z in openRect t (r - t) t (1 - t), partialX h z‖ₑ := ofReal_norm _
    _ ≤ ∫⁻ z in openRect t (r - t) t (1 - t), ‖partialX h z‖ₑ :=
        enorm_integral_le_lintegral_enorm (partialX h)
    _ ≤ ∫⁻ z in rectangle r 1, ‖partialX h z‖ₑ :=
        lintegral_mono_set ((openRect_subset_closedRect t (r - t) t (1 - t)).trans hR)
    _ = ∫⁻ z in rectangle r 1, ENNReal.ofReal ‖dz h z + dzbar h z‖ := by
        apply lintegral_congr_ae
        filter_upwards [thm9_3_differentiable_ae hqc] with z hz
        have hx : partialX h z = dz h z + dzbar h z := by
          rw [partialX_eq_of_differentiableAt hz]
          dsimp [dz, dzbar]
          ring
        rw [hx, ofReal_norm]

private theorem rectangle_endpoint_integral_of_sideLines
    {r s K : ℝ} {h G : ℂ → ℂ} (hr : 0 < r)
    (hqc : IsKQC h (rectangle r 1) K) (hG : Continuous G)
    (hGh : EqOn G h (rectangle r 1))
    (hleft : ∀ y ∈ Icc (0 : ℝ) 1, (G ((y : ℂ) * I)).re = 0)
    (hright : ∀ y ∈ Icc (0 : ℝ) 1, (G ((r : ℂ) + (y : ℂ) * I)).re = s) :
    ENNReal.ofReal s ≤
      ∫⁻ z in rectangle r 1, ENNReal.ofReal ‖dz h z + dzbar h z‖ := by
  let L : ℂ :=
    (∫ y in (0 : ℝ)..1, G ((r : ℂ) + (y : ℂ) * I)) -
      (∫ y in (0 : ℝ)..1, G ((y : ℂ) * I))
  have hlim : Tendsto (fun t : ℝ =>
      (∫ y in t..(1 - t), G (((r - t : ℝ) : ℂ) + (y : ℂ) * I)) -
      (∫ y in t..(1 - t), G ((t : ℂ) + (y : ℂ) * I)))
      (𝓝[>] 0) (𝓝 L) :=
    (rectangle_vertical_side_integrals_tendsto hG r).mono_left nhdsWithin_le_nhds
  have hbound : ENNReal.ofReal ‖L‖ ≤
      ∫⁻ z in rectangle r 1, ENNReal.ofReal ‖dz h z + dzbar h z‖ := by
    apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim.norm)
    have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t ∧ 2 * t < r ∧ 2 * t < 1 := by
      filter_upwards [Ioo_mem_nhdsGT
        (show (0 : ℝ) < min (r / 2) (1 / 2) by positivity)] with t ht
      refine ⟨ht.1, ?_, ?_⟩
      · have := ht.2.trans_le (min_le_left (r / 2) (1 / 2))
        linarith
      · have := ht.2.trans_le (min_le_right (r / 2) (1 / 2))
        linarith
    filter_upwards [hsmall] with t ht
    exact rectangle_inner_side_norm_bound hqc hGh ht.1 ht.2.1 ht.2.2
  have hintR : IntervalIntegrable
      (fun y : ℝ => G ((r : ℂ) + (y : ℂ) * I)) volume 0 1 :=
    (hG.comp (by fun_prop)).intervalIntegrable 0 1
  have hintL : IntervalIntegrable (fun y : ℝ => G ((y : ℂ) * I)) volume 0 1 :=
    (hG.comp (by fun_prop)).intervalIntegrable 0 1
  have hreR : (∫ y in (0 : ℝ)..1, G ((r : ℂ) + (y : ℂ) * I)).re = s := by
    calc (∫ y in (0 : ℝ)..1, G ((r : ℂ) + (y : ℂ) * I)).re
        = ∫ y in (0 : ℝ)..1, (G ((r : ℂ) + (y : ℂ) * I)).re := by
          simpa using (Complex.reCLM.intervalIntegral_comp_comm hintR).symm
      _ = ∫ _y in (0 : ℝ)..1, s := by
          apply intervalIntegral.integral_congr
          intro y hy
          exact hright y (by simpa [uIcc_of_le zero_le_one] using hy)
      _ = s := by simp
  have hreL : (∫ y in (0 : ℝ)..1, G ((y : ℂ) * I)).re = 0 := by
    calc (∫ y in (0 : ℝ)..1, G ((y : ℂ) * I)).re
        = ∫ y in (0 : ℝ)..1, (G ((y : ℂ) * I)).re := by
          simpa using (Complex.reCLM.intervalIntegral_comp_comm hintL).symm
      _ = ∫ _y in (0 : ℝ)..1, (0 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro y hy
          exact hleft y (by simpa [uIcc_of_le zero_le_one] using hy)
      _ = 0 := by simp
  have hreal : L.re = s := by
    dsimp [L]
    rw [hreR, hreL, sub_zero]
  have hnorm : s ≤ ‖L‖ := by
    calc s = L.re := hreal.symm
      _ ≤ |L.re| := le_abs_self _
      _ ≤ ‖L‖ := Complex.abs_re_le_norm L
  exact (ENNReal.ofReal_le_ofReal hnorm).trans hbound

/-- A general quasiconformal rectangle map with its actual closed
extension and all four ordered vertices has horizontal derivative
integral at least the width of the target rectangle. -/
theorem rectangle_horizontal_endpoint_integral_lower_bound
    {r s K : ℝ} (hr : 0 < r) (hs : 0 < s)
    {h : ℂ → ℂ} {H : ExtPlane → ExtPlane}
    (hqc : IsKQC h (rectangle r 1) K)
    (himage : h '' rectangle r 1 = rectangle s 1)
    (hH : IsHomeoExtension h (rectangle r 1) (rectangle s 1) H)
    (hv : ∀ i : Fin 4, H (rectVert r 1 i) = rectVert s 1 i) :
    ENNReal.ofReal s ≤
      ∫⁻ z in rectangle r 1, ENNReal.ofReal ‖dz h z + dzbar h z‖ := by
  obtain ⟨g, hclosed, hgcont, hginj, hgimage, hgh⟩ :=
    qcl_m_descend (isBounded_rectangle r 1) (isBounded_rectangle s 1) hH
  have hgopen : g '' rectangle r 1 = rectangle s 1 := by
    apply Eq.trans _ himage
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, (hgh hw).symm⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w, hw, hgh hw⟩
  have hmem (x y : ℝ) (hx : x ∈ Icc (0 : ℝ) r) (hy : y ∈ Icc (0 : ℝ) 1) :
      (x : ℂ) + (y : ℂ) * I ∈ closure (rectangle r 1) := by
    rw [mem_closure_rectangle_iff hr zero_lt_one]
    simpa using (show 0 ≤ x ∧ x ≤ r ∧ 0 ≤ y ∧ y ≤ 1 from
      ⟨hx.1, hx.2, hy.1, hy.2⟩)
  have hmem0 : (0 : ℂ) ∈ closure (rectangle r 1) := by
    simpa using hmem 0 0 ⟨le_rfl, hr.le⟩ ⟨le_rfl, zero_le_one⟩
  have hmem1 : (r : ℂ) ∈ closure (rectangle r 1) := by
    simpa using hmem r 0 ⟨hr.le, le_rfl⟩ ⟨le_rfl, zero_le_one⟩
  have hmem2 : (r : ℂ) + (1 : ℂ) * I ∈ closure (rectangle r 1) :=
    hmem r 1 ⟨hr.le, le_rfl⟩ ⟨zero_le_one, le_rfl⟩
  have hmem3 : (1 : ℂ) * I ∈ closure (rectangle r 1) := by
    simpa using hmem 0 1 ⟨le_rfl, hr.le⟩ ⟨zero_le_one, le_rfl⟩
  have h0 : g 0 = 0 := by
    apply OnePoint.coe_injective
    rw [hclosed 0 hmem0]
    simpa [rectVert] using hv (0 : Fin 4)
  have h1 : g (r : ℂ) = (s : ℂ) := by
    apply OnePoint.coe_injective
    rw [hclosed (r : ℂ) hmem1]
    simpa [rectVert] using hv (1 : Fin 4)
  have h2 : g ((r : ℂ) + (1 : ℂ) * I) = (s : ℂ) + (1 : ℂ) * I := by
    apply OnePoint.coe_injective
    rw [hclosed _ hmem2]
    simpa [rectVert] using hv (2 : Fin 4)
  have h3 : g ((1 : ℂ) * I) = (1 : ℂ) * I := by
    apply OnePoint.coe_injective
    rw [hclosed _ hmem3]
    simpa [rectVert] using hv (3 : Fin 4)
  have hsides := rect_sideLines_of_homeo hr zero_lt_one hs zero_lt_one
    hgopen hgcont hginj hgimage h0 h1 h2 h3
  obtain ⟨G, hG, hGg⟩ := rectangle_clamped_continuous_extension hr hgcont
  have hGh : EqOn G h (rectangle r 1) := by
    intro z hz
    exact (hGg (subset_closure hz)).trans (hgh hz)
  apply rectangle_endpoint_integral_of_sideLines hr hqc hG hGh
  · intro y hy
    have hz : (y : ℂ) * I ∈ closure (rectangle r 1) := by
      simpa using hmem 0 y ⟨le_rfl, hr.le⟩ hy
    rw [hGg hz]
    exact hsides.2.2.1 y hy
  · intro y hy
    rw [hGg (hmem r y ⟨hr.le, le_rfl⟩ hy)]
    exact hsides.2.2.2 y hy

end LowDimensionalTopology.Geometry.Teichmuller
