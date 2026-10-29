/-
The coordinate-integral construction below localizes Wu Xiaobin's D4 proof in
Li-Zhong-QC-formalization, Ch02/S12_Existence.lean, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2 (Apache-2.0).
The extension theorem and rectangle definitions retain their external attribution.
-/
module

public import LowDimensionalTopology.External.LiZhongQC.Ch02.S12_Existence

/-!
# A local potential on a rectangle

A continuous real one-form whose integrals vanish around all subrectangles
has a real C1 potential on the open rectangle. Values outside the given closed
rectangle are introduced only through continuous extensions for the coordinate
integral construction. No closedness outside that rectangle is assumed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Metric MeasureTheory Filter Topology
open LiZhongQC intervalIntegral

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Local coordinate potential from vanishing boundary integrals on every
subrectangle. Both actual coordinate derivatives agree with the given data. -/
theorem exists_contDiffOn_primitive_on_rectangle
    {P Q : ℂ → ℂ} {a b c d : ℝ} (_hab : a < b) (hcd : c < d)
    (hP : ContinuousOn P (closedRect a b c d))
    (hQ : ContinuousOn Q (closedRect a b c d))
    (hrect : ∀ x u y v : ℝ, x < u → y < v →
      closedRect x u y v ⊆ closedRect a b c d →
      (∫ t in x..u, P ((t : ℂ) + (y : ℂ) * I)) +
        (∫ s in y..v, Q ((u : ℂ) + (s : ℂ) * I)) -
        (∫ t in x..u, P ((t : ℂ) + (v : ℂ) * I)) -
        (∫ s in y..v, Q ((x : ℂ) + (s : ℂ) * I)) = 0) :
    ∃ F : ℂ → ℂ, ContDiffOn ℝ 1 F (openRect a b c d) ∧
      ∀ z ∈ openRect a b c d,
        fderiv ℝ F z 1 = P z ∧ fderiv ℝ F z I = Q z := by
  obtain ⟨P₀, hP₀, hP₀eq⟩ :=
    acl_exists_continuous_ext (acl_isCompact_closedRect a b c d).isClosed hP
  obtain ⟨Q₀, hQ₀, hQ₀eq⟩ :=
    acl_exists_continuous_ext (acl_isCompact_closedRect a b c d).isClosed hQ
  have hPeq : ∀ {x u y : ℝ}, x ∈ Icc a b → u ∈ Icc a b → y ∈ Icc c d →
      (∫ t in x..u, P₀ ((t : ℂ) + (y : ℂ) * I)) =
        ∫ t in x..u, P ((t : ℂ) + (y : ℂ) * I) := by
    intro x u y hx hu hy
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : a ≤ t ∧ t ≤ b :=
      ⟨(le_min hx.1 hu.1).trans ht.1, ht.2.trans (max_le hx.2 hu.2)⟩
    apply hP₀eq
    simpa [closedRect] using
      (show a ≤ t ∧ t ≤ b ∧ c ≤ y ∧ y ≤ d from ⟨ht'.1, ht'.2, hy.1, hy.2⟩)
  have hQeq : ∀ {x y v : ℝ}, x ∈ Icc a b → y ∈ Icc c d → v ∈ Icc c d →
      (∫ s in y..v, Q₀ ((x : ℂ) + (s : ℂ) * I)) =
        ∫ s in y..v, Q ((x : ℂ) + (s : ℂ) * I) := by
    intro x y v hx hy hv
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : c ≤ s ∧ s ≤ d :=
      ⟨(le_min hy.1 hv.1).trans hs.1, hs.2.trans (max_le hy.2 hv.2)⟩
    apply hQ₀eq
    simpa [closedRect] using
      (show a ≤ x ∧ x ≤ b ∧ c ≤ s ∧ s ≤ d from ⟨hx.1, hx.2, hs'.1, hs'.2⟩)
  have hrect₀ : ∀ x u y v : ℝ, x ∈ Icc a b → u ∈ Icc a b →
      y ∈ Icc c d → v ∈ Icc c d → x < u → y < v →
      (∫ t in x..u, P₀ ((t : ℂ) + (y : ℂ) * I)) +
        (∫ s in y..v, Q₀ ((u : ℂ) + (s : ℂ) * I)) -
        (∫ t in x..u, P₀ ((t : ℂ) + (v : ℂ) * I)) -
        (∫ s in y..v, Q₀ ((x : ℂ) + (s : ℂ) * I)) = 0 := by
    intro x u y v hx hu hy hv hxu hyv
    rw [hPeq hx hu hy, hQeq hu hy hv, hPeq hx hu hv, hQeq hx hy hv]
    apply hrect x u y v hxu hyv
    intro z hz
    exact ⟨hx.1.trans hz.1, hz.2.1.trans hu.2,
      hy.1.trans hz.2.2.1, hz.2.2.2.trans hv.2⟩
  have hzero : ∀ x u y v : ℝ, x ∈ Icc a b → u ∈ Icc a b →
      y ∈ Icc c d → v ∈ Icc c d →
      (∫ t in x..u, P₀ ((t : ℂ) + (y : ℂ) * I)) +
        (∫ s in y..v, Q₀ ((u : ℂ) + (s : ℂ) * I)) -
        (∫ t in x..u, P₀ ((t : ℂ) + (v : ℂ) * I)) -
        (∫ s in y..v, Q₀ ((x : ℂ) + (s : ℂ) * I)) = 0 := by
    intro x u y v hx hu hy hv
    rcases lt_trichotomy x u with hxu | hxu | hxu
    · rcases lt_trichotomy y v with hyv | hyv | hyv
      · exact hrect₀ x u y v hx hu hy hv hxu hyv
      · subst hyv; simp
      · have h0 := hrect₀ x u v y hx hu hv hy hxu hyv
        have es1 : (∫ s in v..y, Q₀ ((u : ℂ) + (s : ℂ) * I)) =
            -∫ s in y..v, Q₀ ((u : ℂ) + (s : ℂ) * I) := integral_symm y v
        have es2 : (∫ s in v..y, Q₀ ((x : ℂ) + (s : ℂ) * I)) =
            -∫ s in y..v, Q₀ ((x : ℂ) + (s : ℂ) * I) := integral_symm y v
        linear_combination -h0 + es1 - es2
    · subst hxu; simp
    · rcases lt_trichotomy y v with hyv | hyv | hyv
      · have h0 := hrect₀ u x y v hu hx hy hv hxu hyv
        have es1 : (∫ t in u..x, P₀ ((t : ℂ) + (y : ℂ) * I)) =
            -∫ t in x..u, P₀ ((t : ℂ) + (y : ℂ) * I) := integral_symm x u
        have es2 : (∫ t in u..x, P₀ ((t : ℂ) + (v : ℂ) * I)) =
            -∫ t in x..u, P₀ ((t : ℂ) + (v : ℂ) * I) := integral_symm x u
        linear_combination -h0 + es1 - es2
      · subst hyv; simp
      · have h0 := hrect₀ u x v y hu hx hv hy hxu hyv
        have es1 : (∫ t in u..x, P₀ ((t : ℂ) + (v : ℂ) * I)) =
            -∫ t in x..u, P₀ ((t : ℂ) + (v : ℂ) * I) := integral_symm x u
        have es2 : (∫ t in u..x, P₀ ((t : ℂ) + (y : ℂ) * I)) =
            -∫ t in x..u, P₀ ((t : ℂ) + (y : ℂ) * I) := integral_symm x u
        have es3 : (∫ s in v..y, Q₀ ((x : ℂ) + (s : ℂ) * I)) =
            -∫ s in y..v, Q₀ ((x : ℂ) + (s : ℂ) * I) := integral_symm y v
        have es4 : (∫ s in v..y, Q₀ ((u : ℂ) + (s : ℂ) * I)) =
            -∫ s in y..v, Q₀ ((u : ℂ) + (s : ℂ) * I) := integral_symm y v
        linear_combination h0 - es1 + es2 - es3 + es4
  set F : ℂ → ℂ := fun z =>
    (∫ t in a..z.re, P₀ ((t : ℂ) + (c : ℂ) * I)) +
      ∫ s in c..z.im, Q₀ ((z.re : ℂ) + (s : ℂ) * I) with hFdef
  have hFval : ∀ x y : ℝ, F ((x : ℂ) + (y : ℂ) * I) =
      (∫ t in a..x, P₀ ((t : ℂ) + (c : ℂ) * I)) +
        ∫ s in c..y, Q₀ ((x : ℂ) + (s : ℂ) * I) := by
    intro x y
    simp [hFdef]
  have hkey : ∀ x u y : ℝ, x ∈ Icc a b → u ∈ Icc a b → y ∈ Icc c d →
      F ((u : ℂ) + (y : ℂ) * I) - F ((x : ℂ) + (y : ℂ) * I) =
        ∫ t in x..u, P₀ ((t : ℂ) + (y : ℂ) * I) := by
    intro x u y hx hu hy
    have h0 := hzero x u c y hx hu ⟨le_rfl, hcd.le⟩ hy
    have hline : Continuous (fun t : ℝ => P₀ ((t : ℂ) + (c : ℂ) * I)) :=
      hP₀.comp (by fun_prop)
    have hadd : (∫ t in a..x, P₀ ((t : ℂ) + (c : ℂ) * I)) +
        (∫ t in x..u, P₀ ((t : ℂ) + (c : ℂ) * I)) =
        ∫ t in a..u, P₀ ((t : ℂ) + (c : ℂ) * I) :=
      intervalIntegral.integral_add_adjacent_intervals
        (hline.intervalIntegrable a x) (hline.intervalIntegrable x u)
    rw [hFval, hFval]
    linear_combination h0 - hadd
  have hxderiv : ∀ x y : ℝ, x ∈ Ioo a b → y ∈ Icc c d →
      HasStrictDerivAt (fun u : ℝ => F ((u : ℂ) + (y : ℂ) * I))
        (P₀ ((x : ℂ) + (y : ℂ) * I)) x := by
    intro x y hx hy
    have hcont : Continuous (fun t : ℝ => P₀ ((t : ℂ) + (y : ℂ) * I)) :=
      hP₀.comp (by fun_prop)
    have hbase := (hcont.integral_hasStrictDerivAt x x).const_add
      (F ((x : ℂ) + (y : ℂ) * I))
    apply hbase.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with u hu
    change F ((x : ℂ) + (y : ℂ) * I) +
      (∫ t in x..u, P₀ ((t : ℂ) + (y : ℂ) * I)) = F ((u : ℂ) + (y : ℂ) * I)
    linear_combination -(hkey x u y ⟨hx.1.le, hx.2.le⟩ ⟨hu.1.le, hu.2.le⟩ hy)
  have hyderiv : ∀ x y : ℝ,
      HasStrictDerivAt (fun v : ℝ => F ((x : ℂ) + (v : ℂ) * I))
        (Q₀ ((x : ℂ) + (y : ℂ) * I)) y := by
    intro x y
    have hcont : Continuous (fun s : ℝ => Q₀ ((x : ℂ) + (s : ℂ) * I)) :=
      hQ₀.comp (by fun_prop)
    have hbase := (hcont.integral_hasStrictDerivAt c y).const_add
      (∫ t in a..x, P₀ ((t : ℂ) + (c : ℂ) * I))
    have hfe : (fun v : ℝ => (∫ t in a..x, P₀ ((t : ℂ) + (c : ℂ) * I)) +
        ∫ s in c..v, Q₀ ((x : ℂ) + (s : ℂ) * I)) =
        (fun v : ℝ => F ((x : ℂ) + (v : ℂ) * I)) :=
      funext fun v => (hFval x v).symm
    rwa [hfe] at hbase
  set f₁ : ℝ → ℝ → (ℝ →L[ℝ] ℂ) := fun x y =>
    ContinuousLinearMap.toSpanSingleton ℝ (P₀ ((x : ℂ) + (y : ℂ) * I)) with hf₁def
  set f₂ : ℝ → ℝ → (ℝ →L[ℝ] ℂ) := fun x y =>
    ContinuousLinearMap.toSpanSingleton ℝ (Q₀ ((x : ℂ) + (y : ℂ) * I)) with hf₂def
  have hcf₁ : Continuous (↿f₁ : ℝ × ℝ → ℝ →L[ℝ] ℂ) := by
    have heq : (↿f₁ : ℝ × ℝ → ℝ →L[ℝ] ℂ) = fun v : ℝ × ℝ =>
        ContinuousLinearMap.toSpanSingletonLIE ℝ ℂ
          (P₀ ((v.1 : ℂ) + (v.2 : ℂ) * I)) := rfl
    rw [heq]
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℂ).continuous.comp (by fun_prop)
  have hcf₂ : Continuous (↿f₂ : ℝ × ℝ → ℝ →L[ℝ] ℂ) := by
    have heq : (↿f₂ : ℝ × ℝ → ℝ →L[ℝ] ℂ) = fun v : ℝ × ℝ =>
        ContinuousLinearMap.toSpanSingletonLIE ℝ ℂ
          (Q₀ ((v.1 : ℂ) + (v.2 : ℂ) * I)) := rfl
    rw [heq]
    exact (ContinuousLinearMap.toSpanSingletonLIE ℝ ℂ).continuous.comp (by fun_prop)
  have huncurry : ∀ u ∈ Ioo a b ×ˢ Ioo c d,
      HasStrictFDerivAt (Function.uncurry fun x y : ℝ => F ((x : ℂ) + (y : ℂ) * I))
        ((↿f₁ u).coprod (↿f₂ u)) u := by
    intro u hu
    apply hasStrictFDerivAt_uncurry_coprod
      (f := fun x y : ℝ => F ((x : ℂ) + (y : ℂ) * I))
    · filter_upwards [(isOpen_Ioo.prod isOpen_Ioo).mem_nhds hu] with v hv
      exact (hxderiv v.1 v.2 hv.1 ⟨hv.2.1.le, hv.2.2.le⟩).hasDerivAt.hasFDerivAt
    · exact Eventually.of_forall fun v => (hyderiv v.1 v.2).hasDerivAt.hasFDerivAt
    · exact hcf₁.continuousAt
    · exact hcf₂.continuousAt
  have hFcomp : ∀ z : ℂ, F z =
      (Function.uncurry fun x y : ℝ => F ((x : ℂ) + (y : ℂ) * I))
        (Complex.equivRealProdCLM z) := by
    intro z
    show F z = F ((z.re : ℂ) + (z.im : ℂ) * I)
    rw [Complex.re_add_im]
  have hFstrict : ∀ z ∈ openRect a b c d, HasStrictFDerivAt F
      (((↿f₁ (Complex.equivRealProdCLM z)).coprod (↿f₂ (Complex.equivRealProdCLM z))).comp
        Complex.equivRealProdCLM.toContinuousLinearMap) z := by
    intro z hz
    have hz' : Complex.equivRealProdCLM z ∈ Ioo a b ×ˢ Ioo c d :=
      ⟨⟨hz.1, hz.2.1⟩, ⟨hz.2.2.1, hz.2.2.2⟩⟩
    have hcomp := (huncurry (Complex.equivRealProdCLM z) hz').comp z
      Complex.equivRealProdCLM.hasStrictFDerivAt
    have hfe : (fun x =>
        (Function.uncurry fun x y : ℝ => F ((x : ℂ) + (y : ℂ) * I))
          (Complex.equivRealProdCLM x)) = F := funext fun z' => (hFcomp z').symm
    rwa [hfe] at hcomp
  have hDcont : Continuous fun z : ℂ =>
      (((↿f₁ (Complex.equivRealProdCLM z)).coprod (↿f₂ (Complex.equivRealProdCLM z))).comp
        Complex.equivRealProdCLM.toContinuousLinearMap) := by
    have hcont1 : Continuous fun z : ℂ => ↿f₁ (Complex.equivRealProdCLM z) :=
      hcf₁.comp Complex.equivRealProdCLM.continuous
    have hcont2 : Continuous fun z : ℂ => ↿f₂ (Complex.equivRealProdCLM z) :=
      hcf₂.comp Complex.equivRealProdCLM.continuous
    fun_prop
  refine ⟨F, ?_, fun z hz => ?_⟩
  · have hC1 : ContDiffOn ℝ (0 + 1 : WithTop ℕ∞) F (openRect a b c d) := by
      rw [contDiffOn_succ_iff_fderiv_of_isOpen (acl_isOpen_openRect a b c d)]
      refine ⟨fun z hz => (hFstrict z hz).differentiableAt.differentiableWithinAt, by simp, ?_⟩
      apply contDiffOn_zero.mpr
      exact hDcont.continuousOn.congr fun z hz => (hFstrict z hz).hasFDerivAt.fderiv
    simpa only [zero_add] using hC1
  · have hz1 : Complex.equivRealProdCLM (1 : ℂ) = (1, 0) := by
      change ((1 : ℂ).re, (1 : ℂ).im) = (1, 0)
      norm_num
    have hzI : Complex.equivRealProdCLM (I : ℂ) = (0, 1) := by
      change ((I : ℂ).re, (I : ℂ).im) = (0, 1)
      norm_num
    have h1 : fderiv ℝ F z 1 =
        (((↿f₁ (Complex.equivRealProdCLM z)).coprod (↿f₂ (Complex.equivRealProdCLM z))).comp
          Complex.equivRealProdCLM.toContinuousLinearMap) 1 := by
      rw [(hFstrict z hz).hasFDerivAt.fderiv]
    have hI : fderiv ℝ F z I =
        (((↿f₁ (Complex.equivRealProdCLM z)).coprod (↿f₂ (Complex.equivRealProdCLM z))).comp
          Complex.equivRealProdCLM.toContinuousLinearMap) I := by
      rw [(hFstrict z hz).hasFDerivAt.fderiv]
    have hzclosed : z ∈ closedRect a b c d :=
      ⟨hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le⟩
    rw [h1, hI, ← hP₀eq hzclosed, ← hQ₀eq hzclosed]
    simp [hz1, hzI, ContinuousLinearMap.coprod_apply]
    constructor
    · show (↿f₁ ((z.re : ℝ), (z.im : ℝ))) (1 : ℝ) = P₀ z
      have hthis : (↿f₁ ((z.re : ℝ), (z.im : ℝ))) (1 : ℝ) = f₁ z.re z.im 1 := rfl
      rw [hthis, hf₁def, ContinuousLinearMap.toSpanSingleton_apply, one_smul, Complex.re_add_im]
    · show (↿f₂ ((z.re : ℝ), (z.im : ℝ))) (1 : ℝ) = Q₀ z
      have hthis : (↿f₂ ((z.re : ℝ), (z.im : ℝ))) (1 : ℝ) = f₂ z.re z.im 1 := rfl
      rw [hthis, hf₂def, ContinuousLinearMap.toSpanSingleton_apply, one_smul, Complex.re_add_im]

end LowDimensionalTopology.Geometry.Quasiconformal
