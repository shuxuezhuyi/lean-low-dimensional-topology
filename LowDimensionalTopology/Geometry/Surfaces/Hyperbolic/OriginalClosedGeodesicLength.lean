module

public import LowDimensionalTopology.Geometry.Surfaces.Hyperbolic.OriginalClosedGeodesicExistence
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Dynamics.Circle.RotationNumber.TranslationNumber
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.SeparatedMap
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Full original closed-geodesic length and the actual matrix trace

The entire given original period is proved rectifiable in the original atlas.
For every given actual hyperbolic covering matrix, genuine free-homotopy
lifting aligns an arbitrary original parametrization to that SAME matrix.
A monotone onto parameter change identifies the original whole-period BV
integral with the native C1 traversal of its full actual axis interval,
preserving multiplicity. This general statement requires no compactness.
The same original local arc data derives a hyperbolic full-period covering
matrix even on a noncompact original surface.
-/

public section
noncomputable section
open Set Filter
open scoped UpperHalfPlane unitInterval Topology MatrixGroups ENNReal

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.Mobius

/-- The complete given parameter period is rectifiable in the original atlas;
this follows from the actual local arc data, including the period endpoints. -/
theorem OriginalClosedGeodesic.chartwiseBVOn_period
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M) :
    R.toRiemannAtlas.IsChartwiseBVOn q.curve (Icc 0 1) := by
  obtain ⟨_hc, hlocal⟩ := q.locallyMinimizing
  intro x _hxI
  obtain ⟨_O, a, b, _hOopen, _hxO, hax, hxb, _hO, _hinj, hmin⟩ := hlocal x
  let s := (a + x) / 2
  let t := (x + b) / 2
  have hsx : s < x := by dsimp only [s]; linarith
  have hxt : x < t := by dsimp only [t]; linarith
  have hsJ : s ∈ Ioo a b := by dsimp only [s]; constructor <;> linarith
  have htJ : t ∈ Ioo a b := by dsimp only [t]; constructor <;> linarith
  obtain ⟨hrect, _hminimum⟩ := hmin s hsJ t htJ (hsx.trans hxt)
  obtain ⟨e, he, hex, U, hU, _hUsub, hUmap, hBV⟩ := hrect x ⟨hsx.le, hxt.le⟩
  have hU' : U ∈ 𝓝 x := by
    simpa only [nhdsWithin_eq_nhds.mpr (Icc_mem_nhds hsx hxt)] using hU
  let W := Icc (0 : ℝ) 1 ∩ U
  refine ⟨e, he, hex, W,
    inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hU'),
    inter_subset_left, fun _ ht => hUmap ht.2, hBV.mono inter_subset_right⟩

/-- The actual entire loop in the original-atlas full-BV curve class. -/
@[expose] def OriginalClosedGeodesic.toRectifiable
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M) :
    RiemannSurfaceRectifiableCurvePiece R where
  curve := q.toLoop.2.toContinuousMap
  rectifiable := by
    apply q.chartwiseBVOn_period.congr
    intro t ht
    change q.curve t = q.curve ((projIcc 0 1 zero_le_one t : I) : ℝ)
    rw [projIcc_of_mem zero_le_one ht]

/-- The full literal original hyperbolic length during the whole given period,
including every proper-power traversal. -/
@[expose] def OriginalClosedGeodesic.length
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M) : ℝ≥0∞ :=
  M.rectifiableCurveLength q.toRectifiable

private theorem not_isLocalMax_of_continuous_locallyInjective_real
    {f : ℝ → ℝ} (hf : Continuous f) (hinj : IsLocallyInjective f) (x : ℝ) :
    ¬ IsLocalMax f x := by
  intro hmax
  obtain ⟨U, hUopen, hxU, hUinj⟩ := hinj x
  have hnear : ∀ᶠ y in 𝓝 x, y ∈ U ∧ f y ≤ f x :=
    inter_mem (hUopen.mem_nhds hxU) hmax
  obtain ⟨a, b, ⟨hax, hxb⟩, hsub⟩ := hnear.exists_Ioo_subset
  have hx : x ∈ Ioo a b := ⟨hax, hxb⟩
  have hIinj : InjOn f (Ioo a b) := hUinj.mono (fun _ ht => (hsub ht).1)
  rcases ContinuousOn.strictMonoOn_of_injOn_Ioo (hax.trans hxb)
      hf.continuousOn hIinj with hmono | hanti
  · have hy : (x + b) / 2 ∈ Ioo a b := by constructor <;> linarith
    have hxy : x < (x + b) / 2 := by linarith
    exact (not_lt_of_ge (hsub hy).2) (hmono hx hy hxy)
  · have hy : (a + x) / 2 ∈ Ioo a b := by constructor <;> linarith
    have hyx : (a + x) / 2 < x := by linarith
    exact (not_lt_of_ge (hsub hy).2) (hanti hy hx hyx)

private theorem false_of_equal_endpoints_and_interior_peak
    {f : ℝ → ℝ} (hf : Continuous f) (hinj : IsLocallyInjective f)
    {a b y : ℝ} (hab : a < b) (hay : a < y) (hyb : y < b)
    (hpeak : f a < f y) (hend : f a = f b) : False := by
  have hy : y ∈ Icc a b := ⟨hay.le, hyb.le⟩
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr hab.le) hf.continuousOn
  have hhigh : f a < f x := hpeak.trans_le (hmax hy)
  have hax : a < x := lt_of_le_of_ne hx.1 (fun he => hhigh.ne (congrArg f he))
  have hxb : x < b := lt_of_le_of_ne hx.2 (fun he =>
    hhigh.ne ((congrArg f he).trans hend.symm).symm)
  exact not_isLocalMax_of_continuous_locallyInjective_real hf hinj x
    (hmax.isLocalMax (Icc_mem_nhds hax hxb))

private theorem injective_of_continuous_locallyInjective_real
    {f : ℝ → ℝ} (hf : Continuous f) (hinj : IsLocallyInjective f) :
    Function.Injective f := by
  have hordered : ∀ a b : ℝ, a < b → f a ≠ f b := by
    intro a b hab hend
    obtain ⟨U, hUopen, haU, hUinj⟩ := hinj a
    have hnear : ∀ᶠ y in 𝓝 a, y ∈ U ∧ y < b :=
      inter_mem (hUopen.mem_nhds haU) (Iio_mem_nhds hab)
    obtain ⟨l, u, ⟨hla, hau⟩, hsub⟩ := hnear.exists_Ioo_subset
    let y : ℝ := (a + u) / 2
    have hay : a < y := by dsimp only [y]; linarith
    have hyu : y < u := by dsimp only [y]; linarith
    have hy : y ∈ Ioo l u := ⟨hla.trans hay, hyu⟩
    have hyb : y < b := (hsub hy).2
    have hne : f y ≠ f a := by
      intro he
      exact hay.ne' (hUinj (hsub hy).1 haU he)
    rcases lt_or_gt_of_ne hne with hdown | hup
    · exact false_of_equal_endpoints_and_interior_peak hf.neg
        (hinj.comp_left (g := fun z : ℝ => -z) neg_injective) hab hay hyb
        (neg_lt_neg hdown) (congrArg (fun z : ℝ => -z) hend)
    · exact false_of_equal_endpoints_and_interior_peak hf hinj hab hay hyb hup hend
  intro a b hab
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exact (hordered a b hlt hab).elim
  · exact heq
  · exact (hordered b a hgt hab.symm).elim

private theorem strictMono_or_strictAnti_of_continuous_locallyInjective_real
    {f : ℝ → ℝ} (hf : Continuous f) (hinj : IsLocallyInjective f) :
    StrictMono f ∨ StrictAnti f :=
  hf.strictMono_of_inj (injective_of_continuous_locallyInjective_real hf hinj)


private theorem coordinate_on_isometric_line
    {f γ : ℝ → ℍ} (hf : Continuous f) (hfinj : IsLocallyInjective f)
    (hγ : Isometry γ) (hfrange : range f ⊆ range γ) :
    ∃ κ : ℝ → ℝ, Continuous κ ∧ (StrictMono κ ∨ StrictAnti κ) ∧
      ∀ t : ℝ, γ (κ t) = f t := by
  let e := hγ.isometryEquivOnRange
  let κ : ℝ → ℝ := fun t => e.symm ⟨f t, hfrange (mem_range_self t)⟩
  have hκ : Continuous κ := e.symm.continuous.comp
    (hf.subtype_mk (fun t => hfrange (mem_range_self t)))
  have hpoint (t : ℝ) : γ (κ t) = f t := congrArg Subtype.val
    (e.apply_symm_apply ⟨f t, hfrange (mem_range_self t)⟩)
  have hκinj : IsLocallyInjective κ := by
    intro x
    obtain ⟨U, hUopen, hxU, hUinj⟩ := hfinj x
    refine ⟨U, hUopen, hxU, ?_⟩
    intro s hs t ht he
    exact hUinj hs ht ((hpoint s).symm.trans ((congrArg γ he).trans (hpoint t)))
  exact ⟨κ, hκ, strictMono_or_strictAnti_of_continuous_locallyInjective_real hκ hκinj, hpoint⟩

private theorem projection_ne_one_of_hyperbolic_trace
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (ht : 4 < (Matrix.trace A.val) ^ 2) :
    realSLMobius A ≠ 1 := by
  intro he
  have hidentity : mobiusSquaredTrace (1 : complexMobiusGroup) = (4 : ℂ) := by
    have hh := realSLMobius_squaredTrace (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    norm_num [Matrix.trace_fin_two] at hh
    exact hh
  have hh := congrArg mobiusSquaredTrace he
  rw [realSLMobius_squaredTrace, hidentity] at hh
  have hr : (Matrix.trace A.val) ^ 2 = 4 := Complex.ofReal_injective hh
  linarith

private theorem locallyInjective_actual_curve_lift
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M)
    (f : ℝ → ℍ) (hproj : ∀ t : ℝ, M.halfPlaneCover (f t) = q.curve t) :
    IsLocallyInjective f := by
  obtain ⟨_hc, hlocal⟩ := q.locallyMinimizing
  intro x
  obtain ⟨_O, a, b, _hOopen, _hxO, hax, hxb, _hO, hinj, _hmin⟩ := hlocal x
  refine ⟨Ioo a b, isOpen_Ioo, ⟨hax, hxb⟩, ?_⟩
  intro s hs t ht he
  exact hinj hs ht ((hproj s).symm.trans
    ((congrArg M.halfPlaneCover he).trans (hproj t)))

private theorem whole_period_length_of_equivariant_line_lift
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A ≠ 1)
    (ht : 4 < (Matrix.trace A.val) ^ 2) (f : C(ℝ, ℍ))
    (hproj : ∀ t : ℝ, M.halfPlaneCover (f t) = q.curve t)
    (S : Set ℍ) (hS : IsHalfPlaneHLine S) (hfS : range f ⊆ S)
    (hperiod : ∀ t : ℝ, f (t + 1) = A • f t) :
    q.length = ENNReal.ofReal (hTranslationLength (hSLIsometry A)) := by
  have hfinj := locallyInjective_actual_curve_lift q f hproj
  have haxis := equivariant_arc_supporting_line_eq_axis A hA ht hfinj hS hfS 1 hperiod
  obtain ⟨γ, hγ, hγaxis, hpositive, hγperiod⟩ := exists_unitSpeed_axis_with_actual_period A hA ht
  obtain ⟨κ, hκcont, hκorient, hκpoint⟩ := coordinate_on_isometric_line f.continuous hfinj hγ.1
    (by rw [hγaxis]; exact fun z hz => haxis ▸ hfS hz)
  let T := hTranslationLength (hSLIsometry A)
  have hT : 0 < T := hpositive
  have hκ1 : κ 1 = κ 0 + T := by
    apply hγ.1.injective
    rw [hκpoint, hγperiod, hκpoint]
    simpa only [zero_add] using hperiod 0
  have hκmono : StrictMono κ := hκorient.resolve_right (by
    intro ha
    have he := ha (show (0 : ℝ) < 1 by norm_num)
    linarith [hT])
  have hκdiff : κ 1 - κ 0 = T := by linarith
  obtain ⟨d, hda, hdb, hdpoint, hdlen⟩ :=
    hγ.exists_c1_affine_piece (κ 0) (κ 1) (by linarith [hT])
  let e : C(I, ℍ) := ⟨fun t => f (t : ℝ), f.continuous.comp continuous_subtype_val⟩
  obtain ⟨c, hca, hcb, hcpoint, hclen⟩ :=
    M.exists_rectifiableCurve_of_continuous_lift q.toRectifiable e (fun t => hproj t)
  let reparam : ℝ → ℝ := fun t => (κ t - κ 0) / T
  have hσcont : Continuous reparam := (hκcont.sub continuous_const).div_const T
  have hσmono : Monotone reparam := by
    intro s t hst
    exact div_le_div_of_nonneg_right (sub_le_sub_right (hκmono.monotone hst) _) hT.le
  have hσ0 : reparam 0 = 0 := by simp [reparam]
  have hσ1 : reparam 1 = 1 := by dsimp only [reparam]; rw [hκdiff]; exact div_self hT.ne'
  have hσimage : reparam '' Icc 0 1 = Icc 0 1 := by
    simpa only [hσ0, hσ1] using
      hσcont.continuousOn.image_Icc_of_monotoneOn zero_le_one
        (hσmono.monotoneOn (Icc (0 : ℝ) 1))
  let ρ : ℂ → ℝ≥0∞ := fun ζ => ENNReal.ofReal (1 / ζ.im)
  have htransport : c.weightedLength ρ = d.toRectifiableCurve.weightedLength ρ := by
    apply RectifiableCurve.weightedLength_eq_of_monotone_onto_reparam
      c d.toRectifiableCurve reparam
    · simpa only [hca, hcb] using hσmono.monotoneOn (s := Icc (0 : ℝ) 1)
    · simpa only [hca, hcb, C1CurvePiece.toRectifiableCurve_a,
        C1CurvePiece.toRectifiableCurve_b, hda, hdb] using hσimage
    · simpa only [hca, C1CurvePiece.toRectifiableCurve_a, hda] using hσ0
    · simpa only [hcb, C1CurvePiece.toRectifiableCurve_b, hdb] using hσ1
    · intro t ht'
      have htI : t ∈ Icc (0 : ℝ) 1 := by simpa only [hca, hcb] using ht'
      rw [hcpoint ⟨t, htI⟩]
      change (f t : ℂ) = (d.curve (reparam t) : ℂ)
      apply congrArg ((↑) : ℍ → ℂ)
      rw [← hκpoint t, hdpoint]
      apply congrArg γ
      rw [hκdiff]
      dsimp only [reparam]
      rw [← mul_div_assoc, mul_div_cancel_left₀ _ hT.ne']
      ring
  calc
    q.length = c.weightedLength ρ := hclen.symm
    _ = d.toRectifiableCurve.weightedLength ρ := htransport
    _ = ENNReal.ofReal d.length := d.toRectifiableCurve_weightedLength hda hdb
    _ = ENNReal.ofReal T := congrArg ENNReal.ofReal (hdlen.trans hκdiff)

/-- The full original arbitrary-parameter geodesic length is
exactly the translation length of the GIVEN actual hyperbolic covering matrix.
The surface and its actual half-plane cover are unchanged. No compactness,
non-null, global-lift, unit-speed or primitive-generator hypothesis is added. -/
theorem OriginalClosedGeodesic.length_eq_translationLength_of_covers
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAΓ : A ∈ Γ)
    (ht : 4 < (Matrix.trace A.val) ^ 2)
    (hcov : LiZhongQC.Covers M.halfPlaneCover A q.toLoop) :
    q.length = ENNReal.ofReal (hTranslationLength (hSLIsometry A)) := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨f, S, hproj, hS, hfS⟩ := q.locallyMinimizing.exists_hLine_lift
  let d : C(I, ℍ) := ⟨fun t => f (t : ℝ), f.continuous.comp continuous_subtype_val⟩
  have hd (t : I) : M.halfPlaneCover (d t) = q.toLoop.2 t := hproj t
  obtain ⟨C, hC, hend⟩ := LiZhongQC.s30a_fh_fwd hp hAΓ hcov
    (LiZhongQC.s30b_fh_of_eq (fun _ => rfl)) d hd
  change f 1 = (C * A * C⁻¹) • f 0 at hend
  let η : C(ℝ, ℍ) := ⟨fun t => C⁻¹ • f t, (continuous_const_smul C⁻¹).comp f.continuous⟩
  have hηproj (t : ℝ) : M.halfPlaneCover (η t) = q.curve t := by
    change M.halfPlaneCover (C⁻¹ • f t) = q.curve t
    rw [LiZhongQC.s30a_p_smul hp (Γ.inv_mem hC), hproj]
  have hηend : η 1 = A • η 0 := by
    change C⁻¹ • f 1 = A • (C⁻¹ • f 0)
    rw [hend]
    simp only [mul_smul, inv_smul_smul]
  have hperiod : ∀ t : ℝ, η (t + 1) = A • η t := by
    have hwhole : (fun t : ℝ => η (t + 1)) = (fun t => A • η t) := by
      apply hp.1.eq_of_comp_eq
        (η.continuous.comp (continuous_id.add continuous_const))
        ((continuous_const_smul A).comp η.continuous) ?_ 0 ?_
      · funext t
        change M.halfPlaneCover (η (t + 1)) = M.halfPlaneCover (A • η t)
        rw [hηproj, LiZhongQC.s30a_p_smul hp hAΓ, hηproj, q.periodic t]
      · change η (0 + 1) = A • η 0
        simpa only [zero_add] using hηend
    exact fun t => congrFun hwhole t
  obtain ⟨L, hL⟩ := exists_halfPlaneLine_of_isHLine hS
  obtain ⟨N, hN⟩ := LowDimensionalTopology.Geometry.Hyperbolic.Isometry.halfPlane_image_hLine
    (show Isometry (fun z : ℍ => C⁻¹ • z) from isometry_smul ℍ C⁻¹) L
  have hηN : range η ⊆ N.carrier := by
    rintro _ ⟨t, rfl⟩
    rw [← hN]
    exact ⟨f t, hL.symm ▸ hfS (mem_range_self t), rfl⟩
  exact whole_period_length_of_equivariant_line_lift q A
    (projection_ne_one_of_hyperbolic_trace A ht) ht η hηproj N.carrier N.isHLine hηN hperiod

/-- The general source trace formula for the GIVEN actual hyperbolic matrix
covering the full original geodesic loop. Compactness is not required. -/
theorem OriginalClosedGeodesic.trace_sq_eq_four_cosh_length_sq_of_covers
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hAΓ : A ∈ Γ)
    (ht : 4 < (Matrix.trace A.val) ^ 2)
    (hcov : LiZhongQC.Covers M.halfPlaneCover A q.toLoop) :
    (Matrix.trace A.val) ^ 2 = 4 * Real.cosh (q.length.toReal / 2) ^ 2 := by
  have hA := projection_ne_one_of_hyperbolic_trace A ht
  have hlength := q.length_eq_translationLength_of_covers hp A hAΓ ht hcov
  have hT := hHyperbolic_translationLength_pos A hA ht
  rw [hlength, ENNReal.toReal_ofReal hT.le]
  have htrace := hHyperbolic_translation_trace A hA ht
  linarith

/-- The full original period supplies an actual equivariant lift covering its
matrix's entire axis, in the same original projection and covering group. -/
theorem OriginalClosedGeodesic.exists_actual_hyperbolic_axis_lift
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover) :
    ∃ (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : realSLMobius A ≠ 1)
      (ht : 4 < (Matrix.trace A.val) ^ 2), A ∈ Γ ∧
      LiZhongQC.Covers M.halfPlaneCover A q.toLoop ∧
      ∃ f : C(ℝ, ℍ), (∀ t : ℝ, M.halfPlaneCover (f t) = q.curve t) ∧
        (∀ t : ℝ, f (t + 1) = A • f t) ∧
        range f = (hHyperbolicAxis A hA ht).carrier := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨f, S, hproj, hS, hfS⟩ := q.locallyMinimizing.exists_hLine_lift
  have hfinj := locallyInjective_actual_curve_lift q f hproj
  obtain ⟨L, hL⟩ := exists_halfPlaneLine_of_isHLine hS
  obtain ⟨δ, hδ, hδrange⟩ := L.exists_isometric_param
  obtain ⟨κ, _hκcont, hκmono, hκpoint⟩ := coordinate_on_isometric_line
    f.continuous hfinj hδ (by rw [hδrange, hL]; exact hfS)
  have hglobalinj : Function.Injective (f : ℝ → ℍ) := by
    intro s t he
    have heκ := hδ.injective ((hκpoint s).trans (he.trans (hκpoint t).symm))
    exact hκmono.elim (fun hm => hm.injective heκ) (fun hm => hm.injective heκ)
  have h01 : f 0 ≠ f 1 := hglobalinj.ne (by norm_num)
  have hclosed : M.halfPlaneCover (f 0) = M.halfPlaneCover (f 1) := by
    rw [hproj, hproj]
    simpa only [zero_add] using (q.periodic 0).symm
  obtain ⟨A, hAΓ, hAend⟩ := (hp.2.2.2 (f 0) (f 1)).1 hclosed
  have hcov : LiZhongQC.Covers M.halfPlaneCover A q.toLoop := by
    refine ⟨f, f.continuous.continuousOn, ?_, hAend.symm⟩
    intro t ht
    exact (hproj t).trans (Path.extend_apply q.toLoop.2 ht).symm
  have hA1 : A ≠ 1 := by
    intro he
    rw [he, one_smul] at hAend
    exact h01 hAend
  have hAm1 : A ≠ -1 := by
    intro he
    rw [he, LiZhongQC.s27g_neg_one_smul] at hAend
    exact h01 hAend
  have hA : realSLMobius A ≠ 1 := by
    intro he
    have hfix : A • f 0 = f 0 := by
      apply UpperHalfPlane.ext
      apply OnePoint.coe_eq_coe.mp
      rw [← realSLMobius_action, he]
      rfl
    exact h01 (hfix.symm.trans hAend)
  have hperiod : ∀ t : ℝ, f (t + 1) = A • f t := by
    have hwhole : (fun t : ℝ => f (t + 1)) = (fun t => A • f t) := by
      apply hp.1.eq_of_comp_eq
        (f.continuous.comp (continuous_id.add continuous_const))
        ((continuous_const_smul A).comp f.continuous) ?_ 0 ?_
      · funext t
        change M.halfPlaneCover (f (t + 1)) = M.halfPlaneCover (A • f t)
        rw [hproj, LiZhongQC.s30a_p_smul hp hAΓ, hproj, q.periodic t]
      · change f (0 + 1) = A • f 0
        simpa only [zero_add] using hAend.symm
    exact fun t => congrFun hwhole t
  have ht : 4 < (Matrix.trace A.val) ^ 2 := by
    by_contra hnot
    rcases lt_or_eq_of_le (le_of_not_gt hnot) with hsmall | heq
    · have habs : |A 0 0 + A 1 1| < 2 := by
        apply abs_lt_of_sq_lt_sq ?_ (by norm_num)
        simpa only [Matrix.trace_fin_two, show (2 : ℝ) ^ 2 = 4 by norm_num] using hsmall
      obtain ⟨τ, hτ⟩ := LiZhongQC.s27g_elliptic_fixed habs
      rcases LiZhongQC.s27g_actsFreely hp A hAΓ τ hτ with he | he
      exacts [hA1 he, hAm1 he]
    · have hpara := (realSLMobius_parabolic_iff A hA).mpr heq
      apply realSL_parabolic_not_three_on_hLine A hpara (f 0) L
      · rw [hL]
        exact hfS (mem_range_self 0)
      · rw [hAend, hL]
        exact hfS (mem_range_self 1)
      · rw [hAend, ← hperiod 1, hL]
        exact hfS (mem_range_self (1 + 1))
  have haxis := equivariant_arc_supporting_line_eq_axis A hA ht hfinj hS hfS 1 hperiod
  obtain ⟨γ, hγ, hγaxis, hpositive, hγperiod⟩ :=
    exists_unitSpeed_axis_with_actual_period A hA ht
  obtain ⟨κ, hκcont, hκorient, hκpoint⟩ := coordinate_on_isometric_line f.continuous hfinj hγ.1
    (by rw [hγaxis]; exact fun z hz => haxis ▸ hfS hz)
  let T := hTranslationLength (hSLIsometry A)
  have hT : 0 < T := hpositive
  have hκperiod (t : ℝ) : κ (t + 1) = κ t + T := by
    apply hγ.1.injective
    rw [hκpoint, hγperiod, hκpoint, hperiod]
  have hκmono : StrictMono κ := hκorient.resolve_right (by
    intro ha
    have he := ha (show (0 : ℝ) < 1 by norm_num)
    have hstep : κ 1 = κ 0 + T := by simpa only [zero_add] using hκperiod 0
    linarith)
  let periodLift : CircleDeg1Lift :=
    { toOrderHom := ⟨fun t => κ t / T, fun _ _ h =>
        div_le_div_of_nonneg_right (hκmono.monotone h) hT.le⟩
      map_add_one' := fun t => by
        change κ (t + 1) / T = κ t / T + 1
        rw [hκperiod, add_div, div_self hT.ne'] }
  have hσcont : Continuous (periodLift : ℝ → ℝ) := hκcont.div_const T
  have hfull : range f = (hHyperbolicAxis A hA ht).carrier := by
    apply subset_antisymm (haxis ▸ hfS)
    rw [← hγaxis]
    rintro _ ⟨u, rfl⟩
    obtain ⟨t, hσt⟩ := periodLift.continuous_iff_surjective.mp hσcont (u / T)
    have hκt : κ t = u := (div_left_inj' hT.ne').mp hσt
    exact ⟨t, (hκpoint t).symm.trans (congrArg γ hκt)⟩
  exact ⟨A, hA, ht, hAΓ, hcov, f, hproj, hperiod, hfull⟩

/-- The original local arc data supplies a hyperbolic matrix for the entire
period in the same covering group, including on noncompact original surfaces. -/
theorem OriginalClosedGeodesic.exists_actual_hyperbolic_cover
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hp : let := R.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsUniformization Γ M.halfPlaneCover) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, A ∈ Γ ∧
      LiZhongQC.Covers M.halfPlaneCover A q.toLoop ∧ realSLMobius A ≠ 1 ∧
      4 < (Matrix.trace A.val) ^ 2 := by
  obtain ⟨A, hA, ht, hAΓ, hcov, _f, _hproj, _hperiod, _hfull⟩ :=
    q.exists_actual_hyperbolic_axis_lift hp
  exact ⟨A, hAΓ, hcov, hA, ht⟩

/-- The full original period has a finite strictly positive length. -/
theorem OriginalClosedGeodesic.length_toReal_pos
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M) : 0 < q.length.toReal := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, _hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨A, hAΓ, hcov, hA, ht⟩ := q.exists_actual_hyperbolic_cover hp
  have hT := hHyperbolic_translationLength_pos A hA ht
  rw [q.length_eq_translationLength_of_covers hp A hAΓ ht hcov,
    ENNReal.toReal_ofReal hT.le]
  exact hT

/-- On a compact original surface the original geodesic itself supplies an
actual hyperbolic full-period covering matrix. Its full original BV length and
trace then follow from the general noncompact theorem above. -/
theorem OriginalClosedGeodesic.exists_actual_matrix_length_trace
    {X : Type*} [TopologicalSpace X] [CompactSpace X] {R : RiemannSurface X}
    {M : HyperbolicSurfaceModel R} (q : OriginalClosedGeodesic M) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      (∀ z : ℍ, M.halfPlaneCover (A • z) = M.halfPlaneCover z) ∧
      LiZhongQC.Covers M.halfPlaneCover A q.toLoop ∧ realSLMobius A ≠ 1 ∧
      4 < (Matrix.trace A.val) ^ 2 ∧
      q.length = ENNReal.ofReal (hTranslationLength (hSLIsometry A)) ∧
      Real.cosh (q.length.toReal / 2) ^ 2 = (Matrix.trace A.val) ^ 2 / 4 := by
  let := R.toRiemannAtlas.toChartedSpace
  obtain ⟨Γ, _hΓ, hp⟩ := M.exists_halfPlaneCover_uniformization
  obtain ⟨A, hAΓ, hcov, hA, ht⟩ := q.exists_actual_hyperbolic_cover hp
  have hlength := q.length_eq_translationLength_of_covers hp A hAΓ ht hcov
  have hT := hHyperbolic_translationLength_pos A hA ht
  refine ⟨A, (fun z => LiZhongQC.s30a_p_smul hp hAΓ z), hcov, hA, ht, hlength, ?_⟩
  rw [hlength, ENNReal.toReal_ofReal hT.le]
  exact hHyperbolic_translation_trace A hA ht

end LowDimensionalTopology.Geometry.Surfaces
