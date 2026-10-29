module

public import LowDimensionalTopology.Geometry.Quasiconformal.WeakWirtingerGreen
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.Pompeiu

/-!
# Smooth cutoffs of genuine weak data across one puncture

A smooth multiplier that vanishes near the puncture transports the actual
distributional identities to the whole original open set. The Green consumer
uses the original continuous trace of the punctured function on the circle.
No Green identity, derivative bound, or arbitrary boundary trace is assumed.

Uses the credited LiZhongQC Wirtinger product rules and support lemmas;
see THIRD_PARTY_NOTICES.md.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set MeasureTheory Filter Topology Metric
open scoped ContDiff
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem locallyIntegrableOn_of_zero_near_puncture
    {U : Set ℂ} {f : ℂ → ℂ} (hU : IsOpen U)
    (hf : LocallyIntegrableOn f (U \ {0})) {ε : ℝ} (hε : 0 < ε)
    (hzero : ∀ z ∈ ball (0 : ℂ) ε, f z = 0) : LocallyIntegrableOn f U := by
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    refine ⟨ball (0 : ℂ) ε,
      mem_nhdsWithin_of_mem_nhds (ball_mem_nhds 0 hε), ?_⟩
    exact (integrableOn_congr_fun hzero measurableSet_ball).mpr integrableOn_zero
  · have hzV : z ∈ U \ {0} := ⟨hz, by simpa only [mem_singleton_iff] using hz0⟩
    have hi := hf z hzV
    rw [nhdsWithin_eq_nhds.mpr ((hU.sdiff isClosed_singleton).mem_nhds hzV)] at hi
    rw [nhdsWithin_eq_nhds.mpr (hU.mem_nhds hz)]
    exact hi

private theorem test_mul_locallyIntegrableOn
    {U : Set ℂ} {f ψ : ℂ → ℂ} (hf : LocallyIntegrableOn f U)
    (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) (hsψ : tsupport ψ ⊆ U) :
    IntegrableOn (fun z => ψ z * f z) U := by
  refine (sp_ibp_integrable_of_support hcψ.isCompact.measurableSet ?_ ?_).integrableOn
  · exact (hf.integrableOn_compact_subset hsψ hcψ.isCompact).continuousOn_mul
      hψ.continuousOn hcψ.isCompact
  · intro z hz
    rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

private theorem cutoff_test_derivatives {ψ : ℂ → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hcψ : HasCompactSupport ψ) :
    Continuous (dz ψ) ∧ Continuous (dzbar ψ) ∧
      HasCompactSupport (dz ψ) ∧ HasCompactSupport (dzbar ψ) ∧
      tsupport (dz ψ) ⊆ tsupport ψ ∧ tsupport (dzbar ψ) ⊆ tsupport ψ := by
  have hz : ∀ z ∉ tsupport ψ, dz ψ z = 0 ∧ dzbar ψ z = 0 := by
    intro z hz
    constructor
    · simp only [dz, sp_fderiv_eq_zero_of_notMem_tsupport hz 1,
        sp_fderiv_eq_zero_of_notMem_tsupport hz I, mul_zero, sub_zero, zero_div]
    · simp only [dzbar, sp_fderiv_eq_zero_of_notMem_tsupport hz 1,
        sp_fderiv_eq_zero_of_notMem_tsupport hz I, mul_zero, add_zero, zero_div]
  have hs : tsupport (dz ψ) ⊆ tsupport ψ ∧ tsupport (dzbar ψ) ⊆ tsupport ψ := by
    constructor
    · exact closure_minimal (fun z h => by
        by_contra hn
        exact h ((hz z hn).1)) (isClosed_tsupport ψ)
    · exact closure_minimal (fun z h => by
        by_contra hn
        exact h ((hz z hn).2)) (isClosed_tsupport ψ)
  exact ⟨continuous_dz hψ, continuous_dzbar hψ,
    IsCompact.of_isClosed_subset hcψ.isCompact (isClosed_tsupport _) hs.1,
    IsCompact.of_isClosed_subset hcψ.isCompact (isClosed_tsupport _) hs.2, hs.1, hs.2⟩

private theorem cutoff_pairing
    {U : Set ℂ} {f g χ ψ dχ dψ dη : ℂ → ℂ}
    (hU : MeasurableSet U)
    (hD : ∀ z, dη z = ψ z * dχ z + χ z * dψ z)
    (hA : IntegrableOn (fun z => dψ z * (χ z * f z)) U)
    (hB : IntegrableOn (fun z => ψ z * (dχ z * f z)) U)
    (hC : IntegrableOn (fun z => ψ z * (χ z * g z)) U)
    (he : (∫ z in U, f z * dη z) = -∫ z in U, (ψ z * χ z) * g z) :
    (∫ z in U, (χ z * f z) * dψ z) =
      -∫ z in U, ψ z * (χ z * g z + dχ z * f z) := by
  have hA' : IntegrableOn (fun z => (χ z * f z) * dψ z) U := by
    simpa only [mul_comm] using hA
  have he' :
      (∫ z in U, ψ z * (dχ z * f z)) + (∫ z in U, (χ z * f z) * dψ z) =
        -(∫ z in U, ψ z * (χ z * g z)) := by
    calc
      _ = ∫ z in U, ψ z * (dχ z * f z) + (χ z * f z) * dψ z :=
        (integral_add hB hA').symm
      _ = ∫ z in U, f z * dη z := setIntegral_congr_fun hU (fun z _ => by rw [hD]; ring)
      _ = _ := he.trans (congrArg Neg.neg (setIntegral_congr_fun hU (fun z _ => by ring)))
  rw [show (fun z => ψ z * (χ z * g z + dχ z * f z)) =
    (fun z => ψ z * (χ z * g z) + ψ z * (dχ z * f z)) by funext z; ring,
    integral_add hC hB]
  linear_combination he'

/-- A genuine smooth multiplier vanishing on a neighborhood of the puncture
gives the ordinary weak product rule on the entire original open set. -/
theorem HasDistributionalWirtingerDerivatives.cutoff_puncture
    {U : Set ℂ} {f g h χ : ℂ → ℂ} (hU : IsOpen U)
    (hw : HasDistributionalWirtingerDerivatives f g h (U \ {0}))
    (hχ : ContDiff ℝ ∞ χ) {ε : ℝ} (hε : 0 < ε)
    (hχ0 : ∀ z ∈ ball (0 : ℂ) ε, χ z = 0) :
    HasDistributionalWirtingerDerivatives (fun z => χ z * f z)
      (fun z => χ z * g z + dz χ z * f z)
      (fun z => χ z * h z + dzbar χ z * f z) U := by
  have hV : IsOpen (U \ {(0 : ℂ)}) := hU.sdiff isClosed_singleton
  have hχ1 : ContDiff ℝ 1 χ := hχ.of_le (by simp)
  have hd0 : ∀ z ∈ ball (0 : ℂ) ε, dz χ z = 0 ∧ dzbar χ z = 0 := by
    intro z hz
    have hev : χ =ᶠ[𝓝 z] 0 := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw using hχ0 w hw
    have hn : z ∉ tsupport χ := notMem_tsupport_iff_eventuallyEq.mpr hev
    constructor
    · simp only [dz, sp_fderiv_eq_zero_of_notMem_tsupport hn 1,
        sp_fderiv_eq_zero_of_notMem_tsupport hn I, mul_zero, sub_zero, zero_div]
    · simp only [dzbar, sp_fderiv_eq_zero_of_notMem_tsupport hn 1,
        sp_fderiv_eq_zero_of_notMem_tsupport hn I, mul_zero, add_zero, zero_div]
  have hcf : LocallyIntegrableOn (fun z => χ z * f z) U :=
    locallyIntegrableOn_of_zero_near_puncture hU
      (hw.1.continuousOn_mul hχ.continuous.continuousOn hV.isLocallyClosed) hε
      (fun z hz => by rw [hχ0 z hz, zero_mul])
  have hcg : LocallyIntegrableOn (fun z => χ z * g z) U :=
    locallyIntegrableOn_of_zero_near_puncture hU
      (hw.2.1.continuousOn_mul hχ.continuous.continuousOn hV.isLocallyClosed) hε
      (fun z hz => by rw [hχ0 z hz, zero_mul])
  have hch : LocallyIntegrableOn (fun z => χ z * h z) U :=
    locallyIntegrableOn_of_zero_near_puncture hU
      (hw.2.2.1.continuousOn_mul hχ.continuous.continuousOn hV.isLocallyClosed) hε
      (fun z hz => by rw [hχ0 z hz, zero_mul])
  have hdf : LocallyIntegrableOn (fun z => dz χ z * f z) U :=
    locallyIntegrableOn_of_zero_near_puncture hU
      (hw.1.continuousOn_mul (continuous_dz hχ1).continuousOn hV.isLocallyClosed) hε
      (fun z hz => by rw [(hd0 z hz).1, zero_mul])
  have hbf : LocallyIntegrableOn (fun z => dzbar χ z * f z) U :=
    locallyIntegrableOn_of_zero_near_puncture hU
      (hw.1.continuousOn_mul (continuous_dzbar hχ1).continuousOn hV.isLocallyClosed) hε
      (fun z hz => by rw [(hd0 z hz).2, zero_mul])
  refine ⟨hcf, hcg.add hdf, hch.add hbf, ?_⟩
  intro ψ hψ hcψ hsψ
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  obtain ⟨hdz, hbar, hcdz, hcbar, hsdz, hsbar⟩ := cutoff_test_derivatives hψ1 hcψ
  have hnot : (0 : ℂ) ∉ tsupport χ := by
    apply notMem_tsupport_iff_eventuallyEq.mpr
    filter_upwards [ball_mem_nhds 0 hε] with z hz using hχ0 z hz
  have hs : tsupport (fun z => ψ z * χ z) ⊆ U \ {(0 : ℂ)} := by
    intro z hz
    refine ⟨hsψ (tsupport_mul_subset_left hz), ?_⟩
    intro hz0
    have : z = 0 := mem_singleton_iff.mp hz0
    exact hnot (this ▸ tsupport_mul_subset_right hz)
  have ht := hw.2.2.2 (fun z => ψ z * χ z) (hψ.mul hχ) (hcψ.mul_right (f' := χ)) hs
  have hset : U \ {(0 : ℂ)} =ᵐ[volume] U := sdiff_null_ae_eq_self (measure_singleton 0)
  have htz : (∫ z in U, f z * dz (fun w => ψ w * χ w) z) =
      -∫ z in U, (ψ z * χ z) * g z := by
    calc
      _ = ∫ z in U \ {0}, f z * dz (fun w => ψ w * χ w) z :=
        (setIntegral_congr_set hset).symm
      _ = _ := ht.1
      _ = _ := congrArg Neg.neg (setIntegral_congr_set hset)
  have htb : (∫ z in U, f z * dzbar (fun w => ψ w * χ w) z) =
      -∫ z in U, (ψ z * χ z) * h z := by
    calc
      _ = ∫ z in U \ {0}, f z * dzbar (fun w => ψ w * χ w) z :=
        (setIntegral_congr_set hset).symm
      _ = _ := ht.2
      _ = _ := congrArg Neg.neg (setIntegral_congr_set hset)
  exact ⟨cutoff_pairing hU.measurableSet
      (fun z => dz_mul (hψ1.differentiable one_ne_zero z) (hχ1.differentiable one_ne_zero z))
      (test_mul_locallyIntegrableOn hcf hdz hcdz (hsdz.trans hsψ))
      (test_mul_locallyIntegrableOn hdf hψ.continuous hcψ hsψ)
      (test_mul_locallyIntegrableOn hcg hψ.continuous hcψ hsψ) htz,
    cutoff_pairing hU.measurableSet
      (fun z => dzbar_mul (hψ1.differentiable one_ne_zero z) (hχ1.differentiable one_ne_zero z))
      (test_mul_locallyIntegrableOn hcf hbar hcbar (hsbar.trans hsψ))
      (test_mul_locallyIntegrableOn hbf hψ.continuous hcψ hsψ)
      (test_mul_locallyIntegrableOn hch hψ.continuous hcψ hsψ) htb⟩

/-- The actual cutoff function has a continuous trace across the puncture. -/
theorem continuousOn_puncture_cutoff {U : Set ℂ} {f χ : ℂ → ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f (U \ {0})) (hχ : Continuous χ)
    {ε : ℝ} (hε : 0 < ε) (hχ0 : ∀ z ∈ ball (0 : ℂ) ε, χ z = 0) :
    ContinuousOn (fun z => χ z * f z) U := by
  apply hU.continuousOn_iff.mpr
  intro z hz
  by_cases hz0 : z = 0
  · subst z
    apply continuousAt_const.congr
    filter_upwards [ball_mem_nhds 0 hε] with w hw
    exact (by rw [hχ0 w hw, zero_mul] : χ w * f w = 0).symm
  · have hzV : z ∈ U \ {0} := ⟨hz, by simpa only [mem_singleton_iff] using hz0⟩
    exact hχ.continuousAt.mul
      (((hU.sdiff isClosed_singleton).continuousOn_iff.mp hf) hzV)

/-- Green's formula holds for the actual smooth cutoff of punctured weak
data, with the true continuous boundary values and both product-rule terms. -/
theorem green_of_distributional_wirtinger_puncture_cutoff
    {U : Set ℂ} {f g h χ : ℂ → ℂ} (hU : IsOpen U)
    (hf : ContinuousOn f (U \ {0}))
    (hw : HasDistributionalWirtingerDerivatives f g h (U \ {0}))
    (hχ : ContDiff ℝ ∞ χ) {ε : ℝ} (hε : 0 < ε)
    (hχ0 : ∀ z ∈ ball (0 : ℂ) ε, χ z = 0)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hsub : closedBall c R ⊆ U) :
    CircleIntegrable (fun z => χ z * f z) c R ∧
      (∮ z in C(c, R), χ z * f z) =
        2 * I * ∫ z in ball c R, χ z * h z + dzbar χ z * f z :=
  green_of_distributional_wirtinger hU
    (continuousOn_puncture_cutoff hU hf hχ.continuous hε hχ0)
    (HasDistributionalWirtingerDerivatives.cutoff_puncture hU hw hχ hε hχ0) hR hsub

/-- Multiplication by an actually smooth function on the original open
domain preserves genuine weak derivatives, with the literal product rule.
The multiplier is not required to be smooth outside that domain. -/
theorem HasDistributionalWirtingerDerivatives.mul_contDiffOn
    {U : Set ℂ} {f g h χ : ℂ → ℂ} (hU : IsOpen U)
    (hw : HasDistributionalWirtingerDerivatives f g h U)
    (hχ : ContDiffOn ℝ ∞ χ U) :
    HasDistributionalWirtingerDerivatives (fun z => χ z * f z)
      (fun z => χ z * g z + dz χ z * f z)
      (fun z => χ z * h z + dzbar χ z * f z) U := by
  have hχ1 : ContDiffOn ℝ 1 χ U := hχ.of_le (by simp)
  obtain ⟨hdχ, hbχ⟩ := continuousOn_dz_dzbar hχ1 hU
  have hcf := hw.1.continuousOn_mul hχ.continuousOn hU.isLocallyClosed
  have hcg := hw.2.1.continuousOn_mul hχ.continuousOn hU.isLocallyClosed
  have hch := hw.2.2.1.continuousOn_mul hχ.continuousOn hU.isLocallyClosed
  have hdf := hw.1.continuousOn_mul hdχ hU.isLocallyClosed
  have hbf := hw.1.continuousOn_mul hbχ hU.isLocallyClosed
  refine ⟨hcf, hcg.add hdf, hch.add hbf, ?_⟩
  intro ψ hψ hcψ hsψ
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  obtain ⟨hdz, hbar, hcdz, hcbar, hsdz, hsbar⟩ := cutoff_test_derivatives hψ1 hcψ
  have hη : ContDiff ℝ ∞ (fun z => ψ z * χ z) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ U
    · exact hψ.contDiffAt.mul (hχ.contDiffAt (hU.mem_nhds hz))
    · have hn : z ∉ tsupport ψ := fun hzψ => hz (hsψ hzψ)
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with w hw
      simpa only [Pi.zero_apply, zero_mul] using congrArg (fun v : ℂ => v * χ w) hw
  have ht := hw.2.2.2 (fun z => ψ z * χ z) hη (hcψ.mul_right (f' := χ))
    (tsupport_mul_subset_left.trans hsψ)
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ χ z := fun z hz =>
    (hχ1.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero
  have htz : (∫ z in U, f z * (ψ z * dz χ z + χ z * dz ψ z)) =
      -∫ z in U, (ψ z * χ z) * g z := by
    calc
      _ = ∫ z in U, f z * dz (fun w => ψ w * χ w) z :=
        setIntegral_congr_fun hU.measurableSet (fun z hz => by
          rw [dz_mul (hψ1.differentiable one_ne_zero z) (hdiff z hz)])
      _ = _ := ht.1
  have htb : (∫ z in U, f z * (ψ z * dzbar χ z + χ z * dzbar ψ z)) =
      -∫ z in U, (ψ z * χ z) * h z := by
    calc
      _ = ∫ z in U, f z * dzbar (fun w => ψ w * χ w) z :=
        setIntegral_congr_fun hU.measurableSet (fun z hz => by
          rw [dzbar_mul (hψ1.differentiable one_ne_zero z) (hdiff z hz)])
      _ = _ := ht.2
  exact ⟨cutoff_pairing hU.measurableSet (fun _ => rfl)
      (test_mul_locallyIntegrableOn hcf hdz hcdz (hsdz.trans hsψ))
      (test_mul_locallyIntegrableOn hdf hψ.continuous hcψ hsψ)
      (test_mul_locallyIntegrableOn hcg hψ.continuous hcψ hsψ) htz,
    cutoff_pairing hU.measurableSet (fun _ => rfl)
      (test_mul_locallyIntegrableOn hcf hbar hcbar (hsbar.trans hsψ))
      (test_mul_locallyIntegrableOn hbf hψ.continuous hcψ hsψ)
      (test_mul_locallyIntegrableOn hch hψ.continuous hcψ hsψ) htb⟩

end LowDimensionalTopology.Geometry.Quasiconformal
