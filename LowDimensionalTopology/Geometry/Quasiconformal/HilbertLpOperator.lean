/-
The singular-integral extension and approximation lemmas are due to Wu Xiaobin,
Li-Zhong-QC-formalization commit 1c0d5473c020b66ed5106331a38a61536760b9b2.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.External.LiZhongQC.Ch02.S11b_HilbertNorm
public import Mathlib.Analysis.Normed.Operator.Basic

/-!
# The Hilbert transform as a complex continuous linear operator on Lp

The actual smooth-approximation extension is complex linear on every finite
Lp with p>1. Its induced map on almost-everywhere classes has operator norm
equal to the existing supremum of norm ratios.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology Complex
open scoped ENNReal ContDiff
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

/-- Additivity of the actual Hilbert extension for every finite p>1. -/
theorem hilbertH_add_ae_of_memLp {p : ℝ} (hp : 1 < p) {u v : ℂ → ℂ}
    (hu : MemLp u (ENNReal.ofReal p) (volume : Measure ℂ))
    (hv : MemLp v (ENNReal.ofReal p) (volume : Measure ℂ)) :
    hilbertH (fun z => u z + v z) =ᵐ[volume] fun z => hilbertH u z + hilbertH v z := by
  obtain ⟨A, -, hbound⟩ := zygmund_calderon hp
  have huv : MemLp (fun z => u z + v z) (ENNReal.ofReal p) (volume : Measure ℂ) :=
    MemLp.ae_eq (f := u + v) (g := fun z => u z + v z)
      (Eventually.of_forall fun z => Pi.add_apply u v z) (hu.add hv)
  have hsub := hilbertH_sub_ae_of_smooth_bound hp hbound huv hv
  have hcancel : (fun z => (u z + v z) - v z) = u := by
    funext z
    exact add_sub_cancel_right (u z) (v z)
  rw [hcancel] at hsub
  filter_upwards [hsub] with z hz
  have hz' := congrArg (fun t : ℂ => t + hilbertH v z) hz
  simpa only [sub_add_cancel] using hz'.symm

/-- Complex scalar linearity of the same extension, without an L2 premise. -/
theorem hilbertH_smul_ae_of_memLp {p : ℝ} (hp : 1 < p) {u : ℂ → ℂ} (c : ℂ)
    (hu : MemLp u (ENNReal.ofReal p) (volume : Measure ℂ)) :
    hilbertH (fun z => c * u z) =ᵐ[volume] fun z => c * hilbertH u z := by
  obtain ⟨A, -, hbound⟩ := zygmund_calderon hp
  have hcu := hu.const_mul c
  obtain ⟨hmem, -, hconv⟩ := hilbertH_tendsto_of_smooth_bound hp hbound u hu
  obtain ⟨hmemc, -, hconvc⟩ :=
    hilbertH_tendsto_of_smooth_bound hp hbound (fun z => c * u z) hcu
  have heqn (n : ℕ) : hilbertHSmooth (hilbertHApprox (fun w => c * u w) n) =
      fun z => c * hilbertHSmooth (hilbertHApprox u n) z := by
    rw [hilbertHApprox_smul c hp.le hu n]
    exact hilbertHSmooth_smul c (hilbertHApprox_contDiff hp.le hu n)
      (hilbertHApprox_hasCompactSupport u n)
  have heq (n : ℕ) :
      (fun z => hilbertHSmooth (hilbertHApprox (fun w => c * u w) n) z -
        c * hilbertH u z) =
      fun z => c * (hilbertHSmooth (hilbertHApprox u n) z - hilbertH u z) := by
    funext z
    rw [congrFun (heqn n) z, mul_sub]
  have hnormeq (n : ℕ) :
      eLpNorm (fun z => c * (hilbertHSmooth (hilbertHApprox u n) z - hilbertH u z))
        (ENNReal.ofReal p) (volume : Measure ℂ) =
      ENNReal.ofReal ‖c‖ *
        eLpNorm (fun z => hilbertHSmooth (hilbertHApprox u n) z - hilbertH u z)
          (ENNReal.ofReal p) (volume : Measure ℂ) := by
    rw [show (fun z => c * (hilbertHSmooth (hilbertHApprox u n) z - hilbertH u z)) =
      c • (fun z => hilbertHSmooth (hilbertHApprox u n) z - hilbertH u z) from rfl,
      eLpNorm_const_smul]
    congr 1
    rw [← ofReal_norm]
  have hscaledconv : Tendsto
      (fun n => eLpNorm (fun z => hilbertHSmooth (hilbertHApprox (fun w => c * u w) n) z -
        c * hilbertH u z) (ENNReal.ofReal p) (volume : Measure ℂ)) atTop (𝓝 0) := by
    simp_rw [heq, hnormeq]
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ‖c‖) hconv
        (Or.inr ENNReal.ofReal_ne_top))
  exact hilbertH_indep_of_p hp hp hcu hmemc hconvc
    (hmem.const_mul c) hscaledconv

section Lp

variable {p : ℝ} [Fact (1 ≤ ENNReal.ofReal p)]

private def hilbertLpValue (hp : 1 < p)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) :=
  (hilbertH_memLp hp (Lp.memLp f)).toLp (hilbertH (f : ℂ → ℂ))

omit [Fact (1 ≤ ENNReal.ofReal p)] in
private theorem hilbertLpValue_coeFn (hp : 1 < p)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) :
    (hilbertLpValue hp f : ℂ → ℂ) =ᵐ[volume] hilbertH (f : ℂ → ℂ) :=
  MemLp.coeFn_toLp (hilbertH_memLp hp (Lp.memLp f))

private def hilbertLpLinearMap (hp : 1 < p) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) →ₗ[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) where
  toFun := hilbertLpValue hp
  map_add' f g := by
    apply Lp.ext
    have hin : (fun z => (f + g) z) =ᵐ[volume] fun z => f z + g z := by
      filter_upwards [Lp.coeFn_add f g] with z hz
      exact hz
    have hH := hilbertH_congr_ae hin
    have hadd := hilbertH_add_ae_of_memLp hp (Lp.memLp f) (Lp.memLp g)
    filter_upwards [hilbertLpValue_coeFn hp (f + g), hilbertLpValue_coeFn hp f,
      hilbertLpValue_coeFn hp g, hadd,
      Lp.coeFn_add (hilbertLpValue hp f) (hilbertLpValue hp g)] with z hfg hf hg hz hout
    calc hilbertLpValue hp (f + g) z =
        hilbertH ((f + g : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) : ℂ → ℂ) z := hfg
      _ = hilbertH (fun w => f w + g w) z := congrFun hH z
      _ = hilbertH f z + hilbertH g z := hz
      _ = hilbertLpValue hp f z + hilbertLpValue hp g z := by rw [hf, hg]
      _ = ((hilbertLpValue hp f + hilbertLpValue hp g :
          Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) : ℂ → ℂ) z := hout.symm
  map_smul' c f := by
    apply Lp.ext
    have hin : (fun z => (c • f) z) =ᵐ[volume] fun z => c * f z := by
      filter_upwards [Lp.coeFn_smul c f] with z hz
      simpa only [Pi.smul_apply, smul_eq_mul] using hz
    have hH := hilbertH_congr_ae hin
    have hsmul := hilbertH_smul_ae_of_memLp hp c (Lp.memLp f)
    filter_upwards [hilbertLpValue_coeFn hp (c • f), hilbertLpValue_coeFn hp f,
      hsmul, Lp.coeFn_smul c (hilbertLpValue hp f)] with z hcf hf hz hout
    calc hilbertLpValue hp (c • f) z =
        hilbertH ((c • f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) : ℂ → ℂ) z := hcf
      _ = hilbertH (fun w => c * f w) z := congrFun hH z
      _ = c * hilbertH f z := hz
      _ = c * hilbertLpValue hp f z := by rw [hf]
      _ = ((c • hilbertLpValue hp f :
          Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) : ℂ → ℂ) z := by
        simpa only [Pi.smul_apply, smul_eq_mul] using hout.symm

omit [Fact (1 ≤ ENNReal.ofReal p)] in
private theorem hilbertLpLinearMap_bound (hp : 1 < p)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) :
    ‖hilbertLpLinearMap hp f‖ ≤ hilbertNorm p * ‖f‖ := by
  change ‖(hilbertH_memLp hp (Lp.memLp f)).toLp (hilbertH (f : ℂ → ℂ))‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def]
  exact eq11_16 hp (Lp.memLp f)

/-- The actual Hilbert transform on almost-everywhere classes is a complex
continuous linear map. The structural Fact instance follows from p>1. -/
@[no_expose] def hilbertLp (hp : 1 < p) :
    Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) →L[ℂ]
      Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) :=
  (hilbertLpLinearMap hp).mkContinuous (hilbertNorm p) (hilbertLpLinearMap_bound hp)

/-- The continuous linear map acts by the existing actual Hilbert extension. -/
theorem hilbertLp_coeFn (hp : 1 < p)
    (f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ)) :
    (hilbertLp hp f : ℂ → ℂ) =ᵐ[volume] hilbertH (f : ℂ → ℂ) :=
  hilbertLpValue_coeFn hp f

/-- The operator norm is literally the existing supremum of norm ratios. -/
theorem norm_hilbertLp (hp : 1 < p) : ‖hilbertLp hp‖ = hilbertNorm p := by
  apply le_antisymm
  · exact LinearMap.mkContinuous_norm_le (hilbertLpLinearMap hp)
      (hilbertNorm_nonneg p) (hilbertLpLinearMap_bound hp)
  · rw [hilbertNorm]
    apply csSup_le
    · obtain ⟨hw, hne⟩ := unitDiscIndicator_eLpNorm_ne_zero (lt_trans one_pos hp)
      exact ⟨_, _, hw, hne, rfl⟩
    · rintro a ⟨u, hu, hne, rfl⟩
      let f : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) := hu.toLp u
      have hin : (f : ℂ → ℂ) =ᵐ[volume] u := MemLp.coeFn_toLp hu
      have hout : (hilbertLp hp f : ℂ → ℂ) =ᵐ[volume] hilbertH u := by
        rw [← hilbertH_congr_ae hin]
        exact hilbertLp_coeFn hp f
      have hn : ‖hilbertLp hp f‖ =
          (eLpNorm (hilbertH u) (ENNReal.ofReal p) (volume : Measure ℂ)).toReal := by
        rw [Lp.norm_def, eLpNorm_congr_ae hout]
      have hb := (hilbertLp hp).le_opNorm f
      rw [hn] at hb
      have hfn : ‖f‖ = (eLpNorm u (ENNReal.ofReal p) (volume : Measure ℂ)).toReal :=
        Lp.norm_toLp u hu
      rw [hfn] at hb
      exact (div_le_iff₀ (ENNReal.toReal_pos hne hu.eLpNorm_ne_top)).2 hb

end Lp

/-- Every finite p>1 admits the genuine complex continuous linear extension,
with its exact operator norm. No structural instance is an extra hypothesis. -/
theorem exists_hilbertLp {p : ℝ} (hp : 1 < p) :
    let : Fact (1 ≤ ENNReal.ofReal p) :=
      ⟨by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le⟩
    ∃ T : Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ) →L[ℂ]
        Lp ℂ (ENNReal.ofReal p) (volume : Measure ℂ),
      (∀ f, (T f : ℂ → ℂ) =ᵐ[volume] hilbertH (f : ℂ → ℂ)) ∧
        ‖T‖ = hilbertNorm p := by
  let : Fact (1 ≤ ENNReal.ofReal p) :=
    ⟨by rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hp.le⟩
  exact ⟨hilbertLp hp, hilbertLp_coeFn hp, norm_hilbertLp hp⟩

/-- The norm of this same operator is continuous for p>1. -/
theorem hilbert_operatorNorm_continuousOn : ContinuousOn hilbertNorm (Ioi 1) :=
  LiZhongQC.hilbertNorm_continuousOn

/-- The norms of this same operator tend to one as p tends to two. -/
theorem hilbert_operatorNorm_tendsto_two : Tendsto hilbertNorm (𝓝 2) (𝓝 1) :=
  LiZhongQC.thm11_3_cor2

end LowDimensionalTopology.Geometry.Quasiconformal
