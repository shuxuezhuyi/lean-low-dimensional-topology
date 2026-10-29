/-
The rational-rectangle assembly uses Wu Xiaobin's Li-Zhong-QC-formalization,
commit 1c0d5473c020b66ed5106331a38a61536760b9b2, with retained attribution.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Quasiconformal.DistributionalMollifier
public import LowDimensionalTopology.Geometry.Quasiconformal.QuasiconformalWeakDerivatives
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.Tactic.Ring

/-!
# Real and Wirtinger weak derivatives and smooth compact approximation

The real-coordinate and Wirtinger distributional identities are related by
explicit linear combinations of actual compact smooth tests. Local L1 is
sufficient. No absolute-continuity or approximation hypothesis is imposed.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Topology Complex
open scoped ContDiff ENNReal
open LiZhongQC

namespace LowDimensionalTopology.Geometry.Quasiconformal

private theorem compact_factor_mul_integrable {g b : ℂ → ℂ} {U S : Set ℂ}
    (hg : LocallyIntegrableOn g U) (hb : Continuous b) (hS : IsCompact S)
    (hSU : S ⊆ U) (hb0 : ∀ z ∉ S, b z = 0) :
    IntegrableOn (fun z => b z * g z) U :=
  (sp_ibp_integrable_of_support hS.measurableSet
    (IntegrableOn.continuousOn_mul hb.continuousOn
      (hg.integrableOn_compact_subset hSU hS) hS)
    (fun z hz => by rw [hb0 z hz, zero_mul])).integrableOn

private theorem setIntegral_mul_linear_combination {u g h : ℂ → ℂ} {U : Set ℂ}
    (hg : IntegrableOn (fun z => u z * g z) U)
    (hh : IntegrableOn (fun z => u z * h z) U) (a b : ℂ) :
    (∫ z in U, u z * (a * g z + b * h z)) =
      a * (∫ z in U, u z * g z) + b * ∫ z in U, u z * h z := by
  have heq : (fun z => u z * (a * g z + b * h z)) =
      fun z => a * (u z * g z) + b * (u z * h z) := by funext z; ring
  rw [heq, integral_add (hg.const_mul a) (hh.const_mul b),
    integral_const_mul, integral_const_mul]

/-- Genuine distributional Wirtinger derivatives give the genuine weak
coordinate derivatives `fx=fz+fzb` and `fy=I*(fz-fzb)`, already at local L1. -/
theorem HasDistributionalWirtingerDerivatives.real_partials
    {f g h : ℂ → ℂ} {U : Set ℂ} (hw : HasDistributionalWirtingerDerivatives f g h U) :
    HasDistributionalPartials f (fun z => g z + h z) (fun z => I * (g z - h z)) U := by
  have hx : LocallyIntegrableOn (fun z => g z + h z) U :=
    LocallyIntegrableOn.congr
      (Eventually.of_forall fun z => by simp only [Pi.add_apply]) (hw.2.1.add hw.2.2.1)
  have hy : LocallyIntegrableOn (fun z => I * (g z - h z)) U :=
    LocallyIntegrableOn.congr
      (Eventually.of_forall fun z => by simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply])
      ((hw.2.1.sub hw.2.2.1).smul I)
  have htest (ψ : ℂ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
      (hsψ : tsupport ψ ⊆ U) (a b : ℂ) :
      (∫ z in U, (a * dz ψ z + b * dzbar ψ z) * f z) =
        -∫ z in U, ψ z * (a * g z + b * h z) := by
    have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
    have hdir (v : ℂ) : Continuous (fun z => fderiv ℝ ψ z v) :=
      (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hd : Continuous (dz ψ) := by
      unfold dz
      exact ((hdir 1).sub (continuous_const.mul (hdir I))).div_const 2
    have hdb : Continuous (dzbar ψ) := by
      unfold dzbar
      exact ((hdir 1).add (continuous_const.mul (hdir I))).div_const 2
    have hd0 : ∀ z ∉ tsupport ψ, dz ψ z = 0 := by
      intro z hz
      simp only [dz, sp_fderiv_eq_zero_of_notMem_tsupport hz, mul_zero, sub_self,
        zero_div]
    have hdb0 : ∀ z ∉ tsupport ψ, dzbar ψ z = 0 := by
      intro z hz
      simp only [dzbar, sp_fderiv_eq_zero_of_notMem_tsupport hz, mul_zero, add_zero,
        zero_div]
    have hdf : IntegrableOn (fun z => f z * dz ψ z) U := by
      simpa only [mul_comm] using compact_factor_mul_integrable hw.1 hd hcψ.isCompact hsψ hd0
    have hdbf : IntegrableOn (fun z => f z * dzbar ψ z) U := by
      simpa only [mul_comm] using compact_factor_mul_integrable hw.1 hdb hcψ.isCompact hsψ hdb0
    have hgψ := compact_factor_mul_integrable hw.2.1 hψ.continuous hcψ.isCompact hsψ
      (fun z hz => image_eq_zero_of_notMem_tsupport hz)
    have hhψ := compact_factor_mul_integrable hw.2.2.1 hψ.continuous hcψ.isCompact hsψ
      (fun z hz => image_eq_zero_of_notMem_tsupport hz)
    have hL : (∫ z in U, (a * dz ψ z + b * dzbar ψ z) * f z) =
        a * (∫ z in U, f z * dz ψ z) + b * ∫ z in U, f z * dzbar ψ z := by
      simpa only [mul_comm] using setIntegral_mul_linear_combination hdf hdbf a b
    obtain ⟨hz, hzb⟩ := hw.2.2.2 ψ hψ hcψ hsψ
    rw [hL, setIntegral_mul_linear_combination hgψ hhψ, hz, hzb]
    ring
  refine ⟨⟨hw.1, hx, ?_⟩, ⟨hw.1, hy, ?_⟩⟩
  · intro ψ hψ hcψ hsψ
    calc (∫ z in U, fderiv ℝ ψ z 1 * f z)
        = ∫ z in U, (1 * dz ψ z + 1 * dzbar ψ z) * f z := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          simp only [dz, dzbar]
          ring
      _ = -∫ z in U, ψ z * (1 * g z + 1 * h z) := htest ψ hψ hcψ hsψ 1 1
      _ = -∫ z in U, ψ z * (g z + h z) := by simp only [one_mul]
  · intro ψ hψ hcψ hsψ
    calc (∫ z in U, fderiv ℝ ψ z I * f z)
        = ∫ z in U, (I * dz ψ z + -I * dzbar ψ z) * f z := by
          refine integral_congr_ae (Eventually.of_forall fun z => ?_)
          simp only [dz, dzbar]
          ring_nf
          simp only [I_sq]
          ring
      _ = -∫ z in U, ψ z * (I * g z + -I * h z) := htest ψ hψ hcψ hsψ I (-I)
      _ = -∫ z in U, ψ z * (I * (g z - h z)) := by
        apply congrArg Neg.neg
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        ring

/-- Real weak derivatives give both genuine Wirtinger derivatives, with local
integrability retained and every smooth compact test checked. -/
theorem HasDistributionalPartials.wirtinger
    {f fx fy : ℂ → ℂ} {U : Set ℂ} (hw : HasDistributionalPartials f fx fy U) :
    HasDistributionalWirtingerDerivatives f (fun z => (fx z - I * fy z) / 2)
      (fun z => (fx z + I * fy z) / 2) U := by
  have hfy : LocallyIntegrableOn (fun z => I * fy z) U :=
    LocallyIntegrableOn.congr
      (Eventually.of_forall fun z => by simp only [Pi.smul_apply, smul_eq_mul])
      (hw.2.2.1.smul I)
  have hminus : LocallyIntegrableOn (fun z => (fx z - I * fy z) / 2) U :=
    LocallyIntegrableOn.congr (Eventually.of_forall fun z => by
      simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, div_eq_mul_inv]
      ring) ((hw.1.2.1.sub hfy).smul ((2 : ℂ)⁻¹))
  have hplus : LocallyIntegrableOn (fun z => (fx z + I * fy z) / 2) U :=
    LocallyIntegrableOn.congr (Eventually.of_forall fun z => by
      simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, div_eq_mul_inv]
      ring) ((hw.1.2.1.add hfy).smul ((2 : ℂ)⁻¹))
  refine ⟨hw.1.1, hminus, hplus, ?_⟩
  intro ψ hψ hcψ hsψ
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hdir (v : ℂ) : Continuous (fun z => fderiv ℝ ψ z v) :=
    (hψ1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdf (v : ℂ) : IntegrableOn (fun z => f z * fderiv ℝ ψ z v) U := by
    simpa only [mul_comm] using compact_factor_mul_integrable hw.1.1 (hdir v)
      hcψ.isCompact hsψ (fun z hz => sp_fderiv_eq_zero_of_notMem_tsupport hz v)
  have hfxψ := compact_factor_mul_integrable hw.1.2.1 hψ.continuous hcψ.isCompact hsψ
    (fun z hz => image_eq_zero_of_notMem_tsupport hz)
  have hfyψ := compact_factor_mul_integrable hw.2.2.1 hψ.continuous hcψ.isCompact hsψ
    (fun z hz => image_eq_zero_of_notMem_tsupport hz)
  have hx := hw.1.2.2 ψ hψ hcψ hsψ
  have hy := hw.2.2.2 ψ hψ hcψ hsψ
  have htest (a b : ℂ) :
      (∫ z in U, f z * (a * fderiv ℝ ψ z 1 + b * fderiv ℝ ψ z I)) =
        -∫ z in U, ψ z * (a * fx z + b * fy z) := by
    rw [setIntegral_mul_linear_combination (hdf 1) (hdf I),
      setIntegral_mul_linear_combination hfxψ hfyψ]
    have hx' : (∫ z in U, f z * fderiv ℝ ψ z 1) = -∫ z in U, ψ z * fx z := by
      simpa only [mul_comm] using hx
    have hy' : (∫ z in U, f z * fderiv ℝ ψ z I) = -∫ z in U, ψ z * fy z := by
      simpa only [mul_comm] using hy
    rw [hx', hy']
    ring
  have hdz : (fun z => f z * dz ψ z) =
      fun z => f z * ((1 / 2 : ℂ) * fderiv ℝ ψ z 1 + (-I / 2) * fderiv ℝ ψ z I) := by
    funext z
    simp only [dz]
    ring
  have hdzbar : (fun z => f z * dzbar ψ z) =
      fun z => f z * ((1 / 2 : ℂ) * fderiv ℝ ψ z 1 + (I / 2) * fderiv ℝ ψ z I) := by
    funext z
    simp only [dzbar]
    ring
  refine ⟨?_, ?_⟩
  · rw [hdz, htest]
    apply congrArg Neg.neg
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    ring
  · rw [hdzbar, htest]
    apply congrArg Neg.neg
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    ring

/-- Exact real-coordinate representation of the genuine Wirtinger weak predicate.
Only its defining local L1 hypotheses are required. -/
theorem hasDistributionalWirtingerDerivatives_iff_real
    {f g h : ℂ → ℂ} {U : Set ℂ} :
    HasDistributionalWirtingerDerivatives f g h U ↔
      HasDistributionalPartials f (fun z => g z + h z) (fun z => I * (g z - h z)) U := by
  refine ⟨fun hw => hw.real_partials, fun hw => ?_⟩
  have hW := hw.wirtinger
  have hg : (fun z => ((g z + h z) - I * (I * (g z - h z))) / 2) = g := by
    funext z
    ring_nf
    simp only [I_sq]
    ring
  have hh : (fun z => ((g z + h z) + I * (I * (g z - h z))) / 2) = h := by
    funext z
    ring_nf
    simp only [I_sq]
    ring
  rw [hg, hh] at hW
  exact hW

/-- Fixed complex linear combinations preserve convergence to zero in every
Lp seminorm with p≥1, including the essential-supremum endpoint. -/
theorem tendsto_eLpNorm_linear_combination {ι α : Type*} [MeasurableSpace α]
    {μ : Measure α} {l : Filter ι} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {x y : ι → α → ℂ} (a b : ℂ)
    (hx : Tendsto (fun n => eLpNorm (x n) p μ) l (𝓝 0))
    (hy : Tendsto (fun n => eLpNorm (y n) p μ) l (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun z => a * x n z + b * y n z) p μ) l (𝓝 0) := by
  have ha : Tendsto (fun n => ‖a‖ₑ * eLpNorm (x n) p μ) l (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hx (Or.inr (enorm_ne_top : ‖a‖ₑ ≠ ⊤))
  have hb : Tendsto (fun n => ‖b‖ₑ * eLpNorm (y n) p μ) l (𝓝 0) := by
    simpa only [mul_zero] using
      ENNReal.Tendsto.const_mul hy (Or.inr (enorm_ne_top : ‖b‖ₑ ≠ ⊤))
  have hab : Tendsto (fun n => ‖a‖ₑ * eLpNorm (x n) p μ +
      ‖b‖ₑ * eLpNorm (y n) p μ) l (𝓝 0) := by
    simpa only [add_zero] using ha.add hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hab
    (fun _ => bot_le) (fun n => ?_)
  have hmul (c : ℂ) (f : α → ℂ) :
      eLpNorm (fun z => c * f z) p μ ≤ ‖c‖ₑ * eLpNorm f p μ := by
    calc eLpNorm (fun z => c * f z) p μ = eLpNorm (c • f) p μ :=
          eLpNorm_congr_ae (Eventually.of_forall fun z => by
            simp only [Pi.smul_apply, smul_eq_mul])
      _ ≤ ‖c‖ₑ * eLpNorm f p μ := eLpNorm_const_smul_le
  calc eLpNorm (fun z => a * x n z + b * y n z) p μ
      ≤ eLpNorm (fun z => a * x n z) p μ + eLpNorm (fun z => b * y n z) p μ := by
        simpa only [Pi.add_def] using
          (eLpNorm_add_le (μ := μ) (p := p)
            (f := fun z => a * x n z) (g := fun z => b * y n z) hp)
    _ ≤ ‖a‖ₑ * eLpNorm (x n) p μ + ‖b‖ₑ * eLpNorm (y n) p μ :=
      add_le_add (hmul a (x n)) (hmul b (y n))

/-- Exact pointwise identity for the holomorphic derivative error. -/
theorem wirtinger_z_error_eq_linear_combination (a b g h : ℂ) :
    (a - I * b) / 2 - g =
      (1 / 2 : ℂ) * (a - (g + h)) + (-I / 2) * (b - I * (g - h)) := by
  have hII : I * I = -1 := by simpa only [pow_two] using I_sq
  have hg : ((g + h) - I * (I * (g - h))) / 2 = g := by
    rw [← mul_assoc, hII]
    ring
  calc (a - I * b) / 2 - g
      = (a - I * b) / 2 - ((g + h) - I * (I * (g - h))) / 2 := by rw [hg]
    _ = (1 / 2 : ℂ) * (a - (g + h)) + (-I / 2) * (b - I * (g - h)) := by ring

/-- Exact pointwise identity for the antiholomorphic derivative error. -/
theorem wirtinger_dbar_error_eq_linear_combination (a b g h : ℂ) :
    (a + I * b) / 2 - h =
      (1 / 2 : ℂ) * (a - (g + h)) + (I / 2) * (b - I * (g - h)) := by
  have hII : I * I = -1 := by simpa only [pow_two] using I_sq
  have hh : ((g + h) + I * (I * (g - h))) / 2 = h := by
    rw [← mul_assoc, hII]
    ring
  calc (a + I * b) / 2 - h
      = (a + I * b) / 2 - ((g + h) + I * (I * (g - h))) / 2 := by rw [hh]
    _ = (1 / 2 : ℂ) * (a - (g + h)) + (I / 2) * (b - I * (g - h)) := by ring

/-- Convergence of actual real coordinate derivatives gives convergence of both
actual Wirtinger derivatives, with the exact inverse coordinate transformation. -/
theorem tendsto_eLpNorm_wirtinger_sub {ι : Type*} {l : Filter ι}
    {μ : Measure ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    {fn : ι → ℂ → ℂ} {g h : ℂ → ℂ}
    (hx : Tendsto (fun n => eLpNorm
      (fun z => fderiv ℝ (fn n) z 1 - (g z + h z)) p μ) l (𝓝 0))
    (hy : Tendsto (fun n => eLpNorm
      (fun z => fderiv ℝ (fn n) z I - I * (g z - h z)) p μ) l (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun z => LiZhongQC.dz (fn n) z - g z) p μ) l (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun z => LiZhongQC.dzbar (fn n) z - h z) p μ) l (𝓝 0) := by
  have hz := tendsto_eLpNorm_linear_combination hp (1 / 2 : ℂ) (-I / 2) hx hy
  have hb := tendsto_eLpNorm_linear_combination hp (1 / 2 : ℂ) (I / 2) hx hy
  constructor
  · refine hz.congr' (Eventually.of_forall fun n => ?_)
    apply eLpNorm_congr_ae
    refine Eventually.of_forall fun z => ?_
    simpa only [LiZhongQC.dz] using
      (wirtinger_z_error_eq_linear_combination
        (fderiv ℝ (fn n) z 1) (fderiv ℝ (fn n) z I) (g z) (h z)).symm
  · refine hb.congr' (Eventually.of_forall fun n => ?_)
    apply eLpNorm_congr_ae
    refine Eventually.of_forall fun z => ?_
    simpa only [LiZhongQC.dzbar] using
      (wirtinger_dbar_error_eq_linear_combination
        (fderiv ℝ (fn n) z 1) (fderiv ℝ (fn n) z I) (g z) (h z)).symm

/-- Every compact subset admits genuine C∞ compact
approximants inside the domain, uniformly approximating the function and
converging to both actual distributional Wirtinger derivatives in finite Lp. -/
theorem exists_smooth_compact_wirtinger_approximation
    {f g h : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hw : HasDistributionalWirtingerDerivatives f g h U)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    (hloc : ∀ C ⊆ U, IsCompact C →
      MemLp g p (volume.restrict C) ∧ MemLp h p (volume.restrict C))
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ φ : ℕ → ℂ → ℂ,
      (∀ n, ContDiff ℝ ∞ (φ n) ∧ HasCompactSupport (φ n) ∧ tsupport (φ n) ⊆ U) ∧
      TendstoUniformlyOn φ f atTop K ∧
      Tendsto (fun n => eLpNorm (fun z => dz (φ n) z - g z)
        p (volume.restrict K)) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun z => dzbar (φ n) z - h z)
        p (volume.restrict K)) atTop (𝓝 0) := by
  have hreal : ∀ C ⊆ U, IsCompact C →
      MemLp (fun z => g z + h z) p (volume.restrict C) ∧
        MemLp (fun z => I * (g z - h z)) p (volume.restrict C) := by
    intro C hCU hC
    obtain ⟨hg, hh⟩ := hloc C hCU hC
    refine ⟨MemLp.ae_eq (f := g + h) (g := fun z => g z + h z)
      (Eventually.of_forall fun z => Pi.add_apply g h z) (hg.add hh), ?_⟩
    exact MemLp.ae_eq (f := fun z => I * (g - h) z)
      (g := fun z => I * (g z - h z))
      (Eventually.of_forall fun z => by
        change I * (g - h) z = I * (g z - h z)
        rw [Pi.sub_apply]) ((hg.sub hh).const_mul I)
  obtain ⟨φ, hφ, hval, hx, hy⟩ := exists_smooth_compact_approximation_of_distributional
    hU hf hw.real_partials hp hp' hreal hK hKU
  obtain ⟨hz, hzb⟩ := tendsto_eLpNorm_wirtinger_sub hp hx hy
  exact ⟨φ, hφ, hval, hz, hzb⟩

/-- Local L1 weak Wirtinger derivatives imply ACL and identify the actual
coordinate-line partials almost everywhere. No total derivative is assumed. -/
theorem isACL_of_distributional_wirtinger {f g h : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : ContinuousOn f U)
    (hw : HasDistributionalWirtingerDerivatives f g h U) :
    IsACL f U ∧ (∀ᵐ z ∂(volume.restrict U), partialX f z = g z + h z) ∧
      ∀ᵐ z ∂(volume.restrict U), partialY f z = I * (g z - h z) :=
  isACL_of_distributional_partials hU hf hw.real_partials

/-- ACL implies existence of both coordinate-line partial derivatives a.e.
The rational-rectangle assembly is the one used in the fixed source S09. -/
theorem isACL_coordinate_differentiable_ae {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hacl : IsACL f U) :
    ∀ᵐ z ∂(volume.restrict U),
      DifferentiableAt ℝ (fun t : ℝ => f (z + t)) 0 ∧
        DifferentiableAt ℝ (fun t : ℝ => f (z + t * I)) 0 := by
  obtain ⟨hc, hrect⟩ := hacl
  have hcover : U = ⋃ q : {q : ℚ × ℚ × ℚ × ℚ //
      (q.1 : ℝ) < q.2.1 ∧ (q.2.2.1 : ℝ) < q.2.2.2 ∧
        closedRect q.1 q.2.1 q.2.2.1 q.2.2.2 ⊆ U},
      openRect q.1.1 q.1.2.1 q.1.2.2.1 q.1.2.2.2 := by
    ext z
    constructor
    · intro hz
      obtain ⟨q, h1, h2, h3, h4⟩ := acl_exists_rat_rect hU hz
      exact mem_iUnion.2 ⟨⟨q, h1, h2, h3⟩, h4⟩
    · intro hz
      obtain ⟨q, hq⟩ := mem_iUnion.1 hz
      exact q.2.2.2 (acl_openRect_subset_closedRect le_rfl le_rfl le_rfl le_rfl hq)
  rw [hcover, ae_restrict_iUnion_iff]
  intro q
  exact acl_ae_rect hc q.2.1 q.2.2.1 q.2.2.2
    (hrect _ _ _ _ q.2.1 q.2.2.1 q.2.2.2).2
    (hrect _ _ _ _ q.2.1 q.2.2.1 q.2.2.2).1

/-- For a homeomorphism, actual local L1 weak Wirtinger derivatives are the
ordinary total-fderiv-based Wirtinger derivatives a.e. Menchoff's theorem
supplies total differentiability from the proved coordinate partials. -/
theorem homeomorph_wirtinger_eq_distributional_ae {f g h : ℂ → ℂ} {U V : Set ℂ}
    (hU : IsOpen U) (hf : IsHomeomorphOnto f U V)
    (hw : HasDistributionalWirtingerDerivatives f g h U) :
    ∀ᵐ z ∂(volume.restrict U), dz f z = g z ∧ dzbar f z = h z := by
  obtain ⟨hacl, hx, hy⟩ := isACL_of_distributional_wirtinger hU hf.1 hw
  have hdiff := differentiable_ae_of_partials hU hf (isACL_coordinate_differentiable_ae hU hacl)
  filter_upwards [hdiff, hx, hy] with z hdiffz hxz hyz
  have hfx : fderiv ℝ f z 1 = g z + h z := by
    rw [← partialX_eq_of_differentiableAt hdiffz, hxz]
  have hfy : fderiv ℝ f z I = I * (g z - h z) := by
    rw [← partialY_eq_of_differentiableAt hdiffz, hyz]
  constructor
  · simp only [dz, hfx, hfy]
    ring_nf
    simp only [I_sq]
    ring
  · simp only [dzbar, hfx, hfy]
    ring_nf
    simp only [I_sq]
    ring

end LowDimensionalTopology.Geometry.Quasiconformal
