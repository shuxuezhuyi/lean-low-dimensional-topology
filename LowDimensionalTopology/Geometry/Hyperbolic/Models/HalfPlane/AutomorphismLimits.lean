module

public import LowDimensionalTopology.External.LiZhongQC.Ch06.S22_RiemannSurfaces
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.HalfPlane.GeodesicBoundary
public import LowDimensionalTopology.Geometry.Mobius.Metric.ChordalIsometries
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Limits of actual analytic half-plane automorphisms

A pointwise limit in the actual compactified complex plane is either another
analytic automorphism or one constant ideal boundary point. This includes
infinity and proves the compact-local assertion with weaker convergence data.
There is no assumed inverse sequence or assumed normal-family extraction.

The finite-entry bounded extraction adapts the existing public argument
`LiZhongQC.k22_t_tendsto_norm` from Wu Xiaobin's Li-Zhong-QC-formalization,
commit `1c0d5473c020b66ed5106331a38a61536760b9b2`, Apache-2.0; see
`THIRD_PARTY_NOTICES.md`. The divergent case uses the existing real-matrix
convergence theorem directly, with both exceptional points on the ideal boundary.
-/

public section
noncomputable section
open Set Filter Metric
open scoped UpperHalfPlane Topology OnePoint Manifold

namespace LowDimensionalTopology.Geometry.Hyperbolic

private theorem exists_realSL_entrywise_subsequence_of_not_tendsto_norm
    (A : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hnot : ¬ Tendsto (fun n => ‖(A n) 0 0‖ + ‖(A n) 0 1‖ +
      ‖(A n) 1 0‖ + ‖(A n) 1 1‖) atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
        ∀ i j : Fin 2, Tendsto (fun n => (A (φ n)) i j) atTop (𝓝 (B i j)) := by
  rw [Filter.tendsto_atTop] at hnot
  simp only [not_forall, Filter.not_eventually, not_le] at hnot
  obtain ⟨M, hM⟩ := hnot
  let v : ℕ → (Fin 2 → Fin 2 → ℝ) := fun n i j => (A n) i j
  have hfreq : ∃ᶠ n in atTop, v n ∈ closedBall (0 : Fin 2 → Fin 2 → ℝ) M := by
    refine hM.mono fun n hn => ?_
    have h00 := norm_nonneg ((A n) 0 0)
    have h01 := norm_nonneg ((A n) 0 1)
    have h10 := norm_nonneg ((A n) 1 0)
    have h11 := norm_nonneg ((A n) 1 1)
    have hM0 : 0 ≤ M := by linarith
    have hij : ∀ i j, ‖v n i j‖ ≤ M := by
      simp only [Fin.forall_fin_two, v]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    rw [mem_closedBall_zero_iff]
    exact (pi_norm_le_iff_of_nonneg hM0).2 fun i =>
      (pi_norm_le_iff_of_nonneg hM0).2 fun j => hij i j
  obtain ⟨G, _hGmem, φ, hφ, hG⟩ :=
    tendsto_subseq_of_frequently_bounded isBounded_closedBall hfreq
  have hdetc : Continuous (Matrix.det : Matrix (Fin 2) (Fin 2) ℝ → ℝ) :=
    continuous_id.matrix_det
  have hdetlim : Tendsto (fun n => Matrix.det (v (φ n))) atTop (𝓝 (Matrix.det G)) :=
    hdetc.continuousAt.tendsto.comp hG
  have hone : (fun n => Matrix.det (v (φ n))) = fun _ => (1 : ℝ) := by
    funext n
    exact (A (φ n)).det_coe
  rw [hone] at hdetlim
  have hdet : Matrix.det G = 1 := tendsto_nhds_unique hdetlim tendsto_const_nhds
  refine ⟨φ, hφ, ⟨G, hdet⟩, ?_⟩
  intro i j
  exact tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hG i) j

private theorem complexified_sl_action
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (z : ℍ) :
    LiZhongQC.mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) A)
      ((z : ℂ) : OnePoint ℂ) = (((A • z : ℍ) : ℂ) : OnePoint ℂ) := by
  rw [LiZhongQC.k22_t_mobiusSL_eq_smul]
  change Mobius.fractionalLinear
    (complexifiedRealMobiusMatrix (Matrix.SpecialLinearGroup.mapGL ℝ A))
      ((z : ℂ) : OnePoint ℂ) = _
  exact realMobiusMatrix_coe _ (by change 0 < A.val.det; rw [A.det_coe]; norm_num) z

private theorem source_extended_real_boundary
    {a : OnePoint ℂ}
    (ha : a ∈ LiZhongQC.toExt {z : ℂ | z.im = 0} ∪ {LiZhongQC.extInf}) :
    a ∈ halfPlaneIdealBoundary := by
  change a ∈ ((↑) : ℂ → OnePoint ℂ) '' {z : ℂ | z.im = 0} ∨ a = ∞ at ha
  change a = ∞ ∨ a ∈ ((↑) : ℂ → OnePoint ℂ) '' {z : ℂ | z.im = 0}
  exact ha.symm

private theorem actual_halfPlane_point_not_boundary (z : ℍ) :
    ((z : ℂ) : OnePoint ℂ) ∉ halfPlaneIdealBoundary := by
  intro h
  change ((z : ℂ) : OnePoint ℂ) = ∞ ∨
    ((z : ℂ) : OnePoint ℂ) ∈ ((↑) : ℂ → OnePoint ℂ) '' {w : ℂ | w.im = 0} at h
  rcases h with h | ⟨w, hw, he⟩
  · exact OnePoint.coe_ne_infty (z : ℂ) h
  · have hwz : w = (z : ℂ) := OnePoint.coe_injective he
    rw [hwz] at hw
    exact z.im_pos.ne' hw

/-- Every pointwise compactified limit of actual determinant-one half-plane
maps is another such map or a constant point of the full ideal boundary.
No regularity assumption on the proposed limit is necessary. -/
theorem realSL_halfPlane_pointwise_limit_dichotomy
    (A : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℝ) (f : ℍ → OnePoint ℂ)
    (hlim : ∀ z : ℍ, Tendsto (fun n => (((A n • z : ℍ) : ℂ) : OnePoint ℂ))
      atTop (𝓝 (f z))) :
    (∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      ∀ z : ℍ, f z = (((B • z : ℍ) : ℂ) : OnePoint ℂ)) ∨
    ∃ a ∈ halfPlaneIdealBoundary, ∀ z : ℍ, f z = a := by
  let C : ℕ → Matrix.SpecialLinearGroup (Fin 2) ℂ :=
    fun n => Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) (A n)
  have hC (n : ℕ) (i j : Fin 2) : C n i j = ((A n i j : ℝ) : ℂ) := rfl
  by_cases hdiv : Tendsto (fun n => ‖A n 0 0‖ + ‖A n 0 1‖ +
      ‖A n 1 0‖ + ‖A n 1 1‖) atTop atTop
  · have hdivC : Tendsto (fun n => ‖C n 0 0‖ + ‖C n 0 1‖ +
        ‖C n 1 0‖ + ‖C n 1 1‖) atTop atTop := by
      simpa only [hC, Complex.norm_real] using hdiv
    obtain ⟨φ, a, b, hφ, hforward, _hinverse, ha, hb⟩ :=
      LiZhongQC.k22_convergence_real C hdivC (by intro n i j; rw [hC]; rfl)
    have ha' := source_extended_real_boundary ha
    have hb' := source_extended_real_boundary hb
    right
    refine ⟨a, ha', ?_⟩
    intro z
    have hzb : b ∉ ({((z : ℂ) : OnePoint ℂ)} : Set (OnePoint ℂ)) := by
      intro he
      have heq : b = ((z : ℂ) : OnePoint ℂ) := mem_singleton_iff.mp he
      exact actual_halfPlane_point_not_boundary z (heq ▸ hb')
    have hn : Tendsto
        (fun n => LiZhongQC.mobiusSL (C (φ n)) ((z : ℂ) : OnePoint ℂ))
        atTop (𝓝 a) := by
      rw [Filter.tendsto_def]
      intro U hU
      filter_upwards [hforward {((z : ℂ) : OnePoint ℂ)} isCompact_singleton hzb U hU]
        with n hn
      exact hn (mem_image_of_mem _ (mem_singleton _))
    have hn' : Tendsto (fun n => (((A (φ n) • z : ℍ) : ℂ) : OnePoint ℂ))
        atTop (𝓝 a) := by
      simpa only [C, complexified_sl_action] using hn
    exact tendsto_nhds_unique ((hlim z).comp hφ.tendsto_atTop) hn'
  · obtain ⟨φ, hφ, B, hB⟩ :=
      exists_realSL_entrywise_subsequence_of_not_tendsto_norm A hdiv
    left
    refine ⟨B, ?_⟩
    intro z
    have hent (i j : Fin 2) : Tendsto (fun n => C (φ n) i j)
        atTop (𝓝 ((B i j : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp (hB i j)
    have hdet : (B 0 0 : ℂ) * (B 1 1 : ℂ) - (B 0 1 : ℂ) * (B 1 0 : ℂ) ≠ 0 := by
      have h := LiZhongQC.k22_t_det (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) B)
      change (B 0 0 : ℂ) * (B 1 1 : ℂ) - (B 0 1 : ℂ) * (B 1 0 : ℂ) = 1 at h
      rw [h]
      exact one_ne_zero
    have hn := LiZhongQC.k22_t_tendsto_mobiusExt
      (hent 0 0) (hent 0 1) (hent 1 0) (hent 1 1) hdet ((z : ℂ) : OnePoint ℂ)
    change Tendsto (fun n => LiZhongQC.mobiusSL (C (φ n)) ((z : ℂ) : OnePoint ℂ))
      atTop (𝓝 (LiZhongQC.mobiusSL (Matrix.SpecialLinearGroup.map (algebraMap ℝ ℂ) B)
        ((z : ℂ) : OnePoint ℂ))) at hn
    have hn' : Tendsto (fun n => (((A (φ n) • z : ℍ) : ℂ) : OnePoint ℂ))
        atTop (𝓝 (((B • z : ℍ) : ℂ) : OnePoint ℂ)) := by
      simpa only [C, complexified_sl_action] using hn
    exact tendsto_nhds_unique ((hlim z).comp hφ.tendsto_atTop) hn'

private theorem realSL_halfPlane_mdifferentiable
    (B : Matrix.SpecialLinearGroup (Fin 2) ℝ) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (fun z : ℍ => B • z) := by
  change MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
    (fun z : ℍ => Matrix.SpecialLinearGroup.mapGL ℝ B • z)
  apply UpperHalfPlane.mdifferentiable_smul
  change 0 < B.val.det
  rw [B.det_coe]
  norm_num

/-- An actual pointwise compactified limit of holomorphic half-plane
homeomorphisms is an actual biholomorphic homeomorphism or one constant ideal
boundary point, including infinity. The inverse is derived, not supplied. -/
theorem analytic_halfPlane_pointwise_limit_dichotomy
    (e : ℕ → (ℍ ≃ₜ ℍ))
    (he : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (e n)) (f : ℍ → OnePoint ℂ)
    (hlim : ∀ z : ℍ, Tendsto (fun n => (((e n z : ℍ) : ℂ) : OnePoint ℂ))
      atTop (𝓝 (f z))) :
    (∃ E : ℍ ≃ₜ ℍ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E.symm ∧
      ∀ z : ℍ, f z = (((E z : ℍ) : ℂ) : OnePoint ℂ)) ∨
    ∃ a ∈ halfPlaneIdealBoundary, ∀ z : ℍ, f z = a := by
  choose A hA using fun n => LiZhongQC.k22c5_eq_smul_of_mdifferentiable (e n) (he n)
  have hlimA : ∀ z : ℍ, Tendsto (fun n => (((A n • z : ℍ) : ℂ) : OnePoint ℂ))
      atTop (𝓝 (f z)) := by
    intro z
    simpa only [← hA] using hlim z
  rcases realSL_halfPlane_pointwise_limit_dichotomy A f hlimA with h | h
  · obtain ⟨B, hB⟩ := h
    left
    refine ⟨Homeomorph.smul B, realSL_halfPlane_mdifferentiable B, ?_, hB⟩
    rw [Homeomorph.smul_symm]
    exact realSL_halfPlane_mdifferentiable B⁻¹
  · exact Or.inr h

local instance automorphismLimitChordalMetric : MetricSpace (OnePoint ℂ) :=
  Mobius.complexChordalMetricSpace

/-- Compact-local chordal convergence of actual holomorphic half-plane
automorphisms has exactly the automorphism-or-constant-boundary alternatives. -/
theorem analytic_halfPlane_compactLocal_limit_dichotomy
    (e : ℕ → (ℍ ≃ₜ ℍ))
    (he : ∀ n, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (e n)) (f : ℍ → OnePoint ℂ)
    (hlim : TendstoLocallyUniformly
      (fun n z => (((e n z : ℍ) : ℂ) : OnePoint ℂ)) f atTop) :
    (∃ E : ℍ ≃ₜ ℍ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E ∧
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) E.symm ∧
      ∀ z : ℍ, f z = (((E z : ℍ) : ℂ) : OnePoint ℂ)) ∨
    ∃ a ∈ halfPlaneIdealBoundary, ∀ z : ℍ, f z = a := by
  apply analytic_halfPlane_pointwise_limit_dichotomy e he f
  intro z
  exact (hlim.tendstoLocallyUniformlyOn (s := univ)).tendsto_at (mem_univ z)

end LowDimensionalTopology.Geometry.Hyperbolic
