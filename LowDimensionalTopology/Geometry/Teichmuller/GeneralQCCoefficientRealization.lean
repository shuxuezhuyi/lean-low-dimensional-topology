/-
Copyright (c) 2026 The gpt-lean-low-dimensional-topology authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The gpt-lean-low-dimensional-topology authors

The local deformation charts and covering arguments below reuse Wu Xiaobin's
LiZhongQC, Apache-2.0, pinned upstream 1c0d5473c020b66ed5106331a38a61536760b9b2.
See THIRD_PARTY_NOTICES.md. The general native target is constructed here;
no compact-target packaging theorem is used.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.GeneralQCMarkedSpace
public import LowDimensionalTopology.Geometry.Teichmuller.SourceMarkingSurjectivity

/-!
# General QC targets realizing compatible coefficients

The original surface and its given upper-half-plane covering are retained.
Every compatible measurable coefficient with bound less than one gives an
actual new native atlas on the same topological point set, an actual QC
marking, and its actual conjugated uniformization. The dilatation parameter
is an upper bound, rather than an asserted value of the maximal dilatation.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
open scoped Manifold ContDiff UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Teichmuller.GeneralQC

open Surfaces LiZhongQC
universe u

/-- The unchanged point map into the atlas read from the original manifold
is biholomorphic, independently of the preferred chart choices. -/
theorem manifold_nativeAtlas_identity_biholomorphic
    {Y : Type u} [TY : TopologicalSpace Y] [CY : ChartedSpace ℂ Y]
    [MY : IsManifold 𝓘(ℂ) ω Y] :
    @LiZhongQC.IsBiholomorphic Y TY CY Y TY
      (RiemannAtlas.ofManifold Y).toChartedSpace (id : Y → Y) := by
  let A := RiemannAtlas.ofManifold Y
  apply (analyticHomeomorph_ofManifold_iff_sourceBiholomorphic
    (CX := CY) (CY := A.toChartedSpace) (MX := MY) (MY := A.isManifold)
    (Homeomorph.refl Y)).mp
  change RiemannAnalyticMap A A (id : Y → Y)
  exact RiemannAnalyticMap.id A

/-- Construct the target atlas from the actual deformed covering charts.
There is no compactness premise and no supplied target complex structure. -/
private theorem exists_native_coefficient_atlas
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    {μ : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hμ : IsBeltramiCoeff μ upperHalf k) (hΓ : IsGammaCompatible Γ μ)
    {F : ℍ ≃ₜ ℍ} (hF : ∀ τ, (F τ : ℂ) = s27u_fSym μ τ) :
    ∃ (S : Surface.{u}) (e : R.carrier ≃ₜ S.carrier),
      let := S.riemann.toRiemannAtlas.toChartedSpace
      MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (s27u_proj p e F) := by
  have hcont : Continuous p := hp.1.continuous
  have hEx : ∀ x : R.carrier,
      ∃ E : OpenPartialHomeomorph ℍ R.carrier, x ∈ E.target ∧ ⇑E = p := by
    intro x
    obtain ⟨τ, rfl⟩ := hp.2.2.1 x
    obtain ⟨E, hτE, hpE⟩ := hp.1.isLocalHomeomorph τ
    exact ⟨E, by rw [hpE]; exact E.map_source hτE, hpE.symm⟩
  choose E hEmem hEp using hEx
  let ψ := fun x => s27v_a_chart (E x) F
  have hmem : ∀ x, x ∈ (ψ x).source := by
    intro x
    rw [s27v_a_chart_source]
    exact hEmem x
  have hΦ : ∀ (x : R.carrier) (v : ℂ), 0 < v.im →
      p (F.symm (UpperHalfPlane.ofComplex v)) ∈ (E x).target →
      DifferentiableAt ℂ
        (fun w => (F ((E x).symm (p (F.symm (UpperHalfPlane.ofComplex w)))) : ℂ)) v :=
    fun x _ hv hm => s27v_a_phi hcont hp.2.2.2 hk0 hk1 hμ hΓ hF (E x) (hEp x) hv hm
  have hcompat : ∀ x x', ∀ w ∈ (ψ x').target, (ψ x').symm w ∈ (ψ x).source →
      DifferentiableAt ℂ (fun w => ψ x ((ψ x').symm w)) w := by
    intro x x' w hw hwx
    obtain ⟨hwim, hsw⟩ := s27v_a_chart_symm (E x') F hw
    rw [s27v_a_chart_source, hsw, hEp x'] at hwx
    refine (hΦ x w hwim hwx).congr_of_eventuallyEq ?_
    filter_upwards [(ψ x').open_target.mem_nhds hw] with v hv
    rw [s27v_a_chart_apply, (s27v_a_chart_symm (E x') F hv).2, hEp x']
  let τY : TopologicalSpace (s26d_a_X R.carrier) := R.topology
  let cY : ChartedSpace ℂ (s26d_a_X R.carrier) :=
    ChartedSpace.mk (Set.range ψ) ψ hmem (fun x => ⟨x, rfl⟩)
  have hman : IsManifold 𝓘(ℂ) ω (s26d_a_X R.carrier) := by
    apply isManifold_of_contDiffOn
    rintro e e' ⟨x', rfl⟩ ⟨x, rfl⟩
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.id_comp, Function.comp_id, preimage_id_eq, id_eq, range_id, inter_univ]
    have hopen : IsOpen ((ψ x').symm.trans (ψ x)).source :=
      ((ψ x').symm.trans (ψ x)).open_source
    refine (DifferentiableOn.analyticOnNhd (fun w hw => ?_) hopen).contDiffOn_of_completeSpace
    rw [OpenPartialHomeomorph.trans_source] at hw
    exact (hcompat x x' w hw.1 hw.2).differentiableWithinAt
  let : IsManifold 𝓘(ℂ) ω (s26d_a_X R.carrier) := hman
  let : T2Space (s26d_a_X R.carrier) := R.riemann.t2Space
  let : ConnectedSpace (s26d_a_X R.carrier) := R.riemann.connectedSpace
  let S : Surface.{u} :=
    { carrier := s26d_a_X R.carrier, topology := τY,
      riemann := RiemannSurface.ofManifold (s26d_a_X R.carrier) }
  let e : R.carrier ≃ₜ s26d_a_X R.carrier :=
    ⟨Equiv.refl _, continuous_id, continuous_id⟩
  have hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (s27u_proj p e F) := by
    intro τ
    have hkey : ∀ σ, chartAt ℂ (e (p (F.symm τ))) (e (p (F.symm σ))) =
        (F ((E (p (F.symm τ))).symm (p (F.symm σ))) : ℂ) := fun _ => rfl
    have hd : DifferentiableAt ℂ
        ((fun σ => chartAt ℂ (e (p (F.symm τ))) (e (p (F.symm σ)))) ∘
          UpperHalfPlane.ofComplex) (τ : ℂ) := by
      have h := hΦ (p (F.symm τ)) τ τ.coe_im_pos (by
        rw [UpperHalfPlane.ofComplex_apply]
        exact hEmem _)
      refine h.congr_of_eventuallyEq (Eventually.of_forall fun v => ?_)
      simp only [Function.comp_apply]
      exact hkey _
    have hm1 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ)
        (fun σ => chartAt ℂ (e (p (F.symm τ))) (e (p (F.symm σ)))) τ :=
      UpperHalfPlane.mdifferentiableAt_iff.2 hd
    have hsrc : e (p (F.symm τ)) ∈ (chartAt ℂ (e (p (F.symm τ)))).source :=
      mem_chart_source ℂ _
    have hcp : Continuous (fun σ => e (p (F.symm σ))) :=
      e.continuous.comp (hcont.comp F.symm.continuous)
    have hm2 : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (chartAt ℂ (e (p (F.symm τ)))).symm
        (chartAt ℂ (e (p (F.symm τ))) (e (p (F.symm τ)))) :=
      mdifferentiableAt_atlas_symm (chart_mem_atlas ℂ _) ((chartAt ℂ _).map_source hsrc)
    have hev : (fun σ => e (p (F.symm σ))) =ᶠ[𝓝 τ]
        (chartAt ℂ (e (p (F.symm τ)))).symm ∘
          fun σ => chartAt ℂ (e (p (F.symm τ))) (e (p (F.symm σ))) := by
      filter_upwards [hcp.continuousAt.preimage_mem_nhds
        ((chartAt ℂ _).open_source.mem_nhds hsrc)] with σ hσ
      exact ((chartAt ℂ _).left_inv hσ).symm
    exact (hm2.comp τ hm1).congr_of_eventuallyEq hev
  have hid := manifold_nativeAtlas_identity_biholomorphic (CY := cY) (MY := hman)
  refine ⟨S, e, ?_⟩
  exact @MDifferentiable.comp
    ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ) ℍ _ _
    ℂ _ _ ℂ _ 𝓘(ℂ) (s26d_a_X R.carrier) τY cY
    ℂ _ _ ℂ _ 𝓘(ℂ) (s26d_a_X R.carrier) τY
      (RiemannAtlas.ofManifold (s26d_a_X R.carrier)).toChartedSpace
    (s27u_proj p e F) id hid.1 hhol

/-- Every compatible coefficient is realized on an actual general native
surface with its original QC marking and conjugated conformal covering.
The value `(1+k)/(1-k)` is a QC upper bound for the marking. -/
theorem exists_marked_of_compatible_coefficient
    (R : Surface.{u}) {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p : ℍ → R.carrier} (hp : IsUniformization Γ p)
    {μ : ℂ → ℂ} {k : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hμ : IsBeltramiCoeff μ upperHalf k) (hΓ : IsGammaCompatible Γ μ) :
    ∃ (m : Marked.{u, u} R) (F : ℍ ≃ₜ ℍ),
      (∀ τ, (F τ : ℂ) = s27u_fSym μ τ) ∧
      IsUniformization (s27u_conjGroup Γ F) (s27u_proj p m.marking F) ∧
      IsFuchsian (s27u_conjGroup Γ F) ∧ ActsFreely (s27u_conjGroup Γ F) ∧
      IsNormalizedLift p (s27u_proj p m.marking F) m.marking F
        (OnePoint.map (s27u_fSym μ)) ∧
      IsKQCRS m.marking ((1 + k) / (1 - k)) ∧
      ∀ᵐ z ∂(MeasureTheory.volume.restrict upperHalf),
        s27u_liftCoeff p m.marking z = μ z := by
  obtain ⟨-, hN, hwK, -⟩ := s27u_sym_spec hk0 hk1 hμ
  obtain ⟨hwU, -, -, hwKU, hwd⟩ := s27u_fSym_upperHalf hk0 hk1 hμ
  obtain ⟨F, hF⟩ := s27u_homeo_upper hwK hN.2.1 hwU
  obtain ⟨S, e, hhol⟩ := exists_native_coefficient_atlas R hp hk0 hk1 hμ hΓ hF
  have hU := s27v_isUniformization hp hk0 hk1 hμ hΓ hF e hhol
  have hL : IsLift p (s27u_proj p e F) e F := fun τ => by
    show e (p (F.symm (F τ))) = e (p τ)
    rw [F.symm_apply_apply]
  have hFeq : EqOn (liftToC F) (s27u_fSym μ) upperHalf := by
    intro z hz
    rw [h23l_liftToC_eq F hz,
      UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    exact hF _
  have hFK : IsKQC (liftToC F) upperHalf ((1 + k) / (1 - k)) :=
    ad_isKQC_congr hwKU hFeq
  have hQC := s27v_isKQCRS_of_lift hp hU hL hFK
  let m : Marked.{u, u} R := ⟨S, e, ⟨_, hQC⟩⟩
  refine ⟨m, F, hF, hU, utm_x2_isFuchsian hU, s27g_actsFreely hU,
    s27u_isNormalizedLift e hwK hN.2.1 hwU hN.2.2.1 hN.2.2.2.1 hF, hQC, ?_⟩
  filter_upwards [hwd, MeasureTheory.ae_restrict_mem isOpen_upperHalf.measurableSet]
    with z hz hzu
  show s27u_liftCoeff p e z = μ z
  rw [← s27u_liftCoeff_eq_dilatation hp hU hL hzu, ← hz]
  exact abR_t_complexDilatation_congr isOpen_upperHalf hFeq hzu

end LowDimensionalTopology.Geometry.Teichmuller.GeneralQC
