/-
Copyright (c) 2026 Wu Xiaobin.
The deck-equivariant representative and homotopy assembly adapts Wu Xiaobin's
Li-Zhong-QC-formalization, fixed commit
1c0d5473c020b66ed5106331a38a61536760b9b2, original file
LiZhongQC/Ch06/S24_QuasiFuchsian.lean (s24q_genus_ge_two).
It reuses the actual extension and descent APIs distributed in that archive
as LiZhongQC/Lemmas/DEDescent.lean and DouadyEarle/Extension.lean.
Local changes: expose real analyticity of the actual Cayley conjugate,
descend it through the existing holomorphic covering sheets in every original
chart, and retain the actual target and marked quotient class.
Released under Apache 2.0 license as described in the file LICENSE.
See THIRD_PARTY_NOTICES.md and the retained LiZhongQC license.
-/
module

public import LowDimensionalTopology.Geometry.Teichmuller.DECoverDescent
public import LowDimensionalTopology.External.LiZhongQC.Ch07.S27_TeichmullerExistence
public import LowDimensionalTopology.Geometry.Surfaces.Topology.TorusFundamentalGroup
public import Mathlib.Analysis.Analytic.Constructions

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter Topology MeasureTheory
open scoped ComplexConjugate ContDiff Manifold

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC

universe u v w

/-- The actual DE half-plane map is real analytic in its original coordinates. -/
theorem de_upper_analyticOnNhd (φ : Circle → Circle)
    (hφ : Function.Bijective φ) (hφc : Continuous φ)
    (E : UpperHalfPlane ≃ₜ UpperHalfPlane)
    (hE : ∀ τ : UpperHalfPlane, cayley (E τ) = extension φ (cayley τ)) :
    AnalyticOnNhd ℝ (liftToC E) upperHalf := by
  have hC : AnalyticOnNhd ℂ cayley upperHalf := by
    intro z hz
    exact (analyticAt_id.sub analyticAt_const).div
      (analyticAt_id.add analyticAt_const) (cayley_den_ne_zero hz)
  have hI : AnalyticOnNhd ℂ cayleyInv (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    exact (analyticAt_const.mul (analyticAt_const.add analyticAt_id)).div
      (analyticAt_const.sub analyticAt_id)
      (cayleyInv_den_ne_zero (mem_ball_zero_iff.mp hw))
  have hΦ : AnalyticOnNhd ℝ (extension φ) (Metric.ball (0 : ℂ) 1) :=
    Metric.isOpen_ball.analyticOn_iff_analyticOnNhd.mp (extension_analyticOn_disk φ hφ hφc)
  have hmC : MapsTo cayley upperHalf (Metric.ball (0 : ℂ) 1) :=
    fun z hz => cayley_mem_unitDisc hz
  have hmΦ : MapsTo (extension φ) (Metric.ball (0 : ℂ) 1) (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    exact mem_ball_zero_iff.mpr
      (extension_mem_disk φ hφ hφc w (mem_ball_zero_iff.mp hw))
  have hG : AnalyticOnNhd ℝ (fun z => cayleyInv (extension φ (cayley z))) upperHalf :=
    hI.restrictScalars.comp (hΦ.comp hC.restrictScalars hmC) (hmΦ.comp hmC)
  have he : EqOn (liftToC E) (fun z => cayleyInv (extension φ (cayley z))) upperHalf := by
    intro z hz
    rw [h23l_liftToC_eq E hz]
    have hcoe : ((UpperHalfPlane.ofComplex z : UpperHalfPlane) : ℂ) = z := by
      rw [UpperHalfPlane.ofComplex_apply_of_im_pos (show 0 < z.im from hz)]
    calc
      (E (UpperHalfPlane.ofComplex z) : ℂ) =
          cayleyInv (cayley (E (UpperHalfPlane.ofComplex z))) :=
        (cayleyInv_cayley (E (UpperHalfPlane.ofComplex z)).coe_im_pos).symm
      _ = _ := by rw [hE, hcoe]
  intro z hz
  apply (hG z hz).congr
  exact Filter.eventuallyEq_of_mem (isOpen_upperHalf.mem_nhds hz) fun w hw => (he hw).symm

private theorem realAnalytic_charts_of_analytic_cover
    {U : Type u} {X : Type v} {Y : Type w}
    [TopologicalSpace U] [TopologicalSpace X] [TopologicalSpace Y]
    {A : RiemannAtlas U} {B : RiemannAtlas X} {C : RiemannAtlas Y}
    {p : U → X} {f : X → Y}
    (hp : RiemannAnalyticMap A B p) (hpl : IsLocalHomeomorph p)
    (hps : Function.Surjective p)
    (hF : ∀ a ∈ A.charts, ∀ g ∈ C.charts,
      AnalyticOnNhd ℝ (riemannChartMap a (f ∘ p) g)
        (riemannChartMapDomain a (f ∘ p) g)) :
    ∀ e ∈ B.charts, ∀ g ∈ C.charts,
      AnalyticOnNhd ℝ (riemannChartMap e f g) (riemannChartMapDomain e f g) := by
  intro e he g hg t ht
  obtain ⟨u₀, hu₀⟩ := hps (e.symm t)
  obtain ⟨a, ha, hua⟩ := A.cover u₀
  have hpu : p u₀ ∈ e.source := by rw [hu₀]; exact e.map_target ht.1
  have hfg : (f ∘ p) u₀ ∈ g.source := by
    change f (p u₀) ∈ g.source
    rw [hu₀]
    exact ht.2
  obtain ⟨P, hPfun, huP, hP, hsub⟩ :=
    analyticLocalHomeomorph_coordinateSheet hp hpl a ha e he u₀ hua hpu
  have hPval : P (a u₀) = t := by
    rw [hPfun]
    change e (p (a.symm (a u₀))) = t
    rw [a.left_inv hua, hu₀, e.right_inv ht.1]
  have htP : t ∈ P.target := hPval ▸ P.map_source huP
  have hPinv : P.symm t = a u₀ := by rw [← hPval, P.left_inv huP]
  have hi := openPartialHomeomorph_analytic_inverse P hP
  let F := riemannChartMap a (f ∘ p) g
  have hFdom : a u₀ ∈ riemannChartMapDomain a (f ∘ p) g := by
    refine ⟨a.map_source hua, ?_⟩
    change (f ∘ p) (a.symm (a u₀)) ∈ g.source
    rw [a.left_inv hua]
    exact hfg
  have hFat : AnalyticAt ℝ F (P.symm t) := by
    rw [hPinv]
    exact hF a ha g hg (a u₀) hFdom
  have hcomp : AnalyticAt ℝ (F ∘ P.symm) t :=
    hFat.comp (hi t htP).restrictScalars
  apply hcomp.congr
  filter_upwards [P.open_target.mem_nhds htP] with s hs
  have hsP := hsub (P.map_target hs)
  have hproj : p (a.symm (P.symm s)) = e.symm s := by
    calc
      p (a.symm (P.symm s)) = e.symm (e (p (a.symm (P.symm s)))) :=
        (e.left_inv hsP.2).symm
      _ = e.symm (P (P.symm s)) := by rw [hPfun]; rfl
      _ = e.symm s := congrArg e.symm (P.right_inv hs)
  change g (f (p (a.symm (P.symm s)))) = g (f (e.symm s))
  rw [hproj]

/-- A real-analytic actual lift descends in every original source and target chart. -/
theorem uniformization_realAnalytic_charts
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    {Γ₀ Γ₁ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    {p₀ : UpperHalfPlane → X} {p₁ : UpperHalfPlane → Y}
    (hp₀ : IsUniformization Γ₀ p₀) (hp₁ : IsUniformization Γ₁ p₁)
    (E : UpperHalfPlane ≃ₜ UpperHalfPlane) (f : X ≃ₜ Y)
    (hf : IsLift p₀ p₁ f E)
    (hE : AnalyticOnNhd ℝ (liftToC E) upperHalf) :
    ∀ e ∈ (RiemannAtlas.ofManifold X).charts,
      ∀ g ∈ (RiemannAtlas.ofManifold Y).charts,
        AnalyticOnNhd ℝ (riemannChartMap e f g) (riemannChartMapDomain e f g) := by
  have hpa : RiemannAnalyticMap upperHalfNativeSurface.toRiemannAtlas
      (RiemannAtlas.ofManifold X) p₀ :=
    riemannAnalyticMap_of_contMDiff_ofManifold
      (k22u_mdifferentiable_contMDiff hp₀.2.1)
  have hqa : RiemannAnalyticMap upperHalfNativeSurface.toRiemannAtlas
      (RiemannAtlas.ofManifold Y) p₁ :=
    riemannAnalyticMap_of_contMDiff_ofManifold
      (k22u_mdifferentiable_contMDiff hp₁.2.1)
  apply realAnalytic_charts_of_analytic_cover hpa hp₀.1.isLocalHomeomorph hp₀.2.2.1
  intro a ha g hg t ht
  have ha0 : a = UpperHalfPlane.ofComplex.symm := by
    change a ∈ ({UpperHalfPlane.ofComplex.symm} : Set (OpenPartialHomeomorph UpperHalfPlane ℂ)) at ha
    exact Set.mem_singleton_iff.mp ha
  subst a
  have htarget : UpperHalfPlane.ofComplex.symm.target = upperHalf := by
    change (UpperHalfPlane.isOpenEmbedding_coe.toOpenPartialHomeomorph UpperHalfPlane.coe).target = upperHalf
    rw [Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, UpperHalfPlane.range_coe]
    rfl
  have htH : t ∈ upperHalf := by
    simpa only [UpperHalfPlane.ofComplex, OpenPartialHomeomorph.symm_symm,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target, UpperHalfPlane.range_coe,
      UpperHalfPlane.upperHalfPlaneSet, LiZhongQC.upperHalf] using ht.1
  have hA : UpperHalfPlane.ofComplex.symm ∈ upperHalfNativeSurface.charts := by
    change _ ∈ ({UpperHalfPlane.ofComplex.symm} : Set (OpenPartialHomeomorph UpperHalfPlane ℂ))
    exact Set.mem_singleton _
  have hQ : AnalyticAt ℂ (riemannChartMap UpperHalfPlane.ofComplex.symm p₁ g)
      (liftToC E t) := by
    rw [h23l_liftToC_eq E htH]
    apply hqa.2 UpperHalfPlane.ofComplex.symm hA g hg
    refine ⟨?_, ?_⟩
    · simpa only [htarget, LiZhongQC.upperHalf, Set.mem_ofPred_eq] using
        (E (UpperHalfPlane.ofComplex t)).coe_im_pos
    · change p₁ (UpperHalfPlane.ofComplex (E (UpperHalfPlane.ofComplex t) : ℂ)) ∈ g.source
      rw [UpperHalfPlane.ofComplex_apply, hf]
      exact ht.2
  have hcomp := hQ.restrictScalars.comp (hE t htH)
  apply hcomp.congr
  filter_upwards [isOpen_upperHalf.mem_nhds htH] with w hw
  change g (p₁ (UpperHalfPlane.ofComplex (liftToC E w))) =
    g (f (p₀ (UpperHalfPlane.ofComplex w)))
  rw [h23l_liftToC_eq E hw, UpperHalfPlane.ofComplex_apply, hf]

/-- Every original higher-genus marking has a real-analytic quasiconformal
representative on the same actual target, in its actual free homotopy class. -/
theorem exists_realAnalytic_qc_in_homotopy_class
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace ℂ X] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ) ω X] [IsManifold 𝓘(ℂ) ω Y]
    [T2Space X] [ConnectedSpace X] [T2Space Y] [ConnectedSpace Y]
    {g : ℕ} (hg : 1 < g) (hX : LiZhongQC.HasGenus X g) (hY : LiZhongQC.HasGenus Y g)
    (f : X ≃ₜ Y) (hf : IsOrientationPreservingRS f) :
    ∃ q : X ≃ₜ Y, IsQCRS q ∧
      (∀ e ∈ (RiemannAtlas.ofManifold X).charts,
        ∀ b ∈ (RiemannAtlas.ofManifold Y).charts,
          AnalyticOnNhd ℝ (riemannChartMap e q b) (riemannChartMapDomain e q b)) ∧
      ContinuousMap.Homotopic (f : C(X, Y)) (q : C(X, Y)) := by
  let := hX.1
  let := hY.1
  obtain ⟨Γ₀, p₀, hΓ₀, hfree₀, hp₀⟩ := s22hg_exists_fuchsian_uniformization hg hX
  obtain ⟨Γ₁, p₁, hΓ₁, hfree₁, hp₁⟩ := s22hg_exists_fuchsian_uniformization hg hY
  obtain ⟨τ₀⟩ : Nonempty UpperHalfPlane := inferInstance
  obtain ⟨τ₁, hτ₁⟩ := hp₁.2.2.1 (f (p₀ τ₀))
  obtain ⟨L, hL, -⟩ := exists_lift hp₀ hp₁ f τ₀ τ₁ hτ₁
  obtain ⟨φ, hφ, hφc, hor, hbd⟩ :=
    s24q_boundary hΓ₀ hfree₀ hp₀ hΓ₁ hfree₁ hp₁ hf hL
  obtain ⟨E, hE, hC1, hlt⟩ := s24q_de_upper φ hφ hφc hor
  have hEa := de_upper_analyticOnNhd φ hφ hφc E hE
  have hLE : ∀ γ δ : Matrix.SpecialLinearGroup (Fin 2) ℝ, γ ∈ Γ₀ →
      (∀ τ, L (γ • τ) = δ • L τ) → ∀ τ, E (γ • τ) = δ • E τ :=
    fun γ δ hγ hγδ => s24q_de_equivariant hφ hφc hE (hbd γ δ hγ hγδ)
  have h₀₁ : ∀ γ ∈ Γ₀, ∃ δ ∈ Γ₁, ∀ τ, E (γ • τ) = δ • E τ := by
    intro γ hγ
    obtain ⟨δ, hδ, hγδ⟩ := h23l_deck hp₀ hp₁ hL hγ
    exact ⟨δ, hδ, hLE γ δ hγ hγδ⟩
  have h₁₀ : ∀ δ ∈ Γ₁, ∃ γ ∈ Γ₀, ∀ τ, E (γ • τ) = δ • E τ := by
    intro δ hδ
    obtain ⟨γ, hγ, hγδ⟩ := s24q_deck_surj hp₀ hp₁ hL hδ
    exact ⟨γ, hγ, hLE γ δ hγ hγδ⟩
  obtain ⟨k, hk0, hk1, hk⟩ := s24q_sup_lt_one hp₀ hC1 hlt fun γ hγ => by
    obtain ⟨δ, -, hδ⟩ := h₀₁ γ hγ
    exact ⟨δ, hδ⟩
  obtain ⟨q, hq⟩ := s24q_descend hp₀ hp₁ E h₀₁ h₁₀
  refine ⟨q, ⟨_, s24q_isKQCRS hp₀ hp₁ hq (s24q_isKQC_of_bound hC1 hlt hk0 hk1 hk)⟩,
    uniformization_realAnalytic_charts hp₀ hp₁ E q hq hEa, ?_⟩
  apply (thm23_1_homotopy_iff hp₀ hp₁ f q hL hq).2
  refine ⟨1, Γ₁.one_mem, ?_⟩
  intro γ hγ τ
  obtain ⟨δ, -, hγδ⟩ := h23l_deck hp₀ hp₁ hL hγ
  have hE' := hLE γ δ hγ hγδ
  rw [one_smul, inv_one, one_smul, hγδ, hE', Homeomorph.apply_symm_apply,
    Homeomorph.apply_symm_apply]

/-- The actual original marked class keeps its target and has a real-analytic
QC marking. The equality is in the independently defined original quotient. -/
theorem markedClass_exists_realAnalytic
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
    [IsManifold 𝓘(ℂ) ω X] [T2Space X] [ConnectedSpace X]
    {g : ℕ} (hg : 1 < g) (hX : LiZhongQC.HasGenus X g) (m : MarkedRS X) :
    ∃ (q : X ≃ₜ m.X.carrier) (hq : IsQCRS q),
      (∀ e ∈ (RiemannAtlas.ofManifold X).charts,
        ∀ b ∈ (RiemannAtlas.ofManifold m.X.carrier).charts,
          AnalyticOnNhd ℝ (riemannChartMap e q b) (riemannChartMapDomain e q b)) ∧
      (Quot.mk _ (⟨m.X, q, hq⟩ : MarkedRS X) : TeichSpace X) = Quot.mk _ m := by
  have hY : LiZhongQC.HasGenus m.X.carrier g := by
    refine ⟨inferInstance, fun y => ?_⟩
    obtain ⟨e⟩ := hX.2 (m.marking.symm y)
    exact ⟨(fundamentalGroupHomeomorphMulEquiv m.marking.symm y).trans e⟩
  have hm : IsOrientationPreservingRS m.marking := by
    obtain ⟨K, _, hK⟩ := m.qc
    exact fun x => (hK x).isSensePreserving
  obtain ⟨q, hq, hqa, hhom⟩ :=
    exists_realAnalytic_qc_in_homotopy_class hg hX hY m.marking hm
  exact ⟨q, hq, hqa, Quot.sound
    (markedRS_equiv_same_surface m.X q m.marking hq m.qc hg hY hhom.symm)⟩

end LowDimensionalTopology.Geometry.Teichmuller
