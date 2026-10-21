module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Atlas
public import LowDimensionalTopology.Geometry.DiscreteGroups.Finite.FiniteCyclicGroups
public import Mathlib.Analysis.Complex.Schwarz
public import LowDimensionalTopology.Geometry.Surfaces.Quotient.Mobius
@[expose] public section
noncomputable section
open Set Metric
open scoped OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Schwarz's lemma bounds every holomorphic self-map of the genuine unit disc fixing zero. -/
theorem disc_analytic_zero_norm_le (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hm : MapsTo f (ball 0 1) (ball 0 1)) (h0 : f 0 = 0) {z : ℂ} (hz : z ∈ ball 0 1) :
    ‖f z‖ ≤ ‖z‖ := by
  exact Complex.norm_le_norm_of_mapsTo_ball hf.differentiableOn
    (fun _ hz => ball_subset_closedBall (hm hz)) h0 (mem_ball_zero_iff.mp hz)

/-- A genuine analytic disc homeomorphism fixing zero preserves the complex norm. -/
theorem disc_analytic_automorphism_zero_norm (e : OpenPartialHomeomorph ℂ ℂ)
    (hs : e.source = ball 0 1) (ht : e.target = ball 0 1)
    (he : AnalyticOnNhd ℂ e e.source) (h0 : e 0 = 0) {z : ℂ} (hz : z ∈ ball 0 1) :
    ‖e z‖ = ‖z‖ := by
  have h0s : (0 : ℂ) ∈ e.source := by rw [hs]; exact mem_ball_self zero_lt_one
  have hi0 : e.symm 0 = 0 := (congrArg e.symm h0.symm).trans (e.left_inv h0s)
  have hm : MapsTo e (ball 0 1) (ball 0 1) := by
    intro w hw
    rw [← ht]
    exact e.map_source (hs.symm ▸ hw)
  have hmi : MapsTo e.symm (ball 0 1) (ball 0 1) := by
    intro w hw
    rw [← hs]
    exact e.map_target (ht.symm ▸ hw)
  have hi := openPartialHomeomorph_analytic_inverse e he
  rw [ht] at hi
  have hf := he
  rw [hs] at hf
  apply le_antisymm (disc_analytic_zero_norm_le e hf hm h0 hz)
  have hback := disc_analytic_zero_norm_le e.symm hi hmi hi0 (hm hz)
  rwa [e.left_inv (hs.symm ▸ hz)] at hback

/-- The exact equality case: every analytic automorphism of the disc fixing zero is a unit rotation. -/
theorem disc_analytic_automorphism_fix_zero_rotation (e : OpenPartialHomeomorph ℂ ℂ)
    (hs : e.source = ball 0 1) (ht : e.target = ball 0 1)
    (he : AnalyticOnNhd ℂ e e.source) (h0 : e 0 = 0) :
    ∃ a : ℂ, ‖a‖ = 1 ∧ EqOn e (fun z => a * z) (ball 0 1) := by
  have hf := he
  rw [hs] at hf
  have hm : MapsTo e (ball 0 1) (closedBall (e 0) 1) := by
    intro z hz
    rw [h0]
    exact ball_subset_closedBall (ht ▸ e.map_source (hs.symm ▸ hz))
  let z₀ : ℂ := 1 / 2
  have hz₀ : z₀ ∈ ball (0 : ℂ) 1 := by norm_num [z₀, mem_ball_zero_iff]
  have hn₀ : z₀ ≠ 0 := by norm_num [z₀]
  have hnorm := disc_analytic_automorphism_zero_norm e hs ht he h0 hz₀
  have hds : ‖dslope e 0 z₀‖ = (1 : ℝ) / 1 := by
    rw [dslope_of_ne _ hn₀, slope_def_module, norm_smul, norm_inv, h0, sub_zero, sub_zero, hnorm]
    rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hn₀)]
    norm_num
  refine ⟨dslope e 0 z₀, by simpa using hds, ?_⟩
  have ha := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hf.differentiableOn hm hz₀ hds
  intro z hz
  simpa only [h0, zero_add, sub_zero, smul_eq_mul, mul_comm] using ha hz

/-- The actual Mobius-group representative of the already proved normalized disc formula. -/
def normalizedDiscMobius (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1) :
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  _root_.LowDimensionalTopology.Geometry.Mobius.mobiusMatrixProjection (_root_.LowDimensionalTopology.Geometry.Mobius.coefficientMatrix a (conj c) c (conj a)
    (by rw [_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractional_determinant hdet]; norm_num))

theorem normalizedDiscMobius_val (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1) :
    (normalizedDiscMobius a c hdet).val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.normalizedDiscTransformation a c hdet := by
  rw [normalizedDiscMobius, _root_.LowDimensionalTopology.Geometry.Mobius.mobiusMatrixProjection_coe]
  rfl

theorem normalizedDiscMobius_preserves_disc (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1) :
    (normalizedDiscMobius a c hdet).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
  rw [normalizedDiscMobius_val]
  exact _root_.LowDimensionalTopology.Geometry.Hyperbolic.normalizedDiscTransformation_preserves_disc a c hdet

/-- Real normalization factor for moving an arbitrary disc point to zero. -/
def discCenterScale (b : ℂ) : ℝ := (Real.sqrt (1 - Complex.normSq b))⁻¹

theorem discCenter_determinant {b : ℂ} (hb : ‖b‖ < 1) :
    Complex.normSq (discCenterScale b : ℂ) -
      Complex.normSq (-conj b * (discCenterScale b : ℂ)) = 1 := by
  have hbn : Complex.normSq b < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg b]
  have hd : 0 < 1 - Complex.normSq b := sub_pos.mpr hbn
  have hs : Real.sqrt (1 - Complex.normSq b) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  rw [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_conj, Complex.normSq_ofReal]
  unfold discCenterScale
  field_simp [hs]
  nlinarith [Real.sq_sqrt hd.le]

theorem discCenter_maps_center_zero {b : ℂ} (_hb : ‖b‖ < 1) :
    _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap (discCenterScale b : ℂ) (-conj b * (discCenterScale b : ℂ)) b = 0 := by
  have hreal : conj (discCenterScale b : ℂ) = (discCenterScale b : ℂ) := by simp
  unfold _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.fractionalLinearMap
  simp only [map_mul, map_neg, Complex.conj_conj, hreal]
  simp [mul_comm]

/-- The normalized fractional formula as an actual open partial homeomorphism of the complex disc. -/
def normalizedDiscChart (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1) :
    OpenPartialHomeomorph ℂ ℂ := by
  let D : TopologicalSpace.Opens ℂ := ⟨ball (0 : ℂ) 1, isOpen_ball⟩
  have hD : Nonempty D := ⟨0, mem_ball_self zero_lt_one⟩
  let E : D ≃ₜ D := _root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hdet
  exact (D.openPartialHomeomorphSubtypeCoe hD).symm.trans
    (E.toOpenPartialHomeomorph.trans (D.openPartialHomeomorphSubtypeCoe hD))

theorem normalizedDiscChart_source (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1) :
    (normalizedDiscChart a c hdet).source = ball 0 1 := by
  simp [normalizedDiscChart]
  intro z _hz
  trivial

theorem normalizedDiscChart_target (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1) :
    (normalizedDiscChart a c hdet).target = ball 0 1 := by
  simp [normalizedDiscChart]
  intro z _hz
  trivial

theorem normalizedDiscChart_apply (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1)
    (z : ball (0 : ℂ) 1) : normalizedDiscChart a c hdet z.val = _root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c z.val := by
  let D : TopologicalSpace.Opens ℂ := ⟨ball (0 : ℂ) 1, isOpen_ball⟩
  have hD : Nonempty D := ⟨0, mem_ball_self zero_lt_one⟩
  have hsub := (D.openPartialHomeomorphSubtypeCoe hD).left_inv (Set.mem_univ z)
  change (D.openPartialHomeomorphSubtypeCoe hD).symm z.val = z at hsub
  change ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.discFractionalHomeomorph a c hdet)
    ((D.openPartialHomeomorphSubtypeCoe hD).symm z.val) : ℂ) = _
  rw [hsub]
  rfl

theorem normalizedDiscChart_analytic (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1) :
    AnalyticOnNhd ℂ (normalizedDiscChart a c hdet) (normalizedDiscChart a c hdet).source := by
  rw [normalizedDiscChart_source]
  have hformula : AnalyticOnNhd ℂ (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractionalMap a c) (ball 0 1) := by
    intro z hz
    exact ((analyticAt_const.mul analyticAt_id).add analyticAt_const).div
      ((analyticAt_const.mul analyticAt_id).add analyticAt_const)
      (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractional_den_ne_zero hdet (mem_ball_zero_iff.mp
        hz).le)
  apply AnalyticOnNhd.congr isOpen_ball hformula
  intro z hz
  exact (normalizedDiscChart_apply a c hdet ⟨z, hz⟩).symm

theorem normalizedDiscChart_actualMobius (a c : ℂ) (hdet : Complex.normSq a - Complex.normSq c = 1)
    (z : ℂ) (hz : z ∈ ball 0 1) :
    (normalizedDiscMobius a c hdet).val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
      (normalizedDiscChart a c hdet z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  rw [normalizedDiscMobius_val,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.normalizedDiscTransformation_of_closedDisc a c z hdet
    (mem_ball_zero_iff.mp hz).le, normalizedDiscChart_apply a c hdet ⟨z, hz⟩]

theorem unitDiscChart_trans_source (e f : OpenPartialHomeomorph ℂ ℂ)
    (hes : e.source = ball 0 1) (het : e.target = ball 0 1) (hfs : f.source = ball 0 1) :
    (e.trans f).source = ball 0 1 := by
  ext z
  change z ∈ e.source ∧ e z ∈ f.source ↔ z ∈ ball 0 1
  constructor
  · exact fun hz => hes ▸ hz.1
  · intro hz
    have hze : z ∈ e.source := hes.symm ▸ hz
    exact ⟨hze, hfs.symm ▸ het ▸ e.map_source hze⟩

theorem unitDiscChart_trans_target (e f : OpenPartialHomeomorph ℂ ℂ)
    (het : e.target = ball 0 1) (hfs : f.source = ball 0 1) (hft : f.target = ball 0 1) :
    (e.trans f).target = ball 0 1 := by
  ext z
  change z ∈ f.target ∧ f.symm z ∈ e.target ↔ z ∈ ball 0 1
  constructor
  · exact fun hz => hft ▸ hz.1
  · intro hz
    have hzf : z ∈ f.target := hft.symm ▸ hz
    exact ⟨hzf, het.symm ▸ hfs ▸ f.map_target hzf⟩

theorem discChart_trans_analytic (e f : OpenPartialHomeomorph ℂ ℂ)
    (he : AnalyticOnNhd ℂ e e.source) (hf : AnalyticOnNhd ℂ f f.source) :
    AnalyticOnNhd ℂ (e.trans f) (e.trans f).source := by
  intro z hz
  exact (hf (e z) hz.2).comp (he z hz.1)

/-- Every genuine analytic automorphism of the unit disc is the restriction of an actual Mobius
transformation preserving that disc. -/
theorem disc_analytic_automorphism_exists_mobius (e : OpenPartialHomeomorph ℂ ℂ)
    (hs : e.source = ball 0 1) (ht : e.target = ball 0 1)
    (he : AnalyticOnNhd ℂ e e.source) :
    ∃ M : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, M.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ∧
      ∀ z ∈ ball (0 : ℂ) 1, M.val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (e z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
  have h0s : (0 : ℂ) ∈ e.source := hs.symm ▸ mem_ball_self zero_lt_one
  let b := e 0
  have hb : ‖b‖ < 1 := mem_ball_zero_iff.mp (ht ▸ e.map_source h0s)
  let a : ℂ := discCenterScale b
  let c : ℂ := -conj b * (discCenterScale b : ℂ)
  have hdet : Complex.normSq a - Complex.normSq c = 1 := discCenter_determinant hb
  let N := normalizedDiscChart a c hdet
  have hNs : N.source = ball 0 1 := normalizedDiscChart_source a c hdet
  have hNt : N.target = ball 0 1 := normalizedDiscChart_target a c hdet
  have hNb : N (e 0) = 0 := by
    rw [normalizedDiscChart_apply a c hdet ⟨e 0, mem_ball_zero_iff.mpr hb⟩]
    exact discCenter_maps_center_zero hb
  obtain ⟨k, hk, hlin⟩ := disc_analytic_automorphism_fix_zero_rotation (e.trans N)
    (unitDiscChart_trans_source e N hs ht hNs) (unitDiscChart_trans_target e N ht hNs hNt)
    (discChart_trans_analytic e N he (normalizedDiscChart_analytic a c hdet)) hNb
  have hkn : k ≠ 0 := by intro hn; rw [hn, norm_zero] at hk; norm_num at hk
  let ku : ℂˣ := Units.mk0 k hkn
  let M := (normalizedDiscMobius a c hdet)⁻¹ * _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling ku
  have hmap (z : ℂ) (hz : z ∈ ball 0 1) : M.val (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = (e z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) := by
    apply (normalizedDiscMobius a c hdet).val.injective
    change (normalizedDiscMobius a c hdet).val
      ((normalizedDiscMobius a c hdet).val.symm ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling ku).val (z
        : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex))) = _
    rw [Equiv.apply_symm_apply, _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_coe,
      normalizedDiscChart_actualMobius a c hdet (e z) (ht ▸ e.map_source (hs.symm ▸ hz))]
    have heq : N (e z) = k * z := hlin hz
    rw [heq]
    rfl
  refine ⟨M, ?_, hmap⟩
  apply Set.Subset.antisymm
  · rintro w ⟨v, ⟨z, hz, rfl⟩, rfl⟩
    rw [hmap z (mem_ball_zero_iff.mpr hz)]
    exact ⟨e z, mem_ball_zero_iff.mp (ht ▸ e.map_source (hs.symm ▸ mem_ball_zero_iff.mpr hz)), rfl⟩
  · rintro w ⟨z, hz, rfl⟩
    have hzT : z ∈ e.target := ht.symm ▸ mem_ball_zero_iff.mpr hz
    have hzI : e.symm z ∈ ball 0 1 := hs ▸ e.map_target hzT
    refine ⟨(e.symm z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), ⟨e.symm z, mem_ball_zero_iff.mp
      hzI, rfl⟩, ?_⟩
    rw [hmap (e.symm z) hzI, e.right_inv hzT]

/-- The genuine extended unit disc with the complex structure inherited from the Riemann sphere. -/
def discRiemannSurface : RiemannSurface _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc :=
  mobiusDomainRiemannSurface (unitDiscMobiusInvariantDomain ⊥ (by
    rintro ⟨g, hg⟩ z hz
    have hg1 : g = 1 := hg
    subst g
    exact hz))

/-- The finite sphere chart restricted to the genuine extended unit disc. -/
def discFiniteChart : OpenPartialHomeomorph _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ℂ := by
  let S : TopologicalSpace.Opens _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc, _root_.LowDimensionalTopology.Geometry.Mobius.isOpen_extendedUnitDisc⟩
  have hS : Nonempty S := ⟨(0 : ℂ), by
    change ((0 : ℂ) : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedUnitDisc]
    norm_num⟩
  exact (S.openPartialHomeomorphSubtypeCoe hS).trans sphereFiniteChart

theorem discFiniteChart_source : discFiniteChart.source = Set.univ := by
  ext z
  change (True ∧ z.val ∈ sphereFiniteChart.source) ↔ True
  rw [sphereFiniteChart_source]
  have hz : z.val ≠ ∞ := by
    intro he
    have hp := z.property
    rw [he] at hp
    exact _root_.LowDimensionalTopology.Geometry.Mobius.infty_not_mem_extendedUnitDisc hp
  simpa using hz

theorem discFiniteChart_target : discFiniteChart.target = ball (0 : ℂ) 1 := by
  ext z
  simp [discFiniteChart, sphereFiniteChart_target, sphereFiniteChart_symm,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedUnitDisc]

theorem discFiniteChart_mem : discFiniteChart ∈ discRiemannSurface.charts := by
  refine ⟨_, rfl, sphereFiniteChart, ?_, rfl⟩
  exact Set.mem_insert _ _

theorem discFiniteChart_coe (z : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) : (discFiniteChart z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = z.val := by
  obtain ⟨w, _hw, hwz⟩ := z.property
  change (sphereFiniteChart z.val : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = z.val
  rw [← hwz, sphereFiniteChart_coe]

/-- Analytic automorphisms in the actual inherited surface structure admit genuine Mobius extensions. -/
theorem discRiemannSurface_automorphism_exists_mobius (H :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ≃ₜ
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hH : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas discRiemannSurface.toRiemannAtlas H) :
    ∃ M : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, M.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ∧
      ∀ z : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc, M.val z.val = (H z).val := by
  let F := riemannHomeomorphChart discFiniteChart H discFiniteChart
  have hs : F.source = ball (0 : ℂ) 1 := by
    rw [riemannHomeomorphChart_source]
    simp [riemannChartMapDomain, discFiniteChart_source, discFiniteChart_target]
  have ht : F.target = ball (0 : ℂ) 1 := by
    rw [riemannHomeomorphChart_target]
    simp [riemannChartMapDomain, discFiniteChart_source, discFiniteChart_target]
  have hF : AnalyticOnNhd ℂ F F.source := by
    rw [show F.source = riemannChartMapDomain discFiniteChart H discFiniteChart from
      riemannHomeomorphChart_source _ _ _]
    exact hH.2 discFiniteChart discFiniteChart_mem discFiniteChart discFiniteChart_mem
  obtain ⟨M, hM, hEq⟩ := disc_analytic_automorphism_exists_mobius F hs ht hF
  refine ⟨M, hM, ?_⟩
  intro z
  have hz : z ∈ discFiniteChart.source := discFiniteChart_source.symm ▸ Set.mem_univ z
  have heq := hEq (discFiniteChart z) (discFiniteChart_target ▸ discFiniteChart.map_source hz)
  change M.val (discFiniteChart z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) =
    (discFiniteChart (H (discFiniteChart.symm (discFiniteChart z))) :
      _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) at heq
  rw [discFiniteChart.left_inv hz, discFiniteChart_coe, discFiniteChart_coe] at heq
  exact heq

/-- Agreement on the genuine unit disc determines an actual Mobius transformation uniquely. -/
theorem mobius_eq_of_agree_extendedUnitDisc (M N : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (h : ∀ z : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc, M.val z.val = N.val z.val) : M = N := by
  let a : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := ⟨((0 : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedUnitDisc 0).mpr (by norm_num)⟩
  let b : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := ⟨((1 / 2 : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedUnitDisc _).mpr (by norm_num)⟩
  let c : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := ⟨((-1 / 2 : ℂ) :
    _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex),
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedUnitDisc _).mpr (by norm_num)⟩
  apply _root_.LowDimensionalTopology.Geometry.Mobius.mobius_eq_of_agree_triple M N a.val b.val c.val _ (h a) (h b) (h
    c)
  refine ⟨?_, ?_, ?_⟩
  all_goals
    intro he
    have hh := OnePoint.coe_injective he
    norm_num [a, b, c] at hh

/-- The inherited disc surface has a unique actual Mobius extension for each analytic automorphism. -/
theorem discRiemannSurface_automorphism_existsUnique_mobius (H :
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ≃ₜ
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hH : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas discRiemannSurface.toRiemannAtlas H) :
    ∃! M : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, M.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ∧
      ∀ z : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc, M.val z.val = (H z).val := by
  obtain ⟨M, hM, hEq⟩ := discRiemannSurface_automorphism_exists_mobius H hH
  refine ⟨M, ⟨hM, hEq⟩, ?_⟩
  intro N hN
  exact mobius_eq_of_agree_extendedUnitDisc N M (fun z => (hN.2 z).trans (hEq z).symm)

/-- The unique actual Mobius transformation representing an analytic disc automorphism. -/
def discAnalyticAutomorphismMobius (H : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ≃ₜ
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hH : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas discRiemannSurface.toRiemannAtlas H) :
    _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup := (discRiemannSurface_automorphism_exists_mobius H
      hH).choose

theorem discAnalyticAutomorphismMobius_preserves (H : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
  ≃ₜ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hH : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas discRiemannSurface.toRiemannAtlas H) :
    (discAnalyticAutomorphismMobius H hH).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc :=
  (discRiemannSurface_automorphism_exists_mobius H hH).choose_spec.1

theorem discAnalyticAutomorphismMobius_apply (H : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ≃ₜ
  _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hH : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas discRiemannSurface.toRiemannAtlas H)
    (z : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) : (discAnalyticAutomorphismMobius H
      hH).val z.val = (H z).val :=
  (discRiemannSurface_automorphism_exists_mobius H hH).choose_spec.2 z

/-- Every analytic action on the genuine disc determines an actual Mobius group homomorphism. -/
def discAnalyticActionMobiusHom {G : Type*} [Group G]
    (ρ : G →* (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ≃ₜ
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc))
    (ha : ∀ g, RiemannAnalyticMap discRiemannSurface.toRiemannAtlas
      discRiemannSurface.toRiemannAtlas (ρ
        g)) : G →* _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup where
  toFun g := discAnalyticAutomorphismMobius (ρ g) (ha g)
  map_one' := by
    apply mobius_eq_of_agree_extendedUnitDisc
    intro z
    rw [discAnalyticAutomorphismMobius_apply, map_one]
    rfl
  map_mul' g h := by
    apply mobius_eq_of_agree_extendedUnitDisc
    intro z
    rw [discAnalyticAutomorphismMobius_apply, map_mul]
    change ((ρ g) ((ρ h) z)).val =
      (discAnalyticAutomorphismMobius (ρ g) (ha g)).val
        ((discAnalyticAutomorphismMobius (ρ h) (ha h)).val z.val)
    rw [discAnalyticAutomorphismMobius_apply, discAnalyticAutomorphismMobius_apply]

theorem discAnalyticActionMobiusHom_injective {G : Type*} [Group G]
    (ρ : G →* (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ≃ₜ
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc))
    (ha : ∀ g, RiemannAnalyticMap discRiemannSurface.toRiemannAtlas
      discRiemannSurface.toRiemannAtlas (ρ g))
    (hρ : Function.Injective ρ) : Function.Injective (discAnalyticActionMobiusHom ρ ha) := by
  intro g h he
  apply hρ
  apply Homeomorph.ext
  intro z
  apply Subtype.ext
  have hv := congrArg (fun M : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup => M.val z.val) he
  change (discAnalyticAutomorphismMobius (ρ g) (ha g)).val z.val =
    (discAnalyticAutomorphismMobius (ρ h) (ha h)).val z.val at hv
  simpa only [discAnalyticAutomorphismMobius_apply] using hv

end LowDimensionalTopology.Geometry.Surfaces
