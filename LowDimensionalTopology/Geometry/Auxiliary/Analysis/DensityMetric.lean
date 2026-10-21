/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.Conformal
public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Densities and path metrics
-/

@[expose] public section

open Set Filter MeasureTheory Bundle Bornology Manifold Asymptotics
open scoped Topology ENNReal ContDiff

namespace LowDimensionalTopology.Geometry.Auxiliary.Analysis

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


structure Density (D : TopologicalSpace.Opens E) where
  toFun : D → ℝ
  continuous : Continuous toFun
  positive : ∀ x, 0 < toFun x

instance {D : TopologicalSpace.Opens E} : CoeFun (Density D) (fun _ => D → ℝ) :=
  ⟨Density.toFun⟩


omit [InnerProductSpace ℝ E] in
theorem openDomain_chart_source (D : TopologicalSpace.Opens E) (x y : D) :
    y ∈ (chartAt E x).source := by
  simp [TopologicalSpace.Opens.chartAt_eq, mfld_simps]

theorem openDomain_tangent_trivialization (D : TopologicalSpace.Opens E) (x y : D) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).continuousLinearMapAt ℝ y =
      (tangentSpaceCastModel 𝓘(ℝ, E) y).toContinuousLinearMap := by
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (openDomain_chart_source D x y)]
  simp only [tangentBundleCore_coordChange, mfld_simps]
  have h := (TopologicalSpace.Opens.chartAt_subtype_val_symm_eventuallyEq
    (H := E) D (x := y)).symm
  ext v
  have hh := congrArg (fun A : E →L[ℝ] E => A v) (h.fderiv_eq (𝕜 := ℝ))
  simpa [TopologicalSpace.Opens.chartAt_eq, mfld_simps, Function.comp_def,
    Set.domRestrict, tangentSpaceCastModel] using hh

theorem openDomain_tangent_inverse_trivialization (D : TopologicalSpace.Opens E) (x y : D) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).symmL ℝ y =
      (tangentSpaceCastModel 𝓘(ℝ, E) y).symm.toContinuousLinearMap := by
  rw [TangentBundle.symmL_trivializationAt_eq_core (openDomain_chart_source D x y)]
  simp only [tangentBundleCore_coordChange, mfld_simps]
  have hy : (y : E) ∈ (D : Set E) := y.property
  have heq : (Subtype.val ∘ (chartAt E x).symm) =ᶠ[𝓝 (y : E)] id := by
    filter_upwards [D.isOpen.mem_nhds hy] with z hz
    have hzt : z ∈ (chartAt E x).target := by
      exact (OpenPartialHomeomorph.refl E).map_subtype_source ⟨x⟩
        (x := ⟨z, hz⟩) (by simp)
    exact (chartAt E x).right_inv hzt
  ext v
  change _ = v
  have hh := congrArg (fun A : E →L[ℝ] E => A v) (heq.fderiv_eq (𝕜 := ℝ))
  simpa [TopologicalSpace.Opens.chartAt_eq, mfld_simps, Function.comp_def,
    Set.domRestrict, tangentSpaceCastModel] using hh

theorem openDomain_tangent_inverse_apply (D : TopologicalSpace.Opens E) (x y : D) (v : E) :
    (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x).symm y v =
      (tangentSpaceCastModel 𝓘(ℝ, E) y).symm v := by
  rw [← Trivialization.symmL_apply (R := ℝ) _ (openDomain_chart_source D x y) v,
    openDomain_tangent_inverse_trivialization]
  rfl

set_option backward.isDefEq.respectTransparency true

section TangentModel

def Density.riemannianMetric {D : TopologicalSpace.Opens E} (ρ : Density D) :
    ContinuousRiemannianMetric E (fun x : D => TangentSpace 𝓘(ℝ, E) x) where
  inner x := by
    letI : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x) :=
      inferInstanceAs (NormedAddCommGroup E)
    letI : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
      inferInstanceAs (NormedSpace ℝ E)
    letI : IsNormableSpace ℝ (TangentSpace 𝓘(ℝ, E) x) :=
      inferInstanceAs (IsNormableSpace ℝ E)
    exact (ρ x) ^ 2 • (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).bilinearComp
      (tangentSpaceCastModel 𝓘(ℝ, E) x).toContinuousLinearMap
      (tangentSpaceCastModel 𝓘(ℝ, E) x).toContinuousLinearMap
  symm x v w := by
    simp only [smul_apply, ContinuousLinearMap.bilinearComp_apply,
      innerSL_apply_apply, smul_eq_mul, real_inner_comm]
  pos x v hv := by
    change 0 < (ρ x) ^ 2 * inner ℝ ((tangentSpaceCastModel 𝓘(ℝ, E) x) v)
      ((tangentSpaceCastModel 𝓘(ℝ, E) x) v)
    exact mul_pos (sq_pos_of_pos (ρ.positive x))
      (real_inner_self_pos.mpr (by simpa using hv))
  isVonNBounded x := by
    change IsVonNBounded ℝ {v : E | (ρ x) ^ 2 * inner ℝ v v < 1}
    apply (NormedSpace.isVonNBounded_ball ℝ E ((ρ x)⁻¹)).subset
    intro v hv
    simp only [Metric.mem_ball, dist_zero_right]
    change (ρ x) ^ 2 * inner ℝ v v < 1 at hv
    rw [real_inner_self_eq_norm_sq] at hv
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ (ρ.positive x)).mpr
    nlinarith [norm_nonneg v]
  continuous := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [continuousAt_hom_bundle]
    refine ⟨continuousAt_id, ?_⟩
    have hi : ContinuousAt (fun _ : D => (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)) x :=
      continuousAt_const
    have hc : ContinuousAt (fun y : D => (ρ y) ^ 2 • (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ)) x :=
      ContinuousAt.smul (M := ℝ) (X := E →L[ℝ] E →L[ℝ] ℝ) (Y := D)
        (ρ.continuous.continuousAt.pow 2) hi
    convert hc using 1
    · rfl
    ext y v w
    rw [inCoordinates_apply_eq₂]
    · simp [openDomain_tangent_inverse_apply, ContinuousLinearMap.bilinearComp_apply]
      exact Or.inl rfl
    · exact openDomain_chart_source D x y
    · exact openDomain_chart_source D x y
    · simp

end TangentModel

section ConnectedEMetric

variable {X : Type*} [EMetricSpace X] [PreconnectedSpace X]

theorem connected_edist_ne_top (x y : X) : edist x y ≠ ⊤ := by
  have heq : Metric.eball x (⊤ : ℝ≥0∞) = Set.univ :=
    (show IsClopen (Metric.eball x (⊤ : ℝ≥0∞)) from
      ⟨Metric.isClosed_eball_top, Metric.isOpen_eball⟩).eq_univ ⟨x, by simp⟩
  have hy : y ∈ Metric.eball x (⊤ : ℝ≥0∞) := by rw [heq]; trivial
  exact (by simpa only [Metric.mem_eball, edist_comm] using hy : edist x y < ⊤).ne

@[instance_reducible]
def connectedEMetricToMetric (X : Type*) [EMetricSpace X] [PreconnectedSpace X] :
    MetricSpace X := EMetricSpace.toMetricSpace connected_edist_ne_top

end ConnectedEMetric

section GenericRiemannianChains

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ F H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]

/-- A finite concatenation of continuously differentiable curve pieces. -/
inductive RiemannianC1Chain : M → M → Type _ where
  | nil (x : M) : RiemannianC1Chain x x
  | cons {x y z : M} (γ : ℝ → M) (a b : ℝ) (hab : a ≤ b)
      (hc : CMDiff[Icc a b] 1 γ) (ha : γ a = x) (hb : γ b = y)
      (tail : RiemannianC1Chain y z) : RiemannianC1Chain x z

variable {I M} [∀ x : M, ENorm (TangentSpace I x)]
    [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]

def RiemannianC1Chain.length {x y : M} : RiemannianC1Chain I M x y → ℝ≥0∞
  | .nil _ => 0
  | .cons γ a b _ _ _ _ tail => pathELength I γ a b + tail.length

theorem RiemannianC1Chain.edist_le_length {x y : M} (c : RiemannianC1Chain I M x y) :
    riemannianEDist I x y ≤ c.length := by
  induction c with
  | nil x => simp [RiemannianC1Chain.length, riemannianEDist_self]
  | @cons x y z γ a b hab hc ha hb tail ih =>
      exact (riemannianEDist_triangle (I := I) (x := x) (y := y) (z := z)).trans
        (add_le_add (riemannianEDist_le_pathELength hc ha hb hab) ih)

def piecewiseC1EDist (x y : M) : ℝ≥0∞ := ⨅ c : RiemannianC1Chain I M x y, c.length

theorem piecewiseC1EDist_eq_riemannianEDist (x y : M) :
    piecewiseC1EDist (I := I) x y = riemannianEDist I x y := by
  apply le_antisymm
  · apply le_of_forall_gt
    intro r hr
    obtain ⟨γ, hx, hy, hc, hlen⟩ := exists_lt_of_riemannianEDist_lt hr
    let c : RiemannianC1Chain I M x y := .cons γ 0 1 zero_le_one hc hx hy (.nil y)
    have hle : piecewiseC1EDist (I := I) x y ≤ c.length := iInf_le _ c
    exact hle.trans_lt (by simpa [c, RiemannianC1Chain.length] using hlen)
  · exact le_iInf fun c => c.edist_le_length

end GenericRiemannianChains

section DensityPathMetric

@[instance_reducible]
def Density.eMetricSpace {D : TopologicalSpace.Opens E} (ρ : Density D) : EMetricSpace D :=
  letI : RiemannianBundle (fun x : D => TangentSpace 𝓘(ℝ, E) x) :=
    ⟨ρ.riemannianMetric.toRiemannianMetric⟩
  EMetricSpace.ofRiemannianMetric 𝓘(ℝ, E) D

theorem Density.eMetricSpace_topology {D : TopologicalSpace.Opens E} (ρ : Density D) :
    ρ.eMetricSpace.toPseudoEMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace D) := rfl

theorem Density.tangent_norm {D : TopologicalSpace.Opens E} (ρ : Density D)
    (x : D) (v : TangentSpace 𝓘(ℝ, E) x) :
    letI : RiemannianBundle (fun y : D => TangentSpace 𝓘(ℝ, E) y) :=
      ⟨ρ.riemannianMetric.toRiemannianMetric⟩
    ‖v‖ = ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖ := by
  let : RiemannianBundle (fun y : D => TangentSpace 𝓘(ℝ, E) y) :=
    ⟨ρ.riemannianMetric.toRiemannianMetric⟩
  rw [norm_eq_sqrt_real_inner]
  change Real.sqrt ((ρ x) ^ 2 * inner ℝ ((tangentSpaceCastModel 𝓘(ℝ, E) x) v)
    ((tangentSpaceCastModel 𝓘(ℝ, E) x) v)) = _
  rw [real_inner_self_eq_norm_sq, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (ρ.positive x).le, Real.sqrt_sq (norm_nonneg _)]


def Density.pieceLength {D : TopologicalSpace.Opens E} (ρ : Density D)
    (γ : ℝ → D) (a b : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Icc a b, ENNReal.ofReal (ρ (γ t) *
    ‖(tangentSpaceCastModel 𝓘(ℝ, E) (γ t)) (mfderiv[Icc a b] γ t 1)‖)

theorem Density.pieceLength_eq_pathELength {D : TopologicalSpace.Opens E} (ρ : Density D)
    (γ : ℝ → D) (a b : ℝ) :
    letI : RiemannianBundle (fun y : D => TangentSpace 𝓘(ℝ, E) y) :=
      ⟨ρ.riemannianMetric.toRiemannianMetric⟩
    ρ.pieceLength γ a b = Manifold.pathELength 𝓘(ℝ, E) γ a b := by
  let : RiemannianBundle (fun y : D => TangentSpace 𝓘(ℝ, E) y) :=
    ⟨ρ.riemannianMetric.toRiemannianMetric⟩
  rw [Density.pieceLength, pathELength_eq_lintegral_mfderivWithin_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t _
  dsimp only
  rw [← ofReal_norm, ρ.tangent_norm]


def Density.pathEDist {D : TopologicalSpace.Opens E} (ρ : Density D) (x y : D) : ℝ≥0∞ :=
  letI : RiemannianBundle (fun z : D => TangentSpace 𝓘(ℝ, E) z) :=
    ⟨ρ.riemannianMetric.toRiemannianMetric⟩
  riemannianEDist 𝓘(ℝ, E) x y

theorem Density.pathEDist_eq_edist {D : TopologicalSpace.Opens E} (ρ : Density D)
    (x y : D) :
    ρ.pathEDist x y = @edist D ρ.eMetricSpace.toEDist x y := rfl

@[instance_reducible]
def Density.metricSpace {D : TopologicalSpace.Opens E} [PreconnectedSpace D]
    (ρ : Density D) : MetricSpace D :=
  letI : EMetricSpace D := ρ.eMetricSpace
  connectedEMetricToMetric D

theorem Density.metricSpace_topology {D : TopologicalSpace.Opens E} [PreconnectedSpace D]
    (ρ : Density D) :
    ρ.metricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace D) := rfl


def Density.pathDist {D : TopologicalSpace.Opens E} (ρ : Density D) (x y : D) : ℝ :=
  (ρ.pathEDist x y).toReal

theorem Density.pathDist_eq_dist {D : TopologicalSpace.Opens E} [PreconnectedSpace D]
    (ρ : Density D) (x y : D) :
    ρ.pathDist x y = @dist D ρ.metricSpace.toDist x y := rfl

theorem Density.pathEDist_ne_top {D : TopologicalSpace.Opens E} [PreconnectedSpace D]
    (ρ : Density D) (x y : D) : ρ.pathEDist x y ≠ ⊤ := by
  exact @connected_edist_ne_top D ρ.eMetricSpace inferInstance x y

theorem Density.pathDist_pos {D : TopologicalSpace.Opens E} [PreconnectedSpace D]
    (ρ : Density D) {x y : D} (hxy : x ≠ y) : 0 < ρ.pathDist x y := by
  rw [ρ.pathDist_eq_dist]
  exact (@dist_pos D ρ.metricSpace x y).mpr hxy

theorem Density.pathDist_triangle {D : TopologicalSpace.Opens E} [PreconnectedSpace D]
    (ρ : Density D) (x y z : D) : ρ.pathDist x z ≤ ρ.pathDist x y + ρ.pathDist y z := by
  simp only [ρ.pathDist_eq_dist]
  exact @dist_triangle D ρ.metricSpace.toPseudoMetricSpace x y z


def Density.chainLength {D : TopologicalSpace.Opens E} (ρ : Density D) {x y : D} :
    RiemannianC1Chain 𝓘(ℝ, E) D x y → ℝ≥0∞
  | .nil _ => 0
  | .cons γ a b _ _ _ _ tail => ρ.pieceLength γ a b + ρ.chainLength tail

theorem Density.chainLength_eq_length {D : TopologicalSpace.Opens E} (ρ : Density D)
    {x y : D} (c : RiemannianC1Chain 𝓘(ℝ, E) D x y) :
    letI : RiemannianBundle (fun z : D => TangentSpace 𝓘(ℝ, E) z) :=
      ⟨ρ.riemannianMetric.toRiemannianMetric⟩
    ρ.chainLength c = c.length := by
  let : RiemannianBundle (fun z : D => TangentSpace 𝓘(ℝ, E) z) :=
    ⟨ρ.riemannianMetric.toRiemannianMetric⟩
  induction c with
  | nil x => rfl
  | cons γ a b hab hc ha hb tail ih =>
      simp only [Density.chainLength, RiemannianC1Chain.length,
        ρ.pieceLength_eq_pathELength, ih]

def Density.piecewiseEDist {D : TopologicalSpace.Opens E} (ρ : Density D) (x y : D) : ℝ≥0∞ :=
  ⨅ c : RiemannianC1Chain 𝓘(ℝ, E) D x y, ρ.chainLength c

theorem Density.pathEDist_eq_piecewiseEDist {D : TopologicalSpace.Opens E} (ρ : Density D)
    (x y : D) : ρ.pathEDist x y = ρ.piecewiseEDist x y := by
  let : RiemannianBundle (fun z : D => TangentSpace 𝓘(ℝ, E) z) :=
    ⟨ρ.riemannianMetric.toRiemannianMetric⟩
  unfold Density.pathEDist Density.piecewiseEDist
  simp_rw [ρ.chainLength_eq_length]
  exact (piecewiseC1EDist_eq_riemannianEDist x y).symm

theorem openDomain_mfderivWithin_apply (D : TopologicalSpace.Opens E) (γ : ℝ → D)
    (s : Set ℝ) (t v : ℝ) (hγ : MDifferentiableWithinAt 𝓘(ℝ) 𝓘(ℝ, E) γ s t) :
    (tangentSpaceCastModel 𝓘(ℝ, E) (γ t))
      (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) γ s t v) =
      (fderivWithin ℝ (fun u => (γ u : E)) s t) v := by
  simp only [mfderivWithin, hγ, ite_true]
  simp only [writtenInExtChartAt, TopologicalSpace.Opens.chartAt_eq, mfld_simps]
  rfl


theorem openDomain_contDiffOn_ambient {D : TopologicalSpace.Opens E} {γ : ℝ → D}
    {s : Set ℝ} (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 γ s) :
    ContDiffOn ℝ 1 (fun t => (γ t : E)) s := by
  rw [← contMDiffOn_iff_contDiffOn]
  exact contMDiff_subtype_val.comp_contMDiffOn hγ

theorem Density.pieceLength_eq_lintegral {D : TopologicalSpace.Opens E} (ρ : Density D)
    (γ : ℝ → D) (a b : ℝ) (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 γ (Icc a b)) :
    ρ.pieceLength γ a b = ∫⁻ t in Icc a b, ENNReal.ofReal (ρ (γ t) *
      ‖derivWithin (fun u => (γ u : E)) (Icc a b) t‖) := by
  unfold Density.pieceLength
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  exact congrArg (fun v : E => ENNReal.ofReal (ρ (γ t) * ‖v‖))
    ((openDomain_mfderivWithin_apply D γ (Icc a b) t 1
      (hγ.mdifferentiableOn one_ne_zero t ht)).trans fderivWithin_derivWithin)

theorem Density.pieceLength_eq_ofReal_integral {D : TopologicalSpace.Opens E} (ρ : Density D)
    (γ : ℝ → D) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 γ (Icc a b)) :
    ρ.pieceLength γ a b = ENNReal.ofReal (∫ t in a..b, ρ (γ t) *
      ‖derivWithin (fun u => (γ u : E)) (Icc a b) t‖) := by
  rw [ρ.pieceLength_eq_lintegral γ a b hγ]
  rcases hab.eq_or_lt with rfl | hab
  · simp
  have hc : ContinuousOn (fun t => ρ (γ t) *
      ‖derivWithin (fun u => (γ u : E)) (Icc a b) t‖) (Icc a b) :=
    (ρ.continuous.comp_continuousOn hγ.continuousOn).mul
      ((openDomain_contDiffOn_ambient hγ).continuousOn_derivWithin
        (uniqueDiffOn_Icc hab) le_rfl).norm
  rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc]
  symm
  exact ofReal_integral_eq_lintegral_ofReal hc.integrableOn_Icc
    (Filter.Eventually.of_forall fun t => mul_nonneg (ρ.positive (γ t)).le (norm_nonneg _))

theorem Density.pieceLength_ne_top {D : TopologicalSpace.Opens E} (ρ : Density D)
    (γ : ℝ → D) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 γ (Icc a b)) :
    ρ.pieceLength γ a b ≠ ⊤ := by
  rw [ρ.pieceLength_eq_ofReal_integral γ a b hab hγ]
  exact ENNReal.ofReal_ne_top

theorem Density.chainLength_ne_top {D : TopologicalSpace.Opens E} (ρ : Density D)
    {x y : D} (c : RiemannianC1Chain 𝓘(ℝ, E) D x y) : ρ.chainLength c ≠ ⊤ := by
  induction c with
  | nil x => simp [Density.chainLength]
  | cons γ a b hab hc ha hb tail ih =>
      simp only [Density.chainLength, ENNReal.add_ne_top]
      exact ⟨ρ.pieceLength_ne_top γ a b hab hc, ih⟩


theorem Density.pathDist_eq_sInf_chain_lengths {D : TopologicalSpace.Opens E}
    [PreconnectedSpace D] (ρ : Density D) (x y : D) :
    ρ.pathDist x y = sInf (Set.range (fun c : RiemannianC1Chain 𝓘(ℝ, E) D x y =>
      (ρ.chainLength c).toReal)) := by
  have hbound : BddBelow (Set.range (fun c : RiemannianC1Chain 𝓘(ℝ, E) D x y =>
      (ρ.chainLength c).toReal)) :=
    ⟨0, by rintro _ ⟨c, rfl⟩; exact ENNReal.toReal_nonneg⟩
  have happrox {r : ℝ} (hr : ρ.pathDist x y < r) :
      ∃ c : RiemannianC1Chain 𝓘(ℝ, E) D x y, (ρ.chainLength c).toReal < r := by
    have he : ρ.pathEDist x y < ENNReal.ofReal r :=
      (ENNReal.lt_ofReal_iff_toReal_lt (ρ.pathEDist_ne_top x y)).mpr hr
    rw [ρ.pathEDist_eq_piecewiseEDist, Density.piecewiseEDist, iInf_lt_iff] at he
    obtain ⟨c, hc⟩ := he
    exact ⟨c, (ENNReal.lt_ofReal_iff_toReal_lt (ρ.chainLength_ne_top c)).mp hc⟩
  have hnonempty : (Set.range (fun c : RiemannianC1Chain 𝓘(ℝ, E) D x y =>
      (ρ.chainLength c).toReal)).Nonempty := by
    obtain ⟨c, _⟩ := happrox (show ρ.pathDist x y < ρ.pathDist x y + 1 by linarith)
    exact ⟨_, c, rfl⟩
  apply le_antisymm
  · apply le_csInf hnonempty
    rintro _ ⟨c, rfl⟩
    apply ENNReal.toReal_mono (ρ.chainLength_ne_top c)
    rw [ρ.pathEDist_eq_piecewiseEDist, Density.piecewiseEDist]
    exact iInf_le _ c
  · apply le_of_forall_gt
    intro r hr
    obtain ⟨c, hc⟩ := happrox hr
    exact (csInf_le hbound (Set.mem_range_self c)).trans_lt hc

end DensityPathMetric

section TransportedDensity

variable {D D' : TopologicalSpace.Opens E}


def Density.transportedFunction (ρ : Density D) (f : D ≃ D') (μ : D → ℝ) : D' → ℝ :=
  fun y => ρ (f.symm y) / μ (f.symm y)

omit [InnerProductSpace ℝ E] in
theorem Density.transportedFunction_continuous_iff (ρ : Density D)
    (f : D ≃ₜ D') (μ : D → ℝ) (hμ : ∀ x, 0 < μ x) :
    Continuous (ρ.transportedFunction f.toEquiv μ) ↔ Continuous μ := by
  constructor
  · intro hs
    have hcomp : Continuous (fun x : D => (ρ.transportedFunction f.toEquiv μ) (f x)) :=
      hs.comp f.continuous
    have hnz (x : D) : (ρ.transportedFunction f.toEquiv μ) (f x) ≠ 0 := by
      simpa [Density.transportedFunction] using (div_pos (ρ.positive x) (hμ x)).ne'
    have hc := ρ.continuous.div hcomp hnz
    convert hc using 1
    funext x
    simp [Density.transportedFunction, (ρ.positive x).ne']
  · intro hc
    change Continuous (fun y : D' => ρ (f.symm y) / μ (f.symm y))
    exact (ρ.continuous.comp f.symm.continuous).div (hc.comp f.symm.continuous)
      (fun y => (hμ (f.symm y)).ne')

def Density.transport (ρ : Density D) (f : D ≃ₜ D') (μ : D → ℝ)
    (hμc : Continuous μ) (hμ : ∀ x, 0 < μ x) : Density D' where
  toFun := ρ.transportedFunction f.toEquiv μ
  continuous := (ρ.transportedFunction_continuous_iff f μ hμ).mpr hμc
  positive y := div_pos (ρ.positive (f.symm y)) (hμ (f.symm y))

omit [InnerProductSpace ℝ E] in
theorem Density.transport_apply (ρ : Density D) (f : D ≃ₜ D') (μ : D → ℝ)
    (hμc : Continuous μ) (hμ : ∀ x, 0 < μ x) (x : D) :
    ρ.transport f μ hμc hμ (f x) = ρ x / μ x := by
  simp [Density.transport, Density.transportedFunction]

omit [InnerProductSpace ℝ E] in
theorem Density.transport_covariance (ρ : Density D) (f : D ≃ₜ D') (μ : D → ℝ)
    (hμc : Continuous μ) (hμ : ∀ x, 0 < μ x) (x : D) :
    ρ.transport f μ hμc hμ (f x) * μ x = ρ x := by
  rw [ρ.transport_apply, div_mul_cancel₀ _ (hμ x).ne']

omit [InnerProductSpace ℝ E] in
theorem Density.transport_weighted_norm (ρ : Density D) (f : D ≃ₜ D') (μ : D → ℝ)
    (hμc : Continuous μ) (hμ : ∀ x, 0 < μ x) (x : D) (v w : E)
    (hscale : ‖w‖ = μ x * ‖v‖) :
    ρ.transport f μ hμc hμ (f x) * ‖w‖ = ρ x * ‖v‖ := by
  rw [hscale, ← mul_assoc, ρ.transport_covariance]

omit [InnerProductSpace ℝ E] in
theorem Density.continuous_scale_of_covariance (ρ : Density D) (σ : Density D')
    (f : D ≃ₜ D') (μ : D → ℝ) (hcov : ∀ x, σ (f x) * μ x = ρ x) : Continuous μ := by
  have heq : μ = fun x => ρ x / σ (f x) := by
    funext x
    exact (eq_div_iff (σ.positive (f x)).ne').mpr (by simpa [mul_comm] using hcov x)
  rw [heq]
  exact ρ.continuous.div (σ.continuous.comp f.continuous)
    (fun x => (σ.positive (f x)).ne')

end TransportedDensity

section DensityTransport

variable {D D' : TopologicalSpace.Opens E}

/-- Postcomposition sends finite C¹ chains to finite C¹ chains. -/
def RiemannianC1Chain.map (f : D → D')
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 f) {x y : D} :
    RiemannianC1Chain 𝓘(ℝ, E) D x y →
      RiemannianC1Chain 𝓘(ℝ, E) D' (f x) (f y)
  | .nil x => .nil (f x)
  | .cons γ a b hab hc ha hb tail =>
      .cons (f ∘ γ) a b hab (hf.comp_contMDiffOn hc)
        (congrArg f ha) (congrArg f hb) (tail.map f hf)

/-- A weighted tangent norm identity preserves every C¹ piece length. -/
theorem Density.pieceLength_comp {ρ : Density D} {σ : Density D'} {f : D → D'}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 f)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (f x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (f x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (γ : ℝ → D) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 γ (Icc a b)) :
    σ.pieceLength (f ∘ γ) a b = ρ.pieceLength γ a b := by
  rcases hab.eq_or_lt with rfl | hab
  · simp [Density.pieceLength]
  unfold Density.pieceLength
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [mfderiv_comp_mfderivWithin t
    (hf.mdifferentiable one_ne_zero (γ t))
    (hγ.mdifferentiableOn one_ne_zero t ht)
    (uniqueMDiffWithinAt_iff_uniqueDiffWithinAt.mpr (uniqueDiffOn_Icc hab t ht))]
  exact congrArg ENNReal.ofReal (hscale (γ t) _)

/-- The same covariance preserves the sum of the weighted lengths of all pieces. -/
theorem Density.chainLength_map {ρ : Density D} {σ : Density D'} {f : D → D'}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 f)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (f x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (f x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    {x y : D} (c : RiemannianC1Chain 𝓘(ℝ, E) D x y) :
    σ.chainLength (c.map f hf) = ρ.chainLength c := by
  induction c with
  | nil x => rfl
  | cons γ a b hab hc ha hb tail ih =>
      simp only [RiemannianC1Chain.map, Density.chainLength,
        Density.pieceLength_comp hf hscale γ a b hab hc, ih]

/-- Taking the infimum over mapped chains gives one distance inequality. -/
theorem Density.pathEDist_comp_le {ρ : Density D} {σ : Density D'} {f : D → D'}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 f)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (f x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (f x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (x y : D) : σ.pathEDist (f x) (f y) ≤ ρ.pathEDist x y := by
  rw [ρ.pathEDist_eq_piecewiseEDist, σ.pathEDist_eq_piecewiseEDist]
  unfold Density.piecewiseEDist
  apply le_iInf
  intro c
  calc
    ⨅ d : RiemannianC1Chain 𝓘(ℝ, E) D' (f x) (f y), σ.chainLength d
      ≤ σ.chainLength (c.map f hf) := iInf_le _ _
    _ = ρ.chainLength c := Density.chainLength_map hf hscale c


/-- The inverse weighted tangent identity follows from the forward identity. -/
theorem Density.inverse_tangent_covariance {ρ : Density D} {σ : Density D'}
    (e : D ≃ₜ D')
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e)
    (hei : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e.symm)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (e x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (y : D') (w : TangentSpace 𝓘(ℝ, E) y) :
    ρ (e.symm y) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e.symm y))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y w)‖ =
    σ y * ‖(tangentSpaceCastModel 𝓘(ℝ, E) y) w‖ := by
  have hcomp : (e ∘ e.symm : D' → D') = id := funext e.apply_symm_apply
  have hd := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, E)) y
    (he.mdifferentiable one_ne_zero (e.symm y))
    (hei.mdifferentiable one_ne_zero y)
  rw [hcomp, mfderiv_id] at hd
  have hv := congrArg (fun A : E →L[ℝ] E => A w) hd
  have hn : ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e (e.symm y)))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e (e.symm y)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y w))‖ =
      ‖(tangentSpaceCastModel 𝓘(ℝ, E) y) w‖ := by
    exact congrArg norm hv.symm
  have hs := (hscale (e.symm y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y w)).symm
  rw [hn, e.apply_symm_apply] at hs
  exact hs

/-- A C¹ homeomorphism with C¹ inverse and weighted tangent covariance preserves distance. -/
theorem Density.pathEDist_homeomorph {ρ : Density D} {σ : Density D'}
    (e : D ≃ₜ D')
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e)
    (hei : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e.symm)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (e x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (x y : D) : σ.pathEDist (e x) (e y) = ρ.pathEDist x y := by
  apply le_antisymm (Density.pathEDist_comp_le he hscale x y)
  simpa only [e.symm_apply_apply] using
    (Density.pathEDist_comp_le hei (Density.inverse_tangent_covariance e he hei hscale)
      (e x) (e y))

/-- The preceding equality is an isometry for the density-induced extended metrics. -/
theorem Density.isometry_homeomorph {ρ : Density D} {σ : Density D'}
    (e : D ≃ₜ D')
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e)
    (hei : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e.symm)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (e x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖) :
    @Isometry D D' ρ.eMetricSpace.toPseudoEMetricSpace
      σ.eMetricSpace.toPseudoEMetricSpace e := by
  intro x y
  simpa only [Density.pathEDist_eq_edist] using
    (Density.pathEDist_homeomorph e he hei hscale x y)

/-- Taking real parts gives equality of the associated real path distances. -/
theorem Density.pathDist_homeomorph {ρ : Density D} {σ : Density D'}
    (e : D ≃ₜ D')
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e)
    (hei : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e.symm)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (e x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (x y : D) : σ.pathDist (e x) (e y) = ρ.pathDist x y :=
  congrArg ENNReal.toReal (Density.pathEDist_homeomorph e he hei hscale x y)


/-- The transported density satisfies the weighted tangent identity for the given scale. -/
theorem Density.transport_tangent_covariance (ρ : Density D) (e : D ≃ₜ D')
    (μ : D → ℝ) (hμc : Continuous μ) (hμ : ∀ x, 0 < μ x)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      μ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (x : D) (v : TangentSpace 𝓘(ℝ, E) x) :
    ρ.transport e μ hμc hμ (e x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖ :=
  ρ.transport_weighted_norm e μ hμc hμ x _ _ (hscale x v)

/-- The density transport isometry, under the explicit two-sided C¹ adapter hypotheses. -/
theorem Density.transport_pathEDist_c1 (ρ : Density D) (e : D ≃ₜ D')
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e)
    (hei : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e.symm)
    (μ : D → ℝ) (hμc : Continuous μ) (hμ : ∀ x, 0 < μ x)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      μ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (x y : D) : (ρ.transport e μ hμc hμ).pathEDist (e x) (e y) = ρ.pathEDist x y :=
  Density.pathEDist_homeomorph e he hei
    (ρ.transport_tangent_covariance e μ hμc hμ hscale) x y

/-- The invariant-density isometry, under the explicit two-sided C¹ adapter hypotheses. -/
theorem Density.invariant_pathEDist_c1 (ρ : Density D) (e : D ≃ₜ D)
    (he : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e)
    (hei : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 1 e.symm)
    (μ : D → ℝ)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      μ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (hcov : ∀ x, ρ (e x) * μ x = ρ x)
    (x y : D) : ρ.pathEDist (e x) (e y) = ρ.pathEDist x y := by
  apply Density.pathEDist_homeomorph e he hei
  intro z v
  rw [hscale, ← mul_assoc, hcov]

end DensityTransport

section DensityDini
variable {D : TopologicalSpace.Opens E} [PreconnectedSpace D]

/-- A continuous density gives its sharp local upper comparison with the ambient norm. -/
theorem Density.pathEDist_eventually_le_norm {D : TopologicalSpace.Opens E}
    (ρ : Density D) (x : D) {C : ℝ} (hC : ρ x < C) :
    ∀ᶠ y in 𝓝 x,
      ρ.pathEDist x y ≤ ENNReal.ofReal (C * ‖(y : E) - (x : E)‖) := by
  let U : Set E := (Subtype.val : D → E) '' {z : D | ρ z < C}
  have hU : IsOpen U := D.isOpen.isOpenMap_subtype_val _
    (isOpen_lt ρ.continuous continuous_const)
  have hxU : (x : E) ∈ U := ⟨x, hC, rfl⟩
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hxU)
  have hynear : ∀ᶠ y : D in 𝓝 x, (y : E) ∈ Metric.ball (x : E) r :=
    continuous_subtype_val.continuousAt (Metric.ball_mem_nhds _ hr)
  filter_upwards [hynear] with y hy
  let ℓ : ℝ → E := ContinuousAffineMap.lineMap (R := ℝ) (x : E) (y : E)
  have hℓ : MapsTo ℓ (Icc (0 : ℝ) 1) U := by
    intro t ht
    apply hrU
    simpa [ℓ, ContinuousAffineMap.coe_lineMap_eq] using
      (convex_ball (x : E) r).mapsTo_lineMap (Metric.mem_ball_self hr) hy ht
  have hmem (t : ℝ) : ℓ (projIcc 0 1 zero_le_one t) ∈ (D : Set E) := by
    obtain ⟨z, hz, heq⟩ := hℓ (projIcc 0 1 zero_le_one t).property
    exact heq ▸ z.property
  let γ : ℝ → D := fun t => ⟨ℓ (projIcc 0 1 zero_le_one t), hmem t⟩
  have hγeq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : (γ t : E) = ℓ t := by
    simp [γ, projIcc_of_mem zero_le_one ht]
  have hγambient : ContDiffOn ℝ ∞ (fun t => (γ t : E)) (Icc (0 : ℝ) 1) :=
    (ContinuousAffineMap.contDiff _).contDiffOn.congr hγeq
  have hγsmooth : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ γ (Icc (0 : ℝ) 1) := by
    intro t ht
    rw [← ContMDiffWithinAt.subtypeVal_comp_iff D γ (Icc (0 : ℝ) 1) t]
    rw [contMDiffWithinAt_iff_contDiffWithinAt]
    exact hγambient t ht
  have hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 γ (Icc (0 : ℝ) 1) :=
    hγsmooth.of_le (by norm_num)
  have hγ0 : γ 0 = x := by
    apply Subtype.ext
    simpa [ℓ, ContinuousAffineMap.coe_lineMap_eq] using hγeq 0 (by norm_num)
  have hγ1 : γ 1 = y := by
    apply Subtype.ext
    simpa [ℓ, ContinuousAffineMap.coe_lineMap_eq] using hγeq 1 (by norm_num)
  have hρ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ρ (γ t) < C := by
    obtain ⟨z, hz, heq⟩ := hℓ ht
    have he : z = γ t := Subtype.ext (heq.trans (hγeq t ht).symm)
    exact he ▸ hz
  have hderiv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      derivWithin (fun u => (γ u : E)) (Icc (0 : ℝ) 1) t = (y : E) - (x : E) := by
    have h := (AffineMap.hasDerivAt_lineMap (a := (x : E)) (b := (y : E)) (x := t))
    exact (h.hasDerivWithinAt.congr_of_mem hγeq ht).derivWithin
      (uniqueDiffOn_Icc zero_lt_one t ht)
  have hlen : ρ.pieceLength γ 0 1 ≤
      ENNReal.ofReal (C * ‖(y : E) - (x : E)‖) := by
    rw [ρ.pieceLength_eq_lintegral γ 0 1 hγ]
    calc
      _ ≤ ∫⁻ _t in Icc (0 : ℝ) 1,
          ENNReal.ofReal (C * ‖(y : E) - (x : E)‖) := by
        apply setLIntegral_mono' measurableSet_Icc
        intro t ht
        rw [hderiv t ht]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hρ t ht).le (norm_nonneg _))
      _ = _ := by simp
  let : RiemannianBundle (fun z : D => TangentSpace 𝓘(ℝ, E) z) :=
    ⟨ρ.riemannianMetric.toRiemannianMetric⟩
  have hdist : ρ.pathEDist x y ≤ ρ.pieceLength γ 0 1 := by
    rw [ρ.pieceLength_eq_pathELength]
    exact riemannianEDist_le_pathELength hγ hγ0 hγ1 zero_le_one
  exact hdist.trans hlen

/-- Real-valued version of the local upper comparison. -/
theorem Density.pathDist_eventually_le_norm {D : TopologicalSpace.Opens E}
    (ρ : Density D) (x : D) {C : ℝ} (hC : ρ x < C) :
    ∀ᶠ y in 𝓝 x, ρ.pathDist x y ≤ C * ‖(y : E) - (x : E)‖ := by
  filter_upwards [ρ.pathEDist_eventually_le_norm x hC] with y hy
  have hnonneg : 0 ≤ C * ‖(y : E) - (x : E)‖ :=
    mul_nonneg ((ρ.positive x).le.trans hC.le) (norm_nonneg _)
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hy).trans_eq
    (ENNReal.toReal_ofReal hnonneg)

theorem Density.pathDist_self (ρ : Density D) (x : D) : ρ.pathDist x x = 0 := by
  rw [ρ.pathDist_eq_dist]
  exact @dist_self D ρ.metricSpace.toPseudoMetricSpace x

theorem Density.pathDist_comm (ρ : Density D) (x y : D) :
    ρ.pathDist x y = ρ.pathDist y x := by
  simp only [ρ.pathDist_eq_dist]
  exact @dist_comm D ρ.metricSpace.toPseudoMetricSpace x y

theorem Density.continuous_pathDist_left (ρ : Density D) (p : D) :
    Continuous (fun q => ρ.pathDist p q) := by
  let : PseudoMetricSpace D := ρ.metricSpace.toPseudoMetricSpace
  simp only [ρ.pathDist_eq_dist]
  exact (continuous_const : Continuous (fun _ : D => p)).dist
    (continuous_id : Continuous (fun q : D => q))

/-- A sharp local density-distance bound controls right distance slopes of ordinary derivatives. -/
theorem Density.distance_right_slope_bound (ρ : Density D)
    {δ : ℝ → D} {v : E} {t : ℝ}
    (hδ : HasDerivWithinAt (fun s => (δ s : E)) v (Ici t) t)
    (hδc : ContinuousWithinAt δ (Ioi t) t)
    (p : D) {r : ℝ} (hr : ρ (δ t) * ‖v‖ < r) :
    ∃ᶠ s in 𝓝[>] t, slope (fun s => ρ.pathDist p (δ s)) t s < r := by
  have hright := hδ.Ioi_of_Ici
  have hslope : Tendsto (slope (fun s => (δ s : E)) t) (𝓝[>] t) (𝓝 v) :=
    (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl t)).mp hright
  obtain ⟨C, hC, hCr⟩ : ∃ C : ℝ, ρ (δ t) < C ∧ C * ‖v‖ < r := by
    by_cases hv : ‖v‖ = 0
    · exact ⟨ρ (δ t) + 1, by linarith, by simpa [hv] using hr⟩
    · have hvp := lt_of_le_of_ne (norm_nonneg v) (Ne.symm hv)
      obtain ⟨C, hC, hCr⟩ := exists_between ((lt_div_iff₀ hvp).mpr hr)
      exact ⟨C, hC, (lt_div_iff₀ hvp).mp hCr⟩
  have hd : ∀ᶠ s in 𝓝[>] t,
      ρ.pathDist (δ t) (δ s) ≤ C * ‖(δ s : E) - (δ t : E)‖ :=
    hδc (ρ.pathDist_eventually_le_norm (δ t) hC)
  have hquot : ∀ᶠ s in 𝓝[>] t, C * ‖slope (fun s => (δ s : E)) t s‖ < r :=
    (tendsto_const_nhds.mul hslope.norm) (Iio_mem_nhds hCr)
  apply Filter.Eventually.frequently
  filter_upwards [hd, hquot, self_mem_nhdsWithin] with s hs hq hst
  have hpos : 0 < s - t := sub_pos.mpr hst
  have htri : ρ.pathDist p (δ s) - ρ.pathDist p (δ t) ≤ ρ.pathDist (δ t) (δ s) := by
    have hh := ρ.pathDist_triangle p (δ t) (δ s)
    linarith
  calc
    slope (fun s => ρ.pathDist p (δ s)) t s
      ≤ ρ.pathDist (δ t) (δ s) / (s - t) := by
        rw [slope_def_field]
        exact div_le_div_of_nonneg_right htri hpos.le
    _ ≤ (C * ‖(δ s : E) - (δ t : E)‖) / (s - t) :=
      div_le_div_of_nonneg_right hs hpos.le
    _ = C * ‖slope (fun s => (δ s : E)) t s‖ := by
      simp only [slope_def_module, norm_smul, Real.norm_eq_abs, abs_inv,
        abs_of_pos hpos]
      ring
    _ < r := hq

theorem density_hasDerivWithinAt_right_of_Icc {f : ℝ → E} {a b t : ℝ} {v : E}
    (h : HasDerivWithinAt f v (Icc a b) t) (ht : t ∈ Ico a b) :
    HasDerivWithinAt f v (Ici t) t := by
  apply h.mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)] with s hs hsb
  exact ⟨ht.1.trans hs, hsb.le⟩

/-- An ordinary differentiable curve has distance at most its continuous weighted speed integral. -/
theorem Density.pathDist_le_integral_of_continuous_speed (ρ : Density D)
    (δ : ℝ → D) (v : ℝ → E) (a b : ℝ) (hab : a ≤ b)
    (hδ : ContinuousOn δ (Icc a b))
    (hd : ∀ t ∈ Icc a b, HasDerivWithinAt (fun s => (δ s : E)) (v t) (Icc a b) t)
    (hspeed : ContinuousOn (fun t => ρ (δ t) * ‖v t‖) (Icc a b)) :
    ρ.pathDist (δ a) (δ b) ≤ ∫ t in a..b, ρ (δ t) * ‖v t‖ := by
  let β : ℝ → ℝ := IccExtend hab (fun t : Icc a b => ρ (δ t) * ‖v t‖)
  have hβ : Continuous β := hspeed.domRestrict.Icc_extend'
  have hβeq (t : ℝ) (ht : t ∈ Icc a b) : β t = ρ (δ t) * ‖v t‖ :=
    IccExtend_of_mem hab _ ht
  have hg : ContinuousOn (fun t => ρ.pathDist (δ a) (δ t)) (Icc a b) :=
    (ρ.continuous_pathDist_left (δ a)).comp_continuousOn hδ
  have hB : Continuous (fun t => ∫ s in a..t, β s) :=
    intervalIntegral.continuous_primitive (fun c d => hβ.intervalIntegrable c d) a
  have hbound := image_le_of_liminf_slope_right_le_deriv_boundary hg
    (B := fun t => ∫ s in a..t, β s) (B' := β) (by simp [ρ.pathDist_self]) hB.continuousOn
    (fun t _ => (hβ.integral_hasStrictDerivAt a t).hasDerivAt.hasDerivWithinAt)
    (fun t ht r hr => ρ.distance_right_slope_bound
      (density_hasDerivWithinAt_right_of_Icc (hd t ⟨ht.1, ht.2.le⟩) ht)
      ((hδ t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (by
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)] with s hs hsb
        exact ⟨ht.1.trans hs.le, hsb.le⟩))
      (δ a) (by simpa only [hβeq t ⟨ht.1, ht.2.le⟩] using hr))
  apply (hbound (right_mem_Icc.mpr hab)).trans_eq
  apply intervalIntegral.integral_congr
  intro t ht
  exact hβeq t (by simpa only [uIcc_of_le hab] using ht)

section WeakMap

variable {D' : TopologicalSpace.Opens E} [PreconnectedSpace D']

omit [PreconnectedSpace D] in
/-- Ordinary manifold differentiability suffices for the weighted lower bound on a mapped piece. -/
theorem Density.pathDist_comp_piece_le {ρ : Density D} {σ : Density D'} {f : D → D'}
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) f)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (f x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (f x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (γ : ℝ → D) (a b : ℝ) (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 γ (Icc a b)) :
    σ.pathDist (f (γ a)) (f (γ b)) ≤ (ρ.pieceLength γ a b).toReal := by
  rcases hab.eq_or_lt with rfl | hab
  · simp [Density.pieceLength, σ.pathDist_self]
  let δ : ℝ → D' := f ∘ γ
  let ν : ℝ → E := fun t => (tangentSpaceCastModel 𝓘(ℝ, E) (f (γ t)))
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f (γ t) (mfderivWithin 𝓘(ℝ) 𝓘(ℝ, E) γ (Icc a b) t 1))
  have hδ : ContinuousOn δ (Icc a b) := hf.continuous.comp_continuousOn hγ.continuousOn
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (fun s => (δ s : E)) (ν t) (Icc a b) t := by
    have hm := (hf (γ t)).hasMFDerivAt.comp_hasMFDerivWithinAt t
      ((hγ.mdifferentiableOn one_ne_zero t ht).hasMFDerivWithinAt)
    have hc := hm.2.hasDerivWithinAt
    simp only [writtenInExtChartAt, TopologicalSpace.Opens.chartAt_eq, mfld_simps,
      ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] at hc
    convert hc using 1 <;> rfl
  have hs (t : ℝ) (ht : t ∈ Icc a b) : σ (δ t) * ‖ν t‖ =
      ρ (γ t) * ‖derivWithin (fun u => (γ u : E)) (Icc a b) t‖ := by
    dsimp only [δ, ν, Function.comp_def]
    rw [hscale]
    exact congrArg (fun v : E => ρ (γ t) * ‖v‖)
      ((openDomain_mfderivWithin_apply D γ (Icc a b) t 1
        (hγ.mdifferentiableOn one_ne_zero t ht)).trans fderivWithin_derivWithin)
  have hc : ContinuousOn (fun t => ρ (γ t) *
      ‖derivWithin (fun u => (γ u : E)) (Icc a b) t‖) (Icc a b) :=
    (ρ.continuous.comp_continuousOn hγ.continuousOn).mul
      ((openDomain_contDiffOn_ambient hγ).continuousOn_derivWithin
        (uniqueDiffOn_Icc hab) le_rfl).norm
  have hβ : ContinuousOn (fun t => σ (δ t) * ‖ν t‖) (Icc a b) := hc.congr hs
  have hbound := σ.pathDist_le_integral_of_continuous_speed δ ν a b hab.le hδ hd hβ
  have hint : (∫ t in a..b, σ (δ t) * ‖ν t‖) =
      ∫ t in a..b, ρ (γ t) * ‖derivWithin (fun u => (γ u : E)) (Icc a b) t‖ := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hs t (by simpa only [uIcc_of_le hab.le] using ht)
  rw [hint] at hbound
  rw [ρ.pieceLength_eq_ofReal_integral γ a b hab.le hγ, ENNReal.toReal_ofReal]
  · exact hbound
  · apply intervalIntegral.integral_nonneg hab.le
    intro t _
    exact mul_nonneg (ρ.positive (γ t)).le (norm_nonneg _)


omit [PreconnectedSpace D] in
theorem Density.pathDist_comp_chain_le {ρ : Density D} {σ : Density D'} {f : D → D'}
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) f)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (f x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (f x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    {x y : D} (c : RiemannianC1Chain 𝓘(ℝ, E) D x y) :
    σ.pathDist (f x) (f y) ≤ (ρ.chainLength c).toReal := by
  induction c with
  | nil x => simp [Density.chainLength, σ.pathDist_self]
  | @cons x y z γ a b hab hc ha hb tail ih =>
      have hp := Density.pathDist_comp_piece_le hf hscale γ a b hab hc
      rw [ha, hb] at hp
      calc
        σ.pathDist (f x) (f z) ≤ σ.pathDist (f x) (f y) + σ.pathDist (f y) (f z) :=
          σ.pathDist_triangle _ _ _
        _ ≤ (ρ.pieceLength γ a b).toReal + (ρ.chainLength tail).toReal := add_le_add hp ih
        _ = (ρ.chainLength (.cons γ a b hab hc ha hb tail)).toReal := by
          rw [Density.chainLength, ENNReal.toReal_add (ρ.pieceLength_ne_top γ a b hab hc)
            (ρ.chainLength_ne_top tail)]

/-- Weighted tangent covariance bounds actual path distances under an ordinary differentiable map. -/
theorem Density.pathDist_comp_le_mdifferentiable {ρ : Density D} {σ : Density D'} {f : D → D'}
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) f)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (f x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (f x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (x y : D) : σ.pathDist (f x) (f y) ≤ ρ.pathDist x y := by
  have he : ρ.pathEDist x y < ⊤ := (ρ.pathEDist_ne_top x y).lt_top
  rw [ρ.pathEDist_eq_piecewiseEDist, Density.piecewiseEDist, iInf_lt_iff] at he
  obtain ⟨c, _⟩ := he
  have hnonempty : (Set.range (fun d : RiemannianC1Chain 𝓘(ℝ, E) D x y =>
      (ρ.chainLength d).toReal)).Nonempty := ⟨_, c, rfl⟩
  rw [ρ.pathDist_eq_sInf_chain_lengths]
  apply le_csInf hnonempty
  rintro _ ⟨d, rfl⟩
  exact Density.pathDist_comp_chain_le hf hscale d

/-- Extended-distance version of the ordinary differentiable-map comparison. -/
theorem Density.pathEDist_comp_le_mdifferentiable {ρ : Density D} {σ : Density D'} {f : D → D'}
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) f)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (f x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (f x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (x y : D) : σ.pathEDist (f x) (f y) ≤ ρ.pathEDist x y := by
  apply (ENNReal.toReal_le_toReal (σ.pathEDist_ne_top (f x) (f y))
    (ρ.pathEDist_ne_top x y)).mp
  exact Density.pathDist_comp_le_mdifferentiable hf hscale x y

end WeakMap

end DensityDini

section DensityInverse
variable {D D' : TopologicalSpace.Opens E}
/-- In open Euclidean charts, an invertible ordinary derivative differentiates the inverse. -/
theorem openDomain_hasMFDerivAt_symm (e : D ≃ₜ D') (x : D) (A : E ≃L[ℝ] E)
    (hf : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) e x A.toContinuousLinearMap) :
    HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm (e x) A.symm.toContinuousLinearMap := by
  let P : OpenPartialHomeomorph E E :=
    ((chartAt E x).symm.trans e.toOpenPartialHomeomorph).trans (chartAt E (e x))
  have hxx : (chartAt E x) x = (x : E) := rfl
  have hxt : (x : E) ∈ (chartAt E x).target := by
    rw [← hxx]
    exact (chartAt E x).map_source (mem_chart_source E x)
  have hxs : (chartAt E x).symm (x : E) = x := by
    rw [← hxx]
    exact (chartAt E x).left_inv (mem_chart_source E x)
  have hx : (x : E) ∈ P.source := by
    simpa [P, mfld_simps] using
      (show (x : E) ∈ (chartAt E x).target ∧
        e ((chartAt E x).symm (x : E)) ∈ (chartAt E (e x)).source from
          ⟨hxt, openDomain_chart_source D' (e x) _⟩)
  have hPx : P (x : E) = (e x : E) := by
    change (chartAt E (e x)) (e ((chartAt E x).symm (x : E))) = (e x : E)
    rw [hxs]
    rfl
  have hPs : P.symm (e x : E) = (x : E) := by
    rw [← hPx]
    exact P.left_inv hx
  have hP : HasFDerivAt P A.toContinuousLinearMap (x : E) := by
    have hh : HasFDerivWithinAt
        (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) x e)
        A.toContinuousLinearMap (range 𝓘(ℝ, E)) ((extChartAt 𝓘(ℝ, E) x) x) := by
      convert hf.2 using 1
      ext v
      rfl
    simpa [P, writtenInExtChartAt, TopologicalSpace.Opens.chartAt_eq,
      mfld_simps] using hh
  have hi : HasFDerivAt P.symm A.symm.toContinuousLinearMap (e x : E) := by
    have hy : (e x : E) ∈ P.target := hPx ▸ P.map_source hx
    apply P.hasFDerivAt_symm hy
    simpa only [hPs] using hP
  refine ⟨e.symm.continuous.continuousAt, ?_⟩
  have hi' : HasFDerivWithinAt
      (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) (e x) e.symm)
      A.symm.toContinuousLinearMap (range 𝓘(ℝ, E))
      ((extChartAt 𝓘(ℝ, E) (e x)) (e x)) := by
    simpa [P, writtenInExtChartAt, TopologicalSpace.Opens.chartAt_eq,
      mfld_simps, Function.comp_def] using hi
  convert hi' using 1
  ext v
  rfl

/-- Pointwise invertible ordinary derivatives differentiate the inverse homeomorphism. -/
theorem openDomain_inverse_mdifferentiable (e : D ≃ₜ D') (A : D → E ≃L[ℝ] E)
    (hf : ∀ x, HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) e x (A x).toContinuousLinearMap) :
    MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm := by
  intro y
  have h := openDomain_hasMFDerivAt_symm e (e.symm y) (A (e.symm y)) (hf (e.symm y))
  simpa only [e.apply_symm_apply] using h.mdifferentiableAt

/-- The inverse derivative is the inverse of the forward derivative in the open charts. -/
theorem openDomain_mfderiv_symm (e : D ≃ₜ D') (A : D → E ≃L[ℝ] E)
    (hf : ∀ x, HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) e x (A x).toContinuousLinearMap)
    (y : D') : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y =
      (A (e.symm y)).symm.toContinuousLinearMap := by
  have h := openDomain_hasMFDerivAt_symm e (e.symm y) (A (e.symm y)) (hf (e.symm y))
  exact (mfderiv_congr_point (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (f := e.symm) (e.apply_symm_apply y)).symm.trans h.mfderiv

/-- Strictly positive densities make a weighted norm preserving tangent map injective. -/
theorem Density.mfderiv_injective_of_covariance {ρ : Density D} {σ : Density D'}
    {f : D → D'}
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (f x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (f x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (x : D) : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x) := by
  intro v w hvw
  have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x (v - w) = 0 := by
    rw [map_sub, hvw, sub_self]
  have h := hscale x (v - w)
  rw [hd, map_zero, norm_zero, mul_zero] at h
  have hn : ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) (v - w)‖ = 0 :=
    (mul_eq_zero.mp h.symm).resolve_left (ρ.positive x).ne'
  apply sub_eq_zero.mp
  exact (tangentSpaceCastModel 𝓘(ℝ, E) x).injective (by simpa using norm_eq_zero.mp hn)

/-- In finite dimension, weighted tangent covariance supplies invertibility of the derivative. -/
theorem Density.inverse_mdifferentiable_of_covariance [FiniteDimensional ℝ E]
    {ρ : Density D} {σ : Density D'} (e : D ≃ₜ D')
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (e x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖) :
    MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm := by
  let A : D → E ≃L[ℝ] E := fun x =>
    (LinearEquiv.ofInjectiveEndo
      (show E →ₗ[ℝ] E from (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x).toLinearMap)
      (Density.mfderiv_injective_of_covariance hscale x)).toContinuousLinearEquiv
  apply openDomain_inverse_mdifferentiable e A
  intro x
  convert (hf x).hasMFDerivAt using 1
  rfl

/-- Only the forward weighted identity is needed for the merely differentiable inverse. -/
theorem Density.inverse_tangent_covariance_of_mdifferentiable [FiniteDimensional ℝ E]
    {ρ : Density D} {σ : Density D'} (e : D ≃ₜ D')
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (e x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (y : D') (w : TangentSpace 𝓘(ℝ, E) y) :
    ρ (e.symm y) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e.symm y))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y w)‖ =
    σ y * ‖(tangentSpaceCastModel 𝓘(ℝ, E) y) w‖ := by
  have hi := Density.inverse_mdifferentiable_of_covariance e hf hscale
  have hcomp : (e ∘ e.symm : D' → D') = id := funext e.apply_symm_apply
  have hd := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    (I'' := 𝓘(ℝ, E)) y (hf (e.symm y)) (hi y)
  rw [hcomp, mfderiv_id] at hd
  have hv := congrArg (fun A : E →L[ℝ] E => A w) hd
  have hn : ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e (e.symm y)))
      (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e (e.symm y)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y w))‖ =
      ‖(tangentSpaceCastModel 𝓘(ℝ, E) y) w‖ := by
    exact congrArg norm hv.symm
  have hs := (hscale (e.symm y) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e.symm y w)).symm
  rw [hn, e.apply_symm_apply] at hs
  exact hs

end DensityInverse

section DensityDifferentiableIsometry

variable [FiniteDimensional ℝ E] {D D' : TopologicalSpace.Opens E}
    [PreconnectedSpace D] [PreconnectedSpace D']

/-- Ordinary differentiability and weighted tangent covariance suffice for distance preservation. -/
theorem Density.pathEDist_homeomorph_mdifferentiable {ρ : Density D} {σ : Density D'}
    (e : D ≃ₜ D') (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (e x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (x y : D) : σ.pathEDist (e x) (e y) = ρ.pathEDist x y := by
  apply le_antisymm (Density.pathEDist_comp_le_mdifferentiable hf hscale x y)
  simpa only [e.symm_apply_apply] using
    (Density.pathEDist_comp_le_mdifferentiable
      (Density.inverse_mdifferentiable_of_covariance e hf hscale)
      (Density.inverse_tangent_covariance_of_mdifferentiable e hf hscale)
      (e x) (e y))

/-- The ordinary differentiable distance identity is an isometry for the induced metrics. -/
theorem Density.isometry_homeomorph_mdifferentiable {ρ : Density D} {σ : Density D'}
    (e : D ≃ₜ D') (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (e x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖) :
    @Isometry D D' ρ.eMetricSpace.toPseudoEMetricSpace
      σ.eMetricSpace.toPseudoEMetricSpace e := by
  intro x y
  simpa only [Density.pathEDist_eq_edist] using
    (Density.pathEDist_homeomorph_mdifferentiable e hf hscale x y)

/-- The same isometry preserves the real-valued length-infimum distances. -/
theorem Density.pathDist_homeomorph_mdifferentiable {ρ : Density D} {σ : Density D'}
    (e : D ≃ₜ D') (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (e x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (x y : D) : σ.pathDist (e x) (e y) = ρ.pathDist x y :=
  congrArg ENNReal.toReal
    (Density.pathEDist_homeomorph_mdifferentiable e hf hscale x y)

/-- A merely differentiable conformal homeomorphism preserves the transported density metric. -/
theorem Density.transport_pathEDist_mdifferentiable (ρ : Density D) (e : D ≃ₜ D')
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e)
    (μ : D → ℝ) (hμc : Continuous μ) (hμ : ∀ x, 0 < μ x)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      μ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (x y : D) : (ρ.transport e μ hμc hμ).pathEDist (e x) (e y) = ρ.pathEDist x y :=
  Density.pathEDist_homeomorph_mdifferentiable e hf
    (ρ.transport_tangent_covariance e μ hμc hμ hscale) x y

/-- Density covariance gives an isometry without continuity of the derivative. -/
theorem Density.invariant_pathEDist_mdifferentiable (ρ : Density D) (e : D ≃ₜ D)
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e)
    (μ : D → ℝ)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      μ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (hcov : ∀ x, ρ (e x) * μ x = ρ x)
    (x y : D) : ρ.pathEDist (e x) (e y) = ρ.pathEDist x y := by
  apply Density.pathEDist_homeomorph_mdifferentiable e hf
  intro z v
  rw [hscale, ← mul_assoc, hcov]

end DensityDifferentiableIsometry

section DensityOpenMap
variable [FiniteDimensional ℝ E]
/-- Ordinary everywhere invertible derivatives make the image of an open Euclidean set open. -/
theorem euclidean_image_mem_nhds_of_hasFDerivAt_equiv {f : E → E} {s : Set E}
    (hs : IsOpen s)
    (hf : ∀ x ∈ s, ∃ A : E ≃L[ℝ] E, HasFDerivAt f A.toContinuousLinearMap x)
    {x : E} (hx : x ∈ s) : f '' s ∈ 𝓝 (f x) := by
  obtain ⟨A, hA⟩ := hf x hx
  obtain ⟨c, hc, hbound⟩ := isBigO_iff''.mp
    (hA.isTheta_sub A.toHomeomorph.isInducing).isBigO_symm
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp
    (Filter.inter_mem (hs.mem_nhds hx) hbound)
  let r : ℝ := R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hK (u : E) (hu : u ∈ Metric.closedBall x r) :
      u ∈ s ∧ c * ‖u - x‖ ≤ ‖f u - f x‖ :=
    hball (Metric.closedBall_subset_ball (by dsimp [r]; linarith) hu)
  have hε : 0 < c * r / 2 := by positivity
  apply mem_of_superset (Metric.ball_mem_nhds (f x) hε)
  intro z hz
  have hz' : ‖f x - z‖ < c * r / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hz
  have hfc : ContinuousOn f (Metric.closedBall x r) := by
    intro u hu
    obtain ⟨B, hB⟩ := hf u (hK u hu).1
    exact hB.continuousAt.continuousWithinAt
  have hobj : ContinuousOn (fun v => ‖f v - z‖ ^ 2) (Metric.closedBall x r) :=
    (hfc.sub continuousOn_const).norm.pow 2
  obtain ⟨u, hu, hmin⟩ := (isCompact_closedBall x r).exists_isMinOn
    (Metric.nonempty_closedBall.mpr hr.le) hobj
  have huinside : u ∈ Metric.ball x r := by
    by_contra hnot
    have hnorm : ‖u - x‖ = r := by
      have hle : ‖u - x‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hu
      have hge : r ≤ ‖u - x‖ := by simpa only [Metric.mem_ball, dist_eq_norm, not_lt] using hnot
      exact le_antisymm hle hge
    have hlow := (hK u hu).2
    rw [hnorm] at hlow
    have htri : ‖f u - f x‖ ≤ ‖f u - z‖ + ‖f x - z‖ := by
      have h := norm_add_le (f u - z) (z - f x)
      simpa only [sub_add_sub_cancel, norm_sub_rev z (f x)] using h
    have hminx : ‖f u - z‖ ^ 2 ≤ ‖f x - z‖ ^ 2 :=
      hmin (Metric.mem_closedBall_self hr.le)
    have hpos : ‖f x - z‖ < ‖f u - z‖ := by linarith
    nlinarith [norm_nonneg (f u - z), norm_nonneg (f x - z)]
  have hloc : IsLocalMin (fun v => ‖f v - z‖ ^ 2) u :=
    hmin.isLocalMin (Metric.closedBall_mem_nhds_of_mem huinside)
  obtain ⟨B, hB⟩ := hf u (hK u hu).1
  have hzero := hloc.hasFDerivAt_eq_zero (hB.sub_const z).norm_sq
  have hv := congrArg (fun L : E →L[ℝ] ℝ => L (B.symm (f u - z))) hzero
  simp [two_smul, ContinuousLinearMap.comp_apply, innerSL_apply_apply] at hv
  have hv' : inner ℝ (f u - z) (f u - z) = 0 := by
    rw [inner_sub_left]
    exact hv
  have heq : f u = z := sub_eq_zero.mp (inner_self_eq_zero.mp hv')
  exact ⟨u, (hK u hu).1, heq⟩

/-- The open-image form of the preceding local surjectivity theorem. -/
theorem isOpen_image_of_hasFDerivAt_equiv {f : E → E} {s : Set E}
    (hs : IsOpen s)
    (hf : ∀ x ∈ s, ∃ A : E ≃L[ℝ] E, HasFDerivAt f A.toContinuousLinearMap x) :
    IsOpen (f '' s) := by
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨x, hx, rfl⟩
  exact euclidean_image_mem_nhds_of_hasFDerivAt_equiv hs hf hx

/-- An ordinary differentiable Euclidean map with invertible derivative everywhere is open. -/
theorem isOpenMap_of_hasFDerivAt_equiv {f : E → E}
    (hf : ∀ x, ∃ A : E ≃L[ℝ] E, HasFDerivAt f A.toContinuousLinearMap x) :
    IsOpenMap f := by
  intro s hs
  exact isOpen_image_of_hasFDerivAt_equiv hs (fun x _ => hf x)

section OpenDomains

variable {D D' : TopologicalSpace.Opens E}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Every preferred chart of an open subset is the ambient inclusion. -/
theorem openDomain_chart_symm_apply (x y : D) : (chartAt E x).symm (y : E) = y := by
  have hxy : (chartAt E x) y = (y : E) := rfl
  rw [← hxy]
  exact (chartAt E x).left_inv (openDomain_chart_source D x y)

omit [FiniteDimensional ℝ E] in
/-- Any fixed open-domain chart gives an ordinary derivative extension at every domain point. -/
theorem openDomain_hasFDerivAt_extension {f : D → D'} (x u : D) (A : E ≃L[ℝ] E)
    (hf : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) f u A.toContinuousLinearMap) :
    HasFDerivAt (fun z : E => (f ((chartAt E x).symm z) : E))
      A.toContinuousLinearMap (u : E) := by
  have hcoord : HasFDerivAt (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) u f)
      A.toContinuousLinearMap (u : E) := by
    have hh : HasFDerivWithinAt
        (writtenInExtChartAt 𝓘(ℝ, E) 𝓘(ℝ, E) u f)
        A.toContinuousLinearMap (range 𝓘(ℝ, E)) ((extChartAt 𝓘(ℝ, E) u) u) := by
      convert hf.2 using 1
      ext v
      rfl
    simpa [TopologicalSpace.Opens.chartAt_eq, mfld_simps] using hh
  apply hcoord.congr_of_eventuallyEq
  filter_upwards [D.isOpen.mem_nhds u.property] with z hz
  have hxz := openDomain_chart_symm_apply x (⟨z, hz⟩ : D)
  have huz := openDomain_chart_symm_apply u (⟨z, hz⟩ : D)
  change (f ((chartAt E x).symm z) : E) = (f ((chartAt E u).symm z) : E)
  rw [hxz, huz]

/-- Ordinary invertible derivatives make a map between open Euclidean domains open. -/
theorem openDomain_isOpenMap_of_hasMFDerivAt_equiv {f : D → D'}
    (hf : ∀ x, ∃ A : E ≃L[ℝ] E,
      HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) f x A.toContinuousLinearMap) : IsOpenMap f := by
  apply D'.isOpen.isOpenEmbedding_subtypeVal.isOpenMap_iff.mpr
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro z ⟨x, hx, rfl⟩
  let F : E → E := fun z => (f ((chartAt E x).symm z) : E)
  let S : Set E := (Subtype.val : D → E) '' U
  have hS : IsOpen S := D.isOpen.isOpenMap_subtype_val U hU
  have hF : ∀ u ∈ S, ∃ A : E ≃L[ℝ] E, HasFDerivAt F A.toContinuousLinearMap u := by
    rintro z ⟨u, hu, rfl⟩
    obtain ⟨A, hA⟩ := hf u
    exact ⟨A, openDomain_hasFDerivAt_extension x u A hA⟩
  have hN : F '' S ∈ 𝓝 (F (x : E)) :=
    euclidean_image_mem_nhds_of_hasFDerivAt_equiv hS hF ⟨x, hx, rfl⟩
  have hFx : F (x : E) = (f x : E) := by
    simp only [F, openDomain_chart_symm_apply]
  rw [hFx] at hN
  change ((fun u : D => (f u : E)) '' U) ∈ 𝓝 (f x : E)
  apply mem_of_superset hN
  rintro z ⟨w, ⟨u, hu, rfl⟩, rfl⟩
  refine ⟨u, hu, ?_⟩
  simp only [F, openDomain_chart_symm_apply]

end OpenDomains

end DensityOpenMap

section DensityBijections
variable [FiniteDimensional ℝ E] {D D' : TopologicalSpace.Opens E}
/-- A positive pointwise conformal scale makes the ordinary tangent derivative invertible. -/
theorem openDomain_hasMFDerivAt_equiv_of_positive_scale {f : D → D'}
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) f)
    (μ : D → ℝ) (hμ : ∀ x, 0 < μ x)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖(tangentSpaceCastModel 𝓘(ℝ, E) (f x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v)‖ =
      μ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (x : D) : ∃ A : E ≃L[ℝ] E,
      HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) f x A.toContinuousLinearMap := by
  have hinj : Function.Injective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x) := by
    intro v w hvw
    have hd : mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x (v - w) = 0 := by
      rw [map_sub, hvw, sub_self]
    have h := hscale x (v - w)
    rw [hd, map_zero, norm_zero] at h
    have hn : ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) (v - w)‖ = 0 :=
      (mul_eq_zero.mp h.symm).resolve_left (hμ x).ne'
    apply sub_eq_zero.mp
    exact (tangentSpaceCastModel 𝓘(ℝ, E) x).injective (by simpa using norm_eq_zero.mp hn)
  let A : E ≃L[ℝ] E :=
    (LinearEquiv.ofInjectiveEndo
      (show E →ₗ[ℝ] E from (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x).toLinearMap)
      hinj).toContinuousLinearEquiv
  refine ⟨A, ?_⟩
  convert (hf x).hasMFDerivAt using 1
  rfl

/-- A differentiable conformal bijection is automatically a homeomorphism. -/
def openDomain_homeomorphOfPositiveScaleEquiv (e : D ≃ D')
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e)
    (μ : D → ℝ) (hμ : ∀ x, 0 < μ x)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      μ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖) : D ≃ₜ D' :=
  e.toHomeomorphOfContinuousOpen hf.continuous
    (openDomain_isOpenMap_of_hasMFDerivAt_equiv
      (openDomain_hasMFDerivAt_equiv_of_positive_scale hf μ hμ hscale))

/-- Density covariance supplies invertible ordinary derivatives at every point. -/
theorem Density.hasMFDerivAt_equiv_of_covariance {ρ : Density D} {σ : Density D'}
    {f : D → D'} (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) f)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (f x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (f x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (x : D) : ∃ A : E ≃L[ℝ] E,
      HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) f x A.toContinuousLinearMap := by
  let A : E ≃L[ℝ] E :=
    (LinearEquiv.ofInjectiveEndo
      (show E →ₗ[ℝ] E from (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) f x).toLinearMap)
      (Density.mfderiv_injective_of_covariance hscale x)).toContinuousLinearEquiv
  refine ⟨A, ?_⟩
  convert (hf x).hasMFDerivAt using 1
  rfl

/-- A differentiable density-preserving bijection is automatically a homeomorphism. -/
def Density.homeomorphOfCovariance {ρ : Density D} {σ : Density D'}
    (e : D ≃ D') (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (e x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖) : D ≃ₜ D' :=
  e.toHomeomorphOfContinuousOpen hf.continuous
    (openDomain_isOpenMap_of_hasMFDerivAt_equiv
      (Density.hasMFDerivAt_equiv_of_covariance hf hscale))

/-- Transport along the original bare conformal bijection, with necessary scale continuity. -/
def Density.transportEquiv (ρ : Density D) (e : D ≃ D')
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e)
    (μ : D → ℝ) (hμc : Continuous μ) (hμ : ∀ x, 0 < μ x)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      μ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖) : Density D' :=
  ρ.transport (openDomain_homeomorphOfPositiveScaleEquiv e hf μ hμ hscale) μ hμc hμ

/-- The bare-bijection density transport has the specified pointwise value. -/
theorem Density.transportEquiv_apply (ρ : Density D) (e : D ≃ D')
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e)
    (μ : D → ℝ) (hμc : Continuous μ) (hμ : ∀ x, 0 < μ x)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      μ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖) (x : D) :
    ρ.transportEquiv e hf μ hμc hμ hscale (e x) = ρ x / μ x :=
  ρ.transport_apply (openDomain_homeomorphOfPositiveScaleEquiv e hf μ hμ hscale)
    μ hμc hμ x

section ConnectedBijections

variable [PreconnectedSpace D] [PreconnectedSpace D']

/-- Weighted tangent covariance makes the original differentiable bijection an isometry. -/
theorem Density.pathEDist_equiv {ρ : Density D} {σ : Density D'}
    (e : D ≃ D') (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (e x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (x y : D) : σ.pathEDist (e x) (e y) = ρ.pathEDist x y :=
  Density.pathEDist_homeomorph_mdifferentiable
    (Density.homeomorphOfCovariance e hf hscale) hf hscale x y

/-- The bijection is an isometry for the density-induced extended metrics. -/
theorem Density.isometry_equiv {ρ : Density D} {σ : Density D'}
    (e : D ≃ D') (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (e x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖) :
    @Isometry D D' ρ.eMetricSpace.toPseudoEMetricSpace
      σ.eMetricSpace.toPseudoEMetricSpace e := by
  intro x y
  simpa only [Density.pathEDist_eq_edist] using (Density.pathEDist_equiv e hf hscale x y)

/-- The bare-bijection isometry preserves the ordinary real length-infimum metric. -/
theorem Density.pathDist_equiv {ρ : Density D} {σ : Density D'}
    (e : D ≃ D') (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      σ (e x) * ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      ρ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (x y : D) : σ.pathDist (e x) (e y) = ρ.pathDist x y :=
  congrArg ENNReal.toReal (Density.pathEDist_equiv e hf hscale x y)

/-- The transported density metric is preserved by the conformal bijection. -/
theorem Density.transport_pathEDist_equiv (ρ : Density D) (e : D ≃ D')
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e)
    (μ : D → ℝ) (hμc : Continuous μ) (hμ : ∀ x, 0 < μ x)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      μ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (x y : D) : (ρ.transportEquiv e hf μ hμc hμ hscale).pathEDist (e x) (e y) =
      ρ.pathEDist x y :=
  ρ.transport_pathEDist_mdifferentiable
    (openDomain_homeomorphOfPositiveScaleEquiv e hf μ hμ hscale) hf μ hμc hμ hscale x y

omit [PreconnectedSpace D'] in
/-- The density relation makes a merely differentiable bijection an isometry. -/
theorem Density.invariant_pathEDist_equiv (ρ : Density D) (e : D ≃ D)
    (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ, E) e) (μ : D → ℝ)
    (hscale : ∀ (x : D) (v : TangentSpace 𝓘(ℝ, E) x),
      ‖(tangentSpaceCastModel 𝓘(ℝ, E) (e x))
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) e x v)‖ =
      μ x * ‖(tangentSpaceCastModel 𝓘(ℝ, E) x) v‖)
    (hcov : ∀ x, ρ (e x) * μ x = ρ x)
    (x y : D) : ρ.pathEDist (e x) (e y) = ρ.pathEDist x y := by
  apply Density.pathEDist_equiv e hf
  intro z v
  rw [hscale, ← mul_assoc, hcov]

end ConnectedBijections

end DensityBijections

end
end LowDimensionalTopology.Geometry.Auxiliary.Analysis
