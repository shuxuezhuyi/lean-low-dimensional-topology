module

public import LowDimensionalTopology.Geometry.Teichmuller.NativeTeichmullerMetric
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.S34mManifold
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Actual Bers coordinates of native smooth-marked classes

The native/source equivalence and the normalized-lift source equivalence give
coordinates in an actual bounded connected open subset of a finite-dimensional
complex vector space. The full-log QC metric makes these coordinates continuous.
The coordinate topology below is explicit data; comparison with the independently
coinduced realized-coefficient topology requires a separate proof.
-/

@[expose] public section
noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace

open Surfaces

universe u

variable {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)

variable {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (hPresentation : Unproved.HandleGroupPresentation g)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)}
    (hΓ : LiZhongQC.IsFuchsian Γ) (hfree : LiZhongQC.ActsFreely Γ)
    {p : UpperHalfPlane → X}
    (hp : let := R.toRiemannAtlas.toChartedSpace; LiZhongQC.IsUniformization Γ p)

/-- The source equivalence is selected with its actual normalized-lift law. -/
def sourceGammaEquiv : LiZhongQC.TeichGamma Γ ≃
    let := R.toRiemannAtlas.toChartedSpace
    LiZhongQC.TeichSpace X := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  exact Classical.choose (LiZhongQC.teichGamma_equiv_teichSpace hg
    (R.sourceHasGenus hgenus hPresentation) hΓ hfree hp)

/-- The normalized-lift equivalence also preserves the source half-log distance. -/
theorem sourceGammaEquiv_distance (a b : LiZhongQC.TeichGamma Γ) :
    let := R.toRiemannAtlas.toChartedSpace
    LiZhongQC.teichDistanceGamma a b = LiZhongQC.teichDistance
      (sourceGammaEquiv R hg hgenus hPresentation hΓ hfree hp a)
      (sourceGammaEquiv R hg hgenus hPresentation hΓ hfree hp b) := by
  dsimp only
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  have he := Classical.choose_spec (LiZhongQC.teichGamma_equiv_teichSpace hg
    (R.sourceHasGenus hgenus hPresentation) hΓ hfree hp)
  exact le_antisymm
    (LiZhongQC.s33d_ge hg (R.sourceHasGenus hgenus hPresentation) hΓ hfree hp
      (sourceGammaEquiv R hg hgenus hPresentation hΓ hfree hp) he a b)
    (LiZhongQC.s33d_le hg (R.sourceHasGenus hgenus hPresentation) hΓ hfree hp
      (sourceGammaEquiv R hg hgenus hPresentation hΓ hfree hp) he a b)

/-- Native smooth markings give exactly the actual group-coefficient classes. -/
def gammaEquiv : TeichmullerSpace.{u, u} R ≃ LiZhongQC.TeichGamma Γ :=
  (sourceEquiv R hg hgenus hPresentation).trans
    (sourceGammaEquiv R hg hgenus hPresentation hΓ hfree hp).symm

/-- The native full-log distance is twice the actual group half-log distance. -/
theorem fromQCDistance_eq_two_mul_gamma (a b : TeichmullerSpace.{u, u} R) :
    fromQCDistance R a b = 2 * LiZhongQC.teichDistanceGamma
      (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a)
      (gammaEquiv R hg hgenus hPresentation hΓ hfree hp b) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  let e := sourceGammaEquiv R hg hgenus hPresentation hΓ hfree hp
  have ha : e (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a) = toSource R a :=
    e.apply_symm_apply _
  have hb : e (gammaEquiv R hg hgenus hPresentation hΓ hfree hp b) = toSource R b :=
    e.apply_symm_apply _
  change QCBookMetric.bookDistance (toSource R a) (toSource R b) = _
  rw [QCBookMetric.bookDistance_eq_two_mul, ← ha, ← hb,
    ← sourceGammaEquiv_distance R hg hgenus hPresentation hΓ hfree hp]

/-- Linear coordinates are obtained from actual compact-surface QD theory. -/
def linearBersCoordinates :
    LiZhongQC.automorphicQD Γ ≃L[ℂ] (Fin (3 * g - 3) → ℂ) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  exact Classical.choose (LiZhongQC.s34m_coords hg
    (R.sourceHasGenus hgenus hPresentation) hΓ hp)

/-- The chosen linear coordinate map has the source's proved norm and image properties. -/
theorem linearBersCoordinates_spec :
    (∀ φ : LiZhongQC.automorphicQD Γ,
      LiZhongQC.bersNormL (φ : ℂ → ℂ) < ⊤) ∧
    Function.Injective (fun t : LiZhongQC.TeichGamma Γ =>
      linearBersCoordinates R hg hgenus hPresentation hΓ hp
        ⟨LiZhongQC.bersMapGamma Γ t, (LiZhongQC.bersMapGamma_mem hΓ t).1⟩) ∧
    IsOpen (range fun t : LiZhongQC.TeichGamma Γ =>
      linearBersCoordinates R hg hgenus hPresentation hΓ hp
        ⟨LiZhongQC.bersMapGamma Γ t, (LiZhongQC.bersMapGamma_mem hΓ t).1⟩) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := R.t2Space
  let := R.connectedSpace
  let := R.compactSpace
  exact Classical.choose_spec (LiZhongQC.s34m_coords hg
    (R.sourceHasGenus hgenus hPresentation) hΓ hp)

/-- Bers coordinates evaluated on the actual native marked-surface quotient. -/
def bersCoordinates (a : TeichmullerSpace.{u, u} R) : Fin (3 * g - 3) → ℂ :=
  linearBersCoordinates R hg hgenus hPresentation hΓ hp
    ⟨LiZhongQC.bersMapGamma Γ (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a),
      (LiZhongQC.bersMapGamma_mem hΓ _).1⟩

theorem bersCoordinates_injective : Function.Injective
    (bersCoordinates R hg hgenus hPresentation hΓ hfree hp) :=
  (linearBersCoordinates_spec R hg hgenus hPresentation hΓ hp).2.1.comp
    (gammaEquiv R hg hgenus hPresentation hΓ hfree hp).injective

theorem range_bersCoordinates :
    range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp) =
      range (fun t : LiZhongQC.TeichGamma Γ =>
        linearBersCoordinates R hg hgenus hPresentation hΓ hp
          ⟨LiZhongQC.bersMapGamma Γ t, (LiZhongQC.bersMapGamma_mem hΓ t).1⟩) := by
  ext v
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨gammaEquiv R hg hgenus hPresentation hΓ hfree hp a, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨(gammaEquiv R hg hgenus hPresentation hΓ hfree hp).symm t, ?_⟩
    simp only [bersCoordinates, Equiv.apply_symm_apply]

theorem isOpen_range_bersCoordinates :
    IsOpen (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp)) := by
  rw [range_bersCoordinates R hg hgenus hPresentation hΓ hfree hp]
  exact (linearBersCoordinates_spec R hg hgenus hPresentation hΓ hp).2.2

theorem isConnected_range_bersCoordinates :
    IsConnected (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp)) := by
  rw [range_bersCoordinates R hg hgenus hPresentation hΓ hfree hp]
  exact LiZhongQC.s33dim_coords_connected hΓ
    (linearBersCoordinates R hg hgenus hPresentation hΓ hp)

/-- Actual weighted Bers norm controls differences in these finite-dimensional coordinates. -/
theorem bersCoordinates_norm_comparison : ∃ c > 0,
    ∀ a b : TeichmullerSpace.{u, u} R,
      ENNReal.ofReal (c * ‖bersCoordinates R hg hgenus hPresentation hΓ hfree hp a -
        bersCoordinates R hg hgenus hPresentation hΓ hfree hp b‖) ≤
      LiZhongQC.bersNormL
        (LiZhongQC.bersMapGamma Γ (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a) -
          LiZhongQC.bersMapGamma Γ (gammaEquiv R hg hgenus hPresentation hΓ hfree hp b)) := by
  have hn : 0 < 3 * g - 3 := by omega
  obtain ⟨c, d, hc, _, hcompare⟩ := LiZhongQC.s33dim_coordinate_comparison hn
    (linearBersCoordinates R hg hgenus hPresentation hΓ hp)
    (linearBersCoordinates_spec R hg hgenus hPresentation hΓ hp).1
  refine ⟨c, hc, fun a b => ?_⟩
  simpa only [bersCoordinates, map_sub, Submodule.coe_sub] using
    (hcompare (⟨LiZhongQC.bersMapGamma Γ
      (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a),
        (LiZhongQC.bersMapGamma_mem hΓ _).1⟩ -
      ⟨LiZhongQC.bersMapGamma Γ
        (gammaEquiv R hg hgenus hPresentation hΓ hfree hp b),
        (LiZhongQC.bersMapGamma_mem hΓ _).1⟩)).1

theorem isBounded_range_bersCoordinates :
    Bornology.IsBounded
      (range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp)) := by
  rw [range_bersCoordinates R hg hgenus hPresentation hΓ hfree hp]
  have hn : 0 < 3 * g - 3 := by omega
  obtain ⟨c, d, hc, _, hcompare⟩ := LiZhongQC.s33dim_coordinate_comparison hn
    (linearBersCoordinates R hg hgenus hPresentation hΓ hp)
    (linearBersCoordinates_spec R hg hgenus hPresentation hΓ hp).1
  exact LiZhongQC.s33dim_coords_bounded hΓ
    (linearBersCoordinates R hg hgenus hPresentation hΓ hp) hc fun φ => (hcompare φ).1

/-- The actual full-log metric makes the actual Bers coordinates continuous. -/
theorem continuous_bersCoordinates_fromQC :
    let : MetricSpace (TeichmullerSpace.{u, u} R) :=
      fromQCMetricSpace R hg hgenus hPresentation
    Continuous (bersCoordinates R hg hgenus hPresentation hΓ hfree hp) := by
  let : MetricSpace (TeichmullerSpace.{u, u} R) :=
    fromQCMetricSpace R hg hgenus hPresentation
  obtain ⟨c, hc, hcompare⟩ :=
    bersCoordinates_norm_comparison R hg hgenus hPresentation hΓ hfree hp
  apply continuous_iff_continuousAt.2
  intro a
  apply Metric.continuousAt_iff.2
  intro ε hε
  let δ := Real.log (1 + (2 / 3 : ℝ) * c * ε)
  have harg : 1 < 1 + (2 / 3 : ℝ) * c * ε := by nlinarith
  have hδ : 0 < δ := Real.log_pos harg
  have hexp : (3 / 2 : ℝ) * (Real.exp δ - 1) = c * ε := by
    dsimp only [δ]
    rw [Real.exp_log (lt_trans zero_lt_one harg)]
    ring
  refine ⟨δ, hδ, fun b hb => ?_⟩
  have hd : LiZhongQC.teichDistanceGamma
      (gammaEquiv R hg hgenus hPresentation hΓ hfree hp b)
      (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a) < δ / 2 := by
    change fromQCDistance R b a < δ at hb
    rw [fromQCDistance_eq_two_mul_gamma R hg hgenus hPresentation hΓ hfree hp] at hb
    linarith
  have hbers : LiZhongQC.bersNormL
      (LiZhongQC.bersMapGamma Γ (gammaEquiv R hg hgenus hPresentation hΓ hfree hp b) -
        LiZhongQC.bersMapGamma Γ (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a)) <
      ENNReal.ofReal (3 / 2 * (Real.exp δ - 1)) := by
    obtain ⟨h0, h1, hrep⟩ := LiZhongQC.bg_d_teichDelta_spec
      (gammaEquiv R hg hgenus hPresentation hΓ hfree hp b)
      (gammaEquiv R hg hgenus hPresentation hΓ hfree hp a)
    obtain ⟨μ, ν, hμ, hν, hμν⟩ := hrep _ (LiZhongQC.bg_d_lt_of_log_lt h0 h1 hd)
    rw [LiZhongQC.bg_bersMapGamma_eq hμ, LiZhongQC.bg_bersMapGamma_eq hν]
    have hE : 1 < Real.exp δ := Real.one_lt_exp_iff.2 hδ
    refine (LiZhongQC.eq21_10 ν.1 μ.1).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 ?_)
    linarith
  rw [hexp] at hbers
  have hnorm := (ENNReal.ofReal_lt_ofReal_iff (mul_pos hc hε)).1
    ((hcompare b a).trans_lt hbers)
  rw [dist_eq_norm]
  nlinarith

/-- The coordinate topology is explicit data, distinct until a comparison is proved. -/
@[instance_reducible]
def bersTopology : TopologicalSpace (TeichmullerSpace.{u, u} R) :=
  TopologicalSpace.induced
    (bersCoordinates R hg hgenus hPresentation hΓ hfree hp) inferInstance

/-- In its coordinate topology, the native space is homeomorphic to its actual open image. -/
def bersCoordinateHomeomorph :
    let : TopologicalSpace (TeichmullerSpace.{u, u} R) :=
      bersTopology R hg hgenus hPresentation hΓ hfree hp
    TeichmullerSpace.{u, u} R ≃ₜ
      range (bersCoordinates R hg hgenus hPresentation hΓ hfree hp) := by
  let : TopologicalSpace (TeichmullerSpace.{u, u} R) :=
    bersTopology R hg hgenus hPresentation hΓ hfree hp
  exact (show Topology.IsEmbedding
      (bersCoordinates R hg hgenus hPresentation hΓ hfree hp) from
    ⟨⟨rfl⟩, bersCoordinates_injective R hg hgenus hPresentation hΓ hfree hp⟩).toHomeomorph

/-- The proved open range makes these actual coordinates an open embedding. -/
theorem bersCoordinates_isOpenEmbedding :
    let : TopologicalSpace (TeichmullerSpace.{u, u} R) :=
      bersTopology R hg hgenus hPresentation hΓ hfree hp
    Topology.IsOpenEmbedding
      (bersCoordinates R hg hgenus hPresentation hΓ hfree hp) := by
  let : TopologicalSpace (TeichmullerSpace.{u, u} R) :=
    bersTopology R hg hgenus hPresentation hΓ hfree hp
  exact ⟨⟨⟨rfl⟩, bersCoordinates_injective R hg hgenus hPresentation hΓ hfree hp⟩,
    isOpen_range_bersCoordinates R hg hgenus hPresentation hΓ hfree hp⟩

/-- An actual complex atlas, carried by the explicit Bers coordinate topology. -/
@[instance_reducible]
def bersChartedSpace :
    let : TopologicalSpace (TeichmullerSpace.{u, u} R) :=
      bersTopology R hg hgenus hPresentation hΓ hfree hp
    ChartedSpace (Fin (3 * g - 3) → ℂ) (TeichmullerSpace.{u, u} R) := by
  let : TopologicalSpace (TeichmullerSpace.{u, u} R) :=
    bersTopology R hg hgenus hPresentation hΓ hfree hp
  exact Topology.IsOpenEmbedding.singletonChartedSpace
    (bersCoordinates_isOpenEmbedding R hg hgenus hPresentation hΓ hfree hp)

/-- The coordinate atlas has analytic transition maps. -/
theorem bers_isManifold :
    let : TopologicalSpace (TeichmullerSpace.{u, u} R) :=
      bersTopology R hg hgenus hPresentation hΓ hfree hp
    let : ChartedSpace (Fin (3 * g - 3) → ℂ) (TeichmullerSpace.{u, u} R) :=
      bersChartedSpace R hg hgenus hPresentation hΓ hfree hp
    IsManifold 𝓘(ℂ, Fin (3 * g - 3) → ℂ) ω (TeichmullerSpace.{u, u} R) := by
  let : TopologicalSpace (TeichmullerSpace.{u, u} R) :=
    bersTopology R hg hgenus hPresentation hΓ hfree hp
  exact Topology.IsOpenEmbedding.isManifold_singleton
    (bersCoordinates_isOpenEmbedding R hg hgenus hPresentation hΓ hfree hp)

end LowDimensionalTopology.Geometry.Teichmuller.TeichmullerSpace
