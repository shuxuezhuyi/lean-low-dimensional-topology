module

public import LowDimensionalTopology.Geometry.Surfaces.Riemann.HolomorphicQuadraticDifferential
public import LowDimensionalTopology.Geometry.Surfaces.Topology.Genus.HandleGenusBridge
public import LowDimensionalTopology.Geometry.Teichmuller.SourceMarking
public import LowDimensionalTopology.External.LiZhongQC.Lemmas.UniformizedTeichmuller

/-!
# Unique extremal maps on the original closed Riemann surfaces

The original carriers, complex atlases, homeomorphisms and homotopy classes are
retained. The proved handle presentation supplies the fundamental-group genus
needed by the analytic existence and uniqueness theorems. Initial and terminal
quadratic differentials belong to the original native atlases.

The analytic results are adapted from Wu Xiaobin's Li-Zhong-QC-formalization,
pinned at `1c0d5473c020b66ed5106331a38a61536760b9b2` under Apache-2.0; see
`THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open scoped Manifold ContDiff

namespace LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface

open Teichmuller

universe u v

/-- A Teichmüller map, including its conformal case, between the original atlases
is extremal. Equality of maximal dilatations in its homotopy class holds exactly
for that same map. -/
theorem teichmullerMap_unique_extremal
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) {f₀ : X ≃ₜ Y}
    (hkind :
      letI := R.toRiemannAtlas.toChartedSpace
      letI := S.toRiemannAtlas.toChartedSpace
      RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f₀ ∨
        ∃ (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
          (q' : HolomorphicQuadraticDifferential S.toRiemannAtlas) (k : ℝ),
            LiZhongQC.IsTeichmullerMap f₀ q q' k) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := S.toRiemannAtlas.toChartedSpace
    LiZhongQC.IsExtremalInHomotopyClass f₀ ∧
      ∀ f : X ≃ₜ Y, LiZhongQC.IsQCRS f →
        ContinuousMap.Homotopic (f₀ : C(X, Y)) (f : C(X, Y)) →
          LiZhongQC.maxDilatationRS f₀ ≤ LiZhongQC.maxDilatationRS f ∧
            (LiZhongQC.maxDilatationRS f = LiZhongQC.maxDilatationRS f₀ ↔ f = f₀) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := S.toRiemannAtlas.isManifold
  let := R.t2Space
  let := S.t2Space
  let := R.connectedSpace
  let := S.connectedSpace
  have htarget : S.HasGenus g := by
    obtain ⟨e⟩ := hgenus
    exact ⟨f₀.symm.trans e⟩
  have hR := R.hasSourceGenus hgenus
  have hS := S.hasSourceGenus htarget
  rcases hkind with hanalytic | ⟨q, q', k, hTeich⟩
  · have hbihol := (analyticHomeomorph_iff_sourceBiholomorphic
      R.toRiemannAtlas S.toRiemannAtlas f₀).mp hanalytic
    have hc1 := (LiZhongQC.isKQCRS_one_iff f₀).2 hbihol
    have hqc : LiZhongQC.IsQCRS f₀ := ⟨1, hc1⟩
    have hmax : LiZhongQC.maxDilatationRS f₀ = 1 :=
      le_antisymm (by simpa using LiZhongQC.maxDilatationRS_le hc1)
        (LiZhongQC.s29_m_one_le_maxDilatationRS hqc)
    have hext : LiZhongQC.IsExtremalInHomotopyClass f₀ :=
      ⟨hqc, fun f hf _ => hmax.le.trans (LiZhongQC.s29_m_one_le_maxDilatationRS hf)⟩
    refine ⟨hext, fun f hf hhom => ⟨hext.2 f hf hhom, ?_⟩⟩
    constructor
    · intro heq
      apply Homeomorph.ext
      intro x
      exact congrFun (LiZhongQC.conformal_unique_extremal hg hR hS hbihol hf hhom
        (heq.trans hmax)) x
    · intro heq
      subst f
      rfl
  · refine ⟨(LiZhongQC.teichmullerMap_isExtremal hg hR hS hTeich).1, ?_⟩
    intro f hf hhom
    obtain ⟨hbound, hrigid⟩ := LiZhongQC.thm26_2_uniqueness hg hR hS hTeich hf hhom
    have hmax := (LiZhongQC.teichmullerMap_beltrami hTeich).2
    refine ⟨hmax.le.trans hbound, ?_⟩
    constructor
    · intro heq
      apply Homeomorph.ext
      intro x
      exact congrFun (hrigid (heq.trans hmax)) x
    · intro heq
      subst f
      rfl

/-- Every actual QC homeomorphism between the original closed surfaces is homotopic
to a unique extremal map, which is conformal or a Teichmüller map with genuine
initial and terminal quadratic differentials on those original atlases. -/
theorem exists_unique_teichmuller_extremal
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) (f : X ≃ₜ Y)
    (hf :
      letI := R.toRiemannAtlas.toChartedSpace
      letI := S.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsQCRS f) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := S.toRiemannAtlas.toChartedSpace
    ∃ f₀ : X ≃ₜ Y, ContinuousMap.Homotopic (f : C(X, Y)) (f₀ : C(X, Y)) ∧
      (RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f₀ ∨
        ∃ (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
          (q' : HolomorphicQuadraticDifferential S.toRiemannAtlas) (k : ℝ),
            LiZhongQC.IsTeichmullerMap f₀ q q' k) ∧
      LiZhongQC.IsExtremalInHomotopyClass f₀ ∧
      ∀ h : X ≃ₜ Y, LiZhongQC.IsExtremalInHomotopyClass h →
        ContinuousMap.Homotopic (f : C(X, Y)) (h : C(X, Y)) → h = f₀ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := S.toRiemannAtlas.isManifold
  let := R.t2Space
  let := S.t2Space
  let := R.connectedSpace
  let := S.connectedSpace
  have htarget : S.HasGenus g := by
    obtain ⟨e⟩ := hgenus
    exact ⟨f.symm.trans e⟩
  have hR := R.hasSourceGenus hgenus
  have hS := S.hasSourceGenus htarget
  obtain ⟨Γ₀, p₀, _, _, hp₀⟩ := LiZhongQC.s22hg_exists_fuchsian_uniformization hg hR
  obtain ⟨Γ₁, p₁, _, _, hp₁⟩ := LiZhongQC.s22hg_exists_fuchsian_uniformization hg hS
  obtain ⟨f₀, hhom, hkind, hext, huniq⟩ :=
    LiZhongQC.thm27_2_existence_qc_of_uniformization hg hR hS f hf hp₀ hp₁
  refine ⟨f₀, hhom, ?_, hext, ?_⟩
  · rcases hkind with hbihol | ⟨q, q', k, hTeich⟩
    · exact Or.inl ((analyticHomeomorph_iff_sourceBiholomorphic
        R.toRiemannAtlas S.toRiemannAtlas f₀).mpr hbihol)
    · exact Or.inr ⟨⟨q, hTeich.initial⟩, ⟨q', hTeich.terminal⟩, k, hTeich⟩
  · intro h hh hfh
    apply Homeomorph.ext
    intro x
    exact congrFun (huniq h hh hfh) x

end LowDimensionalTopology.Geometry.Surfaces.ClosedRiemannSurface

namespace LowDimensionalTopology.Geometry.Teichmuller.MarkedRiemannSurface

open Surfaces

universe u

/-- The original smooth positive marking has a unique extremal representative in
its actual homotopy class, on the same target surface and original complex atlas. -/
theorem exists_unique_extremal
    {X : Type u} [TopologicalSpace X] {R : ClosedRiemannSurface X}
    (M : MarkedRiemannSurface.{u, u} R) {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := M.surface.toRiemannAtlas.toChartedSpace
    ∃ f₀ : X ≃ₜ M.carrier,
      ContinuousMap.Homotopic (M.marking.toHomeomorph : C(X, M.carrier))
        (f₀ : C(X, M.carrier)) ∧
      (RiemannAnalyticMap R.toRiemannAtlas M.surface.toRiemannAtlas f₀ ∨
        ∃ (q : HolomorphicQuadraticDifferential R.toRiemannAtlas)
          (q' : HolomorphicQuadraticDifferential M.surface.toRiemannAtlas) (k : ℝ),
            LiZhongQC.IsTeichmullerMap f₀ q q' k) ∧
      LiZhongQC.IsExtremalInHomotopyClass f₀ ∧
      ∀ h : X ≃ₜ M.carrier, LiZhongQC.IsExtremalInHomotopyClass h →
        ContinuousMap.Homotopic (M.marking.toHomeomorph : C(X, M.carrier))
          (h : C(X, M.carrier)) → h = f₀ := by
  let := R.compactSpace
  have hqc := M.marking.isQCRS_of_compact M.orientation_preserving
  exact R.exists_unique_teichmuller_extremal M.surface hg hgenus M.marking.toHomeomorph hqc

end LowDimensionalTopology.Geometry.Teichmuller.MarkedRiemannSurface
