module

public import LowDimensionalTopology.Geometry.Teichmuller.BookTeichmullerMaps

/-!
# Formal Teichmüller maps with an independent parameter

The source and target keep their original complex atlases. The coefficient
uses an arbitrary holomorphic quadratic differential and a separate real
parameter. No compactness or normalization by an integral is imposed.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
open Complex Set Filter Topology MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u v

/-- An actual QC homeomorphism with coefficient `k conj(φ)/|φ|` in its
original source charts. Zero parameters and zero differentials are included. -/
def IsFormalTeichmullerMap
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : RiemannAtlas X) (S : RiemannAtlas Y) (f : X ≃ₜ Y) (k : ℝ)
    (φ : HolomorphicQuadraticDifferential R) : Prop :=
  let := R.toChartedSpace
  let := S.toChartedSpace
  0 ≤ k ∧ k < 1 ∧ LiZhongQC.IsQCRS f ∧
    ∀ x : X, ∀ᵐ z ∂(volume.restrict (LiZhongQC.localMapDomain f x)),
      LiZhongQC.complexDilatation (LiZhongQC.localMapExpr f x) z =
        LiZhongQC.teichmullerBeltrami k (φ : X → ℂ → ℂ) x z

/-- Positive real scaling of the differential leaves its Beltrami field
unchanged, including at every zero of the differential. -/
theorem formalBeltrami_pos_smul {X : Type u} (k : ℝ) (q : X → ℂ → ℂ)
    (c : ℝ) (hc : 0 < c) :
    LiZhongQC.teichmullerBeltrami k ((c : ℂ) • q) =
      LiZhongQC.teichmullerBeltrami k q := by
  funext x z
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  simp only [LiZhongQC.teichmullerBeltrami, Pi.smul_apply, smul_eq_mul,
    map_mul, Complex.conj_ofReal, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg hc.le, Complex.ofReal_mul]
  rw [← mul_assoc, mul_comm (k : ℂ) (c : ℂ), mul_assoc,
    mul_div_mul_left _ _ hc']

/-- The formal-map condition is unchanged by any positive real rescaling
of the original quadratic differential. -/
theorem isFormalTeichmullerMap_pos_smul
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : RiemannAtlas X) (S : RiemannAtlas Y) (f : X ≃ₜ Y) (k : ℝ)
    (φ : HolomorphicQuadraticDifferential R) (c : ℝ) (hc : 0 < c) :
    IsFormalTeichmullerMap R S f k ((c : ℂ) • φ) ↔
      IsFormalTeichmullerMap R S f k φ := by
  have heq : LiZhongQC.teichmullerBeltrami k
      (((c : ℂ) • φ : HolomorphicQuadraticDifferential R) : X → ℂ → ℂ) =
      LiZhongQC.teichmullerBeltrami k (φ : X → ℂ → ℂ) :=
    formalBeltrami_pos_smul k (φ : X → ℂ → ℂ) c hc
  dsimp only [IsFormalTeichmullerMap]
  rw [heq]

/-- Identity maps have zero complex dilatation in their actual local charts. -/
theorem identity_local_dilatation_zero
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] :
    ∀ x : X, ∀ᵐ z ∂(volume.restrict (LiZhongQC.localMapDomain (Homeomorph.refl X) x)),
      LiZhongQC.complexDilatation (LiZhongQC.localMapExpr (Homeomorph.refl X) x) z = 0 := by
  intro x
  have hD := LiZhongQC.s23_localMapDomain_isOpen (Homeomorph.refl X).continuous x
  have heq : Set.EqOn (LiZhongQC.localMapExpr (Homeomorph.refl X) x) id
      (LiZhongQC.localMapDomain (Homeomorph.refl X) x) := by
    intro z hz
    simp only [LiZhongQC.localMapDomain, Set.mem_inter_iff] at hz
    simpa [LiZhongQC.localMapExpr] using (chartAt ℂ x).right_inv hz.1
  refine ae_restrict_of_forall_mem hD.measurableSet fun z hz => ?_
  exact (LiZhongQC.abR_t_complexDilatation_congr hD heq hz).trans
    (LiZhongQC.nxT_complexDilatation_id z)

/-- If the parameter or differential vanishes, formal maps are exactly
analytic homeomorphisms on the unchanged source and target. -/
theorem isFormalTeichmullerMap_iff_analytic_of_zero
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : RiemannAtlas X) (S : RiemannAtlas Y) (f : X ≃ₜ Y) (k : ℝ)
    (φ : HolomorphicQuadraticDifferential R) (hk₀ : 0 ≤ k) (hk₁ : k < 1)
    (hz : k = 0 ∨ φ = 0) :
    IsFormalTeichmullerMap R S f k φ ↔ RiemannAnalyticMap R S f := by
  let := R.toChartedSpace
  let := S.toChartedSpace
  let := R.isManifold
  let := S.isManifold
  have hzero (x : X) (z : ℂ) :
      LiZhongQC.teichmullerBeltrami k (φ : X → ℂ → ℂ) x z = 0 := by
    rcases hz with hk | hφ
    · simp [LiZhongQC.teichmullerBeltrami, hk]
    · simp [LiZhongQC.teichmullerBeltrami, hφ]
  dsimp only [IsFormalTeichmullerMap]
  constructor
  · rintro ⟨_, _, hf, hμ⟩
    have hBel := LiZhongQC.teichmullerBeltrami_isBeltramiDifferential φ.property hk₀ hk₁
    have hid : ∀ x : X, ∀ᵐ z ∂(volume.restrict
        (LiZhongQC.localMapDomain (Homeomorph.refl X) x)),
        LiZhongQC.complexDilatation (LiZhongQC.localMapExpr (Homeomorph.refl X) x) z =
          LiZhongQC.teichmullerBeltrami k (φ : X → ℂ → ℂ) x z := by
      intro x
      simpa only [hzero] using identity_local_dilatation_zero (X := X) x
    have hb := sameBeltrami_biholomorphic LiZhongQC.isQCRS_refl hf hk₁ hBel hid hμ
    have he : (Homeomorph.refl X).symm.trans f = f := by ext x; rfl
    exact (analyticHomeomorph_iff_sourceBiholomorphic R S f).mpr (he ▸ hb)
  · intro ha
    have hK := (LiZhongQC.isKQCRS_one_iff f).mpr
      ((analyticHomeomorph_iff_sourceBiholomorphic R S f).mp ha)
    refine ⟨hk₀, hk₁, ⟨1, hK⟩, ?_⟩
    intro x
    filter_upwards [(LiZhongQC.isKQC_maxDilatation_le (hK.2 x)).2] with z hzμ
    rw [hzero]
    exact norm_eq_zero.mp (le_antisymm (by simpa using hzμ) (norm_nonneg _))

/-- The actual normalized coefficient interface is exactly the formal-map
condition at the integral norm parameter, on the same original surfaces. -/
theorem bookCoefficient_iff_formalTeichmullerMap
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y) (f : X ≃ₜ Y)
    (φ : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (hφ : φ ∈ QuadraticL1.openUnitBall R) :
    (let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsQCRS f ∧ HasBookTeichmullerCoefficient R S f φ) ↔
      IsFormalTeichmullerMap R.toRiemannAtlas S.toRiemannAtlas f
        (QuadraticL1.bookNorm R φ) φ := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  have hk₀ : 0 ≤ QuadraticL1.bookNorm R φ := by
    unfold QuadraticL1.bookNorm
    positivity
  have hk₁ := (QuadraticL1.mem_openUnitBall R φ).mp hφ
  constructor
  · rintro ⟨hf, hμ⟩
    exact ⟨hk₀, hk₁, hf, hμ⟩
  · rintro ⟨_, _, hf, hμ⟩
    exact ⟨hf, hμ⟩

end LowDimensionalTopology.Geometry.Teichmuller
