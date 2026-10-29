module

public import LowDimensionalTopology.Geometry.Teichmuller.TeichmullerExtremalMaps
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticL1Norm
public import LowDimensionalTopology.Geometry.Teichmuller.SameBeltramiBiholomorph

/-!
# The literal book definition of a Teichmüller map

The coefficient is `‖φ‖₁ conj(φ)/|φ|`, with the norm `2 ∫ |φ|` on the original
atlas. A QC map with this coefficient acquires genuine natural parameters and
an actual terminal quadratic differential by comparison with the constructed
canonical deformation, followed by biholomorphic transport.

The analytic source results are due to Wu Xiaobin, Li-Zhong-QC-formalization,
commit `1c0d5473c020b66ed5106331a38a61536760b9b2` (Apache-2.0); see
`THIRD_PARTY_NOTICES.md`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Complex Set Filter Topology MeasureTheory
open scoped Manifold ContDiff ComplexConjugate

namespace LowDimensionalTopology.Geometry.Teichmuller

open Surfaces
universe u v

/-- The literal normalized Beltrami form defining a book Teichmüller map for `φ`.
The QC condition is supplied separately for the actual homeomorphism. -/
def HasBookTeichmullerCoefficient
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y) (f : X ≃ₜ Y)
    (φ : HolomorphicQuadraticDifferential R.toRiemannAtlas) : Prop :=
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  ∀ x : X, ∀ᵐ z ∂(volume.restrict (LiZhongQC.localMapDomain f x)),
    LiZhongQC.complexDilatation (LiZhongQC.localMapExpr f x) z =
      (QuadraticL1.bookNorm R φ : ℂ) * conj ((φ : X → ℂ → ℂ) x z) /
        (‖(φ : X → ℂ → ℂ) x z‖ : ℂ)

private theorem identity_beltrami_zero
    {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X] :
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

/-- Every actual QC map having the book coefficient is conformal at parameter
zero, or has the full natural-parameter structure with a genuinely constructed
terminal differential on its original target. -/
theorem bookCoefficient_geometric
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y)
    (φ : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (hφ : φ ∈ QuadraticL1.openUnitBall R) (f : X ≃ₜ Y)
    (hf :
      let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsQCRS f)
    (hμ : HasBookTeichmullerCoefficient R S f φ) :
    let := R.toRiemannAtlas.toChartedSpace
    let := S.toRiemannAtlas.toChartedSpace
    (φ = 0 ∧ RiemannAnalyticMap R.toRiemannAtlas S.toRiemannAtlas f) ∨
      ∃ q' : HolomorphicQuadraticDifferential S.toRiemannAtlas,
        LiZhongQC.IsTeichmullerMap f φ q' (QuadraticL1.bookNorm R φ) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := S.toRiemannAtlas.isManifold
  let := R.t2Space
  let := S.t2Space
  let := R.connectedSpace
  let := S.connectedSpace
  let := R.compactSpace
  let := S.compactSpace
  have hk0 : 0 ≤ QuadraticL1.bookNorm R φ := by
    unfold QuadraticL1.bookNorm
    positivity
  have hk1 := (QuadraticL1.mem_openUnitBall R φ).mp hφ
  have hBel := LiZhongQC.teichmullerBeltrami_isBeltramiDifferential φ.property hk0 hk1
  have hμ' : ∀ x : X, ∀ᵐ z ∂(volume.restrict (LiZhongQC.localMapDomain f x)),
      LiZhongQC.complexDilatation (LiZhongQC.localMapExpr f x) z =
        LiZhongQC.teichmullerBeltrami (QuadraticL1.bookNorm R φ) φ x z := hμ
  by_cases hz : φ = 0
  · have hid : ∀ x : X, ∀ᵐ z ∂(volume.restrict
        (LiZhongQC.localMapDomain (Homeomorph.refl X) x)),
        LiZhongQC.complexDilatation (LiZhongQC.localMapExpr (Homeomorph.refl X) x) z =
          LiZhongQC.teichmullerBeltrami (QuadraticL1.bookNorm R φ) φ x z := by
      intro x
      filter_upwards [identity_beltrami_zero (X := X) x] with z hzid
      simpa only [hz, Submodule.coe_zero, Pi.zero_apply,
        LiZhongQC.teichmullerBeltrami, map_zero, mul_zero, zero_div] using hzid
    have hb := sameBeltrami_biholomorphic LiZhongQC.isQCRS_refl hf hk1 hBel hid hμ'
    have he : (Homeomorph.refl X).symm.trans f = f := by ext x; rfl
    exact Or.inl ⟨hz, (analyticHomeomorph_iff_sourceBiholomorphic
      R.toRiemannAtlas S.toRiemannAtlas f).mpr (he ▸ hb)⟩
  · have hz' : (φ : X → ℂ → ℂ) ≠ 0 := fun h => hz (Subtype.ext h)
    obtain ⟨D, e, q', hDef⟩ := LiZhongQC.exists_teichDeformation φ.property hz' hk0 hk1
    have hT := LiZhongQC.teichDeformation_isTeichmullerMap hDef
    have hc := sameBeltrami_biholomorphic hT.qc hf hk1 hBel
      (LiZhongQC.teichmullerMap_beltrami hT).1 hμ'
    obtain ⟨q'', hTrans⟩ := LiZhongQC.utm_x_teichmullerMap_trans hT hc
    have he : e.trans (e.symm.trans f) = f := by
      ext x
      simp only [Homeomorph.trans_apply, Homeomorph.symm_apply_apply]
    rw [he] at hTrans
    exact Or.inr ⟨⟨q'', hTrans.terminal⟩, hTrans⟩

/-- The actual deformation witness has precisely the normalized book Beltrami
law, with no natural-parameter hypothesis added to the resulting coefficient. -/
theorem deformationPoint_exists_literal_beltrami
    {X : Type u} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (φ : HolomorphicQuadraticDifferential R.toRiemannAtlas) :
    let := R.toRiemannAtlas.toChartedSpace
    ∀ p : LiZhongQC.TeichSpace X,
      LiZhongQC.IsDeformationPoint φ (QuadraticL1.bookNorm R φ) p →
      ∃ (D : LiZhongQC.ClosedRS.{u}) (e : X ≃ₜ D.carrier) (hqc : LiZhongQC.IsQCRS e),
        p = Quot.mk _ ⟨D, e, hqc⟩ ∧
        (∀ x : X, ∀ᵐ z ∂(volume.restrict (LiZhongQC.localMapDomain e x)),
          LiZhongQC.complexDilatation (LiZhongQC.localMapExpr e x) z =
            (QuadraticL1.bookNorm R φ : ℂ) * conj ((φ : X → ℂ → ℂ) x z) /
              (‖(φ : X → ℂ → ℂ) x z‖ : ℂ)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.connectedSpace
  dsimp only
  intro p hp
  obtain ⟨D, e, hqc, q', hDef, he⟩ := hp
  refine ⟨D, e, hqc, he, ?_⟩
  exact (LiZhongQC.teichmullerMap_beltrami
    (LiZhongQC.teichDeformation_isTeichmullerMap hDef)).1

/-- The book coefficient alone suffices for the full extremality and equality
rigidity theorem on the unchanged original surfaces. -/
theorem bookTeichmuller_unique_extremal
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (φ : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (hφ : φ ∈ QuadraticL1.openUnitBall R) (f₀ : X ≃ₜ Y)
    (hf₀ :
      let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsQCRS f₀)
    (hμ : HasBookTeichmullerCoefficient R S f₀ φ) :
    let := R.toRiemannAtlas.toChartedSpace
    let := S.toRiemannAtlas.toChartedSpace
    LiZhongQC.IsExtremalInHomotopyClass f₀ ∧
      ∀ f : X ≃ₜ Y, LiZhongQC.IsQCRS f →
        ContinuousMap.Homotopic (f₀ : C(X, Y)) (f : C(X, Y)) →
          LiZhongQC.maxDilatationRS f₀ ≤ LiZhongQC.maxDilatationRS f ∧
            (LiZhongQC.maxDilatationRS f = LiZhongQC.maxDilatationRS f₀ ↔ f = f₀) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  have hkind := bookCoefficient_geometric R S φ hφ f₀ hf₀ hμ
  apply R.teichmullerMap_unique_extremal S hg hgenus
  rcases hkind with ⟨_, ha⟩ | ⟨q', hT⟩
  · exact Or.inl ha
  · exact Or.inr ⟨φ, q', QuadraticL1.bookNorm R φ, hT⟩

/-- The actual maximal dilatation of a book-defined map has the precise book
normalization, including the zero/conformal parameter. -/
theorem bookCoefficient_maxDilatation
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y)
    (φ : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (hφ : φ ∈ QuadraticL1.openUnitBall R) (f : X ≃ₜ Y)
    (hf :
      let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsQCRS f)
    (hμ : HasBookTeichmullerCoefficient R S f φ) :
    let := R.toRiemannAtlas.toChartedSpace
    let := S.toRiemannAtlas.toChartedSpace
    LiZhongQC.maxDilatationRS f = ENNReal.ofReal
      ((1 + QuadraticL1.bookNorm R φ) / (1 - QuadraticL1.bookNorm R φ)) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  let := S.toRiemannAtlas.isManifold
  let := R.connectedSpace
  rcases bookCoefficient_geometric R S φ hφ f hf hμ with ⟨hz, ha⟩ | ⟨q', hT⟩
  · let Q := HolomorphicQuadraticDifferential R.toRiemannAtlas
    let : NormedAddCommGroup Q := QuadraticL1.normedAddCommGroup R
    have hzero : QuadraticL1.bookNorm R φ = 0 := by
      rw [← QuadraticL1.norm_eq_bookNorm R φ, hz, norm_zero]
    have hb := (analyticHomeomorph_iff_sourceBiholomorphic
      R.toRiemannAtlas S.toRiemannAtlas f).mp ha
    have hmax : LiZhongQC.maxDilatationRS f = 1 :=
      le_antisymm
        (by simpa using LiZhongQC.maxDilatationRS_le ((LiZhongQC.isKQCRS_one_iff f).2 hb))
        (LiZhongQC.s29_m_one_le_maxDilatationRS hf)
    simpa only [hzero, add_zero, sub_zero, div_one, ENNReal.ofReal_one] using hmax
  · exact (LiZhongQC.teichmullerMap_beltrami hT).2

/-- The full extremality and rigidity statement with the literal L1 parameter
visible in the lower bound, rather than hidden behind the name of a map. -/
theorem bookTeichmuller_extremal_formula
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    (R : ClosedRiemannSurface X) (S : ClosedRiemannSurface Y)
    {g : ℕ} (hg : 1 < g) (hgenus : R.HasGenus g)
    (φ : HolomorphicQuadraticDifferential R.toRiemannAtlas)
    (hφ : φ ∈ QuadraticL1.openUnitBall R) (f₀ : X ≃ₜ Y)
    (hf₀ :
      let := R.toRiemannAtlas.toChartedSpace
      let := S.toRiemannAtlas.toChartedSpace
      LiZhongQC.IsQCRS f₀)
    (hμ : HasBookTeichmullerCoefficient R S f₀ φ) :
    let := R.toRiemannAtlas.toChartedSpace
    let := S.toRiemannAtlas.toChartedSpace
    LiZhongQC.maxDilatationRS f₀ = ENNReal.ofReal
        ((1 + QuadraticL1.bookNorm R φ) / (1 - QuadraticL1.bookNorm R φ)) ∧
      LiZhongQC.IsExtremalInHomotopyClass f₀ ∧
      ∀ f : X ≃ₜ Y, LiZhongQC.IsQCRS f →
        ContinuousMap.Homotopic (f₀ : C(X, Y)) (f : C(X, Y)) →
          ENNReal.ofReal ((1 + QuadraticL1.bookNorm R φ) /
            (1 - QuadraticL1.bookNorm R φ)) ≤ LiZhongQC.maxDilatationRS f ∧
          (LiZhongQC.maxDilatationRS f = ENNReal.ofReal
            ((1 + QuadraticL1.bookNorm R φ) / (1 - QuadraticL1.bookNorm R φ)) ↔ f = f₀) := by
  let := R.toRiemannAtlas.toChartedSpace
  let := S.toRiemannAtlas.toChartedSpace
  have hK := bookCoefficient_maxDilatation R S φ hφ f₀ hf₀ hμ
  obtain ⟨hext, hrigid⟩ := bookTeichmuller_unique_extremal R S hg hgenus φ hφ f₀ hf₀ hμ
  refine ⟨hK, hext, ?_⟩
  intro f hf hhom
  obtain ⟨hbound, heq⟩ := hrigid f hf hhom
  refine ⟨hK.symm.le.trans hbound, ?_⟩
  constructor
  · intro h
    exact heq.mp (h.trans hK.symm)
  · intro h
    subst f
    exact hK

end LowDimensionalTopology.Geometry.Teichmuller
