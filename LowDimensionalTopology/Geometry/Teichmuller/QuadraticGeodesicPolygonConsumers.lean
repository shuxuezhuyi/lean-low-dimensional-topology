module

public import LowDimensionalTopology.Geometry.Teichmuller.ActualQuadraticGeodesicLift
public import LowDimensionalTopology.Unproved.Teichmuller.QuadraticGeodesicPolygonInputs
public import LowDimensionalTopology.Geometry.Teichmuller.NativeQuadraticBigonUniqueness
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Data.Set.Card

/-!
# Loop exclusion and original homotopy-class traces from finite geometry

The existing polygon-angle theorem is applied to the actual finite polygon
supplied by the extraction input. The separate local angle input excludes
deficient angles outside its joining vertices. Covering lifts then handle
both equal and different lifted endpoints of the original homotopy class.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped Real ENNReal NNReal

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC
open LowDimensionalTopology.Unproved.Teichmuller

/-- Every actual native lifted local-geodesic loop is constant, using the
finite polygon extraction and local corner-angle inputs separately. -/
theorem nativeQuadraticGeodesic_loop_constant_of_polygon_inputs
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hextract : QuadraticGeodesicFinitePolygonExtraction R q hq (Γ := Γ) (p := p))
    (hangle : QuadraticGeodesicLocalAngleBound R q hq (Γ := Γ) (p := p)) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ (z : UpperHalfPlane) (δ : Path z z),
        IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) δ → ∀ u, δ u = z := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro z δ hδ u
  by_contra hne
  have hclose : δ.extend 0 = δ.extend 1 := by simp
  have hnon : ∃ v ∈ Icc (0 : ℝ) 1, δ.extend v ≠ δ.extend 0 := by
    refine ⟨(u : ℝ), u.property, ?_⟩
    simpa only [Path.extend_apply δ u.property, Path.extend_zero] using hne
  obtain ⟨c, r, hr, hmap, n, hn, hdata⟩ :=
    hextract hp δ hδ 0 1 le_rfl zero_lt_one le_rfl hclose hnon
  let := hn
  obtain ⟨P, E, _htrace, hE, hcorners⟩ := hdata
  let φ : ℂ → ℂ := fun w => (r : ℂ) ^ 2 * ψ (c + (r : ℂ) * w)
  have hA : Differentiable ℂ (fun w : ℂ => c + (r : ℂ) * w) := by fun_prop
  have hφ : DifferentiableOn ℂ φ unitDisc :=
    ((utm_liftQD_differentiableOn q.property hp).comp hA.differentiableOn hmap).const_mul _
  have hhalf : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hφne : ∃ w ∈ unitDisc, φ w ≠ 0 := by
    refine ⟨P.side 0 (1 / 2), ?_, ?_⟩
    · apply P.closure_sub
      apply frontier_subset_closure
      rw [P.frontier_eq]
      exact mem_iUnion.mpr ⟨0, 1 / 2, Ioo_subset_Icc_self hhalf, rfl⟩
    · obtain ⟨θ, hθ⟩ := (P.side_straight 0).1
      exact (mul_ne_zero_iff.mp (hθ (1 / 2) hhalf).2.2.1).1
  let S : Set (Fin n) := {j | ∃ m : ℕ,
    meromorphicOrderAt φ (P.vert j) = (m : ℤ) ∧ P.angle j < 2 * π / ((m : ℝ) + 2)}
  have hcount : 3 ≤ S.ncard := thm25_2_polygon hφ hφne P
  have hsub : S ⊆ (E : Set (Fin n)) := by
    intro j hj
    by_contra hjE
    obtain ⟨m, hm, hsmall⟩ := hj
    have hlarge := hangle hp δ hδ c r hr hmap n P j 0 1 (hcorners j hjE) m hm
    exact (not_lt_of_ge hlarge) hsmall
  have hupper : S.ncard ≤ 2 := by
    calc S.ncard ≤ (E : Set (Fin n)).ncard := Set.ncard_le_ncard hsub
      _ = E.card := Set.ncard_coe_finset E
      _ ≤ 2 := hE
  omega

/-- In an original fixed endpoint homotopy class, all local quadratic
geodesics have the same range, including when the original endpoints agree. -/
theorem phiGeodesic_range_eq_of_homotopic_of_polygon_inputs
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (g : ℕ) (_hg : 2 ≤ g) (_hgenus : R.HasGenus g)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hbigon : QuadraticGeodesicBigonExtraction R q hq (Γ := Γ) (p := p))
    (hextract : QuadraticGeodesicFinitePolygonExtraction R q hq (Γ := Γ) (p := p))
    (hangle : QuadraticGeodesicLocalAngleBound R q hq (Γ := Γ) (p := p)) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ _hp : IsUniformization Γ p,
      ∀ {a b : X} (α β : Path a b),
        IsPhiGeodesicRS (q : X → ℂ → ℂ) α →
        IsPhiGeodesicRS (q : X → ℂ → ℂ) β →
        α.Homotopic β → Set.range α = Set.range β := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp a b α β hα hβ hhom
  let ψ : ℂ → ℂ := utm_liftQD (q : X → ℂ → ℂ) p
  let qH := upperHalfNativeQuadratic ψ (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  obtain ⟨z₀, hz₀⟩ := hp.2.2.1 a
  have hα0 : (α : C(unitInterval, X)) 0 = p z₀ := by
    rw [hz₀]
    exact α.source
  have hβ0 : (β : C(unitInterval, X)) 0 = p z₀ := by
    rw [hz₀]
    exact β.source
  let A : C(unitInterval, UpperHalfPlane) :=
    hp.1.liftPath (α : C(unitInterval, X)) z₀ hα0
  let B : C(unitInterval, UpperHalfPlane) :=
    hp.1.liftPath (β : C(unitInterval, X)) z₀ hβ0
  have hA0 : A 0 = z₀ := hp.1.liftPath_zero (α : C(unitInterval, X)) z₀ hα0
  have hB0 : B 0 = z₀ := hp.1.liftPath_zero (β : C(unitInterval, X)) z₀ hβ0
  have hAlift : ∀ u, p (A u) = α u :=
    fun u => congrFun (hp.1.liftPath_lifts (α : C(unitInterval, X)) z₀ hα0) u
  have hBlift : ∀ u, p (B u) = β u :=
    fun u => congrFun (hp.1.liftPath_lifts (β : C(unitInterval, X)) z₀ hβ0) u
  have hB1A1 : B 1 = A 1 :=
    hp.1.liftPath_apply_one_eq_of_homotopicRel hhom.symm z₀ hβ0 hα0
  let δA : Path (A 0) (A 1) := ⟨A, rfl, rfl⟩
  let δB₀ : Path (B 0) (B 1) := ⟨B, rfl, rfl⟩
  let δB : Path (A 0) (A 1) := δB₀.cast (hA0.trans hB0.symm) hB1A1.symm
  have hδA : IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) δA :=
    isPhiGeodesicRS_actualLift R.toRiemannSurface q hp α A hAlift hα
  have hδB₀ : IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) δB₀ :=
    isPhiGeodesicRS_actualLift R.toRiemannSurface q hp β B hBlift hβ
  have hδB : IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) δB := by
    simpa only [δB, IsPhiGeodesicRS, phiLengthOn, Path.extend_cast] using hδB₀
  by_cases hsame : A 0 = A 1
  · have hδAloop : IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) (δA.cast rfl hsame) := by
      simpa only [IsPhiGeodesicRS, phiLengthOn, Path.extend_cast] using hδA
    have hδBloop : IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) (δB.cast rfl hsame) := by
      simpa only [IsPhiGeodesicRS, phiLengthOn, Path.extend_cast] using hδB
    have hloop := nativeQuadraticGeodesic_loop_constant_of_polygon_inputs R q hq hextract hangle hp
    have hAconst : ∀ u, A u = A 0 := hloop (A 0) (δA.cast rfl hsame) hδAloop
    have hBconst : ∀ u, B u = A 0 := hloop (A 0) (δB.cast rfl hsame) hδBloop
    have heq : (α : unitInterval → X) = (β : unitInterval → X) := by
      funext u
      rw [← hAlift u, ← hBlift u, hAconst u, hBconst u]
    exact congrArg Set.range heq
  · have htraces : Set.range δA = Set.range δB :=
      native_quadratic_geodesic_range_eq_of_bigon_inputs
        R q hq hbigon hangle hp δA δB hsame hδA hδB
    have hAp : (p ∘ δA) = (α : unitInterval → X) := funext hAlift
    have hBp : (p ∘ δB) = (β : unitInterval → X) := funext hBlift
    have hproject := congrArg (fun S : Set UpperHalfPlane => p '' S) htraces
    rw [← Set.range_comp, ← Set.range_comp, hAp, hBp] at hproject
    exact hproject

end LowDimensionalTopology.Geometry.Teichmuller
