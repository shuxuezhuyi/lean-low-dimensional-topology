module

public import LowDimensionalTopology.Unproved.Teichmuller.QuadraticSmoothCarrierInputs
public import LowDimensionalTopology.Unproved.Teichmuller.QuadraticGeodesicSourceSmoothTrace
public import LowDimensionalTopology.Geometry.Teichmuller.NativeQuadraticLiftedFiniteMinimum
public import LowDimensionalTopology.Geometry.Teichmuller.NativeQuadraticFiniteTraceLength
public import LowDimensionalTopology.Geometry.Teichmuller.NativeLiftedQuadraticIntervalLength
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticGlobalMinimizer
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticProjectionDistance
public import LowDimensionalTopology.Geometry.Teichmuller.QuadraticGeodesicPolygonConsumers
public import Mathlib.Topology.Subpath

/-!
# The actual smooth quadratic path carrier and local geodesics

The same native lifted differential is used for both path infima. Explicit
classical arc-factorization and smooth-approximation inputs retain their
unproved status; the length comparison uses the original two path functions.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal NNReal ContDiff Manifold

namespace LowDimensionalTopology.Geometry.Teichmuller
open Surfaces LiZhongQC LowDimensionalTopology.Unproved.Teichmuller

/-- The actual same-trace smooth curves have equal lengths, using the
explicit common-arc input and their own absolutely continuous parametrizations. -/
theorem native_sameTrace_length_eq_of_common_arc
    (hArc : NativeCommonMonotoneArc)
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (_hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X} :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (α β : Path a b), a ≠ b →
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface α →
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface β →
        NativePathHasIntervalFibers α → NativePathHasIntervalFibers β →
        Set.range α = Set.range β →
        phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) α =
          phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) β := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
    (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b α β hab hαSmooth hβSmooth hαFib hβFib htrace
  exact native_finite_sameTrace_length_eq_of_common_arc hArc R q hp α β hab
    (quadraticLengthPath_lt_top_of_piecewiseSmooth upperHalfNativeSurface qH α hαSmooth)
    (quadraticLengthPath_lt_top_of_piecewiseSmooth upperHalfNativeSurface qH β hβSmooth)
    hαFib hβFib htrace

private theorem isPhiGeodesic_subpath_of_lt
    {S : Type} [TopologicalSpace S] [ChartedSpace ℂ S] (q : S → ℂ → ℂ)
    {a b : S} (γ : Path a b) (hγ : IsPhiGeodesicRS q γ)
    (s t : unitInterval) (hst : s < t) : IsPhiGeodesicRS q (γ.subpath s t) := by
  let δ := γ.subpath s t
  let l : ℝ := (t : ℝ) - (s : ℝ)
  let A : ℝ → ℝ := fun u => l * u + (s : ℝ)
  have hl : 0 < l := sub_pos.mpr hst
  have hcomb (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
      (Icc.convexComb s t ⟨u, hu⟩ : ℝ) = A u := by
    rw [Icc.coe_convexComb]
    dsimp only [A, l]
    ring
  have hA : ∀ u ∈ Icc (0 : ℝ) 1, A u ∈ Icc (0 : ℝ) 1 := by
    intro u hu
    rw [← hcomb u hu]
    exact (Icc.convexComb s t ⟨u, hu⟩).property
  have hext : ∀ u ∈ Icc (0 : ℝ) 1, δ.extend u = γ.extend (A u) := by
    intro u hu
    rw [Path.extend_apply δ hu]
    change γ (Icc.convexComb s t ⟨u, hu⟩) = γ.extend (A u)
    rw [Path.extend_apply γ (hA u hu)]
    exact congrArg (fun v : unitInterval => γ v) (Subtype.ext (hcomb u hu))
  intro r₀ hr₀
  obtain ⟨d, hd, hloc⟩ := hγ (A r₀) (hA r₀ hr₀)
  have hcancel : l * (d / l) = d := by field_simp [hl.ne']
  refine ⟨d / l, div_pos hd hl, ?_⟩
  intro x hx y hy hleft hxy hright
  have hxA : A r₀ - d < A x := by
    have h := mul_lt_mul_of_pos_left hleft hl
    dsimp only [A]
    nlinarith [hcancel]
  have hyA : A y < A r₀ + d := by
    have h := mul_lt_mul_of_pos_left hright hl
    dsimp only [A]
    nlinarith [hcancel]
  have hxyA : A x < A y := by
    dsimp only [A]
    linarith [mul_lt_mul_of_pos_left hxy hl]
  have hold := hloc (A x) (hA x hx) (A y) (hA y hy) hxA hxyA hyA
  apply le_antisymm
  · have hup := s25i_transport (q := q) γ δ hl hxy.le (fun u hu =>
      hext u ⟨hx.1.trans hu.1, hu.2.trans hy.2⟩)
    change phiLengthOn q δ x y ≤ phiLengthOn q γ (A x) (A y) at hup
    rw [hold, ← hext x hx, ← hext y hy] at hup
    exact hup
  · obtain ⟨η, _, hη⟩ := s25i_subpath_length (q := q) δ hx.1 hxy hy.2
    exact (iInf_le (fun ζ : Path (δ.extend x) (δ.extend y) => phiLengthPath q ζ) η).trans hη

private theorem native_geodesic_hasIntervalFibers
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
      ∀ {a b : UpperHalfPlane} (L : Path a b),
        IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) L → NativePathHasIntervalFibers L := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
    (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b L hgeo s t hst heq u hu
  rcases lt_or_eq_of_le hst with hlt | rfl
  · have hδ := isPhiGeodesic_subpath_of_lt (qH : UpperHalfPlane → ℂ → ℂ) L hgeo s t hlt
    let δLoop : Path (L s) (L s) := (L.subpath s t).cast rfl heq
    have hloopGeo : IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) δLoop := by
      simpa only [δLoop, IsPhiGeodesicRS, phiLengthOn, Path.extend_cast] using hδ
    have hconst := nativeQuadraticGeodesic_loop_constant_of_polygon_inputs
      R q hq hextract hangle hp (L s) δLoop hloopGeo
    have hmem : L u ∈ Set.range (L.subpath s t) := by
      rw [Path.range_subpath_of_le L s t hlt.le]
      exact ⟨u, hu, rfl⟩
    obtain ⟨v, hv⟩ := hmem
    have hvconst : (L.subpath s t) v = L s := hconst v
    exact hv.symm.trans hvconst
  · have hus : u = s := le_antisymm hu.2 hu.1
    rw [hus]

/-- On the source-smooth carrier, local geodesicity is equivalent to the
actual global minimum, under the explicit geometric and classical inputs. -/
theorem native_sourceSmooth_isPhiGeodesic_iff_globalMinimizer
    (hArc : NativeCommonMonotoneArc) (happrox : NativeQuadraticSmoothCofinality)
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (g : ℕ) (hg : 2 ≤ g) (hgenus : R.HasGenus g)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hbigon : QuadraticGeodesicBigonExtraction R q hq (Γ := Γ) (p := p))
    (hextract : QuadraticGeodesicFinitePolygonExtraction R q hq (Γ := Γ) (p := p))
    (hangle : QuadraticGeodesicLocalAngleBound R q hq (Γ := Γ) (p := p)) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ {a b : UpperHalfPlane} (L : Path a b),
        HasPiecewiseSmoothChartSubdivision upperHalfNativeSurface L →
        (IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) L ↔
          IsGlobalQuadraticMinimizer upperHalfNativeSurface qH L) := by
  classical
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
    (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b L hSmooth
  constructor
  · intro hgeo
    by_cases hab : a = b
    · subst b
      have hconst := nativeQuadraticGeodesic_loop_constant_of_polygon_inputs
        R q hq hextract hangle hp a L hgeo
      have hL : L = Path.refl a := by
        apply Path.ext
        funext u
        exact hconst u
      rw [hL]
      exact isGlobalQuadraticMinimizer_refl upperHalfNativeSurface qH a
    · obtain ⟨κ, hκGeo, hκFinite, hκMin⟩ :=
        exists_native_lifted_finite_geodesic_minimum R q hq hp a b
      have htrace : Set.range L = Set.range κ :=
        native_quadratic_geodesic_range_eq_of_bigon_inputs
          R q hq hbigon hangle hp L κ hab hgeo hκGeo
      have hLFib := native_geodesic_hasIntervalFibers R q hq hextract hangle hp L hgeo
      have hκFib := native_geodesic_hasIntervalFibers R q hq hextract hangle hp κ hκGeo
      have hlen := native_finite_sameTrace_length_eq_of_common_arc hArc R q hp
        L κ hab (quadraticLengthPath_lt_top_of_piecewiseSmooth
          upperHalfNativeSurface qH L hSmooth) hκFinite hLFib hκFib htrace
      apply (isGlobalQuadraticMinimizer_iff_length_le upperHalfNativeSurface qH L).mpr
      refine ⟨hSmooth, fun δ _hδ => ?_⟩
      rw [hlen]
      exact hκMin δ
  · intro hmin
    have hdist : piecewiseSmoothQuadraticDistance upperHalfNativeSurface qH a b =
        phiDistRS (qH : UpperHalfPlane → ℂ → ℂ) a b := by
      apply le_antisymm
      · change piecewiseSmoothQuadraticDistance upperHalfNativeSurface qH a b ≤
          ⨅ δ : Path a b, phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) δ
        refine le_iInf fun δ => ENNReal.le_of_forall_pos_le_add fun ε hε hδfin => ?_
        obtain ⟨η, hηSmooth, hη⟩ :=
          happrox R g hg hgenus q hq (Γ := Γ) (p := p) hp δ hδfin ε hε
        exact (piecewiseSmoothQuadraticDistance_le_length upperHalfNativeSurface qH η hηSmooth).trans hη
      · exact phiDistRS_le_piecewiseSmoothQuadraticDistance upperHalfNativeSurface qH a b
    have hfinite := quadraticLengthPath_lt_top_of_piecewiseSmooth upperHalfNativeSurface qH L hSmooth
    have hall : ∀ δ : Path a b,
        phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) L ≤
          phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) δ := by
      intro δ
      rw [hmin.2, hdist]
      exact iInf_le (fun η : Path a b => phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) η) δ
    exact native_finite_allPathMinimum_isPhiGeodesic R q hq hp L hfinite hall

/-- The actual finite geodesic trace has a source-smooth shortest representative
with the unique local-geodesic range, using only its precise trace regularity. -/
theorem native_sourceSmooth_lifted_geodesic_exists_unique_minimum
    (hArc : NativeCommonMonotoneArc)
    {X : Type} [TopologicalSpace X] (R : ClosedRiemannSurface X)
    (g : ℕ) (_hg : 2 ≤ g) (_hgenus : R.HasGenus g)
    (q : HolomorphicQuadraticDifferential R.toRiemannAtlas) (hq : q ≠ 0)
    {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℝ)} {p : UpperHalfPlane → X}
    (hregular : QuadraticGeodesicSourceSmoothTrace R q hq (Γ := Γ) (p := p))
    (hbigon : QuadraticGeodesicBigonExtraction R q hq (Γ := Γ) (p := p))
    (hextract : QuadraticGeodesicFinitePolygonExtraction R q hq (Γ := Γ) (p := p))
    (hangle : QuadraticGeodesicLocalAngleBound R q hq (Γ := Γ) (p := p)) :
    letI := R.toRiemannAtlas.toChartedSpace
    letI := R.toRiemannAtlas.isManifold
    ∀ hp : IsUniformization Γ p,
      let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
        (utm_liftQD_differentiableOn q.property hp)
      letI := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
      ∀ a b : UpperHalfPlane, a ≠ b → ∃ δ : Path a b,
        IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) δ ∧
        IsGlobalQuadraticMinimizer upperHalfNativeSurface qH δ ∧
        ∀ η : Path a b, IsPhiGeodesicRS (qH : UpperHalfPlane → ℂ → ℂ) η →
          Set.range δ = Set.range η := by
  let := R.toRiemannAtlas.toChartedSpace
  let := R.toRiemannAtlas.isManifold
  intro hp
  let qH := upperHalfNativeQuadratic (utm_liftQD (q : X → ℂ → ℂ) p)
    (utm_liftQD_differentiableOn q.property hp)
  let := upperHalfNativeSurface.toRiemannAtlas.toChartedSpace
  dsimp only
  intro a b hab
  obtain ⟨γ, hγGeo, hγFinite, hγMin⟩ :=
    exists_native_lifted_finite_geodesic_minimum R q hq hp a b
  have hγFib := native_geodesic_hasIntervalFibers R q hq hextract hangle hp γ hγGeo
  obtain ⟨δ, hδSmooth, hδFib, htrace⟩ :=
    hregular hp γ hab hγFinite hγGeo hγFib
  have hδFinite := quadraticLengthPath_lt_top_of_piecewiseSmooth
    upperHalfNativeSurface qH δ hδSmooth
  have hlength := native_finite_sameTrace_length_eq_of_common_arc hArc R q hp
    δ γ hab hδFinite hγFinite hδFib hγFib htrace
  have hδMin (η : Path a b) :
      phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) δ ≤
        phiLengthPath (qH : UpperHalfPlane → ℂ → ℂ) η :=
    hlength.trans_le (hγMin η)
  have hδGeo := native_finite_allPathMinimum_isPhiGeodesic R q hq hp δ hδFinite hδMin
  have hδSmoothMin : IsGlobalQuadraticMinimizer upperHalfNativeSurface qH δ :=
    (isGlobalQuadraticMinimizer_iff_length_le upperHalfNativeSurface qH δ).mpr
      ⟨hδSmooth, fun η _hη => hδMin η⟩
  refine ⟨δ, hδGeo, hδSmoothMin, ?_⟩
  intro η hη
  exact native_quadratic_geodesic_range_eq_of_bigon_inputs
    R q hq hbigon hangle hp δ η hab hδGeo hη

end LowDimensionalTopology.Geometry.Teichmuller
