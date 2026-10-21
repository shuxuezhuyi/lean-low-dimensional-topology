module
public import LowDimensionalTopology.Geometry.Mobius.Affine.Basic
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.DiscAnalyticAutomorphisms
public import LowDimensionalTopology.Geometry.Surfaces.Covering.UniversalDeck
public import LowDimensionalTopology.Geometry.Surfaces.Covering.UniversalCover
public import LowDimensionalTopology.Geometry.Mobius.InvariantDisc.InvariantDiscGroups
@[expose] public section
noncomputable section
open Set Metric Filter Topology
open scoped OnePoint ComplexConjugate
namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Euclidean LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Mobius LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace


/-- A continuous lift through an analytic local homeomorphism is analytic in the given
complex atlases, without changing either atlas or assuming an unramified derivative. -/
theorem RiemannAnalyticMap.of_comp_localHomeomorph
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {A : RiemannAtlas X} {B : RiemannAtlas Y} {C : RiemannAtlas Z}
    {f : X → Y} {q : Y → Z} (hq : RiemannAnalyticMap B C q)
    (hql : IsLocalHomeomorph q) (hf : Continuous f)
    (ha : RiemannAnalyticMap A C (q ∘ f)) : RiemannAnalyticMap A B f := by
  rw [riemannAnalyticMap_iff_locally]
  refine ⟨hf, ?_⟩
  intro x
  obtain ⟨e, he, hx⟩ := A.cover x
  obtain ⟨g, hg, hy⟩ := B.cover (f x)
  obtain ⟨b, hb, hz⟩ := C.cover (q (f x))
  obtain ⟨l, hlx, hl⟩ := hql (f x)
  let P := g.symm.trans (l.trans b)
  have hsub : P.source ⊆ riemannChartMapDomain g q b := by
    intro w hw
    change w ∈ g.target ∧ g.symm w ∈ l.source ∧ l (g.symm w) ∈ b.source at hw
    refine ⟨hw.1, ?_⟩
    change q (g.symm w) ∈ b.source
    rw [hl]
    exact hw.2.2
  have hP : AnalyticOnNhd ℂ P P.source := by
    apply AnalyticOnNhd.congr P.open_source
      ((hq.2 g hg b hb).mono hsub)
    intro w _hw
    change b (q (g.symm w)) = b (l (g.symm w))
    rw [hl]
  have hPs : g (f x) ∈ P.source := by
    change g (f x) ∈ g.target ∧ g.symm (g (f x)) ∈ l.source ∧
      l (g.symm (g (f x))) ∈ b.source
    rw [g.left_inv hy, ← hl]
    exact ⟨g.map_source hy, hlx, hz⟩
  have hPv (y : Y) (hyg : y ∈ g.source) : P (g y) = b (q y) := by
    change b (l (g.symm (g y))) = b (q y)
    rw [g.left_inv hyg, ← hl]
  have hi := openPartialHomeomorph_analytic_inverse P hP
  have hai : AnalyticAt ℂ P.symm (b (q (f x))) := by
    rw [← hPv (f x) hy]
    exact hi _ (P.map_source hPs)
  have hforward : AnalyticAt ℂ (riemannChartMap e (q ∘ f) b) (e x) :=
    ha.2 e he b hb (e x) (riemannChartMapDomain_mem e (q ∘ f) b x hx hz)
  have hcompose : AnalyticAt ℂ (P.symm ∘ riemannChartMap e (q ∘ f) b) (e x) := by
    apply AnalyticAt.comp (f := riemannChartMap e (q ∘ f) b) (x := e x) ?_ hforward
    simpa only [riemannChartMap, Function.comp_apply, e.left_inv hx] using hai
  refine ⟨e, he, hx, g, hg, hy, hcompose.congr ?_⟩
  have hnear : ∀ᶠ w in 𝓝 (e x),
      f (e.symm w) ∈ g.source ∧ f (e.symm w) ∈ l.source ∧
        q (f (e.symm w)) ∈ b.source := by
    have ht : Tendsto (f ∘ e.symm) (𝓝 (e x)) (𝓝 (f x)) := by
      have hc := hf.continuousAt.comp (e.continuousAt_symm (e.map_source hx))
      change Tendsto (f ∘ e.symm) (𝓝 (e x)) (𝓝 (f (e.symm (e x)))) at hc
      simpa only [e.left_inv hx] using hc
    exact ht.eventually ((g.open_source.inter (l.open_source.inter
      (b.open_source.preimage hq.1))).mem_nhds ⟨hy, hlx, hz⟩)
  filter_upwards [hnear] with w hw
  let y := f (e.symm w)
  have hgy : g y ∈ P.source := by
    change g y ∈ g.target ∧ g.symm (g y) ∈ l.source ∧ l (g.symm (g y)) ∈ b.source
    rw [g.left_inv hw.1, ← hl]
    exact ⟨g.map_source hw.1, hw.2.1, hw.2.2⟩
  change P.symm (b (q y)) = g y
  rw [← hPv y hw.1, P.left_inv hgy]

/-- Every deck transformation of an analytic cover is analytic in the original source atlas. -/
theorem covering_deck_analytic_of_analytic {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {A : RiemannAtlas E} {B : RiemannAtlas X} {p : E → X}
    (hp : IsCoveringMap p) (ha : RiemannAnalyticMap A B p) (g : deck p) :
    RiemannAnalyticMap A A g.val := by
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_localHomeomorph ha hp.isLocalHomeomorph g.val.continuous
  have he : (p ∘ (g.val : E → E)) = p := g.property
  rw [he]
  exact ha

/-- The genuine extended disc is homeomorphic to the actual complex unit ball by its finite chart. -/
def discFiniteHomeomorph : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc ≃ₜ ball (0 : ℂ) 1 where
  toFun z := ⟨discFiniteChart z, discFiniteChart_target ▸
    discFiniteChart.map_source (discFiniteChart_source.symm ▸ Set.mem_univ z)⟩
  invFun z := discFiniteChart.symm z.val
  left_inv z := discFiniteChart.left_inv (discFiniteChart_source.symm ▸ Set.mem_univ z)
  right_inv z := Subtype.ext (discFiniteChart.right_inv (discFiniteChart_target.symm ▸ z.property))
  continuous_toFun := (continuous_iff_continuousAt.mpr (fun z =>
    discFiniteChart.continuousAt (discFiniteChart_source.symm ▸ Set.mem_univ z))).subtype_mk _
  continuous_invFun := discFiniteChart.continuousOn_symm.comp_continuous continuous_subtype_val
    (fun z => discFiniteChart_target.symm ▸ z.property)

theorem discRiemannSurface_simplyConnected : SimplyConnectedSpace _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
  let : ContractibleSpace (ball (0 : ℂ) 1) := Metric.contractibleSpace_ball zero_lt_one
  exact discFiniteHomeomorph.toHomotopyEquiv.simplyConnectedSpace_iff.mpr inferInstance

/-- The actual analytic deck action on the disc, represented by a homomorphism into the actual Mobius group. -/
def discDeckMobiusHom {X : Type*} [TopologicalSpace X] (B : RiemannAtlas X)
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas B p) :
    deck p →* _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup :=
  discAnalyticActionMobiusHom (deck p).subtype (covering_deck_analytic_of_analytic hp ha)

theorem discDeckMobiusHom_injective {X : Type*} [TopologicalSpace X] (B : RiemannAtlas X)
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas B p) :
    Function.Injective (discDeckMobiusHom B p hp ha) :=
  discAnalyticActionMobiusHom_injective _ _ Subtype.val_injective

theorem discDeckMobiusHom_apply {X : Type*} [TopologicalSpace X] (B : RiemannAtlas X)
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas B p)
    (g : deck p) (z : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    (discDeckMobiusHom B p hp ha g).val z.val = (g • z).val :=
  discAnalyticAutomorphismMobius_apply g.val (covering_deck_analytic_of_analytic hp ha g) z

theorem discDeckMobiusHom_preserves {X : Type*} [TopologicalSpace X] (B : RiemannAtlas X)
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas B p) (g : deck p) :
    (discDeckMobiusHom B p hp ha g).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc :=
  discAnalyticAutomorphismMobius_preserves g.val (covering_deck_analytic_of_analytic hp ha g)

theorem discDeckMobiusRange_invariant {X : Type*} [TopologicalSpace X] (B : RiemannAtlas X)
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas B p)
    (g : (discDeckMobiusHom B p hp ha).range) (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
    (hz : z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) : g • z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
  obtain ⟨d, hd⟩ := g.property
  change g.val.val z ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
  rw [← hd]
  exact (discDeckMobiusHom_preserves B p hp ha d).subset (Set.mem_image_of_mem _ hz)

/-- The actual Mobius image of the disc deck group satisfies the source compact-set definition of discontinuity. -/
theorem discDeckMobiusRange_discontinuous {X : Type*} [TopologicalSpace X] [T2Space X]
    (B : RiemannAtlas X) (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp :
      IsCoveringMap p)
    (ha : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas B p) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn (discDeckMobiusHom B p hp ha).range _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
  let : SimplyConnectedSpace _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := discRiemannSurface_simplyConnected
  let : LocallyPathConnectedSpace _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc :=
    discRiemannSurface.toRiemannAtlas.locallyPathConnectedSpace
  let H := (discDeckMobiusHom B p hp ha).range
  let hInv := discDeckMobiusRange_invariant B p hp ha
  let : MulAction H _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.invariantSubsetMulAction _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc hInv
  apply (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.isMobiusDiscontinuousOn_iff_subtype H
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc hInv).mpr
  let φ := (discDeckMobiusHom B p hp ha).ofInjective (discDeckMobiusHom_injective B p hp ha)
  apply _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsDiscontinuous.transport φ.toEquiv (Homeomorph.refl _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) ?_
    (covering_deck_discontinuous hp)
  intro g z
  apply Subtype.ext
  change (g • z).val = (discDeckMobiusHom B p hp ha g).val z.val
  exact (discDeckMobiusHom_apply B p hp ha g z).symm

/-- No nonidentity element of the actual Mobius deck image fixes a point of the genuine disc. -/
theorem discDeckMobiusRange_no_fixed {X : Type*} [TopologicalSpace X]
    (B : RiemannAtlas X) (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp :
      IsCoveringMap p)
    (ha : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas B p)
    (g : (discDeckMobiusHom B p hp ha).range) (z : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc)
    (hfix : g.val.val z.val = z.val) : g = 1 := by
  let : ConnectedSpace _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := discRiemannSurface.connectedSpace
  obtain ⟨d, hd⟩ := g.property
  have hdFix : d • z = z := by
    apply Subtype.ext
    rw [← discDeckMobiusHom_apply B p hp ha d z, hd]
    exact hfix
  have hd1 := _root_.LowDimensionalTopology.Geometry.Auxiliary.Topology.covering_deck_fixedPoint_eq_one hp d z hdFix
  apply Subtype.ext
  rw [← hd, hd1, map_one]
  rfl



/-- The normalized elliptic disc equation has a genuine fixed point strictly inside the disc. -/
theorem normalized_disc_elliptic_fixed_inside (a c : ℂ)
    (hdet : Complex.normSq a - Complex.normSq c = 1) (ha : a.re ^ 2 < 1) :
    ∃ z : ℂ, ‖z‖ < 1 ∧ _root_.LowDimensionalTopology.Geometry.Hyperbolic.normalizedDiscTransformation a c hdet (z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) = z := by
  have hsq : ‖c‖ ^ 2 < a.im ^ 2 := by
    rw [Complex.normSq_apply] at hdet
    rw [Complex.normSq_eq_norm_sq] at hdet
    nlinarith
  let s : ℝ := Real.sqrt (a.im ^ 2 - ‖c‖ ^ 2)
  have hs : 0 < s := Real.sqrt_pos.mpr (sub_pos.mpr hsq)
  have hs2 : s ^ 2 = a.im ^ 2 - ‖c‖ ^ 2 := Real.sq_sqrt (sub_nonneg.mpr hsq.le)
  obtain ⟨d, hdn, hdq⟩ : ∃ d : ℝ, ‖c‖ < |d| ∧ d ^ 2 - 2 * a.im * d + ‖c‖ ^ 2 = 0 := by
    by_cases hi : 0 ≤ a.im
    · refine ⟨a.im + s, ?_, ?_⟩
      · rw [abs_of_pos (by linarith)]
        have hc := (sq_lt_sq₀ (norm_nonneg c) hi).mp hsq
        linarith
      · nlinarith
    · refine ⟨a.im - s, ?_, ?_⟩
      · rw [abs_of_neg (by linarith)]
        have hc : ‖c‖ < -a.im := (sq_lt_sq₀ (norm_nonneg c) (by linarith)).mp (by nlinarith)
        linarith
      · nlinarith
  have hd : d ≠ 0 := by intro he; simp only [he, abs_zero] at hdn; linarith [norm_nonneg c]
  have hdC : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd
  let z : ℂ := Complex.I * conj c / (d : ℂ)
  have hz : ‖z‖ < 1 := by
    dsimp [z]
    rw [norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_conj, Complex.norm_real]
    exact (div_lt_one (abs_pos.mpr hd)).mpr hdn
  refine ⟨z, hz, ?_⟩
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.normalizedDiscTransformation_of_closedDisc a c z hdet hz.le]
  apply congrArg ((↑) : ℂ → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)
  change (a * z + conj c) / (c * z + conj a) = z
  apply (div_eq_iff (_root_.LowDimensionalTopology.Geometry.Auxiliary.Analysis.discFractional_den_ne_zero hdet
    hz.le)).mpr
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hdq
  dsimp [z]
  apply Complex.ext <;>
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.I_re, Complex.I_im,
      Complex.div_re, Complex.div_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.normSq_ofReal, mul_zero, zero_mul, zero_add]
  · field_simp [hd]
    linear_combination c.re * d ^ 2 * hdq
  · field_simp [hd]
    linear_combination -(c.im * d ^ 2) * hdq

/-- A geometrically elliptic actual Mobius map preserving the unit disc fixes a point in that disc. -/
theorem mobiusElliptic_disc_fixed_inside (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf :
  _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f)
    (hp : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    ∃ z : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc, f.val z.val = z.val := by
  obtain ⟨a, c, hdet, hform⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.complexMobius_disc_normal_form f hp
  obtain ⟨r, _hr0, hr4,
    htrace⟩ := (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_elliptic_iff_squaredTrace_mem_nonnegative_lt_four f
    hf.1).mp hf
  have htrace2 : _root_.LowDimensionalTopology.Geometry.Mobius.mobiusSquaredTrace f = ((4 * a.re ^ 2 : ℝ) : ℂ) :=
    _root_.LowDimensionalTopology.Geometry.Mobius.fractional_squaredTrace_of_normalized_disc (_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusEquivFractionalLinear f) hdet
      (by simpa only [_root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusEquivFractionalLinear_apply] using hform)
  have hre : 4 * a.re ^ 2 = r := Complex.ofReal_injective (htrace2.symm.trans htrace)
  obtain ⟨z, hz, hfix⟩ := normalized_disc_elliptic_fixed_inside a c hdet (by linarith)
  exact ⟨⟨(z : _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex), (_root_.LowDimensionalTopology.Geometry.Hyperbolic.coe_mem_extendedUnitDisc z).mpr hz⟩, by rwa [hform]⟩


/-- The actual Mobius image of an analytic disc covering has no elliptic elements. -/
theorem discDeckMobiusRange_noElliptic {X : Type*} [TopologicalSpace X]
    (B : RiemannAtlas X) (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp :
      IsCoveringMap p)
    (ha : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas B p)
    (f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hf : f ∈ (discDeckMobiusHom B p hp ha).range) : ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f := by
  intro hE
  obtain ⟨d, hd⟩ := hf
  have hpres : f.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := by
    rw [← hd]
    exact discDeckMobiusHom_preserves B p hp ha d
  obtain ⟨z, hz⟩ := mobiusElliptic_disc_fixed_inside f hE hpres
  have he := discDeckMobiusRange_no_fixed B p hp ha (⟨f, ⟨d, hd⟩⟩) z hz
  exact hE.1 (congrArg Subtype.val he)

/-- Analyticity descends through a surjective analytic local homeomorphism in the original
atlases; no derivative nonvanishing hypothesis is introduced. -/
theorem RiemannAnalyticMap.of_comp_surjective_localHomeomorph
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    {A : RiemannAtlas X} {B : RiemannAtlas Y} {C : RiemannAtlas Z}
    {p : X → Y} {f : Y → Z} (hp : RiemannAnalyticMap A B p)
    (hpl : IsLocalHomeomorph p) (hps : Function.Surjective p) (hf : Continuous f)
    (ha : RiemannAnalyticMap A C (f ∘ p)) : RiemannAnalyticMap B C f := by
  rw [riemannAnalyticMap_iff_locally]
  refine ⟨hf, ?_⟩
  intro y
  obtain ⟨x, rfl⟩ := hps y
  obtain ⟨e, he, hx⟩ := A.cover x
  obtain ⟨g, hg, hy⟩ := B.cover (p x)
  obtain ⟨b, hb, hz⟩ := C.cover (f (p x))
  obtain ⟨l, hlx, hl⟩ := hpl x
  let P := e.symm.trans (l.trans g)
  have hsub : P.source ⊆ riemannChartMapDomain e p g := by
    intro w hw
    change w ∈ e.target ∧ e.symm w ∈ l.source ∧ l (e.symm w) ∈ g.source at hw
    refine ⟨hw.1, ?_⟩
    change p (e.symm w) ∈ g.source
    rw [hl]
    exact hw.2.2
  have hP : AnalyticOnNhd ℂ P P.source := by
    apply AnalyticOnNhd.congr P.open_source ((hp.2 e he g hg).mono hsub)
    intro w _hw
    change g (p (e.symm w)) = g (l (e.symm w))
    rw [hl]
  have hPs : e x ∈ P.source := by
    change e x ∈ e.target ∧ e.symm (e x) ∈ l.source ∧ l (e.symm (e x)) ∈ g.source
    rw [e.left_inv hx, ← hl]
    exact ⟨e.map_source hx, hlx, hy⟩
  have hPv : P (e x) = g (p x) := by
    change g (l (e.symm (e x))) = g (p x)
    rw [e.left_inv hx, ← hl]
  have hPt : g (p x) ∈ P.target := hPv ▸ P.map_source hPs
  have hPi : P.symm (g (p x)) = e x := by rw [← hPv, P.left_inv hPs]
  have hi : AnalyticAt ℂ P.symm (g (p x)) := openPartialHomeomorph_analytic_inverse P hP _ hPt
  have hforward : AnalyticAt ℂ (riemannChartMap e (f ∘ p) b) (e x) :=
    ha.2 e he b hb (e x) (riemannChartMapDomain_mem e (f ∘ p) b x hx hz)
  have hcompose : AnalyticAt ℂ (riemannChartMap e (f ∘ p) b ∘ P.symm) (g (p x)) := by
    apply AnalyticAt.comp (f := P.symm) (x := g (p x)) ?_ hi
    rwa [hPi]
  refine ⟨g, hg, hy, b, hb, hz, hcompose.congr ?_⟩
  filter_upwards [P.open_target.mem_nhds hPt] with w hw
  have hsource := P.map_target hw
  change P.symm w ∈ e.target ∧ e.symm (P.symm w) ∈ l.source ∧
    l (e.symm (P.symm w)) ∈ g.source at hsource
  have hEq := congrArg g.symm (P.right_inv hw)
  change g.symm (g (l (e.symm (P.symm w)))) = g.symm w at hEq
  rw [← hl] at hEq
  rw [g.left_inv (by rw [hl]; exact hsource.2.2)] at hEq
  change b (f (p (e.symm (P.symm w)))) = b (f (g.symm w))
  rw [hEq]



/-- A genuine local quotient chart can be selected with the original specified point inside
its actual sphere disc, rather than merely its orbit inside the quotient chart. -/
theorem mobiusQuotientChartData_containing {G : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G
      D.carrier) (z : D.carrier) :
    ∃ C : MobiusQuotientChartData D, z.val ∈ C.disc := by
  obtain ⟨q, r, hr, _hqz, _hd, hzN, hcl, hrot, hsep⟩ :=
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_discontinuous_roundDisc G D.carrier D.isOpen D.invariant hD z.val z.property
  let K := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer G z.val
  have hfin : Finite K := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer_finite G hD
    z.val z.property).to_subtype
  have hi : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K ≤ _root_.LowDimensionalTopology.Geometry.Mobius.mobiusInftyStabilizer := by
    intro f hf
    obtain ⟨a, _, rfl⟩ := hrot f hf
    exact _root_.LowDimensionalTopology.Geometry.Mobius.mobiusScaling_infty a
  have hz : ∀ f ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K, f.val (0 : ℂ) = (0 : ℂ) := by
    intro f hf
    obtain ⟨a, _, rfl⟩ := hrot f hf
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusScaling_zero a
  have hND : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r ⊆ D.carrier := subset_closure.trans hcl
  have hKG : K ≤ G := fun f hf => ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer G
    z.val f).mp hf).1
  have hseparated : ∀ g ∈ G, g ∉ K →
      Disjoint (g.val '' _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusNormalizedDisc q r) := by
    intro g hg hn
    apply (hsep ⟨g, hg⟩).2
    intro hfix
    exact hn ((_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer G z.val g).mpr ⟨hg,
      hfix⟩)
  exact ⟨⟨K, hfin, q, hi, hz, r, hr, hND, hKG, hseparated⟩, hzN⟩

/-- The actual orbit projection is analytic for the genuine finite-power branched quotient
atlas, including elliptic branch points. -/
theorem mobiusDomainProjection_analytic {G : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : MobiusInvariantDomain G) (hD : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsMobiusDiscontinuousOn G
      D.carrier) :
    RiemannAnalyticMap (mobiusDomainRiemannSurface D).toRiemannAtlas
      (mobiusQuotientRiemannSurface D hD).toRiemannAtlas (mobiusDomainProjection D) := by
  rw [riemannAnalyticMap_iff_locally]
  refine ⟨mobiusDomainProjection_continuous D, ?_⟩
  intro x
  obtain ⟨e, he, hx⟩ := (mobiusDomainRiemannSurface D).cover x
  obtain ⟨C, hCx⟩ := mobiusQuotientChartData_containing D hD x
  have hCmem : C.chart ∈ (mobiusQuotientRiemannSurface D hD).charts := ⟨C, rfl⟩
  have hCsource : mobiusDomainProjection D x ∈ C.chart.source := by
    rw [C.chart_source]
    exact ⟨⟨x.val, hCx⟩, rfl⟩
  have hinc : RiemannAnalyticMap (mobiusDomainRiemannSurface D).toRiemannAtlas
      sphereRiemannAtlas (Subtype.val : D.carrier → _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex) :=
    sphereRiemannAtlas.liftLocalHomeomorph_projection_analytic _
      D.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hn := (mobius_riemannSphere_analytic C.normalizer).comp hinc
  have hfinite : C.normalizer.val x.val ∈ sphereFiniteChart.source := by
    rw [C.coordinate_coe ⟨x.val, hCx⟩, sphereFiniteChart_source]
    exact OnePoint.coe_ne_infty _
  have hfa : AnalyticAt ℂ (riemannChartMap e
      (C.normalizer.val ∘ (Subtype.val : D.carrier →
        _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex)) sphereFiniteChart) (e x) :=
    hn.2 e he sphereFiniteChart (Set.mem_insert _ _) (e x)
      (riemannChartMapDomain_mem e _ sphereFiniteChart x hx hfinite)
  have hpower := hfa.pow C.degree
  refine ⟨e, he, hx, C.chart, hCmem, hCsource, hpower.congr ?_⟩
  have hnear : ∀ᶠ w in 𝓝 (e x), (e.symm w).val ∈ C.disc := by
    have ht : Tendsto (Subtype.val ∘ e.symm) (𝓝 (e x)) (𝓝 x.val) :=
      continuous_subtype_val.continuousAt.tendsto.comp (e.tendsto_symm hx)
    exact ht.eventually (C.disc_isOpen.mem_nhds hCx)
  filter_upwards [hnear] with w hw
  let a : C.disc := ⟨(e.symm w).val, hw⟩
  have hp := C.chart_apply_projection a
  have hc : sphereFiniteChart (C.normalizer.val a.val) = (C.coordinate a).val := by
    simpa only [sphereFiniteChart_coe] using congrArg sphereFiniteChart (C.coordinate_coe a)
  change sphereFiniteChart (C.normalizer.val (e.symm w).val) ^ C.degree =
    C.chart (mobiusDomainProjection D (e.symm w))
  exact (congrArg (fun z : ℂ => z ^ C.degree) hc).trans hp.symm

/-- The actual invariant unit-disc domain of the Mobius image of an analytic disc deck group. -/
def discDeckMobiusDomain {X : Type*} [TopologicalSpace X] (B : RiemannAtlas X)
    (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp : IsCoveringMap p)
    (ha : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas B p) :
    MobiusInvariantDomain (discDeckMobiusHom B p hp ha).range :=
  unitDiscMobiusInvariantDomain _ (discDeckMobiusRange_invariant B p hp ha)

/-- Fibers of the original cover are precisely orbits of its actual Mobius deck image. -/
theorem discDeckMobius_fiber_iff_orbit {X : Type*} [TopologicalSpace X]
    (B : RiemannAtlas X) (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp :
      IsCoveringMap p)
    (ha : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas B p)
    (a b : (discDeckMobiusDomain B p hp ha).carrier) :
    p a = p b ↔ a ∈ MulAction.orbit (discDeckMobiusHom B p hp ha).range b := by
  let : SimplyConnectedSpace _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := discRiemannSurface_simplyConnected
  let : LocallyPathConnectedSpace _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc :=
    discRiemannSurface.toRiemannAtlas.locallyPathConnectedSpace
  constructor
  · intro hab
    obtain ⟨d, hd⟩ := covering_exists_deck_map hp b a hab.symm
    refine ⟨⟨discDeckMobiusHom B p hp ha d, ⟨d, rfl⟩⟩, ?_⟩
    apply Subtype.ext
    exact (discDeckMobiusHom_apply B p hp ha d b).trans (congrArg Subtype.val hd)
  · rintro ⟨g, rfl⟩
    obtain ⟨d, hd⟩ := g.property
    have he : g • b = d.val b := by
      apply Subtype.ext
      change g.val.val b.val = (d.val b).val
      exact (congrArg (fun M : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup => M.val b.val)
        hd).symm.trans
        (discDeckMobiusHom_apply B p hp ha d b)
    exact (congrArg p he).trans (deck.proj_smul d b)

/-- The genuine full Mobius orbit quotient of an analytic disc cover is homeomorphic to its
original base, using the original quotient topology. -/
def discDeckMobiusQuotientHomeomorph {X : Type*} [TopologicalSpace X]
    (B : RiemannAtlas X) (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp :
      IsCoveringMap p)
    (ha : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas B p)
    (hs : Function.Surjective p) : MobiusDomainQuotient (discDeckMobiusDomain B p hp ha) ≃ₜ X := by
  let F : C(_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc, X) := ⟨p, hp.continuous⟩
  have hF : Topology.IsQuotientMap F := hp.isQuotientMap hs
  exact (Homeomorph.Quotient.congrRight (fun a b =>
    (discDeckMobius_fiber_iff_orbit B p hp ha a b).symm)).trans hF.homeomorph

theorem discDeckMobiusQuotientHomeomorph_apply_projection {X : Type*} [TopologicalSpace X]
    (B : RiemannAtlas X) (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp :
      IsCoveringMap p)
    (ha : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas B p)
    (hs : Function.Surjective p) (z : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) :
    discDeckMobiusQuotientHomeomorph B p hp ha hs
      (mobiusDomainProjection (discDeckMobiusDomain B p hp ha) z) = p z := rfl

/-- The quotient homeomorphism is analytic for the actual branched quotient atlas, rather
than a complex structure newly defined by transporting the target atlas. -/
theorem discDeckMobiusQuotientHomeomorph_analytic {X : Type*} [TopologicalSpace X] [T2Space X]
    (B : RiemannAtlas X) (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp :
      IsCoveringMap p)
    (ha : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas B p) (hs : Function.Surjective p) :
    RiemannAnalyticMap
      (mobiusQuotientRiemannSurface (discDeckMobiusDomain B p hp ha)
        (discDeckMobiusRange_discontinuous B p hp ha)).toRiemannAtlas B
      (discDeckMobiusQuotientHomeomorph B p hp ha hs) := by
  let D := discDeckMobiusDomain B p hp ha
  let hd := discDeckMobiusRange_discontinuous B p hp ha
  have hno : ∀ f ∈ (discDeckMobiusHom B p hp
    ha).range, f ≠ 1 → ¬_root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f :=
    fun f hf _hne => discDeckMobiusRange_noElliptic B p hp ha f hf
  have hπ := mobiusDomain_noElliptic_covering D hd hno
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannAnalyticMap.of_comp_surjective_localHomeomorph
    (mobiusDomainProjection_analytic D hd) hπ.isCoveringMap.isLocalHomeomorph
    (mobiusDomainProjection_surjective D) (discDeckMobiusQuotientHomeomorph B p hp ha hs).continuous
  exact ha

/-- Every surface admitting an actual analytic unit-disc covering is conformally equivalent
to the actual discontinuous no-elliptic Mobius quotient supplied by that covering. -/
theorem riemannSurface_discCover_conformallyEquivalent {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp :
      IsCoveringMap p)
    (ha : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas R.toRiemannAtlas p)
    (hs : Function.Surjective p) :
    RiemannConformallyEquivalent R
      (mobiusQuotientRiemannSurface (discDeckMobiusDomain R.toRiemannAtlas p hp ha)
        (by let := R.t2Space; exact discDeckMobiusRange_discontinuous R.toRiemannAtlas p hp ha)) := by
  let := R.t2Space
  apply _root_.LowDimensionalTopology.Geometry.Surfaces.RiemannConformallyEquivalent.symm
  exact ⟨discDeckMobiusQuotientHomeomorph R.toRiemannAtlas p hp ha hs,
    discDeckMobiusQuotientHomeomorph_analytic R.toRiemannAtlas p hp ha hs,
    (discDeckMobiusQuotientHomeomorph R.toRiemannAtlas p hp ha hs).bijective⟩

/-- The disc case of the standard-cover classification gives the literal source definition
of hyperbolic type. The existence of such a model cover is not assumed for arbitrary surfaces. -/
theorem riemannSurface_isHyperbolicType_of_discCover {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) (p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X) (hp :
      IsCoveringMap p)
    (ha : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas R.toRiemannAtlas p)
    (hs : Function.Surjective p) : IsHyperbolicType R := by
  let := R.t2Space
  refine ⟨(discDeckMobiusHom R.toRiemannAtlas p hp ha).range,
    discDeckMobiusRange_invariant R.toRiemannAtlas p hp ha,
    discDeckMobiusRange_discontinuous R.toRiemannAtlas p hp ha,
    ?_, riemannSurface_discCover_conformallyEquivalent R p hp ha hs⟩
  intro f hf _hne
  exact discDeckMobiusRange_noElliptic R.toRiemannAtlas p hp ha f hf

/-- The disc alternative for a genuinely constructed universal cover yields the actual
hyperbolic-type quotient conclusion. Uniformization itself is kept as the explicit hypothesis. -/
theorem RiemannUniversalCover.isHyperbolicType_of_conformallyEquivalent_disc
    {X : Type*} [TopologicalSpace X] {R : RiemannSurface X} (C : RiemannUniversalCover R)
    (hc : @RiemannConformallyEquivalent C.space _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc
      C.topology _
      C.surface discRiemannSurface) : IsHyperbolicType R := by
  let : TopologicalSpace C.space := C.topology
  obtain ⟨f, hf, hbij⟩ := hc
  let E := hf.toHomeomorph hbij
  have hi := hf.inverse_analytic hbij
  have hp : IsCoveringMap (C.projection ∘ E.symm) := C.covering.comp_homeomorph E.symm
  have ha : RiemannAnalyticMap discRiemannSurface.toRiemannAtlas R.toRiemannAtlas
      (C.projection ∘ E.symm) := C.analytic_projection.comp hi
  exact riemannSurface_isHyperbolicType_of_discCover R (C.projection ∘ E.symm) hp ha
    (C.surjective.comp E.symm.surjective)

/-- Conversely, the source definition of hyperbolic type supplies a genuine surjective
analytic disc covering in the canonical inherited complex structure. -/
theorem IsHyperbolicType.exists_analytic_discCover {X : Type*} [TopologicalSpace X]
    {R : RiemannSurface X} (hR : IsHyperbolicType R) :
    ∃ p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X, IsCoveringMap p ∧ Function.Surjective p ∧
      RiemannAnalyticMap discRiemannSurface.toRiemannAtlas R.toRiemannAtlas p := by
  obtain ⟨H, hInv, hD, hno, f, hf, hbij⟩ := hR
  let D := unitDiscMobiusInvariantDomain H hInv
  let E := hf.toHomeomorph hbij
  have hπ := mobiusDomain_noElliptic_covering D hD hno
  have hi := hf.inverse_analytic hbij
  refine ⟨E.symm ∘ mobiusDomainProjection D,
    hπ.isCoveringMap.homeomorph_comp E.symm,
    E.symm.surjective.comp (mobiusDomainProjection_surjective D), ?_⟩
  exact hi.comp (mobiusDomainProjection_analytic D hD)

/-- Hyperbolic type is exactly the existence of an analytic covering by the actual unit
disc. This equivalence classifies the disc alternative without asserting uniformization. -/
theorem isHyperbolicType_iff_analytic_discCover {X : Type*} [TopologicalSpace X]
    (R : RiemannSurface X) : IsHyperbolicType R ↔
      ∃ p : _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc → X, IsCoveringMap p ∧ Function.Surjective p ∧
        RiemannAnalyticMap discRiemannSurface.toRiemannAtlas R.toRiemannAtlas p := by
  constructor
  · exact _root_.LowDimensionalTopology.Geometry.Surfaces.IsHyperbolicType.exists_analytic_discCover
  · rintro ⟨p, hp, hs, ha⟩
    exact riemannSurface_isHyperbolicType_of_discCover R p hp ha hs

end LowDimensionalTopology.Geometry.Surfaces
