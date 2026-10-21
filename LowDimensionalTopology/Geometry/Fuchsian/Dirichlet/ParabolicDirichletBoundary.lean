module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import LowDimensionalTopology.Geometry.Hyperbolic.Models.Disc.ExtendedCarrier
public import LowDimensionalTopology.Geometry.Fuchsian.Dirichlet.DirichletEquivariance
public import LowDimensionalTopology.Geometry.Fuchsian.FundamentalDomain.Vertex.PolygonIdealBoundary
public import LowDimensionalTopology.Geometry.Surfaces.Cusp.GeneralParabolicCusps
public import LowDimensionalTopology.Geometry.DiscreteGroups.Elementary.DiscreteTranslationGroups
public import LowDimensionalTopology.Geometry.Fuchsian.Ford.FordHeightRepresentatives
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology OnePoint UpperHalfPlane Complex.UnitDisc
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

/-- Above a maximal-height free orbit point, every other orbit point is strictly farther away. -/
theorem vertical_closer_of_height_le {w b z : ℍ} (hb : b.im ≤ w.im) (hbw : b ≠ w)
    (hzre : z.re = w.re) (hzheight : w.im ≤ z.im) : dist z w < dist z b := by
  have hcore : 0 < w.im*(w.re-b.re)^2+(w.im-b.im)*(z.im^2-w.im*b.im) := by
    by_cases hlt : b.im < w.im
    · have hs : w.im^2 ≤ z.im^2 := by
        nlinarith only [hzheight, w.im_pos, z.im_pos]
      have hi : 0 < z.im^2-w.im*b.im := by
        have hp := mul_pos w.im_pos (sub_pos.mpr hlt)
        nlinarith only [hs, hp]
      exact add_pos_of_nonneg_of_pos (mul_nonneg w.im_pos.le (sq_nonneg _))
        (mul_pos (sub_pos.mpr hlt) hi)
    · have him : b.im = w.im := le_antisymm hb (not_lt.mp hlt)
      have hre : w.re-b.re ≠ 0 := by
        intro he
        exact hbw (UpperHalfPlane.ext (Complex.ext (sub_eq_zero.mp he).symm him))
      rw [him, sub_self, zero_mul, add_zero]
      exact mul_pos w.im_pos (sq_pos_of_ne_zero hre)
  have hcos : Real.cosh (dist z w) < Real.cosh (dist z b) := by
    rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist', hzre]
    apply (div_lt_div_iff₀ (by positivity : 0 < 2*z.im*w.im)
      (by positivity : 0 < 2*z.im*b.im)).mpr
    have hp := mul_pos (by positivity : 0 < 2*z.im) hcore
    nlinarith only [hp]
  simpa only [abs_of_nonneg dist_nonneg] using Real.cosh_lt_cosh.mp hcos

/-- The whole actual native group is used; no cyclic subgroup substitutes for it. -/
theorem nativeDirichletDomain_vertical_ray (G : Subgroup (ℍ ≃ᵢ ℍ)) (w : ℍ)
    (hfree : ∀ g : G, g.val w = w → g = 1)
    (hmax : ∀ g : G, (g.val w).im ≤ w.im) :
    {z : ℍ | z.re = w.re ∧ w.im ≤ z.im} ⊆ nativeDirichletDomain G w := by
  rintro z ⟨hzr, hzy⟩ g hg
  exact vertical_closer_of_height_le (hmax g) (fun he => hg (hfree g he)) hzr hzy

/-- The genuine upward vertical points converge to the actual sphere point infinity. -/
theorem vertical_probe_tendsto_infty (x : ℝ) :
    Tendsto (fun t : ℝ => (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe x (Real.exp t) (Real.exp_pos
      t) : ℍ) : ℂ) : OnePoint ℂ))
      atTop (𝓝 (∞ : OnePoint ℂ)) := by
  have hn : Tendsto (fun t : ℝ => ‖((_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe x (Real.exp t)
    (Real.exp_pos t) : ℍ) : ℂ)‖)
      atTop atTop := by
    apply tendsto_atTop_mono _ Real.tendsto_exp_atTop
    intro t
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe, UpperHalfPlane.coe_mk] using
      (Complex.im_le_norm ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe x (Real.exp t) (Real.exp_pos
        t) : ℍ) : ℂ))
  have hc : Tendsto (fun t : ℝ => ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe x (Real.exp t)
    (Real.exp_pos t) : ℍ) : ℂ))
      atTop (coclosedCompact ℂ) := by
    rw [coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact tendsto_norm_atTop_iff_cobounded.mp hn
  exact OnePoint.tendsto_coe_infty.comp hc

theorem nativeDirichletDomain_infty_mem_closure_of_maxheight (G : Subgroup (ℍ ≃ᵢ ℍ)) (w : ℍ)
    (hfree : ∀ g : G, g.val w = w → g = 1)
    (hmax : ∀ g : G, (g.val w).im ≤ w.im) :
    (∞ : OnePoint ℂ) ∈ closure ((fun z : ℍ => ((z : ℂ) : OnePoint ℂ)) ''
      nativeDirichletDomain G w) := by
  apply mem_closure_of_tendsto (vertical_probe_tendsto_infty w.re)
  filter_upwards [Real.tendsto_exp_atTop.eventually (eventually_ge_atTop w.im)] with t ht
  exact ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe w.re (Real.exp t) (Real.exp_pos t),
    nativeDirichletDomain_vertical_ray G w hfree hmax ⟨rfl, ht⟩, rfl⟩

def fordSLNativeHom : Matrix.SpecialLinearGroup (Fin 2) ℝ →* (ℍ ≃ᵢ ℍ) where
  toFun A := IsometryEquiv.constSMul (X := ℍ) A
  map_one' := by
    apply IsometryEquiv.ext
    intro z
    change (1 : Matrix.SpecialLinearGroup (Fin 2) ℝ) • z = z
    exact one_smul _ z
  map_mul' A B := by
    apply IsometryEquiv.ext
    intro z
    change (A*B) • z = A • (B • z)
    exact mul_smul A B z

/-- The actual native image of all real determinant-one lifts in the original subgroup. -/
def fordNativeGroup (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) : Subgroup (ℍ ≃ᵢ
  ℍ) :=
  (H.comap _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius).map fordSLNativeHom

theorem mem_fordNativeGroup (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (e : ℍ ≃ᵢ
  ℍ) :
    e ∈ fordNativeGroup H ↔ ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A ∈ H ∧ fordSLNativeHom A = e := Iff.rfl

theorem native_free_center_orbit (G : Subgroup (ℍ ≃ᵢ ℍ)) (w : ℍ)
    (hfree : ∀ g : G, g.val w = w → g = 1) (e : ℍ ≃ᵢ ℍ) (he : e ∈ G) :
    ∀ g : G, g.val (e w) = e w → g = 1 := by
  intro g hfix
  let E : G := ⟨e, he⟩
  have hc : (E⁻¹*g*E).val w = w := by
    change e.symm (g.val (e w)) = w
    rw [hfix, e.symm_apply_apply]
  have hk := hfree (E⁻¹*g*E) hc
  calc
    g = E*(E⁻¹*g*E)*E⁻¹ := by group
    _ = 1 := by rw [hk]; group

/-- The original Ford maximum theorem constructs the actual maximal-height free center
for the whole native image, instead of assuming the height-maximality conclusion. -/
theorem exists_ford_native_dirichlet_infty (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ H) (z : ℍ)
    (hfree : ∀ g : fordNativeGroup H, g.val z = z → g = 1) :
    ∃ B : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B ∈ H ∧
      (∞ : OnePoint ℂ) ∈ closure ((fun p : ℍ => ((p : ℂ) : OnePoint ℂ)) ''
        nativeDirichletDomain (fordNativeGroup H) (B • z)) := by
  obtain ⟨B, hB, _, hmax⟩ := exists_ford_maximal_orbit_point H hd hT z
  have hBG : fordSLNativeHom B ∈ fordNativeGroup H := (mem_fordNativeGroup H _).mpr ⟨B, hB, rfl⟩
  have hf : ∀ g : fordNativeGroup H, g.val (B • z) = B • z → g = 1 :=
    native_free_center_orbit (fordNativeGroup H) z hfree (fordSLNativeHom B) hBG
  refine ⟨B, hB, nativeDirichletDomain_infty_mem_closure_of_maxheight (fordNativeGroup H) (B • z) hf ?_⟩
  intro g
  obtain ⟨A, hA, he⟩ := (mem_fordNativeGroup H g.val).mp g.property
  rw [← he]
  exact hmax A hA

theorem fordSLNativeHom_eq_one_of_projection_eq_one
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = 1) : fordSLNativeHom A = 1 := by
  apply IsometryEquiv.ext
  intro w
  have he := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A w
  rw [hA] at he
  change ((w : ℂ) : OnePoint ℂ) = (((A • w : ℍ) : ℂ) : OnePoint ℂ) at he
  change A • w = w
  exact UpperHalfPlane.ext (OnePoint.coe_injective he.symm)

/-- A free native center exists for the actual whole real-lift image of any discrete Mobius subgroup. -/
theorem exists_ford_native_free_center (H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) :
    ∃ z : ℍ, ∀ g : fordNativeGroup H, g.val z = z → g = 1 := by
  classical
  let : DiscreteTopology H := hd
  have : Countable H := _root_.LowDimensionalTopology.Geometry.Mobius.discreteMobius_countable H hd
  have : Uncountable ℍ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.imaginaryAxisParam_isometry.injective.uncountable
  let S : Set ℍ := {z | ∃ f : H, f.val ≠ 1 ∧
    f.val.val ((z : ℂ) : OnePoint ℂ) = ((z : ℂ) : OnePoint ℂ)}
  have hcount : S.Countable := by
    have hF (f : {f : H // f.val ≠ 1}) :
        {z : ℍ | f.val.val.val ((z : ℂ) : OnePoint ℂ) = ((z : ℂ) : OnePoint ℂ)}.Countable := by
      have hi : Function.Injective (fun z : ℍ => ((z : ℂ) : OnePoint ℂ)) :=
        OnePoint.coe_injective.comp UpperHalfPlane.coe_injective
      exact (mobius_boundary_fixed_finite f.val.val f.property).countable.preimage hi
    apply (countable_iUnion hF).mono
    rintro z ⟨f, hf, hz⟩
    exact mem_iUnion.mpr ⟨⟨f, hf⟩, hz⟩
  have hex : ∃ z : ℍ, z ∉ S := by
    by_contra hn
    push Not at hn
    have he : S = univ := eq_univ_of_forall hn
    exact Set.not_countable_univ (he ▸ hcount)
  obtain ⟨z, hz⟩ := hex
  refine ⟨z, ?_⟩
  intro g hg
  obtain ⟨A, hA, he⟩ := (mem_fordNativeGroup H g.val).mp g.property
  have hproj : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = 1 := by
    by_contra hn
    apply hz
    refine ⟨⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A, hA⟩, hn, ?_⟩
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action]
    have hf : A • z = z := by
      change fordSLNativeHom A z = z
      rwa [he]
    rw [hf]
  apply Subtype.val_injective
  exact he.symm.trans (fordSLNativeHom_eq_one_of_projection_eq_one A hproj)

/-- Unit-translation membership and actual discreteness alone construct a true Dirichlet
center whose literal full native-group domain has infinity in its Euclidean closure. -/
theorem exists_unitTranslation_native_dirichlet_infty (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ H) :
    ∃ w : ℍ, (∞ : OnePoint ℂ) ∈ closure ((fun p : ℍ => ((p : ℂ) : OnePoint ℂ)) ''
      nativeDirichletDomain (fordNativeGroup H) w) := by
  obtain ⟨z, hz⟩ := exists_ford_native_free_center H hd
  obtain ⟨B, _, hB⟩ := exists_ford_native_dirichlet_infty H hd hT z hz
  exact ⟨B • z, hB⟩

theorem UnitDiscFuchsianGroup.halfPlaneCoordinate_extended {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (x : P.domain.carrier) :
    (((P.halfPlaneCoordinate x : ℍ) : ℂ) : OnePoint ℂ) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val x.val := by
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val.injective
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.finiteCoordinate x) : ℍ) : ℂ) : OnePoint ℂ) =
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm x.val)
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.apply_symm_apply,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley_coe _
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayley_denom_ne_zero _)]
  change (((_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane (P.finiteCoordinate x)) : 𝔻) : ℂ) : OnePoint
    ℂ) = x.val
  rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane]
  exact P.finiteCoordinate_extended x

theorem UnitDiscFuchsianGroup.halfPlaneCoordinate_symm_extended {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (w : ℍ) :
    (P.halfPlaneCoordinate.symm w).val = _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val ((w : ℂ) : OnePoint ℂ) := by
  have h := P.halfPlaneCoordinate_extended (P.halfPlaneCoordinate.symm w)
  rw [P.halfPlaneCoordinate.apply_symm_apply] at h
  have he := congrArg _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val h
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius • ((w : ℂ) : OnePoint ℂ) =
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ • (P.halfPlaneCoordinate.symm w).val) at he
  rw [smul_inv_smul] at he
  exact he.symm

theorem UnitDiscFuchsianGroup.halfPlaneAction_extended {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (g : H) (w : ℍ) :
    (((P.halfPlaneAction g w : ℍ) : ℂ) : OnePoint ℂ) =
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*g.val*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius).val ((w : ℂ) : OnePoint ℂ) := by
  rw [P.halfPlaneAction_apply, P.halfPlaneCoordinate_extended]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ • (g.val • (P.halfPlaneCoordinate.symm
    w).val) = _
  rw [P.halfPlaneCoordinate_symm_extended]
  change _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ • (g.val •
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius • ((w : ℂ) : OnePoint ℂ))) =
    (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*g.val*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) • ((w : ℂ) : OnePoint ℂ)
  rw [mul_smul, mul_smul]

theorem halfPlane_chart_real_lift (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) ℝ, _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A = q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius := by
  apply mobius_preserves_halfPlane_exists_SL
  change ((fun z => q.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius.val z)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
  rw [← image_image, cayleyMobius_image_openHalfPlane, hq]

theorem halfPlane_chart_action_intertwine {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A =
      q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
    (g : H) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B = q*g.val*q⁻¹) :
    fordSLNativeHom B * fordSLNativeHom A = fordSLNativeHom A * P.halfPlaneAction g := by
  apply IsometryEquiv.ext
  intro w
  apply UpperHalfPlane.ext
  apply OnePoint.coe_injective
  change (((B • (A • w) : ℍ) : ℂ) : OnePoint ℂ) =
    (((A • P.halfPlaneAction g w : ℍ) : ℂ) : OnePoint ℂ)
  calc
    _ = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B).val ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val ((w : ℂ) : OnePoint ℂ)) := by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action,
        _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action]
    _ = (q*g.val*q⁻¹).val ((q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius).val ((w : ℂ) : OnePoint ℂ)) := by rw [hA, hB]
    _ = (q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius).val ((_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*g.val*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius).val ((w : ℂ) : OnePoint ℂ)) := by
      have he : (q*g.val*q⁻¹)*(q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) =
          (q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)*(_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*g.val*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) := by group
      exact congrArg (fun f : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup => f.val ((w : ℂ) :
        OnePoint ℂ)) he
    _ = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (((P.halfPlaneAction g w : ℍ) : ℂ) : OnePoint ℂ) := by
      rw [hA, P.halfPlaneAction_extended]
    _ = _ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A _

theorem halfPlane_chart_action_conjugate {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A =
      q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
    (g : H) (B : Matrix.SpecialLinearGroup (Fin 2) ℝ)
    (hB : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius B = q*g.val*q⁻¹) :
    fordSLNativeHom B = MulAut.conj (fordSLNativeHom A) (P.halfPlaneAction g) := by
  have he := halfPlane_chart_action_intertwine P q A hA g B hB
  change fordSLNativeHom B = fordSLNativeHom A * P.halfPlaneAction g * (fordSLNativeHom A)⁻¹
  calc
    _ = (fordSLNativeHom B * fordSLNativeHom A) * (fordSLNativeHom A)⁻¹ := by group
    _ = _ := by rw [he]

theorem halfPlane_chart_whole_native_group {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A =
      q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) :
    fordNativeGroup (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H) =
      nativeConjugateGroup (fordSLNativeHom A) P.halfPlaneActionHom.range := by
  ext e
  constructor
  · intro he
    obtain ⟨B, hB, hBe⟩ := (mem_fordNativeGroup _ _).mp he
    obtain ⟨g, hg, hBg⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mp hB
    let gH : H := ⟨g, hg⟩
    refine ⟨P.halfPlaneAction gH, ⟨gH, rfl⟩, ?_⟩
    exact (halfPlane_chart_action_conjugate P q A hA gH B hBg.symm).symm.trans hBe
  · rintro ⟨f, ⟨g, hg⟩, hfe⟩
    have hpres : (q*g.val*q⁻¹).val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
      rw [← hq, _root_.LowDimensionalTopology.Geometry.Surfaces.cusp_conjugate_image, P.image_eq g]
    obtain ⟨B, hB⟩ := mobius_preserves_halfPlane_exists_SL (q*g.val*q⁻¹) hpres
    apply (mem_fordNativeGroup _ _).mpr
    refine ⟨B, (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H
      _).mpr ⟨g.val, g.property, hB.symm⟩, ?_⟩
    have he := halfPlane_chart_action_conjugate P q A hA g B hB
    rw [show P.halfPlaneAction g = f from hg] at he
    exact he.trans hfe

theorem vertical_cusp_shift_image (h : ℝ) :
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(h : ℂ)*Complex.I)).val '' _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspSphere h = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
  ext ζ
  constructor
  · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
    refine ⟨z+(-(h : ℂ)*Complex.I), ?_, rfl⟩
    have hi : (z+(-(h : ℂ)*Complex.I)).im = z.im-h := by simp; ring
    change 0 < (z+(-(h : ℂ)*Complex.I)).im
    rw [hi]
    exact sub_pos.mpr hz
  · rintro ⟨z, hz, rfl⟩
    have hmem : z+(h : ℂ)*Complex.I ∈ _root_.LowDimensionalTopology.Geometry.Surfaces.stableCuspHalfPlane h := by
      change h < (z+(h : ℂ)*Complex.I).im
      simpa using hz
    refine ⟨((z+(h : ℂ)*Complex.I : ℂ) : OnePoint ℂ), ⟨_, hmem, rfl⟩, ?_⟩
    rw [_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_coe]
    congr 1
    ring

theorem translation_conjugation_commutes (a b : ℂ) :
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation a * _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b * (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation a)⁻¹ = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation b := by
  rw [← _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_neg, ←
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_add, ←
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_add]
  congr 1
  ring

theorem parabolic_unit_halfPlane_normalizer {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (ξ : OnePoint ℂ) (hξ : f.val.val ξ = ξ) :
    ∃ q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup, q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet ∧
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H ∧ q.val ξ = ∞ := by
  obtain ⟨q₀, h, hdisc,
    hfq⟩ := _root_.LowDimensionalTopology.Geometry.Surfaces.parabolic_disc_signed_normalization f.val hf
    _root_.LowDimensionalTopology.Geometry.DiscreteGroups.extendedUnitDisc_isComplexOpenDisc (P.image_eq f)
  let r := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation (-(h : ℂ)*Complex.I)
  let q := r*q₀
  have hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := by
    change ((fun z => r.val (q₀.val z)) '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc) = _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet
    rw [← image_image, hdisc]
    exact vertical_cusp_shift_image h
  have hfq' : q*f.val*q⁻¹ = _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∨ q*f.val*q⁻¹ = (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)⁻¹ := by
    have he : q*f.val*q⁻¹ = r*(q₀*f.val*q₀⁻¹)*r⁻¹ := by dsimp only [q]; group
    rw [he]
    rcases hfq with hp | hn
    · exact Or.inl (by rw [hp]; exact translation_conjugation_commutes _ _)
    · right
      rw [hn]
      have he : r*(_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1)⁻¹*r⁻¹ = (r*_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1*r⁻¹)⁻¹ := by group
      rw [he, translation_conjugation_commutes]
  have hm : q*f.val*q⁻¹ ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H :=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨f.val,
      f.property, rfl⟩
  have hT : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H := by
    rcases hfq' with hp | hn
    · rwa [hp] at hm
    · rw [hn] at hm
      simpa only [inv_inv] using (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate
        q H).inv_mem hm
  have hfix : (q*f.val*q⁻¹).val ∞ = ∞ := by
    rcases hfq' with hp | hn
    · rw [hp]
      exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty _
    · rw [hn, ← _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_neg]
      exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation_infty _
  have hfix₀ := (_root_.LowDimensionalTopology.Geometry.Mobius.mobius_conjugate_boundary_fixed_iff f.val q ∞).mp hfix
  obtain ⟨a, ha⟩ := hf.2
  have hξq : ξ = q.val.symm ∞ := ((ha ξ).mp hξ).trans ((ha (q.val.symm ∞)).mp hfix₀).symm
  exact ⟨q, hq, hT, by rw [hξq, Equiv.apply_symm_apply]⟩

theorem exists_unitTranslation_native_free_dirichlet_infty (H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hd : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup H) (hT :
      _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusTranslation 1 ∈ H) :
    ∃ w : ℍ, (∀ g : fordNativeGroup H, g.val w = w → g = 1) ∧
      (∞ : OnePoint ℂ) ∈ closure ((fun p : ℍ => ((p : ℂ) : OnePoint ℂ)) ''
        nativeDirichletDomain (fordNativeGroup H) w) := by
  obtain ⟨z, hz⟩ := exists_ford_native_free_center H hd
  obtain ⟨B, hB, hInf⟩ := exists_ford_native_dirichlet_infty H hd hT z hz
  exact ⟨B • z, native_free_center_orbit (fordNativeGroup H) z hz (fordSLNativeHom B)
    ((mem_fordNativeGroup H _).mpr ⟨B, hB, rfl⟩), hInf⟩

theorem halfPlane_chart_coordinate_extended {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A =
      q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
    (x : P.domain.carrier) :
    q.val x.val = (((fordSLNativeHom A (P.halfPlaneCoordinate x) : ℍ) : ℂ) : OnePoint ℂ) := by
  symm
  calc
    _ = (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (((P.halfPlaneCoordinate x : ℍ) : ℂ) :
      OnePoint ℂ) :=
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_action A _).symm
    _ = (q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹.val x.val) := by
      rw [hA, P.halfPlaneCoordinate_extended]
    _ = q.val x.val := by
      change (q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius) • (_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ • x.val) = q • x.val
      rw [mul_smul, smul_inv_smul]

theorem halfPlane_chart_dirichlet_image {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (q : _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup)
    (hq : q.val '' _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc =
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet)
    (A : Matrix.SpecialLinearGroup (Fin 2) ℝ) (hA : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A =
      q*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius)
    (w : P.domain.carrier) :
    q.val '' ((Subtype.val : P.domain.carrier → OnePoint ℂ) '' dirichletDomain P w) =
      (fun z : ℍ => ((z : ℂ) : OnePoint ℂ)) ''
        nativeDirichletDomain (fordNativeGroup
          (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H))
          (fordSLNativeHom A (P.halfPlaneCoordinate w)) := by
  have hgeom := dirichletDomain_isometry_conjugate P w (fordSLNativeHom A)
  rw [← halfPlane_chart_whole_native_group P q hq A hA] at hgeom
  calc
    _ = (fun z : ℍ => ((z : ℂ) : OnePoint ℂ)) ''
        (fordSLNativeHom A '' (P.halfPlaneCoordinate '' dirichletDomain P w)) := by
      simp only [image_image]
      congr 1
      funext x
      exact halfPlane_chart_coordinate_extended P q A hA x
    _ = _ := congrArg (Set.image (fun z : ℍ => ((z : ℂ) : OnePoint ℂ))) hgeom

theorem halfPlane_chart_free_center {H : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (F : ℍ ≃ᵢ ℍ) (W : ℍ)
    (hfree : ∀ g : nativeConjugateGroup F P.halfPlaneActionHom.range,
      g.val W = W → g = 1) :
    IsDirichletCenter P (P.halfPlaneCoordinate.symm (F.symm W)) := by
  let w := P.halfPlaneCoordinate.symm (F.symm W)
  have hw : F (P.halfPlaneCoordinate w) = W := by
    dsimp only [w]
    rw [P.halfPlaneCoordinate.apply_symm_apply, F.apply_symm_apply]
  intro g hfix
  let v : nativeConjugateGroup F P.halfPlaneActionHom.range :=
    ⟨MulAut.conj F (P.halfPlaneAction g), ⟨P.halfPlaneAction g, ⟨g, rfl⟩, rfl⟩⟩
  have hv : v.val W = W := by
    rw [← hw]
    change MulAut.conj F (P.halfPlaneAction g) (F (P.halfPlaneCoordinate w)) =
      F (P.halfPlaneCoordinate w)
    rw [native_conjugate_apply, P.halfPlaneAction_coordinate, hfix]
  have hv1 := congrArg Subtype.val (hfree v hv)
  apply P.halfPlaneActionHom_injective
  apply (MulAut.conj F).injective
  change MulAut.conj F (P.halfPlaneAction g) = 1 at hv1
  change MulAut.conj F (P.halfPlaneAction g) = MulAut.conj F (P.halfPlaneActionHom 1)
  simpa only [map_one] using hv1

/-- Every actual parabolic fixed point lies on the literal boundary of a genuine
Dirichlet polygon for the original whole group, at an actual free center. -/
theorem parabolic_fixedPoint_dirichlet_boundary {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val)
    (ξ : OnePoint ℂ) (hξ : f.val.val ξ = ξ) :
    ∃ w : P.domain.carrier, IsDirichletCenter P w ∧
      ξ ∈ frontier ((Subtype.val : P.domain.carrier → OnePoint ℂ) '' dirichletDomain P w) := by
  obtain ⟨q, hq, hT, hqξ⟩ := parabolic_unit_halfPlane_normalizer P f hf ξ hξ
  obtain ⟨A, hA⟩ := halfPlane_chart_real_lift q hq
  let N := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q H
  have hdN : _root_.LowDimensionalTopology.Geometry.Mobius.IsDiscreteMobiusSubgroup N := by
    let : DiscreteTopology H := P.discrete
    exact _root_.LowDimensionalTopology.Geometry.DiscreteGroups.MatrixGroups.conjugateSubgroup_discrete q H
  obtain ⟨W, hfreeW, hInf⟩ := exists_unitTranslation_native_free_dirichlet_infty N hdN hT
  let F := fordSLNativeHom A
  have hGroup : fordNativeGroup N = nativeConjugateGroup F P.halfPlaneActionHom.range :=
    halfPlane_chart_whole_native_group P q hq A hA
  have hfree : ∀ g : nativeConjugateGroup F P.halfPlaneActionHom.range,
      g.val W = W → g = 1 := by rwa [← hGroup]
  let w := P.halfPlaneCoordinate.symm (F.symm W)
  have hw : IsDirichletCenter P w := halfPlane_chart_free_center P F W hfree
  have hwW : F (P.halfPlaneCoordinate w) = W := by
    dsimp only [w]
    rw [P.halfPlaneCoordinate.apply_symm_apply, F.apply_symm_apply]
  have himage := halfPlane_chart_dirichlet_image P q hq A hA w
  rw [show fordSLNativeHom A (P.halfPlaneCoordinate w) = W from hwW] at himage
  have hInfImage : (∞ : OnePoint ℂ) ∈ closure
      (q.val '' ((Subtype.val : P.domain.carrier → OnePoint ℂ) '' dirichletDomain P w)) := by
    rw [himage]
    exact hInf
  have hcl : ξ ∈ closure ((Subtype.val : P.domain.carrier → OnePoint ℂ) '' dirichletDomain P w) := by
    change (∞ : OnePoint ℂ) ∈ closure ((_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q) ''
      ((Subtype.val : P.domain.carrier → OnePoint ℂ) '' dirichletDomain P w)) at hInfImage
    rw [← (_root_.LowDimensionalTopology.Geometry.Mobius.mobiusBoundaryHomeomorph q).image_closure] at hInfImage
    obtain ⟨ζ, hζ, hqζ⟩ := hInfImage
    have he : ζ = ξ := q.val.injective (hqζ.trans hqξ.symm)
    exact he ▸ hζ
  have hnot : ξ ∉ ((Subtype.val : P.domain.carrier → OnePoint ℂ) '' dirichletDomain P w) := by
    rintro ⟨ζ, _hζ, he⟩
    have hζ : ζ.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedUnitDisc := ζ.property
    have hi : q.val ζ.val ∈ _root_.LowDimensionalTopology.Geometry.Hyperbolic.openHalfPlaneSet := hq ▸ mem_image_of_mem q.val hζ
    rw [he, hqξ] at hi
    obtain ⟨z, _, hz⟩ := hi
    exact OnePoint.coe_ne_infty z hz
  exact ⟨w, hw, hcl, fun h => hnot (interior_subset h)⟩

end LowDimensionalTopology.Geometry.Fuchsian
