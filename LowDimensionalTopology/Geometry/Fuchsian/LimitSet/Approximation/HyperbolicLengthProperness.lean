module
public import LowDimensionalTopology.Geometry.Fuchsian.Nielsen.NielsenCoreApproximation
public import Mathlib.Topology.MetricSpace.Thickening
public import LowDimensionalTopology.Geometry.Fuchsian.CyclicClass.HyperbolicConjugacy
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter Topology
open scoped UpperHalfPlane OnePoint Complex.UnitDisc Pointwise
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- Upward rays with the same genuine ideal endpoint are arbitrarily close
outside an actual compact initial portion, rather than merely at some finite
distance depending on their initial points. -/
theorem upward_hRays_asymptotic_outside_compact {z v : ℍ}
    (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt z)
    (S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt v)
    (hR : R.idealEndpoint=∞) (hS : S.idealEndpoint=∞)
    (ε : ℝ) (hε : 0<ε) :
    ∃ K : Set ℍ,IsCompact K ∧ ∀w∈R.val\K,∃u∈S.val,dist w u<ε := by
  let H:=max z.im v.im+|z.re-v.re|/ε+1
  have hHz : z.im<H := by
    dsimp [H]
    linarith [le_max_left z.im v.im,div_nonneg (abs_nonneg (z.re-v.re)) hε.le]
  have hHv : v.im<H := by
    dsimp [H]
    linarith [le_max_right z.im v.im,div_nonneg (abs_nonneg (z.re-v.re)) hε.le]
  have hHa : |z.re-v.re|/ε<H := by
    dsimp [H]
    linarith [z.im_pos,le_max_left z.im v.im]
  let γ : ℝ→ℍ:=fun t=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe z.re (Real.exp t) (Real.exp_pos t)
  have hγ : Continuous γ := (UpperHalfPlane.isometry_vertical_line z.re).continuous
  let K:=γ '' Icc (Real.log z.im) (Real.log H)
  refine ⟨K,isCompact_Icc.image hγ,?_⟩
  rintro w ⟨hw,hwK⟩
  obtain ⟨hwr,hwi⟩ := (hRay_mem_iff_upward_of_endpoint_infty R hR w).mp hw
  have hwH : H<w.im := by
    by_contra h
    have him : w.im≤H:=le_of_not_gt h
    apply hwK
    refine ⟨Real.log w.im,⟨Real.log_le_log z.im_pos hwi,Real.log_le_log w.im_pos him⟩,?_⟩
    apply UpperHalfPlane.ext
    apply Complex.ext
    · change z.re=w.re
      exact hwr.symm
    · change Real.exp (Real.log w.im)=w.im
      exact Real.exp_log w.im_pos
  let u:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.metricProbe v.re w.im w.im_pos
  have hu : u∈S.val :=
    (hRay_mem_iff_upward_of_endpoint_infty S hS u).mpr ⟨rfl,(hHv.trans hwH).le⟩
  have hsub : (w:ℂ)-(u:ℂ)=((z.re-v.re:ℝ):ℂ) := by
    apply Complex.ext
    · change w.re-v.re=z.re-v.re
      rw [hwr]
    · change w.im-w.im=0
      ring
  have hd := UpperHalfPlane.dist_le_dist_coe_div_sqrt w u
  have hdist : dist (w:ℂ) (u:ℂ)=|z.re-v.re| := by
    rw [dist_eq_norm,hsub,Complex.norm_real,Real.norm_eq_abs]
  have huim : u.im=w.im:=rfl
  rw [hdist,huim,←pow_two,Real.sqrt_sq_eq_abs,abs_of_pos w.im_pos] at hd
  refine ⟨u,hu,hd.trans_lt ((div_lt_iff₀ w.im_pos).mpr ?_)⟩
  have ha := (div_lt_iff₀ hε).mp (hHa.trans hwH)
  nlinarith only [ha]

/-- The compact-exception asymptotic assertion is independent of the true
half-plane coordinate and holds for any two actual same-endpoint rays. -/
theorem same_endpoint_hRays_asymptotic_outside_compact {z v : ℍ}
    (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt z)
    (S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.HRayAt v)
    (hEnd : R.idealEndpoint=S.idealEndpoint)
    (ε : ℝ) (hε : 0<ε) :
    ∃ K : Set ℍ,IsCompact K ∧ ∀w∈R.val\K,∃u∈S.val,dist w u<ε := by
  obtain ⟨s,_hs,hR⟩ := R.exists_sl2_normalized_upward
  let g:=Matrix.SpecialLinearGroup.mapGL ℝ s
  have hg : 0<g.val.det := by simp [g]
  have hS : (S.realGLMap g).idealEndpoint=∞ := by
    rw [S.realGLMap_idealEndpoint g hg,←hEnd,←R.realGLMap_idealEndpoint g hg]
    exact hR
  obtain ⟨L,hL,hnear⟩ :=
    upward_hRays_asymptotic_outside_compact (R.realGLMap g) (S.realGLMap g) hR hS ε hε
  let K:=(fun u : ℍ=>g⁻¹ • u) '' L
  refine ⟨K,hL.image (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g⁻¹).continuous,?_⟩
  rintro w ⟨hw,hwK⟩
  have hgw : g • w∈(R.realGLMap g).val := by
    rw [←R.realGLMap_carrier g]
    exact mem_image_of_mem _ hw
  have hgwL : g • w∉L := by
    intro hh
    exact hwK ⟨g • w,hh,inv_smul_smul g w⟩
  obtain ⟨u,hu,hd⟩ := hnear (g • w) ⟨hgw,hgwL⟩
  rw [←S.realGLMap_carrier g] at hu
  obtain ⟨y,hy,rfl⟩ := hu
  exact ⟨y,hy,by simpa only [(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realGL_isometry g).dist_eq] using hd⟩

/-- Same-endpoint actual disc rays are arbitrarily close outside a true
compact initial portion in the unchanged native disc topology. -/
theorem same_endpoint_discRays_asymptotic_outside_compact {z v : 𝔻}
    (R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt z)
    (S : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt v)
    (hEnd : R.idealEndpoint=S.idealEndpoint)
    (ε : ℝ) (hε : 0<ε) :
    ∃ K : Set 𝔻,IsCompact K ∧ ∀w∈R.val\K,∃u∈S.val,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist w u<ε := by
  have hH : R.toHalfPlane.idealEndpoint=S.toHalfPlane.idealEndpoint := by
    rw [R.toHalfPlane_idealEndpoint,S.toHalfPlane_idealEndpoint,hEnd]
  obtain ⟨L,hL,hnear⟩ := same_endpoint_hRays_asymptotic_outside_compact R.toHalfPlane S.toHalfPlane hH ε hε
  refine ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc '' L,hL.image _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyHomeomorph.continuous,?_⟩
  rintro w ⟨hw,hwK⟩
  have hwL : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w∉L := by
    intro h
    exact hwK ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w,h,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc_discToHalfPlane w⟩
  obtain ⟨u,hu,hd⟩ := hnear (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane w) ⟨⟨w,hw,rfl⟩,hwL⟩
  obtain ⟨y,hy,rfl⟩ := hu
  exact ⟨y,hy,by rwa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist_eq_halfPlane]⟩

/-- Every genuinely connected subset of the actual Nielsen region which
avoids all original translates of one constructed compact set has only
actual parabolic ideal endpoints. The compact set is derived from the
original group and regular-circle geometry. -/
theorem RegularDirichletCircleData.connected_core_escape_parabolic
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {w : P.domain.carrier} (d : RegularDirichletCircleData P w)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hw : IsDirichletCenter P w) :
    ∃ K : Set P.domain.carrier,IsCompact K ∧
      ∀S : Set P.domain.carrier,IsConnected S→S⊆fuchsianNielsenCore P hNE→
      ∀p∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discTraceIdealEndpoints (P.finiteCoordinate '' S),
      (∀g : H,Disjoint S (g • K))→∃f : H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val ∧ f.val.val p=p := by
  obtain ⟨F,K,hK,hCover⟩ := d.nielsen_core_compact_cusp_orbit_cover hNE hw
  refine ⟨K,hK,?_⟩
  intro S hS hSN p hp hAvoid
  have hSCover : S⊆⋃q : Mobius.ExtendedComplex,nielsenCuspOrbitTail F q := by
    intro x hx
    rcases hCover (hSN hx) with h|h
    · obtain ⟨g,hg⟩ := mem_iUnion.mp h
      exact False.elim (disjoint_left.mp (hAvoid g) hx hg)
    · obtain ⟨g,hg⟩ := mem_iUnion.mp h
      obtain ⟨C,hC,hxC⟩ := mem_iUnion₂.mp hg
      exact mem_iUnion.mpr ⟨g.val.val C.endpoint,mem_iUnion₂.mpr ⟨C,hC,⟨g,rfl,hxC⟩⟩⟩
  obtain ⟨q,hSq⟩ := connected_subset_one_of_disjoint_open_cover hS
    (nielsenCuspOrbitTail F) (nielsenCuspOrbitTail_isOpen F)
    (nielsenCuspOrbitTail_pairwise_disjoint F) hSCover
  have hMono : _root_.LowDimensionalTopology.Geometry.Hyperbolic.discTraceIdealEndpoints (P.finiteCoordinate '' S)⊆
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.discTraceIdealEndpoints (P.finiteCoordinate '' nielsenCuspOrbitTail F q) :=
    inter_subset_inter_left _ (closure_mono (image_mono (image_mono hSq)))
  have hpq : p=q := mem_singleton_iff.mp (nielsenCuspOrbitTail_idealEndpoints_subset F q (hMono hp))
  obtain ⟨f,hf,hfix⟩ := nielsenCuspOrbitTail_parabolic F q (hS.nonempty.mono hSq)
  exact ⟨f,hf,hpq.symm ▸ hfix⟩

/-- One genuine compact subset, independent of the endpoint and initial
point of the ray, meets an original group translate of every actual ray
ending at a nonparabolic original limit point. -/
theorem RegularDirichletCircleData.uniform_nonparabolic_ray_core
    {H : Subgroup Mobius.complexMobiusGroup} {P : UnitDiscFuchsianGroup H}
    {w : P.domain.carrier} (d : RegularDirichletCircleData P w)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hw : IsDirichletCenter P w) :
    ∃ K : Set 𝔻,IsCompact K ∧
      ∀ξ : ℂ,(ξ:Mobius.ExtendedComplex)∈fuchsianLimitSet H→
      (¬∃f : H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val ∧ f.val.val (ξ:Mobius.ExtendedComplex)=(ξ:Mobius.ExtendedComplex))→
      ∀z : 𝔻,∀R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt z,R.idealEndpoint=(ξ:Mobius.ExtendedComplex)→
      ∃g : H,∃u∈K,P.discAction g u∈R.val := by
  classical
  let :=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  have : ProperSpace 𝔻:=disc_hyperbolic_properSpace
  obtain ⟨K,hK,hEscape⟩ := d.connected_core_escape_parabolic hNE hw
  let L:=P.finiteCoordinate '' K
  have hL : IsCompact L:=hK.image P.finiteCoordinate.continuous
  refine ⟨Metric.cthickening 1 L,hL.cthickening,?_⟩
  intro ξ hξ hNot z R hR
  obtain ⟨v,_hv,hvN⟩ := exists_dirichlet_center_in_nielsenCore P hNE
  have hn:=fuchsian_limit_finite_norm_one P ξ hξ
  let A:=approximationCanonicalRay (P.finiteCoordinate v) ξ hn
  have hA:=approximationCanonicalRay_endpoint (P.finiteCoordinate v) ξ hn
  have hAN : A.val⊆P.finiteCoordinate '' fuchsianNielsenCore P hNE :=
    fuchsianNielsenCore_canonical_ray_subset P hNE v hvN ξ hn
      (by rwa [←fuchsianLimitSet_eq_nonElementary H hNE])
  obtain ⟨B,hB,hNear⟩ := same_endpoint_discRays_asymptotic_outside_compact A R (hA.trans hR.symm) 1 zero_lt_one
  obtain ⟨T,hT,hTAB,hEnd⟩ := discRay_tail_avoids_compact A B hB
  let S:=P.finiteCoordinate.symm '' T
  have hS : IsConnected S:=hT.image _ P.finiteCoordinate.symm.continuous.continuousOn
  have hSN : S⊆fuchsianNielsenCore P hNE := by
    rintro x ⟨t,ht,rfl⟩
    obtain ⟨y,hy,hey⟩ := hAN (hTAB ht).1
    rwa [←hey,P.finiteCoordinate.symm_apply_apply]
  have hST : P.finiteCoordinate '' S=T := by
    rw [image_image]
    simp only [P.finiteCoordinate.apply_symm_apply,image_id']
  have hp : (ξ:Mobius.ExtendedComplex)∈_root_.LowDimensionalTopology.Geometry.Hyperbolic.discTraceIdealEndpoints (P.finiteCoordinate '' S) := by
    rw [hST,←hA]
    exact hEnd
  by_contra hNo
  apply hNot
  apply hEscape S hS hSN (ξ:Mobius.ExtendedComplex) hp
  intro g
  apply disjoint_left.mpr
  rintro x ⟨t,ht,htx⟩ ⟨y,hy,hgyx⟩
  obtain ⟨r,hr,htr⟩ := hNear t (hTAB ht)
  let u:=(P.discAction g).symm r
  have he : P.discAction g (P.finiteCoordinate y)=t := by
    change P.finiteCoordinate (g • P.finiteCoordinate.symm (P.finiteCoordinate y))=t
    change g • y=x at hgyx
    rw [P.finiteCoordinate.symm_apply_apply,hgyx,←htx,P.finiteCoordinate.apply_symm_apply]
  have hu : dist u (P.finiteCoordinate y)<1 := by
    rw [←(P.discAction_isometry g).dist_eq u (P.finiteCoordinate y)]
    change dist ((P.discAction g) ((P.discAction g).symm r)) (P.discAction g (P.finiteCoordinate y))<1
    rw [(P.discAction g).apply_symm_apply,he,dist_comm]
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance] using htr
  have huL : u∈Metric.cthickening 1 L :=
    Metric.thickening_subset_cthickening 1 L (Metric.mem_thickening_iff.mpr
      ⟨P.finiteCoordinate y,⟨y,hy,rfl⟩,hu⟩)
  exact hNo ⟨g,u,huL,(P.discAction g).apply_symm_apply r ▸ hr⟩

/--
The uniform compact-core ray statement in the body,
with all actual interior starting points and all true ending rays retained.
-/
theorem finitelyGenerated_nonElementary_uniform_nonparabolic_ray_core
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H) (hFG : H.FG) :
    ∃ K : Set 𝔻,IsCompact K ∧
      ∀ξ : ℂ,(ξ:Mobius.ExtendedComplex)∈fuchsianLimitSet H→
      (¬∃f : H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val ∧ f.val.val (ξ:Mobius.ExtendedComplex)=(ξ:Mobius.ExtendedComplex))→
      ∀z : 𝔻,∀R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt z,R.idealEndpoint=(ξ:Mobius.ExtendedComplex)→
      ∃g : H,∃u∈K,P.discAction g u∈R.val := by
  obtain ⟨w,hw,_hwN⟩ := exists_dirichlet_center_in_nielsenCore P hNE
  let : Infinite H:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.nonElementary_infinite H hNE
  obtain ⟨g,hg⟩ := exists_ne (1:H)
  obtain ⟨d,_hd⟩ := finitelyGenerated_regular_dirichlet_circle_data P hFG w hw g hg 1
  exact d.uniform_nonparabolic_ray_core hNE hw

/-- The genuine original action has finite compact-to-compact transporter
sets in the actual native disc, including its finite stabilizers. -/
theorem UnitDiscFuchsianGroup.compact_disc_translate_hits_finite
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (K L : Set 𝔻) (hK : IsCompact K) (hL : IsCompact L) :
    {g : H | (P.discAction g '' K∩L).Nonempty}.Finite := by
  let : ProperlyDiscontinuousSMul H P.domain.carrier:=
    _root_.LowDimensionalTopology.Geometry.Surfaces.mobiusDomain_properlyDiscontinuous P.domain P.discontinuous
  have hf:=ProperlyDiscontinuousSMul.finite_disjoint_inter_image (Γ:=H)
    (hK.image P.finiteCoordinate.symm.continuous) (hL.image P.finiteCoordinate.symm.continuous)
  apply hf.subset
  rintro g ⟨x,⟨y,hy,hgx⟩,hxL⟩
  refine ⟨P.finiteCoordinate.symm x,⟨P.finiteCoordinate.symm y,⟨y,hy,rfl⟩,?_⟩,⟨x,hxL,rfl⟩⟩
  have he:=congrArg P.finiteCoordinate.symm hgx
  change P.finiteCoordinate.symm (P.finiteCoordinate (g • P.finiteCoordinate.symm y))=
    P.finiteCoordinate.symm x at he
  rwa [P.finiteCoordinate.symm_apply_apply] at he

/-- A genuine approximation endpoint admits one compact return set working
for every actual ending ray. The fixed reference ray, asymptotic tail
comparison and finite true compact transporters prove the uniformity. -/
theorem pointOfApproximation_uniform_ray_core
    {H : Subgroup Mobius.complexMobiusGroup} (P : UnitDiscFuchsianGroup H)
    (ξ : ℂ) (hApprox : IsFuchsianPointOfApproximation P ξ) :
    ∃ K : Set 𝔻,IsCompact K ∧ ∀z : 𝔻,∀R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt z,
      R.idealEndpoint=(ξ:Mobius.ExtendedComplex)→∃g : H,∃u∈K,P.discAction g u∈R.val := by
  classical
  let :=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  have : ProperSpace 𝔻:=disc_hyperbolic_properSpace
  obtain ⟨g,hg,hRate⟩ := hApprox.2 0
  let A:=approximationCanonicalRay 0 ξ (fuchsian_limit_finite_norm_one P ξ hApprox.1)
  have hA:=approximationCanonicalRay_endpoint 0 ξ (fuchsian_limit_finite_norm_one P ξ hApprox.1)
  have hNear:=(disc_orbit_matrix_rate_iff_ray_bound P g ξ
    (fuchsian_limit_finite_norm_one P ξ hApprox.1) 0 A hA).mp hRate
  obtain ⟨K,hK,hReturns⟩ := (disc_orbit_ray_infDist_iff_compact P g A 0).mp hNear
  refine ⟨Metric.cthickening 1 K,hK.cthickening,?_⟩
  intro z R hR
  obtain ⟨L,hL,hTail⟩ := same_endpoint_discRays_asymptotic_outside_compact A R (hA.trans hR.symm) 1 zero_lt_one
  let bad : Set H:={f | (P.discAction f '' K∩L).Nonempty}
  have hBad : bad.Finite:=_root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.compact_disc_translate_hits_finite P K L hK hL
  have hex : ∃n : ℕ,g n∉bad := by
    by_contra h
    push Not at h
    apply (infinite_range_of_injective hg)
    apply hBad.subset
    rintro _ ⟨n,rfl⟩
    exact h n
  obtain ⟨n,hn⟩ := hex
  obtain ⟨a,haA,haK⟩ := hReturns n
  have haL : P.discAction (g n) a∉L := by
    intro hh
    exact hn ⟨P.discAction (g n) a,⟨a,haK,rfl⟩,hh⟩
  obtain ⟨r,hr,har⟩ := hTail (P.discAction (g n) a) ⟨haA,haL⟩
  let u:=(P.discAction (g n)).symm r
  have hu : dist u a<1 := by
    rw [←(P.discAction_isometry (g n)).dist_eq u a]
    change dist ((P.discAction (g n)) ((P.discAction (g n)).symm r)) (P.discAction (g n) a)<1
    rw [(P.discAction (g n)).apply_symm_apply,dist_comm]
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance] using har
  refine ⟨g n,u,Metric.thickening_subset_cthickening 1 K
    (Metric.mem_thickening_iff.mpr ⟨a,haK,hu⟩),?_⟩
  exact (P.discAction (g n)).apply_symm_apply r ▸ hr

/-- The complete elementary limit set is finite; its nonparabolic points
therefore have one common genuine compact return set for all ending rays. -/
theorem elementary_uniform_nonparabolic_ray_core
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsElementary H) :
    ∃ K : Set 𝔻,IsCompact K ∧
      ∀ξ : ℂ,(ξ:Mobius.ExtendedComplex)∈fuchsianLimitSet H→
      (¬∃f : H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val ∧ f.val.val (ξ:Mobius.ExtendedComplex)=(ξ:Mobius.ExtendedComplex))→
      ∀z : 𝔻,∀R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt z,R.idealEndpoint=(ξ:Mobius.ExtendedComplex)→
      ∃g : H,∃u∈K,P.discAction g u∈R.val := by
  classical
  obtain ⟨a,b,hL⟩ := elementary_fuchsianLimitSet_subset_pair H P.discrete hE
  have hLf : (fuchsianLimitSet H).Finite:=(toFinite ({a,b}:Set Mobius.ExtendedComplex)).subset hL
  have hPre : {ξ : ℂ | (ξ:Mobius.ExtendedComplex)∈fuchsianLimitSet H}.Finite :=
    hLf.preimage OnePoint.coe_injective.injOn
  let E : Set ℂ:={ξ | (ξ:Mobius.ExtendedComplex)∈fuchsianLimitSet H ∧
    ¬∃f : H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val ∧ f.val.val (ξ:Mobius.ExtendedComplex)=(ξ:Mobius.ExtendedComplex)}
  have hEf : E.Finite:=hPre.subset (fun _ h=>h.1)
  let : Finite E:=hEf.to_subtype
  have hApprox (ξ : E) : IsFuchsianPointOfApproximation P ξ.val :=
    (elementary_split_limitSet P hE ξ.val ξ.property.1).resolve_left ξ.property.2
  choose K hK hCore using fun ξ : E=>pointOfApproximation_uniform_ray_core P ξ.val (hApprox ξ)
  refine ⟨⋃ξ : E,K ξ,isCompact_iUnion hK,?_⟩
  intro ξ hξ hNot z R hR
  let i : E:=⟨ξ,hξ,hNot⟩
  obtain ⟨g,u,hu,hgu⟩ := hCore i z R hR
  exact ⟨g,u,mem_iUnion.mpr ⟨i,hu⟩,hgu⟩

/-- The original uniform compact-core assertion for every finitely generated
Fuchsian group, including all elementary cases, all nonparabolic actual limit
points, all interior starting points and all genuine ending rays. -/
theorem finitelyGenerated_uniform_nonparabolic_ray_core
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hFG : H.FG) :
    ∃ K : Set 𝔻,IsCompact K ∧
      ∀ξ : ℂ,(ξ:Mobius.ExtendedComplex)∈fuchsianLimitSet H→
      (¬∃f : H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic f.val ∧ f.val.val (ξ:Mobius.ExtendedComplex)=(ξ:Mobius.ExtendedComplex))→
      ∀z : 𝔻,∀R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt z,R.idealEndpoint=(ξ:Mobius.ExtendedComplex)→
      ∃g : H,∃u∈K,P.discAction g u∈R.val := by
  classical
  by_cases hNE : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.IsNonElementary H
  · exact finitelyGenerated_nonElementary_uniform_nonparabolic_ray_core P hNE hFG
  · exact elementary_uniform_nonparabolic_ray_core P (Classical.not_not.mp hNE)


/-- Original disc translation infima are invariant under actual group conjugacy. -/
theorem fuchsian_disc_translationLength_conjugation
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (f g : H) :
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.dTranslationLength (P.discAction (g⁻¹*f*g))=_root_.LowDimensionalTopology.Geometry.Hyperbolic.dTranslationLength (P.discAction f) := by
  let :=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  have hcomp (z : 𝔻) : P.discAction g (P.discAction (g⁻¹*f*g) z)=
      P.discAction f (P.discAction g z) := by
    simp [_root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.discAction,mul_smul]
  unfold _root_.LowDimensionalTopology.Geometry.Hyperbolic.dTranslationLength
  congr 1
  ext r
  constructor
  · rintro ⟨z,rfl⟩
    refine ⟨P.discAction g z,?_⟩
    have he:= (P.discAction_isometry g).dist_eq z (P.discAction (g⁻¹*f*g) z)
    rw [hcomp] at he
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance] using he
  · rintro ⟨z,rfl⟩
    refine ⟨(P.discAction g).symm z,?_⟩
    have he:= (P.discAction_isometry g).dist_eq ((P.discAction g).symm z)
      (P.discAction (g⁻¹*f*g) ((P.discAction g).symm z))
    rw [hcomp,(P.discAction g).apply_symm_apply] at he
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance] using he.symm

/-- Real determinant-one coordinates represent the same genuine original disc action. -/
theorem fuchsian_disc_real_lift {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f : H) :
    ∃A : Matrix.SpecialLinearGroup (Fin 2) ℝ,
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A=_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹*f.val*_root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius ∧
      P.discAction f=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discRealGL (Matrix.SpecialLinearGroup.mapGL ℝ A) := by
  obtain ⟨A,hA,hact⟩ := P.halfPlaneAction_real_lift f
  refine ⟨A,hA,?_⟩
  funext z
  apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_injective
  rw [discAction_halfPlane_intertwine, _root_.LowDimensionalTopology.Geometry.Hyperbolic.discRealGL,
    _root_.LowDimensionalTopology.Geometry.Hyperbolic.discToHalfPlane_halfPlaneToDisc]
  exact (hact _).symm

/-- Discreteness rules out a parabolic element at either genuine hyperbolic endpoint. -/
theorem hyperbolic_fixed_not_parabolic {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val)
    (ξ : Mobius.ExtendedComplex) (hfix : f.val.val ξ=ξ) :
    ¬∃p : H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic p.val ∧ p.val.val ξ=ξ := by
  rintro ⟨p,hp,hpfix⟩
  obtain ⟨a,b,hab,hfixed⟩ := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobius_loxodromic_boundary_fixed_pair f.val hf.1
  let K:=_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H ξ
  have hK:=P.asFuchsianDisc.stabilizer_isCyclic ξ
  have hfK : f.val∈K := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ξ f.val).mpr ⟨f.property,hfix⟩
  have hpK : p.val∈K := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H ξ p.val).mpr ⟨p.property,hpfix⟩
  have hpa:=cyclic_mobius_fixedPoint K hK f.val hfK hf.1.1 a ((hfixed a).mpr (Or.inl rfl)) p.val hpK
  have hpb:=cyclic_mobius_fixedPoint K hK f.val hfK hf.1.1 b ((hfixed b).mpr (Or.inr rfl)) p.val hpK
  obtain ⟨c,hc⟩ := hp.2
  exact hab (((hc a).mp hpa).trans ((hc b).mp hpb).symm)


/-- A genuine hyperbolic element admits a true axis ray on which its actual
metric displacement equals its translation infimum at every point. -/
theorem hyperbolic_minimum_ending_ray {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val) :
    ∃ξ : ℂ,(ξ:Mobius.ExtendedComplex)∈fuchsianLimitSet H ∧
      (¬∃p : H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusParabolic p.val ∧ p.val.val (ξ:Mobius.ExtendedComplex)=(ξ:Mobius.ExtendedComplex)) ∧
      ∃z : 𝔻,∃R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt z,R.idealEndpoint=(ξ:Mobius.ExtendedComplex) ∧
        ∀w∈R.val,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist w (P.discAction f w)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.dTranslationLength (P.discAction f) := by
  obtain ⟨A,hA,hact⟩ := fuchsian_disc_real_lift P f
  have hAH : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A) := by
    rw [hA]
    simpa only [inv_inv] using _root_.LowDimensionalTopology.Geometry.Mobius.mobiusHyperbolic_conjugation_forward f.val _root_.LowDimensionalTopology.Geometry.Hyperbolic.cayleyMobius⁻¹ hf
  have hAn : _root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A≠1:=hAH.1.1
  have ht:=(_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius_hyperbolic_iff A hAn).mp hAH
  obtain ⟨w,hw,_⟩ := _root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolic_translation_minimum_attained A hAn ht
  let L:=_root_.LowDimensionalTopology.Geometry.Hyperbolic.dHyperbolicAxis A hAn ht
  have hwL : _root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w∈L.carrier := by
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.dHyperbolicAxis_carrier]
    exact ⟨w,hw,rfl⟩
  obtain ⟨a,b,_hab,he,_hu,_hi⟩ := L.exists_canonical_rays_at (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w) hwL
  have ha : a∈L.idealEndpoints:=he.symm ▸ mem_insert a {b}
  have hξex : ∃ξ : ℂ,(ξ:Mobius.ExtendedComplex)=a := by
    cases a with
    | infty => simpa [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedDiscIdealBoundary] using ha.2
    | coe ξ => exact ⟨ξ,rfl⟩
  obtain ⟨ξ,rfl⟩ := hξex
  have hAfixed : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (ξ:Mobius.ExtendedComplex))=
      _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (ξ:Mobius.ExtendedComplex) := by
    change (ξ:Mobius.ExtendedComplex)∈(_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis A hAn ht).toDiscLine.idealEndpoints at ha
    rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.HalfPlaneLine.toDiscLine_idealEndpoints] at ha
    obtain ⟨e,he,hee⟩ := ha
    have hefixed : (_root_.LowDimensionalTopology.Geometry.Hyperbolic.realSLMobius A).val e=e := by
      rw [_root_.LowDimensionalTopology.Geometry.Hyperbolic.hHyperbolicAxis_idealEndpoints] at he
      exact he
    simpa only [←hee,_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm_apply_apply] using hefixed
  have hfixed : f.val.val (ξ:Mobius.ExtendedComplex)=(ξ:Mobius.ExtendedComplex) := by
    apply _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm.injective
    rw [hA] at hAfixed
    change _root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (f.val.val (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley (_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.symm (ξ:Mobius.ExtendedComplex))))=_ at hAfixed
    simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.extendedCayley.apply_symm_apply] using hAfixed
  have hbdy := ha.2
  let R : _root_.LowDimensionalTopology.Geometry.Hyperbolic.DiscRayAt (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w):=
    ⟨_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w) ξ,ξ,hbdy,_root_.LowDimensionalTopology.Geometry.Hyperbolic.isDiscHLineRay_discHRay _ ξ hbdy⟩
  refine ⟨ξ,subset_closure ⟨f,Or.inr hf.1,hfixed⟩,
    hyperbolic_fixed_not_parabolic P f hf ξ hfixed,_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w,R,?_,?_⟩
  · exact R.idealEndpoint_eq_of_canonical_subset ξ hbdy (Subset.refl _)
  · intro z hz
    rw [hact]
    exact (_root_.LowDimensionalTopology.Geometry.Hyperbolic.dHyperbolic_translation_minimum A hAn ht z).mpr
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHRay_subset_line L (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc w) hwL ξ ha hz)


/-- One genuine compact set meets a displacement-minimizing axis in every
actual hyperbolic conjugacy class of the finitely generated group. -/
theorem finitelyGenerated_uniform_axis_minimum_core
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hFG : H.FG) :
    ∃K : Set 𝔻,IsCompact K ∧ ∀f : H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val→
      ∃g : H,∃u∈K,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discPathDist u (P.discAction (g⁻¹*f*g) u)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.dTranslationLength (P.discAction f) := by
  let :=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  obtain ⟨K,hK,hCore⟩ := finitelyGenerated_uniform_nonparabolic_ray_core P hFG
  refine ⟨K,hK,?_⟩
  intro f hf
  obtain ⟨ξ,hξ,hNot,z,R,hR,hMin⟩ := hyperbolic_minimum_ending_ray P f hf
  obtain ⟨g,u,hu,hgu⟩ := hCore ξ hξ hNot z R hR
  refine ⟨g,u,hu,?_⟩
  have he:= (P.discAction_isometry g).dist_eq u (P.discAction (g⁻¹*f*g) u)
  have hcomp : P.discAction g (P.discAction (g⁻¹*f*g) u)=
      P.discAction f (P.discAction g u) := by
    simp [_root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.discAction,mul_smul]
  rw [hcomp] at he
  rw [←hMin _ hgu]
  simpa only [_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance] using he.symm

/-- A bounded translation-length range has only finitely many true group
conjugacy representatives; the bound comes from compact transporters. -/
theorem finitelyGenerated_bounded_hyperbolic_conjugacy_representatives
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hFG : H.FG)
    (T : ℝ) :
    ∃E : Finset H,∀f : H,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic f.val→_root_.LowDimensionalTopology.Geometry.Hyperbolic.dTranslationLength (P.discAction f)≤T→
      ∃a∈E,IsConj f a := by
  classical
  let :=_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric
  have : ProperSpace 𝔻:=disc_hyperbolic_properSpace
  obtain ⟨K,hK,hMin⟩ := finitelyGenerated_uniform_axis_minimum_core P hFG
  let L:=Metric.cthickening T K
  have hL : IsCompact L:=hK.cthickening
  let E : Set H:={a | (P.discAction a '' K∩L).Nonempty}
  have hE : E.Finite:=_root_.LowDimensionalTopology.Geometry.Fuchsian.UnitDiscFuchsianGroup.compact_disc_translate_hits_finite P K L hK hL
  refine ⟨hE.toFinset,?_⟩
  intro f hf hT
  obtain ⟨g,u,hu,hdis⟩ := hMin f hf
  refine ⟨g⁻¹*f*g,?_,isConj_iff.mpr ⟨g⁻¹,by simp⟩⟩
  apply hE.mem_toFinset.mpr
  refine ⟨P.discAction (g⁻¹*f*g) u,⟨u,hu,rfl⟩,?_⟩
  apply Metric.mem_cthickening_of_dist_le _ u T K hu
  rw [dist_comm,_root_.LowDimensionalTopology.Geometry.Hyperbolic.discHyperbolicMetric_distance,hdis]
  exact hT


/-- The actual translation infimum is constant on genuine element-conjugacy classes. -/
theorem fuchsian_disc_translationLength_eq_of_isConj
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (f g : H)
    (hc : IsConj f g) : _root_.LowDimensionalTopology.Geometry.Hyperbolic.dTranslationLength (P.discAction f)=_root_.LowDimensionalTopology.Geometry.Hyperbolic.dTranslationLength (P.discAction g) := by
  obtain ⟨a,rfl⟩ := isConj_iff.mp hc
  simpa only [inv_inv] using (fuchsian_disc_translationLength_conjugation P f a⁻¹).symm

/--
any sequence of distinct genuine hyperbolic conjugacy
classes has actual metric translation lengths tending to positive infinity.
-/
theorem hyperbolic_translationLength_tendsto_atTop_of_pairwise_not_isConj
    {H : Subgroup Mobius.complexMobiusGroup}
    (P : UnitDiscFuchsianGroup H)
    (hFG : H.FG)
    (f : ℕ→H) (hf : ∀n,_root_.LowDimensionalTopology.Geometry.Mobius.MobiusHyperbolic (f n).val)
    (hclasses : Pairwise (fun m n=>¬IsConj (f m) (f n))) :
    Tendsto (fun n=>_root_.LowDimensionalTopology.Geometry.Hyperbolic.dTranslationLength (P.discAction (f n))) atTop atTop := by
  classical
  have hfinite (T : ℝ) : {n : ℕ | _root_.LowDimensionalTopology.Geometry.Hyperbolic.dTranslationLength (P.discAction (f n))≤T}.Finite := by
    obtain ⟨E,hE⟩ := finitelyGenerated_bounded_hyperbolic_conjugacy_representatives P hFG T
    have hFib (a : H) : {n : ℕ | IsConj (f n) a}.Finite := by
      apply Set.Subsingleton.finite
      intro m hm n hn
      by_contra hne
      exact hclasses hne (hm.trans hn.symm)
    apply (E.finite_toSet.biUnion (fun a _=>hFib a)).subset
    intro n hn
    obtain ⟨a,ha,hfa⟩ := hE (f n) (hf n) hn
    exact mem_iUnion₂.mpr ⟨a,ha,hfa⟩
  apply tendsto_atTop.2
  intro T
  have hh : ∀ᶠn in (atTop : Filter ℕ),n∉{n : ℕ | _root_.LowDimensionalTopology.Geometry.Hyperbolic.dTranslationLength (P.discAction (f n))≤T} :=
    (hfinite T).eventually_cofinite_notMem.filter_mono Filter.atTop_le_cofinite
  filter_upwards [hh] with n hn
  exact (lt_of_not_ge hn).le

end LowDimensionalTopology.Geometry.Fuchsian
