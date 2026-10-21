/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.Atlas
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Compactness.LocallyCompact
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
namespace LowDimensionalTopology.Geometry.Surfaces

def ConnectedPuncturedNeighborhoods (X : Type*) [TopologicalSpace X] : Prop :=
  ∀x:X,∀s:Set X,s∈𝓝 x→∃t:Set X,t∈𝓝 x ∧t⊆s ∧IsPreconnected (t\{x})

theorem puncture_homeomorph_compact_preimage {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (A:Set X) (B:Set Y)
    (e:↥(Aᶜ) ≃ₜ ↥(Bᶜ)) (F:X→Y) (he:∀x:↥(Aᶜ),F x=(e x).val)
    (K:Set Y) (hK:IsCompact K) (hKB:K⊆Bᶜ) :
    IsCompact (Aᶜ∩F ⁻¹' K) := by
  have hKs:IsCompact (((↑):↥(Bᶜ)→Y) ⁻¹' K):=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK (by simpa only [Subtype.range_val] using hKB)
  have h:=hKs.image (continuous_subtype_val.comp e.symm.continuous)
  convert h using 1
  ext x
  constructor
  · rintro ⟨hx,hFx⟩
    refine ⟨e ⟨x,hx⟩,?_,?_⟩
    · change (e ⟨x,hx⟩).val∈K
      rwa [←he ⟨x,hx⟩]
    · simp only [Function.comp_apply,e.symm_apply_apply]
  · rintro ⟨y,hy,rfl⟩
    refine ⟨(e.symm y).property,?_⟩
    change F ((e.symm y):X)∈K
    rw [he,e.apply_symm_apply]
    exact hy

theorem finite_punctures_compact_frontier_neighborhood {Y : Type*}
    [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (B:Set Y) (hB:B.Finite) (b:Y) (s:Set Y) (hs:s∈𝓝 b) :
    ∃V:Set Y,IsOpen V ∧b∈V ∧V⊆s ∧IsCompact (frontier V) ∧frontier V⊆Bᶜ := by
  have hb:b∉B\{b}:=by simp
  have hn:(B\{b})ᶜ∈𝓝 b:=hB.sdiff.isClosed.isOpen_compl.mem_nhds hb
  obtain ⟨K,hKn,hKsub,hKc⟩:=local_compact_nhds (inter_mem hs hn)
  let V:=interior K
  have hVK:closure V⊆K:=closure_minimal interior_subset hKc.isClosed
  have hbV:b∈V:=mem_interior_iff_mem_nhds.mpr hKn
  refine ⟨V,isOpen_interior,hbV,interior_subset.trans (hKsub.trans inter_subset_left),
    hKc.of_isClosed_subset isClosed_frontier (frontier_subset_closure.trans hVK),?_⟩
  intro y hy hyB
  have hyK:y∈K:=hVK (frontier_subset_closure hy)
  have hyne:y≠b:=by
    intro heq
    subst y
    exact ((disjoint_frontier_iff_isOpen.mpr (show IsOpen V from isOpen_interior)).notMem_of_mem_left hy) hbV
  exact (hKsub hyK).2 ⟨hyB,by simpa only [mem_singleton_iff] using hyne⟩

theorem puncture_mapClusterPt_tendsto {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (A:Set X) (hA:A.Finite) (B:Set Y) (hB:B.Finite)
    (e:↥(Aᶜ) ≃ₜ ↥(Bᶜ)) (F:X→Y) (he:∀x:↥(Aᶜ),F x=(e x).val)
    (hOne:ConnectedPuncturedNeighborhoods X) (a:X) (ha:a∈A) (b:Y)
    (hcluster:MapClusterPt b (𝓝[Aᶜ] a) F) : Tendsto F (𝓝[Aᶜ] a) (𝓝 b) := by
  have hf:ContinuousOn F Aᶜ:=by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp e.continuous).congr (fun x=>(he x).symm)
  apply tendsto_def.mpr
  intro s hs
  obtain ⟨V,hVo,hbV,hVs,hVcomp,hVB⟩:=finite_punctures_compact_frontier_neighborhood B hB b s hs
  let K:=Aᶜ∩F ⁻¹' frontier V
  have hK:IsCompact K:=puncture_homeomorph_compact_preimage A B e F he _ hVcomp hVB
  have haK:a∉K:=by intro h;exact h.1 ha
  have hKa:Kᶜ∈𝓝 a:=hK.isClosed.isOpen_compl.mem_nhds haK
  have hother:(A\{a})ᶜ∈𝓝 a:=hA.sdiff.isClosed.isOpen_compl.mem_nhds (by simp)
  obtain ⟨U,hUa,hUsub,hUconn⟩:=hOne a (Kᶜ∩(A\{a})ᶜ) (inter_mem hKa hother)
  have hUold:U\{a}⊆Aᶜ:=by
    intro x hx hxA
    exact (hUsub hx.1).2 ⟨hxA,hx.2⟩
  have hne:∀x∈Aᶜ,x≠a:=by intro x hx h;subst x;exact hx ha
  have himconn:IsPreconnected (F '' (U\{a})):=hUconn.image F (hf.mono hUold)
  have hfreq:=hcluster.frequently (hVo.mem_nhds hbV)
  have hUevent:∀ᶠx in 𝓝[Aᶜ] a,x∈U ∧x∈Aᶜ:=by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hUa,self_mem_nhdsWithin] with x hx hxA
    exact ⟨hx,hxA⟩
  obtain ⟨x,hxV,hxU,hxA⟩:=(hfreq.and_eventually hUevent).exists
  have hinter:(F '' (U\{a})∩V).Nonempty:=⟨F x,⟨x,⟨hxU,by simpa only [mem_singleton_iff] using hne x hxA⟩,rfl⟩,hxV⟩
  have himsub:F '' (U\{a})⊆V:=by
    apply himconn.subset_of_closure_inter_subset hVo hinter
    rintro y ⟨hyCl,z,hz,rfl⟩
    by_contra hyV
    have hyFront:F z∈frontier V:=by
      rw [frontier,hVo.interior_eq]
      exact ⟨hyCl,hyV⟩
    exact (hUsub hz.1).1 ⟨hUold hz,hyFront⟩
  filter_upwards [hUevent] with x hx
  exact hVs (himsub ⟨x,⟨hx.1,by simpa only [mem_singleton_iff] using hne x hx.2⟩,rfl⟩)

theorem puncture_mapClusterPt_symm {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (A:Set X) (B:Set Y) (e:↥(Aᶜ) ≃ₜ ↥(Bᶜ))
    (F:X→Y) (G:Y→X) (he:∀x:↥(Aᶜ),F x=(e x).val)
    (hG:∀y:↥(Bᶜ),G y=(e.symm y).val) (a:X) (b:Y)
    (hcluster:MapClusterPt b (𝓝[Aᶜ] a) F) : MapClusterPt a (𝓝[Bᶜ] b) G := by
  apply mapClusterPt_iff_frequently.mpr
  intro U hU
  rw [frequently_nhdsWithin_iff]
  change ∃ᶠx in 𝓝 b,x∈{y|G y∈U ∧y∈Bᶜ}
  rw [←mem_closure_iff_frequently]
  apply mem_closure_iff_nhds.mpr
  intro V hV
  have hfreq:=hcluster.frequently hV
  have hUevent:∀ᶠx in 𝓝[Aᶜ] a,x∈U ∧x∈Aᶜ:=by
    filter_upwards [mem_nhdsWithin_of_mem_nhds hU,self_mem_nhdsWithin] with x hx hxA
    exact ⟨hx,hxA⟩
  obtain ⟨x,hxV,hxU,hxA⟩:=(hfreq.and_eventually hUevent).exists
  have hFB:F x∈Bᶜ:=by rw [he ⟨x,hxA⟩];exact (e ⟨x,hxA⟩).property
  have hGF:G (F x)=x:=by
    rw [he ⟨x,hxA⟩,hG (e ⟨x,hxA⟩),e.symm_apply_apply]
  exact ⟨F x,hxV,by simpa only [mem_ofPred_eq,hGF] using And.intro hxU hFB⟩

theorem finite_puncture_map_continuous {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (A:Set X) (hA:A.Finite) (B:Set Y) (hB:B.Finite)
    (e:↥(Aᶜ) ≃ₜ ↥(Bᶜ)) (F:X→Y) (he:∀x:↥(Aᶜ),F x=(e x).val)
    (hOne:ConnectedPuncturedNeighborhoods X)
    (hcluster:∀a∈A,MapClusterPt (F a) (𝓝[Aᶜ] a) F) : Continuous F := by
  have hf:ContinuousOn F Aᶜ:=by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp e.continuous).congr (fun x=>(he x).symm)
  apply continuous_iff_continuousAt.mpr
  intro a
  by_cases ha:a∈A
  · apply continuousAt_iff_punctured_nhds.mpr
    have heq:𝓝[Aᶜ] a=𝓝[≠] a:=by
      apply nhdsWithin_eq_iff_eventuallyEqSet.mpr
      filter_upwards [hA.sdiff.isClosed.isOpen_compl.mem_nhds (show a∉A\{a} by simp)] with x hx
      apply propext
      change (x∉A)↔x≠a
      constructor
      · intro hxA h;subst x;exact hxA ha
      · intro hne hxA;exact hx ⟨hxA,by simpa only [mem_singleton_iff] using hne⟩
    rw [←heq]
    exact puncture_mapClusterPt_tendsto A hA B hB e F he hOne a ha (F a) (hcluster a ha)
  · exact (hf a ha).continuousAt (hA.isClosed.isOpen_compl.mem_nhds ha)

theorem finite_puncture_map_isHomeomorph {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (A:Set X) (hA:A.Finite) (B:Set Y) (hB:B.Finite) (hDenseB:Dense Bᶜ)
    (e:↥(Aᶜ) ≃ₜ ↥(Bᶜ)) (F:X→Y) (he:∀x:↥(Aᶜ),F x=(e x).val)
    (hNew:∀a∈A,F a∈B)
    (hOneX:ConnectedPuncturedNeighborhoods X) (hOneY:ConnectedPuncturedNeighborhoods Y)
    (hcluster:∀a∈A,MapClusterPt (F a) (𝓝[Aᶜ] a) F) : IsHomeomorph F := by
  have hf:=finite_puncture_map_continuous A hA B hB e F he hOneX hcluster
  classical
  let G:Y→X:=fun y=>if hy:y∈B then Classical.choice (inferInstance:Nonempty X) else (e.symm ⟨y,hy⟩).val
  have hG:∀y:↥(Bᶜ),G y=(e.symm y).val:=by intro y;simp only [G,dite_eq_right y.property]
  have hOld:∀x∉A,F x∉B:=by intro x hx;rw [he ⟨x,hx⟩];exact (e ⟨x,hx⟩).property
  have hinj:Function.Injective F:=by
    intro x x' hxx
    by_cases hx:x∈A
    · have hx':x'∈A:=by
        by_contra hn
        exact hOld x' hn (hxx ▸ hNew x hx)
      let b:=F x
      have hb:b∈B:=hNew x hx
      have hCx:MapClusterPt x (𝓝[Bᶜ] b) G:=puncture_mapClusterPt_symm A B e F G he hG x b (hcluster x hx)
      have hCx':MapClusterPt x' (𝓝[Bᶜ] b) G:=by
        have h:=puncture_mapClusterPt_symm A B e F G he hG x' (F x') (hcluster x' hx')
        simpa only [←hxx] using h
      have ht:=puncture_mapClusterPt_tendsto B hB A hA e.symm G hG hOneY b hb x hCx
      have ht':=puncture_mapClusterPt_tendsto B hB A hA e.symm G hG hOneY b hb x' hCx'
      have : NeBot (𝓝[Bᶜ] b):=mem_closure_iff_nhdsWithin_neBot.mp (hDenseB b)
      exact tendsto_nhds_unique ht ht'
    · have hx':x'∉A:=by intro hx';exact hOld x hx (hxx.symm ▸ hNew x' hx')
      have h:e ⟨x,hx⟩=e ⟨x',hx'⟩:=Subtype.ext ((he ⟨x,hx⟩).symm.trans (hxx.trans (he ⟨x',hx'⟩)))
      exact congrArg Subtype.val (e.injective h)
  have hsur:Function.Surjective F:=by
    intro y
    have hOldRange:Bᶜ⊆range F:=by
      intro z hz
      refine ⟨(e.symm ⟨z,hz⟩).val,?_⟩
      rw [he,e.apply_symm_apply]
    exact closure_minimal hOldRange (isCompact_range hf).isClosed (hDenseB y)
  exact isHomeomorph_iff_continuous_bijective.mpr ⟨hf,hinj,hsur⟩

theorem complex_punctured_ball_preconnected (a:ℂ) (r:ℝ) (hr:0<r) :
    IsPreconnected (Metric.ball a r\{a}) := by
  let H:Set ℂ:={z|z.re<Real.log r}
  have hH:IsPreconnected H:=((convex_Iio (Real.log r)).linear_preimage Complex.reCLM.toLinearMap).isPreconnected
  have heq:(fun z:ℂ=>a+Complex.exp z) '' H=Metric.ball a r\{a}:=by
    ext w
    constructor
    · rintro ⟨z,hz,rfl⟩
      refine ⟨?_,?_⟩
      · rw [Metric.mem_ball,dist_eq_norm,show a+Complex.exp z-a=Complex.exp z by ring,Complex.norm_exp]
        exact (Real.exp_lt_exp.mpr hz).trans_eq (Real.exp_log hr)
      · simp only [mem_singleton_iff]
        intro h
        exact Complex.exp_ne_zero z (by linear_combination h)
    · rintro ⟨hw,hwa⟩
      have hne:w-a≠0:=sub_ne_zero.mpr (by simpa only [mem_singleton_iff] using hwa)
      have hnorm:‖w-a‖<r:=by simpa only [Metric.mem_ball,dist_eq_norm] using hw
      refine ⟨Complex.log (w-a),?_,?_⟩
      · change (Complex.log (w-a)).re<Real.log r
        rw [Complex.log_re]
        exact Real.log_lt_log (norm_pos_iff.mpr hne) hnorm
      · dsimp only
        rw [Complex.exp_log hne];ring
  rw [←heq]
  exact hH.image _ (continuous_const.add Complex.continuous_exp).continuousOn

theorem chartedComplex_connectedPuncturedNeighborhoods (X:Type*)
    [TopologicalSpace X] [ChartedSpace ℂ X] : ConnectedPuncturedNeighborhoods X := by
  intro x U hU
  let e:=chartAt ℂ x
  have hx:x∈e.source:=mem_chart_source ℂ x
  have ht:e.target∈𝓝 (e x):=e.open_target.mem_nhds (e.map_source hx)
  have hU':e.symm ⁻¹' U∈𝓝 (e x):=(e.tendsto_symm hx) hU
  obtain ⟨r,hr,hrsub⟩:=Metric.mem_nhds_iff.mp (inter_mem ht hU')
  let V:=e.symm '' Metric.ball (e x) r
  have hV:V∈𝓝 x:=by
    have h:=e.symm.image_mem_nhds (e.map_source hx) (Metric.ball_mem_nhds (e x) hr)
    simpa only [e.left_inv hx] using h
  have hVU:V⊆U:=by rintro y ⟨z,hz,rfl⟩;exact (hrsub hz).2
  have heq:V\{x}=e.symm '' (Metric.ball (e x) r\{e x}):=by
    ext y
    constructor
    · rintro ⟨⟨z,hz,rfl⟩,hne⟩
      refine ⟨z,⟨hz,?_⟩,rfl⟩
      intro he
      have hz':z=e x:=by simpa only [mem_singleton_iff] using he
      rw [hz',e.left_inv hx] at hne
      exact hne (mem_singleton x)
    · rintro ⟨z,⟨hz,hne⟩,rfl⟩
      refine ⟨⟨z,hz,rfl⟩,?_⟩
      intro he
      have he':e.symm z=x:=by simpa only [mem_singleton_iff] using he
      have hz':z=e x:=(e.right_inv (hrsub hz).1).symm.trans (congrArg e he')
      exact hne (by simpa only [mem_singleton_iff] using hz')
  refine ⟨V,hV,hVU,?_⟩
  rw [heq]
  exact (complex_punctured_ball_preconnected (e x) r hr).image e.symm
    (e.continuousOn_symm.mono (fun z hz=>(hrsub hz.1).1))

theorem chartedComplex_finite_complement_dense (X:Type*)
    [TopologicalSpace X] [ChartedSpace ℂ X] (B:Set X) (hB:B.Finite) : Dense Bᶜ := by
  apply dense_iff_inter_open.mpr
  intro U hUo hUn
  obtain ⟨x,hxU⟩:=hUn
  let e:=chartAt ℂ x
  have hx:x∈e.source:=mem_chart_source ℂ x
  have ht:e.target∈𝓝 (e x):=e.open_target.mem_nhds (e.map_source hx)
  have hU':e.symm ⁻¹' U∈𝓝 (e x):=(e.tendsto_symm hx) (hUo.mem_nhds hxU)
  obtain ⟨r,hr,hrsub⟩:=Metric.mem_nhds_iff.mp (inter_mem ht hU')
  have hd:Dense (e '' B)ᶜ:=(hB.image e).countable.dense_compl ℝ
  obtain ⟨z,hz,hzB⟩:=hd.inter_open_nonempty (Metric.ball (e x) r) Metric.isOpen_ball
    ⟨e x,Metric.mem_ball_self hr⟩
  refine ⟨e.symm z,(hrsub hz).2,?_⟩
  intro hb
  exact hzB ⟨e.symm z,hb,e.right_inv (hrsub hz).1⟩

theorem chartedComplex_finite_puncture_isHomeomorph {X Y : Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X] [ChartedSpace ℂ X]
    [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y]
    (A:Set X) (hA:A.Finite) (B:Set Y) (hB:B.Finite)
    (e:↥(Aᶜ) ≃ₜ ↥(Bᶜ)) (F:X→Y) (he:∀x:↥(Aᶜ),F x=(e x).val)
    (hNew:∀a∈A,F a∈B)
    (hcluster:∀a∈A,MapClusterPt (F a) (𝓝[Aᶜ] a) F) : IsHomeomorph F := by
  let : LocallyCompactSpace Y:=ChartedSpace.locallyCompactSpace ℂ Y
  exact finite_puncture_map_isHomeomorph A hA B hB (chartedComplex_finite_complement_dense Y B hB)
    e F he hNew (chartedComplex_connectedPuncturedNeighborhoods X)
    (chartedComplex_connectedPuncturedNeighborhoods Y) hcluster

theorem puncture_mapClusterPt_of_two_limits {Z X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] {l:Filter Z} [l.NeBot]
    (A:Set X) (a:X) (b:Y) (u:Z→X) (F:X→Y)
    (hu:Tendsto u l (𝓝 a)) (hOld:∀ᶠz in l,u z∈Aᶜ)
    (hF:Tendsto (F∘u) l (𝓝 b)) : MapClusterPt b (𝓝[Aᶜ] a) F := by
  have hWithin:Tendsto u l (𝓝[Aᶜ] a):=tendsto_nhdsWithin_iff.mpr ⟨hu,hOld⟩
  have hmap:map (F∘u) l≤map F (𝓝[Aᶜ] a):=by
    rw [←Filter.map_map]
    exact Filter.map_mono hWithin
  exact hF.mapClusterPt.clusterPt.mono hmap

end LowDimensionalTopology.Geometry.Surfaces
