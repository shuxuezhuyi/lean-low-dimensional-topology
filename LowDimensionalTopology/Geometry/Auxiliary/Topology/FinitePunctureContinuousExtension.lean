/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.FinitePunctureExtension
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace LowDimensionalTopology.Geometry.Auxiliary.Topology


set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 600000 in
/-- For a continuous extension across finite exceptional sets, connected punctured neighborhoods
in the target suffice to turn the extension into a homeomorphism. -/
theorem finite_puncture_continuous_map_isHomeomorph {X Y:Type*}
    [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (A:Set X) (hA:A.Finite) (B:Set Y) (hB:B.Finite) (hDenseB:Dense Bᶜ)
    (e:↥(Aᶜ)≃ₜ↥(Bᶜ)) (F:X→Y) (he:∀x:↥(Aᶜ),F x=(e x).val)
    (hf:Continuous F) (hNew:∀a∈A,F a∈B)
    (hOneY:Surfaces.ConnectedPuncturedNeighborhoods Y)
    (hcluster:∀a∈A,MapClusterPt (F a) (𝓝[Aᶜ] a) F) : IsHomeomorph F := by
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
      have hCx : MapClusterPt x (𝓝[Bᶜ] b) G :=
        Surfaces.puncture_mapClusterPt_symm A B e F G he hG x b (hcluster x hx)
      have hCx':MapClusterPt x' (𝓝[Bᶜ] b) G:=by
        have h:=Surfaces.puncture_mapClusterPt_symm A B e F G he hG x' (F x') (hcluster x' hx')
        simpa only [←hxx] using h
      have ht:=Surfaces.puncture_mapClusterPt_tendsto B hB A hA e.symm G hG hOneY b hb x hCx
      have ht':=Surfaces.puncture_mapClusterPt_tendsto B hB A hA e.symm G hG hOneY b hb x' hCx'
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

end LowDimensionalTopology.Geometry.Auxiliary.Topology
