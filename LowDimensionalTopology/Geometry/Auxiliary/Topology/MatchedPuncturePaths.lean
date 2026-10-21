module
public import LowDimensionalTopology.Geometry.Surfaces.Topology.FinitePunctureExtension
@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter Topology
namespace LowDimensionalTopology.Geometry.Auxiliary.Topology


set_option backward.isDefEq.respectTransparency false in
/-- Matching actual old-part paths determines a genuine homeomorphism of finite surface completions. -/
theorem homeomorph_of_matching_puncture_paths {O X Y:Type*}
    [TopologicalSpace O] [TopologicalSpace X] [T2Space X] [CompactSpace X] [Nonempty X]
    [ChartedSpace ℂ X] [TopologicalSpace Y] [T2Space Y] [ChartedSpace ℂ Y]
    (I:O→X) (J:O→Y) (hI:Topology.IsOpenEmbedding I) (hJ:Topology.IsOpenEmbedding J)
    (hA:(range I)ᶜ.Finite) (hB:(range J)ᶜ.Finite)
    (hMatch:∀a∉range I,∃b∉range J,∃u:ℕ→O,
      Tendsto (I∘u) atTop (𝓝 a) ∧Tendsto (J∘u) atTop (𝓝 b)) :
    ∃E:X≃ₜY,∀o:O,E (I o)=J o := by
  classical
  let A:Set X:=(range I)ᶜ
  let B:Set Y:=(range J)ᶜ
  let eI:O≃ₜrange I:=hI.isEmbedding.toHomeomorph
  let eJ:O≃ₜrange J:=hJ.isEmbedding.toHomeomorph
  let e:↥(Aᶜ)≃ₜ↥(Bᶜ):=
    (Homeomorph.setCongr (compl_compl (range I))).trans
      ((eI.symm.trans eJ).trans (Homeomorph.setCongr (compl_compl (range J))).symm)
  let F:X→Y:=fun x=>if hx:x∈range I then J (eI.symm ⟨x,hx⟩) else (hMatch x hx).choose
  have hF:∀o:O,F (I o)=J o:=by
    intro o
    have ho:I o∈range I:=mem_range_self o
    dsimp only [F]
    rw [dite_eq_left ho]
    have hpre:eI.symm ⟨I o,ho⟩=o:=eI.symm_apply_apply o
    rw [hpre]
  have he:∀x:↥(Aᶜ),F x=(e x).val:=by
    intro x
    have hx:x.val∈range I:=by simpa only [A,compl_compl] using x.property
    dsimp only [F]
    rw [dite_eq_left hx]
    rfl
  have hNew:∀x∈A,F x∈B:=by
    intro x hx
    change x∉range I at hx
    change F x∉range J
    dsimp only [F]
    rw [dite_eq_right hx]
    exact (hMatch x hx).choose_spec.1
  have hcluster:∀a∈A,MapClusterPt (F a) (𝓝[Aᶜ] a) F:=by
    intro a ha
    change a∉range I at ha
    obtain ⟨u,hu,hJu⟩:=(hMatch a ha).choose_spec.2
    have hFa:F a=(hMatch a ha).choose:=dite_eq_right ha
    rw [hFa]
    apply Surfaces.puncture_mapClusterPt_of_two_limits A a ((hMatch a ha).choose) (I ∘ u) F hu
    · filter_upwards [] with n
      change ¬¬I (u n)∈range I
      exact not_not.mpr (mem_range_self _)
    · apply hJu.congr'
      filter_upwards [] with n
      exact (hF (u n)).symm
  have hh :=
    Surfaces.chartedComplex_finite_puncture_isHomeomorph A hA B hB e F he hNew hcluster
  exact ⟨hh.homeomorph,hF⟩

end LowDimensionalTopology.Geometry.Auxiliary.Topology
