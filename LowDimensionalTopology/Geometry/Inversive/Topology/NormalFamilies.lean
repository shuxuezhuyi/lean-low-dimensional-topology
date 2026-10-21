/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.Group
public import Mathlib.Topology.UniformSpace.Ascoli
public import Mathlib.Topology.MetricSpace.Equicontinuity
public import Mathlib.Topology.Sequences
public import LowDimensionalTopology.Geometry.Inversive.Distortion.MobiusDistortion
/-!
# Equicontinuity and normal families

The common global metric modulus is identified with uniform equicontinuity.
Normality uses one subsequence converging on every compact set.
Arzelà–Ascoli and a countably generated compact-convergence uniformity
give the criterion on genuine open domains of the chordal compactification.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology Uniformity
namespace LowDimensionalTopology.Geometry.Inversive
variable {ι X Y : Type*}

def EquicontinuousFamily [PseudoMetricSpace X] [PseudoMetricSpace Y] (F : ι → X → Y) : Prop :=
  ∀ ε>0, ∃ δ>0, ∀ x y, dist x y<δ → ∀ i, dist (F i x) (F i y)<ε

theorem equicontinuousFamily_iff [PseudoMetricSpace X] [PseudoMetricSpace Y] (F : ι → X → Y) :
    EquicontinuousFamily F ↔ UniformEquicontinuous F :=
  Metric.uniformEquicontinuous_iff.symm

theorem EquicontinuousFamily.uniformContinuous [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {F : ι → X → Y} (hF : EquicontinuousFamily F) (i : ι) : UniformContinuous (F i) :=
  ((equicontinuousFamily_iff F).mp hF).uniformContinuous i

def NormalFamily [TopologicalSpace X] [UniformSpace Y] (F : ι → X → Y) : Prop :=
  ∀ u : ℕ → ι, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : X → Y,
    ∀ K : Set X, IsCompact K → TendstoUniformlyOn (fun j => F (u (φ j))) f atTop K

theorem normalFamily_of_compactwise_equicontinuous [TopologicalSpace X]
    [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X] [MetricSpace Y] [CompactSpace Y]
    {F : ι → X → Y} (hF : ∀ K : Set X, IsCompact K → EquicontinuousOn F K) : NormalFamily F := by
  classical
  let 𝔖 : Set (Set X) := {K | IsCompact K}
  let U := UniformOnFun X Y 𝔖
  let K := CompactExhaustion.choice X
  let : IsCountablyGenerated (𝓤 U) :=
    UniformOnFun.isCountablyGenerated_uniformity 𝔖 K.isCompact K.subset
      (fun _ h => K.exists_superset_of_isCompact h)
  let s : Set U := range (fun i => UniformOnFun.ofFun 𝔖 (F i))
  have hc : IsCompact (closure s) := by
    apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
      (F := UniformOnFun.toFun 𝔖) (𝔖 := 𝔖) (fun _ h => h)
    · exact Topology.IsClosedEmbedding.id
    · intro A hA
      have h := (hF A hA).comp (fun z : s => z.property.choose)
      convert h using 1
      funext z x
      have hz := congrArg (fun v : U => UniformOnFun.toFun 𝔖 v x) z.property.choose_spec
      exact hz.symm
    · intro A hA x hx
      exact ⟨univ,isCompact_univ,by intro i hi; trivial⟩
  intro u
  obtain ⟨f,hf,φ,hφ,hconv⟩ := hc.isSeqCompact (x := fun j => UniformOnFun.ofFun 𝔖 (F (u j)))
    (fun j => subset_closure ⟨u j,rfl⟩)
  refine ⟨φ,hφ,UniformOnFun.toFun 𝔖 f,?_⟩
  intro A hA
  exact (UniformOnFun.tendsto_iff_tendstoUniformlyOn.mp hconv) A hA

section Mobius
variable {n : ℕ}
local instance normalFamilyChordalMetric : MetricSpace (ExtendedEuclidean n) := chordalMetricSpace n

def MobiusNormalOn (D : TopologicalSpace.Opens (ExtendedEuclidean n)) (F : ι → GM n) : Prop :=
  NormalFamily (fun i (x : D) => (F i : ExtendedHomeomorph n) x)

theorem mobiusNormalOn_of_compactwise_equicontinuous
    (D : TopologicalSpace.Opens (ExtendedEuclidean n)) (F : ι → GM n)
    (hF : ∀ K : Set D, IsCompact K →
      UniformEquicontinuousOn (fun i (x : D) => (F i : ExtendedHomeomorph n) x) K) :
    MobiusNormalOn D F := by
  let : SecondCountableTopology (ExtendedEuclidean n) :=
    (stereographicHomeomorph n).secondCountableTopology
  let : LocallyCompactSpace D := D.isOpen.locallyCompactSpace
  have : SecondCountableTopology D := inferInstance
  apply normalFamily_of_compactwise_equicontinuous
  intro K hK
  exact (hF K hK).equicontinuousOn
end Mobius

section OmittedValues
variable [MetricSpace X]

def SeparatedOmissions (D : Set X) (F : ι → X → X) : Prop :=
  ∃ ε : ℝ, 0<ε ∧ ∀ i, ∃ a b : X, a ∉ F i '' D ∧ b ∉ F i '' D ∧ ε≤dist a b

def PositiveComplementDiameter (D : Set X) (F : ι → X → X) : Prop :=
  ∃ ε : ℝ, 0<ε ∧ ∀ i, ε≤Metric.diam (F i '' Dᶜ)

theorem homeomorph_image_compl_iff (f : X ≃ₜ X) (D : Set X) (a : X) :
    a ∈ f '' Dᶜ ↔ a ∉ f '' D := by
  change a ∈ f.toEquiv '' Dᶜ ↔ a ∉ f.toEquiv '' D
  rw [f.toEquiv.image_compl D]
  rfl

theorem separatedOmissions_iff_positiveComplementDiameter [CompactSpace X] (D : Set X) (F : ι → X ≃ₜ X) :
    SeparatedOmissions D (fun i => (F i : X → X)) ↔
      PositiveComplementDiameter D (fun i => (F i : X → X)) := by
  constructor
  · rintro ⟨ε,hε,hF⟩
    refine ⟨ε,hε,?_⟩
    intro i
    obtain ⟨a,b,ha,hb,hab⟩ := hF i
    have ha' := (homeomorph_image_compl_iff (F i) D a).mpr ha
    have hb' := (homeomorph_image_compl_iff (F i) D b).mpr hb
    have hbound : Bornology.IsBounded (F i '' Dᶜ) :=
      (isCompact_univ : IsCompact (univ : Set X)).isBounded.subset (subset_univ _)
    exact hab.trans (Metric.dist_le_diam_of_mem hbound ha' hb')
  · rintro ⟨ε,hε,hF⟩
    refine ⟨ε/2,by positivity,?_⟩
    intro i
    have hex : ∃ a ∈ F i '' Dᶜ, ∃ b ∈ F i '' Dᶜ, ε/2<dist a b := by
      by_contra! hn
      have hdiam : Metric.diam (F i '' Dᶜ) ≤ ε/2 :=
        Metric.diam_le_of_forall_dist_le (by positivity) hn
      have h := hF i
      linarith
    obtain ⟨a,ha,b,hb,hab⟩ := hex
    exact ⟨a,b,(homeomorph_image_compl_iff (F i) D a).mp ha,
      (homeomorph_image_compl_iff (F i) D b).mp hb,hab.le⟩
theorem positiveComplementDiameter_iff_iInf_pos [Nonempty ι]
    (D : Set X) (F : ι → X → X) :
    PositiveComplementDiameter D F ↔ 0 < ⨅ i, Metric.diam (F i '' Dᶜ) := by
  constructor
  · rintro ⟨ε,hε,hF⟩
    exact hε.trans_le (le_ciInf hF)
  · intro h
    refine ⟨_,h,fun i => ciInf_le ?_ i⟩
    exact ⟨0,by rintro _ ⟨j,rfl⟩; exact Metric.diam_nonneg⟩

end OmittedValues


section MobiusOmittedValues
variable {n : ℕ}
local instance omittedValuesChordalMetric : MetricSpace (ExtendedEuclidean n) := chordalMetricSpace n

theorem mobius_separatedOmissions_iff_positiveComplementDiameter
    (D : Set (ExtendedEuclidean n)) (F : ι → GM n) :
    SeparatedOmissions D (fun i z => (F i : ExtendedHomeomorph n) z) ↔
      PositiveComplementDiameter D (fun i z => (F i : ExtendedHomeomorph n) z) :=
  separatedOmissions_iff_positiveComplementDiameter D (fun i => (F i : ExtendedHomeomorph n))
theorem mobius_separatedOmissions_iff_iInf_diameter_pos [Nonempty ι]
    (D : Set (ExtendedEuclidean n)) (F : ι → GM n) :
    SeparatedOmissions D (fun i z => (F i : ExtendedHomeomorph n) z) ↔
      0 < ⨅ i, Metric.diam ((fun z => (F i : ExtendedHomeomorph n) z) '' Dᶜ) :=
  (mobius_separatedOmissions_iff_positiveComplementDiameter D F).trans
    (positiveComplementDiameter_iff_iInf_pos D _)
theorem mobiusNormalOn_of_separatedOmissions
    (D : TopologicalSpace.Opens (ExtendedEuclidean n)) (F : ι → GM n)
    (hF : SeparatedOmissions (D : Set (ExtendedEuclidean n))
      (fun i z => (F i : ExtendedHomeomorph n) z)) : MobiusNormalOn D F := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl h =>
    intro u
    exact (h.false (u 0)).elim
  | inr h =>
    let : Nonempty ι := h
    obtain ⟨ε,hε,hF⟩ := hF
    obtain ⟨a,b,ha,_,_⟩ := hF (Classical.choice h)
    have hcompl : (D : Set (ExtendedEuclidean n))ᶜ |>.Nonempty := by
      refine ⟨(F (Classical.choice h) : ExtendedHomeomorph n).symm a,?_⟩
      intro hx
      exact ha ⟨_,hx,(F (Classical.choice h) : ExtendedHomeomorph n).apply_symm_apply a⟩
    apply mobiusNormalOn_of_compactwise_equicontinuous
    intro K hK
    have hex : ∃ r : ℝ, 0<r ∧ ∀ x ∈ K,
        r≤Metric.infDist x.val (D : Set (ExtendedEuclidean n))ᶜ := by
      rcases K.eq_empty_or_nonempty with rfl | hne
      · exact ⟨1,by positivity,by intro x hx; exact hx.elim⟩
      obtain ⟨x,hx,hmin⟩ := hK.exists_isMinOn hne
        ((Metric.continuous_infDist_pt (D : Set (ExtendedEuclidean n))ᶜ).comp
          continuous_subtype_val).continuousOn
      refine ⟨_,?_,hmin⟩
      exact (D.isOpen.isClosed_compl.notMem_iff_infDist_pos hcompl).mp (by
        intro hx
        exact hx x.property)
    obtain ⟨r,hr,hrK⟩ := hex
    rw [← uniformEquicontinuous_restrict_iff,Metric.uniformEquicontinuous_iff]
    intro η hη
    let C : ℝ := 8/(ε*r)
    have hC : 0<C := div_pos (by norm_num) (mul_pos hε hr)
    refine ⟨η/C,div_pos hη hC,?_⟩
    intro x y hxy i
    obtain ⟨a,b,ha,hb,hab⟩ := hF i
    have hbnd := generalMobius_omitted_distortion_uniform (F i) (F i).property
      (D : Set (ExtendedEuclidean n)) D.isOpen a b ε r hε hr ha hb hab
      x.val.val y.val.val x.val.property y.val.property (hrK _ x.property) (hrK _ y.property)
    change dist ((F i : ExtendedHomeomorph n) x.val.val)
      ((F i : ExtendedHomeomorph n) y.val.val) < η
    have hbound : dist ((F i : ExtendedHomeomorph n) x.val.val)
        ((F i : ExtendedHomeomorph n) y.val.val) ≤ C*dist x y := hbnd
    exact hbound.trans_lt (by nlinarith [(lt_div_iff₀ hC).mp hxy])

end MobiusOmittedValues

end LowDimensionalTopology.Geometry.Inversive
