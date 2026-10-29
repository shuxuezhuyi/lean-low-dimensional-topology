module

public import LowDimensionalTopology.Geometry.Hyperbolic.Reflection.AnnularClippedMirrorProjectionInjective

/-!
# Distinct projected endpoint pairs separate the finite mirror clips

A common projected point intertwines the two actual mirror reflections.
The native deck element then carries the entire finite Nielsen clip to the
other one, forcing equality of their projected endpoint pairs.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set
open scoped UpperHalfPlane

namespace LowDimensionalTopology.Geometry.Hyperbolic
open LowDimensionalTopology.Geometry.DiscreteGroups.Action
open LowDimensionalTopology.Geometry.Fuchsian

variable (E r x : ℝ) (hE : 1 < E) (hr : 0 < r)
  (hin : 1 + r < x) (hout : x + r < E)
local notation "G" => annularPairReflectionGroup E r x (zero_lt_one.trans hE) hr
local notation "S" => annularPairReflectionMirrors E r x (zero_lt_one.trans hE) hr
local notation "π" => orbitProjection G ℍ
local notation "J" => annularPairQuotientReflection E r x (zero_lt_one.trans hE) hr
local notation "P" => annularPairReflectionHalfPlaneData E r x hE hr hin hout
local notation "hNE" => annularPairReflectionDiscGroup_nonElementary E r x hE hr hin
local notation "K" => HalfPlaneFuchsianGroup.cayleyCoordinate P ⁻¹'
  fuchsianNielsenCore (HalfPlaneFuchsianGroup.cayleyData P) hNE

/-- Closed finite original mirror clips with different projected endpoint
pairs have disjoint projections under the unchanged native orbit map. -/
theorem annularPairOrbitProjection_mirror_clips_disjoint
    (i j : Fin 3) (p q u v : ℍ) (hpq : p ≠ q) (huv : u ≠ v)
    (hclipi : K ∩ (S i).carrier = openHSegment p q)
    (hclipj : K ∩ (S j).carrier = openHSegment u v)
    (hpair_ne : ({π p, π q} : Set (orbitQuotient G ℍ)) ≠ {π u, π v}) :
    Disjoint (π '' closedHSegment p q) (π '' closedHSegment u v) := by
  classical
  let σ : Fin 3 → (ℍ ≃ᵢ ℍ) := fun k => halfPlaneLineReflectionIsometry (S k)
  have hcover := annularPairOrbitProjection_isCoveringMap E r x hE hr hin hout
  have hdeck (g : G) (z : ℍ) : π (g.val z) = π z := orbitProjection_smul G ℍ g z
  have hK (g : G) (z : ℍ) (hz : z ∈ K) : g • z ∈ K :=
    annularPairNativeGroup_preserves_originalNielsenLift E r x hE hr hin hout g z hz
  have hproj (k : Fin 3) (z : ℍ) : J (π z) = π (σ k z) :=
    annularPairQuotientReflection_mirror_projection E r x (zero_lt_one.trans hE) hr k z
  have hsegment (k : Fin 3) (c d : ℍ) (hcd : c ≠ d)
      (hc : K ∩ (S k).carrier = openHSegment c d) :
      closedHSegment c d ⊆ (S k).carrier := by
    have hclosed : IsClosed (S k).carrier := by
      have he : (S k).carrier = {z : ℍ | σ k z = z} := by
        ext z
        exact ((S k).reflection_fixed_iff z).symm
      rw [he]
      exact isClosed_eq (σ k).continuous continuous_id
    have hsub : openHSegment c d ⊆ (S k).carrier := by
      intro z hz
      exact (show z ∈ K ∩ (S k).carrier from hc.symm ▸ hz).2
    exact (closure_openHSegment hcd) ▸ closure_minimal hsub hclosed
  apply disjoint_left.mpr
  rintro z ⟨a, ha, hpa⟩ ⟨b, hb, hpb⟩
  obtain ⟨g, hg⟩ :=
    (Quotient.exact (hpa.trans hpb.symm).symm : MulAction.orbitRel G ℍ b a)
  have hga : g.val a = b := hg
  have hσa : σ i a = a := ((S i).reflection_fixed_iff a).mpr (hsegment i p q hpq hclipi ha)
  have hσb : σ j b = b := ((S j).reflection_fixed_iff b).mpr (hsegment j u v huv hclipj hb)
  have hinter : σ j ∘ g.val = g.val ∘ σ i := hcover.eq_of_comp_eq
      ((σ j).continuous.comp g.val.continuous) (g.val.continuous.comp (σ i).continuous) (by
        funext w
        change π (σ j (g.val w)) = π (g.val (σ i w))
        calc
          π (σ j (g.val w)) = J (π (g.val w)) := (hproj j (g.val w)).symm
          _ = J (π w) := congrArg J (hdeck g w)
          _ = π (σ i w) := hproj i w
          _ = π (g.val (σ i w)) := (hdeck g (σ i w)).symm) a (by
        change σ j (g.val a) = g.val (σ i a)
        simp only [hga, hσb, hσa])
  have hinterPoint (w : ℍ) : σ j (g.val w) = g.val (σ i w) := congrFun hinter w
  have hmirror (w : ℍ) : g.val w ∈ (S j).carrier ↔ w ∈ (S i).carrier := by
    constructor
    · intro hw
      apply ((S i).reflection_fixed_iff w).mp
      apply g.val.injective
      change g.val (σ i w) = g.val w
      rw [← hinterPoint]
      exact ((S j).reflection_fixed_iff (g.val w)).mpr hw
    · intro hw
      apply ((S j).reflection_fixed_iff (g.val w)).mp
      change σ j (g.val w) = g.val w
      have hwσ : σ i w = w := ((S i).reflection_fixed_iff w).mpr hw
      exact (hinterPoint w).trans (congrArg g.val hwσ)
  have hslice : g.val '' (K ∩ (S i).carrier) = K ∩ (S j).carrier := by
    apply subset_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact ⟨hK g w hw.1, (hmirror w).mpr hw.2⟩
    · intro w hw
      refine ⟨g.val.symm w, ⟨?_, ?_⟩, g.val.apply_symm_apply w⟩
      · change g⁻¹ • w ∈ K
        exact hK g⁻¹ w hw.1
      · apply (hmirror (g.val.symm w)).mp
        simpa only [g.val.apply_symm_apply] using hw.2
  have hopen : g.val '' openHSegment p q = openHSegment u v := by
    calc
      g.val '' openHSegment p q = g.val '' (K ∩ (S i).carrier) :=
        congrArg (fun A : Set ℍ => g.val '' A) hclipi.symm
      _ = K ∩ (S j).carrier := hslice
      _ = openHSegment u v := hclipj
  have hclosed : g.val '' closedHSegment p q = closedHSegment u v := by
    calc
      g.val '' closedHSegment p q = g.val '' closure (openHSegment p q) :=
        congrArg (fun A : Set ℍ => g.val '' A) (closure_openHSegment hpq).symm
      _ = closure (g.val '' openHSegment p q) := g.val.toHomeomorph.image_closure _
      _ = closure (openHSegment u v) := congrArg closure hopen
      _ = closedHSegment u v := closure_openHSegment huv
  have hpair : ({g.val p, g.val q} : Set ℍ) = {u, v} :=
    native_closedHSegment_image_endpoints g.val p q u v hclosed
  apply hpair_ne
  simpa only [image_pair, hdeck] using congrArg (fun A : Set ℍ => π '' A) hpair

end LowDimensionalTopology.Geometry.Hyperbolic
