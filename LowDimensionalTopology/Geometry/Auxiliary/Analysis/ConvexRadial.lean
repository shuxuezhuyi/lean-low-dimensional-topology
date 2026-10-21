module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NthRewrite
public import Mathlib.Analysis.Normed.Module.Normalize
public import Mathlib.Analysis.Convex.PathConnected

/-!
# Radial regions in real normed spaces.

Radial projection connects points of a convex set containing zero to a fixed positive
sphere. A finite preconnected cover of the spherical slice yields a finite preconnected
cover, and hence finitely many connected components, outside that sphere.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology
open scoped Pointwise

namespace LowDimensionalTopology.Geometry.Auxiliary.Analysis

/-- A finite cover by genuinely preconnected subsets gives finitely many actual components. -/
theorem finite_connectedComponentIn_image_of_finite_preconnected_cover
    {X : Type*} [TopologicalSpace X] (S : Set X) (F : Set (Set X))
    (hF : F.Finite) (hcover : S ⊆ ⋃ U ∈ F, U)
    (hsub : ∀ U ∈ F, U ⊆ S) (hconn : ∀ U ∈ F, IsPreconnected U) :
    ((fun x => connectedComponentIn S x) '' S).Finite := by
  classical
  rcases S.eq_empty_or_nonempty with he | ⟨x₀,hx₀⟩
  · rw [he,image_empty]
    exact finite_empty
  let rep : Set X → X := fun U => if h : U.Nonempty then h.choose else x₀
  apply (hF.image (fun U => connectedComponentIn S (rep U))).subset
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨U,hUF,hxU⟩ := mem_iUnion₂.mp (hcover hx)
  have hUne : U.Nonempty := ⟨x,hxU⟩
  have hrep : rep U ∈ U := by simp only [rep,dite_eq_left hUne]; exact hUne.choose_spec
  refine ⟨U,hUF,?_⟩
  exact connectedComponentIn_eq ((hconn U hUF).subset_connectedComponentIn hrep (hsub U hUF) hxU)

/-- The genuine radial projection onto a positive Euclidean sphere. -/
def radialSphereProjection {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (x : E) : E := r • NormedSpace.normalize x

theorem radialSphereProjection_norm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 < r) {x : E} (hx : x ≠ 0) :
    ‖radialSphereProjection r x‖ = r := by
  rw [radialSphereProjection,norm_smul,NormedSpace.norm_normalize hx,Real.norm_eq_abs,abs_of_pos hr,mul_one]

theorem radialSphereProjection_eq_self {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) {x : E} (hx : ‖x‖ = r) :
    radialSphereProjection r x = x := by
  rw [radialSphereProjection,←hx,NormedSpace.norm_smul_normalize]

/-- Convexity through the genuine center puts the actual radial projection back
in the original set. -/
theorem radialSphereProjection_mem_convex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : Convex ℝ U) (h0 : (0:E) ∈ U)
    (r : ℝ) (hr : 0 < r) {x : E} (hx : x ∈ U) (hrx : r ≤ ‖x‖) :
    radialSphereProjection r x ∈ U := by
  have hn : 0 < ‖x‖ := hr.trans_le hrx
  have hc : r/‖x‖ ∈ Icc (0:ℝ) 1 :=
    ⟨(div_pos hr hn).le,(div_le_one hn).mpr hrx⟩
  have hm := hU.smul_mem_of_zero_mem h0 hx hc
  simpa only [radialSphereProjection,NormedSpace.normalize,smul_smul,div_eq_mul_inv] using hm

/-- The actual part of a convex exterior lying above one genuine spherical set. -/
def convexRadialEndRegion {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (U : Set E) (r : ℝ) (A : Set E) : Set E :=
  {x | x ∈ U ∧ r ≤ ‖x‖ ∧ radialSphereProjection r x ∈ A}

/-- The entire actual radial segment stays in the original convex exterior and
has exactly the same genuine radial projection. -/
theorem radialSphereProjection_segment {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : Convex ℝ U) (h0 : (0:E) ∈ U)
    (r : ℝ) (hr : 0 < r) {x : E} (hx : x ∈ U) (hrx : r ≤ ‖x‖)
    {p : E} (hp : p ∈ segment ℝ x (radialSphereProjection r x)) :
    p ∈ U ∧ r ≤ ‖p‖ ∧ radialSphereProjection r p = radialSphereProjection r x := by
  have hxne : x ≠ 0 := by intro h; subst x; simp only [norm_zero] at hrx; linarith
  have hpu : p ∈ U := hU.segment_subset hx (radialSphereProjection_mem_convex hU h0 r hr hx hrx) hp
  obtain ⟨a,b,ha,hb,hab,hpEq⟩ := hp
  let s := a*‖x‖+b*r
  have hrs : r ≤ s := by dsimp [s]; nlinarith
  have hs : 0 < s := hr.trans_le hrs
  have hp' : p = s • NormedSpace.normalize x := by
    rw [←hpEq,radialSphereProjection]
    nth_rw 1 [←NormedSpace.norm_smul_normalize x]
    rw [smul_smul,smul_smul,←add_smul]
  have hnorm : ‖p‖ = s := by
    rw [hp',norm_smul,NormedSpace.norm_normalize hxne,Real.norm_eq_abs,abs_of_pos hs,mul_one]
  refine ⟨hpu,hnorm ▸ hrs,?_⟩
  rw [hp',radialSphereProjection,NormedSpace.normalize_smul_of_pos hs,
    NormedSpace.normalize_normalize]
  rfl

/-- A genuinely preconnected spherical set gives a genuinely preconnected radial
exterior region in the original convex set, with no assumed end classification. -/
theorem convexRadialEndRegion_preconnected
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : Convex ℝ U) (h0 : (0:E) ∈ U)
    (r : ℝ) (hr : 0 < r) {A : Set E} (hA : IsPreconnected A)
    (hAsub : A ⊆ U ∩ {x | ‖x‖ = r}) : IsPreconnected (convexRadialEndRegion U r A) := by
  have hAr : A ⊆ convexRadialEndRegion U r A := by
    intro x hx
    have hax := hAsub hx
    refine ⟨hax.1,hax.2.ge,?_⟩
    rwa [radialSphereProjection_eq_self r hax.2]
  have hseg (x : E) (hx : x ∈ convexRadialEndRegion U r A) :
      segment ℝ x (radialSphereProjection r x) ⊆ convexRadialEndRegion U r A := by
    intro p hp
    obtain ⟨hpu,hpr,hpeq⟩ := radialSphereProjection_segment hU h0 r hr hx.1 hx.2.1 hp
    exact ⟨hpu,hpr,hpeq.symm ▸ hx.2.2⟩
  apply isPreconnected_of_forall_pair
  intro x hx y hy
  let Sx := segment ℝ x (radialSphereProjection r x)
  let Sy := segment ℝ y (radialSphereProjection r y)
  have hSx : IsPreconnected Sx := (convex_segment (𝕜 := ℝ) x _).isPreconnected
  have hSy : IsPreconnected Sy := (convex_segment (𝕜 := ℝ) y _).isPreconnected
  have hSxA : IsPreconnected (Sx ∪ A) := IsPreconnected.union'
    ⟨radialSphereProjection r x,right_mem_segment ℝ x _,hx.2.2⟩ hSx hA
  have htotal : IsPreconnected ((Sx ∪ A) ∪ Sy) := IsPreconnected.union'
    ⟨radialSphereProjection r y,Or.inr hy.2.2,right_mem_segment ℝ y _⟩ hSxA hSy
  refine ⟨(Sx ∪ A) ∪ Sy,union_subset (union_subset (hseg x hx) hAr) (hseg y hy),
    Or.inl (Or.inl (left_mem_segment ℝ x _)),Or.inr (left_mem_segment ℝ y _),htotal⟩

/-- A finite genuine preconnected cover of the spherical slice gives a finite
genuine preconnected cover of the whole original convex exterior. -/
theorem convex_radial_exterior_finite_preconnected_cover
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : Convex ℝ U) (h0 : (0:E) ∈ U)
    (r : ℝ) (hr : 0 < r) (F : Set (Set E)) (hF : F.Finite)
    (hcover : U ∩ {x | ‖x‖ = r} ⊆ ⋃ A ∈ F, A)
    (hsub : ∀ A ∈ F, A ⊆ U ∩ {x | ‖x‖ = r})
    (hconn : ∀ A ∈ F, IsPreconnected A) :
    ∃ B : Set (Set E), B.Finite ∧ U ∩ {x | r ≤ ‖x‖} = ⋃ V ∈ B, V ∧
      (∀ V ∈ B, IsPreconnected V) := by
  let B := convexRadialEndRegion U r '' F
  refine ⟨B,hF.image _,?_,?_⟩
  · apply subset_antisymm
    · intro x hx
      have hxne : x ≠ 0 := by
        intro h
        have hh : r ≤ ‖x‖ := hx.2
        rw [h,norm_zero] at hh
        exact (not_le_of_gt hr) hh
      have hproj : radialSphereProjection r x ∈ U ∩ {x | ‖x‖ = r} :=
        ⟨radialSphereProjection_mem_convex hU h0 r hr hx.1 hx.2,radialSphereProjection_norm r hr hxne⟩
      obtain ⟨A,hAF,hpA⟩ := mem_iUnion₂.mp (hcover hproj)
      exact mem_iUnion₂.mpr ⟨convexRadialEndRegion U r A,⟨A,hAF,rfl⟩,hx.1,hx.2,hpA⟩
    · intro x hx
      obtain ⟨V,⟨A,hAF,rfl⟩,hx⟩ := mem_iUnion₂.mp hx
      exact ⟨hx.1,hx.2.1⟩
  · rintro V ⟨A,hAF,rfl⟩
    exact convexRadialEndRegion_preconnected hU h0 r hr (hconn A hAF) (hsub A hAF)

/-- The actual exterior of such a convex set has only finitely many genuine
connected components, derived from its actual finite spherical cover. -/
theorem convex_radial_exterior_components_finite
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} (hU : Convex ℝ U) (h0 : (0:E) ∈ U)
    (r : ℝ) (hr : 0 < r) (F : Set (Set E)) (hF : F.Finite)
    (hcover : U ∩ {x | ‖x‖ = r} ⊆ ⋃ A ∈ F, A)
    (hsub : ∀ A ∈ F, A ⊆ U ∩ {x | ‖x‖ = r})
    (hconn : ∀ A ∈ F, IsPreconnected A) :
    ((fun x => connectedComponentIn (U ∩ {y | r ≤ ‖y‖}) x) ''
      (U ∩ {x | r ≤ ‖x‖})).Finite := by
  obtain ⟨B,hB,hEq,hpre⟩ := convex_radial_exterior_finite_preconnected_cover hU h0 r hr F hF hcover hsub hconn
  apply finite_connectedComponentIn_image_of_finite_preconnected_cover _ B hB
  · rw [hEq]
  · intro V hV
    rw [hEq]
    intro x hx
    exact mem_iUnion₂.mpr ⟨V,hV,hx⟩
  · exact hpre

end LowDimensionalTopology.Geometry.Auxiliary.Analysis
