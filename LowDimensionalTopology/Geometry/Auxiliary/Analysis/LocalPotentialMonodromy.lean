module

public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Sheaves.EtaleSpace
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.LinearCombination

/-!
# Topological gluing of actual locally specified functions

Actual local complex-valued functions with locally constant overlap
differences define a sheaf of functions locally equal to a model plus a constant.
Section and stalk evaluation bijections prove the actual local germ covering
criterion. A continuous lift over the simply connected base then gives one
global function with those same local expressions. No global primitive,
covering, germ bijection or differentiable homotopy is an input to the public
theorem. The universe-zero base includes the original open planar domains.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open Set Filter TopologicalSpace Opposite CategoryTheory
open scoped Topology

namespace LowDimensionalTopology.Geometry

universe u

/-- Evaluation turns the actual section and stalk value bijections into the
local germ bijection required by the genuine covering criterion. -/
private theorem germ_bijective_of_point_evaluations
    {X : TopCat.{u}} {T : Type u}
    (P : TopCat.LocalPredicate (fun _ : X => T))
    (U : Opens X) (x : X) (hx : x ∈ U)
    (hstalk : Function.Bijective (TopCat.stalkToFiber P x))
    (hsections : Function.Bijective
      (fun s : (TopCat.subsheafToTypes P).presheaf.obj (op U) => s.1 ⟨x, hx⟩)) :
    Function.Bijective ((TopCat.subsheafToTypes P).presheaf.germ U x hx) := by
  have hcomp : (TopCat.stalkToFiber P x) ∘
      ((TopCat.subsheafToTypes P).presheaf.germ U x hx) =
      (fun s => s.1 ⟨x, hx⟩) := by
    funext s
    exact TopCat.stalkToFiber_germ P U x hx s
  apply (Function.Bijective.of_comp_iff' hstalk
    ((TopCat.subsheafToTypes P).presheaf.germ U x hx)).mp
  rw [hcomp]
  exact hsections

/-- A local predicate whose germs are genuinely constant across sufficiently
small neighborhoods has a global section over a simply connected locally path
connected base. A specified initial germ fixes its value at the base point. -/
private theorem exists_global_localPredicate_section
    {X : TopCat.{u}} {T : Type u}
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (P : TopCat.LocalPredicate (fun _ : X => T)) (x₀ : X)
    (g₀ : (TopCat.subsheafToTypes P).presheaf.stalk x₀)
    (hlocal : ∀ x : X, ∃ U : Opens X, x ∈ U ∧
      ∀ y : X, ∀ hy : y ∈ U,
        Function.Bijective ((TopCat.subsheafToTypes P).presheaf.germ U y hy)) :
    ∃ f : (x : (⊤ : Opens X)) → T, P.pred f ∧
      f ⟨x₀, mem_univ x₀⟩ = TopCat.stalkToFiber P x₀ g₀ := by
  let F := (TopCat.subsheafToTypes P).presheaf
  have hcover : IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := F)) :=
    TopCat.Presheaf.EtaleSpace.isCoveringMap_base hlocal
  let e₀ : F.EtaleSpace := ⟨x₀, g₀⟩
  obtain ⟨s, ⟨hs₀, hs⟩, _hsunique⟩ :=
    hcover.existsUnique_continuousMap_lifts (ContinuousMap.id X) x₀ e₀ rfl
  have hbase (x : X) : (s x).base = x := congrFun hs x
  let value : F.EtaleSpace → T := fun e => TopCat.stalkToFiber P e.base e.germ
  let φ : X → T := fun x => value (s x)
  let f : (x : (⊤ : Opens X)) → T := fun x => φ x
  refine ⟨f, ?_, ?_⟩
  · apply P.locality
    intro x
    have hsx : Tendsto s (𝓝 (x : X)) (𝓝 (s (x : X))) :=
      s.continuous.continuousAt
    obtain ⟨U, _hxU, t, ht⟩ :=
      TopCat.Presheaf.EtaleSpace.exists_section_of_tendsto hsx
    have hformula : ∀ᶠ y in 𝓝 (x : X),
        ∃ hy : y ∈ U, φ y = t.1 ⟨y, hy⟩ := by
      filter_upwards [ht] with y hy
      obtain ⟨hy, hgerm⟩ := hy
      have hyU : y ∈ U := by rwa [hbase y] at hy
      refine ⟨hyU, ?_⟩
      change TopCat.stalkToFiber P (s y).base (s y).germ = _
      rw [hgerm, TopCat.stalkToFiber_germ]
      exact congrArg t.1 (Subtype.ext (hbase y))
    obtain ⟨V, hVsub, hVopen, hxV⟩ := mem_nhds_iff.mp hformula
    let V' : Opens X := ⟨V, hVopen⟩
    have hVU : V' ≤ U := fun y hy => (hVsub hy).choose
    refine ⟨V', hxV, homOfLE le_top, ?_⟩
    change P.pred (fun y : V' => φ (y : X))
    have heq : (fun y : V' => φ (y : X)) =
        (fun y : V' => t.1 (homOfLE hVU y)) := by
      funext y
      obtain ⟨hyU, hy⟩ := hVsub y.property
      exact hy
    rw [heq]
    exact P.res (homOfLE hVU) t.1 t.property
  · change value (s x₀) = value e₀
    exact congrArg value hs₀


private def potentialModelPrelocal
    {X : TopCat.{0}} {ι : Type} (U : ι → Opens X) (F : ι → X → ℂ) :
    TopCat.PrelocalPredicate (fun _ : X => ℂ) where
  pred {V} f := ∃ i, V ≤ U i ∧ ∃ c : ℂ, ∀ x : V, f x = F i x + c
  res {V W} h f hf := by
    obtain ⟨i, hWi, c, hfc⟩ := hf
    exact ⟨i, h.le.trans hWi, c, fun x => hfc (h x)⟩

private def potentialModelLocal
    {X : TopCat.{0}} {ι : Type} (U : ι → Opens X) (F : ι → X → ℂ) :
    TopCat.LocalPredicate (fun _ : X => ℂ) :=
  (potentialModelPrelocal U F).sheafify

private theorem potentialModel_add_pred
    {X : TopCat.{0}} {ι : Type} (U : ι → Opens X) (F : ι → X → ℂ)
    (i : ι) (c : ℂ) :
    (potentialModelLocal U F).pred (fun x : U i => F i x + c) := by
  apply TopCat.PrelocalPredicate.sheafifyOf
  exact ⟨i, le_rfl, c, fun _ => rfl⟩

private theorem potentialModel_local_expression
    {X : TopCat.{0}} {ι : Type} (U : ι → Opens X) (F : ι → X → ℂ)
    {V : Opens X} {f : V → ℂ} (hf : (potentialModelLocal U F).pred f)
    (x : X) (hx : x ∈ V) :
    ∃ i, x ∈ U i ∧ ∃ c : ℂ, ∀ᶠ y in 𝓝 x,
      ∃ hy : y ∈ V, f ⟨y, hy⟩ = F i y + c := by
  obtain ⟨W, hxW, hWV, i, hWi, c, hfc⟩ := hf ⟨x, hx⟩
  refine ⟨i, hWi hxW, c, ?_⟩
  filter_upwards [W.isOpen.mem_nhds hxW] with y hy
  exact ⟨hWV.le hy, hfc ⟨y, hy⟩⟩

private theorem potentialModel_difference_locallyConstant
    {X : TopCat.{0}} {ι : Type} (U : ι → Opens X) (F : ι → X → ℂ)
    (htransition : ∀ i j (x : X), x ∈ U i → x ∈ U j →
      ∀ᶠ y in 𝓝 x, F i y - F j y = F i x - F j x)
    {V : Opens X} {f : V → ℂ} (hf : (potentialModelLocal U F).pred f)
    (i : ι) (hVi : V ≤ U i) :
    IsLocallyConstant (fun x : V => f x - F i x) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro x
  obtain ⟨j, hxj, c, hnear⟩ := potentialModel_local_expression U F hf x x.property
  have hfx : f x = F j x + c := hnear.self_of_nhds.choose_spec
  have hnearV := (continuous_subtype_val.tendsto x).eventually hnear
  have htransV := (continuous_subtype_val.tendsto x).eventually
    (htransition j i x hxj (hVi x.property))
  filter_upwards [hnearV, htransV] with y hy htrans
  obtain ⟨hyV, hfy⟩ := hy
  rw [hfy, hfx]
  linear_combination htrans

private theorem potentialModel_section_evaluation_bijective
    {X : TopCat.{0}} {ι : Type} (U : ι → Opens X) (F : ι → X → ℂ)
    (hconnected : ∀ i, IsPreconnected (U i : Set X))
    (htransition : ∀ i j (x : X), x ∈ U i → x ∈ U j →
      ∀ᶠ y in 𝓝 x, F i y - F j y = F i x - F j x)
    (i : ι) (x : X) (hx : x ∈ U i) :
    Function.Bijective
      (fun s : (TopCat.subsheafToTypes (potentialModelLocal U F)).presheaf.obj (op (U i)) =>
        s.1 ⟨x, hx⟩) := by
  let : PreconnectedSpace (U i) := Subtype.preconnectedSpace (hconnected i)
  constructor
  · intro s t hst
    apply Subtype.ext
    funext y
    have hs := potentialModel_difference_locallyConstant U F htransition s.property i le_rfl
    have ht := potentialModel_difference_locallyConstant U F htransition t.property i le_rfl
    have hsy := hs.apply_eq_of_preconnectedSpace y ⟨x, hx⟩
    have hty := ht.apply_eq_of_preconnectedSpace y ⟨x, hx⟩
    linear_combination hsy - hty + hst
  · intro z
    refine ⟨⟨fun y => F i y + (z - F i x),
      potentialModel_add_pred U F i (z - F i x)⟩, ?_⟩
    change F i x + (z - F i x) = z
    abel

private theorem potentialModel_stalk_evaluation_surjective
    {X : TopCat.{0}} {ι : Type} (U : ι → Opens X) (F : ι → X → ℂ)
    (hcover : ∀ x : X, ∃ i, x ∈ U i) (x : X) :
    Function.Surjective (TopCat.stalkToFiber (potentialModelLocal U F) x) := by
  apply TopCat.stalkToFiber_surjective
  intro z
  obtain ⟨i, hxi⟩ := hcover x
  refine ⟨⟨U i, hxi⟩, fun y => F i y + (z - F i x),
    potentialModel_add_pred U F i (z - F i x), ?_⟩
  change F i x + (z - F i x) = z
  abel

private theorem potentialModel_stalk_evaluation_injective
    {X : TopCat.{0}} {ι : Type} (U : ι → Opens X) (F : ι → X → ℂ)
    (htransition : ∀ i j (x : X), x ∈ U i → x ∈ U j →
      ∀ᶠ y in 𝓝 x, F i y - F j y = F i x - F j x)
    (x : X) :
    Function.Injective (TopCat.stalkToFiber (potentialModelLocal U F) x) := by
  apply TopCat.stalkToFiber_injective
  intro V W f hf g hg hfg
  obtain ⟨i, hxi, c, hnearF⟩ := potentialModel_local_expression U F hf x V.property
  obtain ⟨j, hxj, d, hnearG⟩ := potentialModel_local_expression U F hg x W.property
  have hfx : f ⟨x, V.property⟩ = F i x + c := hnearF.self_of_nhds.choose_spec
  have hgx : g ⟨x, W.property⟩ = F j x + d := hnearG.self_of_nhds.choose_spec
  have hzero : F i x + c = F j x + d := hfx.symm.trans (hfg.trans hgx)
  have hnear : ∀ᶠ y in 𝓝 x, ∃ hyV : y ∈ V.1, ∃ hyW : y ∈ W.1,
      f ⟨y, hyV⟩ = g ⟨y, hyW⟩ := by
    filter_upwards [hnearF, hnearG, htransition i j x hxi hxj] with y hyF hyG htrans
    obtain ⟨hyV, hfy⟩ := hyF
    obtain ⟨hyW, hgy⟩ := hyG
    refine ⟨hyV, hyW, ?_⟩
    rw [hfy, hgy]
    linear_combination htrans + hzero
  obtain ⟨B, hBsub, hBopen, hxB⟩ := mem_nhds_iff.mp hnear
  let B' : Opens X := ⟨B, hBopen⟩
  have hBV : B' ≤ V.1 := fun y hy => (hBsub hy).choose
  have hBW : B' ≤ W.1 := fun y hy => (hBsub hy).choose_spec.choose
  refine ⟨⟨B', hxB⟩, homOfLE hBV, homOfLE hBW, ?_⟩
  intro y
  obtain ⟨_hyV, _hyW, hy⟩ := hBsub y.property
  exact hy

/-- Actual local functions whose overlap differences are locally constant glue
to one global function on any simply connected locally path connected base.
The result retains the original local functions and neighborhoods. -/
theorem exists_global_potential_of_local_constant_transitions
    {X : TopCat.{0}} {ι : Type}
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (U : ι → Opens X) (F : ι → X → ℂ)
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hconnected : ∀ i, IsPreconnected (U i : Set X))
    (htransition : ∀ i j (x : X), x ∈ U i → x ∈ U j →
      ∀ᶠ y in 𝓝 x, F i y - F j y = F i x - F j x) :
    ∃ φ : X → ℂ, ∀ x : X, ∃ i c, x ∈ U i ∧
      ∀ᶠ y in 𝓝 x, φ y = F i y + c := by
  let P := potentialModelLocal U F
  let S := (TopCat.subsheafToTypes P).presheaf
  have hstalk (x : X) : Function.Bijective (TopCat.stalkToFiber P x) :=
    ⟨potentialModel_stalk_evaluation_injective U F htransition x,
      potentialModel_stalk_evaluation_surjective U F hcover x⟩
  have hlocal : ∀ x : X, ∃ V : Opens X, x ∈ V ∧ ∀ y : X, ∀ hy : y ∈ V,
      Function.Bijective (S.germ V y hy) := by
    intro x
    obtain ⟨i, hxi⟩ := hcover x
    refine ⟨U i, hxi, ?_⟩
    intro y hy
    exact germ_bijective_of_point_evaluations P (U i) y hy (hstalk y)
      (potentialModel_section_evaluation_bijective U F hconnected htransition i y hy)
  let x₀ : X := Classical.choice (inferInstance : Nonempty X)
  obtain ⟨i₀, hxi₀⟩ := hcover x₀
  let s₀ : S.obj (op (U i₀)) :=
    ⟨fun y => F i₀ y + 0, potentialModel_add_pred U F i₀ 0⟩
  let g₀ : S.stalk x₀ := S.germ (U i₀) x₀ hxi₀ s₀
  obtain ⟨f, hf, _hfvalue⟩ := exists_global_localPredicate_section P x₀ g₀ hlocal
  let φ : X → ℂ := fun x => f ⟨x, mem_univ x⟩
  refine ⟨φ, ?_⟩
  intro x
  obtain ⟨i, hxi, c, hnear⟩ := potentialModel_local_expression U F hf x (mem_univ x)
  refine ⟨i, c, hxi, ?_⟩
  filter_upwards [hnear] with y hy
  obtain ⟨_hy, he⟩ := hy
  exact he

end LowDimensionalTopology.Geometry
