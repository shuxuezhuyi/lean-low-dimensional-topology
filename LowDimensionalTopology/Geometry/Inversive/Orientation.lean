/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LowDimensionalTopology.Geometry.Inversive.ReflectionDerivatives
public import LowDimensionalTopology.Geometry.Inversive.ReflectionConjugacy
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Data.List.Infix
public import LowDimensionalTopology.Geometry.Auxiliary.Analysis.Conformal
/-!
# Orientation criteria in finite Euclidean charts

The predicates use conformal derivatives and the actual sign of
their real determinant at every finite point whose image is finite. They do not
assign an orientation from a chosen reflection word. Isometric changes of real
coordinates preserve the positive determinant condition.

Genuine sphere and plane reflections are proved conformal with negative real
Jacobian on every regular finite chart. Chain rules explicitly retain the
finite-intermediate-value hypothesis.

For positive dimension, the full finite-chart orientation criterion is proved
equivalent to reflection-word parity, even when intermediate points are infinite.
The orientation-preserving subgroup is defined by its actual Jacobian condition;
its equivalent even-word characterization is a theorem. The complex case is
identified with fractional-linear transformations in `LowDimensionalTopology.Geometry.Mobius.ReflectionEquivalence`.
-/

@[expose] public section
noncomputable section
open scoped Topology OnePoint
open Filter EuclideanGeometry
namespace LowDimensionalTopology.Geometry.Inversive
open LowDimensionalTopology.Geometry.Auxiliary.Analysis
variable {n : ℕ}
def finiteEuclideanPart (f : ExtendedHomeomorph n) (x : Euclidean n) : Euclidean n :=
  (f (x : ExtendedEuclidean n)).elim 0 id

def PreservesOrientation (f : ExtendedHomeomorph n) : Prop :=
  ∀ x : Euclidean n, f (x : ExtendedEuclidean n) ≠ ∞ →
    Auxiliary.Analysis.directlyConformalAt (finiteEuclideanPart f) x

def ReversesOrientation (f : ExtendedHomeomorph n) : Prop :=
  ∀ x : Euclidean n, f (x : ExtendedEuclidean n) ≠ ∞ →
    Auxiliary.Analysis.indirectlyConformalAt (finiteEuclideanPart f) x

theorem directlyConformalAt_isometricConjugate
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {f : E → E} {x : E} (h : Auxiliary.Analysis.directlyConformalAt f x) :
    Auxiliary.Analysis.directlyConformalAt (fun y : F ↦ e (f (e.symm y))) (e x) := by
  rcases h.1 with ⟨A, hA, hconf⟩
  let B : F →L[ℝ] F := (e : E →L[ℝ] F).comp (A.comp (e.symm : F →L[ℝ] E))
  have hA' : HasFDerivAt f A (e.symm (e x)) := by simpa using hA
  have hB : HasFDerivAt (fun y : F ↦ e (f (e.symm y))) B (e x) :=
    (e : E →L[ℝ] F).hasFDerivAt.comp _
      (hA'.comp _ (e.symm : F →L[ℝ] E).hasFDerivAt)
  refine ⟨⟨B, hB, e.toLinearIsometry.isConformalMap.comp
    (hconf.comp e.symm.toLinearIsometry.isConformalMap)⟩, ?_⟩
  rw [hB.fderiv]
  have hdet : LinearMap.det B.toLinearMap = LinearMap.det A.toLinearMap := by
    convert LinearMap.det_conj A.toLinearMap e.toLinearEquiv using 1
    congr 1
  change 0 < LinearMap.det B.toLinearMap
  rw [hdet]
  simpa only [hA.fderiv] using h.2

theorem directlyConformalAt_isometricConjugate_iff
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {f : E → E} {x : E} :
    Auxiliary.Analysis.directlyConformalAt (fun y : F ↦ e (f (e.symm y))) (e x) ↔
      Auxiliary.Analysis.directlyConformalAt f x := by
  constructor
  · intro h
    have h' := directlyConformalAt_isometricConjugate e.symm h
    simpa only [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply] using h'
  · exact directlyConformalAt_isometricConjugate e

/-! ## Reflections and the negative Jacobian criterion -/


theorem finiteEuclideanPart_planeReflection (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    finiteEuclideanPart (planeReflectionHomeomorph a t ha) = planeReflectionFinite a t := by
  funext x
  rfl

theorem finiteEuclideanPart_sphereInversion_eventuallyEq (c : Euclidean n) (r : ℝ)
    (hr : r ≠ 0) {x : Euclidean n} (hx : x ≠ c) :
    finiteEuclideanPart (sphereInversionHomeomorph c r hr) =ᶠ[𝓝 x] inversion c r := by
  have hne : ∀ᶠ y : Euclidean n in 𝓝 x, y ≠ c := eventually_ne_nhds hx
  filter_upwards [hne] with y hy
  simp only [finiteEuclideanPart, sphereInversionHomeomorph_apply, sphereInversion_coe c r hy]
  rfl

theorem planeReflection_reversesOrientation (a : Euclidean n) (t : ℝ) (ha : a ≠ 0) :
    ReversesOrientation (planeReflectionHomeomorph a t ha) := by
  intro x _
  rw [finiteEuclideanPart_planeReflection]
  refine ⟨planeReflectionFinite_conformalAt a t x, ?_⟩
  rw [planeReflectionFinite_fderiv_det a t ha]
  norm_num

theorem sphereInversion_reversesOrientation (c : Euclidean n) (r : ℝ) (hr : r ≠ 0) :
    ReversesOrientation (sphereInversionHomeomorph c r hr) := by
  intro x hx
  have hxc : x ≠ c := by
    intro h
    subst x
    exact hx (by simp [sphereInversionHomeomorph_apply])
  have he := finiteEuclideanPart_sphereInversion_eventuallyEq c r hr hxc
  refine ⟨?_, ?_⟩
  · rcases sphereInversion_conformalAt hr hxc with ⟨A, hA, hc⟩
    exact ⟨A, hA.congr_of_eventuallyEq he, hc⟩
  · rw [he.fderiv_eq]
    exact sphereInversion_fderiv_det_neg hr hxc

theorem IsReflection.reversesOrientation {f : ExtendedHomeomorph n} (hf : IsReflection f) :
    ReversesOrientation f := by
  rcases hf with ⟨c, r, hr, rfl⟩ | ⟨a, t, ha, rfl⟩
  · exact sphereInversion_reversesOrientation c r hr.ne'
  · exact planeReflection_reversesOrientation a t ha

theorem exists_regular_euclidean_point [NeZero n] (f : ExtendedHomeomorph n) :
    ∃ x : Euclidean n, f (x : ExtendedEuclidean n) ≠ ∞ := by
  obtain ⟨v, hv⟩ := exists_ne (0 : Euclidean n)
  by_cases h0 : f ((0 : Euclidean n) : ExtendedEuclidean n) = ∞
  · refine ⟨v, ?_⟩
    intro h1
    have he := f.injective (h1.trans h0.symm)
    exact hv (OnePoint.coe_injective he)
  · exact ⟨0, h0⟩

theorem not_preservesOrientation_of_reversesOrientation [NeZero n]
    {f : ExtendedHomeomorph n} (hf : ReversesOrientation f) : ¬ PreservesOrientation f := by
  intro hp
  obtain ⟨x, hx⟩ := exists_regular_euclidean_point f
  exact (not_lt_of_gt (hp x hx).2) (hf x hx).2

theorem IsReflection.not_preservesOrientation [NeZero n] {f : ExtendedHomeomorph n}
    (hf : IsReflection f) : ¬ PreservesOrientation f :=
  not_preservesOrientation_of_reversesOrientation hf.reversesOrientation
theorem indirectlyConformalAt_isometricConjugate
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {f : E → E} {x : E} (h : Auxiliary.Analysis.indirectlyConformalAt f x) :
    Auxiliary.Analysis.indirectlyConformalAt (fun y : F ↦ e (f (e.symm y))) (e x) := by
  rcases h.1 with ⟨A, hA, hconf⟩
  let B : F →L[ℝ] F := (e : E →L[ℝ] F).comp (A.comp (e.symm : F →L[ℝ] E))
  have hA' : HasFDerivAt f A (e.symm (e x)) := by simpa using hA
  have hB : HasFDerivAt (fun y : F ↦ e (f (e.symm y))) B (e x) :=
    (e : E →L[ℝ] F).hasFDerivAt.comp _
      (hA'.comp _ (e.symm : F →L[ℝ] E).hasFDerivAt)
  refine ⟨⟨B, hB, e.toLinearIsometry.isConformalMap.comp
    (hconf.comp e.symm.toLinearIsometry.isConformalMap)⟩, ?_⟩
  rw [hB.fderiv]
  have hdet : LinearMap.det B.toLinearMap = LinearMap.det A.toLinearMap := by
    convert LinearMap.det_conj A.toLinearMap e.toLinearEquiv using 1
    congr 1
  change LinearMap.det B.toLinearMap < 0
  rw [hdet]
  simpa only [hA.fderiv] using h.2

theorem indirectlyConformalAt_isometricConjugate_iff
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {f : E → E} {x : E} :
    Auxiliary.Analysis.indirectlyConformalAt (fun y : F ↦ e (f (e.symm y))) (e x) ↔
      Auxiliary.Analysis.indirectlyConformalAt f x := by
  constructor
  · intro h
    have h' := indirectlyConformalAt_isometricConjugate e.symm h
    simpa only [LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.apply_symm_apply] using h'
  · exact indirectlyConformalAt_isometricConjugate e



/-! ## Chain rules when the intermediate value is finite -/


theorem finiteEuclideanPart_mul_eventuallyEq (f g : ExtendedHomeomorph n)
    {x : Euclidean n} (hg : g (x : ExtendedEuclidean n) ≠ ∞) :
    finiteEuclideanPart (f * g) =ᶠ[𝓝 x] finiteEuclideanPart f ∘ finiteEuclideanPart g := by
  have hne : ∀ᶠ y : Euclidean n in 𝓝 x, g (y : ExtendedEuclidean n) ≠ ∞ :=
    (g.continuous.comp OnePoint.continuous_coe).continuousAt.eventually_ne hg
  filter_upwards [hne] with y hy
  simp only [finiteEuclideanPart, Homeomorph.mul_apply, Function.comp_apply]
  generalize g (y : ExtendedEuclidean n) = w at hy ⊢
  induction w using OnePoint.rec with
  | infty => exact False.elim (hy rfl)
  | coe w => rfl

theorem finiteEuclideanPart_mul_conformalAt (f g : ExtendedHomeomorph n)
    {x : Euclidean n} (hreg : g (x : ExtendedEuclidean n) ≠ ∞)
    (hf : ConformalAt (finiteEuclideanPart f) (finiteEuclideanPart g x))
    (hg : ConformalAt (finiteEuclideanPart g) x) :
    ConformalAt (finiteEuclideanPart (f * g)) x := by
  rcases hf.comp x hg with ⟨A, hA, hc⟩
  exact ⟨A, hA.congr_of_eventuallyEq (finiteEuclideanPart_mul_eventuallyEq f g hreg), hc⟩

theorem finiteEuclideanPart_mul_fderiv_det (f g : ExtendedHomeomorph n)
    {x : Euclidean n} (hreg : g (x : ExtendedEuclidean n) ≠ ∞)
    (hf : DifferentiableAt ℝ (finiteEuclideanPart f) (finiteEuclideanPart g x))
    (hg : DifferentiableAt ℝ (finiteEuclideanPart g) x) :
    LinearMap.det (fderiv ℝ (finiteEuclideanPart (f * g)) x).toLinearMap =
      LinearMap.det (fderiv ℝ (finiteEuclideanPart f) (finiteEuclideanPart g x)).toLinearMap *
        LinearMap.det (fderiv ℝ (finiteEuclideanPart g) x).toLinearMap := by
  rw [(finiteEuclideanPart_mul_eventuallyEq f g hreg).fderiv_eq,
    fderiv_comp x hf hg]
  exact LinearMap.det_comp _ _

theorem finiteEuclideanPart_mul_direct_direct (f g : ExtendedHomeomorph n)
    {x : Euclidean n} (hreg : g (x : ExtendedEuclidean n) ≠ ∞)
    (hf : Auxiliary.Analysis.directlyConformalAt (finiteEuclideanPart f) (finiteEuclideanPart g x))
    (hg : Auxiliary.Analysis.directlyConformalAt (finiteEuclideanPart g) x) :
    Auxiliary.Analysis.directlyConformalAt (finiteEuclideanPart (f * g)) x := by
  refine ⟨finiteEuclideanPart_mul_conformalAt f g hreg hf.1 hg.1, ?_⟩
  rw [finiteEuclideanPart_mul_fderiv_det f g hreg hf.1.differentiableAt hg.1.differentiableAt]
  exact mul_pos hf.2 hg.2

theorem finiteEuclideanPart_mul_indirect_indirect (f g : ExtendedHomeomorph n)
    {x : Euclidean n} (hreg : g (x : ExtendedEuclidean n) ≠ ∞)
    (hf : Auxiliary.Analysis.indirectlyConformalAt (finiteEuclideanPart f) (finiteEuclideanPart g x))
    (hg : Auxiliary.Analysis.indirectlyConformalAt (finiteEuclideanPart g) x) :
    Auxiliary.Analysis.directlyConformalAt (finiteEuclideanPart (f * g)) x := by
  refine ⟨finiteEuclideanPart_mul_conformalAt f g hreg hf.1 hg.1, ?_⟩
  rw [finiteEuclideanPart_mul_fderiv_det f g hreg hf.1.differentiableAt hg.1.differentiableAt]
  exact mul_pos_of_neg_of_neg hf.2 hg.2

theorem finiteEuclideanPart_mul_direct_indirect (f g : ExtendedHomeomorph n)
    {x : Euclidean n} (hreg : g (x : ExtendedEuclidean n) ≠ ∞)
    (hf : Auxiliary.Analysis.directlyConformalAt (finiteEuclideanPart f) (finiteEuclideanPart g x))
    (hg : Auxiliary.Analysis.indirectlyConformalAt (finiteEuclideanPart g) x) :
    Auxiliary.Analysis.indirectlyConformalAt (finiteEuclideanPart (f * g)) x := by
  refine ⟨finiteEuclideanPart_mul_conformalAt f g hreg hf.1 hg.1, ?_⟩
  rw [finiteEuclideanPart_mul_fderiv_det f g hreg hf.1.differentiableAt hg.1.differentiableAt]
  exact mul_neg_of_pos_of_neg hf.2 hg.2

theorem finiteEuclideanPart_mul_indirect_direct (f g : ExtendedHomeomorph n)
    {x : Euclidean n} (hreg : g (x : ExtendedEuclidean n) ≠ ∞)
    (hf : Auxiliary.Analysis.indirectlyConformalAt (finiteEuclideanPart f) (finiteEuclideanPart g x))
    (hg : Auxiliary.Analysis.directlyConformalAt (finiteEuclideanPart g) x) :
    Auxiliary.Analysis.indirectlyConformalAt (finiteEuclideanPart (f * g)) x := by
  refine ⟨finiteEuclideanPart_mul_conformalAt f g hreg hf.1 hg.1, ?_⟩
  rw [finiteEuclideanPart_mul_fderiv_det f g hreg hf.1.differentiableAt hg.1.differentiableAt]
  exact mul_neg_of_neg_of_pos hf.2 hg.2



/-! ## General reflection words, including intermediate infinity -/


def FiniteWordRegular (l : List (ExtendedHomeomorph n)) (x : Euclidean n) : Prop :=
  ∀ k ∈ l.tails, k.prod (x : ExtendedEuclidean n) ≠ ∞

theorem coe_finiteEuclideanPart (g : ExtendedHomeomorph n) {x : Euclidean n}
    (hx : g (x : ExtendedEuclidean n) ≠ ∞) :
    (finiteEuclideanPart g x : ExtendedEuclidean n) = g (x : ExtendedEuclidean n) := by
  unfold finiteEuclideanPart
  generalize g (x : ExtendedEuclidean n) = w at hx ⊢
  induction w using OnePoint.rec with
  | infty => exact False.elim (hx rfl)
  | coe w => rfl

theorem finiteWordRegular_cons (f : ExtendedHomeomorph n)
    (l : List (ExtendedHomeomorph n)) (x : Euclidean n) :
    FiniteWordRegular (f :: l) x ↔
      (f * l.prod) (x : ExtendedEuclidean n) ≠ ∞ ∧ FiniteWordRegular l x := by
  simp [FiniteWordRegular, List.tails]

theorem finiteWordRegular_prod {l : List (ExtendedHomeomorph n)} {x : Euclidean n}
    (h : FiniteWordRegular l x) : l.prod (x : ExtendedEuclidean n) ≠ ∞ := by
  exact h l ((List.mem_tails _ _).mpr (List.suffix_refl l))

theorem homeomorph_regular_cofinite (f : ExtendedHomeomorph n) :
    ∀ᶠ x : Euclidean n in Filter.cofinite, f (x : ExtendedEuclidean n) ≠ ∞ := by
  have hi : Function.Injective (fun x : Euclidean n ↦ f (x : ExtendedEuclidean n)) :=
    f.injective.comp OnePoint.coe_injective
  have hs : Set.Subsingleton {x : Euclidean n | f (x : ExtendedEuclidean n) = ∞} :=
    fun x hx y hy ↦ hi (hx.trans hy.symm)
  exact hs.finite.compl_mem_cofinite

theorem finiteWordRegular_cofinite (l : List (ExtendedHomeomorph n)) :
    ∀ᶠ x : Euclidean n in Filter.cofinite, FiniteWordRegular l x := by
  induction l with
  | nil => exact Filter.Eventually.of_forall (by intro x; simp [FiniteWordRegular, List.tails])
  | cons f l ih =>
    filter_upwards [ih, homeomorph_regular_cofinite (f * l.prod)] with x hx hprod
    exact (finiteWordRegular_cons f l x).mpr ⟨hprod, hx⟩

theorem reflectionWord_finite_orientation (l : List (ExtendedHomeomorph n))
    (hl : ∀ f ∈ l, IsReflection f) {x : Euclidean n} (hx : FiniteWordRegular l x) :
    (Even l.length → Auxiliary.Analysis.directlyConformalAt (finiteEuclideanPart l.prod) x) ∧
    (Odd l.length → Auxiliary.Analysis.indirectlyConformalAt (finiteEuclideanPart l.prod) x) := by
  induction l with
  | nil =>
    constructor
    · intro _
      refine ⟨conformalAt_id x, ?_⟩
      change 0 < LinearMap.det (fderiv ℝ (_root_.id : Euclidean n → Euclidean n) x).toLinearMap
      rw [fderiv_id]
      simp
    · simp
  | cons f l ih =>
    obtain ⟨hprod, htail⟩ := (finiteWordRegular_cons f l x).mp hx
    have hreg := finiteWordRegular_prod htail
    have hfreg : f (finiteEuclideanPart l.prod x : ExtendedEuclidean n) ≠ ∞ := by
      rw [coe_finiteEuclideanPart l.prod hreg]
      exact hprod
    have hf := (hl f (by simp)).reversesOrientation (finiteEuclideanPart l.prod x) hfreg
    have hi := ih (fun g hg ↦ hl g (by simp [hg])) htail
    simp only [List.length_cons, List.prod_cons]
    constructor
    · intro he
      apply finiteEuclideanPart_mul_indirect_indirect f l.prod hreg hf
      exact hi.2 (by simpa only [Nat.even_add_one, Nat.not_even_iff_odd] using he)
    · intro ho
      apply finiteEuclideanPart_mul_indirect_direct f l.prod hreg hf
      exact hi.1 (by simpa only [Nat.odd_add_one, Nat.not_odd_iff_even] using ho)

theorem reflectionWord_even_iff_of_prod_eq_generic [NeZero n]
    (l k : List (ExtendedHomeomorph n))
    (hl : ∀ f ∈ l, IsReflection f) (hk : ∀ f ∈ k, IsReflection f) (h : l.prod = k.prod) :
    Even l.length ↔ Even k.length := by
  obtain ⟨x, hxl, hxk⟩ := ((finiteWordRegular_cofinite l).and (finiteWordRegular_cofinite k)).exists
  have hil := reflectionWord_finite_orientation l hl hxl
  have hik := reflectionWord_finite_orientation k hk hxk
  constructor
  · intro he
    by_contra ho
    have hp := (hil.1 he).2
    have hn := (hik.2 (Nat.not_even_iff_odd.mp ho)).2
    rw [h] at hp
    exact (not_lt_of_gt hp) hn
  · intro he
    by_contra ho
    have hp := (hik.1 he).2
    have hn := (hil.2 (Nat.not_even_iff_odd.mp ho)).2
    rw [h] at hn
    exact (not_lt_of_gt hp) hn


def OrbitAvoids (l : List (ExtendedHomeomorph n)) (x c : Euclidean n) : Prop :=
  ∀ k ∈ l.tails, k.prod (x : ExtendedEuclidean n) ≠ (c : ExtendedEuclidean n)

theorem point_ne_coe_cofinite (p : ExtendedEuclidean n) :
    ∀ᶠ c : Euclidean n in Filter.cofinite, p ≠ (c : ExtendedEuclidean n) := by
  have hs : Set.Subsingleton {c : Euclidean n | p = (c : ExtendedEuclidean n)} :=
    fun x hx y hy ↦ OnePoint.coe_injective (hx.symm.trans hy)
  exact hs.finite.compl_mem_cofinite

theorem orbitAvoids_cofinite (l : List (ExtendedHomeomorph n)) (x : Euclidean n) :
    ∀ᶠ c : Euclidean n in Filter.cofinite, OrbitAvoids l x c := by
  induction l with
  | nil =>
    filter_upwards [point_ne_coe_cofinite (x : ExtendedEuclidean n)] with c hc
    simpa [OrbitAvoids, List.tails] using hc
  | cons f l ih =>
    filter_upwards [ih, point_ne_coe_cofinite ((f * l.prod) (x : ExtendedEuclidean n))] with c hc hprod
    simpa [OrbitAvoids, List.tails] using And.intro hprod hc

theorem sphereInversionHomeomorph_ne_infty_iff (c : Euclidean n) (r : ℝ) (hr : r ≠ 0)
    (p : ExtendedEuclidean n) :
    sphereInversionHomeomorph c r hr p ≠ ∞ ↔ p ≠ (c : ExtendedEuclidean n) := by
  have hc : sphereInversionHomeomorph c r hr (c : ExtendedEuclidean n) = ∞ := by
    simp [sphereInversionHomeomorph_apply]
  constructor
  · intro h hp
    exact h (hp ▸ hc)
  · intro h hp
    exact h ((sphereInversionHomeomorph c r hr).injective (hp.trans hc.symm))

theorem conjugateWord_prod (T : ExtendedHomeomorph n) (l : List (ExtendedHomeomorph n)) :
    (l.map (MulAut.conj T)).prod = T * l.prod * T⁻¹ := by
  rw [← map_list_prod]
  rfl

theorem conjugateWord_regular (l : List (ExtendedHomeomorph n)) (x c : Euclidean n)
    (havoid : OrbitAvoids l x c) :
    FiniteWordRegular (l.map (MulAut.conj (sphereInversionHomeomorph c 1 one_ne_zero)))
      (finiteEuclideanPart (sphereInversionHomeomorph c 1 one_ne_zero) x) := by
  let T := sphereInversionHomeomorph c 1 one_ne_zero
  have hx : (x : ExtendedEuclidean n) ≠ (c : ExtendedEuclidean n) := by
    exact havoid [] (by simp [List.mem_tails])
  have hTx : T (x : ExtendedEuclidean n) ≠ ∞ :=
    (sphereInversionHomeomorph_ne_infty_iff c 1 one_ne_zero _).mpr hx
  intro k hk
  rw [List.map_tails] at hk
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hk
  rw [conjugateWord_prod]
  change T (j.prod (T⁻¹ (finiteEuclideanPart T x : ExtendedEuclidean n))) ≠ ∞
  rw [coe_finiteEuclideanPart T hTx]
  change T (j.prod (T.symm (T (x : ExtendedEuclidean n)))) ≠ ∞
  rw [Homeomorph.symm_apply_apply]
  exact (sphereInversionHomeomorph_ne_infty_iff c 1 one_ne_zero _).mpr (havoid j hj)

/-- A geometric reflection-conjugacy theorem removes all intermediate-pole
restrictions from the finite-chart chain-rule argument. -/
theorem reflectionWord_orientation_of_conjugacy [NeZero n]
    (hconj : ∀ (c : Euclidean n) (f : ExtendedHomeomorph n), IsReflection f →
      IsReflection (sphereInversionHomeomorph c 1 one_ne_zero * f *
        (sphereInversionHomeomorph c 1 one_ne_zero)⁻¹))
    (l : List (ExtendedHomeomorph n)) (hl : ∀ f ∈ l, IsReflection f)
    {x : Euclidean n} (hfx : l.prod (x : ExtendedEuclidean n) ≠ ∞) :
    (Even l.length → Auxiliary.Analysis.directlyConformalAt (finiteEuclideanPart l.prod) x) ∧
    (Odd l.length → Auxiliary.Analysis.indirectlyConformalAt (finiteEuclideanPart l.prod) x) := by
  obtain ⟨c, hc⟩ := (orbitAvoids_cofinite l x).exists
  let T := sphereInversionHomeomorph c 1 one_ne_zero
  let L := l.map (MulAut.conj T)
  let H := L.prod
  have hT : IsReflection T := sphereInversion_isReflection c 1 zero_lt_one
  have hTx : T (x : ExtendedEuclidean n) ≠ ∞ := by
    apply (sphereInversionHomeomorph_ne_infty_iff c 1 one_ne_zero _).mpr
    exact hc [] (by simp [List.mem_tails])
  have hL : ∀ f ∈ L, IsReflection f := by
    intro f hf
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hf
    exact hconj c g (hl g hg)
  have hreg := conjugateWord_regular l x c hc
  have hsign := reflectionWord_finite_orientation L hL hreg
  have hlen : L.length = l.length := List.length_map _
  rw [hlen] at hsign
  have hHreg : H (finiteEuclideanPart T x : ExtendedEuclidean n) ≠ ∞ :=
    finiteWordRegular_prod hreg
  have hKreg : (H * T) (x : ExtendedEuclidean n) ≠ ∞ := by
    change H (T (x : ExtendedEuclidean n)) ≠ ∞
    simpa only [coe_finiteEuclideanPart T hTx] using hHreg
  have hHeq : H = T * l.prod * T⁻¹ := conjugateWord_prod T l
  have hrestore : T⁻¹ * (H * T) = l.prod := by simp [hHeq, mul_assoc]
  have houterReg : T⁻¹ (finiteEuclideanPart (H * T) x : ExtendedEuclidean n) ≠ ∞ := by
    rw [coe_finiteEuclideanPart (H * T) hKreg]
    change (T⁻¹ * (H * T)) (x : ExtendedEuclidean n) ≠ ∞
    rw [hrestore]
    exact hfx
  have hinner := hT.reversesOrientation x hTx
  have houter := hT.inv.reversesOrientation (finiteEuclideanPart (H * T) x) houterReg
  constructor
  · intro he
    have hK := finiteEuclideanPart_mul_direct_indirect H T hTx (hsign.1 he) hinner
    have hfinal := finiteEuclideanPart_mul_indirect_indirect T⁻¹ (H * T) hKreg houter hK
    rwa [hrestore] at hfinal
  · intro ho
    have hK := finiteEuclideanPart_mul_indirect_indirect H T hTx (hsign.2 ho) hinner
    have hfinal := finiteEuclideanPart_mul_indirect_direct T⁻¹ (H * T) hKreg houter hK
    rwa [hrestore] at hfinal

theorem reflectionWord_orientation [NeZero n] (l : List (ExtendedHomeomorph n))
    (hl : ∀ f ∈ l, IsReflection f) {x : Euclidean n}
    (hx : l.prod (x : ExtendedEuclidean n) ≠ ∞) :
    (Even l.length → Auxiliary.Analysis.directlyConformalAt (finiteEuclideanPart l.prod) x) ∧
    (Odd l.length → Auxiliary.Analysis.indirectlyConformalAt (finiteEuclideanPart l.prod) x) :=
  reflectionWord_orientation_of_conjugacy (fun c _ hf ↦ sphereUnit_conjugate_isReflection c hf) l hl hx

theorem reflectionWord_preservesOrientation_iff_even [NeZero n]
    (l : List (ExtendedHomeomorph n)) (hl : ∀ f ∈ l, IsReflection f) :
    PreservesOrientation l.prod ↔ Even l.length := by
  constructor
  · intro hp
    by_contra he
    obtain ⟨x, hx⟩ := exists_regular_euclidean_point l.prod
    have hn := ((reflectionWord_orientation l hl hx).2 (Nat.not_even_iff_odd.mp he)).2
    exact (not_lt_of_gt (hp x hx).2) hn
  · intro he x hx
    exact (reflectionWord_orientation l hl hx).1 he

theorem reflectionWord_reversesOrientation_iff_odd [NeZero n]
    (l : List (ExtendedHomeomorph n)) (hl : ∀ f ∈ l, IsReflection f) :
    ReversesOrientation l.prod ↔ Odd l.length := by
  constructor
  · intro hp
    by_contra he
    obtain ⟨x, hx⟩ := exists_regular_euclidean_point l.prod
    have hn := ((reflectionWord_orientation l hl hx).1 (Nat.not_odd_iff_even.mp he)).2
    exact (not_lt_of_gt hn) (hp x hx).2
  · intro he x hx
    exact (reflectionWord_orientation l hl hx).2 he

theorem generalMobius_preservesOrientation_iff_even_word [NeZero n] {f : ExtendedHomeomorph n}
    (hf : f ∈ generalMobiusGroup n) :
    PreservesOrientation f ↔ ∃ l : List (ExtendedHomeomorph n),
      (∀ g ∈ l, IsReflection g) ∧ l.prod = f ∧ Even l.length := by
  constructor
  · intro hp
    obtain ⟨l, hl, hprod⟩ := (mem_generalMobiusGroup_iff f).mp hf
    exact ⟨l, hl, hprod, (reflectionWord_preservesOrientation_iff_even l hl).mp (hprod.symm ▸ hp)⟩
  · rintro ⟨l, hl, rfl, he⟩
    exact (reflectionWord_preservesOrientation_iff_even l hl).mpr he

theorem generalMobius_reversesOrientation_iff_odd_word [NeZero n] {f : ExtendedHomeomorph n}
    (hf : f ∈ generalMobiusGroup n) :
    ReversesOrientation f ↔ ∃ l : List (ExtendedHomeomorph n),
      (∀ g ∈ l, IsReflection g) ∧ l.prod = f ∧ Odd l.length := by
  constructor
  · intro hp
    obtain ⟨l, hl, hprod⟩ := (mem_generalMobiusGroup_iff f).mp hf
    exact ⟨l, hl, hprod, (reflectionWord_reversesOrientation_iff_odd l hl).mp (hprod.symm ▸ hp)⟩
  · rintro ⟨l, hl, rfl, he⟩
    exact (reflectionWord_reversesOrientation_iff_odd l hl).mpr he

theorem generalMobius_orientation_dichotomy [NeZero n] {f : ExtendedHomeomorph n}
    (hf : f ∈ generalMobiusGroup n) : PreservesOrientation f ∨ ReversesOrientation f := by
  obtain ⟨l, hl, rfl⟩ := (mem_generalMobiusGroup_iff f).mp hf
  rcases Nat.even_or_odd l.length with he | ho
  · exact Or.inl ((reflectionWord_preservesOrientation_iff_even l hl).mpr he)
  · exact Or.inr ((reflectionWord_reversesOrientation_iff_odd l hl).mpr ho)

theorem generalMobius_conformalAt [NeZero n] {f : ExtendedHomeomorph n}
    (hf : f ∈ generalMobiusGroup n) {x : Euclidean n} (hx : f (x : ExtendedEuclidean n) ≠ ∞) :
    ConformalAt (finiteEuclideanPart f) x := by
  rcases generalMobius_orientation_dichotomy hf with hp | hp
  · exact (hp x hx).1
  · exact (hp x hx).1

/-- With its actual positive real-Jacobian carrier. -/
def orientationPreservingMobiusGroup (n : ℕ) [NeZero n] : Subgroup (ExtendedHomeomorph n) where
  carrier := {f | f ∈ generalMobiusGroup n ∧ PreservesOrientation f}
  one_mem' := by
    refine ⟨one_mem _, ?_⟩
    exact (reflectionWord_preservesOrientation_iff_even ([] : List (ExtendedHomeomorph n))
      (by simp)).mpr (by simp)
  mul_mem' {f g} hf hg := by
    have hm := (generalMobiusGroup n).mul_mem hf.1 hg.1
    refine ⟨hm, (generalMobius_preservesOrientation_iff_even_word hm).mpr ?_⟩
    obtain ⟨l, hl, hlf, he⟩ := (generalMobius_preservesOrientation_iff_even_word hf.1).mp hf.2
    obtain ⟨k, hk, hkg, hek⟩ := (generalMobius_preservesOrientation_iff_even_word hg.1).mp hg.2
    refine ⟨l ++ k, ?_, ?_, ?_⟩
    · simpa only [List.mem_append, or_imp, forall_and] using And.intro hl hk
    · rw [List.prod_append, hlf, hkg]
    · simpa only [List.length_append] using he.add hek
  inv_mem' {f} hf := by
    have hm := (generalMobiusGroup n).inv_mem hf.1
    refine ⟨hm, (generalMobius_preservesOrientation_iff_even_word hm).mpr ?_⟩
    obtain ⟨l, hl, hlf, he⟩ := (generalMobius_preservesOrientation_iff_even_word hf.1).mp hf.2
    refine ⟨(l.map fun g ↦ g⁻¹).reverse, ?_, ?_, ?_⟩
    · intro g hg
      obtain ⟨h, hh, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hg)
      exact (hl h hh).inv
    · exact (List.prod_inv_reverse l).symm.trans (congrArg (fun g ↦ g⁻¹) hlf)
    · simpa only [List.length_reverse, List.length_map] using he

/-- The notation M for the orientation-preserving Möbius group. -/
abbrev M (n : ℕ) [NeZero n] := orientationPreservingMobiusGroup n

@[simp] theorem mem_orientationPreservingMobiusGroup [NeZero n] (f : ExtendedHomeomorph n) :
    f ∈ orientationPreservingMobiusGroup n ↔ f ∈ generalMobiusGroup n ∧ PreservesOrientation f := Iff.rfl

theorem orientationPreservingMobiusGroup_le_general (n : ℕ) [NeZero n] :
    orientationPreservingMobiusGroup n ≤ generalMobiusGroup n := fun _ h ↦ h.1

theorem mem_orientationPreservingMobiusGroup_iff_even_word [NeZero n] (f : ExtendedHomeomorph n) :
    f ∈ orientationPreservingMobiusGroup n ↔ ∃ l : List (ExtendedHomeomorph n),
      (∀ g ∈ l, IsReflection g) ∧ l.prod = f ∧ Even l.length := by
  constructor
  · intro hf
    exact (generalMobius_preservesOrientation_iff_even_word hf.1).mp hf.2
  · rintro ⟨l, hl, rfl, he⟩
    exact ⟨(generalMobiusGroup n).list_prod_mem (fun f hf ↦ (hl f hf).mem_generalMobiusGroup),
      (reflectionWord_preservesOrientation_iff_even l hl).mpr he⟩

theorem IsReflection.not_mem_orientationPreservingMobiusGroup [NeZero n]
    {f : ExtendedHomeomorph n} (hf : IsReflection f) : f ∉ orientationPreservingMobiusGroup n :=
  fun h ↦ hf.not_preservesOrientation h.2

end LowDimensionalTopology.Geometry.Inversive
