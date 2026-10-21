/- Released under Apache 2.0 license as described in the file LICENSE. -/
/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Mobius.Circle.GeometricDisc
public import Mathlib.Topology.Sheaves.EtaleSpace
public import Mathlib.Topology.Sheaves.LocalPredicate
public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Tactic
public import LowDimensionalTopology.Geometry.Surfaces.Topology.FinitePunctureExtension
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Analysis.Complex.Basic
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.FuchsianBranchGeometry
public import LowDimensionalTopology.Geometry.Surfaces.Riemann.CompatiblePowerBranches
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Topology TopologicalSpace CategoryTheory Opposite Filter Set
namespace LowDimensionalTopology.Geometry.Surfaces

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The genuine sheaf of continuous local lifts of p through q. -/
def continuousLiftLocalPredicate (p : X → Z) (q : Y → Z) :
    TopCat.LocalPredicate (fun _ : TopCat.of X => Y) where
  pred {_} f := Continuous f ∧ ∀ x, q (f x) = p x.val
  res {U V} i f h := by
    refine ⟨h.1.comp (Opens.isOpenEmbedding_of_le i.le).continuous, ?_⟩
    intro x
    exact h.2 ⟨x.val, i.le x.property⟩
  locality {_} f h := by
    refine ⟨(TopCat.continuousLocal (TopCat.of X) Y).locality f ?_, ?_⟩
    · intro x
      obtain ⟨V, hx, i, hv⟩ := h x
      exact ⟨V, hx, i, hv.1⟩
    · intro x
      obtain ⟨V, hx, i, hv⟩ := h x
      exact hv.2 ⟨x.val, hx⟩

abbrev continuousLiftPresheaf (p : X → Z) (q : Y → Z) :=
  (TopCat.subsheafToTypes (continuousLiftLocalPredicate p q)).presheaf

/-- Evaluation of the actual germ, retaining its physical target point. -/
def continuousLiftEtaleValue (p : X → Z) (q : Y → Z)
    (g : (continuousLiftPresheaf p q).EtaleSpace) : Y :=
  TopCat.stalkToFiber (continuousLiftLocalPredicate p q) g.base g.germ

theorem continuousLiftEtaleValue_projection (p : X → Z) (q : Y → Z)
    (g : (continuousLiftPresheaf p q).EtaleSpace) :
    q (continuousLiftEtaleValue p q g) = p g.base := by
  obtain ⟨U, hx, s, hs⟩ := (continuousLiftPresheaf p q).exists_germ_eq g.germ
  unfold continuousLiftEtaleValue
  rw [← hs, TopCat.stalkToFiber_germ]
  exact s.property.2 ⟨g.base, hx⟩

theorem continuousLiftEtaleValue_continuous (p : X → Z) (q : Y → Z) :
    Continuous (continuousLiftEtaleValue p q) := by
  rw [continuous_iff_continuousAt]
  intro g
  obtain ⟨U, hx, s, hs⟩ := (continuousLiftPresheaf p q).exists_germ_eq g.germ
  have hbase : ContinuousAt (fun g : (continuousLiftPresheaf p q).EtaleSpace => g.base) g :=
    (TopCat.Presheaf.EtaleSpace.continuous_base _).continuousAt
  have hsec := g.eventually_nhds hx s hs
  rw [ContinuousAt, tendsto_def]
  intro V hV
  have he : continuousLiftEtaleValue p q g = s.val ⟨g.base, hx⟩ := by
    unfold continuousLiftEtaleValue
    rw [← hs, TopCat.stalkToFiber_germ]
  rw [he] at hV
  have hnear := s.property.1.continuousAt.preimage_mem_nhds hV
  rw [nhds_subtype] at hnear
  obtain ⟨W, hW, hw⟩ := hnear
  filter_upwards [hbase.preimage_mem_nhds hW, hsec] with g' hg' hsg'
  obtain ⟨hx', hsg'⟩ := hsg'
  have hval : continuousLiftEtaleValue p q g' = s.val ⟨g'.base, hx'⟩ := by
    unfold continuousLiftEtaleValue
    rw [hsg', TopCat.stalkToFiber_germ]
  change continuousLiftEtaleValue p q g' ∈ V
  rw [hval]
  exact hw hg'

/-- Local unique continuation of actual lift germs turns the germ space into
a genuine covering. On a simply connected source its section evaluates to a
global continuous lift, with the prescribed original germ value. -/
theorem continuous_lift_exists_of_locally_extendible_germs
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (p : X → Z) (q : Y → Z)
    (hExt : ∀ x : X, ∃ U : Opens (TopCat.of X), x ∈ U ∧
      ∀ y (hy : y ∈ U), Function.Bijective
        ((continuousLiftPresheaf p q).germ U y hy))
    (U : Opens (TopCat.of X)) (a : X) (ha : a ∈ U)
    (s : (continuousLiftPresheaf p q).obj (op U)) :
    ∃ F : C(X, Y), F a = s.val ⟨a, ha⟩ ∧ ∀ x, q (F x) = p x := by
  let P := continuousLiftPresheaf p q
  let g : P.EtaleSpace := ⟨a, P.germ U a ha s⟩
  have hp : IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := P)) :=
    TopCat.Presheaf.EtaleSpace.isCoveringMap_base hExt
  obtain ⟨S, hS, _⟩ := hp.existsUnique_continuousMap_lifts (ContinuousMap.id X) a g rfl
  let F : C(X, Y) := ⟨fun x => continuousLiftEtaleValue p q (S x),
    (continuousLiftEtaleValue_continuous p q).comp S.continuous⟩
  refine ⟨F, ?_, ?_⟩
  · change continuousLiftEtaleValue p q (S a) = s.val ⟨a, ha⟩
    rw [hS.1]
    exact TopCat.stalkToFiber_germ (continuousLiftLocalPredicate p q) U a ha s
  · intro x
    have hx : (S x).base = x := congrFun hS.2 x
    change q (continuousLiftEtaleValue p q (S x)) = p x
    rw [continuousLiftEtaleValue_projection p q (S x), hx]

/-- A germ determines a continuous lift on an entire one-puncture chart.
Uniqueness is proved on the genuine unramified covering and then extended
across the puncture by continuity; no branched-cover axiom is used. -/
theorem continuousLift_germ_injective_of_covering_off_point
    [TopologicalSpace Z] [T2Space Y]
    (p : X → Z) (q : Y → Z) (V : Set Z) (a : X)
    (hconn : IsPreconnected ({a}ᶜ : Set X)) (hdense : Dense ({a}ᶜ : Set X))
    (hpV : ∀ x, x ≠ a → p x ∈ V) (hq : IsCoveringMap (V.restrictPreimage q))
    (x : X) : Function.Injective
      ((continuousLiftPresheaf p q).germ ⊤ x (mem_univ x)) := by
  let P := continuousLiftPresheaf p q
  intro s t he
  obtain ⟨W, hxW, i, j, hW⟩ := P.germ_eq x (mem_univ x) (mem_univ x) s t he
  obtain ⟨u, hua, huW⟩ := hdense.exists_mem_open W.isOpen ⟨x, hxW⟩
  have heu : s.val ⟨u, mem_univ u⟩ = t.val ⟨u, mem_univ u⟩ := by
    exact congrFun (congrArg Subtype.val hW) ⟨u, huW⟩
  let S : ({a}ᶜ : Set X) → q ⁻¹' V := fun z =>
    ⟨s.val ⟨z.val, mem_univ z.val⟩, by
      change q (s.val ⟨z.val, mem_univ z.val⟩) ∈ V
      rw [s.property.2]
      exact hpV z.val z.property⟩
  let T : ({a}ᶜ : Set X) → q ⁻¹' V := fun z =>
    ⟨t.val ⟨z.val, mem_univ z.val⟩, by
      change q (t.val ⟨z.val, mem_univ z.val⟩) ∈ V
      rw [t.property.2]
      exact hpV z.val z.property⟩
  have hSc : Continuous S :=
    (s.property.1.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _
  have hTc : Continuous T :=
    (t.property.1.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _
  have hcomp : V.restrictPreimage q ∘ S = V.restrictPreimage q ∘ T := by
    funext z
    apply Subtype.ext
    change q (s.val ⟨z.val, mem_univ z.val⟩) = q (t.val ⟨z.val, mem_univ z.val⟩)
    rw [s.property.2, t.property.2]
  let : PreconnectedSpace ({a}ᶜ : Set X) := isPreconnected_iff_preconnectedSpace.mp hconn
  have hST : S = T := hq.eq_of_comp_eq hSc hTc hcomp ⟨u, hua⟩ (Subtype.ext heu)
  have hs : Continuous (fun z : X => s.val ⟨z, mem_univ z⟩) :=
    s.property.1.comp (continuous_id.subtype_mk _)
  have ht : Continuous (fun z : X => t.val ⟨z, mem_univ z⟩) :=
    t.property.1.comp (continuous_id.subtype_mk _)
  have hAll := hs.ext_on hdense ht (fun z hz => congrArg Subtype.val (congrFun hST ⟨z, hz⟩))
  apply Subtype.ext
  funext z
  exact congrFun hAll z.val

end LowDimensionalTopology.Geometry.Surfaces


noncomputable section
set_option autoImplicit false
open Set Topology
namespace LowDimensionalTopology.Geometry.Surfaces

/-- Two continuous power branches on a connected set differ by one constant
root of unity whenever the reference branch has no zeros there. -/
theorem continuous_equal_power_branches_ratio_constant
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsPreconnected S)
    (f g : X → ℂ) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hgn : ∀ x ∈ S, g x ≠ 0) (n : ℕ) (hn : n ≠ 0)
    (hpow : ∀ x ∈ S, f x ^ n = g x ^ n) {a : X} (ha : a ∈ S) :
    (f a / g a) ^ n = 1 ∧ ∀ x ∈ S, f x = (f a / g a) * g x := by
  have hp : ∀ x ∈ S, (f x / g x) ^ n = 1 := by
    intro x hx
    rw [div_pow, hpow x hx, div_self (pow_ne_zero _ (hgn x hx))]
  have hc : ContinuousOn (fun x => f x / g x) S := hf.div hg hgn
  have hfin : IsDiscrete (↑(Polynomial.nthRootsFinset n (1 : ℂ)) : Set ℂ) :=
    (Polynomial.nthRootsFinset n (1 : ℂ)).finite_toSet.isDiscrete
  have hmap : MapsTo (fun x => f x / g x) S
      (↑(Polynomial.nthRootsFinset n (1 : ℂ)) : Set ℂ) := by
    intro x hx
    exact (Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn) 1).mpr (hp x hx)
  refine ⟨hp a ha, ?_⟩
  intro x hx
  have he := hS.constant_of_mapsTo hfin hc hmap hx ha
  exact (div_eq_iff (hgn x hx)).mp he

/-- Agreement at one regular point forces agreement of the entire continuous
branches on that connected set; no branch choice is added as a hypothesis. -/
theorem continuous_equal_power_branches_eqOn
    {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsPreconnected S)
    (f g : X → ℂ) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hgn : ∀ x ∈ S, g x ≠ 0) (n : ℕ) (hn : n ≠ 0)
    (hpow : ∀ x ∈ S, f x ^ n = g x ^ n) {a : X} (ha : a ∈ S)
    (he : f a = g a) : EqOn f g S := by
  obtain ⟨_, h⟩ := continuous_equal_power_branches_ratio_constant
    hS f g hf hg hgn n hn hpow ha
  intro x hx
  simpa only [he, div_self (hgn a ha), one_mul] using h x hx

/-- Every continuous local solution of two equal power equations is a
single root-of-unity multiple of the reference branch as a genuine germ,
including the center where all physical values coincide. -/
theorem continuous_equal_power_branches_germ_factor
    (f g : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hf : ContinuousOn f U) (hg : ContinuousOn g U) (hg0 : g 0 = 0)
    (hgn : ∀ z ∈ U, z ≠ 0 → g z ≠ 0) (n : ℕ) (hn : n ≠ 0)
    (hpow : ∀ z ∈ U, f z ^ n = g z ^ n) (x : ℂ) (hx : x ∈ U) :
    ∃ ζ : ℂ, ζ ^ n = 1 ∧ f =ᶠ[𝓝 x] (fun z => ζ * g z) := by
  by_cases hx0 : x = 0
  · subst x
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU 0 hx
    let a : ℂ := (r / 2 : ℝ)
    have ha : a ∈ Metric.ball (0 : ℂ) r \ {0} := by
      refine ⟨?_, ?_⟩
      · change dist a 0 < r
        simpa [a, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (half_pos hr), abs_of_pos hr] using half_lt_self hr
      · simpa only [mem_singleton_iff, a, Complex.ofReal_eq_zero] using (half_pos hr).ne'
    have hc := complex_punctured_ball_preconnected (0 : ℂ) r hr
    obtain ⟨hζ, he⟩ := continuous_equal_power_branches_ratio_constant hc f g
      (hf.mono (fun z hz => hrU hz.1)) (hg.mono (fun z hz => hrU hz.1))
      (fun z hz => hgn z (hrU hz.1) hz.2) n hn
      (fun z hz => hpow z (hrU hz.1)) ha
    have hf0 : f 0 = 0 := by
      apply (pow_eq_zero_iff hn).mp
      simpa only [hg0, zero_pow hn] using hpow 0 hx
    refine ⟨f a / g a, hζ, ?_⟩
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with z hz
    by_cases hz0 : z = 0
    · simp only [hz0, hf0, hg0, mul_zero]
    · exact he z ⟨hz, hz0⟩
  · have hxU : x ∈ U \ {0} := ⟨hx, hx0⟩
    obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp (hU.sdiff isClosed_singleton) x hxU
    have ha : x ∈ Metric.ball x r := Metric.mem_ball_self hr
    obtain ⟨hζ, he⟩ := continuous_equal_power_branches_ratio_constant
      (convex_ball x r).isPreconnected f g
      (hf.mono (fun z hz => (hrU hz).1)) (hg.mono (fun z hz => (hrU hz).1))
      (fun z hz => hgn z (hrU hz).1 (hrU hz).2) n hn
      (fun z hz => hpow z (hrU hz).1) ha
    refine ⟨f x / g x, hζ, ?_⟩
    filter_upwards [Metric.ball_mem_nhds x hr] with z hz
    exact he z hz

/-- All global continuous roots of the same physical power map are its
literal root-of-unity rotations, with no analyticity premise. -/
theorem continuous_power_identity_root_classification
    (f : ℂ → ℂ) (hf : Continuous f) (n : ℕ) (hn : n ≠ 0)
    (hpow : ∀ z, f z ^ n = z ^ n) :
    ∃ ζ : ℂ, ζ ^ n = 1 ∧ f = (fun z => ζ * z) := by
  have hc : IsPreconnected ({0}ᶜ : Set ℂ) := by
    rw [← Complex.range_exp]
    exact isPreconnected_range Complex.continuous_exp
  obtain ⟨hζ, he⟩ := continuous_equal_power_branches_ratio_constant hc f id
    hf.continuousOn continuousOn_id (fun z hz => hz) n hn
    (fun z _ => hpow z) (show (1 : ℂ) ∈ ({0}ᶜ : Set ℂ) by simp)
  refine ⟨f 1, by simpa only [id_eq, div_one] using hζ, ?_⟩
  funext z
  by_cases hz : z = 0
  · subst z
    have hzero : f 0 = 0 := (pow_eq_zero_iff hn).mp (by simpa only [zero_pow hn] using hpow 0)
    simp only [hzero, mul_zero]
  · simpa only [id_eq, div_one] using he z hz

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
open Set Topology Filter
open scoped OnePoint

namespace MobiusQuotientChartData
variable {H : Subgroup Mobius.complexMobiusGroup} {D : Surfaces.MobiusInvariantDomain H}

/-- Every continuous local lift in an actual quotient power chart extends
throughout a fixed physical coordinate neighborhood. The original germ is
retained, including at a branch center where point values alone do not
separate the different lift germs. -/
theorem continuous_local_lift_continuation
    (C : Surfaces.MobiusQuotientChartData D) (U : Set ℂ) (hU : IsOpen U)
    (G : ℂ → ℂ) (hG : ContinuousOn G U) (hG0 : G 0 = 0)
    (hGn : ∀ v ∈ U, v ≠ 0 → G v ≠ 0)
    (hGb : ∀ v ∈ U, G v ∈ Metric.ball (0 : ℂ) C.radius)
    (p : ℂ → Surfaces.MobiusDomainQuotient D)
    (hp : ∀ v (hv : v ∈ U), Surfaces.mobiusDiscDomainProjection D C.disc C.disc_subset
      (C.coordinate.symm ⟨G v, hGb v hv⟩) = p v)
    (V : Set ℂ) (hV : IsOpen V) (f : ℂ → D.carrier)
    (hf : ContinuousOn f V)
    (hfp : ∀ v ∈ V, Surfaces.mobiusDomainProjection D (f v) = p v)
    (x : ℂ) (hx : x ∈ U) (hxV : x ∈ V) :
    ∃ F : C(U, D.carrier), (∀ v, Surfaces.mobiusDomainProjection D (F v) = p v.val) ∧
      ∀ᶠ v : ℂ in 𝓝 x, ∃ hv : v ∈ U, F ⟨v, hv⟩ = f v := by
  classical
  let c : C.disc := C.coordinate.symm ⟨G x, hGb x hx⟩
  have hproj : Surfaces.mobiusDomainProjection D ⟨c.val, C.disc_subset c.property⟩ =
      Surfaces.mobiusDomainProjection D (f x) := (hp x hx).trans (hfp x hxV).symm
  obtain ⟨g, hg⟩ := Quotient.exact hproj
  change g • f x = (⟨c.val, C.disc_subset c.property⟩ : D.carrier) at hg
  let k : ℂ → D.carrier := fun v => g • f v
  have hkc : ContinuousOn k V := (continuous_const_smul g).comp_continuousOn hf
  let W : Set ℂ := U ∩ (V ∩ (fun v => (k v).val) ⁻¹' C.disc)
  have hWo : IsOpen W := hU.inter
    ((continuous_subtype_val.comp_continuousOn hkc).isOpen_inter_preimage hV C.disc_isOpen)
  have hxW : x ∈ W := by
    refine ⟨hx, hxV, ?_⟩
    change (g • f x).val ∈ C.disc
    rw [hg]
    exact c.property
  let R : ℂ → ℂ := fun v => Surfaces.mobiusNormalizedDiscChart C.normalizer (k v).val
  have hRcoord (v : ℂ) (hv : v ∈ W) :
      R v = (C.coordinate ⟨(k v).val, hv.2.2⟩).val := by
    change Surfaces.mobiusNormalizedDiscChart C.normalizer (k v).val = _
    have he := C.coordinate_coe ⟨(k v).val, hv.2.2⟩
    have hh := congrArg Surfaces.sphereFiniteChart he
    change Surfaces.sphereFiniteChart (C.normalizer.val (k v).val) = _
    simpa only [Surfaces.sphereFiniteChart_coe] using hh
  have hRc : ContinuousOn R W := by
    intro v hv
    have hc : ContinuousAt (fun v => (k v).val) v :=
      ((continuous_subtype_val.comp_continuousOn hkc) v hv.2.1).continuousAt
        (hV.mem_nhds hv.2.1)
    exact (ContinuousAt.comp (f := fun v : ℂ => (k v).val) (x := v)
      ((Surfaces.mobiusNormalizedDiscChart C.normalizer).continuousAt
        (Surfaces.mobiusNormalizedDiscChart_source C.normalizer C.radius hv.2.2)) hc).continuousWithinAt
  have hpow (v : ℂ) (hv : v ∈ W) : R v ^ C.degree = G v ^ C.degree := by
    have he : Surfaces.mobiusDiscDomainProjection D C.disc C.disc_subset ⟨(k v).val, hv.2.2⟩ =
        Surfaces.mobiusDiscDomainProjection D C.disc C.disc_subset
          (C.coordinate.symm ⟨G v, hGb v hv.1⟩) := by
      calc
        Surfaces.mobiusDomainProjection D ⟨(k v).val, C.disc_subset hv.2.2⟩ =
            Surfaces.mobiusDomainProjection D (f v) := Quotient.sound ⟨g, rfl⟩
        _ = p v := hfp v hv.2.1
        _ = _ := (hp v hv.1).symm
    calc
      R v ^ C.degree = C.chart
          (Surfaces.mobiusDiscDomainProjection D C.disc C.disc_subset ⟨(k v).val, hv.2.2⟩) := by
        rw [C.chart_apply_projection, hRcoord v hv]
      _ = C.chart (Surfaces.mobiusDiscDomainProjection D C.disc C.disc_subset
          (C.coordinate.symm ⟨G v, hGb v hv.1⟩)) := congrArg C.chart he
      _ = G v ^ C.degree := by
        rw [C.chart_apply_projection, Homeomorph.apply_symm_apply]
  obtain ⟨ζ, hζ, hEq⟩ := Surfaces.continuous_equal_power_branches_germ_factor R G W hWo
    hRc (hG.mono inter_subset_left) hG0
    (fun v hv => hGn v hv.1) C.degree C.degree_pos.ne' hpow x hxW
  have hζn : ‖ζ‖ = 1 := Complex.norm_eq_one_of_pow_eq_one hζ C.degree_pos.ne'
  have hζb (v : U) : ζ * G v.val ∈ Metric.ball (0 : ℂ) C.radius := by
    have hv := hGb v.val v.property
    simpa only [Metric.mem_ball, dist_zero_right, norm_mul, hζn, one_mul] using hv
  let L : U → C.disc := fun v => C.coordinate.symm ⟨ζ * G v.val, hζb v⟩
  have hLc : Continuous L := C.coordinate.symm.continuous.comp
    ((continuous_const.mul (hG.domRestrict)).subtype_mk _)
  let l : U → D.carrier := fun v => ⟨(L v).val, C.disc_subset (L v).property⟩
  have hlc : Continuous l := (continuous_subtype_val.comp hLc).subtype_mk _
  let F : C(U, D.carrier) := ⟨fun v => g⁻¹ • l v,
    (continuous_const_smul g⁻¹).comp hlc⟩
  refine ⟨F, ?_, ?_⟩
  · intro v
    have he : Surfaces.mobiusDiscDomainProjection D C.disc C.disc_subset (L v) = p v.val := by
      rw [← hp v.val v.property]
      apply C.chart.injOn (C.projection_mem_source (L v))
        (C.projection_mem_source (C.coordinate.symm ⟨G v.val, hGb v.val v.property⟩))
      rw [C.chart_apply_projection, C.chart_apply_projection]
      dsimp only [L]
      rw [Homeomorph.apply_symm_apply, Homeomorph.apply_symm_apply,
        mul_pow, hζ, one_mul]
    change Surfaces.mobiusDomainProjection D (g⁻¹ • _) = p v.val
    have heq : Surfaces.mobiusDomainProjection D (g⁻¹ • l v) =
        Surfaces.mobiusDomainProjection D (l v) := Quotient.sound ⟨g⁻¹, rfl⟩
    exact heq.trans he
  · filter_upwards [hWo.mem_nhds hxW, hEq] with v hv hve
    refine ⟨hv.1, ?_⟩
    have hcoord : C.coordinate ⟨(k v).val, hv.2.2⟩ =
        (⟨ζ * G v, hζb ⟨v, hv.1⟩⟩ : Metric.ball (0 : ℂ) C.radius) := by
      apply Subtype.ext
      exact (hRcoord v hv).symm.trans hve
    have hpoint : L ⟨v, hv.1⟩ = ⟨(k v).val, hv.2.2⟩ := by
      apply C.coordinate.injective
      exact (C.coordinate.apply_symm_apply _).trans hcoord.symm
    change g⁻¹ • (⟨(L ⟨v, hv.1⟩).val, _⟩ : D.carrier) = f v
    rw [hpoint]
    change g⁻¹ • (g • f v) = f v
    exact inv_smul_smul g (f v)

end MobiusQuotientChartData
end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Surfaces
open Set Topology TopologicalSpace CategoryTheory Opposite Filter
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces

/-- A genuine regular covering makes lift sections on a punctured complex
chart uniquely determined by their original germs. Continuity fills the
single center; the target may have genuine branching there. -/
theorem continuousLift_germ_injective_on_complex_open
    {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] [T2Space Y]
    (p : ℂ → Z) (q : Y → Z) (U : Opens (TopCat.of ℂ)) (a : ℂ)
    (hconn : IsPreconnected ((U : Set ℂ) \ {a}))
    (V : Set Z) (hpV : ∀ z ∈ (U : Set ℂ), z ≠ a → p z ∈ V)
    (hq : IsCoveringMap (V.restrictPreimage q)) (x : ℂ) (hx : x ∈ U) :
    Function.Injective ((continuousLiftPresheaf p q).germ U x hx) := by
  let P := continuousLiftPresheaf p q
  intro s t he
  obtain ⟨W, hxW, i, j, hW⟩ := P.germ_eq x hx hx s t he
  obtain ⟨u, hua, huW⟩ := (dense_compl_singleton a).exists_mem_open W.isOpen ⟨x, hxW⟩
  have heu : s.val ⟨u, i.le huW⟩ = t.val ⟨u, j.le huW⟩ :=
    congrFun (congrArg Subtype.val hW) ⟨u, huW⟩
  let A : Set ℂ := (U : Set ℂ) \ {a}
  let S : A → q ⁻¹' V := fun z =>
    ⟨s.val ⟨z.val, z.property.1⟩, by
      change q (s.val ⟨z.val, z.property.1⟩) ∈ V
      rw [s.property.2]
      exact hpV z.val z.property.1 z.property.2⟩
  let T : A → q ⁻¹' V := fun z =>
    ⟨t.val ⟨z.val, z.property.1⟩, by
      change q (t.val ⟨z.val, z.property.1⟩) ∈ V
      rw [t.property.2]
      exact hpV z.val z.property.1 z.property.2⟩
  have hSc : Continuous S :=
    (s.property.1.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _
  have hTc : Continuous T :=
    (t.property.1.comp (continuous_subtype_val.subtype_mk _)).subtype_mk _
  have hcomp : V.restrictPreimage q ∘ S = V.restrictPreimage q ∘ T := by
    funext z
    apply Subtype.ext
    change q (s.val ⟨z.val, z.property.1⟩) = q (t.val ⟨z.val, z.property.1⟩)
    rw [s.property.2, t.property.2]
  let : PreconnectedSpace A := isPreconnected_iff_preconnectedSpace.mp hconn
  have hST : S = T := hq.eq_of_comp_eq hSc hTc hcomp
    ⟨u, i.le huW, hua⟩ (Subtype.ext heu)
  have hdense : Dense ((Subtype.val : U → ℂ) ⁻¹' ({a}ᶜ : Set ℂ)) :=
    (dense_compl_singleton a).preimage U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap
  have hAll : s.val = t.val := s.property.1.ext_on hdense t.property.1 (by
    intro z hz
    exact congrArg Subtype.val (congrFun hST ⟨z.val, z.property, hz⟩))
  exact Subtype.ext hAll

namespace MobiusQuotientChartData
variable {H : Subgroup Mobius.complexMobiusGroup} {D : Surfaces.MobiusInvariantDomain H}

/-- In an actual quotient coordinate neighborhood with equal branch powers,
every original continuous lift germ extends over that whole neighborhood.
The physical quotient and its true finite stabilizer supply all branches. -/
theorem continuousLift_germ_surjective_on_coordinate_open
    (C : Surfaces.MobiusQuotientChartData D) (U : Opens (TopCat.of ℂ))
    (G : ℂ → ℂ) (hG : ContinuousOn G U) (hG0 : G 0 = 0)
    (hGn : ∀ v ∈ (U : Set ℂ), v ≠ 0 → G v ≠ 0)
    (hGb : ∀ v ∈ (U : Set ℂ), G v ∈ Metric.ball (0 : ℂ) C.radius)
    (p : ℂ → Surfaces.MobiusDomainQuotient D)
    (hp : ∀ v (hv : v ∈ (U : Set ℂ)), Surfaces.mobiusDiscDomainProjection D C.disc C.disc_subset
      (C.coordinate.symm ⟨G v, hGb v hv⟩) = p v)
    (x : ℂ) (hx : x ∈ U) :
    Function.Surjective ((Surfaces.continuousLiftPresheaf p (Surfaces.mobiusDomainProjection D)).germ U x hx) := by
  classical
  let P := Surfaces.continuousLiftPresheaf p (Surfaces.mobiusDomainProjection D)
  intro a
  obtain ⟨V, hxV, s, hs⟩ := P.exists_germ_eq a
  let f : ℂ → D.carrier := fun z => if hz : z ∈ V then s.val ⟨z, hz⟩ else s.val ⟨x, hxV⟩
  have hf (z : V) : f z.val = s.val z := by simp only [f, dite_eq_left z.property]
  have hfc : ContinuousOn f V := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert s.property.1 using 1
    funext z
    exact hf z
  have hfp (z : ℂ) (hz : z ∈ V) : Surfaces.mobiusDomainProjection D (f z) = p z := by
    rw [hf ⟨z, hz⟩]
    exact s.property.2 ⟨z, hz⟩
  obtain ⟨F, hFp, hFs⟩ := C.continuous_local_lift_continuation U U.isOpen
    G hG hG0 hGn hGb p hp V V.isOpen f hfc hfp x hx hxV
  let t : P.obj (op U) := ⟨F, F.continuous, hFp⟩
  refine ⟨t, ?_⟩
  obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.mp hFs
  let O : Opens (TopCat.of ℂ) := ⟨W ∩ ((U : Set ℂ) ∩ V),
    hWo.inter (U.isOpen.inter V.isOpen)⟩
  refine (P.germ_ext O ⟨hxW, hx, hxV⟩
    (homOfLE (fun z hz => hz.2.1)) (homOfLE (fun z hz => hz.2.2)) ?_).trans hs
  apply Subtype.ext
  funext z
  obtain ⟨hv, he⟩ := hW z.val z.property.1
  change F ⟨z.val, z.property.2.1⟩ = s.val ⟨z.val, z.property.2.2⟩
  exact he.trans (hf ⟨z.val, z.property.2.2⟩)

end MobiusQuotientChartData
end LowDimensionalTopology.Geometry.Surfaces


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
open scoped OnePoint
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- Equal actual branch degrees give an actual local analytic lift between
the physical invariant discs, with the original quotient projections commuting.
The local lift is constructed, rather than supplied as an orbifold hypothesis. -/
theorem actual_equal_degree_quotient_local_lift
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (B : Surfaces.MobiusDomainQuotient D.domain ≃ₜ Surfaces.MobiusDomainQuotient E.domain)
    (hB : Surfaces.RiemannAnalyticMap
      (Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas
      (Surfaces.mobiusQuotientRiemannSurface E.domain E.discontinuous).toRiemannAtlas B)
    (C : Surfaces.MobiusQuotientChartData D.domain)
    (F : Surfaces.MobiusQuotientChartData E.domain)
    (z : C.disc) (w : F.disc)
    (hz : C.normalizer.val z.val = (0 : ℂ)) (hw : F.normalizer.val w.val = (0 : ℂ))
    (hBw : B (Surfaces.mobiusDiscDomainProjection D.domain C.disc C.disc_subset z) =
      Surfaces.mobiusDiscDomainProjection E.domain F.disc F.disc_subset w)
    (hn : F.degree = C.degree) :
    ∃ G : OpenPartialHomeomorph ℂ ℂ, 0 ∈ G.source ∧ G 0 = 0 ∧
      AnalyticAt ℂ G 0 ∧ deriv G 0 ≠ 0 ∧
      ∀ᶠ v : ℂ in 𝓝 0, ∃ hv : v ∈ Metric.ball (0 : ℂ) C.radius,
        ∃ hv' : G v ∈ Metric.ball (0 : ℂ) F.radius,
          Surfaces.mobiusDiscDomainProjection E.domain F.disc F.disc_subset
              (F.coordinate.symm ⟨G v, hv'⟩) =
            B (Surfaces.mobiusDiscDomainProjection D.domain C.disc C.disc_subset
              (C.coordinate.symm ⟨v, hv⟩)) := by
  let P := C.chart.symm.trans (B.toOpenPartialHomeomorph.trans F.chart)
  have hzC : (C.coordinate z).val = 0 :=
    OnePoint.coe_injective ((C.coordinate_coe z).symm.trans hz)
  have hwF : (F.coordinate w).val = 0 :=
    OnePoint.coe_injective ((F.coordinate_coe w).symm.trans hw)
  have hz0 : C.chart (Surfaces.mobiusDiscDomainProjection D.domain C.disc C.disc_subset z) = 0 := by
    rw [C.chart_apply_projection, hzC, zero_pow C.degree_pos.ne']
  have hw0 : F.chart (Surfaces.mobiusDiscDomainProjection E.domain F.disc F.disc_subset w) = 0 := by
    rw [F.chart_apply_projection, hwF, zero_pow F.degree_pos.ne']
  have hzS := C.projection_mem_source z
  have hwS := F.projection_mem_source w
  have hzT : (0 : ℂ) ∈ C.chart.target := by
    rw [← hz0]
    exact C.chart.map_source hzS
  have hzInv : C.chart.symm 0 = Surfaces.mobiusDiscDomainProjection D.domain C.disc C.disc_subset z := by
    rw [← hz0, C.chart.left_inv hzS]
  have hP0 : (0 : ℂ) ∈ P.source := by
    refine ⟨hzT, ?_⟩
    change C.chart.symm 0 ∈ Set.univ ∧ B (C.chart.symm 0) ∈ F.chart.source
    rw [hzInv, hBw]
    exact ⟨trivial, hwS⟩
  have hPval : P 0 = 0 := by
    change F.chart (B (C.chart.symm 0)) = 0
    rw [hzInv, hBw, hw0]
  have hPa : AnalyticOnNhd ℂ P P.source := by
    intro u hu
    change AnalyticAt ℂ (Surfaces.riemannChartMap C.chart B F.chart) u
    exact hB.2 C.chart ⟨C, rfl⟩ F.chart ⟨F, rfl⟩ u ⟨hu.1, hu.2.2⟩
  have hPd : deriv P 0 ≠ 0 := Surfaces.openPartialHomeomorph_analytic_forward_deriv_ne_zero P hPa 0 hP0
  obtain ⟨G, hG0, hGval, hGa, hGd, hpow⟩ :=
    Surfaces.analytic_local_coordinate_change_power_homeomorph P (hPa 0 hP0) hPval hPd C.degree C.degree_pos.ne'
  refine ⟨G, hG0, hGval, hGa, hGd, ?_⟩
  have hsource : ∀ᶠ v : ℂ in 𝓝 0, v ^ C.degree ∈ P.source := by
    have hc : ContinuousAt (fun v : ℂ => v ^ C.degree) 0 := (continuous_id.pow _).continuousAt
    apply hc.eventually
    change P.source ∈ 𝓝 ((0 : ℂ) ^ C.degree)
    rw [zero_pow C.degree_pos.ne']
    exact P.open_source.mem_nhds hP0
  have hvC : ∀ᶠ v : ℂ in 𝓝 0, v ∈ Metric.ball (0 : ℂ) C.radius :=
    Metric.ball_mem_nhds 0 C.radius_pos
  have hvF : ∀ᶠ v : ℂ in 𝓝 0, G v ∈ Metric.ball (0 : ℂ) F.radius := by
    apply (G.continuousAt hG0).eventually
    rw [hGval]
    exact Metric.ball_mem_nhds 0 F.radius_pos
  filter_upwards [hsource, hvC, hvF] with v hvp hv hv'
  refine ⟨hv, hv', ?_⟩
  have hleft := F.projection_mem_source (F.coordinate.symm ⟨G v, hv'⟩)
  have hright : B (Surfaces.mobiusDiscDomainProjection D.domain C.disc C.disc_subset
      (C.coordinate.symm ⟨v, hv⟩)) ∈ F.chart.source := by
    rw [← C.chart_symm_pow ⟨v, hv⟩]
    exact hvp.2.2
  apply F.chart.injOn hleft hright
  rw [F.chart_apply_projection, Homeomorph.apply_symm_apply, hn, hpow]
  change F.chart (B (C.chart.symm (v ^ C.degree))) = _
  rw [C.chart_symm_pow ⟨v, hv⟩]

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Topology Filter TopologicalSpace CategoryTheory Opposite
open scoped OnePoint
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- Equality of the actual branch degrees produces one fixed source
coordinate ball on which every continuous lift germ extends uniquely.
The resulting continuation property is proved from the actual quotient
power charts, including at elliptic centers. -/
theorem actual_equal_degree_local_germ_bijective
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (B : Surfaces.MobiusDomainQuotient D.domain ≃ₜ Surfaces.MobiusDomainQuotient E.domain)
    (hB : Surfaces.RiemannAnalyticMap
      (Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas
      (Surfaces.mobiusQuotientRiemannSurface E.domain E.discontinuous).toRiemannAtlas B)
    (C : Surfaces.MobiusQuotientChartData D.domain)
    (F : Surfaces.MobiusQuotientChartData E.domain)
    (z : C.disc) (w : F.disc)
    (hz : C.normalizer.val z.val = (0 : ℂ)) (hw : F.normalizer.val w.val = (0 : ℂ))
    (hFw : F.stabilizer = DiscreteGroups.mobiusBoundaryStabilizer K w.val)
    (hBw : B (Surfaces.mobiusDiscDomainProjection D.domain C.disc C.disc_subset z) =
      Surfaces.mobiusDiscDomainProjection E.domain F.disc F.disc_subset w)
    (hn : F.degree = C.degree) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball (0 : ℂ) r ⊆ Metric.ball (0 : ℂ) C.radius ∧
      Nonempty ((Surfaces.continuousLiftPresheaf (fun v : ℂ => B (C.chart.symm (v ^ C.degree)))
        (Surfaces.mobiusDomainProjection E.domain)).obj
          (op (⟨Metric.ball (0 : ℂ) r, Metric.isOpen_ball⟩ : Opens (TopCat.of ℂ)))) ∧
      ∀ x (hx : x ∈ Metric.ball (0 : ℂ) r), Function.Bijective
        ((Surfaces.continuousLiftPresheaf (fun v : ℂ => B (C.chart.symm (v ^ C.degree)))
          (Surfaces.mobiusDomainProjection E.domain)).germ ⟨Metric.ball (0 : ℂ) r, Metric.isOpen_ball⟩ x hx) := by
  obtain ⟨G, hG0, hGval, _, _, hEq⟩ :=
    actual_equal_degree_quotient_local_lift D E B hB C F z w hz hw hBw hn
  obtain ⟨r, hr, hSub⟩ := Metric.mem_nhds_iff.mp
    (hEq.and (G.open_source.mem_nhds hG0))
  let U : Opens (TopCat.of ℂ) := ⟨Metric.ball (0 : ℂ) r, Metric.isOpen_ball⟩
  have hCball : (U : Set ℂ) ⊆ Metric.ball (0 : ℂ) C.radius := by
    intro v hv
    exact (hSub hv).1.choose
  have hGc : ContinuousOn G U := G.continuousOn.mono (fun v hv => (hSub hv).2)
  have hGn : ∀ v ∈ (U : Set ℂ), v ≠ 0 → G v ≠ 0 := by
    intro v hv hvn he
    apply hvn
    exact G.injOn (hSub hv).2 hG0 (he.trans hGval.symm)
  have hGb : ∀ v ∈ (U : Set ℂ), G v ∈ Metric.ball (0 : ℂ) F.radius := by
    intro v hv
    exact (hSub hv).1.choose_spec.choose
  let p : ℂ → Surfaces.MobiusDomainQuotient E.domain := fun v => B (C.chart.symm (v ^ C.degree))
  have hp (v : ℂ) (hv : v ∈ (U : Set ℂ)) :
      Surfaces.mobiusDiscDomainProjection E.domain F.disc F.disc_subset
        (F.coordinate.symm ⟨G v, hGb v hv⟩) = p v := by
    obtain ⟨hvC, hvF, he⟩ := (hSub hv).1
    change _ = B (C.chart.symm (v ^ C.degree))
    rw [C.chart_symm_pow ⟨v, hvC⟩]
    exact he
  have hpRegular (v : ℂ) (hv : v ∈ (U : Set ℂ)) (hvn : v ≠ 0) :
      p v ∈ fuchsianRegularQuotientSet E := by
    rw [← hp v hv]
    apply (original_regular_value_iff_stabilizer_bot E _).mpr
    have hfree := centered_branch_punctured_point_free E
      (⟨w.val, F.disc_subset w.property⟩ : E.domain.carrier) F hw hFw
      (F.coordinate.symm ⟨G v, hGb v hv⟩)
      (by simpa only [Homeomorph.apply_symm_apply] using hGn v hv hvn)
    apply le_antisymm
    · intro g hg
      exact hfree g hg
    · exact bot_le
  have hseed : Nonempty ((Surfaces.continuousLiftPresheaf p (Surfaces.mobiusDomainProjection E.domain)).obj (op U)) := by
    let l : U → F.disc := fun v => F.coordinate.symm ⟨G v.val, hGb v.val v.property⟩
    have hlc : Continuous l := F.coordinate.symm.continuous.comp (hGc.domRestrict.subtype_mk _)
    exact ⟨⟨fun v => ⟨(l v).val, F.disc_subset (l v).property⟩,
      (continuous_subtype_val.comp hlc).subtype_mk _, fun v => hp v.val v.property⟩⟩
  refine ⟨r, hr, hCball, hseed, ?_⟩
  intro x hx
  exact ⟨Surfaces.continuousLift_germ_injective_on_complex_open p (Surfaces.mobiusDomainProjection E.domain)
      U 0 (Surfaces.complex_punctured_ball_preconnected 0 r hr)
      (fuchsianRegularQuotientSet E) hpRegular (fuchsian_regular_projection_covering E) x hx,
    F.continuousLift_germ_surjective_on_coordinate_open U G hGc hGval hGn hGb p hp x hx⟩

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Surfaces
open Set Topology TopologicalSpace CategoryTheory Opposite Filter

/-- Equality of original continuous-lift germs is exactly local agreement
of their actual section functions; it is stronger than equality of values. -/
theorem continuousLift_germ_eq_iff_eventuallyEq
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (p : X → Z) (q : Y → Z) (U : Opens (TopCat.of X))
    (x : X) (hx : x ∈ U) (s t : (continuousLiftPresheaf p q).obj (op U)) :
    (continuousLiftPresheaf p q).germ U x hx s =
      (continuousLiftPresheaf p q).germ U x hx t ↔
      s.val =ᶠ[𝓝 (⟨x, hx⟩ : U)] t.val := by
  let P := continuousLiftPresheaf p q
  constructor
  · intro he
    obtain ⟨W, hxW, i, j, hW⟩ := P.germ_eq x hx hx s t he
    filter_upwards [(W.isOpen.preimage (continuous_subtype_val : Continuous
      (Subtype.val : U → X))).mem_nhds hxW] with z hz
    exact congrFun (congrArg Subtype.val hW) ⟨z.val, hz⟩
  · intro he
    obtain ⟨W, hW, hWo, hxW⟩ := eventually_nhds_iff.mp he
    let V : Opens (TopCat.of X) := ⟨Subtype.val '' W,
      U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap W hWo⟩
    have hVU : V ≤ U := fun z hz => by
      obtain ⟨w, _, rfl⟩ := hz
      exact w.property
    apply P.germ_ext V ⟨⟨x, hx⟩, hxW, rfl⟩ (homOfLE hVU) (homOfLE hVU)
    apply Subtype.ext
    funext z
    obtain ⟨w, hw, hwe⟩ := z.property
    have heq := hW w hw
    change s.val ⟨z.val, hVU z.property⟩ = t.val ⟨z.val, hVU z.property⟩
    have hwEq : w = (⟨z.val, hVU z.property⟩ : U) := Subtype.ext hwe
    simpa only [hwEq] using heq

/-- Genuine coordinate homeomorphisms transport whole sections of the
continuous local-lift sheaf, with the physical projection unchanged. -/
def continuousLiftSectionCoordinateEquiv
    {X T Y Z : Type} [TopologicalSpace X] [TopologicalSpace T] [TopologicalSpace Y]
    (p : X → Z) (r : T → Z) (q : Y → Z)
    (U : Opens (TopCat.of X)) (V : Opens (TopCat.of T)) (e : U ≃ₜ V)
    (he : ∀ u : U, p u.val = r (e u).val) :
    (continuousLiftPresheaf p q).obj (op U) ≃
      (continuousLiftPresheaf r q).obj (op V) where
  toFun s := ⟨fun v => s.val (e.symm v), s.property.1.comp e.symm.continuous, by
    intro v
    rw [s.property.2, he, e.apply_symm_apply]⟩
  invFun s := ⟨fun u => s.val (e u), s.property.1.comp e.continuous, by
    intro u
    rw [s.property.2, he]⟩
  left_inv s := by
    apply Subtype.ext
    funext u
    exact congrArg s.val (e.symm_apply_apply u)
  right_inv s := by
    apply Subtype.ext
    funext v
    exact congrArg s.val (e.apply_symm_apply v)

/-- Local agreement, and hence equality of germs, is preserved and reflected
by the actual change of source coordinates. -/
theorem continuousLiftSectionCoordinateEquiv_germ_eq_iff
    {X T Y Z : Type} [TopologicalSpace X] [TopologicalSpace T] [TopologicalSpace Y]
    (p : X → Z) (r : T → Z) (q : Y → Z)
    (U : Opens (TopCat.of X)) (V : Opens (TopCat.of T)) (e : U ≃ₜ V)
    (he : ∀ u : U, p u.val = r (e u).val)
    (x : U) (s t : (continuousLiftPresheaf p q).obj (op U)) :
    (continuousLiftPresheaf p q).germ U x.val x.property s =
      (continuousLiftPresheaf p q).germ U x.val x.property t ↔
    (continuousLiftPresheaf r q).germ V (e x).val (e x).property
        (continuousLiftSectionCoordinateEquiv p r q U V e he s) =
      (continuousLiftPresheaf r q).germ V (e x).val (e x).property
        (continuousLiftSectionCoordinateEquiv p r q U V e he t) := by
  rw [continuousLift_germ_eq_iff_eventuallyEq, continuousLift_germ_eq_iff_eventuallyEq]
  constructor
  · intro h
    change (∀ᶠ u : U in 𝓝 x, s.val u = t.val u) at h
    change ∀ᶠ v : V in 𝓝 (e x), s.val (e.symm v) = t.val (e.symm v)
    have hh : ∀ᶠ u : U in 𝓝 (e.symm (e x)), s.val u = t.val u := by
      simpa only [e.symm_apply_apply] using h
    exact (e.symm.continuous.continuousAt (x := e x)).eventually hh
  · intro h
    change (∀ᶠ v : V in 𝓝 (e x), s.val (e.symm v) = t.val (e.symm v)) at h
    have hh := (e.continuous.continuousAt (x := x)).eventually h
    change ∀ᶠ u : U in 𝓝 x, s.val u = t.val u
    simpa only [continuousLiftSectionCoordinateEquiv, Equiv.coe_fn_mk,
      e.symm_apply_apply] using hh

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Surfaces
open Set Topology TopologicalSpace CategoryTheory Opposite Filter

/-- The ability of all lift germs to extend uniquely over a coordinate
neighborhood is invariant under a genuine change of source coordinates. -/
theorem continuousLift_germ_bijective_of_coordinates
    {X T Y Z : Type} [TopologicalSpace X] [TopologicalSpace T] [TopologicalSpace Y]
    (p : X → Z) (r : T → Z) (q : Y → Z)
    (U : Opens (TopCat.of X)) (V : Opens (TopCat.of T)) (e : U ≃ₜ V)
    (he : ∀ u : U, p u.val = r (e u).val)
    (hV : ∀ y (hy : y ∈ V), Function.Bijective
      ((continuousLiftPresheaf r q).germ V y hy))
    (x : X) (hx : x ∈ U) : Function.Bijective
      ((continuousLiftPresheaf p q).germ U x hx) := by
  let P := continuousLiftPresheaf p q
  let Q := continuousLiftPresheaf r q
  let E := continuousLiftSectionCoordinateEquiv p r q U V e he
  constructor
  · intro s t hst
    apply E.injective
    apply (hV (e ⟨x, hx⟩).val (e ⟨x, hx⟩).property).injective
    exact (continuousLiftSectionCoordinateEquiv_germ_eq_iff p r q U V e he
      ⟨x, hx⟩ s t).mp hst
  · intro a
    obtain ⟨W, hxW, s, hs⟩ := P.exists_germ_eq a
    let A : Set U := Subtype.val ⁻¹' (W : Set X)
    let L : Opens (TopCat.of T) := ⟨Subtype.val '' (e '' A),
      V.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _
        (e.isOpenMap A (W.isOpen.preimage continuous_subtype_val))⟩
    have hLV : L ≤ V := by
      rintro z ⟨v, _, rfl⟩
      exact v.property
    have hLW (v : L) : (e.symm ⟨v.val, hLV v.property⟩).val ∈ W := by
      obtain ⟨y, ⟨u, hu, hue⟩, hyv⟩ := v.property
      have huEq : e.symm (⟨v.val, hLV v.property⟩ : V) = u := by
        apply e.injective
        rw [e.apply_symm_apply]
        exact Subtype.ext (hyv.symm.trans (congrArg Subtype.val hue).symm)
      rw [huEq]
      exact hu
    let j : L → U := fun v => e.symm ⟨v.val, hLV v.property⟩
    have hj : Continuous j := e.symm.continuous.comp
      (continuous_subtype_val.subtype_mk _)
    let m : Q.obj (op L) := ⟨fun v => s.val ⟨(j v).val, hLW v⟩,
      s.property.1.comp ((continuous_subtype_val.comp hj).subtype_mk _), by
        intro v
        rw [s.property.2, he]
        change r (e (e.symm ⟨v.val, hLV v.property⟩)).val = r v.val
        rw [e.apply_symm_apply]⟩
    have hyL : (e ⟨x, hx⟩).val ∈ L :=
      ⟨e ⟨x, hx⟩, ⟨⟨x, hx⟩, hxW, rfl⟩, rfl⟩
    obtain ⟨t, ht⟩ := (hV (e ⟨x, hx⟩).val (e ⟨x, hx⟩).property).surjective
      (Q.germ L (e ⟨x, hx⟩).val hyL m)
    obtain ⟨N, hyN, iN, jN, hN⟩ := Q.germ_eq (e ⟨x, hx⟩).val
      (e ⟨x, hx⟩).property hyL t m ht
    let B : Set U := e ⁻¹' (Subtype.val ⁻¹' (N : Set T))
    let O : Opens (TopCat.of X) := ⟨Subtype.val '' B,
      U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap B
        ((N.isOpen.preimage continuous_subtype_val).preimage e.continuous)⟩
    have hOU : O ≤ U := by
      rintro z ⟨u, _, rfl⟩
      exact u.property
    have hOW : O ≤ W := by
      rintro z ⟨u, hu, rfl⟩
      have hh := hLW ⟨(e u).val, jN.le hu⟩
      simpa only [e.symm_apply_apply] using hh
    refine ⟨E.symm t, ?_⟩
    refine (P.germ_ext O ⟨⟨x, hx⟩, hyN, rfl⟩ (homOfLE hOU) (homOfLE hOW) ?_).trans hs
    apply Subtype.ext
    funext z
    obtain ⟨u, hu, huz⟩ := z.property
    have hh := congrFun (congrArg Subtype.val hN) ⟨(e u).val, hu⟩
    change t.val ⟨(e u).val, iN.le hu⟩ =
      s.val ⟨(e.symm ⟨(e u).val, hLV (jN.le hu)⟩).val,
        hLW ⟨(e u).val, jN.le hu⟩⟩ at hh
    have huEq : u = (⟨z.val, hOU z.property⟩ : U) := Subtype.ext huz
    change t.val (e ⟨z.val, hOU z.property⟩) = s.val ⟨z.val, hOW z.property⟩
    simpa only [e.symm_apply_apply, huEq] using hh

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Surfaces
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
open Set Topology TopologicalSpace
open scoped OnePoint

namespace MobiusQuotientChartData
variable {H : Subgroup Mobius.complexMobiusGroup} {D : Surfaces.MobiusInvariantDomain H}

/-- The actual finite branch coordinate, regarded as an open partial
homeomorphism on the original physical invariant domain. -/
def physicalCoordinate (C : Surfaces.MobiusQuotientChartData D) :
    OpenPartialHomeomorph D.carrier ℂ := by
  let i : C.disc → D.carrier := fun z => ⟨z.val, C.disc_subset z.property⟩
  have hi : IsOpenEmbedding i := isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
    ⟨continuous_subtype_val.subtype_mk _,
      fun (a b : C.disc) h => Subtype.ext (congrArg (Subtype.val : D.carrier → Mobius.ExtendedComplex) h),
      C.disc_isOpen.isOpenMap_subtype_val.subtype_mk _⟩
  let V : Opens (TopCat.of ℂ) := ⟨Metric.ball (0 : ℂ) C.radius, Metric.isOpen_ball⟩
  let φ := C.coordinate.toOpenPartialHomeomorph.trans
    (V.openPartialHomeomorphSubtypeCoe ⟨⟨0, Metric.mem_ball_self C.radius_pos⟩⟩)
  exact φ.lift_openEmbedding hi

theorem physicalCoordinate_target (C : Surfaces.MobiusQuotientChartData D) :
    C.physicalCoordinate.target = Metric.ball (0 : ℂ) C.radius := by
  simp [physicalCoordinate]

theorem physicalCoordinate_source (C : Surfaces.MobiusQuotientChartData D) :
    C.physicalCoordinate.source = {z : D.carrier | z.val ∈ C.disc} := by
  ext z
  constructor
  · rintro ⟨w, _, hw⟩
    have he : w.val = z.val := congrArg (Subtype.val : D.carrier → Mobius.ExtendedComplex) hw
    change z.val ∈ C.disc
    rw [← he]
    exact w.property
  · intro hz
    exact ⟨⟨z.val, hz⟩, ⟨trivial, trivial⟩, rfl⟩

theorem physicalCoordinate_apply
    (C : Surfaces.MobiusQuotientChartData D)
    (z : C.disc) :
    C.physicalCoordinate (⟨z.val, C.disc_subset z.property⟩ : D.carrier) =
      (C.coordinate z).val := by
  dsimp only [physicalCoordinate]
  rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
  rfl

theorem physicalCoordinate_quotient (C : Surfaces.MobiusQuotientChartData D)
    (z : D.carrier) (hz : z ∈ C.physicalCoordinate.source) :
    C.chart.symm (C.physicalCoordinate z ^ C.degree) = Surfaces.mobiusDomainProjection D z := by
  rw [C.physicalCoordinate_source] at hz
  have he := C.chart_symm_pow (C.coordinate ⟨z.val, hz⟩)
  rw [Homeomorph.symm_apply_apply] at he
  have hc := C.physicalCoordinate_apply ⟨z.val, hz⟩
  exact (congrArg (fun v : ℂ => C.chart.symm (v ^ C.degree)) hc).trans he

end MobiusQuotientChartData
end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Topology Filter TopologicalSpace CategoryTheory Opposite
open scoped OnePoint
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- A true analytic equivalence of the original quotients that matches the
actual full stabilizer orders has uniquely extendible lift germs on actual
open neighborhoods in the original physical invariant disc. -/
theorem actual_quotient_lift_neighborhoods
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (B : Surfaces.MobiusDomainQuotient D.domain ≃ₜ Surfaces.MobiusDomainQuotient E.domain)
    (hB : Surfaces.RiemannAnalyticMap
      (Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas
      (Surfaces.mobiusQuotientRiemannSurface E.domain E.discontinuous).toRiemannAtlas B)
    (hDegree : ∀ (z : D.domain.carrier) (w : E.domain.carrier),
      B (Surfaces.mobiusDomainProjection D.domain z) = Surfaces.mobiusDomainProjection E.domain w →
        Nat.card (DiscreteGroups.mobiusBoundaryStabilizer H z.val) = Nat.card (DiscreteGroups.mobiusBoundaryStabilizer K
          w.val)) :
    ∀ a : D.domain.carrier, ∃ U : Opens (TopCat.of D.domain.carrier), a ∈ U ∧
      Nonempty ((Surfaces.continuousLiftPresheaf (B ∘ Surfaces.mobiusDomainProjection D.domain)
        (Surfaces.mobiusDomainProjection E.domain)).obj (op U)) ∧
      ∀ x (hx : x ∈ U), Function.Bijective
        ((Surfaces.continuousLiftPresheaf (B ∘ Surfaces.mobiusDomainProjection D.domain)
          (Surfaces.mobiusDomainProjection E.domain)).germ U x hx) := by
  intro a
  obtain ⟨C, hC0, _, haC, hCn⟩ := fuchsian_centered_quotient_branch_chart D a
  obtain ⟨b, hb⟩ := Surfaces.mobiusDomainProjection_surjective E.domain
    (B (Surfaces.mobiusDomainProjection D.domain a))
  obtain ⟨F, hF0, hFK, hbF, hFn⟩ := fuchsian_centered_quotient_branch_chart E b
  have hBw : B (Surfaces.mobiusDiscDomainProjection D.domain C.disc C.disc_subset ⟨a.val, haC⟩) =
      Surfaces.mobiusDiscDomainProjection E.domain F.disc F.disc_subset ⟨b.val, hbF⟩ := hb.symm
  have hn : F.degree = C.degree := by
    rw [hFn, hCn]
    exact (hDegree a b hb.symm).symm
  obtain ⟨r, hr, hCr, hseed, hBij⟩ := actual_equal_degree_local_germ_bijective
    D E B hB C F ⟨a.val, haC⟩ ⟨b.val, hbF⟩ hC0 hF0 hFK hBw hn
  let φ := C.physicalCoordinate
  let U : Opens (TopCat.of D.domain.carrier) :=
    ⟨φ.source ∩ φ ⁻¹' Metric.ball (0 : ℂ) r,
      φ.continuousOn.isOpen_inter_preimage φ.open_source Metric.isOpen_ball⟩
  let V : Opens (TopCat.of ℂ) := ⟨Metric.ball (0 : ℂ) r, Metric.isOpen_ball⟩
  have hVT : (V : Set ℂ) ⊆ φ.target := by
    rw [C.physicalCoordinate_target]
    exact hCr
  have hImage : φ '' (U : Set D.domain.carrier) = (V : Set ℂ) := by
    apply Subset.antisymm
    · rintro v ⟨u, hu, rfl⟩
      exact hu.2
    · intro v hv
      refine ⟨φ.symm v, ⟨φ.map_target (hVT hv), ?_⟩, φ.right_inv (hVT hv)⟩
      change φ (φ.symm v) ∈ V
      rw [φ.right_inv (hVT hv)]
      exact hv
  let e : U ≃ₜ V := φ.homeomorphOfImageSubsetSource inter_subset_left hImage
  have haSource : a ∈ φ.source := by
    rw [C.physicalCoordinate_source]
    exact haC
  have ha0 : φ a = 0 := by
    rw [C.physicalCoordinate_apply ⟨a.val, haC⟩]
    exact OnePoint.coe_injective ((C.coordinate_coe ⟨a.val, haC⟩).symm.trans hC0)
  have haU : a ∈ U := ⟨haSource, by
    change φ a ∈ Metric.ball (0 : ℂ) r
    rw [ha0]
    exact Metric.mem_ball_self hr⟩
  let p := B ∘ Surfaces.mobiusDomainProjection D.domain
  let q := Surfaces.mobiusDomainProjection E.domain
  let rmap : ℂ → Surfaces.MobiusDomainQuotient E.domain := fun v => B (C.chart.symm (v ^ C.degree))
  have he (u : U) : p u.val = rmap (e u).val := by
    change B (Surfaces.mobiusDomainProjection D.domain u.val) = B (C.chart.symm (φ u.val ^ C.degree))
    exact congrArg B (C.physicalCoordinate_quotient u.val u.property.1).symm
  let S := Surfaces.continuousLiftSectionCoordinateEquiv p rmap q U V e he
  have hsU : Nonempty ((Surfaces.continuousLiftPresheaf p q).obj (op U)) :=
    ⟨S.symm (Classical.choice hseed)⟩
  refine ⟨U, haU, hsU, ?_⟩
  intro x hx
  exact Surfaces.continuousLift_germ_bijective_of_coordinates p rmap q U V e he hBij x hx

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Topology Filter TopologicalSpace CategoryTheory Opposite
open scoped OnePoint
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- The space of actual continuous lift germs is a genuine covering of the
original invariant disc when the analytic quotient equivalence preserves
actual full stabilizer orders. No global continuation is assumed. -/
theorem actual_quotient_lift_etale_covering
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (B : Surfaces.MobiusDomainQuotient D.domain ≃ₜ Surfaces.MobiusDomainQuotient E.domain)
    (hB : Surfaces.RiemannAnalyticMap
      (Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas
      (Surfaces.mobiusQuotientRiemannSurface E.domain E.discontinuous).toRiemannAtlas B)
    (hDegree : ∀ (z : D.domain.carrier) (w : E.domain.carrier),
      B (Surfaces.mobiusDomainProjection D.domain z) = Surfaces.mobiusDomainProjection E.domain w →
        Nat.card (DiscreteGroups.mobiusBoundaryStabilizer H z.val) = Nat.card (DiscreteGroups.mobiusBoundaryStabilizer K
          w.val)) :
    IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := Surfaces.continuousLiftPresheaf
      (B ∘ Surfaces.mobiusDomainProjection D.domain) (Surfaces.mobiusDomainProjection E.domain))) := by
  apply TopCat.Presheaf.EtaleSpace.isCoveringMap_base
  intro a
  obtain ⟨U, ha, _, hU⟩ := actual_quotient_lift_neighborhoods D E B hB hDegree a
  exact ⟨U, ha, hU⟩

/-- Analytic quotient equivalences with matching actual branch orders lift
continuously to the original physical discs, including across every
elliptic center. This is the monodromy step, not a supplied orbifold lift. -/
theorem actual_quotient_exists_continuous_lift
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (B : Surfaces.MobiusDomainQuotient D.domain ≃ₜ Surfaces.MobiusDomainQuotient E.domain)
    (hB : Surfaces.RiemannAnalyticMap
      (Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas
      (Surfaces.mobiusQuotientRiemannSurface E.domain E.discontinuous).toRiemannAtlas B)
    (hDegree : ∀ (z : D.domain.carrier) (w : E.domain.carrier),
      B (Surfaces.mobiusDomainProjection D.domain z) = Surfaces.mobiusDomainProjection E.domain w →
        Nat.card (DiscreteGroups.mobiusBoundaryStabilizer H z.val) = Nat.card (DiscreteGroups.mobiusBoundaryStabilizer K
          w.val)) :
    ∃ F : C(D.domain.carrier, E.domain.carrier),
      ∀ z, Surfaces.mobiusDomainProjection E.domain (F z) = B (Surfaces.mobiusDomainProjection D.domain z) := by
  let RD := Surfaces.mobiusDomainRiemannSurface D.domain
  let := fuchsianDisc_domain_simplyConnected D
  let := RD.toRiemannAtlas.locallyPathConnectedSpace
  let := RD.connectedSpace
  let a : D.domain.carrier := Classical.choice inferInstance
  obtain ⟨U, ha, hs, _⟩ := actual_quotient_lift_neighborhoods D E B hB hDegree a
  have hExt : ∀ x : D.domain.carrier, ∃ V : Opens (TopCat.of D.domain.carrier),
      x ∈ V ∧ ∀ y (hy : y ∈ V), Function.Bijective
        ((Surfaces.continuousLiftPresheaf (B ∘ Surfaces.mobiusDomainProjection D.domain)
          (Surfaces.mobiusDomainProjection E.domain)).germ V y hy) := by
    intro x
    obtain ⟨V, hx, _, hV⟩ := actual_quotient_lift_neighborhoods D E B hB hDegree x
    exact ⟨V, hx, hV⟩
  obtain ⟨F, _, hF⟩ := Surfaces.continuous_lift_exists_of_locally_extendible_germs
    (B ∘ Surfaces.mobiusDomainProjection D.domain) (Surfaces.mobiusDomainProjection E.domain)
      hExt U a ha (Classical.choice hs)
  exact ⟨F, hF⟩

end LowDimensionalTopology.Geometry.Fuchsian


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Topology Filter
namespace LowDimensionalTopology.Geometry.Surfaces

/-- A continuous root of an analytic power is analytic at any nonzero value.
The actual local inverse is selected by continuity of the given root. -/
theorem analyticAt_continuous_root_of_ne_zero (f : ℂ → ℂ) (z : ℂ)
    (hf : ContinuousAt f z) (hfn : f z ≠ 0) (n : ℕ) (hn : n ≠ 0)
    (ha : AnalyticAt ℂ (fun w => f w ^ n) z) : AnalyticAt ℂ f z := by
  have hp : AnalyticAt ℂ (fun v : ℂ => v ^ n) (f z) := analyticAt_id.pow n
  have hpd : deriv (fun v : ℂ => v ^ n) (f z) ≠ 0 := by
    rw [deriv_pow_field]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hn) (pow_ne_zero _ hfn)
  have hstrict := hp.hasStrictDerivAt.hasStrictFDerivAt_equiv hpd
  let P := hstrict.toOpenPartialHomeomorph (fun v : ℂ => v ^ n)
  have hz : f z ∈ P.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hP : AnalyticOnNhd ℂ P P.source := fun v _ => analyticAt_id.pow n
  have hi := openPartialHomeomorph_analytic_inverse P hP
  have hpa : AnalyticAt ℂ P.symm (f z ^ n) := hi _ (P.map_source hz)
  have hcomp : AnalyticAt ℂ (fun w => P.symm (f w ^ n)) z :=
    AnalyticAt.comp (f := fun w : ℂ => f w ^ n) (x := z) hpa ha
  apply hcomp.congr
  filter_upwards [hf.eventually (P.open_source.mem_nhds hz)] with w hw
  exact P.left_inv hw

/-- A continuous local nth root of an analytic function is holomorphic even
at its zeros. No analytic branch or zero multiplicity is assumed. -/
theorem analyticAt_of_continuousOn_power (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hf : ContinuousOn f U) (z : ℂ) (hz : z ∈ U) (n : ℕ) (hn : n ≠ 0)
    (ha : AnalyticAt ℂ (fun w => f w ^ n) z) : AnalyticAt ℂ f z := by
  obtain hzero | hnonzero := ha.eventually_eq_zero_or_eventually_ne_zero
  · apply (analyticAt_const (v := (0 : ℂ))).congr
    filter_upwards [hzero] with w hw
    exact ((pow_eq_zero_iff hn).mp hw).symm
  · apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
      _ ((hf z hz).continuousAt (hU.mem_nhds hz))
    have hnear : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ (fun v => f v ^ n) w :=
      (isOpen_analyticAt ℂ _).mem_nhds ha
    filter_upwards [hnonzero, mem_nhdsWithin_of_mem_nhds hnear,
      mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hz)] with w hw hwa hwU
    have hfn : f w ≠ 0 := by
      intro he
      apply hw
      rw [he, zero_pow hn]
    exact (analyticAt_continuous_root_of_ne_zero f w
      ((hf w hwU).continuousAt (hU.mem_nhds hwU)) hfn n hn hwa).differentiableAt

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Surfaces
open Set Topology Filter
open scoped OnePoint
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces

/-- A continuous lift through the original branched Mobius quotient is
analytic in the original atlases, including elliptic branch values. -/
theorem RiemannAnalyticMap.of_comp_mobiusProjection
    {X : Type*} [TopologicalSpace X] (A : RiemannAtlas X)
    {H : Subgroup Mobius.complexMobiusGroup} (D : MobiusInvariantDomain H)
    (hD : DiscreteGroups.IsMobiusDiscontinuousOn H D.carrier)
    (f : X → D.carrier) (hf : Continuous f)
    (ha : RiemannAnalyticMap A (mobiusQuotientRiemannSurface D hD).toRiemannAtlas
      (mobiusDomainProjection D ∘ f)) :
    RiemannAnalyticMap A (mobiusDomainRiemannSurface D).toRiemannAtlas f := by
  apply Surfaces.RiemannAnalyticMap.of_comp_localHomeomorph
    (sphereRiemannAtlas.liftLocalHomeomorph_projection_analytic Subtype.val
      D.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph)
    D.isOpen.isOpenEmbedding_subtypeVal.isLocalHomeomorph hf
  rw [riemannAnalyticMap_iff_locally]
  refine ⟨continuous_subtype_val.comp hf, ?_⟩
  intro x
  obtain ⟨e, he, hx⟩ := A.cover x
  obtain ⟨g, hg, hxg⟩ := sphereRiemannAtlas.cover (f x).val
  obtain ⟨C, hxC⟩ := mobiusQuotientChartData_containing D hD (f x)
  let R : ℂ → ℂ := fun u => mobiusNormalizedDiscChart C.normalizer (f (e.symm u)).val
  have hnear : ∀ᶠ u : ℂ in 𝓝 (e x),
      u ∈ e.target ∧ (f (e.symm u)).val ∈ C.disc := by
    have ht : Tendsto (fun u : ℂ => (f (e.symm u)).val)
        (𝓝 (e x)) (𝓝 (f x).val) := by
      have ht := (continuous_subtype_val.comp hf).continuousAt.comp
        (e.continuousAt_symm (e.map_source hx))
      change Tendsto (fun u : ℂ => (f (e.symm u)).val)
        (𝓝 (e x)) (𝓝 (f (e.symm (e x))).val) at ht
      simpa only [e.left_inv hx] using ht
    exact Filter.Eventually.and (e.open_target.mem_nhds (e.map_source hx))
      (ht.eventually (C.disc_isOpen.mem_nhds hxC))
  obtain ⟨r, hr, hrSub⟩ := Metric.mem_nhds_iff.mp hnear
  have hRcont : ContinuousOn R (Metric.ball (e x) r) := by
    intro u hu
    have hcu := (hrSub hu).2
    have hcs := mobiusNormalizedDiscChart_source C.normalizer C.radius hcu
    have hc1 : ContinuousAt (fun v : ℂ => (f (e.symm v)).val) u :=
      (continuous_subtype_val.comp hf).continuousAt.comp
        (e.continuousAt_symm (hrSub hu).1)
    have hc2 : ContinuousAt (mobiusNormalizedDiscChart C.normalizer)
        (f (e.symm u)).val := (mobiusNormalizedDiscChart C.normalizer).continuousAt hcs
    exact (ContinuousAt.comp (f := fun v : ℂ => (f (e.symm v)).val) hc2 hc1).continuousWithinAt
  have hsource : (mobiusDomainProjection D ∘ f) x ∈ C.chart.source :=
    C.projection_mem_source ⟨(f x).val, hxC⟩
  have hP : AnalyticAt ℂ
      (riemannChartMap e (mobiusDomainProjection D ∘ f) C.chart) (e x) :=
    ha.2 e he C.chart ⟨C, rfl⟩ (e x)
      (riemannChartMapDomain_mem e _ C.chart x hx hsource)
  have hEqPow : ∀ u ∈ Metric.ball (e x) r,
      riemannChartMap e (mobiusDomainProjection D ∘ f) C.chart u = R u ^ C.degree := by
    intro u hu
    exact C.chart_apply_projection ⟨(f (e.symm u)).val, (hrSub hu).2⟩
  have hPpow : AnalyticAt ℂ (fun u => R u ^ C.degree) (e x) := by
    apply hP.congr
    filter_upwards [Metric.ball_mem_nhds (e x) hr] with u hu
    exact hEqPow u hu
  have hRa : AnalyticAt ℂ R (e x) :=
    analyticAt_of_continuousOn_power R _ Metric.isOpen_ball hRcont (e x)
      (Metric.mem_ball_self hr) C.degree C.degree_pos.ne' hPpow
  have hInv (u : ℂ) (hu : u ∈ Metric.ball (e x) r) :
      (C.normalizer⁻¹).val (R u : Mobius.ExtendedComplex) = (f (e.symm u)).val := by
    apply C.normalizer.val.injective
    change C.normalizer.val (C.normalizer.val.symm (R u : Mobius.ExtendedComplex)) = _
    rw [Equiv.apply_symm_apply]
    exact (C.coordinate_coe ⟨(f (e.symm u)).val, (hrSub hu).2⟩).symm
  have hInv0 : (C.normalizer⁻¹).val (R (e x) : Mobius.ExtendedComplex) = (f x).val := by
    simpa only [e.left_inv hx] using hInv (e x) (Metric.mem_ball_self hr)
  have hMa : AnalyticAt ℂ (riemannChartMap sphereFiniteChart (C.normalizer⁻¹).val g)
      (R (e x)) := by
    apply (mobius_riemannSphere_analytic C.normalizer⁻¹).2 sphereFiniteChart
      (by change sphereFiniteChart ∈ sphereCharts; exact Set.mem_insert _ _) g hg
    refine ⟨?_, ?_⟩
    · rw [sphereFiniteChart_target]
      trivial
    · change (C.normalizer⁻¹).val (sphereFiniteChart.symm (R (e x))) ∈ g.source
      rw [sphereFiniteChart_symm, hInv0]
      exact hxg
  have hcomp : AnalyticAt ℂ
      (fun u => riemannChartMap sphereFiniteChart (C.normalizer⁻¹).val g (R u)) (e x) :=
    AnalyticAt.comp (f := R) (x := e x) hMa hRa
  refine ⟨e, he, hx, g, hg, hxg, hcomp.congr ?_⟩
  filter_upwards [Metric.ball_mem_nhds (e x) hr] with u hu
  change g ((C.normalizer⁻¹).val (sphereFiniteChart.symm (R u))) = g (f (e.symm u)).val
  rw [sphereFiniteChart_symm, hInv u hu]

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Topology Filter TopologicalSpace CategoryTheory Opposite
open scoped OnePoint
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- The globally continued lift is analytic in the original physical
atlases, including all elliptic branch centers. -/
theorem actual_quotient_exists_analytic_lift
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (B : Surfaces.MobiusDomainQuotient D.domain ≃ₜ Surfaces.MobiusDomainQuotient E.domain)
    (hB : Surfaces.RiemannAnalyticMap
      (Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas
      (Surfaces.mobiusQuotientRiemannSurface E.domain E.discontinuous).toRiemannAtlas B)
    (hDegree : ∀ (z : D.domain.carrier) (w : E.domain.carrier),
      B (Surfaces.mobiusDomainProjection D.domain z) = Surfaces.mobiusDomainProjection E.domain w →
        Nat.card (DiscreteGroups.mobiusBoundaryStabilizer H z.val) = Nat.card (DiscreteGroups.mobiusBoundaryStabilizer K
          w.val)) :
    ∃ F : C(D.domain.carrier, E.domain.carrier),
      Surfaces.RiemannAnalyticMap (Surfaces.mobiusDomainRiemannSurface D.domain).toRiemannAtlas
        (Surfaces.mobiusDomainRiemannSurface E.domain).toRiemannAtlas F ∧
      ∀ z, Surfaces.mobiusDomainProjection E.domain (F z) = B (Surfaces.mobiusDomainProjection D.domain z) := by
  obtain ⟨F, hF⟩ := actual_quotient_exists_continuous_lift D E B hB hDegree
  refine ⟨F, ?_, hF⟩
  apply Surfaces.RiemannAnalyticMap.of_comp_mobiusProjection
    (Surfaces.mobiusDomainRiemannSurface D.domain).toRiemannAtlas E.domain E.discontinuous F F.continuous
  have he : Surfaces.mobiusDomainProjection E.domain ∘ F = B ∘ Surfaces.mobiusDomainProjection D.domain :=
    funext hF
  rw [he]
  exact hB.comp (Surfaces.mobiusDomainProjection_analytic D.domain D.discontinuous)

end LowDimensionalTopology.Geometry.Fuchsian

namespace LowDimensionalTopology.Geometry.Surfaces
open Set Topology TopologicalSpace CategoryTheory Opposite Filter

/-- The simply connected continuation retains the entire prescribed germ,
not merely its value at a possibly branched point. -/
theorem continuous_lift_exists_preserving_germ
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    (p : X → Z) (q : Y → Z)
    (hExt : ∀ x : X, ∃ U : Opens (TopCat.of X), x ∈ U ∧
      ∀ y (hy : y ∈ U), Function.Bijective ((continuousLiftPresheaf p q).germ U y hy))
    (U : Opens (TopCat.of X)) (a : X) (ha : a ∈ U)
    (s : (continuousLiftPresheaf p q).obj (op U)) :
    ∃ F : C(X, Y), F a = s.val ⟨a, ha⟩ ∧ (∀ x, q (F x) = p x) ∧
      ∀ᶠ x : X in 𝓝 a, ∃ hx : x ∈ U, F x = s.val ⟨x, hx⟩ := by
  let P := continuousLiftPresheaf p q
  let g : P.EtaleSpace := ⟨a, P.germ U a ha s⟩
  have hp : IsCoveringMap (TopCat.Presheaf.EtaleSpace.base (F := P)) :=
    TopCat.Presheaf.EtaleSpace.isCoveringMap_base hExt
  obtain ⟨S, hS, _⟩ := hp.existsUnique_continuousMap_lifts (ContinuousMap.id X) a g rfl
  let F : C(X, Y) := ⟨fun x => continuousLiftEtaleValue p q (S x),
    (continuousLiftEtaleValue_continuous p q).comp S.continuous⟩
  refine ⟨F, ?_, ?_, ?_⟩
  · change continuousLiftEtaleValue p q (S a) = s.val ⟨a, ha⟩
    rw [hS.1]
    exact TopCat.stalkToFiber_germ (continuousLiftLocalPredicate p q) U a ha s
  · intro x
    have hx : (S x).base = x := congrFun hS.2 x
    change q (continuousLiftEtaleValue p q (S x)) = p x
    rw [continuousLiftEtaleValue_projection p q (S x), hx]
  · have hnear : ∀ᶠ x in 𝓝 a, ∃ hxU : (S x).base ∈ U,
        (S x).germ = P.germ U (S x).base hxU s := by
      have ht : Tendsto S (𝓝 a) (𝓝 g) := by
        have ht := S.continuous.continuousAt (x := a)
        change Tendsto S (𝓝 a) (𝓝 (S a)) at ht
        rw [hS.1] at ht
        exact ht
      exact ht.eventually (g.eventually_nhds ha s rfl)
    filter_upwards [hnear] with x hx
    obtain ⟨hxU, hxs⟩ := hx
    have hxBase : (S x).base = x := congrFun hS.2 x
    refine ⟨hxBase ▸ hxU, ?_⟩
    change continuousLiftEtaleValue p q (S x) = _
    unfold continuousLiftEtaleValue
    rw [hxs, TopCat.stalkToFiber_germ]
    exact congrArg s.val (Subtype.ext hxBase)

/-- Local unique extension of all germs makes a global continuous lift
uniquely determined by one genuine germ on a connected source. -/
theorem continuousLift_global_section_eq_of_germ_eq
    {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [PreconnectedSpace X]
    (p : X → Z) (q : Y → Z)
    (hExt : ∀ x : X, ∃ U : Opens (TopCat.of X), x ∈ U ∧
      ∀ y (hy : y ∈ U), Function.Bijective ((continuousLiftPresheaf p q).germ U y hy))
    (s t : (continuousLiftPresheaf p q).obj (op ⊤)) (a : X)
    (ha : (continuousLiftPresheaf p q).germ ⊤ a (mem_univ a) s =
      (continuousLiftPresheaf p q).germ ⊤ a (mem_univ a) t) : s = t := by
  let P := continuousLiftPresheaf p q
  let A : Set X := {x | P.germ ⊤ x (mem_univ x) s = P.germ ⊤ x (mem_univ x) t}
  have hAo : IsOpen A := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    change P.germ ⊤ x (mem_univ x) s = P.germ ⊤ x (mem_univ x) t at hx
    obtain ⟨W, hxW, i, j, hW⟩ := P.germ_eq x (mem_univ x) (mem_univ x) s t hx
    apply Filter.mem_of_superset (W.isOpen.mem_nhds hxW)
    intro y hy
    exact P.germ_ext W hy i j hW
  have hBo : IsOpen Aᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨U, hxU, hU⟩ := hExt x
    let i : U ⟶ ⊤ := homOfLE le_top
    apply Filter.mem_of_superset (U.isOpen.mem_nhds hxU)
    intro y hy hya
    have he : P.germ U y hy (P.map i.op s) = P.germ U y hy (P.map i.op t) := by
      rw [P.germ_res_apply, P.germ_res_apply]
      exact hya
    have hst := (hU y hy).injective he
    apply hx
    change P.germ ⊤ x (mem_univ x) s = P.germ ⊤ x (mem_univ x) t
    rw [← P.germ_res_apply i x hxU, ← P.germ_res_apply i x hxU, hst]
  have hAc : IsClosed A := by simpa only [compl_compl] using hBo.isClosed_compl
  have hAll : A = univ := (show IsClopen A from ⟨hAc, hAo⟩).eq_univ ⟨a, ha⟩
  apply Subtype.ext
  funext x
  have hx : x.val ∈ A := hAll ▸ mem_univ x.val
  change P.germ ⊤ x.val (mem_univ x.val) s = P.germ ⊤ x.val (mem_univ x.val) t at hx
  have he := congrArg (TopCat.stalkToFiber (continuousLiftLocalPredicate p q) x.val) hx
  exact (TopCat.stalkToFiber_germ (continuousLiftLocalPredicate p q) ⊤ x.val
    (mem_univ x.val) s).symm.trans (he.trans
      (TopCat.stalkToFiber_germ (continuousLiftLocalPredicate p q) ⊤ x.val (mem_univ x.val) t))

end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Surfaces
open Set Topology Filter
open scoped OnePoint
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
namespace MobiusQuotientChartData
variable {H : Subgroup Mobius.complexMobiusGroup} {D : Surfaces.MobiusInvariantDomain H}

theorem physicalCoordinate_symm_apply (C : Surfaces.MobiusQuotientChartData D)
    (v : ℂ) (hv : v ∈ Metric.ball (0 : ℂ) C.radius) :
    C.physicalCoordinate.symm v =
      (⟨(C.coordinate.symm ⟨v, hv⟩).val,
        C.disc_subset (C.coordinate.symm ⟨v, hv⟩).property⟩ : D.carrier) := by
  let z : C.disc := C.coordinate.symm ⟨v, hv⟩
  have hz : (⟨z.val, C.disc_subset z.property⟩ : D.carrier) ∈ C.physicalCoordinate.source := by
    rw [C.physicalCoordinate_source]
    exact z.property
  have he : C.physicalCoordinate (⟨z.val, C.disc_subset z.property⟩ : D.carrier) = v := by
    rw [C.physicalCoordinate_apply]
    exact congrArg Subtype.val (C.coordinate.apply_symm_apply ⟨v, hv⟩)
  calc
    C.physicalCoordinate.symm v = C.physicalCoordinate.symm
        (C.physicalCoordinate (⟨z.val, C.disc_subset z.property⟩ : D.carrier)) :=
      congrArg C.physicalCoordinate.symm he.symm
    _ = _ := C.physicalCoordinate.left_inv hz

end MobiusQuotientChartData
end LowDimensionalTopology.Geometry.Surfaces

namespace LowDimensionalTopology.Geometry.Fuchsian
open Set Topology Filter TopologicalSpace CategoryTheory Opposite
open scoped OnePoint
open LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace
  LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Topology

/-- Equality of actual stabilizer orders gives a genuine local physical
homeomorphism over the quotient equivalence, not only a formal root. -/
theorem actual_equal_degree_physical_local_equivalence
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (B : Surfaces.MobiusDomainQuotient D.domain ≃ₜ Surfaces.MobiusDomainQuotient E.domain)
    (hB : Surfaces.RiemannAnalyticMap
      (Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas
      (Surfaces.mobiusQuotientRiemannSurface E.domain E.discontinuous).toRiemannAtlas B)
    (a : D.domain.carrier) (b : E.domain.carrier)
    (hab : B (Surfaces.mobiusDomainProjection D.domain a) = Surfaces.mobiusDomainProjection E.domain b)
    (hn : Nat.card (DiscreteGroups.mobiusBoundaryStabilizer H a.val) =
      Nat.card (DiscreteGroups.mobiusBoundaryStabilizer K b.val)) :
    ∃ L : OpenPartialHomeomorph D.domain.carrier E.domain.carrier,
      a ∈ L.source ∧ L a = b ∧
      ∀ z ∈ L.source, Surfaces.mobiusDomainProjection E.domain (L z) = B (Surfaces.mobiusDomainProjection D.domain z) := by
  obtain ⟨C, hC0, _, haC, hCn⟩ := fuchsian_centered_quotient_branch_chart D a
  obtain ⟨F, hF0, _, hbF, hFn⟩ := fuchsian_centered_quotient_branch_chart E b
  have hCF : F.degree = C.degree := by rw [hFn, hCn, hn]
  obtain ⟨G, hG0, hGval, _, _, hEq⟩ := actual_equal_degree_quotient_local_lift
    D E B hB C F ⟨a.val, haC⟩ ⟨b.val, hbF⟩ hC0 hF0 hab hCF
  let φ := C.physicalCoordinate
  let ψ := F.physicalCoordinate
  have haS : a ∈ φ.source := by rw [C.physicalCoordinate_source]; exact haC
  have hbS : b ∈ ψ.source := by rw [F.physicalCoordinate_source]; exact hbF
  have ha0 : φ a = 0 := by
    rw [C.physicalCoordinate_apply ⟨a.val, haC⟩]
    exact OnePoint.coe_injective ((C.coordinate_coe ⟨a.val, haC⟩).symm.trans hC0)
  have hb0 : ψ b = 0 := by
    rw [F.physicalCoordinate_apply ⟨b.val, hbF⟩]
    exact OnePoint.coe_injective ((F.coordinate_coe ⟨b.val, hbF⟩).symm.trans hF0)
  let L := φ.trans (G.trans ψ.symm)
  have haL : a ∈ L.source := by
    refine ⟨haS, ?_⟩
    change φ a ∈ G.source ∧ G (φ a) ∈ ψ.target
    rw [ha0, hGval, F.physicalCoordinate_target]
    exact ⟨hG0, Metric.mem_ball_self F.radius_pos⟩
  have hLa : L a = b := by
    change ψ.symm (G (φ a)) = b
    rw [ha0, hGval, ← hb0, ψ.left_inv hbS]
  have hT : Tendsto φ (𝓝 a) (𝓝 (0 : ℂ)) := by
    have ht := φ.continuousAt haS
    change Tendsto φ (𝓝 a) (𝓝 (φ a)) at ht
    rw [ha0] at ht
    exact ht
  have hNear : ∀ᶠ z : D.domain.carrier in 𝓝 a,
      Surfaces.mobiusDomainProjection E.domain (L z) = B (Surfaces.mobiusDomainProjection D.domain z) := by
    filter_upwards [L.open_source.mem_nhds haL, hT.eventually hEq] with z hz he
    obtain ⟨hvC, hvF, hp⟩ := he
    have hCz : (⟨(C.coordinate.symm ⟨φ z, hvC⟩).val,
        C.disc_subset (C.coordinate.symm ⟨φ z, hvC⟩).property⟩ : D.domain.carrier) = z :=
      (C.physicalCoordinate_symm_apply (φ z) hvC).symm.trans (φ.left_inv hz.1)
    have hFz : L z = (⟨(F.coordinate.symm ⟨G (φ z), hvF⟩).val,
        F.disc_subset (F.coordinate.symm ⟨G (φ z), hvF⟩).property⟩ : E.domain.carrier) :=
      F.physicalCoordinate_symm_apply (G (φ z)) hvF
    change Surfaces.mobiusDomainProjection E.domain _ = B (Surfaces.mobiusDomainProjection D.domain _) at hp
    simpa only [← hFz, hCz] using hp
  obtain ⟨W, hW, hWo, haW⟩ := eventually_nhds_iff.mp hNear
  refine ⟨L.restr W, ?_, hLa, ?_⟩
  · rw [L.restr_source' W hWo]
    exact ⟨haL, haW⟩
  · intro z hz
    rw [L.restr_source' W hWo] at hz
    exact hW z hz.2


open scoped OnePoint

/-- The actual full point-stabilizer order depends only on the original
quotient point, including regular points of order one. -/
theorem original_quotient_point_stabilizer_card_eq
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (z w : D.domain.carrier)
    (h : Surfaces.mobiusDomainProjection D.domain z = Surfaces.mobiusDomainProjection D.domain w) :
    Nat.card (DiscreteGroups.mobiusBoundaryStabilizer H z.val) = Nat.card (DiscreteGroups.mobiusBoundaryStabilizer H w.val) := by
  obtain ⟨g, hg⟩ := Quotient.exact h
  have hr : MulAction.orbitRel H Mobius.ExtendedComplex z.val w.val :=
    ⟨g, congrArg Subtype.val hg⟩
  let ez : MulAction.stabilizer H z.val ≃* DiscreteGroups.mobiusBoundaryStabilizer H z.val :=
    (MulAction.stabilizer H z.val).equivMapOfInjective H.subtype Subtype.val_injective
  let ew : MulAction.stabilizer H w.val ≃* DiscreteGroups.mobiusBoundaryStabilizer H w.val :=
    (MulAction.stabilizer H w.val).equivMapOfInjective H.subtype Subtype.val_injective
  exact Nat.card_congr ((ez.symm.trans (MulAction.stabilizerEquivStabilizerOfOrbitRel hr)).trans ew).toEquiv


open scoped OnePoint

/-- Original quotient-preserving continuous maps agree globally as soon as
their actual germs agree, even in the presence of elliptic stabilizers. -/
theorem original_quotient_lifts_eq_of_eventuallyEq
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (f g : C(D.domain.carrier, D.domain.carrier))
    (hf : ∀ z, Surfaces.mobiusDomainProjection D.domain (f z) = Surfaces.mobiusDomainProjection D.domain z)
    (hg : ∀ z, Surfaces.mobiusDomainProjection D.domain (g z) = Surfaces.mobiusDomainProjection D.domain z)
    (a : D.domain.carrier) (hfg : f =ᶠ[𝓝 a] g) : f = g := by
  let RD := Surfaces.mobiusDomainRiemannSurface D.domain
  let := RD.connectedSpace
  let p := Surfaces.mobiusDomainProjection D.domain
  have hExt : ∀ x : D.domain.carrier, ∃ U : Opens (TopCat.of D.domain.carrier), x ∈ U ∧
      ∀ y (hy : y ∈ U), Function.Bijective ((Surfaces.continuousLiftPresheaf p p).germ U y hy) := by
    intro x
    obtain ⟨U, hx, _, hU⟩ := actual_quotient_lift_neighborhoods D D (Homeomorph.refl _)
      (Surfaces.RiemannAnalyticMap.id _) (fun z w h => original_quotient_point_stabilizer_card_eq D z w h) x
    exact ⟨U, hx, hU⟩
  let s : (Surfaces.continuousLiftPresheaf p p).obj (op ⊤) :=
    ⟨fun z => f z.val, f.continuous.comp continuous_subtype_val, fun z => hf z.val⟩
  let t : (Surfaces.continuousLiftPresheaf p p).obj (op ⊤) :=
    ⟨fun z => g z.val, g.continuous.comp continuous_subtype_val, fun z => hg z.val⟩
  have hst : (Surfaces.continuousLiftPresheaf p p).germ ⊤ a (mem_univ a) s =
      (Surfaces.continuousLiftPresheaf p p).germ ⊤ a (mem_univ a) t := by
    apply (Surfaces.continuousLift_germ_eq_iff_eventuallyEq p p ⊤ a (mem_univ a) s t).mpr
    change ∀ᶠ z : (⊤ : Opens (TopCat.of D.domain.carrier)) in 𝓝 ⟨a, mem_univ a⟩,
      f z.val = g z.val
    have ht : Tendsto (Subtype.val : (⊤ : Opens (TopCat.of D.domain.carrier)) → D.domain.carrier)
        (𝓝 ⟨a, mem_univ a⟩) (𝓝 a) := continuous_subtype_val.continuousAt
    exact ht.eventually hfg
  have he := Surfaces.continuousLift_global_section_eq_of_germ_eq p p hExt s t a hst
  apply ContinuousMap.ext
  intro z
  exact congrFun (congrArg Subtype.val he) ⟨z, mem_univ z⟩

/-- Matching the actual ramification orders of the original quotient
equivalence gives a genuine homeomorphism of the original physical discs.
The inverse is constructed by continuing the inverse local germ. -/
theorem actual_quotient_exists_physical_homeomorph
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (B : Surfaces.MobiusDomainQuotient D.domain ≃ₜ Surfaces.MobiusDomainQuotient E.domain)
    (hB : Surfaces.RiemannAnalyticMap
      (Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas
      (Surfaces.mobiusQuotientRiemannSurface E.domain E.discontinuous).toRiemannAtlas B)
    (hDegree : ∀ (z : D.domain.carrier) (w : E.domain.carrier),
      B (Surfaces.mobiusDomainProjection D.domain z) = Surfaces.mobiusDomainProjection E.domain w →
        Nat.card (DiscreteGroups.mobiusBoundaryStabilizer H z.val) = Nat.card (DiscreteGroups.mobiusBoundaryStabilizer K
          w.val)) :
    ∃ F : D.domain.carrier ≃ₜ E.domain.carrier,
      ∀ z, Surfaces.mobiusDomainProjection E.domain (F z) = B (Surfaces.mobiusDomainProjection D.domain z) := by
  let RD := Surfaces.mobiusDomainRiemannSurface D.domain
  let RE := Surfaces.mobiusDomainRiemannSurface E.domain
  let := RD.connectedSpace
  let := RE.connectedSpace
  let := fuchsianDisc_domain_simplyConnected D
  let := fuchsianDisc_domain_simplyConnected E
  let := RD.toRiemannAtlas.locallyPathConnectedSpace
  let := RE.toRiemannAtlas.locallyPathConnectedSpace
  have hBi := Surfaces.riemannAnalyticMap_homeomorph_symm B hB
  have hDi (w : E.domain.carrier) (z : D.domain.carrier)
      (h : B.symm (Surfaces.mobiusDomainProjection E.domain w) = Surfaces.mobiusDomainProjection D.domain z) :
      Nat.card (DiscreteGroups.mobiusBoundaryStabilizer K w.val) = Nat.card (DiscreteGroups.mobiusBoundaryStabilizer H z.val) := by
    apply (hDegree z w ?_).symm
    rw [← h, B.apply_symm_apply]
  let a : D.domain.carrier := Classical.choice inferInstance
  obtain ⟨b, hb⟩ := Surfaces.mobiusDomainProjection_surjective E.domain (B (Surfaces.mobiusDomainProjection D.domain a))
  obtain ⟨L, haL, hLa, hL⟩ := actual_equal_degree_physical_local_equivalence D E B hB a b hb.symm
    (hDegree a b hb.symm)
  let U : Opens (TopCat.of D.domain.carrier) := ⟨L.source, L.open_source⟩
  let V : Opens (TopCat.of E.domain.carrier) := ⟨L.target, L.open_target⟩
  have hbL : b ∈ L.target := hLa ▸ L.map_source haL
  let s : (Surfaces.continuousLiftPresheaf (B ∘ Surfaces.mobiusDomainProjection D.domain)
      (Surfaces.mobiusDomainProjection E.domain)).obj (op U) :=
    ⟨fun z => L z.val, L.continuousOn.domRestrict, fun z => hL z.val z.property⟩
  let t : (Surfaces.continuousLiftPresheaf (B.symm ∘ Surfaces.mobiusDomainProjection E.domain)
      (Surfaces.mobiusDomainProjection D.domain)).obj (op V) :=
    ⟨fun z => L.symm z.val, L.continuousOn_symm.domRestrict, by
      intro z
      apply B.injective
      change B (Surfaces.mobiusDomainProjection D.domain (L.symm z.val)) =
        B (B.symm (Surfaces.mobiusDomainProjection E.domain z.val))
      rw [← hL _ (L.map_target z.property), L.right_inv z.property, B.apply_symm_apply]⟩
  have hExt : ∀ x : D.domain.carrier, ∃ W : Opens (TopCat.of D.domain.carrier), x ∈ W ∧
      ∀ y (hy : y ∈ W), Function.Bijective ((Surfaces.continuousLiftPresheaf
        (B ∘ Surfaces.mobiusDomainProjection D.domain) (Surfaces.mobiusDomainProjection E.domain)).germ W y hy) := by
    intro x
    obtain ⟨W, hx, _, hW⟩ := actual_quotient_lift_neighborhoods D E B hB hDegree x
    exact ⟨W, hx, hW⟩
  have hExti : ∀ x : E.domain.carrier, ∃ W : Opens (TopCat.of E.domain.carrier), x ∈ W ∧
      ∀ y (hy : y ∈ W), Function.Bijective ((Surfaces.continuousLiftPresheaf
        (B.symm ∘ Surfaces.mobiusDomainProjection E.domain) (Surfaces.mobiusDomainProjection D.domain)).germ W y hy) := by
    intro x
    obtain ⟨W, hx, _, hW⟩ := actual_quotient_lift_neighborhoods E D B.symm hBi hDi x
    exact ⟨W, hx, hW⟩
  obtain ⟨F, hFa, hF, hFnear⟩ := Surfaces.continuous_lift_exists_preserving_germ
    (B ∘ Surfaces.mobiusDomainProjection D.domain) (Surfaces.mobiusDomainProjection E.domain) hExt U a haL s
  obtain ⟨G, hGb, hG, hGnear⟩ := Surfaces.continuous_lift_exists_preserving_germ
    (B.symm ∘ Surfaces.mobiusDomainProjection E.domain) (Surfaces.mobiusDomainProjection D.domain) hExti V b hbL t
  have hFa' : F a = b := hFa.trans hLa
  have hGb' : G b = a := by
    calc
      G b = L.symm b := hGb
      _ = L.symm (L a) := congrArg L.symm hLa.symm
      _ = a := L.left_inv haL
  have hGF : (fun z => G (F z)) =ᶠ[𝓝 a] id := by
    have hGp : ∀ᶠ z in 𝓝 a, ∃ hv : F z ∈ V, G (F z) = L.symm (F z) := by
      have ht : Tendsto F (𝓝 a) (𝓝 b) := by
        have ht := F.continuous.continuousAt (x := a)
        change Tendsto F (𝓝 a) (𝓝 (F a)) at ht
        rw [hFa'] at ht
        exact ht
      exact ht.eventually hGnear
    filter_upwards [hFnear, hGp] with z hz hgz
    obtain ⟨hzU, hFz⟩ := hz
    obtain ⟨_, hGz⟩ := hgz
    change G (F z) = z
    rw [hGz, hFz]
    exact L.left_inv hzU
  have hFG : (fun z => F (G z)) =ᶠ[𝓝 b] id := by
    have hFp : ∀ᶠ z in 𝓝 b, ∃ hu : G z ∈ U, F (G z) = L (G z) := by
      have ht : Tendsto G (𝓝 b) (𝓝 a) := by
        have ht := G.continuous.continuousAt (x := b)
        change Tendsto G (𝓝 b) (𝓝 (G b)) at ht
        rw [hGb'] at ht
        exact ht
      exact ht.eventually hFnear
    filter_upwards [hGnear, hFp] with z hz hfz
    obtain ⟨hzV, hGz⟩ := hz
    obtain ⟨_, hFz⟩ := hfz
    change F (G z) = z
    rw [hFz, hGz]
    exact L.right_inv hzV
  have hGFall : G.comp F = ContinuousMap.id D.domain.carrier :=
    original_quotient_lifts_eq_of_eventuallyEq D (G.comp F) (ContinuousMap.id _) (by
      intro z
      change Surfaces.mobiusDomainProjection D.domain (G (F z)) = _
      calc
        Surfaces.mobiusDomainProjection D.domain (G (F z)) =
            B.symm (Surfaces.mobiusDomainProjection E.domain (F z)) := hG (F z)
        _ = B.symm (B (Surfaces.mobiusDomainProjection D.domain z)) := congrArg B.symm (hF z)
        _ = _ := B.symm_apply_apply _) (fun _ => rfl) a hGF
  have hFGall : F.comp G = ContinuousMap.id E.domain.carrier :=
    original_quotient_lifts_eq_of_eventuallyEq E (F.comp G) (ContinuousMap.id _) (by
      intro z
      change Surfaces.mobiusDomainProjection E.domain (F (G z)) = _
      calc
        Surfaces.mobiusDomainProjection E.domain (F (G z)) =
            B (Surfaces.mobiusDomainProjection D.domain (G z)) := hF (G z)
        _ = B (B.symm (Surfaces.mobiusDomainProjection E.domain z)) := congrArg B (hG z)
        _ = _ := B.apply_symm_apply _) (fun _ => rfl) b hFG
  let e : D.domain.carrier ≃ₜ E.domain.carrier :=
    { toFun := F
      invFun := G
      left_inv := fun z => congrFun (congrArg DFunLike.coe hGFall) z
      right_inv := fun z => congrFun (congrArg DFunLike.coe hFGall) z
      continuous_toFun := F.continuous
      continuous_invFun := G.continuous }
  exact ⟨e, hF⟩


open scoped OnePoint

/-- The physical homeomorphism obtained by continuation is analytic in
both original atlases, with the actual quotient diagram commuting. -/
theorem actual_quotient_exists_analytic_physical_homeomorph
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (B : Surfaces.MobiusDomainQuotient D.domain ≃ₜ Surfaces.MobiusDomainQuotient E.domain)
    (hB : Surfaces.RiemannAnalyticMap
      (Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas
      (Surfaces.mobiusQuotientRiemannSurface E.domain E.discontinuous).toRiemannAtlas B)
    (hDegree : ∀ (z : D.domain.carrier) (w : E.domain.carrier),
      B (Surfaces.mobiusDomainProjection D.domain z) = Surfaces.mobiusDomainProjection E.domain w →
        Nat.card (DiscreteGroups.mobiusBoundaryStabilizer H z.val) = Nat.card (DiscreteGroups.mobiusBoundaryStabilizer K
          w.val)) :
    ∃ F : D.domain.carrier ≃ₜ E.domain.carrier,
      Surfaces.RiemannAnalyticMap (Surfaces.mobiusDomainRiemannSurface D.domain).toRiemannAtlas
        (Surfaces.mobiusDomainRiemannSurface E.domain).toRiemannAtlas F ∧
      Surfaces.RiemannAnalyticMap (Surfaces.mobiusDomainRiemannSurface E.domain).toRiemannAtlas
        (Surfaces.mobiusDomainRiemannSurface D.domain).toRiemannAtlas F.symm ∧
      ∀ z, Surfaces.mobiusDomainProjection E.domain (F z) = B (Surfaces.mobiusDomainProjection D.domain z) := by
  obtain ⟨F, hF⟩ := actual_quotient_exists_physical_homeomorph D E B hB hDegree
  have hFa : Surfaces.RiemannAnalyticMap (Surfaces.mobiusDomainRiemannSurface D.domain).toRiemannAtlas
      (Surfaces.mobiusDomainRiemannSurface E.domain).toRiemannAtlas F := by
    apply Surfaces.RiemannAnalyticMap.of_comp_mobiusProjection
      (Surfaces.mobiusDomainRiemannSurface D.domain).toRiemannAtlas E.domain E.discontinuous F F.continuous
    have he : Surfaces.mobiusDomainProjection E.domain ∘ F = B ∘ Surfaces.mobiusDomainProjection D.domain := funext hF
    rw [he]
    exact hB.comp (Surfaces.mobiusDomainProjection_analytic D.domain D.discontinuous)
  exact ⟨F, hFa, Surfaces.riemannAnalyticMap_homeomorph_symm F hFa, hF⟩

/-- An actual invariant disc has uncountably many physical points. -/
theorem fuchsianDisc_domain_uncountable
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) : Uncountable D.domain.carrier := by
  obtain ⟨q, hq⟩ := D.isDisc.normalize
  let e := (fuchsianDiscUnitHomeomorph D q hq).trans Surfaces.discFiniteHomeomorph
  let : Uncountable ℂ := Complex.ofReal_injective.uncountable
  let b := (Homeomorph.unitBall : ℂ ≃ₜ Metric.ball (0 : ℂ) 1)
  exact (e.symm.injective.comp b.injective).uncountable

/-- Pointwise membership in actual original group orbits forces a Mobius
map to be one original group element. Elliptic stabilizers are allowed:
countably many nonidentical Mobius maps cannot agree pointwise with one
map on the uncountable original disc. -/
theorem mobius_mem_of_pointwise_original_orbits
    {H : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (M : Mobius.complexMobiusGroup)
    (hOrbit : ∀ z : D.domain.carrier, ∃ g : H, M.val z.val = g.val.val z.val) : M ∈ H := by
  classical
  let := Mobius.discreteMobius_countable H D.discrete
  let := fuchsianDisc_domain_uncountable D
  by_contra hM
  have hc (g : H) : {z : D.domain.carrier | M.val z.val = g.val.val z.val}.Countable := by
    have hn : g.val⁻¹ * M ≠ 1 := by
      intro he
      apply hM
      have hEq : M = g.val := by
        calc
          M = g.val * (g.val⁻¹ * M) := by group
          _ = g.val := by rw [he, mul_one]
      exact hEq ▸ g.property
    apply ((Fuchsian.mobius_boundary_fixed_finite (g.val⁻¹ * M) hn).countable.preimage
      (Subtype.val_injective : Function.Injective (Subtype.val : D.domain.carrier → Mobius.ExtendedComplex))).mono
    intro z hz
    change g.val.val.symm (M.val z.val) = z.val
    rw [hz, Equiv.symm_apply_apply]
  have hu : (⋃ g : H, {z : D.domain.carrier | M.val z.val = g.val.val z.val}) = univ := by
    apply eq_univ_of_forall
    intro z
    obtain ⟨g, hg⟩ := hOrbit z
    exact mem_iUnion.mpr ⟨g, hg⟩
  exact Set.not_countable_univ (hu ▸ Set.countable_iUnion hc)

/-- The original whole-group membership test holds with elliptic points. -/
theorem mobius_mem_of_original_quotient_action_with_elliptics
    {H : Subgroup Mobius.complexMobiusGroup} (D : FuchsianDisc H)
    (M : Mobius.complexMobiusGroup) (f : D.domain.carrier → D.domain.carrier)
    (hM : ∀ z, M.val z.val = (f z).val)
    (hproj : ∀ z, Surfaces.mobiusDomainProjection D.domain (f z) = Surfaces.mobiusDomainProjection D.domain z) : M ∈ H := by
  apply mobius_mem_of_pointwise_original_orbits D M
  intro z
  obtain ⟨g, hg⟩ := Quotient.exact (hproj z)
  change g • z = f z at hg
  exact ⟨g, (hM z).trans (congrArg Subtype.val hg).symm⟩



theorem original_quotient_mobius_conjugate_mem_with_elliptics
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (e : D.domain.carrier ≃ₜ E.domain.carrier)
    (B : Surfaces.MobiusDomainQuotient D.domain ≃ₜ Surfaces.MobiusDomainQuotient E.domain)
    (M : Mobius.complexMobiusGroup)
    (hM : ∀ z : D.domain.carrier, M.val z.val = (e z).val)
    (hcomm : ∀ z, Surfaces.mobiusDomainProjection E.domain (e z) = B (Surfaces.mobiusDomainProjection D.domain z))
    (g : H) : M * g.val * M⁻¹ ∈ K := by
  have hMi (z : E.domain.carrier) : M.val.symm z.val = (e.symm z).val := by
    apply M.val.injective
    rw [Equiv.apply_symm_apply, hM, e.apply_symm_apply]
  let f : E.domain.carrier → E.domain.carrier := fun z => e (g • e.symm z)
  apply mobius_mem_of_original_quotient_action_with_elliptics E (M * g.val * M⁻¹) f
  · intro z
    change M.val (g.val.val (M.val.symm z.val)) = (e (g • e.symm z)).val
    rw [hMi]
    exact hM (g • e.symm z)
  · intro z
    change Surfaces.mobiusDomainProjection E.domain (e (g • e.symm z)) = Surfaces.mobiusDomainProjection E.domain z
    rw [hcomm, Surfaces.mobiusDomainProjection_smul, ← hcomm, e.apply_symm_apply]

/-- A physical Mobius equivalence over the actual branched quotients
conjugates the entire original groups, not merely a selected generating pair. -/
theorem original_quotient_mobius_group_conjugacy_with_elliptics
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (e : D.domain.carrier ≃ₜ E.domain.carrier)
    (B : Surfaces.MobiusDomainQuotient D.domain ≃ₜ Surfaces.MobiusDomainQuotient E.domain)
    (M : Mobius.complexMobiusGroup)
    (hM : ∀ z : D.domain.carrier, M.val z.val = (e z).val)
    (hcomm : ∀ z, Surfaces.mobiusDomainProjection E.domain (e z) = B (Surfaces.mobiusDomainProjection D.domain z)) :
    DiscreteGroups.Action.Actions.subgroupConjugate M H = K := by
  have hMi (z : E.domain.carrier) : (M⁻¹).val z.val = (e.symm z).val := by
    apply M.val.injective
    change M.val (M.val.symm z.val) = M.val (e.symm z).val
    rw [Equiv.apply_symm_apply, hM, e.apply_symm_apply]
  have hback (z : E.domain.carrier) :
      Surfaces.mobiusDomainProjection D.domain (e.symm z) = B.symm (Surfaces.mobiusDomainProjection E.domain z) := by
    apply B.injective
    rw [B.apply_symm_apply, ← hcomm, e.apply_symm_apply]
  apply le_antisymm
  · intro f hf
    obtain ⟨g, hg, rfl⟩ := (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff M H f).mp hf
    exact original_quotient_mobius_conjugate_mem_with_elliptics D E e B M hM hcomm ⟨g, hg⟩
  · intro f hf
    have hin := original_quotient_mobius_conjugate_mem_with_elliptics E D e.symm B.symm M⁻¹ hMi hback ⟨f, hf⟩
    exact (DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff M H f).mpr
      ⟨M⁻¹ * f * M, by simpa only [inv_inv] using hin, by group⟩



open scoped OnePoint

/-- An analytic equivalence of the genuine quotients preserving actual
full stabilizer orders identifies the entire original Mobius groups and
their whole invariant discs, including elliptic points. -/
theorem actual_order_preserving_quotient_equivalence_mobius_conjugate
    {H K : Subgroup Mobius.complexMobiusGroup}
    (D : FuchsianDisc H)
    (E : FuchsianDisc K)
    (B : Surfaces.MobiusDomainQuotient D.domain ≃ₜ Surfaces.MobiusDomainQuotient E.domain)
    (hB : Surfaces.RiemannAnalyticMap
      (Surfaces.mobiusQuotientRiemannSurface D.domain D.discontinuous).toRiemannAtlas
      (Surfaces.mobiusQuotientRiemannSurface E.domain E.discontinuous).toRiemannAtlas B)
    (hDegree : ∀ (z : D.domain.carrier) (w : E.domain.carrier),
      B (Surfaces.mobiusDomainProjection D.domain z) = Surfaces.mobiusDomainProjection E.domain w →
        Nat.card (DiscreteGroups.mobiusBoundaryStabilizer H z.val) = Nat.card (DiscreteGroups.mobiusBoundaryStabilizer K
          w.val)) :
    ∃ M : Mobius.complexMobiusGroup, DiscreteGroups.Action.Actions.subgroupConjugate M H = K ∧ M.val '' D.carrier = E.carrier := by
  obtain ⟨F, hFa, _, hF⟩ := actual_quotient_exists_analytic_physical_homeomorph D E B hB hDegree
  obtain ⟨M, hWhole, hM⟩ := analytic_fuchsianDisc_homeomorph_exists_mobius D E F hFa
  exact ⟨M, original_quotient_mobius_group_conjugacy_with_elliptics D E F B M hM hF, hWhole⟩

end LowDimensionalTopology.Geometry.Fuchsian
