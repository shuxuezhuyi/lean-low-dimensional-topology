/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.TriangleGroup.TriangleSupergroups
public import LowDimensionalTopology.Geometry.Fuchsian.Covolume.CompactSignatureFiniteGeneration
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory Topology
open scoped OnePoint Pointwise ENNReal
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Algebra LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.Auxiliary.Topology LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Hyperbolic LowDimensionalTopology.Geometry.Mobius
  LowDimensionalTopology.Geometry.Polygon LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.DiscreteGroups LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Fuchsian LowDimensionalTopology.Geometry.Hyperbolic.QuaternionHalfSpace

local instance ellipticTriangleSignatureSphereMeasurable : MeasurableSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex :=
  borel _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex
local instance ellipticTriangleSignatureSphereBorel : BorelSpace _root_.LowDimensionalTopology.Geometry.Mobius.ExtendedComplex := ⟨rfl⟩

/-- The exact order of an actual elliptic element divides an actual listed cone order. -/
theorem elliptic_order_dvd_signature_entry {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (f : H) (hf : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic f.val)
    {g p : ℕ} {orders : List ℕ} (hSig : HasCofiniteFuchsianSignature D g orders p) :
    ∃ c ∈ orders, orderOf f ∣ c := by
  obtain ⟨x, hx, _⟩ := elliptic_disc_existsUnique_fixed f.val hf D.isDisc (D.image_eq f)
  let M : fuchsianMaximalCyclicSubgroups H .elliptic :=
    ⟨_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mobiusBoundaryStabilizer H x.val,
      elliptic_stabilizer_isMaximalCyclic D f.val f.property hf x hx,
      f.val, (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H x.val
        f.val).mpr ⟨f.property, hx⟩, hf⟩
  let : Finite M.val := fuchsianMaximalElliptic_finite D M
  have hmem : f.val ∈ M.val :=
    (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.mem_mobiusBoundaryStabilizer H x.val f.val).mpr ⟨f.property,
      hx⟩
  have hdiv := orderOf_dvd_natCard (⟨f.val, hmem⟩ : M.val)
  have ho : orderOf (⟨f.val, hmem⟩ : M.val) = orderOf f :=
    (orderOf_injective M.val.subtype Subtype.val_injective _).symm.trans
      (orderOf_injective H.subtype Subtype.val_injective f)
  rw [ho] at hdiv
  exact ⟨fuchsianEllipticClassOrder D (Quotient.mk _ M),
    hSig.mem_orders.mpr ⟨Quotient.mk _ M, rfl⟩, hdiv⟩

/-- The actual area/index formula for two original genus-zero signatures, with finite index derived. -/
theorem cofinite_triangle_subgroup_deficit_index {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH : K ≤ H)
    (hTK : IsMobiusTriangleGroup K) {orders₀ orders₁ : List ℕ} {p₀ p₁ : ℕ}
    (hSig₀ : HasCofiniteFuchsianSignature (fuchsianDiscRestrict D K hKH) 0 orders₀ p₀)
    (hSig₁ : HasCofiniteFuchsianSignature D 0 orders₁ p₁) :
    ∃ k : ℕ, 0 < k ∧ (K ≠ H → 2 ≤ k) ∧
      -2 + (p₀ : ℝ) + (orders₀.map (fun m : ℕ => 1 - 1 / (m : ℝ))).sum =
        (k : ℝ) * (-2 + (p₁ : ℝ) + (orders₁.map (fun m : ℕ => 1 - 1 / (m : ℝ))).sum) := by
  let q := geometricDiscNormalizer D
  let P := geometricDiscData D
  let K' := _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.subgroupConjugate q K
  have hK'H : K' ≤ geometricDiscGroup D := by
    intro f hf
    obtain ⟨k, hk, rfl⟩ := (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q K f).mp hf
    exact (_root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.Actions.mem_subgroupConjugate_iff q H _).mpr ⟨k,
      hKH hk, rfl⟩
  let Q := unitDiscSubgroupData P K' hK'H
  have hSig₀' : HasCofiniteFuchsianSignature Q.asFuchsianDisc 0 orders₀ p₀ := by
    apply cofinite_signature_of_conjugate_group (fuchsianDiscRestrict D K hKH)
      Q.asFuchsianDisc q rfl _ 0 p₀ orders₀ hSig₀
    exact geometricDiscNormalizer_image D
  have hSig₁' : HasCofiniteFuchsianSignature P.asFuchsianDisc 0 orders₁ p₁ := by
    rw [geometricDiscData_asFuchsianDisc]
    exact cofinite_signature_global_conjugation D q 0 p₁ orders₁ hSig₁
  obtain ⟨w₀, hw₀, _⟩ := exists_actual_dirichlet_horocycle_good_center Q
  obtain ⟨w₁, hw₁, _⟩ := exists_actual_dirichlet_horocycle_good_center P
  let D₀ := dirichletDomain Q w₀
  let D₁ := dirichletDomain P w₁
  have hD₀ := dirichletDomain_fundamental Q w₀ hw₀
  have hD₁ := dirichletDomain_fundamental P w₁ hw₁
  have ha₀ := firstKind_finitelyGenerated_area_ne_top Q
    (mobiusTriangleGroup_actual_firstKind Q.asFuchsianDisc (hTK.conjugation q))
    hSig₀'.finitelyGenerated hD₀
  obtain ⟨hidx, hAidx, ha₁⟩ :=
    fuchsian_subgroup_fundamentalDomain_index_area P K' hK'H D₀ D₁ hD₀ hD₁ ha₀
  let : (K'.subgroupOf (geometricDiscGroup D)).FiniteIndex := hidx
  have hD₀' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain K' (fuchsianGeometricDomain Q.asFuchsianDisc).carrier
      (geometricModelArea Q.asFuchsianDisc) D₀ := by
    rw [geometricModelArea_asUnitDisc]
    exact hD₀
  have hD₁' : _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain (geometricDiscGroup D)
      (fuchsianGeometricDomain P.asFuchsianDisc).carrier
      (geometricModelArea P.asFuchsianDisc) D₁ := by
    rw [geometricModelArea_asUnitDisc]
    exact hD₁
  have ha₀' : geometricModelArea Q.asFuchsianDisc D₀ ≠ ⊤ := by
    rwa [geometricModelArea_asUnitDisc]
  have ha₁' : geometricModelArea P.asFuchsianDisc D₁ ≠ ⊤ := by
    rwa [geometricModelArea_asUnitDisc]
  have hA₀ := cofinite_signature_area_of_genus_le_one Q.asFuchsianDisc D₀ hD₀' ha₀'
    0 p₀ orders₀ hSig₀' (by decide)
  have hA₁ := cofinite_signature_area_of_genus_le_one P.asFuchsianDisc D₁ hD₁' ha₁'
    0 p₁ orders₁ hSig₁' (by decide)
  rw [geometricModelArea_asUnitDisc] at hA₀ hA₁
  have hR := congrArg ENNReal.toReal hAidx
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast] at hR
  change (Q.area D₀).toReal =
    ((K'.subgroupOf (geometricDiscGroup D)).index : ℝ) * (P.area D₁).toReal at hR
  have hR' := hA₀.symm.trans (hR.trans (congrArg
    (fun a : ℝ => ((K'.subgroupOf (geometricDiscGroup D)).index : ℝ) * a) hA₁))
  norm_num only [Nat.cast_zero, mul_zero, zero_sub] at hR'
  refine ⟨(K'.subgroupOf (geometricDiscGroup D)).index,
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, ?_, ?_⟩
  · intro hne
    have hne' : K' ≠ geometricDiscGroup D := by
      intro he
      apply hne
      apply Subgroup.map_injective (f := (MulAut.conj q).toMonoidHom) (MulAut.conj q).injective
      exact he
    have hproper : K'.subgroupOf (geometricDiscGroup D) ≠ ⊤ :=
      fun he => hne' (le_antisymm hK'H (Subgroup.subgroupOf_eq_top.mp he))
    exact (K'.subgroupOf (geometricDiscGroup D)).one_lt_index_of_ne_top hproper
  · apply mul_left_cancel₀ (show 2 * Real.pi ≠ 0 by positivity)
    linear_combination hR'

/-- The two remaining genuine cone orders obey the finite source list. -/
theorem elliptic_signature_reciprocal_pair (a b : ℕ) (ha : 2 ≤ a) (hab : a ≤ b)
    (hsum : (1 / 2 : ℝ) < 1 / (a : ℝ) + 1 / (b : ℝ)) :
    a = 2 ∨ a = 3 ∧ (b = 3 ∨ b = 4 ∨ b = 5) := by
  have ha3 : a ≤ 3 := by
    by_contra h
    have h4a : 4 ≤ a := by omega
    have h1 := signature_reciprocal_le 4 a (by decide) h4a
    have h2 := signature_reciprocal_le 4 b (by decide) (h4a.trans hab)
    norm_num at h1 h2
    simp only [one_div] at hsum h1 h2
    linarith
  by_cases he : a = 2
  · exact Or.inl he
  · have haeq : a = 3 := by omega
    right
    refine ⟨haeq, ?_⟩
    have hb5 : b ≤ 5 := by
      by_contra h
      have h6b : 6 ≤ b := by omega
      have hrec := signature_reciprocal_le 6 b (by decide) h6b
      rw [haeq] at hsum
      norm_num at hrec hsum
      linarith
    omega

/-- A genuine three-marked profile below the exact elliptic budget has no cusp and
has precisely the source's two small companion cone orders. -/
theorem elliptic_triangle_signature_numeric (orders : List ℕ) (p n c : ℕ)
    (hn : 3 ≤ n) (htwo : ∀ m ∈ orders, 2 ≤ m)
    (hthree : orders.length + p = 3) (hc : c ∈ orders) (hdiv : n ∣ c)
    (hbudget : -2 + (p : ℝ) + (orders.map (fun m : ℕ => 1 - 1 / (m : ℝ))).sum <
      1 / 2 - 1 / (n : ℝ)) :
    ∃ a b : ℕ, 2 ≤ a ∧ a ≤ b ∧ orders.Perm [a, b, c] ∧ p = 0 ∧
      (a = 2 ∨ a = 3 ∧ (b = 3 ∨ b = 4 ∨ b = 5)) := by
  have hc2 := htwo c hc
  have hnc : n ≤ c := Nat.le_of_dvd (by omega) hdiv
  have hrec := signature_reciprocal_le n c (by omega) hnc
  have hperm : orders.Perm (c :: orders.erase c) := List.perm_cons_erase hc
  have hlen : (orders.erase c).length + p = 2 := by
    have he := hperm.length_eq
    simp only [List.length_cons] at he
    omega
  have htailtwo : ∀ m ∈ orders.erase c, 2 ≤ m :=
    fun m hm => htwo m (List.mem_of_mem_erase hm)
  have hsum := signature_elliptic_sum_perm hperm
  rw [hsum] at hbudget
  simp only [List.map_cons, List.sum_cons] at hbudget
  cases ht : orders.erase c with
  | nil =>
    have hp : p = 2 := by simp only [ht, List.length_nil] at hlen; omega
    simp only [ht, hp, List.map_nil, List.sum_nil, Nat.cast_ofNat] at hbudget
    linarith
  | cons a tail =>
    have ha : 2 ≤ a := htailtwo a (by simp [ht])
    cases hu : tail with
    | nil =>
      have hp : p = 1 := by simp only [ht, hu, List.length_cons, List.length_nil] at hlen; omega
      have hrecA := signature_reciprocal_le 2 a (by decide) ha
      simp only [ht, hu, hp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.cast_one] at hbudget
      norm_num at hrecA
      simp only [one_div] at hbudget hrec hrecA
      linarith
    | cons b rest =>
      have hp : p = 0 := by
        simp only [ht, hu, List.length_cons] at hlen
        omega
      have hrest : rest = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [ht, hu, List.length_cons] at hlen
        omega
      have hb : 2 ≤ b := htailtwo b (by simp [ht, hu])
      simp only [ht, hu, hrest, hp, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, Nat.cast_zero] at hbudget
      have hsumAB : (1 / 2 : ℝ) < 1 / (a : ℝ) + 1 / (b : ℝ) := by linarith
      rw [ht, hu, hrest] at hperm
      have hcycle : [c, a, b].Perm [a, b, c] := by
        simpa using (List.perm_append_comm : ([c] ++ [a, b]).Perm ([a, b] ++ [c]))
      have hfinal := hperm.trans hcycle
      by_cases hab : a ≤ b
      · exact ⟨a, b, ha, hab, hfinal, hp, elliptic_signature_reciprocal_pair a b ha hab hsumAB⟩
      · have hba : b ≤ a := by omega
        have hswap : [a, b, c].Perm [b, a, c] := by
          have habp : [a, b].Perm [b, a] := by
            simpa using (List.perm_append_comm : ([a] ++ [b]).Perm ([b] ++ [a]))
          exact habp.append_right [c]
        exact ⟨b, a, hb, hba, hfinal.trans hswap, hp,
          elliptic_signature_reciprocal_pair b a hb hba (by linarith)⟩

/--
The triangle-subgroup alternatives constrain the ambient signature. The
given elliptic element's order divides the third cone order; the other two
orders are sorted and satisfy the displayed finite list of alternatives.
-/
theorem elliptic_triangle_signature_profile {H : Subgroup
  _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup}
    (D : FuchsianDisc H) (g : H) (hg : _root_.LowDimensionalTopology.Geometry.Mobius.MobiusElliptic g.val)
    (n r : ℕ) (hn : 3 ≤ n) (hr : 2 ≤ r) (horder : orderOf g = n)
    (K : Subgroup _root_.LowDimensionalTopology.Geometry.Mobius.complexMobiusGroup) (hKH : K ≤ H) (hTK :
      IsMobiusTriangleGroup K)
    (halt : (HasCofiniteFuchsianSignature (fuchsianDiscRestrict D K hKH) 0 [n, r, n] 0 ∧ K ≠ H) ∨
      HasCofiniteFuchsianSignature (fuchsianDiscRestrict D K hKH) 0 [n, r, 2] 0) :
    ∃ a b c : ℕ, 2 ≤ a ∧ a ≤ b ∧ 2 ≤ c ∧ n ∣ c ∧
      HasCofiniteFuchsianSignature D 0 [a, b, c] 0 ∧
      (a = 2 ∨ a = 3 ∧ (b = 3 ∨ b = 4 ∨ b = 5)) := by
  have hTH := fuchsian_supergroup_of_triangleGroup_is_triangleGroup D K hKH hTK
  obtain ⟨orders, p, hSig, hthree⟩ := mobiusTriangleGroup_actual_three_marked_signature D hTH
  obtain ⟨c, hc, hcdiv⟩ := elliptic_order_dvd_signature_entry D g hg hSig
  rw [horder] at hcdiv
  have hpos := firstKind_finitelyGenerated_genus_zero_signature_deficit_pos D hSig.finitelyGenerated
    (mobiusTriangleGroup_actual_firstKind D hTH) orders p hSig
  have hrpos : (0 : ℝ) < 1 / (r : ℝ) := one_div_pos.mpr (by exact_mod_cast (show 0 < r by omega))
  have hbudget : -2 + (p : ℝ) + (orders.map (fun m : ℕ => 1 - 1 / (m : ℝ))).sum <
      1 / 2 - 1 / (n : ℝ) := by
    rcases halt with ⟨hK, hproper⟩ | hK
    · obtain ⟨k, _hkpos, hkproper, hA⟩ :=
        cofinite_triangle_subgroup_deficit_index D K hKH hTK hK hSig
      have hk : (2 : ℝ) ≤ k := by exact_mod_cast hkproper hproper
      have hm := mul_le_mul_of_nonneg_right hk hpos.le
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.cast_zero, add_zero] at hA
      linarith
    · obtain ⟨k, hkpos, _hkproper, hA⟩ :=
        cofinite_triangle_subgroup_deficit_index D K hKH hTK hK hSig
      have hk : (1 : ℝ) ≤ k := by exact_mod_cast hkpos
      have hm := mul_le_mul_of_nonneg_right hk hpos.le
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Nat.cast_zero, Nat.cast_ofNat, add_zero] at hA
      linarith
  obtain ⟨a, b, ha, hab, hperm, hp, hcase⟩ := elliptic_triangle_signature_numeric orders p n c hn
    (fun m hm => hSig.orders_two_le hm) hthree hc hcdiv hbudget
  refine ⟨a, b, c, ha, hab, hSig.orders_two_le hc, hcdiv, ?_, hcase⟩
  simpa only [hp] using hSig.perm_orders hperm.symm

end LowDimensionalTopology.Geometry.Fuchsian
