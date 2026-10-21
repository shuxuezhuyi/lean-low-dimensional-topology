/- Released under Apache 2.0 license as described in the file LICENSE. -/
module
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.CofinitePolygonLowerSharpness
public import LowDimensionalTopology.Geometry.Fuchsian.Signature.Realization.GeneralSignatureCorePolygon
@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
open Set
open scoped UpperHalfPlane
namespace LowDimensionalTopology.Geometry.Fuchsian
open LowDimensionalTopology.Geometry.Auxiliary.Topology
  LowDimensionalTopology.Geometry.DiscreteGroups
  LowDimensionalTopology.Geometry.Euclidean
  LowDimensionalTopology.Geometry.Fuchsian
  LowDimensionalTopology.Geometry.Hyperbolic
  LowDimensionalTopology.Geometry.Polygon
  LowDimensionalTopology.Geometry.Surfaces
  LowDimensionalTopology.Geometry.Auxiliary.Algebra
  LowDimensionalTopology.Geometry.Auxiliary.Analysis
  LowDimensionalTopology.Geometry.DiscreteGroups.Action
  LowDimensionalTopology.Geometry.Mobius

/-- In a true boundary triple the two real sides are paired and the cut is
self-paired only in the auxiliary cofinite group. The target subgroup omits it. -/
def generalSignatureAuxBoundaryPairNat (i : ℕ) : ℕ :=
  if i % 3 = 0 then i + 2 else if i % 3 = 1 then i else i - 2

theorem generalSignatureAuxBoundaryPairNat_involutive :
    Function.Involutive generalSignatureAuxBoundaryPairNat := by
  intro i
  simp only [generalSignatureAuxBoundaryPairNat]
  split_ifs <;> omega

theorem generalSignatureAuxBoundaryPairNat_bound (t i : ℕ) (hi : i < 3 * t) :
    generalSignatureAuxBoundaryPairNat i < 3 * t := by
  unfold generalSignatureAuxBoundaryPairNat
  split_ifs <;> omega

theorem generalSignatureAuxBoundaryPairNat_fixed_iff (i : ℕ) :
    generalSignatureAuxBoundaryPairNat i = i ↔ i % 3 = 1 := by
  unfold generalSignatureAuxBoundaryPairNat
  split_ifs <;> omega

theorem generalSignatureAuxBoundaryPairNat_zero (j : ℕ) :
    generalSignatureAuxBoundaryPairNat (3 * j) = 3 * j + 2 := by
  simp [generalSignatureAuxBoundaryPairNat]

theorem generalSignatureAuxBoundaryPairNat_one (j : ℕ) :
    generalSignatureAuxBoundaryPairNat (3 * j + 1) = 3 * j + 1 := by
  simp [generalSignatureAuxBoundaryPairNat]

theorem generalSignatureAuxBoundaryPairNat_two (j : ℕ) :
    generalSignatureAuxBoundaryPairNat (3 * j + 2) = 3 * j := by
  simp [generalSignatureAuxBoundaryPairNat]

/-- The actual ordered core angle list, with the ordinary-cycle angle left
explicit for the combinatorial pairing proof. Zero entries of ms remain cusps. -/
def generalSignatureAuxAngleList (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ) : List ℝ :=
  cofiniteConstructionSideAngles β g ms ++
    (List.replicate t [β, Real.pi / 2, Real.pi / 2]).flatten

/-- The original handle and cone/cusp pairing is extended by literal boundary triples. -/
def generalSignatureAuxPairNat (β : ℝ) (g : ℕ) (ms : List ℕ) (i : ℕ) : ℕ :=
  let p := (cofiniteConstructionSideAngles β g ms).length
  if i < p then cofiniteConstructionPairNat g ms i
  else p + generalSignatureAuxBoundaryPairNat (i - p)

theorem generalSignatureAuxPairNat_involutive (β : ℝ) (g : ℕ) (ms : List ℕ) :
    Function.Involutive (generalSignatureAuxPairNat β g ms) := by
  intro i
  let p := (cofiniteConstructionSideAngles β g ms).length
  by_cases hi : i < p
  · have hj : cofiniteConstructionPairNat g ms i < p :=
      cofiniteConstructionPairNat_bound β g ms i hi
    have hfi : generalSignatureAuxPairNat β g ms i = cofiniteConstructionPairNat g ms i := by
      change (if i < p then _ else _) = _
      rw [ite_eq_left hi]
    rw [hfi]
    change (if cofiniteConstructionPairNat g ms i < p then _ else _) = i
    rw [ite_eq_left hj]
    exact cofiniteConstructionPairNat_involutive g ms i
  · have hj : ¬ p + generalSignatureAuxBoundaryPairNat (i - p) < p := by omega
    have hfi : generalSignatureAuxPairNat β g ms i =
        p + generalSignatureAuxBoundaryPairNat (i - p) := by
      change (if i < p then _ else _) = _
      rw [ite_eq_right hi]
    rw [hfi]
    change (if p + generalSignatureAuxBoundaryPairNat (i - p) < p then _ else _) = i
    rw [ite_eq_right hj]
    change p + generalSignatureAuxBoundaryPairNat
      (p + generalSignatureAuxBoundaryPairNat (i - p) - p) = i
    rw [Nat.add_sub_cancel_left, generalSignatureAuxBoundaryPairNat_involutive (i - p)]
    exact Nat.add_sub_of_le (by omega : p ≤ i)

theorem generalSignatureAuxAngleList_length (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ) :
    (generalSignatureAuxAngleList β g ms t).length =
      (cofiniteConstructionSideAngles β g ms).length + 3 * t := by
  simp [generalSignatureAuxAngleList, List.length_flatten, List.sum_replicate, Nat.mul_comm]

theorem generalSignatureAuxPairNat_bound (β : ℝ) (g : ℕ) (ms : List ℕ) (t i : ℕ)
    (hi : i < (generalSignatureAuxAngleList β g ms t).length) :
    generalSignatureAuxPairNat β g ms i < (generalSignatureAuxAngleList β g ms t).length := by
  rw [generalSignatureAuxAngleList_length] at hi ⊢
  let p := (cofiniteConstructionSideAngles β g ms).length
  change (if i < p then cofiniteConstructionPairNat g ms i
    else p + generalSignatureAuxBoundaryPairNat (i - p)) < p + 3 * t
  by_cases hip : i < p
  · have h := cofiniteConstructionPairNat_bound β g ms i hip
    rw [ite_eq_left hip]
    change cofiniteConstructionPairNat g ms i < p + 3 * t
    omega
  · have hit : i - p < 3 * t := by omega
    have h := generalSignatureAuxBoundaryPairNat_bound t (i - p) hit
    rw [ite_eq_right hip]
    omega

/-- The auxiliary involution acts on the actual finite ordered sides. -/
def generalSignatureAuxPairing (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ) :
    Equiv.Perm (Fin (generalSignatureAuxAngleList β g ms t).length) :=
  let f : Fin (generalSignatureAuxAngleList β g ms t).length →
      Fin (generalSignatureAuxAngleList β g ms t).length := fun i =>
    ⟨generalSignatureAuxPairNat β g ms i.val,
      generalSignatureAuxPairNat_bound β g ms t i.val i.isLt⟩
  { toFun := f
    invFun := f
    left_inv := fun i => Fin.ext (generalSignatureAuxPairNat_involutive β g ms i.val)
    right_inv := fun i => Fin.ext (generalSignatureAuxPairNat_involutive β g ms i.val) }

theorem generalSignatureAuxPairing_val (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ)
    (i : Fin (generalSignatureAuxAngleList β g ms t).length) :
    (generalSignatureAuxPairing β g ms t i).val = generalSignatureAuxPairNat β g ms i.val := rfl

theorem generalSignatureAuxPairing_involutive (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ) :
    Function.Involutive (generalSignatureAuxPairing β g ms t) := by
  intro i
  apply Fin.ext
  exact generalSignatureAuxPairNat_involutive β g ms i.val

theorem generalSignatureAuxBoundaryAngles_getD (β : ℝ) (t i : ℕ) :
    ((List.replicate t [β, Real.pi / 2, Real.pi / 2]).flatten).getD i β =
      if i < 3 * t ∧ i % 3 ≠ 0 then Real.pi / 2 else β := by
  induction t generalizing i with
  | zero => simp
  | succ t ih =>
    rw [List.replicate_succ, List.flatten_cons]
    by_cases hi : i < 3
    · interval_cases i
      · simp
      · simp [show 1 < 3 * (t + 1) by omega]
      · simp [show 2 < 3 * (t + 1) by omega]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 3 := ⟨i - 3, by omega⟩
      have hthree (ls : List ℝ) :
          (β :: Real.pi / 2 :: Real.pi / 2 :: ls).getD (j + 3) β = ls.getD j β := rfl
      change (β :: Real.pi / 2 :: Real.pi / 2 :: _).getD (j + 3) β = _
      rw [hthree]
      change ((List.replicate t [β, Real.pi / 2, Real.pi / 2]).flatten).getD j β = _
      rw [ih]
      have hc : (j + 3 < 3 * (t + 1) ∧ (j + 3) % 3 ≠ 0) ↔
          (j < 3 * t ∧ j % 3 ≠ 0) := by omega
      simp only [hc]

theorem generalSignatureAuxBoundaryAngles_pair_getD (β : ℝ) (t i : ℕ) :
    ((List.replicate t [β, Real.pi / 2, Real.pi / 2]).flatten).getD
        (generalSignatureAuxBoundaryPairNat i + 1) β =
      ((List.replicate t [β, Real.pi / 2, Real.pi / 2]).flatten).getD i β := by
  rw [generalSignatureAuxBoundaryAngles_getD, generalSignatureAuxBoundaryAngles_getD]
  have hc : (generalSignatureAuxBoundaryPairNat i + 1 < 3 * t ∧
      (generalSignatureAuxBoundaryPairNat i + 1) % 3 ≠ 0) ↔ (i < 3 * t ∧ i % 3 ≠ 0) := by
    unfold generalSignatureAuxBoundaryPairNat
    split_ifs <;> omega
  simp only [hc]

/-- The untruncated next-side angle identity includes the literal final-to-first wrap. -/
theorem generalSignatureAuxPairNat_getD (β : ℝ) (g : ℕ) (ms : List ℕ) (t i : ℕ) :
    (generalSignatureAuxAngleList β g ms t).getD (generalSignatureAuxPairNat β g ms i + 1) β =
      (generalSignatureAuxAngleList β g ms t).getD i β := by
  let A := cofiniteConstructionSideAngles β g ms
  let B := (List.replicate t [β, Real.pi / 2, Real.pi / 2]).flatten
  let p := A.length
  have hhead : B.getD 0 β = β := by
    dsimp only [B]
    rw [generalSignatureAuxBoundaryAngles_getD]
    simp
  have hleft (j : ℕ) (hj : j ≤ p) : (A ++ B).getD j β = A.getD j β := by
    rcases lt_or_eq_of_le hj with hj | rfl
    · exact List.getD_append A B β j hj
    · rw [List.getD_append_right A B β p (le_refl _), Nat.sub_self, hhead,
        List.getD_eq_default A β (le_refl _)]
  by_cases hi : i < p
  · have hfi : generalSignatureAuxPairNat β g ms i = cofiniteConstructionPairNat g ms i := by
      change (if i < p then _ else _) = _
      rw [ite_eq_left hi]
    have hj : cofiniteConstructionPairNat g ms i < p := cofiniteConstructionPairNat_bound β g ms i hi
    rw [hfi]
    change (A ++ B).getD (cofiniteConstructionPairNat g ms i + 1) β = (A ++ B).getD i β
    rw [hleft _ (by omega), hleft _ hi.le]
    exact cofiniteConstructionPairNat_getD β g ms i
  · have hfi : generalSignatureAuxPairNat β g ms i = p + generalSignatureAuxBoundaryPairNat (i - p) := by
      change (if i < p then _ else _) = _
      rw [ite_eq_right hi]
    rw [hfi]
    change (A ++ B).getD (p + generalSignatureAuxBoundaryPairNat (i - p) + 1) β = (A ++ B).getD i β
    rw [List.getD_append_right A B β _ (by omega), List.getD_append_right A B β i (by omega)]
    rw [show p + generalSignatureAuxBoundaryPairNat (i - p) + 1 - A.length =
        generalSignatureAuxBoundaryPairNat (i - p) + 1 by dsimp only [p]; omega]
    exact generalSignatureAuxBoundaryAngles_pair_getD β t (i - p)

theorem generalSignatureAuxAngleList_head (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ) :
    (generalSignatureAuxAngleList β g ms t).getD 0 β = β := by
  by_cases hp : 0 < (cofiniteConstructionSideAngles β g ms).length
  · rw [generalSignatureAuxAngleList, List.getD_append _ _ _ _ hp]
    exact cofiniteConstructionSideAngles_head β g ms
  · have he : cofiniteConstructionSideAngles β g ms = [] := List.eq_nil_iff_length_eq_zero.mpr (by omega)
    rw [generalSignatureAuxAngleList, he, List.nil_append, generalSignatureAuxBoundaryAngles_getD]
    simp

theorem generalSignatureAux_finRotate_val {n : ℕ} (i : Fin n) :
    (finRotate n i).val = if i.val + 1 = n then 0 else i.val + 1 := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    rw [coe_finRotate]
    by_cases hi : i = Fin.last n
    · subst i
      simp
    · have hn : i.val + 1 ≠ n + 1 := by
        intro h
        apply hi
        apply Fin.ext
        change i.val = n
        omega
      simp only [hi, ite_false, hn]

/-- The concrete auxiliary side permutation has the exact original angle profile. -/
theorem generalSignatureAuxPairing_angle_profile (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ)
    (i : Fin (generalSignatureAuxAngleList β g ms t).length) :
    (generalSignatureAuxAngleList β g ms t)[i] =
      (generalSignatureAuxAngleList β g ms t)[finRotate _ (generalSignatureAuxPairing β g ms t i)] := by
  let L := generalSignatureAuxAngleList β g ms t
  let j := generalSignatureAuxPairing β g ms t i
  have hprofile : L.getD (j.val + 1) β = L.getD i.val β :=
    generalSignatureAuxPairNat_getD β g ms t i.val
  have hrot := generalSignatureAux_finRotate_val j
  have hget : L.getD i.val β = L.getD (finRotate L.length j).val β := by
    by_cases he : j.val + 1 = L.length
    · rw [ite_eq_left he] at hrot
      rw [hrot, generalSignatureAuxAngleList_head]
      rw [he, List.getD_eq_default L β (le_refl _)] at hprofile
      exact hprofile.symm
    · rw [ite_eq_right he] at hrot
      rw [hrot]
      exact hprofile.symm
  simpa only [List.getD_eq_getElem L β i.isLt,
    List.getD_eq_getElem L β (finRotate L.length j).isLt, Fin.getElem_fin, L, j] using hget

theorem generalSignature_markAngles_append (β : ℝ) (ms ns : List ℕ) :
    cofiniteConstructionMarkAngles β (ms ++ ns) =
      cofiniteConstructionMarkAngles β ms ++ cofiniteConstructionMarkAngles β ns := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    by_cases hm : m = 2 <;> simp [cofiniteConstructionMarkAngles, hm, ih]

theorem generalSignature_markAngles_cusps (β : ℝ) (s : ℕ) :
    cofiniteConstructionMarkAngles β (List.replicate s 0) =
      (List.replicate s [β, 0]).flatten := by
  induction s with
  | zero => rfl
  | succ s ih =>
    simp [List.replicate_succ, cofiniteConstructionMarkAngles, cofiniteConstructionConeAngle, ih]

/-- The profile acts on the exact frozen ordered core list, preserving its
literal distinction between cusp vertices and the two boundary right corners. -/
theorem generalCoreAngles_eq_auxAngleList (g : ℕ) (orders : List ℕ) (s t : ℕ) :
    generalCoreAngles g orders s t =
      generalSignatureAuxAngleList (generalCoreBaseAngle g orders s t) g
        (orders ++ List.replicate s 0) t := by
  unfold generalCoreAngles generalSignatureAuxAngleList cofiniteConstructionSideAngles
  rw [generalSignature_markAngles_append, generalSignature_markAngles_cusps]
  simp only [List.append_assoc]

/-- The concrete auxiliary pairing is carried to the actual frozen core sides. -/
def generalCoreAuxPairing (g : ℕ) (orders : List ℕ) (s t : ℕ) :
    Equiv.Perm (Fin (generalCoreAngles g orders s t).length) :=
  let e := finCongr (congrArg List.length (generalCoreAngles_eq_auxAngleList g orders s t))
  e.trans ((generalSignatureAuxPairing (generalCoreBaseAngle g orders s t) g
    (orders ++ List.replicate s 0) t).trans e.symm)

theorem generalCoreAuxPairing_val (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (i : Fin (generalCoreAngles g orders s t).length) :
    (generalCoreAuxPairing g orders s t i).val =
      generalSignatureAuxPairNat (generalCoreBaseAngle g orders s t) g
        (orders ++ List.replicate s 0) i.val := rfl

theorem generalCoreAuxPairing_involutive (g : ℕ) (orders : List ℕ) (s t : ℕ) :
    Function.Involutive (generalCoreAuxPairing g orders s t) := by
  intro i
  apply Fin.ext
  exact generalSignatureAuxPairNat_involutive (generalCoreBaseAngle g orders s t) g
    (orders ++ List.replicate s 0) i.val

theorem generalCoreAuxPairing_angle_profile (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (i : Fin (generalCoreAngles g orders s t).length) :
    generalCoreTheta g orders s t i =
      generalCoreTheta g orders s t (finRotate _ (generalCoreAuxPairing g orders s t i)) := by
  let L := generalCoreAngles g orders s t
  let β := generalCoreBaseAngle g orders s t
  let j := generalCoreAuxPairing g orders s t i
  have hprofile : L.getD (j.val + 1) β = L.getD i.val β := by
    change L.getD (generalSignatureAuxPairNat β g (orders ++ List.replicate s 0) i.val + 1) β = _
    have hNat (r : ℕ) : L.getD (generalSignatureAuxPairNat β g
        (orders ++ List.replicate s 0) r + 1) β = L.getD r β := by
      dsimp only [L]
      rw [generalCoreAngles_eq_auxAngleList]
      exact generalSignatureAuxPairNat_getD β g (orders ++ List.replicate s 0) t r
    exact hNat i.val
  have hhead : L.getD 0 β = β := by
    dsimp only [L]
    rw [generalCoreAngles_eq_auxAngleList]
    exact generalSignatureAuxAngleList_head β g (orders ++ List.replicate s 0) t
  have hrot := generalSignatureAux_finRotate_val j
  have hget : L.getD i.val β = L.getD (finRotate L.length j).val β := by
    by_cases he : j.val + 1 = L.length
    · rw [ite_eq_left he] at hrot
      rw [hrot, hhead]
      rw [he, List.getD_eq_default L β (le_refl _)] at hprofile
      exact hprofile.symm
    · rw [ite_eq_right he] at hrot
      rw [hrot]
      exact hprofile.symm
  simpa only [List.getD_eq_getElem L β i.isLt,
    List.getD_eq_getElem L β (finRotate L.length j).isLt, Fin.getElem_fin, generalCoreTheta, L, j] using hget

/-- Ordinary-cycle labels include one real base corner for each boundary triple. -/
def generalSignatureAuxBaseNat (β : ℝ) (g : ℕ) (ms : List ℕ) (i : ℕ) : ℕ :=
  if i < 4 * g + ms.length then cofiniteConstructionBaseNat g ms i
  else (cofiniteConstructionSideAngles β g ms).length + 3 * (i - (4 * g + ms.length))

theorem generalSignatureAuxBaseNat_zero (β : ℝ) (g : ℕ) (ms : List ℕ) :
    generalSignatureAuxBaseNat β g ms 0 = 0 := by
  unfold generalSignatureAuxBaseNat
  split_ifs with h
  · exact cofiniteConstructionBaseNat_zero g ms
  · have hb : 4 * g + ms.length = 0 := by omega
    have hp := cofiniteConstructionBaseNat_full β g ms
    rw [hb, cofiniteConstructionBaseNat_zero] at hp
    simpa only [Nat.zero_sub, Nat.mul_zero, Nat.add_zero] using hp.symm

theorem generalSignatureAuxBaseNat_bound (β : ℝ) (g : ℕ) (ms : List ℕ) (t i : ℕ)
    (hi : i < 4 * g + ms.length + t) :
    generalSignatureAuxBaseNat β g ms i < (generalSignatureAuxAngleList β g ms t).length := by
  rw [generalSignatureAuxAngleList_length]
  unfold generalSignatureAuxBaseNat
  split_ifs with h
  · have hp := cofiniteConstructionBaseNat_bound β g ms i h
    omega
  · omega

theorem generalSignatureAuxBaseNat_full (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ) :
    generalSignatureAuxBaseNat β g ms (4 * g + ms.length + t) =
      (generalSignatureAuxAngleList β g ms t).length := by
  rw [generalSignatureAuxBaseNat, ite_eq_right (by omega),
    Nat.add_sub_cancel_left, generalSignatureAuxAngleList_length]

theorem generalSignatureAuxBaseNat_angle (β : ℝ) (g : ℕ) (ms : List ℕ) (t i : ℕ) :
    (generalSignatureAuxAngleList β g ms t).getD (generalSignatureAuxBaseNat β g ms i) β = β := by
  unfold generalSignatureAuxBaseNat
  split_ifs with h
  · have hb := cofiniteConstructionBaseNat_bound β g ms i h
    rw [generalSignatureAuxAngleList, List.getD_append _ _ _ _ hb]
    exact cofiniteConstructionBaseNat_angle β g ms i
  · rw [generalSignatureAuxAngleList, List.getD_append_right _ _ _ _ (by omega),
      Nat.add_sub_cancel_left, generalSignatureAuxBoundaryAngles_getD]
    simp

theorem generalSignatureAuxBaseNat_step (β : ℝ) (g : ℕ) (ms : List ℕ) (i : ℕ) :
    generalSignatureAuxPairNat β g ms (generalSignatureAuxBaseNat β g ms i) + 1 =
      generalSignatureAuxBaseNat β g ms (i + 1) := by
  let b := 4 * g + ms.length
  let p := (cofiniteConstructionSideAngles β g ms).length
  by_cases hi : i < b
  · have hbi : generalSignatureAuxBaseNat β g ms i = cofiniteConstructionBaseNat g ms i := by
      exact ite_eq_left hi
    have hbj : generalSignatureAuxBaseNat β g ms (i + 1) = cofiniteConstructionBaseNat g ms (i + 1) := by
      by_cases hj : i + 1 < b
      · exact ite_eq_left hj
      · have hje : i + 1 = b := by omega
        rw [hje]
        change (if b < b then _ else _) = _
        rw [ite_eq_right (lt_irrefl _), Nat.sub_self, Nat.mul_zero, Nat.add_zero]
        exact (cofiniteConstructionBaseNat_full β g ms).symm
    have hbp : cofiniteConstructionBaseNat g ms i < p := cofiniteConstructionBaseNat_bound β g ms i hi
    rw [hbi, hbj]
    change (if cofiniteConstructionBaseNat g ms i < p then _ else _) + 1 = _
    rw [ite_eq_left hbp]
    exact cofiniteConstructionBaseNat_step g ms i
  · have hbi : generalSignatureAuxBaseNat β g ms i = p + 3 * (i - b) := ite_eq_right hi
    have hbj : generalSignatureAuxBaseNat β g ms (i + 1) = p + 3 * (i + 1 - b) :=
      ite_eq_right (by omega)
    rw [hbi, hbj]
    change (if p + 3 * (i - b) < p then _ else _) + 1 = _
    rw [ite_eq_right (by omega)]
    change p + generalSignatureAuxBoundaryPairNat (p + 3 * (i - b) - p) + 1 = p + 3 * (i + 1 - b)
    rw [Nat.add_sub_cancel_left, generalSignatureAuxBoundaryPairNat_zero]
    omega

def generalSignatureAuxBaseIndex (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ)
    (i : Fin (4 * g + ms.length + t)) : Fin (generalSignatureAuxAngleList β g ms t).length :=
  ⟨generalSignatureAuxBaseNat β g ms i.val, generalSignatureAuxBaseNat_bound β g ms t i.val i.isLt⟩

theorem generalSignatureAuxBaseIndex_next (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ)
    (i : Fin (4 * g + ms.length + t)) :
    generalSignatureAuxBaseIndex β g ms t (finRotate _ i) =
      finRotate _ (generalSignatureAuxPairing β g ms t (generalSignatureAuxBaseIndex β g ms t i)) := by
  let B := 4 * g + ms.length + t
  let N := (generalSignatureAuxAngleList β g ms t).length
  have hstep := generalSignatureAuxBaseNat_step β g ms i.val
  have hfull := generalSignatureAuxBaseNat_full β g ms t
  have hrotB := generalSignatureAux_finRotate_val i
  have hrotN := generalSignatureAux_finRotate_val
    (generalSignatureAuxPairing β g ms t (generalSignatureAuxBaseIndex β g ms t i))
  apply Fin.ext
  change generalSignatureAuxBaseNat β g ms (finRotate B i).val = _
  rw [hrotB, hrotN]
  change generalSignatureAuxBaseNat β g ms (if i.val + 1 = B then 0 else i.val + 1) =
    if generalSignatureAuxPairNat β g ms (generalSignatureAuxBaseNat β g ms i.val) + 1 = N then 0
      else generalSignatureAuxPairNat β g ms (generalSignatureAuxBaseNat β g ms i.val) + 1
  by_cases hi : i.val + 1 = B
  · rw [ite_eq_left hi, generalSignatureAuxBaseNat_zero, hstep, hi, hfull, ite_eq_left rfl]
  · have hb : i.val + 1 < B := by have := i.isLt; omega
    have hbn : generalSignatureAuxBaseNat β g ms (i.val + 1) < N :=
      generalSignatureAuxBaseNat_bound β g ms t _ hb
    have hn : generalSignatureAuxPairNat β g ms (generalSignatureAuxBaseNat β g ms i.val) + 1 ≠ N := by
      rw [hstep]
      omega
    rw [ite_eq_right hi, ite_eq_right hn]
    exact hstep.symm

theorem generalSignatureAuxBaseIndex_iterate (β : ℝ) (g : ℕ) (ms : List ℕ) (t k : ℕ)
    (i : Fin (4 * g + ms.length + t)) :
    (((generalSignatureAuxPairing β g ms t).trans (finRotate _))^[k])
        (generalSignatureAuxBaseIndex β g ms t i) =
      generalSignatureAuxBaseIndex β g ms t ((finRotate _)^[k] i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    exact (generalSignatureAuxBaseIndex_next β g ms t _).symm

open Fin.NatCast in
theorem generalSignatureAuxBaseIndex_full_turn (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ)
    (i : Fin (4 * g + ms.length + t)) :
    (((generalSignatureAuxPairing β g ms t).trans (finRotate _))^[4 * g + ms.length + t])
      (generalSignatureAuxBaseIndex β g ms t i) = generalSignatureAuxBaseIndex β g ms t i := by
  let B := 4 * g + ms.length + t
  let baseCountNeZero : NeZero B := i.neZero
  have hrot (j : ℕ) : ((finRotate B)^[j]) i = i + (j : Fin B) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih, finRotate_apply]
      simp only [Nat.cast_add, Nat.cast_one, add_assoc]
  rw [generalSignatureAuxBaseIndex_iterate, hrot, Fin.natCast_self, add_zero]

/-- Every actual cone/cusp prefix corner is an independently labelled base
corner or its actual retained outer corner, including prefixes with fewer than two marks. -/
theorem generalSignature_mark_label_cover (β : ℝ) (ms : List ℕ) (i : ℕ)
    (hi : i < (cofiniteConstructionMarkAngles β ms).length) :
    (∃ a < ms.length, cofiniteConstructionMarkBaseNat ms a = i) ∨
      (∃ j < ms.length, ms.getD j 2 ≠ 2 ∧ cofiniteConstructionMarkBaseNat ms j + 1 = i) := by
  induction ms generalizing i with
  | nil => simp [cofiniteConstructionMarkAngles] at hi
  | cons m ms ih =>
    let w : ℕ := if m = 2 then 1 else 2
    have hlen : (cofiniteConstructionMarkAngles β (m :: ms)).length =
        w + (cofiniteConstructionMarkAngles β ms).length := by
      by_cases hm : m = 2 <;> simp [cofiniteConstructionMarkAngles, w, hm] <;> omega
    rw [hlen] at hi
    by_cases hiw : i < w
    · by_cases hi0 : i = 0
      · subst i
        exact Or.inl ⟨0, by simp, rfl⟩
      · have hm : m ≠ 2 := by intro h; simp only [w, h, ite_true] at hiw; omega
        have hie : i = 1 := by simp only [w, hm, ite_false] at hiw; omega
        subst i
        exact Or.inr ⟨0, by simp, hm, rfl⟩
    · have htail : i - w < (cofiniteConstructionMarkAngles β ms).length := by omega
      rcases ih (i - w) htail with ⟨a, ha, he⟩ | ⟨j, hj, hm, he⟩
      · apply Or.inl
        refine ⟨a + 1, by simp only [List.length_cons]; omega, ?_⟩
        change w + cofiniteConstructionMarkBaseNat ms a = i
        omega
      · apply Or.inr
        refine ⟨j + 1, by simp only [List.length_cons]; omega, hm, ?_⟩
        change w + cofiniteConstructionMarkBaseNat ms j + 1 = i
        omega

theorem generalSignature_prefix_label_cover (β : ℝ) (g : ℕ) (ms : List ℕ) (i : ℕ)
    (hi : i < (cofiniteConstructionSideAngles β g ms).length) :
    (∃ a < 4 * g + ms.length, cofiniteConstructionBaseNat g ms a = i) ∨
      (∃ j < ms.length, ms.getD j 2 ≠ 2 ∧ 4 * g + cofiniteConstructionMarkBaseNat ms j + 1 = i) := by
  induction g generalizing i with
  | zero => simpa only [cofiniteConstructionSideAngles, List.replicate_zero,
      List.nil_append, cofiniteConstructionBaseNat, Nat.mul_zero, Nat.zero_add] using
        generalSignature_mark_label_cover β ms i hi
  | succ g ih =>
    rw [cofiniteConstructionSideAngles_handle] at hi
    simp only [List.length_cons] at hi
    by_cases hi4 : i < 4
    · apply Or.inl
      refine ⟨cofiniteConstructionHandleBaseNat i, ?_, ?_⟩
      · have h := cofiniteConstructionHandleBaseNat_lt_four i hi4
        omega
      · rw [cofiniteConstructionBaseNat,
          ite_eq_left (cofiniteConstructionHandleBaseNat_lt_four i hi4)]
        exact cofiniteConstructionHandleBaseNat_involutive i
    · have hit : i - 4 < (cofiniteConstructionSideAngles β g ms).length := by omega
      rcases ih (i - 4) hit with ⟨a, ha, he⟩ | ⟨j, hj, hm, he⟩
      · apply Or.inl
        refine ⟨4 + a, by omega, ?_⟩
        rw [cofiniteConstructionBaseNat, ite_eq_right (by omega), Nat.add_sub_cancel_left]
        omega
      · exact Or.inr ⟨j, hj, hm, by omega⟩

theorem generalSignatureAux_outer_bound (β : ℝ) (g : ℕ) (ms : List ℕ) (j : ℕ)
    (hj : j < ms.length) (hm : ms.getD j 2 ≠ 2) :
    4 * g + cofiniteConstructionMarkBaseNat ms j + 1 < (cofiniteConstructionSideAngles β g ms).length := by
  have h := cofiniteConstructionMarkOuterNat_bound β ms j hj hm
  simp only [cofiniteConstructionSideAngles, List.length_append, List.length_replicate]
  omega

theorem generalSignatureAux_outer_step (β : ℝ) (g : ℕ) (ms : List ℕ) (j : ℕ)
    (hj : j < ms.length) (hm : ms.getD j 2 ≠ 2) :
    generalSignatureAuxPairNat β g ms (4 * g + cofiniteConstructionMarkBaseNat ms j + 1) + 1 =
      4 * g + cofiniteConstructionMarkBaseNat ms j + 1 := by
  have hb := generalSignatureAux_outer_bound β g ms j hj hm
  rw [generalSignatureAuxPairNat, ite_eq_left hb]
  rw [show 4 * g + cofiniteConstructionMarkBaseNat ms j + 1 =
    4 * g + (cofiniteConstructionMarkBaseNat ms j + 1) by omega,
    cofiniteConstructionPairNat_handle_prefix]
  have hs := cofiniteConstructionMarkOuterNat_fixed ms j hj hm
  omega

theorem generalSignatureAux_outer_angle (β : ℝ) (g : ℕ) (ms : List ℕ) (t j : ℕ)
    (hj : j < ms.length) (hm : ms.getD j 2 ≠ 2) :
    (generalSignatureAuxAngleList β g ms t).getD
      (4 * g + cofiniteConstructionMarkBaseNat ms j + 1) β = cofiniteConstructionConeAngle (ms.getD j 2) := by
  have hb := generalSignatureAux_outer_bound β g ms j hj hm
  rw [generalSignatureAuxAngleList, List.getD_append _ _ _ _ hb,
    show 4 * g + cofiniteConstructionMarkBaseNat ms j + 1 =
      4 * g + (cofiniteConstructionMarkBaseNat ms j + 1) by omega,
    cofiniteConstructionSideAngles_mark_getD]
  exact cofiniteConstructionMarkOuterNat_angle β ms j hj hm

def generalSignatureAuxBoundaryRightIndex (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ)
    (j : Fin t) (r : Fin 2) : Fin (generalSignatureAuxAngleList β g ms t).length :=
  ⟨(cofiniteConstructionSideAngles β g ms).length + 3 * j.val + (r.val + 1), by
    rw [generalSignatureAuxAngleList_length]
    have hj := j.isLt
    have hr := r.isLt
    omega⟩

theorem generalSignatureAuxBoundaryRightIndex_angle (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ)
    (j : Fin t) (r : Fin 2) :
    (generalSignatureAuxAngleList β g ms t)[generalSignatureAuxBoundaryRightIndex β g ms t j r] =
      Real.pi / 2 := by
  let p := (cofiniteConstructionSideAngles β g ms).length
  have hget : (generalSignatureAuxAngleList β g ms t).getD (p + 3 * j.val + (r.val + 1)) β =
      Real.pi / 2 := by
    rw [generalSignatureAuxAngleList, List.getD_append_right _ _ _ _ (by omega)]
    rw [show p + 3 * j.val + (r.val + 1) - (cofiniteConstructionSideAngles β g ms).length =
      3 * j.val + (r.val + 1) by dsimp only [p]; omega]
    rw [generalSignatureAuxBoundaryAngles_getD, ite_eq_left ?_]
    have hj := j.isLt
    have hr := r.isLt
    omega
  exact (List.getD_eq_getElem _ β (generalSignatureAuxBoundaryRightIndex β g ms t j r).isLt).symm.trans hget

theorem generalSignatureAuxBoundaryRightIndex_step_zero (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ)
    (j : Fin t) :
    ((generalSignatureAuxPairing β g ms t).trans (finRotate _))
        (generalSignatureAuxBoundaryRightIndex β g ms t j 0) =
      generalSignatureAuxBoundaryRightIndex β g ms t j 1 := by
  let p := (cofiniteConstructionSideAngles β g ms).length
  let N := (generalSignatureAuxAngleList β g ms t).length
  have hN : N = p + 3 * t := generalSignatureAuxAngleList_length β g ms t
  have hj := j.isLt
  have hpair : generalSignatureAuxPairNat β g ms (p + 3 * j.val + 1) = p + 3 * j.val + 1 := by
    change (if p + 3 * j.val + 1 < p then _ else _) = _
    rw [ite_eq_right (by omega)]
    rw [show p + 3 * j.val + 1 - p = 3 * j.val + 1 by omega,
      generalSignatureAuxBoundaryPairNat_one]
    dsimp only [p]
    omega
  apply Fin.ext
  change (finRotate N (generalSignatureAuxPairing β g ms t
    (generalSignatureAuxBoundaryRightIndex β g ms t j 0))).val = p + 3 * j.val + 2
  rw [generalSignatureAux_finRotate_val]
  change (if generalSignatureAuxPairNat β g ms (p + 3 * j.val + 1) + 1 = N then 0
    else generalSignatureAuxPairNat β g ms (p + 3 * j.val + 1) + 1) = p + 3 * j.val + 2
  rw [hpair, ite_eq_right (by omega)]

theorem generalSignatureAuxBoundaryRightIndex_step_one (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ)
    (j : Fin t) :
    ((generalSignatureAuxPairing β g ms t).trans (finRotate _))
        (generalSignatureAuxBoundaryRightIndex β g ms t j 1) =
      generalSignatureAuxBoundaryRightIndex β g ms t j 0 := by
  let p := (cofiniteConstructionSideAngles β g ms).length
  let N := (generalSignatureAuxAngleList β g ms t).length
  have hN : N = p + 3 * t := generalSignatureAuxAngleList_length β g ms t
  have hj := j.isLt
  have hpair : generalSignatureAuxPairNat β g ms (p + 3 * j.val + 2) = p + 3 * j.val := by
    change (if p + 3 * j.val + 2 < p then _ else _) = _
    rw [ite_eq_right (by omega)]
    rw [show p + 3 * j.val + 2 - p = 3 * j.val + 2 by omega,
      generalSignatureAuxBoundaryPairNat_two]
  apply Fin.ext
  change (finRotate N (generalSignatureAuxPairing β g ms t
    (generalSignatureAuxBoundaryRightIndex β g ms t j 1))).val = p + 3 * j.val + 1
  rw [generalSignatureAux_finRotate_val]
  change (if generalSignatureAuxPairNat β g ms (p + 3 * j.val + 2) + 1 = N then 0
    else generalSignatureAuxPairNat β g ms (p + 3 * j.val + 2) + 1) = p + 3 * j.val + 1
  rw [hpair, ite_eq_right (by omega)]

theorem generalSignatureAuxBoundaryRightIndex_period_four (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ)
    (j : Fin t) (r : Fin 2) :
    (((generalSignatureAuxPairing β g ms t).trans (finRotate _))^[4])
      (generalSignatureAuxBoundaryRightIndex β g ms t j r) =
        generalSignatureAuxBoundaryRightIndex β g ms t j r := by
  fin_cases r
  · change ((generalSignatureAuxPairing β g ms t).trans (finRotate _))
      (((generalSignatureAuxPairing β g ms t).trans (finRotate _))
      (((generalSignatureAuxPairing β g ms t).trans (finRotate _))
      (((generalSignatureAuxPairing β g ms t).trans (finRotate _))
      (generalSignatureAuxBoundaryRightIndex β g ms t j 0)))) = _
    rw [generalSignatureAuxBoundaryRightIndex_step_zero, generalSignatureAuxBoundaryRightIndex_step_one,
      generalSignatureAuxBoundaryRightIndex_step_zero, generalSignatureAuxBoundaryRightIndex_step_one]
    apply congrArg (generalSignatureAuxBoundaryRightIndex β g ms t j)
    apply Fin.ext
    rfl
  · change ((generalSignatureAuxPairing β g ms t).trans (finRotate _))
      (((generalSignatureAuxPairing β g ms t).trans (finRotate _))
      (((generalSignatureAuxPairing β g ms t).trans (finRotate _))
      (((generalSignatureAuxPairing β g ms t).trans (finRotate _))
      (generalSignatureAuxBoundaryRightIndex β g ms t j 1)))) = _
    rw [generalSignatureAuxBoundaryRightIndex_step_one, generalSignatureAuxBoundaryRightIndex_step_zero,
      generalSignatureAuxBoundaryRightIndex_step_one, generalSignatureAuxBoundaryRightIndex_step_zero]
    apply congrArg (generalSignatureAuxBoundaryRightIndex β g ms t j)
    apply Fin.ext
    rfl

/-- The three actual label families exhaust all native core corners. -/
theorem generalSignatureAux_corner_label_cover (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ)
    (i : Fin (generalSignatureAuxAngleList β g ms t).length) :
    (∃ a : Fin (4 * g + ms.length + t), generalSignatureAuxBaseIndex β g ms t a = i) ∨
      (∃ j : Fin ms.length, ms[j] ≠ 2 ∧
        4 * g + cofiniteConstructionMarkBaseNat ms j.val + 1 = i.val) ∨
      (∃ j : Fin t, ∃ r : Fin 2, generalSignatureAuxBoundaryRightIndex β g ms t j r = i) := by
  let b := 4 * g + ms.length
  let p := (cofiniteConstructionSideAngles β g ms).length
  have hi : i.val < p + 3 * t :=
    i.isLt.trans_eq (generalSignatureAuxAngleList_length β g ms t)
  by_cases hip : i.val < p
  · rcases generalSignature_prefix_label_cover β g ms i.val hip with ⟨a, ha, he⟩ | ⟨j, hj, hm, he⟩
    · apply Or.inl
      refine ⟨⟨a, by omega⟩, Fin.ext ?_⟩
      change generalSignatureAuxBaseNat β g ms a = i.val
      rw [generalSignatureAuxBaseNat, ite_eq_left ha]
      exact he
    · exact Or.inr (Or.inl ⟨⟨j, hj⟩, by simpa only [List.getD_eq_getElem ms 2 hj, Fin.getElem_fin] using hm, he⟩)
  · let j : ℕ := (i.val - p) / 3
    have hj : j < t := by dsimp only [j]; omega
    by_cases hm : (i.val - p) % 3 = 0
    · apply Or.inl
      refine ⟨⟨b + j, by omega⟩, Fin.ext ?_⟩
      change generalSignatureAuxBaseNat β g ms (b + j) = i.val
      rw [generalSignatureAuxBaseNat, ite_eq_right (by omega), Nat.add_sub_cancel_left]
      change p + 3 * j = i.val
      dsimp only [j]
      omega
    · apply Or.inr ∘ Or.inr
      let r : ℕ := (i.val - p) % 3 - 1
      have hr : r < 2 := by dsimp only [r]; omega
      refine ⟨⟨j, hj⟩, ⟨r, hr⟩, Fin.ext ?_⟩
      change p + 3 * j + (r + 1) = i.val
      dsimp only [j, r]
      omega

/-- All actual finite corners have complete physical angular periods.
The ordinary cycle, retained outer singleton cycles and boundary two-cycles
are proved separately before being combined by the exhaustive labels. -/
theorem generalSignatureAux_positive_angular_periods (β : ℝ) (g : ℕ) (ms : List ℕ) (t : ℕ)
    (hB : 3 ≤ 4 * g + ms.length + t)
    (hβ : β = _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod (4 * g + ms.length + t))
    (hms : ∀ m ∈ ms, m = 0 ∨ 2 ≤ m) :
    ∀ i : Fin (generalSignatureAuxAngleList β g ms t).length,
      0 < (generalSignatureAuxAngleList β g ms t)[i] → ∃ N : ℕ, 3 ≤ N ∧
        (((generalSignatureAuxPairing β g ms t).trans (finRotate _))^[N]) i = i ∧
        (generalSignatureAuxAngleList β g ms t)[i] = _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N := by
  let L := generalSignatureAuxAngleList β g ms t
  let B := 4 * g + ms.length + t
  let τ := (generalSignatureAuxPairing β g ms t).trans (finRotate _)
  have hBase (a : Fin B) : ∃ N : ℕ, 3 ≤ N ∧
      τ^[N] (generalSignatureAuxBaseIndex β g ms t a) = generalSignatureAuxBaseIndex β g ms t a ∧
      L[generalSignatureAuxBaseIndex β g ms t a] = _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N := by
    refine ⟨B, hB, generalSignatureAuxBaseIndex_full_turn β g ms t a, ?_⟩
    have ha : L[generalSignatureAuxBaseIndex β g ms t a] = β := by
      exact (List.getD_eq_getElem L β (generalSignatureAuxBaseIndex β g ms t a).isLt).symm.trans
        (generalSignatureAuxBaseNat_angle β g ms t a.val)
    exact ha.trans hβ
  intro i hpos
  rcases generalSignatureAux_corner_label_cover β g ms t i with ⟨a, rfl⟩ | ⟨j, hm, he⟩ | ⟨j, r, rfl⟩
  · exact hBase a
  · have hmD : ms.getD j.val 2 ≠ 2 := by simpa only [List.getD_eq_getElem ms 2 j.isLt, Fin.getElem_fin] using hm
    have hAngle : L[i] = cofiniteConstructionConeAngle (ms[j]) := by
      calc
        L[i] = L.getD i.val β := (List.getD_eq_getElem L β i.isLt).symm
        _ = cofiniteConstructionConeAngle (ms[j]) := by
          rw [← he]
          simpa only [List.getD_eq_getElem ms 2 j.isLt, Fin.getElem_fin] using
            generalSignatureAux_outer_angle β g ms t j.val j.isLt hmD
    have horder := hms (ms[j]) (List.getElem_mem j.isLt)
    have hm3 : 3 ≤ ms[j] := by
      rcases horder with hm0 | hm2
      · rw [hAngle, hm0] at hpos
        simp [cofiniteConstructionConeAngle] at hpos
      · omega
    have hFix : τ i = i := by
      have hs : generalSignatureAuxPairNat β g ms i.val + 1 = i.val := by
        rw [← he]
        exact generalSignatureAux_outer_step β g ms j.val j.isLt hmD
      apply Fin.ext
      change (finRotate L.length (generalSignatureAuxPairing β g ms t i)).val = i.val
      rw [generalSignatureAux_finRotate_val]
      change (if generalSignatureAuxPairNat β g ms i.val + 1 = L.length then 0
        else generalSignatureAuxPairNat β g ms i.val + 1) = i.val
      rw [hs, ite_eq_right (Nat.ne_of_lt i.isLt)]
    have hMany : ∀ k : ℕ, τ^[k] i = i := by
      intro k
      induction k with
      | zero => rfl
      | succ k ih => rw [Function.iterate_succ_apply', ih, hFix]
    refine ⟨ms[j], hm3, hMany _, ?_⟩
    exact hAngle
  · refine ⟨4, by norm_num, generalSignatureAuxBoundaryRightIndex_period_four β g ms t j r, ?_⟩
    rw [generalSignatureAuxBoundaryRightIndex_angle]
    norm_num [_root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod]
    ring

theorem generalSignature_finCongr_rotate {n m : ℕ} (h : n = m) (i : Fin n) :
    finCongr h (finRotate n i) = finRotate m (finCongr h i) := by
  subst m
  rfl

/-- The complete physical angular periods hold on the frozen actual core indices. -/
theorem generalCoreAux_positive_angular_periods (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t) :
    ∀ i : Fin (generalCoreAngles g orders s t).length,
      0 < generalCoreTheta g orders s t i → ∃ N : ℕ, 3 ≤ N ∧
        (((generalCoreAuxPairing g orders s t).trans (finRotate _))^[N]) i = i ∧
        generalCoreTheta g orders s t i = _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod N := by
  let β := generalCoreBaseAngle g orders s t
  let ms := orders ++ List.replicate s 0
  let A := generalSignatureAuxAngleList β g ms t
  let e := finCongr (congrArg List.length (generalCoreAngles_eq_auxAngleList g orders s t))
  let τ := (generalCoreAuxPairing g orders s t).trans (finRotate _)
  let τA := (generalSignatureAuxPairing β g ms t).trans (finRotate _)
  have hBcount : 4 * g + ms.length + t = generalCoreBaseCount g orders s t := by
    simp [ms, generalCoreBaseCount]
    omega
  have hB : 3 ≤ 4 * g + ms.length + t := hBcount ▸ generalCore_base_count g orders s t hdef
  have hβ : β = _root_.LowDimensionalTopology.Geometry.Euclidean.finiteRotationPeriod (4 * g + ms.length + t) := by
    rw [hBcount]
    rfl
  have hms : ∀ m ∈ ms, m = 0 ∨ 2 ≤ m := by
    intro m hm
    rcases List.mem_append.mp hm with hm | hm
    · exact Or.inr (ho m hm)
    · exact Or.inl (List.eq_of_mem_replicate hm)
  have hpair (i : Fin (generalCoreAngles g orders s t).length) :
      e (generalCoreAuxPairing g orders s t i) = generalSignatureAuxPairing β g ms t (e i) := by
    change e (e.symm (generalSignatureAuxPairing β g ms t (e i))) = _
    exact e.apply_symm_apply _
  have hstep (i : Fin (generalCoreAngles g orders s t).length) : e (τ i) = τA (e i) := by
    change e (finRotate _ (generalCoreAuxPairing g orders s t i)) =
      finRotate _ (generalSignatureAuxPairing β g ms t (e i))
    rw [generalSignature_finCongr_rotate, hpair]
  have hiter (k : ℕ) (i : Fin (generalCoreAngles g orders s t).length) :
      e (τ^[k] i) = τA^[k] (e i) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', hstep, ih, Function.iterate_succ_apply']
  have hθ (i : Fin (generalCoreAngles g orders s t).length) : generalCoreTheta g orders s t i = A[e i] := by
    have hn (r : ℕ) : (generalCoreAngles g orders s t).getD r β = A.getD r β :=
      congrArg (fun L : List ℝ => L.getD r β) (generalCoreAngles_eq_auxAngleList g orders s t)
    calc
      generalCoreTheta g orders s t i = (generalCoreAngles g orders s t).getD i.val β :=
        (List.getD_eq_getElem _ β i.isLt).symm
      _ = A.getD i.val β := hn i.val
      _ = A[e i] := List.getD_eq_getElem A β (e i).isLt
  intro i hpos
  obtain ⟨N, hN, hcycle, hangle⟩ := generalSignatureAux_positive_angular_periods β g ms t
    hB hβ hms (e i) (by rw [← hθ i]; exact hpos)
  refine ⟨N, hN, ?_, (hθ i).trans hangle⟩
  apply e.injective
  rw [hiter, hcycle]

/-- The auxiliary side pairing acts on the actual ordered cut-core polygon.
Its cut self-pairings will be omitted from the final boundary-signature subgroup. -/
def generalCoreAuxSidePairing (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi) :
    _root_.LowDimensionalTopology.Geometry.Polygon.PoincareSidePairing (ℍ ≃ᵢ ℍ) (_root_.LowDimensionalTopology.Geometry.Polygon.jordanDiscPoincarePolygon
      (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
        (generalCoreTheta_mem g orders s t ho hdef) hd hb)) :=
  cofiniteTangentialSidePairing (generalCoreTheta g orders s t) d
    (generalCoreTheta_mem g orders s t ho hdef) hd hb (generalCoreAuxPairing g orders s t)
    (generalCoreAuxPairing_involutive g orders s t) (generalCoreAuxPairing_angle_profile g orders s t)

/--
Complete finite corner fans and genuine cusp strips give actual local tessellation for
this concrete auxiliary group; no local tessellation is supplied as a premise.
-/
theorem generalCore_auxiliary_local_tessellation (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi) :
    (generalCoreAuxSidePairing g orders s t ho hdef d hd hb).FiniteFiberLocalTessellationCondition := by
  apply cofiniteTangential_mixed_local_tessellation
  exact generalCoreAux_positive_angular_periods g orders s t ho hdef

/-- The concrete auxiliary group is discrete and has the original cut-core
polygon as a genuine fundamental domain. It is not declared to be the target
group with t boundary ends. -/
theorem generalCore_auxiliary_poincare (g : ℕ) (orders : List ℕ) (s t : ℕ)
    (ho : ∀ m ∈ orders, 2 ≤ m) (hdef : 0 < generalCoreDeficit g orders s t)
    (d : ℝ) (hd : 0 < d) (hb : _root_.LowDimensionalTopology.Geometry.Polygon.polygonAngleBalance (generalCoreTheta g orders s t) d = Real.pi) :
    let S := generalCoreAuxSidePairing g orders s t ho hdef d hd hb
    DiscreteTopology S.Generated ∧ _root_.LowDimensionalTopology.Geometry.DiscreteGroups.Action.IsFundamentalDomain S.Generated ℍ MeasureTheory.volume
      (_root_.LowDimensionalTopology.Geometry.Hyperbolic.halfPlaneToDisc ⁻¹' (_root_.LowDimensionalTopology.Geometry.Polygon.polygonTangentialPolygon (generalCoreTheta g orders s t) d
        (generalCoreTheta_mem g orders s t ho hdef) hd hb).interior) := by
  apply cofiniteTangential_mixed_poincare
  exact generalCoreAux_positive_angular_periods g orders s t ho hdef

end LowDimensionalTopology.Geometry.Fuchsian
