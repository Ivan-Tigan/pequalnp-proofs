import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3545

open PEqualNP.CircuitLowerBounds

lemma foldl_len {α β : Type*} (h : List α → β → α) (l : List β) (acc : List α) :
    (l.foldl (fun cs g => cs ++ [h cs g]) acc).length = acc.length + l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons g l ih => simp only [List.foldl_cons, ih, List.length_append, List.length_cons,
      List.length_nil]; omega

lemma foldl_prefix {α β : Type*} (h : List α → β → α) (l : List β) (acc : List α) (i : ℕ)
    (hi : i < acc.length) (d : α) :
    (l.foldl (fun cs g => cs ++ [h cs g]) acc).getD i d = acc.getD i d := by
  induction l generalizing acc with
  | nil => rfl
  | cons g l ih =>
    rw [List.foldl_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

lemma foldl_at {α β : Type*} (h : List α → β → α) (l : List β) (acc : List α) (j : ℕ)
    (hj : j < l.length) (d : α) :
    (l.foldl (fun cs g => cs ++ [h cs g]) acc).getD (acc.length + j) d =
      h ((l.take j).foldl (fun cs g => cs ++ [h cs g]) acc) l[j] := by
  conv_lhs => rw [← List.take_append_drop j l, List.foldl_append, List.drop_eq_getElem_cons hj,
    List.foldl_cons]
  have hl : ((l.take j).foldl (fun cs g => cs ++ [h cs g]) acc).length = acc.length + j := by
    rw [foldl_len, List.length_take]; omega
  rw [foldl_prefix _ _ _ _ (by simp [hl]), List.getD_append_right _ _ _ _ (by omega)]
  simp [hl]

lemma foldl_split {α β : Type*} (h : List α → β → α) (l : List β) (acc : List α) (j : ℕ) :
    l.foldl (fun cs g => cs ++ [h cs g]) acc =
      (l.drop j).foldl (fun cs g => cs ++ [h cs g])
        ((l.take j).foldl (fun cs g => cs ++ [h cs g]) acc) := by
  conv_lhs => rw [← List.take_append_drop j l, List.foldl_append]

lemma wires_len (C : Circuit) (x : List Bool) : (C.wires x).length = x.length + C.gates.length :=
  foldl_len _ _ _

lemma wires_input (C : Circuit) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  foldl_prefix _ _ _ _ hi _

lemma wires_gate (C : Circuit) (x : List Bool) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (x.length + j) false =
      C.gates[j].op.eval (C.gates[j].inputs.map fun i =>
        if i < x.length + j then (C.wires x).getD i false else false) := by
  unfold Circuit.wires
  rw [foldl_at _ _ _ _ hj]
  congr 1
  apply List.map_congr_left
  intro i _
  have hl : ((C.gates.take j).foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i =>
      w.getD i false)]) x).length = x.length + j := by
    rw [foldl_len, List.length_take]; omega
  split_ifs with hi
  · conv_rhs => rw [foldl_split _ C.gates x j]
    rw [foldl_prefix _ (C.gates.drop j) _ _ (by rw [hl]; exact hi)]
  · rw [List.getD_eq_default _ _ (by omega)]

lemma wires_append (gs1 gs2 : List Gate) (o o' : ℕ) (x : List Bool) (i : ℕ)
    (hi : i < x.length + gs1.length) :
    (Circuit.wires ⟨gs1 ++ gs2, o⟩ x).getD i false = (Circuit.wires ⟨gs1, o'⟩ x).getD i false := by
  unfold Circuit.wires
  simp only
  rw [List.foldl_append, foldl_prefix _ _ _ _ (by rw [foldl_len]; exact hi)]

lemma cones_at (n : ℕ) (C : Circuit) (r : ℕ) (hr : r < C.gates.length) (a : ℕ) :
    a ∈ (PEqualNP.EdgeOwnership.cones n C).getD r [] ↔
      ∃ w ∈ C.gates[r].inputs, (n ≤ w ∧ w < n + r) ∧
        (a = w - n ∨ a ∈ (PEqualNP.EdgeOwnership.cones n C).getD (w - n) []) := by
  have e1 : PEqualNP.EdgeOwnership.cones n C = C.gates.foldl (fun cs g => cs ++
      [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])]) [] := rfl
  have hl : ((C.gates.take r).foldl (fun cs g => cs ++
      [(g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])]) []).length = r := by
    rw [foldl_len, List.length_take]; simp; omega
  rw [e1]
  have := foldl_at (fun cs (g : Gate) => (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) [])) C.gates [] r hr []
  simp only [List.length_nil, Nat.zero_add] at this
  rw [this, hl]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hw2⟩, h3⟩
    refine ⟨w, hw, hw2, ?_⟩
    rcases h3 with h3 | h3
    · exact Or.inl h3
    · right
      rw [foldl_split _ C.gates [] r, foldl_prefix _ _ _ _ (by rw [hl]; omega)]
      exact h3
  · rintro ⟨w, hw, hw2, h3⟩
    refine ⟨w, ⟨hw, hw2⟩, ?_⟩
    rcases h3 with h3 | h3
    · exact Or.inl h3
    · right
      rw [foldl_split _ C.gates [] r, foldl_prefix _ _ _ _ (by rw [hl]; omega)] at h3
      exact h3

lemma orSets_len (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  let _ := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have e1 : PEqualNP.CleanedNonEdge.orSets n C = C.gates.foldl (fun cs g => cs ++
      [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) []) else [])]) [] := rfl
  rw [e1, foldl_len]
  simp

lemma orSets_at (n : ℕ) (C : Circuit) (t : ℕ) (ht : t < C.gates.length) (g : ℕ) :
    g ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD t [] ↔
      g = t ∨ (C.gates[t].op = GateOp.or ∧ ∃ w ∈ C.gates[t].inputs, (n ≤ w ∧ w < n + t) ∧
        g ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  let _ := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have e1 : PEqualNP.CleanedNonEdge.orSets n C = C.gates.foldl (fun cs g => cs ++
      [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) []) else [])]) [] := rfl
  have hl : ((C.gates.take t).foldl (fun cs g => cs ++
      [cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) []) else [])]) []).length = t := by
    rw [foldl_len, List.length_take]; simp; omega
  rw [e1]
  have := foldl_at (fun cs (g : Gate) => cs.length :: (if g.op = GateOp.or then
        (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
          (fun w => cs.getD (w - n) []) else [])) C.gates [] t ht []
  simp only [List.length_nil, Nat.zero_add] at this
  rw [this, hl]
  simp only [List.mem_cons]
  apply or_congr Iff.rfl
  split_ifs with hop
  · simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, hop, true_and]
    constructor
    · rintro ⟨w, ⟨hw, hw2⟩, h3⟩
      refine ⟨w, hw, hw2, ?_⟩
      rw [foldl_split _ C.gates [] t, foldl_prefix _ _ _ _ (by rw [hl]; omega)]
      exact h3
    · rintro ⟨w, hw, hw2, h3⟩
      refine ⟨w, ⟨hw, hw2⟩, ?_⟩
      rw [foldl_split _ C.gates [] t, foldl_prefix _ _ _ _ (by rw [hl]; omega)] at h3
      exact h3
  · simp [hop]

open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.EdgeOwnership

lemma gateAt_eq (C : Circuit) (j : ℕ) (h : j < C.gates.length) : gateAt C j = C.gates[j] :=
  List.getD_eq_getElem _ _ h

lemma ofFn_getD {n : ℕ} (y : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn y).getD i false = y ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma C_input (n : ℕ) (C : Circuit) (y : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal n C i y = y ⟨i, hi⟩ := by
  unfold wireVal
  rw [wires_input _ _ _ (by simpa using hi), ofFn_getD]

lemma C_gate (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (g : ℕ) (hg : g < C.gates.length)
    (y : Fin n → Bool) :
    wireVal n C (n + g) y =
      (gateAt C g).op.eval ((gateAt C g).inputs.map fun i => wireVal n C i y) := by
  unfold wireVal
  have := wires_gate C (List.ofFn y) g hg
  rw [List.length_ofFn] at this
  rw [this, gateAt_eq _ _ hg]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos (hRB g hg i (by rwa [gateAt_eq _ _ hg]))]

lemma cone_read (n : ℕ) (C : Circuit) (r : ℕ) (hr : r < C.gates.length) (a : ℕ)
    (ha : n + a ∈ (gateAt C r).inputs) (har : a < r) : InCone n C a r := by
  unfold InCone
  rw [cones_at n C r hr]
  refine ⟨n + a, by rwa [gateAt_eq _ _ hr] at ha, ⟨by omega, by omega⟩, Or.inl (by omega)⟩

lemma cone_trans (n : ℕ) (C : Circuit) (r : ℕ) (hr : r < C.gates.length) (a g : ℕ)
    (hag : InCone n C a g) (hg : n + g ∈ (gateAt C r).inputs) (hgr : g < r) :
    InCone n C a r := by
  unfold InCone at hag ⊢
  rw [cones_at n C r hr]
  refine ⟨n + g, by rwa [gateAt_eq _ _ hr] at hg, ⟨by omega, by omega⟩, Or.inr ?_⟩
  rwa [show n + g - n = g by omega]

lemma or_mono (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (t : ℕ) :
    ∀ g, g ∈ (orSets n C).getD t [] → ∀ y : Fin n → Bool,
      wireVal n C (n + g) y = true → wireVal n C (n + t) y = true := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro g hm y hy
    by_cases ht : t < C.gates.length
    · rw [orSets_at n C t ht] at hm
      rcases hm with rfl | ⟨hor, w, hw, ⟨hw1, hw2⟩, hm⟩
      · exact hy
      · have h1 := ih (w - n) (by omega) g hm y hy
        rw [C_gate n C hRB t ht, gateAt_eq _ _ ht, hor]
        show List.any _ id = true
        rw [List.any_eq_true]
        refine ⟨wireVal n C w y, List.mem_map.mpr ⟨w, hw, rfl⟩, ?_⟩
        rwa [show n + (w - n) = w by omega] at h1
    · rw [List.getD_eq_default _ _ (by rw [orSets_len]; omega)] at hm
      simp at hm

lemma or_reach (n : ℕ) (C : Circuit) (hRB : ReadsBack n C) (w g : ℕ) (h : OrReaches n C w g)
    (y : Fin n → Bool) (hy : wireVal n C (n + g) y = true) : wireVal n C w y = true := by
  obtain ⟨hn, hm⟩ := h
  have := or_mono n C hRB (w - n) g hm y hy
  rwa [show n + (w - n) = w by omega] at this

def Dc (C : Circuit) (G0 : List Gate) (rho : ℕ → ℕ → ℕ) (out : ℕ) : Circuit :=
  ⟨G0 ++ C.gates.mapIdx (fun r7 g7 =>
    ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : Gate)), out⟩

lemma D_gate (n : ℕ) (C : Circuit) (G0 : List Gate) (rho : ℕ → ℕ → ℕ) (out : ℕ) (r : ℕ)
    (hr : r < C.gates.length) (y : Fin n → Bool) :
    wireVal n (Dc C G0 rho out) (n + G0.length + r) y =
      (gateAt C r).op.eval ((gateAt C r).inputs.map fun i =>
        if rho r i < n + G0.length + r then wireVal n (Dc C G0 rho out) (rho r i) y
        else false) := by
  unfold wireVal
  have hlt : G0.length + r < (Dc C G0 rho out).gates.length := by simp [Dc]; omega
  have := wires_gate (Dc C G0 rho out) (List.ofFn y) (G0.length + r) hlt
  rw [List.length_ofFn] at this
  rw [show n + G0.length + r = n + (G0.length + r) by omega, this]
  have hg : (Dc C G0 rho out).gates[G0.length + r] =
      ({ op := C.gates[r].op, inputs := C.gates[r].inputs.map (fun i7 => rho r i7) } : Gate) := by
    simp only [Dc]
    rw [List.getElem_append_right (by omega)]
    simp
  rw [hg, gateAt_eq _ _ hr, List.map_map]
  rfl

lemma D_pre (n : ℕ) (C : Circuit) (G0 : List Gate) (rho : ℕ → ℕ → ℕ) (out : ℕ) (i : ℕ)
    (hi : i < n + G0.length) (y : Fin n → Bool) :
    wireVal n (Dc C G0 rho out) i y = wireVal n ⟨G0, 0⟩ i y := by
  unfold wireVal Dc
  exact wires_append _ _ _ _ _ _ (by simpa using hi)

lemma D_input (n : ℕ) (C : Circuit) (G0 : List Gate) (rho : ℕ → ℕ → ℕ) (out : ℕ) (i : ℕ)
    (hi : i < n) (y : Fin n → Bool) :
    wireVal n (Dc C G0 rho out) i y = y ⟨i, hi⟩ := C_input n _ y i hi

end PEqualNP.Outside.L_meta_3545

theorem PEqualNP.Outside.L_meta_3545 : ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (qH : (Fin n → Bool) → Bool) (C : PEqualNP.CircuitLowerBounds.Circuit) (m : ℕ) (u T W z : ℕ → ℕ) (NR : ℕ → ℕ → Prop) (P : ℕ → (Fin n → Bool) → Bool) (G0 : List PEqualNP.CircuitLowerBounds.Gate) (rho : ℕ → ℕ → ℕ) (D : PEqualNP.CircuitLowerBounds.Circuit), (∀ y0 : Fin n → Bool, qH y0 = true ↔ ∃ a0 b0 : Fin n, H.Adj a0 b0 ∧ y0 a0 = true ∧ y0 b0 = true) → PEqualNP.TopForm.IsAO2 n C → (∀ y1 : Fin n → Bool, C.eval (List.ofFn y1) = qH y1) → (∀ k0 r0 : ℕ, NR k0 r0 ↔ r0 < C.gates.length ∧ n + u k0 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).inputs ∧ (r0 = T k0 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k0) r0 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r0).op = PEqualNP.CircuitLowerBounds.GateOp.or))) → (∀ (k1 : ℕ) (y2 : Fin n → Bool), P k1 y2 = decide (∃ w1 : Fin n, y2 w1 = true ∧ PEqualNP.CleanedNonEdge.wireVal n C (n + u k1) (fun j1 : Fin n => decide (j1 = w1 ∨ (j1 : ℕ) = z k1)) = true)) → (∀ k2 < m, u k2 < C.gates.length ∧ T k2 < C.gates.length ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ z k2 < n ∧ ((PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [W k2, z k2] ∨ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T k2)).inputs = [z k2, W k2]) ∧ (∀ y3 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + T k2) y3 = true → qH y3 = true) ∧ ∀ g2 < C.gates.length, PEqualNP.EdgeOwnership.InCone n C (T k2) g2 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g2).op = PEqualNP.CircuitLowerBounds.GateOp.or) → (∀ k3 < m, ∀ g3 < C.gates.length, PEqualNP.CleanedNonEdge.OrReaches n C (W k3) g3 → (PEqualNP.MetaComplexity.NestedCover.gateAt C g3).op = PEqualNP.CircuitLowerBounds.GateOp.or → PEqualNP.EdgeOwnership.InCone n C (u k3) g3 → C.output ≠ n + g3 ∧ ∀ r3 < C.gates.length, n + g3 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).inputs → r3 = T k3 ∨ (PEqualNP.CleanedNonEdge.OrReaches n C (W k3) r3 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt C r3).op = PEqualNP.CircuitLowerBounds.GateOp.or)) → (∀ k4 < m, ∀ k5 < m, ∀ r4 : ℕ, NR k5 r4 → r4 ≠ u k4 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r4 (u k4)) → (∀ i6 < G0.length, ∀ w6 ∈ (G0.getD i6 ⟨PEqualNP.CircuitLowerBounds.GateOp.or, []⟩).inputs, w6 < n + i6) → D = ⟨G0 ++ C.gates.mapIdx (fun r7 g7 => ({ op := g7.op, inputs := g7.inputs.map (fun i7 => rho r7 i7) } : PEqualNP.CircuitLowerBounds.Gate)), if C.output < n then C.output else C.output + G0.length⟩ → (∀ r8 < C.gates.length, ∀ i8 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r8).inputs, (∀ k8 < m, ¬ (NR k8 r8 ∧ i8 = n + u k8)) → rho r8 i8 = if i8 < n then i8 else i8 + G0.length) → (∀ r9 : ℕ, ∀ k9 < m, NR k9 r9 → (rho r9 (n + u k9) < n + G0.length ∧ ∀ y9 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n (⟨G0, 0⟩ : PEqualNP.CircuitLowerBounds.Circuit) (rho r9 (n + u k9)) y9 = P k9 y9) ∨ (∃ g9 < r9, rho r9 (n + u k9) = n + G0.length + g9 ∧ (∀ y10 : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C (n + g9) y10 = P k9 y10) ∧ ∀ k10 < m, ∀ r10 : ℕ, NR k10 r10 → r10 ≠ g9 ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r10 g9) ∨ ((∀ y11 : Fin n → Bool, P k9 y11 = false) ∧ n + G0.length + r9 ≤ rho r9 (n + u k9))) → ∀ y12 : Fin n → Bool, D.eval (List.ofFn y12) = qH y12 := by
  intro n H qH C m u T W z NR P G0 rho D hqH hAO hC hNR hP hpairs hup hnodep hG0 hD hrhoP hrhoN y12
  obtain ⟨hAndOr, hRB, -⟩ := hAO
  have hop : ∀ g < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op =
      PEqualNP.CircuitLowerBounds.GateOp.and ∨
      (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or :=
    fun g hg => hAndOr _ (by
      rw [PEqualNP.Outside.L_meta_3545.gateAt_eq _ _ hg]; exact List.getElem_mem hg)
  have hRBg : ∀ g < C.gates.length, ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs,
      i < n + g := hRB
  have hDk : D = PEqualNP.Outside.L_meta_3545.Dc C G0 rho
      (if C.output < n then C.output else C.output + G0.length) := hD
  clear hD
  subst hDk
  generalize hout : (if C.output < n then C.output else C.output + G0.length) = out
  -- plain reads
  have plain : ∀ r < C.gates.length, ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C r).inputs,
      (∀ k < m, ¬ (NR k r ∧ i = n + u k)) → ∀ y : Fin n → Bool,
      (if rho r i < n + G0.length + r then
        PEqualNP.CleanedNonEdge.wireVal n (PEqualNP.Outside.L_meta_3545.Dc C G0 rho out) (rho r i) y
        else false) =
      (if i < n then PEqualNP.CleanedNonEdge.wireVal n C i y else
        PEqualNP.CleanedNonEdge.wireVal n (PEqualNP.Outside.L_meta_3545.Dc C G0 rho out)
          (n + G0.length + (i - n)) y) := by
    intro r hr i hi hnn y
    have hlt := hRBg r hr i hi
    rw [hrhoP r hr i hi hnn]
    by_cases hin : i < n
    · simp only [hin, if_true]
      rw [if_pos (by omega), PEqualNP.Outside.L_meta_3545.D_input _ _ _ _ _ _ hin,
        PEqualNP.Outside.L_meta_3545.C_input _ _ _ _ hin]
    · simp only [hin, if_false]
      rw [if_pos (by omega), show i + G0.length = n + G0.length + (i - n) by omega]
  -- clean gates
  have hE : ∀ g, g < C.gates.length →
      (∀ k < m, ∀ r, NR k r → r ≠ g ∧ ¬ PEqualNP.EdgeOwnership.InCone n C r g) →
      ∀ y : Fin n → Bool,
      PEqualNP.CleanedNonEdge.wireVal n (PEqualNP.Outside.L_meta_3545.Dc C G0 rho out)
        (n + G0.length + g) y = PEqualNP.CleanedNonEdge.wireVal n C (n + g) y := by
    intro g
    induction g using Nat.strong_induction_on with
    | _ g ih =>
      intro hg hcl y
      rw [PEqualNP.Outside.L_meta_3545.D_gate _ _ _ _ _ _ hg,
        PEqualNP.Outside.L_meta_3545.C_gate _ _ hRB _ hg]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hnn : ∀ k < m, ¬ (NR k g ∧ i = n + u k) := fun k hk h => (hcl k hk g h.1).1 rfl
      rw [plain g hg i hi hnn y]
      by_cases hin : i < n
      · simp only [hin, if_true]
      · simp only [hin, if_false]
        have hlt := hRBg g hg i hi
        rw [ih (i - n) (by omega) (by omega) ?_ y, show n + (i - n) = i by omega]
        intro k hk r hr
        have hc := hcl k hk r hr
        constructor
        · rintro rfl
          exact hc.2 (PEqualNP.Outside.L_meta_3545.cone_read n C g hg (i - n)
            (by rwa [show n + (i - n) = i by omega]) (by omega))
        · intro hin2
          exact hc.2 (PEqualNP.Outside.L_meta_3545.cone_trans n C g hg r (i - n) hin2
            (by rwa [show n + (i - n) = i by omega]) (by omega))
  -- narrowed reads give P
  have hNRV : ∀ j < m, ∀ r, NR j r → ∀ y : Fin n → Bool,
      (if rho r (n + u j) < n + G0.length + r then
        PEqualNP.CleanedNonEdge.wireVal n (PEqualNP.Outside.L_meta_3545.Dc C G0 rho out)
          (rho r (n + u j)) y else false) = P j y := by
    intro j hj r hr y
    have hrL := ((hNR j r).1 hr).1
    rcases hrhoN r j hj hr with ⟨h1, h2⟩ | ⟨g9, hg9, h1, h2, h3⟩ | ⟨h1, h2⟩
    · rw [if_pos (by omega), PEqualNP.Outside.L_meta_3545.D_pre _ _ _ _ _ _ h1, h2]
    · rw [if_pos (by omega), h1, hE g9 (by omega) h3 y, h2]
    · rw [if_neg (by omega), h1 y]
  -- facts about tops
  have hTin : ∀ j < m, ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T j)).inputs,
      n ≤ i → i = W j := by
    intro j hj i hi hn
    obtain ⟨-, -, -, hzn, hin, -⟩ := hpairs j hj
    rcases hin with h | h <;> rw [h] at hi <;> simp at hi <;> omega
  have hzin : ∀ j < m, z j ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C (T j)).inputs := by
    intro j hj
    obtain ⟨-, -, -, -, hin, -⟩ := hpairs j hj
    rcases hin with h | h <;> rw [h] <;> simp
  -- narrowed readers and readers of tainted gates
  have hnar : ∀ j < m, ∀ g, NR j g → g = T j ∨ (g < C.gates.length ∧
      PEqualNP.CleanedNonEdge.OrReaches n C (W j) g ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      PEqualNP.EdgeOwnership.InCone n C (u j) g) := by
    intro j hj g hg
    obtain ⟨hgL, hin, h3⟩ := (hNR j g).1 hg
    rcases h3 with h3 | ⟨h4, h5⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hgL, h4, h5, PEqualNP.Outside.L_meta_3545.cone_read n C g hgL (u j) hin
        (by have := hRBg g hgL _ hin; omega)⟩
  have hreader : ∀ j < m, ∀ a, (a < C.gates.length ∧ PEqualNP.CleanedNonEdge.OrReaches n C (W j) a ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C a).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      PEqualNP.EdgeOwnership.InCone n C (u j) a) → ∀ g < C.gates.length,
      n + a ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs → g = T j ∨
      (g < C.gates.length ∧ PEqualNP.CleanedNonEdge.OrReaches n C (W j) g ∧
      (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
      PEqualNP.EdgeOwnership.InCone n C (u j) g) := by
    intro j hj a ⟨haL, ha1, ha2, ha3⟩ g hg hga
    rcases (hup j hj a haL ha1 ha2 ha3).2 g hg hga with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨hg, h1, h2, PEqualNP.Outside.L_meta_3545.cone_trans n C g hg (u j) a ha3 hga
        (by have := hRBg g hg _ hga; omega)⟩
  -- a cofactor star true with z on gives an edge
  have hPZ : ∀ j < m, (∃ r, NR j r) → ∀ (y : Fin n → Bool) (hz : z j < n), P j y = true →
      y ⟨z j, hz⟩ = true → qH y = true := by
    intro j hj ⟨r, hr⟩ y hz hPj hyz
    obtain ⟨huL, hTL, hTand, -, hin, hbelow, -⟩ := hpairs j hj
    rw [hP j y, decide_eq_true_iff] at hPj
    obtain ⟨w1, hyw, hu⟩ := hPj
    set e : Fin n → Bool := fun j1 : Fin n => decide (j1 = w1 ∨ (j1 : ℕ) = z j) with he
    have hW : PEqualNP.CleanedNonEdge.wireVal n C (W j) e = true := by
      obtain ⟨hrL, hrin, h3⟩ := (hNR j r).1 hr
      rcases h3 with rfl | ⟨h4, h5⟩
      · rw [← hTin j hj (n + u j) hrin (by omega)]; exact hu
      · apply PEqualNP.Outside.L_meta_3545.or_reach n C hRB (W j) r h4 e
        rw [PEqualNP.Outside.L_meta_3545.C_gate n C hRB r hrL, h5]
        show List.any _ id = true
        rw [List.any_eq_true]
        exact ⟨_, List.mem_map.mpr ⟨n + u j, hrin, rfl⟩, hu⟩
    have hTv : PEqualNP.CleanedNonEdge.wireVal n C (n + T j) e = true := by
      rw [PEqualNP.Outside.L_meta_3545.C_gate n C hRB (T j) hTL, hTand]
      show List.all _ id = true
      rw [List.all_eq_true]
      intro b hb
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
      rcases hin with h | h <;> rw [h] at hi <;> simp only [List.mem_cons, List.mem_nil_iff,
        or_false] at hi <;> rcases hi with rfl | rfl
      all_goals first
        | exact hW
        | (rw [PEqualNP.Outside.L_meta_3545.C_input n C e _ hz]; simp [he])
    obtain ⟨a0, b0, hadj, ha, hb⟩ := (hqH e).1 (hbelow e hTv)
    have hne := hadj.ne
    simp only [he, decide_eq_true_eq] at ha hb
    apply (hqH y).2
    have hzz : ∀ c : Fin n, (c : ℕ) = z j → y c = true := by
      intro c hc
      have : c = ⟨z j, hz⟩ := Fin.ext hc
      rw [this]; exact hyz
    rcases ha with rfl | ha <;> rcases hb with rfl | hb
    · exact absurd rfl hne
    · exact ⟨a0, b0, hadj, hyw, hzz b0 hb⟩
    · exact ⟨a0, b0, hadj, hzz a0 ha, hyw⟩
    · exact absurd (Fin.ext (ha.trans hb.symm)) hne
  -- upper bound
  have hU : ∀ (y : Fin n → Bool) (g : ℕ), g < C.gates.length →
      PEqualNP.CleanedNonEdge.wireVal n (PEqualNP.Outside.L_meta_3545.Dc C G0 rho out)
        (n + G0.length + g) y = true →
      PEqualNP.CleanedNonEdge.wireVal n C (n + g) y = true ∨ qH y = true ∨
      ∃ j < m, (∃ r, NR j r) ∧ (g < C.gates.length ∧ PEqualNP.CleanedNonEdge.OrReaches n C (W j) g ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        PEqualNP.EdgeOwnership.InCone n C (u j) g) ∧ P j y = true := by
    intro y g
    induction g using Nat.strong_induction_on with
    | _ g ih =>
      intro hg hDv
      have PI : ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs,
          (if rho g i < n + G0.length + g then
            PEqualNP.CleanedNonEdge.wireVal n (PEqualNP.Outside.L_meta_3545.Dc C G0 rho out)
              (rho g i) y else false) = true →
          PEqualNP.CleanedNonEdge.wireVal n C i y = true ∨ qH y = true ∨
          ∃ j < m, (∃ r, NR j r) ∧ (g = T j ∨ (g < C.gates.length ∧
            PEqualNP.CleanedNonEdge.OrReaches n C (W j) g ∧
            (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op =
              PEqualNP.CircuitLowerBounds.GateOp.or ∧
            PEqualNP.EdgeOwnership.InCone n C (u j) g)) ∧ P j y = true := by
        intro i hi hd
        by_cases hn : ∃ k < m, NR k g ∧ i = n + u k
        · obtain ⟨k, hk, hNRk, rfl⟩ := hn
          rw [hNRV k hk g hNRk y] at hd
          exact Or.inr (Or.inr ⟨k, hk, ⟨g, hNRk⟩, hnar k hk g hNRk, hd⟩)
        · have hnn : ∀ k < m, ¬ (NR k g ∧ i = n + u k) := fun k hk h => hn ⟨k, hk, h⟩
          rw [plain g hg i hi hnn y] at hd
          by_cases hin : i < n
          · rw [if_pos hin] at hd; exact Or.inl hd
          · rw [if_neg hin] at hd
            have hlt := hRBg g hg i hi
            rcases ih (i - n) (by omega) (by omega) hd with h | h | ⟨j, hj, hex, hR, hPj⟩
            · left; rwa [show n + (i - n) = i by omega] at h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr ⟨j, hj, hex, hreader j hj (i - n) hR g hg
                (by rwa [show n + (i - n) = i by omega]), hPj⟩)
      rw [PEqualNP.Outside.L_meta_3545.D_gate _ _ _ _ _ _ hg] at hDv
      rcases hop g hg with hand | hor
      · rw [hand] at hDv
        change List.all _ id = true at hDv
        rw [List.all_eq_true] at hDv
        have hDall : ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs,
            (if rho g i < n + G0.length + g then
              PEqualNP.CleanedNonEdge.wireVal n (PEqualNP.Outside.L_meta_3545.Dc C G0 rho out)
                (rho g i) y else false) = true :=
          fun i hi => hDv _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
        by_cases hq : qH y = true
        · exact Or.inr (Or.inl hq)
        by_cases hall : ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs,
            PEqualNP.CleanedNonEdge.wireVal n C i y = true
        · left
          rw [PEqualNP.Outside.L_meta_3545.C_gate n C hRB g hg, hand]
          change List.all _ id = true
          rw [List.all_eq_true]
          intro b hb
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
          exact hall i hi
        · simp only [not_forall] at hall
          obtain ⟨i, hi, hci⟩ := hall
          rcases PI i hi (hDall i hi) with h | h | ⟨j, hj, hex, hR, hPj⟩
          · exact absurd h hci
          · exact absurd h hq
          · rcases hR with rfl | hR
            · obtain ⟨-, hTL, -, hzn, -⟩ := hpairs j hj
              have hd := hDall (z j) (hzin j hj)
              rw [plain (T j) hTL (z j) (hzin j hj) (fun k hk h => by omega) y, if_pos hzn,
                PEqualNP.Outside.L_meta_3545.C_input _ _ _ _ hzn] at hd
              exact Or.inr (Or.inl (hPZ j hj hex y hzn hPj hd))
            · exact absurd (hand.symm.trans hR.2.2.1) (fun h => PEqualNP.CircuitLowerBounds.GateOp.noConfusion h)
      · rw [hor] at hDv
        change List.any _ id = true at hDv
        rw [List.any_eq_true] at hDv
        obtain ⟨b, hb, hbt⟩ := hDv
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
        rcases PI i hi hbt with h | h | ⟨j, hj, hex, hR, hPj⟩
        · left
          rw [PEqualNP.Outside.L_meta_3545.C_gate n C hRB g hg, hor]
          change List.any _ id = true
          rw [List.any_eq_true]
          exact ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, h⟩
        · exact Or.inr (Or.inl h)
        · rcases hR with rfl | hR
          · obtain ⟨-, -, hTand, -⟩ := hpairs j hj
            exact absurd (hTand.symm.trans hor) (fun h => PEqualNP.CircuitLowerBounds.GateOp.noConfusion h)
          · exact Or.inr (Or.inr ⟨j, hj, hex, hR, hPj⟩)
  -- lower bound at an edge
  have hL : ∀ (y : Fin n → Bool) (a0 b0 : Fin n), H.Adj a0 b0 → y a0 = true → y b0 = true →
      ∀ g, g < C.gates.length →
      (¬ ∃ j < m, (g < C.gates.length ∧ PEqualNP.CleanedNonEdge.OrReaches n C (W j) g ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
        PEqualNP.EdgeOwnership.InCone n C (u j) g) ∧ ¬ (z j = a0.val ∨ z j = b0.val)) →
      PEqualNP.CleanedNonEdge.wireVal n C (n + g) (fun w => decide (w = a0 ∨ w = b0)) = true →
      PEqualNP.CleanedNonEdge.wireVal n (PEqualNP.Outside.L_meta_3545.Dc C G0 rho out)
        (n + G0.length + g) y = true := by
    intro y a0 b0 hadj ha hb g
    induction g using Nat.strong_induction_on with
    | _ g ih =>
      intro hg hnex hCv
      have hey : ∀ w, (decide (w = a0 ∨ w = b0)) = true → y w = true := by
        intro w hw
        simp only [decide_eq_true_eq] at hw
        rcases hw with rfl | rfl
        · exact ha
        · exact hb
      have PI : ∀ i ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C g).inputs,
          PEqualNP.CleanedNonEdge.wireVal n C i (fun w => decide (w = a0 ∨ w = b0)) = true →
          (if rho g i < n + G0.length + g then
            PEqualNP.CleanedNonEdge.wireVal n (PEqualNP.Outside.L_meta_3545.Dc C G0 rho out)
              (rho g i) y else false) = true ∨
          ∃ j < m, g = T j ∧ ¬ (z j = a0.val ∨ z j = b0.val) := by
        intro i hi hci
        by_cases hn : ∃ k < m, NR k g ∧ i = n + u k
        · obtain ⟨k, hk, hNRk, rfl⟩ := hn
          rw [hNRV k hk g hNRk y]
          by_cases hz : z k = a0.val ∨ z k = b0.val
          · left
            rw [hP k y, decide_eq_true_iff]
            rcases hz with hz | hz
            · refine ⟨b0, hb, ?_⟩
              convert hci using 2
              funext j1
              apply decide_eq_decide.mpr
              rw [hz, ← Fin.ext_iff]
              tauto
            · refine ⟨a0, ha, ?_⟩
              convert hci using 2
              funext j1
              apply decide_eq_decide.mpr
              rw [hz, ← Fin.ext_iff]
          · rcases hnar k hk g hNRk with rfl | hR
            · exact Or.inr ⟨k, hk, rfl, hz⟩
            · exact absurd ⟨k, hk, hR, hz⟩ hnex
        · have hnn : ∀ k < m, ¬ (NR k g ∧ i = n + u k) := fun k hk h => hn ⟨k, hk, h⟩
          rw [plain g hg i hi hnn y]
          by_cases hin : i < n
          · left
            rw [if_pos hin, PEqualNP.Outside.L_meta_3545.C_input _ _ _ _ hin]
            rw [PEqualNP.Outside.L_meta_3545.C_input _ _ _ _ hin] at hci
            exact hey _ hci
          · rw [if_neg hin]
            have hlt := hRBg g hg i hi
            by_cases hexa : ∃ j < m, ((i - n) < C.gates.length ∧
                PEqualNP.CleanedNonEdge.OrReaches n C (W j) (i - n) ∧
                (PEqualNP.MetaComplexity.NestedCover.gateAt C (i - n)).op =
                  PEqualNP.CircuitLowerBounds.GateOp.or ∧
                PEqualNP.EdgeOwnership.InCone n C (u j) (i - n)) ∧ ¬ (z j = a0.val ∨ z j = b0.val)
            · obtain ⟨j, hj, hR, hz⟩ := hexa
              rcases hreader j hj (i - n) hR g hg (by rwa [show n + (i - n) = i by omega])
                with rfl | hRg
              · exact Or.inr ⟨j, hj, rfl, hz⟩
              · exact absurd ⟨j, hj, hRg, hz⟩ hnex
            · left
              exact ih (i - n) (by omega) (by omega) hexa
                (by rwa [show n + (i - n) = i by omega])
      rw [PEqualNP.Outside.L_meta_3545.D_gate _ _ _ _ _ _ hg]
      rw [PEqualNP.Outside.L_meta_3545.C_gate n C hRB g hg] at hCv
      rcases hop g hg with hand | hor
      · rw [hand] at hCv ⊢
        change List.all _ id = true at hCv
        change List.all _ id = true
        rw [List.all_eq_true] at hCv ⊢
        intro b hb
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
        rcases PI i hi (hCv _ (List.mem_map.mpr ⟨i, hi, rfl⟩)) with h | ⟨j, hj, rfl, hz⟩
        · exact h
        · exfalso
          obtain ⟨-, -, -, hzn, -⟩ := hpairs j hj
          have h2 := hCv _ (List.mem_map.mpr ⟨z j, hzin j hj, rfl⟩)
          rw [PEqualNP.Outside.L_meta_3545.C_input _ _ _ _ hzn] at h2
          have h3 : (⟨z j, hzn⟩ : Fin n) = a0 ∨ (⟨z j, hzn⟩ : Fin n) = b0 := by simpa using h2
          apply hz
          rcases h3 with h3 | h3
          · left; rw [← h3]
          · right; rw [← h3]
      · rw [hor] at hCv ⊢
        change List.any _ id = true at hCv
        change List.any _ id = true
        rw [List.any_eq_true] at hCv ⊢
        obtain ⟨b, hb, hbt⟩ := hCv
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
        rcases PI i hi hbt with h | ⟨j, hj, rfl, hz⟩
        · exact ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, h⟩
        · exfalso
          obtain ⟨-, -, hTand, -⟩ := hpairs j hj
          exact PEqualNP.CircuitLowerBounds.GateOp.noConfusion (hTand.symm.trans hor)
  -- the output
  have hCe : ∀ y : Fin n → Bool, PEqualNP.CleanedNonEdge.wireVal n C C.output y = qH y := hC
  change PEqualNP.CleanedNonEdge.wireVal n (PEqualNP.Outside.L_meta_3545.Dc C G0 rho out) out y12 = qH y12
  rw [← hCe y12]
  by_cases h1 : C.output < n
  · rw [if_pos h1] at hout
    subst hout
    rw [PEqualNP.Outside.L_meta_3545.D_input _ _ _ _ _ _ h1,
      PEqualNP.Outside.L_meta_3545.C_input _ _ _ _ h1]
  · rw [if_neg h1] at hout
    subst hout
    by_cases h2 : C.output < n + C.gates.length
    · obtain ⟨g, hg⟩ : ∃ g, C.output = n + g := ⟨C.output - n, by omega⟩
      have hgL : g < C.gates.length := by omega
      have nottaint : ∀ j < m, ¬ (g < C.gates.length ∧ PEqualNP.CleanedNonEdge.OrReaches n C (W j) g ∧
          (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧
          PEqualNP.EdgeOwnership.InCone n C (u j) g) :=
        fun j hj hR => (hup j hj g hR.1 hR.2.1 hR.2.2.1 hR.2.2.2).1 hg
      rw [show C.output + G0.length = n + G0.length + g by omega, hg]
      have hCq : PEqualNP.CleanedNonEdge.wireVal n C (n + g) y12 = qH y12 := by
        rw [← hg]; exact hCe y12
      rw [hCq]
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hd
        rcases hU y12 g hgL hd with h | h | ⟨j, hj, -, hR, -⟩
        · rwa [hCq] at h
        · exact h
        · exact absurd hR (nottaint j hj)
      · intro hq
        obtain ⟨a0, b0, hadj, ha, hb⟩ := (hqH y12).1 hq
        apply hL y12 a0 b0 hadj ha hb g hgL (fun ⟨j, hj, hR, _⟩ => nottaint j hj hR)
        rw [← hg, hCe]
        exact (hqH _).2 ⟨a0, b0, hadj, by simp, by simp⟩
    · unfold PEqualNP.CleanedNonEdge.wireVal
      rw [List.getD_eq_default _ _ (by
          rw [PEqualNP.Outside.L_meta_3545.wires_len]; simp [PEqualNP.Outside.L_meta_3545.Dc]; omega),
        List.getD_eq_default _ _ (by rw [PEqualNP.Outside.L_meta_3545.wires_len]; simp; omega)]
