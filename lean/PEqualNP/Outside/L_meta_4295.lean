import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4295

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.CircuitMoves PEqualNP.EdgeOwnership

def scan {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) : List α :=
  gs.foldl (fun w g => w ++ [step w g]) w

lemma scan_cons {α : Type} (step : List α → Gate → α) (g : Gate) (gs : List Gate) (w : List α) :
    scan step (g :: gs) w = scan step gs (w ++ [step w g]) := rfl

lemma scan_append {α : Type} (step : List α → Gate → α) (gs hs : List Gate) (w : List α) :
    scan step (gs ++ hs) w = scan step hs (scan step gs w) := by
  simp [scan, List.foldl_append]

lemma scan_length {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α) :
    (scan step gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih]
    simp
    omega

lemma scan_prefix {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (i : ℕ) (hi : i < w.length) :
    (scan step gs w).getD i d = w.getD i d := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [scan_cons, ih _ (by simp; omega)]
    exact List.getD_append _ _ _ _ hi

lemma scan_getD_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length) :
    (scan step gs w).getD (w.length + j) d = step (scan step (gs.take j) w) gs[j] := by
  have hp : (scan step (gs.take j) w).length = w.length + j := by
    simp [scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) (scan step (gs.take j) w) := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) _ d (w.length + j) (by simp [hp])]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  have hsub : w.length + j - (scan step (gs.take j) w).length = 0 := by omega
  rw [hsub]
  simp only [List.getD_cons_zero]

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

lemma wires_scan (D : Circuit) (X : List Bool) : D.wires X = scan boolStep D.gates X := rfl

lemma wires_len (D : Circuit) (X : List Bool) : (D.wires X).length = X.length + D.gates.length := by
  rw [wires_scan, scan_length]

lemma wv_ge (D : Circuit) (X : List Bool) (i : ℕ) (hi : X.length + D.gates.length ≤ i) :
    (D.wires X).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; exact hi)]
  rfl

lemma wv_input (D : Circuit) (X : List Bool) (i : ℕ) (hi : i < X.length) :
    (D.wires X).getD i false = X.getD i false := by
  rw [wires_scan]
  exact scan_prefix _ _ _ _ _ hi

lemma wv_gate (D : Circuit) (X : List Bool) (j : ℕ) (hj : j < D.gates.length)
    (hrb : ∀ i ∈ (D.gates[j]).inputs, i < X.length + j) :
    (D.wires X).getD (X.length + j) false = boolStep (D.wires X) D.gates[j] := by
  rw [wires_scan, scan_getD_gate _ _ _ _ j hj]
  unfold boolStep
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi' := hrb i hi
  have hlen : (scan boolStep (D.gates.take j) X).length = X.length + j := by
    rw [scan_length]; simp [Nat.min_eq_left hj.le]
  have e := scan_prefix boolStep (D.gates.drop j) (scan boolStep (D.gates.take j) X) false i
    (by rw [hlen]; exact hi')
  rw [← scan_append, List.take_append_drop] at e
  exact e.symm

lemma bs_and (W : List Bool) (g : Gate) (a b : ℕ) (hin : g.inputs = [a, b])
    (hop : g.op = GateOp.and) :
    boolStep W g = (W.getD a false && W.getD b false) := by
  simp [boolStep, hop, hin, GateOp.eval]

lemma bs_or (W : List Bool) (g : Gate) (a b : ℕ) (hin : g.inputs = [a, b])
    (hop : g.op = GateOp.or) :
    boolStep W g = (W.getD a false || W.getD b false) := by
  simp [boolStep, hop, hin, GateOp.eval]

lemma ao2_gate {n : ℕ} {C : Circuit} (hA : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or) ∧
      ∃ a b, C.gates[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j := by
  have hmem := List.getElem_mem hj
  have hop := hA.1 _ hmem
  have hlen := hA.2.2 _ hmem
  have hrb := hA.2.1 j hj
  have hgat : gateAt C j = C.gates[j] := by
    simp [gateAt, List.getD_eq_getElem?_getD, hj]
  rw [hgat] at hrb
  refine ⟨hop, ?_⟩
  rcases h : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rw [h] at hlen; simp at hlen
  · rw [h] at hlen; simp at hlen
  · rw [h] at hrb
    exact ⟨a, b, rfl, hrb a (by simp), hrb b (by simp)⟩
  · rw [h] at hlen; simp at hlen

def rdG (n m p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩

lemma e_gates {n m p : ℕ} {C : Circuit} (hm : m < C.gates.length) :
    (eraseGate n C m p).gates = C.gates.take m ++ (C.gates.drop (m + 1)).map (rdG n m p) := by
  unfold eraseGate
  rw [if_pos hm]
  rfl

lemma e_out {n m p : ℕ} {C : Circuit} (hm : m < C.gates.length) :
    (eraseGate n C m p).output = eraseRedirect n m p C.output := by
  simp [eraseGate, hm]

lemma e_len {n m p : ℕ} {C : Circuit} (hm : m < C.gates.length) :
    (eraseGate n C m p).gates.length = C.gates.length - 1 := by
  rw [e_gates hm]
  simp
  omega

lemma e_get_lt {n m p : ℕ} {C : Circuit} (hm : m < C.gates.length) {j : ℕ} (hj : j < m) :
    (eraseGate n C m p).gates[j]? = C.gates[j]? := by
  rw [e_gates hm, List.getElem?_append_left (by simp; omega)]
  simp [hj]

lemma e_get_ge {n m p : ℕ} {C : Circuit} (hm : m < C.gates.length) {j : ℕ} (hj : m ≤ j) :
    (eraseGate n C m p).gates[j]? = (C.gates[j + 1]?).map (rdG n m p) := by
  rw [e_gates hm, List.getElem?_append_right (by simp; omega)]
  rw [List.getElem?_map, List.getElem?_drop]
  congr 2
  simp
  omega

lemma get_of_get? {l : List Gate} {j : ℕ} {g : Gate} (hj : j < l.length) (h : l[j]? = some g) :
    l[j] = g := by
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

lemma redir_lt (n m p i : ℕ) (hi : i < n + m) : eraseRedirect n m p i = i := by
  unfold eraseRedirect
  split_ifs <;> omega

lemma redir_eq (n m p : ℕ) : eraseRedirect n m p (n + m) = p := by
  simp [eraseRedirect]

lemma redir_gt (n m p i : ℕ) (hi : n + m < i) : eraseRedirect n m p i = i - 1 := by
  unfold eraseRedirect
  split_ifs <;> omega

lemma e_rb {n m p : ℕ} {C : Circuit} (hA : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m)
    (j : ℕ) (hj : j < (eraseGate n C m p).gates.length) :
    ∀ i ∈ ((eraseGate n C m p).gates[j]).inputs, i < n + j := by
  have hlenE := e_len (n := n) (p := p) hm
  intro i hi
  by_cases hjm : j < m
  · have h1 := e_get_lt (n := n) (p := p) hm hjm
    have hjC : j < C.gates.length := by omega
    rw [List.getElem?_eq_getElem hjC] at h1
    rw [get_of_get? hj h1] at hi
    obtain ⟨_, a, b, hab, ha, hb⟩ := ao2_gate hA hjC
    rw [hab] at hi
    simp at hi
    rcases hi with rfl | rfl <;> omega
  · have h1 := e_get_ge (n := n) (p := p) hm (j := j) (by omega)
    have hjC : j + 1 < C.gates.length := by omega
    rw [List.getElem?_eq_getElem hjC, Option.map_some] at h1
    rw [get_of_get? hj h1] at hi
    obtain ⟨_, a, b, hab, ha, hb⟩ := ao2_gate hA hjC
    simp only [rdG, hab, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl
    · unfold eraseRedirect; split_ifs <;> omega
    · unfold eraseRedirect; split_ifs <;> omega

lemma e_prefix {n m p : ℕ} {C : Circuit} (hm : m < C.gates.length) (X : List Bool)
    (hX : X.length = n) (i : ℕ) (hi : i < n + m) :
    ((eraseGate n C m p).wires X).getD i false = (C.wires X).getD i false := by
  rw [wires_scan, wires_scan, e_gates hm, scan_append]
  have hlen : (scan boolStep (C.gates.take m) X).length = X.length + m := by
    rw [scan_length]; simp [Nat.min_eq_left hm.le]
  rw [scan_prefix boolStep _ (scan boolStep (C.gates.take m) X) false i (by rw [hlen, hX]; exact hi)]
  have e := scan_prefix boolStep (C.gates.drop m) (scan boolStep (C.gates.take m) X) false i
    (by rw [hlen, hX]; exact hi)
  rw [← scan_append, List.take_append_drop] at e
  exact e.symm

lemma sim {n m p h : ℕ} {C : Circuit} (hA : IsAO2 n C) (hm : m < C.gates.length)
    (hp : p < n + m) (hh : h < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (X : List Bool) (hX : X.length = n) :
    ∀ i, ((((eraseGate n C m p).wires X).getD (eraseRedirect n m p i) false = true →
        (C.wires X).getD i false = true) ∧
      ((C.wires X).getD h false = false →
        ((eraseGate n C m p).wires X).getD (eraseRedirect n m p i) false =
          (C.wires X).getD i false)) := by
  have hlenE := e_len (n := n) (p := p) hm
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    by_cases h1 : i < n + m
    · rw [redir_lt n m p i h1, e_prefix hm X hX i h1]
      exact ⟨id, fun _ => rfl⟩
    · by_cases h2 : i = n + m
      · subst h2
        rw [redir_eq, e_prefix hm X hX p hp]
        have hval : (C.wires X).getD (n + m) false =
            ((C.wires X).getD p false || (C.wires X).getD h false) := by
          have hg := wv_gate C X m hm (by
            intro i hi
            obtain ⟨_, a, b, hab, ha, hb⟩ := ao2_gate hA hm
            rw [hab] at hi
            simp at hi
            rcases hi with rfl | rfl <;> omega)
          rw [hX] at hg
          rw [hg]
          rcases hgate with hg' | hg'
          · rw [get_of_get? hm hg']
            simp [boolStep, GateOp.eval]
          · rw [get_of_get? hm hg']
            simp [boolStep, GateOp.eval, Bool.or_comm]
        rw [hval]
        refine ⟨fun hpv => by rw [hpv]; rfl, fun hhv => by rw [hhv, Bool.or_false]⟩
      · by_cases h3 : i < n + C.gates.length
        · obtain ⟨j, rfl⟩ : ∃ j, i = n + j := ⟨i - n, by omega⟩
          have hj : j < C.gates.length := by omega
          have hjm : m < j := by omega
          rw [redir_gt n m p _ (by omega)]
          have hE : (eraseGate n C m p).gates[j - 1]? = some (rdG n m p C.gates[j]) := by
            rw [e_get_ge hm (by omega), show j - 1 + 1 = j by omega, List.getElem?_eq_getElem hj]
            rfl
          have hjE : j - 1 < (eraseGate n C m p).gates.length := by omega
          have hgE := wv_gate (eraseGate n C m p) X (j - 1) hjE (by rw [hX]; exact e_rb hA hm hp _ hjE)
          have hgC := wv_gate C X j hj (by
            intro i hi
            obtain ⟨_, a, b, hab, ha, hb⟩ := ao2_gate hA hj
            rw [hab] at hi
            simp at hi
            rw [hX]
            rcases hi with rfl | rfl <;> omega)
          rw [hX] at hgE hgC
          rw [show n + j - 1 = n + (j - 1) by omega, hgE, get_of_get? hjE hE, hgC]
          obtain ⟨hop, a, b, hab, ha, hb⟩ := ao2_gate hA hj
          have iha := ih a (by omega)
          have ihb := ih b (by omega)
          have hopE : (rdG n m p C.gates[j]).op = C.gates[j].op := rfl
          have hinE : (rdG n m p C.gates[j]).inputs =
              [eraseRedirect n m p a, eraseRedirect n m p b] := by
            simp [rdG, hab]
          rcases hop with hop | hop
          · rw [bs_and _ _ _ _ hinE (by rw [hopE]; exact hop), bs_and _ _ _ _ hab hop]
            refine ⟨fun hv => ?_, fun hz => ?_⟩
            · simp only [Bool.and_eq_true] at hv ⊢
              exact ⟨iha.1 hv.1, ihb.1 hv.2⟩
            · rw [iha.2 hz, ihb.2 hz]
          · rw [bs_or _ _ _ _ hinE (by rw [hopE]; exact hop), bs_or _ _ _ _ hab hop]
            refine ⟨fun hv => ?_, fun hz => ?_⟩
            · simp only [Bool.or_eq_true] at hv ⊢
              rcases hv with hv | hv
              · exact Or.inl (iha.1 hv)
              · exact Or.inr (ihb.1 hv)
            · rw [iha.2 hz, ihb.2 hz]
        · rw [redir_gt n m p _ (by omega)]
          rw [wv_ge _ X _ (by rw [hX, hlenE]; omega), wv_ge _ X _ (by rw [hX]; omega)]
          exact ⟨id, fun _ => rfl⟩

def Good (n : ℕ) (D : Circuit) : Prop :=
  ∀ j < D.gates.length, ∀ a b : ℕ, D.gates[j]? = some ⟨GateOp.or, [a, b]⟩ →
    (n ≤ b → WireBelowOutput n D b → WireBelowOutput n D a) ∧
      (n ≤ a → WireBelowOutput n D a → WireBelowOutput n D b)

def M (n : ℕ) (D : Circuit) : ℕ :=
  ((Finset.range D.gates.length).filter fun g => ¬ WireBelowOutput n D (n + g)).card

lemma l_wires (n m p h : ℕ) (C : Circuit) (X : List Bool) :
    (liftAt n C m p h).wires X = (eraseGate n C m p).wires X ++
      [(((eraseGate n C m p).wires X).getD (eraseGate n C m p).output false ||
        ((eraseGate n C m p).wires X).getD h false)] := by
  rw [wires_scan, wires_scan]
  simp only [liftAt]
  rw [scan_append]
  simp [scan, boolStep, GateOp.eval]

lemma lift_core {n m p h : ℕ} {C : Circuit} (hA : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m) (hnh : n ≤ h)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (hWh : WireBelowOutput n C h) (hWp : ¬ WireBelowOutput n C p) :
    Lift n C (liftAt n C m p h) ∧ IsAO2 n (liftAt n C m p h) ∧
      (liftAt n C m p h).output < n + (liftAt n C m p h).gates.length ∧
      M n (liftAt n C m p h) < M n C := by
  have hlenE := e_len (n := n) (p := p) hm
  have hLlen : (liftAt n C m p h).gates.length = C.gates.length := by
    simp only [liftAt, List.length_append, List.length_singleton]
    omega
  have hLout : (liftAt n C m p h).output = n + (C.gates.length - 1) := by
    simp only [liftAt]
    rw [hlenE]
  have hEout : (eraseGate n C m p).output < n + (C.gates.length - 1) := by
    rw [e_out hm]
    unfold eraseRedirect
    split_ifs <;> omega
  -- the function is kept
  have hF : ∀ x : Fin n → Bool, (liftAt n C m p h).eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro x
    have hX : (List.ofFn x).length = n := List.length_ofFn
    have hs := sim hA hm hp hh hgate (List.ofFn x) hX C.output
    show ((liftAt n C m p h).wires (List.ofFn x)).getD (liftAt n C m p h).output false =
      (C.wires (List.ofFn x)).getD C.output false
    rw [l_wires, hLout, List.getD_append_right _ _ _ _ (by rw [wires_len, hX, hlenE]),
      wires_len, hX, hlenE, show n + (C.gates.length - 1) - (n + (C.gates.length - 1)) = 0 by omega,
      List.getD_cons_zero, e_prefix hm _ hX h hh, e_out hm]
    cases hhv : (C.wires (List.ofFn x)).getD h false
    · rw [Bool.or_false]
      exact hs.2 hhv
    · rw [Bool.or_true]
      exact (hWh x hhv).symm
  -- wires of the lifted circuit below its last gate are those of the erased circuit
  have hLpre : ∀ (X : List Bool), X.length = n → ∀ i, i < n + (C.gates.length - 1) →
      ((liftAt n C m p h).wires X).getD i false = ((eraseGate n C m p).wires X).getD i false := by
    intro X hX i hi
    rw [l_wires, List.getD_append _ _ _ _ (by rw [wires_len, hX, hlenE]; exact hi)]
  refine ⟨⟨m, hm, p, hp, h, hh, hnh, hgate, hWh, rfl⟩, ?_, ?_, ?_⟩
  · -- the model is kept
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [liftAt, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | hg
      · rw [e_gates hm, List.mem_append] at hg
        rcases hg with hg | hg
        · exact hA.1 g (List.mem_of_mem_take hg)
        · rw [List.mem_map] at hg
          obtain ⟨g0, hg0, rfl⟩ := hg
          exact hA.1 g0 (List.mem_of_mem_drop hg0)
      · subst hg
        exact Or.inr rfl
    · intro j hj i hi
      rw [hLlen] at hj
      have hgat : gateAt (liftAt n C m p h) j = (liftAt n C m p h).gates[j]'(by rw [hLlen]; exact hj) := by
        simp [gateAt, List.getD_eq_getElem?_getD, hLlen, hj]
      rw [hgat] at hi
      by_cases hjE : j < C.gates.length - 1
      · have hjE' : j < (eraseGate n C m p).gates.length := by omega
        have heq : (liftAt n C m p h).gates[j]'(by rw [hLlen]; exact hj) =
            (eraseGate n C m p).gates[j]'hjE' := by
          simp only [liftAt]
          rw [List.getElem_append_left]
        rw [heq] at hi
        exact e_rb hA hm hp j hjE' i hi
      · have hjl : j = C.gates.length - 1 := by omega
        have heq : (liftAt n C m p h).gates[j]'(by rw [hLlen]; exact hj) =
            ⟨GateOp.or, [(eraseGate n C m p).output, h]⟩ := by
          simp only [liftAt]
          rw [List.getElem_append_right (by omega)]
          simp
        rw [heq] at hi
        simp at hi
        rcases hi with rfl | rfl <;> omega
    · intro g hg
      simp only [liftAt, List.mem_append, List.mem_singleton] at hg
      rcases hg with hg | hg
      · rw [e_gates hm, List.mem_append] at hg
        rcases hg with hg | hg
        · exact hA.2.2 g (List.mem_of_mem_take hg)
        · rw [List.mem_map] at hg
          obtain ⟨g0, hg0, rfl⟩ := hg
          simp only [rdG, List.length_map]
          exact hA.2.2 g0 (List.mem_of_mem_drop hg0)
      · subst hg
        rfl
  · rw [hLout, hLlen]
    omega
  · -- the measure drops
    have hmC : m ∈ (Finset.range C.gates.length).filter
        (fun g => ¬ WireBelowOutput n C (n + g)) := by
      rw [Finset.mem_filter, Finset.mem_range]
      refine ⟨hm, fun hWm => hWp ?_⟩
      intro x hx
      apply hWm x
      have hX : (List.ofFn x).length = n := List.length_ofFn
      have hs := sim hA hm hp hh hgate (List.ofFn x) hX (n + m)
      rw [redir_eq, e_prefix hm _ hX p hp] at hs
      exact hs.1 hx
    have hcard : M n (liftAt n C m p h) ≤
        (((Finset.range C.gates.length).filter
          (fun g => ¬ WireBelowOutput n C (n + g))).erase m).card := by
      unfold M
      apply Finset.card_le_card_of_injOn (fun g => if g < m then g else g + 1)
      · intro g hg
        rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range, hLlen] at hg
        obtain ⟨hgl, hgW⟩ := hg
        have hgE : g < C.gates.length - 1 := by
          by_contra hge
          apply hgW
          have hgl' : g = C.gates.length - 1 := by omega
          intro x hx
          rw [hgl', ← hLout] at hx
          exact hx
        rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
        beta_reduce
        refine ⟨by split_ifs <;> omega, by split_ifs <;> omega, ?_⟩
        intro hW
        apply hgW
        intro x hx
        have hX : (List.ofFn x).length = n := List.length_ofFn
        rw [hF x]
        apply hW x
        rw [hLpre _ hX _ (by omega)] at hx
        have hs := sim hA hm hp hh hgate (List.ofFn x) hX (n + (if g < m then g else g + 1))
        have hr : eraseRedirect n m p (n + (if g < m then g else g + 1)) = n + g := by
          split_ifs with hgm
          · exact redir_lt n m p _ (by omega)
          · rw [redir_gt n m p _ (by omega)]
            omega
        rw [hr] at hs
        exact hs.1 hx
      · intro a _ b _ hab
        simp only at hab
        split_ifs at hab <;> omega
    rw [Finset.card_erase_of_mem hmC] at hcard
    have hpos : 0 < M n C := Finset.card_pos.mpr ⟨m, hmC⟩
    have hMC : M n C = ((Finset.range C.gates.length).filter
        (fun g => ¬ WireBelowOutput n C (n + g))).card := rfl
    omega

theorem main_ind (n : ℕ) : ∀ (k : ℕ) (C : Circuit), M n C = k → IsAO2 n C →
    C.output < n + C.gates.length →
    ∃ D, Relation.ReflTransGen (Lift n) C D ∧ Good n D := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro C hk hA hout
    by_cases hg : Good n C
    · exact ⟨C, Relation.ReflTransGen.refl, hg⟩
    · unfold Good at hg
      push_neg at hg
      obtain ⟨j, hj, a, b, hab, hv⟩ := hg
      obtain ⟨_, a', b', hin, ha, hb⟩ := ao2_gate hA hj
      have hgj := get_of_get? hj hab
      rw [hgj] at hin
      simp only [List.cons.injEq, and_true] at hin
      obtain ⟨rfl, rfl⟩ := hin
      by_cases h1 : (n ≤ b → WireBelowOutput n C b → WireBelowOutput n C a)
      · obtain ⟨hna, hwa, hnwb⟩ := hv h1
        obtain ⟨hL, hAL, hoL, hML⟩ := lift_core hA hout hj hb ha hna (Or.inr hab) hwa hnwb
        obtain ⟨D, hD, hgD⟩ := ih _ (by omega) _ rfl hAL hoL
        exact ⟨D, Relation.ReflTransGen.head hL hD, hgD⟩
      · push_neg at h1
        obtain ⟨hnb, hwb, hnwa⟩ := h1
        obtain ⟨hL, hAL, hoL, hML⟩ := lift_core hA hout hj ha hb hnb (Or.inl hab) hwb hnwa
        obtain ⟨D, hD, hgD⟩ := ih _ (by omega) _ rfl hAL hoL
        exact ⟨D, Relation.ReflTransGen.head hL hD, hgD⟩

end PEqualNP.Outside.L_meta_4295

theorem PEqualNP.Outside.L_meta_4295 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift x1) x2 x5 ∧ ∀ x6 < x5.gates.length, ∀ (x8 x9 : ℕ), x5.gates[x6]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x8, x9] : PEqualNP.CircuitLowerBounds.Gate } → (x1 ≤ x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8) ∧ (x1 ≤ x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9) := by
  intro x1 x2 hA hout
  obtain ⟨D, hD, hG⟩ := PEqualNP.Outside.L_meta_4295.main_ind x1 _ x2 rfl hA hout
  exact ⟨D, hD, hG⟩
