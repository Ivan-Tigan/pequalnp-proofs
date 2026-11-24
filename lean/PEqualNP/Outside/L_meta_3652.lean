import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3652

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

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

lemma scan_gate {α : Type} (step : List α → Gate → α) (gs : List Gate) (w : List α)
    (d : α) (j : ℕ) (hj : j < gs.length)
    (hstep : ∀ p p' : List α, (∀ i < w.length + j, p.getD i d = p'.getD i d) →
      step p gs[j] = step p' gs[j]) :
    (scan step gs w).getD (w.length + j) d = step (scan step gs w) gs[j] := by
  let pre := scan step (gs.take j) w
  have hp : pre.length = w.length + j := by
    simp [pre, scan_length, Nat.min_eq_left hj.le]
  have hs : scan step gs w = scan step (gs[j] :: gs.drop (j + 1)) pre := by
    have hsplit := List.take_append_drop j gs
    conv_lhs => rw [← hsplit, scan_append, List.drop_eq_getElem_cons hj]
  have hpre : ∀ i < w.length + j, (scan step gs w).getD i d = pre.getD i d := by
    intro i hi
    rw [hs]
    exact scan_prefix step (gs[j] :: gs.drop (j + 1)) pre d i (by omega)
  have hres : (scan step gs w).getD (w.length + j) d = step pre gs[j] := by
    rw [hs, scan_cons, scan_prefix step (gs.drop (j + 1)) (pre ++ [step pre gs[j]]) d (w.length + j) (by simp [hp])]
    rw [List.getD_append_right _ _ _ _ (by omega)]
    have hsub : w.length + j - pre.length = 0 := by omega
    rw [hsub]
    simp only [List.getD_cons_zero]
  rw [hres]
  exact hstep pre (scan step gs w) (fun i hi => (hpre i hi).symm)

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def linStep (w : List (Bool × Bool)) (g : Gate) : Bool × Bool :=
  let ins := g.inputs.map fun i => w.getD i (false, false)
  match g.op with
  | GateOp.or => (ins.any (·.1), ins.any (·.2))
  | GateOp.and => ins.foldl (fun (acc : Bool × Bool) p =>
        (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (true, false)
  | _ => (false, false)

lemma wires_eq_scan (C : Circuit) (x : List Bool) :
    C.wires x = scan boolStep C.gates x := rfl

lemma linearParts_eq_scan (C : Circuit) (isLine : ℕ → Bool) (x : List Bool) :
    linearParts C isLine x =
      scan linStep C.gates ((x.zipIdx).map fun (b, i) => if isLine i then (false, b) else (b, false)) := rfl

lemma list_eq_two {l : List ℕ} (hl : l.length = 2) : l = [l.getD 0 0, l.getD 1 0] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩ <;> simp at hl ⊢

lemma gateAt_eq_getElem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, hj]

lemma ao2_gate_props {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
    opnd C j 0 < n + j ∧ opnd C j 1 < n + j := by
  have hmem : C.gates[j] ∈ C.gates := List.getElem_mem hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.1 C.gates[j] hmem
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem hj]
    exact hAO2.2.2 C.gates[j] hmem
  have hin : (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
    simpa [opnd] using list_eq_two hlen
  have hrb := hAO2.2.1 j hj
  have h0 : opnd C j 0 < n + j := hrb (opnd C j 0) (by rw [hin]; simp)
  have h1 : opnd C j 1 < n + j := hrb (opnd C j 1) (by rw [hin]; simp)
  exact ⟨hop, hin, h0, h1⟩

def pairList (N : ℕ) (p l : Fin N) : List Bool :=
  (List.range (N + N)).map fun i => i == p.val || i == N + l.val

def lpInit (N : ℕ) (p l : Fin N) : List (Bool × Bool) :=
  ((pairList N p l).zipIdx).map fun (b, i) => if decide (N ≤ i) then (false, b) else (b, false)

def lpList (C : Circuit) (N : ℕ) (p l : Fin N) : List (Bool × Bool) :=
  linearParts C (fun k => decide (N ≤ k)) (pairList N p l)

def lpAt (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) : Bool × Bool :=
  (lpList C N p l).getD w (false, false)

lemma lineSingle_eq_lpAt (C : Circuit) (N : ℕ) (p l : Fin N) :
    lineSingle C (N + N) (fun k => decide (N ≤ k)) p.val (N + l.val) = (lpAt C N p l C.output).2 := rfl

lemma lpInit_length (N : ℕ) (p l : Fin N) : (lpInit N p l).length = N + N := by
  simp [lpInit, pairList]

lemma lpInit_getD (N : ℕ) (p l : Fin N) (i : ℕ) (hi : i < N + N) :
    (lpInit N p l).getD i (false, false) =
      if i < N then (decide (i = p.val), false) else (false, decide (i = N + l.val)) := by
  have hl1 : (pairList N p l).length = N + N := by simp [pairList]
  have hl2 : ((pairList N p l).zipIdx).length = N + N := by simp [hl1]
  rw [lpInit, List.getD_eq_getElem _ _ (by simp [hl2, hi]), List.getElem_map]
  have hz : ((pairList N p l).zipIdx)[i]'(by omega) = ((pairList N p l)[i]'(by omega), i) := by
    simp [List.getElem_zipIdx]
  rw [hz]
  dsimp only
  unfold pairList
  rw [List.getElem_map, List.getElem_range]
  by_cases hlt : i < N
  · have hni : ¬ (N ≤ i) := by omega
    have hne : (i == N + l.val) = false := by
      simp
      omega
    simp only [hlt, hni, hne, Bool.or_false, decide_false, ite_true]
    by_cases hep : i = p.val <;> simp [hep]
  · have hle : N ≤ i := by omega
    have hne : (i == p.val) = false := by
      simp
      omega
    simp only [hlt, hle, hne, Bool.false_or, decide_true, ite_true, ite_false]
    by_cases hel : i = N + l.val <;> simp [hel]

def pointInput (N : ℕ) (p : Fin N) : Fin (N + N) → Bool :=
  fun i => decide (i.val = p.val)

def zInput {N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (l : Fin N) : Fin (N + N) → Bool :=
  fun i => if h : i.val < N then decide (¬ I ⟨i.val, h⟩ l) else decide (i.val = N + l.val)

def wireVal (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma getD_map_fst (ws : List (Bool × Bool)) (i : ℕ) :
    (ws.map (·.1)).getD i false = (ws.getD i (false, false)).1 := by
  by_cases hi : i < ws.length
  · simp [hi]
  · have hle : ws.length ≤ i := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using hle)]

lemma boolStep_fst_linStep (g : Gate) (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (ws : List (Bool × Bool)) :
    (linStep ws g).1 = boolStep (ws.map (·.1)) g := by
  rcases hg with hop | hop
  · simp only [linStep, boolStep, hop, GateOp.eval]
    have hfold : ∀ (l : List (Bool × Bool)) (b c : Bool),
        (l.foldl (fun (acc : Bool × Bool) p =>
          (acc.1 && p.1, (acc.1 && p.2) || (acc.2 && p.1))) (b, c)).1 =
        (b && l.all (·.1)) := by
      intro l
      induction l with
      | nil => intro b c; simp
      | cons x xs ih =>
        intro b c
        simp only [List.foldl_cons, List.all_cons]
        rw [ih, Bool.and_assoc]
    rw [hfold, Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro h i hi; rw [getD_map_fst]; exact h i hi
    · intro h i hi; rw [← getD_map_fst]; exact h i hi
  · simp only [linStep, boolStep, hop, GateOp.eval]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    constructor
    · intro ⟨i, hi, hit⟩; exact ⟨i, hi, by rw [getD_map_fst]; exact hit⟩
    · intro ⟨i, hi, hit⟩; exact ⟨i, hi, by rw [← getD_map_fst]; exact hit⟩

lemma scan_lin_fst (gs : List Gate) (hAO : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ws : List (Bool × Bool)) :
    (scan linStep gs ws).map (·.1) = scan boolStep gs (ws.map (·.1)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := hAO g (by simp)
    have hgs : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or := fun g' hg' => hAO g' (by simp [hg'])
    rw [scan_cons, scan_cons, ih hgs]
    simp [boolStep_fst_linStep g hg ws]

lemma lpInit_map_fst (N : ℕ) (p l : Fin N) :
    (lpInit N p l).map (·.1) = List.ofFn (pointInput N p) := by
  apply List.ext_getElem
  · simp [lpInit_length]
  · intro i h1 h2
    have hi : i < N + N := by simpa [lpInit_length] using h1
    rw [List.getElem_map, List.getElem_ofFn]
    have hg := lpInit_getD N p l i hi
    rw [List.getD_eq_getElem _ _ (by simp [lpInit_length, hi])] at hg
    rw [hg]
    by_cases hlt : i < N
    · simp [hlt, pointInput]
    · simp [hlt, pointInput]
      omega

lemma lpAt_fst (C : Circuit) (hAO : AndOrOnly C) (N : ℕ) (p l : Fin N) (w : ℕ) :
    (lpAt C N p l w).1 = wireVal (N + N) C w (pointInput N p) := by
  rw [lpAt, lpList, linearParts_eq_scan]
  change ((scan linStep C.gates (lpInit N p l)).getD w (false, false)).1 =
    (scan boolStep C.gates (List.ofFn (pointInput N p))).getD w false
  rw [← getD_map_fst, scan_lin_fst C.gates hAO, lpInit_map_fst]

lemma lpList_length (C : Circuit) (N : ℕ) (p l : Fin N) :
    (lpList C N p l).length = N + N + C.gates.length := by
  rw [lpList, linearParts_eq_scan, scan_length]
  change (lpInit N p l).length + C.gates.length = N + N + C.gates.length
  rw [lpInit_length]

lemma lpAt_ge (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (hw : N + N + C.gates.length ≤ w) :
    lpAt C N p l w = (false, false) := by
  rw [lpAt, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [lpList_length]; exact hw)]
  rfl

lemma lpAt_lt_len (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (hw : w < N + N) :
    lpAt C N p l w = (lpInit N p l).getD w (false, false) := by
  rw [lpAt, lpList, linearParts_eq_scan]
  exact scan_prefix linStep C.gates (lpInit N p l) (false, false) w (by rw [lpInit_length]; exact hw)

lemma lpAt_snd_lt_N (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (hw : w < N) :
    (lpAt C N p l w).2 = false := by
  rw [lpAt_lt_len C N p l w (by omega), lpInit_getD N p l w (by omega)]
  simp [hw]

lemma lpAt_snd_line (C : Circuit) (N : ℕ) (p l : Fin N) (w : ℕ) (h1 : N ≤ w) (h2 : w < N + N) :
    (lpAt C N p l w).2 = decide (w = N + l.val) := by
  rw [lpAt_lt_len C N p l w h2, lpInit_getD N p l w h2]
  have hnot : ¬ (w < N) := by omega
  simp [hnot]

lemma lpAt_gate {N : ℕ} {C : Circuit} (hAO2 : IsAO2 (N + N) C) (p l : Fin N)
    {j : ℕ} (hj : j < C.gates.length) :
    lpAt C N p l (N + N + j) = linStep (lpList C N p l) C.gates[j] := by
  rw [lpAt, lpList, linearParts_eq_scan]
  have hlen : (lpInit N p l).length = N + N := lpInit_length N p l
  conv_lhs => rw [← hlen]
  apply scan_gate linStep C.gates (lpInit N p l) (false, false) j hj
  intro q1 q2 hq
  simp only [linStep]
  have hrb := hAO2.2.1 j hj
  have hcongr : C.gates[j].inputs.map (fun i => q1.getD i (false, false)) =
      C.gates[j].inputs.map (fun i => q2.getD i (false, false)) := by
    apply List.map_congr_left
    intro i hi
    apply hq
    rw [hlen]
    exact hrb i (by rw [gateAt_eq_getElem hj]; exact hi)
  rw [hcongr]

lemma lpAt_snd_or {N : ℕ} {C : Circuit} (hAO2 : IsAO2 (N + N) C) (p l : Fin N)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    (lpAt C N p l (N + N + j)).2 =
      ((lpAt C N p l (opnd C j 0)).2 || (lpAt C N p l (opnd C j 1)).2) := by
  rw [lpAt_gate hAO2 p l hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [linStep, hop, hin, lpAt]

lemma lpAt_snd_and {N : ℕ} {C : Circuit} (hAO2 : IsAO2 (N + N) C) (p l : Fin N)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    (lpAt C N p l (N + N + j)).2 =
      ((wireVal (N + N) C (opnd C j 0) (pointInput N p) && (lpAt C N p l (opnd C j 1)).2) ||
       ((lpAt C N p l (opnd C j 0)).2 && wireVal (N + N) C (opnd C j 1) (pointInput N p))) := by
  rw [lpAt_gate hAO2 p l hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp only [linStep, hop, hin, List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil,
    Bool.true_and, Bool.false_and, Bool.or_false]
  rw [← lpAt_fst C hAO2.1 N p l (opnd C j 0), ← lpAt_fst C hAO2.1 N p l (opnd C j 1)]
  rfl

lemma wireVal_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_scan, scan_length, List.length_ofFn]

lemma wireVal_ge (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : n + C.gates.length ≤ w) :
    wireVal n C w x = false := by
  rw [wireVal, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wireVal_length]; exact hw)]
  rfl

lemma wireVal_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wireVal n C i x = x ⟨i, hi⟩ := by
  rw [wireVal, wires_eq_scan, scan_prefix boolStep C.gates (List.ofFn x) false i (by simp [hi])]
  rw [List.getD_eq_getElem _ _ (by simp [hi]), List.getElem_ofFn]

lemma wireVal_gate {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wireVal n C (n + j) x = boolStep (C.wires (List.ofFn x)) C.gates[j] := by
  rw [wireVal, wires_eq_scan]
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have h := scan_gate boolStep C.gates (List.ofFn x) false j hj (by
    intro q1 q2 hq
    simp only [boolStep]
    have hrb := hAO2.2.1 j hj
    have hcongr : C.gates[j].inputs.map (fun i => q1.getD i false) =
        C.gates[j].inputs.map (fun i => q2.getD i false) := by
      apply List.map_congr_left
      intro i hi
      apply hq
      rw [hlen]
      exact hrb i (by rw [gateAt_eq_getElem hj]; exact hi)
    rw [hcongr])
  simpa only [hlen] using h

lemma wireVal_or {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO2 x hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [boolStep, hop, hin, GateOp.eval, wireVal]

lemma wireVal_and {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate hAO2 x hj]
  have ⟨_, hin, _, _⟩ := ao2_gate_props hAO2 hj
  rw [gateAt_eq_getElem hj] at hop hin
  simp [boolStep, hop, hin, GateOp.eval, wireVal]


lemma gateVal_eq (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wireVal n C (n + j) x := rfl

def single (n : ℕ) (a : ℕ) : Fin n → Bool := fun i => decide (i.val = a)

lemma graphFun_single {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (a : ℕ) :
    graphFun G ∅ (single n a) = false := by
  have h : ¬ ∃ u v, G.Adj u v ∧ single n a u = true ∧ single n a v = true := by
    rintro ⟨u, v, huv, hu, hv⟩
    simp only [single, decide_eq_true_eq] at hu hv
    have huv' : u = v := Fin.ext (by omega)
    subst huv'
    exact G.irrefl huv
  unfold graphFun
  rw [Bool.or_eq_false_iff]
  exact ⟨by simp, decide_eq_false h⟩

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {u v : Fin n}
    (h : G.Adj u v) : graphFun G ∅ (pairInput u v) = true := by
  unfold graphFun
  rw [Bool.or_eq_true]
  right
  exact decide_eq_true ⟨u, v, h, by simp [pairInput], by simp [pairInput]⟩

def WB {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (w : ℕ) : Prop :=
  ∀ x : Fin n → Bool, wireVal n C w x = true → graphFun G ∅ x = true

lemma input_not_WB {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {w : ℕ} (hw : w < n) : ¬ WB G C w := by
  intro h
  have h1 := h (single n w) (by rw [wireVal_input n C _ w hw]; simp [single])
  rw [graphFun_single] at h1
  exact absurd h1 (by simp)

lemma allOnes {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) :
    ∀ w, w < n + C.gates.length → wireVal n C w (fun _ => true) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hlt : w < n
    · rw [wireVal_input n C _ w hlt]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨hop, _, h0, h1⟩ := ao2_gate_props hAO2 hj
      have e0 := ih _ h0 (by omega)
      have e1 := ih _ h1 (by omega)
      rcases hop with hop | hop
      · rw [wireVal_and hAO2 _ hj hop, e0, e1]
        rfl
      · rw [wireVal_or hAO2 _ hj hop, e0]
        rfl

lemma descent {N : ℕ} {G : SimpleGraph (Fin (N + N))} [DecidableRel G.Adj] {C : Circuit}
    (hAO2 : IsAO2 (N + N) C) (p l : Fin N) (x : Fin (N + N) → Bool) (P : Prop) :
    ∀ j, j < C.gates.length → WB G C (N + N + j) → wireVal (N + N) C (N + N + j) x = true →
      ((lpAt C N p l (N + N + j)).2 = true → P) →
      ∃ g, g < C.gates.length ∧ (gateAt C g).op = GateOp.and ∧ WB G C (N + N + g) ∧
        wireVal (N + N) C (N + N + g) x = true ∧ ((lpAt C N p l (N + N + g)).2 = true → P) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hj hwb hval hP
    obtain ⟨hop, _, h0, h1⟩ := ao2_gate_props hAO2 hj
    rcases hop with hop | hop
    · exact ⟨j, hj, hop, hwb, hval, hP⟩
    · have step : ∀ o, o < N + N + j → WB G C o → wireVal (N + N) C o x = true →
          ((lpAt C N p l o).2 = true → (lpAt C N p l (N + N + j)).2 = true) →
          ∃ g, g < C.gates.length ∧ (gateAt C g).op = GateOp.and ∧ WB G C (N + N + g) ∧
            wireVal (N + N) C (N + N + g) x = true ∧ ((lpAt C N p l (N + N + g)).2 = true → P) := by
        intro o ho hwbo hvo himp
        by_cases hlt : o < N + N
        · exact absurd hwbo (input_not_WB hlt)
        · obtain ⟨j', rfl⟩ : ∃ j', o = N + N + j' := ⟨o - (N + N), by omega⟩
          exact ih j' (by omega) (by omega) hwbo hvo (fun h => hP (himp h))
      rw [wireVal_or hAO2 x hj hop, Bool.or_eq_true] at hval
      rcases hval with hv | hv
      · refine step _ h0 ?_ hv ?_
        · intro y hy
          apply hwb y
          rw [wireVal_or hAO2 y hj hop, hy]
          rfl
        · intro h
          rw [lpAt_snd_or hAO2 p l hj hop, h]
          rfl
      · refine step _ h1 ?_ hv ?_
        · intro y hy
          apply hwb y
          rw [wireVal_or hAO2 y hj hop, hy, Bool.or_true]
        · intro h
          rw [lpAt_snd_or hAO2 p l hj hop, h, Bool.or_true]

def rvStep (S : List ℕ) (k : ℕ) (R : List (List (List ℕ))) (g : Gate) : List (List ℕ) :=
  let ins := g.inputs.map fun i => R.getD i []
  match g.op with
  | GateOp.or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | GateOp.and => ins.foldl (andStep k) [S.map fun _ => 0]
  | _ => []

lemma readVectors_eq_scan (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    readVectors C n S k = scan (rvStep S k) C.gates ((List.range n).map (leafVectors S k)) := rfl

lemma readVectors_length (C : Circuit) (n : ℕ) (S : List ℕ) (k : ℕ) :
    (readVectors C n S k).length = n + C.gates.length := by
  rw [readVectors_eq_scan, scan_length]
  simp

lemma rv_gate {n : ℕ} {C : Circuit} (hAO2 : IsAO2 n C) (S : List ℕ) (k : ℕ) {j : ℕ}
    (hj : j < C.gates.length) :
    (readVectors C n S k).getD (n + j) [] = rvStep S k (readVectors C n S k) C.gates[j] := by
  rw [readVectors_eq_scan]
  have hlen : ((List.range n).map (leafVectors S k)).length = n := by simp
  have h := scan_gate (rvStep S k) C.gates ((List.range n).map (leafVectors S k)) [] j hj (by
    intro q1 q2 hq
    simp only [rvStep]
    have hrb := hAO2.2.1 j hj
    have hcongr : C.gates[j].inputs.map (fun i => q1.getD i []) =
        C.gates[j].inputs.map (fun i => q2.getD i []) := by
      apply List.map_congr_left
      intro i hi
      apply hq
      rw [hlen]
      exact hrb i (by rw [gateAt_eq_getElem hj]; exact hi)
    rw [hcongr])
  simpa only [hlen] using h

lemma mem_foldl_insertNew (A acc : List (List ℕ)) (v : List ℕ) :
    v ∈ A.foldl insertNew acc → v ∈ acc ∨ v ∈ A := by
  induction A generalizing acc with
  | nil => intro h; exact Or.inl h
  | cons a A ih =>
    intro h
    rcases ih _ h with h1 | h1
    · unfold insertNew at h1
      split_ifs at h1 with ha
      · exact Or.inl h1
      · rw [List.mem_append, List.mem_singleton] at h1
        rcases h1 with h1 | h1
        · exact Or.inl h1
        · exact Or.inr (by simp [h1])
    · exact Or.inr (List.mem_cons_of_mem _ h1)

lemma mem_andStep {k : ℕ} {A B : List (List ℕ)} {v : List ℕ} (h : v ∈ andStep k A B) :
    ∃ a ∈ A, ∃ b ∈ B, v = capAdd k a b := by
  unfold andStep at h
  rcases mem_foldl_insertNew _ [] v h with h1 | h1
  · simp at h1
  · rw [List.mem_flatMap] at h1
    obtain ⟨a, ha, hb⟩ := h1
    rw [List.mem_map] at hb
    obtain ⟨b, hb, rfl⟩ := hb
    exact ⟨a, ha, b, hb, rfl⟩

lemma len_two {a : List ℕ} (h : a.length = 2) : ∃ a0 a1, a = [a0, a1] := by
  rcases a with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, t⟩⟩⟩ <;> simp at h ⊢

lemma keyK {N : ℕ} {C : Circuit} (hAO2 : IsAO2 (N + N) C) (p l : Fin N) :
    ∀ w, ∀ v ∈ (readVectors C (N + N) [p.val, N + l.val] 1).getD w [],
      v.length = 2 ∧ (v.getD 1 0 = 0 → wireVal (N + N) C w (pointInput N p) = true) ∧
        (v.getD 1 0 = 1 → (lpAt C N p l w).2 = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro v hv
    by_cases hlt : w < N + N
    · have hR : (readVectors C (N + N) [p.val, N + l.val] 1).getD w [] =
          leafVectors [p.val, N + l.val] 1 w := by
        rw [readVectors_eq_scan, scan_prefix _ _ _ _ _ (by simp [hlt])]
        rw [List.getD_eq_getElem _ _ (by simp [hlt]), List.getElem_map, List.getElem_range]
      rw [hR] at hv
      unfold leafVectors at hv
      split_ifs at hv with hmem
      · rw [List.mem_singleton] at hv
        subst hv
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
        have hpl : p.val ≠ N + l.val := by omega
        rcases hmem with hw | hw
        · subst hw
          have hne : ¬ (N + l.val = p.val) := fun h => hpl h.symm
          refine ⟨by simp, ?_, ?_⟩
          · intro _
            rw [wireVal_input _ _ _ _ hlt]
            simp [pointInput]
          · intro h
            simp [hne] at h
        · subst hw
          refine ⟨by simp, ?_, ?_⟩
          · intro h
            simp [hpl] at h
          · intro _
            rw [lpAt_snd_line C N p l _ (by omega) hlt]
            simp
      · simp at hv
    · by_cases hge : N + N + C.gates.length ≤ w
      · have h0 : (readVectors C (N + N) [p.val, N + l.val] 1).getD w [] = [] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [readVectors_length]; omega)]
          rfl
        rw [h0] at hv
        simp at hv
      · obtain ⟨j, rfl⟩ : ∃ j, w = N + N + j := ⟨w - (N + N), by omega⟩
        have hj : j < C.gates.length := by omega
        rw [rv_gate hAO2 _ 1 hj] at hv
        obtain ⟨hop, hin, h0, h1⟩ := ao2_gate_props hAO2 hj
        have hop' := hop
        rw [gateAt_eq_getElem hj] at hop hin
        rcases hop with hop | hop
        · have hopA : (gateAt C j).op = GateOp.and := by rw [gateAt_eq_getElem hj]; exact hop
          simp only [rvStep, hop, hin, List.map_cons, List.map_nil, List.foldl_cons,
            List.foldl_nil] at hv
          obtain ⟨a', ha', b, hb, rfl⟩ := mem_andStep hv
          obtain ⟨z, hz, a, ha, rfl⟩ := mem_andStep ha'
          rw [List.mem_singleton] at hz
          subst hz
          obtain ⟨hal, ha0, ha1⟩ := ih _ h0 a ha
          obtain ⟨hbl, hb0, hb1⟩ := ih _ h1 b hb
          obtain ⟨a0, a1, rfl⟩ := len_two hal
          obtain ⟨b0, b1, rfl⟩ := len_two hbl
          simp only [List.getD_cons_succ, List.getD_cons_zero] at ha0 ha1 hb0 hb1
          simp only [capAdd, List.zipWith_cons_cons, List.zipWith_nil_left, List.length_cons,
            List.length_nil, List.getD_cons_succ, List.getD_cons_zero]
          refine ⟨by simp, ?_, ?_⟩
          · intro hz
            have ha : a1 = 0 := by omega
            have hb : b1 = 0 := by omega
            rw [wireVal_and hAO2 _ hj hopA, ha0 ha, hb0 hb]
            rfl
          · intro ho
            rw [lpAt_snd_and hAO2 p l hj hopA]
            rcases (by omega : (a1 = 1 ∧ b1 = 0) ∨ (a1 = 0 ∧ b1 = 1)) with ⟨ha, hb⟩ | ⟨ha, hb⟩
            · rw [ha1 ha, hb0 hb]
              simp
            · rw [ha0 ha, hb1 hb]
              simp
        · have hopO : (gateAt C j).op = GateOp.or := by rw [gateAt_eq_getElem hj]; exact hop
          simp only [rvStep, hop, hin, List.map_cons, List.map_nil, List.foldl_cons,
            List.foldl_nil] at hv
          rcases mem_foldl_insertNew _ _ v hv with h | h
          · rcases mem_foldl_insertNew _ [] v h with h' | h'
            · simp at h'
            · obtain ⟨hl, h0', h1'⟩ := ih _ h0 v h'
              refine ⟨hl, fun hz => ?_, fun ho => ?_⟩
              · rw [wireVal_or hAO2 _ hj hopO, h0' hz]
                rfl
              · rw [lpAt_snd_or hAO2 p l hj hopO, h1' ho]
                rfl
          · obtain ⟨hl, h0', h1'⟩ := ih _ h1 v h
            refine ⟨hl, fun hz => ?_, fun ho => ?_⟩
            · rw [wireVal_or hAO2 _ hj hopO, h0' hz, Bool.or_true]
            · rw [lpAt_snd_or hAO2 p l hj hopO, h1' ho, Bool.or_true]

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

def cstep (n : ℕ) (cs : List (List ℕ)) (g : Gate) : List ℕ :=
  (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
    (fun w => (w - n) :: cs.getD (w - n) [])

lemma cones_eq (n : ℕ) (C : Circuit) : cones n C = scan (cstep n) C.gates [] := rfl

lemma inCone_step {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) :
    j < C.gates.length ∧ ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone at h
  by_cases hj : j < C.gates.length
  · refine ⟨hj, ?_⟩
    rw [cones_eq] at h
    have hg := scan_getD_gate (cstep n) C.gates [] [] j hj
    simp only [List.length_nil, Nat.zero_add] at hg
    rw [hg] at h
    unfold cstep at h
    rw [List.mem_flatMap] at h
    obtain ⟨w, hw, hi⟩ := h
    rw [List.mem_filter, decide_eq_true_eq] at hw
    obtain ⟨hw, hnw, hwlt⟩ := hw
    have hpre_len : (scan (cstep n) (C.gates.take j) []).length = j := by
      simp [scan_length, Nat.min_eq_left hj.le]
    have hwlt2 : w < n + j := by
      rw [← hpre_len]
      exact hwlt
    refine ⟨w, by rw [gateAt_eq_getElem hj]; exact hw, hnw, hwlt2, ?_⟩
    rw [List.mem_cons] at hi
    rcases hi with hi | hi
    · exact Or.inl hi
    · right
      unfold InCone
      rw [cones_eq]
      have hpre : (scan (cstep n) C.gates []).getD (w - n) [] =
          (scan (cstep n) (C.gates.take j) []).getD (w - n) [] := by
        have hsplit := List.take_append_drop j C.gates
        conv_lhs => rw [← hsplit, scan_append]
        exact scan_prefix _ _ _ _ _ (by rw [hpre_len]; omega)
      rw [hpre]
      exact hi
  · exfalso
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none] at h
    · simp at h
    · rw [cones_eq, scan_length]
      simp
      omega

lemma above_below {N : ℕ} {G : SimpleGraph (Fin (N + N))} [DecidableRel G.Adj] {C : Circuit}
    (hAO2 : IsAO2 (N + N) C) (hfix : PEqualNP.Core.IsLiftFixedPoint G C)
    (hlive : ∀ k < C.gates.length, PEqualNP.Core.InOutputCone (N + N) C k)
    (hnoA : ∀ k2 < C.gates.length, (gateAt C k2).op = GateOp.and →
      ∀ t ∈ (gateAt C k2).inputs, ¬ WB G C t)
    (j0 : ℕ) (hj0 : WB G C (N + N + j0)) :
    ∀ i, InCone (N + N) C j0 i → (gateAt C i).op = GateOp.or ∧ WB G C (N + N + i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hc
    obtain ⟨hi, w, hw, hnw, hwlt, hcase⟩ := inCone_step hc
    have hwb : WB G C w := by
      rcases hcase with h | h
      · have hw0 : w = N + N + j0 := by omega
        rw [hw0]
        exact hj0
      · have h2 := (ih (w - (N + N)) (by omega) h).2
        rwa [show N + N + (w - (N + N)) = w by omega] at h2
    obtain ⟨hop, hin, _, _⟩ := ao2_gate_props hAO2 hi
    rcases hop with hop | hop
    · exact absurd hwb (hnoA i hi hop w hw)
    · refine ⟨hop, ?_⟩
      by_contra hnb
      apply hfix
      rw [hin] at hw
      have hw' : w = opnd C i 0 ∨ w = opnd C i 1 := by simpa using hw
      have himp : ∀ b : Fin 2, opnd C i b = w → PEqualNP.Core.LiftAt G C i b := by
        intro b hb
        subst hb
        exact ⟨hlive i hi, hop, fun hB => hnb hB, fun x hx => hwb x hx,
          ⟨fun _ => true, allOnes hAO2 _ (by omega)⟩⟩
      rcases hw' with h | h
      · exact ⟨i, hi, 0, himp 0 h.symm⟩
      · exact ⟨i, hi, 1, himp 1 h.symm⟩

lemma core_and {N : ℕ} {G : SimpleGraph (Fin (N + N))} [DecidableRel G.Adj] {C : Circuit}
    (hAO2 : IsAO2 (N + N) C) {c : ℕ} (hc : PEqualNP.Core.IsCore G C c) :
    (gateAt C c).op = GateOp.and := by
  obtain ⟨hcl, ⟨hB, _⟩, hnot, _⟩ := hc
  obtain ⟨hop, _, h0, h1⟩ := ao2_gate_props hAO2 hcl
  rcases hop with hop | hop
  · exact hop
  · exfalso
    apply hnot
    have hb0 : WB G C (opnd C c 0) := fun x hx => hB x (by
      rw [gateVal_eq, wireVal_or hAO2 x hcl hop, hx]
      rfl)
    have hb1 : WB G C (opnd C c 1) := fun x hx => hB x (by
      rw [gateVal_eq, wireVal_or hAO2 x hcl hop, hx, Bool.or_true])
    have imp : ∀ o, o < N + N + c → WB G C o → PEqualNP.Core.IsImpOperand G C o := by
      intro o ho hwo
      by_cases hlt : o < N + N
      · exact absurd hwo (input_not_WB hlt)
      · have he : N + N + (o - (N + N)) = o := by omega
        refine ⟨by omega, ?_, ?_⟩
        · intro x hx
          apply hwo x
          rwa [gateVal_eq, he] at hx
        · exact ⟨fun _ => true, by rw [gateVal_eq, he]; exact allOnes hAO2 o (by omega)⟩
    exact ⟨imp _ h0 hb0, imp _ h1 hb1⟩

end PEqualNP.Outside.L_meta_3652

theorem PEqualNP.Outside.L_meta_3652 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (G : SimpleGraph (Fin (N + N))) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ u v : Fin (N + N), G.Adj u v ↔ ∃ p l : Fin N, I p l ∧ ((u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨ (u = Fin.natAdd N l ∧ v = Fin.castAdd N p))) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 (N + N) C → PEqualNP.MetaComplexity.circuitFun (N + N) C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone (N + N) C k) → (∀ k2 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).inputs, ¬ (∀ x : Fin (N + N) → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → ∀ p1 l1 : Fin N, (p1.val, N + l1.val) ∈ (PEqualNP.ReadK.doubleReread C (N + N) (fun w => decide (N ≤ w)) ((List.finRange N).flatMap (fun p5 => ((List.finRange N).filter (fun l5 => decide (I p5 l5))).map (fun l6 => (p5.val, N + l6.val))))) → ∃ j ∈ PEqualNP.Core.maximalCores G C, s(Fin.castAdd N p1, Fin.natAdd N l1) ∈ PEqualNP.TopForm.gammaE G C j := by
  intro N I _ G _ C hG _ hAO2 hF hfix hlive hnoA p1 l1 hdr
  have hnoA' : ∀ k2 < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).op =
      PEqualNP.CircuitLowerBounds.GateOp.and →
      ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k2).inputs, ¬ PEqualNP.Outside.L_meta_3652.WB G C t :=
    fun k2 hk2 hop t ht => hnoA k2 hk2 hop t ht
  unfold PEqualNP.ReadK.doubleReread at hdr
  rw [List.mem_filter] at hdr
  obtain ⟨hE, hsingle⟩ := hdr
  have hI : I p1 l1 := by
    rw [List.mem_flatMap] at hE
    obtain ⟨p5, _, h5⟩ := hE
    rw [List.mem_map] at h5
    obtain ⟨l6, hl6, heq⟩ := h5
    rw [List.mem_filter, decide_eq_true_eq] at hl6
    simp only [Prod.mk.injEq] at heq
    have hp : p5 = p1 := Fin.ext heq.1
    have hl : l6 = l1 := Fin.ext (by omega)
    subst hp
    subst hl
    exact hl6.2
  have hls : PEqualNP.ReadK.lineSingle C (N + N) (fun w => decide (N ≤ w)) p1.val (N + l1.val) =
      false := by
    cases h : PEqualNP.ReadK.lineSingle C (N + N) (fun w => decide (N ≤ w)) p1.val (N + l1.val)
    · rfl
    · rw [h] at hsingle
      simp at hsingle
  have hadj : G.Adj (Fin.castAdd N p1) (Fin.natAdd N l1) :=
    (hG _ _).2 ⟨p1, l1, hI, Or.inl ⟨rfl, rfl⟩⟩
  have hout_wb : PEqualNP.Outside.L_meta_3652.WB G C C.output := fun x hx => by
    rw [← congrFun hF x]
    exact hx
  have hout_val : PEqualNP.Outside.L_meta_3652.wireVal (N + N) C C.output
      (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd N p1) (Fin.natAdd N l1)) = true := by
    have h := congrFun hF (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd N p1) (Fin.natAdd N l1))
    rw [PEqualNP.Outside.L_meta_3652.graphFun_pair G hadj] at h
    exact h
  obtain ⟨j0, hj0, hoeq⟩ : ∃ j0, j0 < C.gates.length ∧ C.output = N + N + j0 := by
    by_cases hlt : C.output < N + N
    · exact absurd hout_wb (PEqualNP.Outside.L_meta_3652.input_not_WB hlt)
    · by_cases hge : N + N + C.gates.length ≤ C.output
      · rw [PEqualNP.Outside.L_meta_3652.wireVal_ge _ _ _ _ hge] at hout_val
        exact absurd hout_val (by simp)
      · exact ⟨C.output - (N + N), by omega, by omega⟩
  obtain ⟨g, hg, hgand, hgwb, hgval, hgls⟩ :=
    PEqualNP.Outside.L_meta_3652.descent hAO2 p1 l1
      (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd N p1) (Fin.natAdd N l1))
      (PEqualNP.ReadK.lineSingle C (N + N) (fun w => decide (N ≤ w)) p1.val (N + l1.val) = true)
      j0 hj0 (by rw [← hoeq]; exact hout_wb) (by rw [← hoeq]; exact hout_val)
      (fun h => by rw [PEqualNP.Outside.L_meta_3652.lineSingle_eq_lpAt, hoeq]; exact h)
  have hcore : PEqualNP.Core.IsCore G C g := by
    refine ⟨hg, ⟨hgwb, ⟨_, hgval⟩⟩, ?_, ⟨Fin.castAdd N p1, Fin.natAdd N l1, hadj, hgval, ?_⟩⟩
    · rintro ⟨⟨hle, hB0, _⟩, _⟩
      obtain ⟨_, hin, _, _⟩ := PEqualNP.Outside.L_meta_3652.ao2_gate_props hAO2 hg
      apply hnoA' g hg hgand (PEqualNP.TopForm.opnd C g 0) (by rw [hin]; simp)
      intro x hx
      apply hB0 x
      rwa [PEqualNP.Outside.L_meta_3652.gateVal_eq,
        show N + N + (PEqualNP.TopForm.opnd C g 0 - (N + N)) = PEqualNP.TopForm.opnd C g 0 by omega]
    · unfold PEqualNP.Core.ReadTwiceAt
      rw [Fin.val_castAdd, Fin.val_natAdd]
      by_contra hne
      rw [Bool.not_eq_false] at hne
      unfold PEqualNP.ReadK.readsAtMost at hne
      rw [List.any_eq_true] at hne
      obtain ⟨vec, hvec, hall⟩ := hne
      change vec ∈ (PEqualNP.ReadK.readVectors C (N + N) [p1.val, N + l1.val] 1).getD (N + N + g) []
        at hvec
      obtain ⟨hlen, h0v, h1v⟩ := PEqualNP.Outside.L_meta_3652.keyK hAO2 p1 l1 (N + N + g) vec hvec
      obtain ⟨a0, a1, rfl⟩ := PEqualNP.Outside.L_meta_3652.len_two hlen
      simp only [List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
        decide_eq_true_eq] at hall
      simp only [List.getD_cons_succ, List.getD_cons_zero] at h0v h1v
      rcases (by omega : a1 = 0 ∨ a1 = 1) with ha | ha
      · have h2 := hgwb _ (h0v ha)
        rw [show PEqualNP.Outside.L_meta_3652.pointInput N p1 =
          PEqualNP.Outside.L_meta_3652.single (N + N) p1.val from rfl,
          PEqualNP.Outside.L_meta_3652.graphFun_single] at h2
        exact absurd h2 (by simp)
      · have h2 := hgls (h1v ha)
        rw [hls] at h2
        exact absurd h2 (by simp)
  have hmax : PEqualNP.Core.IsMaximalCore G C g := by
    refine ⟨hcore, fun i hi hic hcone => ?_⟩
    have h2 := (PEqualNP.Outside.L_meta_3652.above_below hAO2 hfix hlive hnoA' g hgwb i hcone).1
    rw [PEqualNP.Outside.L_meta_3652.core_and hAO2 hic] at h2
    cases h2
  refine ⟨g, ?_, ?_⟩
  · unfold PEqualNP.Core.maximalCores PEqualNP.TopForm.gatesWhere
    rw [Finset.mem_filter, Finset.mem_range]
    exact ⟨hg, hmax⟩
  · unfold PEqualNP.TopForm.gammaE
    rw [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨hadj, _, _, rfl, hgval⟩
