import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4161

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

def boolStep (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def nw (ng : List Gate) (y : Fin 8 → Bool) : List Bool := scan boolStep ng (List.ofFn y)

lemma nw_length (ng : List Gate) (y : Fin 8 → Bool) : (nw ng y).length = 8 + ng.length := by
  simp [nw, scan_length]

lemma nw_snoc (ng : List Gate) (g : Gate) (y : Fin 8 → Bool) :
    nw (ng ++ [g]) y = nw ng y ++ [boolStep (nw ng y) g] := by
  unfold nw
  rw [scan_append]
  rfl

lemma nw_prefix (ng : List Gate) (g : Gate) (y : Fin 8 → Bool) (k : ℕ) (hk : k < 8 + ng.length) :
    (nw (ng ++ [g]) y).getD k false = (nw ng y).getD k false := by
  rw [nw_snoc, List.getD_append _ _ _ _ (by rw [nw_length]; exact hk)]

lemma nw_last (ng : List Gate) (g : Gate) (y : Fin 8 → Bool) :
    (nw (ng ++ [g]) y).getD (8 + ng.length) false = boolStep (nw ng y) g := by
  rw [nw_snoc, List.getD_append_right _ _ _ _ (by rw [nw_length]), nw_length, Nat.sub_self,
    List.getD_cons_zero]

def dval (w : List Bool) : Bool ⊕ ℕ → Bool
  | Sum.inl c => c
  | Sum.inr k => w.getD k false

def idx : Bool ⊕ ℕ → Option ℕ
  | Sum.inl _ => none
  | Sum.inr k => some k

def mkG (op : GateOp) (ds : List (Bool ⊕ ℕ)) : Gate :=
  match op with
  | GateOp.and =>
    if Sum.inl false ∈ ds then ⟨GateOp.or, []⟩ else ⟨GateOp.and, ds.filterMap idx⟩
  | GateOp.or =>
    if Sum.inl true ∈ ds then ⟨GateOp.and, []⟩ else ⟨GateOp.or, ds.filterMap idx⟩
  | GateOp.not =>
    match ds with
    | [] => ⟨GateOp.not, []⟩
    | Sum.inl c :: _ => if c then ⟨GateOp.or, []⟩ else ⟨GateOp.and, []⟩
    | Sum.inr k :: _ => ⟨GateOp.not, [k]⟩
  | _ => ⟨GateOp.or, []⟩

def remD (op : GateOp) (ds : List (Bool ⊕ ℕ)) : Bool ⊕ ℕ :=
  match op with
  | GateOp.or => Sum.inl true
  | GateOp.and =>
    match ds.filter (fun d => d != Sum.inl true) with
    | [] => Sum.inl true
    | [d] => d
    | _ => Sum.inl false
  | _ => Sum.inl false

def OkG (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

lemma mk_sem (w : List Bool) (op : GateOp) (ds : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ds.length ≤ 2) :
    (mkG op ds).op.eval ((mkG op ds).inputs.map fun i => w.getD i false) =
      op.eval (ds.map (dval w)) := by
  rcases ds with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [mkG, GateOp.eval]
  · rcases a with (_ | _) | k <;> rcases hop with rfl | rfl | rfl <;>
      simp [mkG, GateOp.eval, dval, idx]
  · rcases a with (_ | _) | k <;> rcases b with (_ | _) | k' <;> rcases hop with rfl | rfl | rfl <;>
      simp [mkG, GateOp.eval, dval, idx]
  · simp at hlen

lemma mk_ok (op : GateOp) (ds : List (Bool ⊕ ℕ))
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ds.length ≤ 2) :
    OkG (mkG op ds) := by
  rcases ds with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rcases hop with rfl | rfl | rfl <;> simp [mkG, OkG]
  · rcases a with (_ | _) | k <;> rcases hop with rfl | rfl | rfl <;> simp [mkG, OkG, idx] <;>
      exact (List.length_filterMap_le _ _).trans (by simp)
  · rcases a with (_ | _) | k <;> rcases b with (_ | _) | k' <;> rcases hop with rfl | rfl | rfl <;>
      simp [mkG, OkG, idx] <;> exact (List.length_filterMap_le _ _).trans (by simp)
  · simp at hlen

lemma rem_sem (w : List Bool) (op : GateOp) (ds : List (Bool ⊕ ℕ)) (hlen : ds.length ≤ 2)
    (h : ((op = GateOp.and ∨ op = GateOp.or) ∧ Sum.inl true ∈ ds) ∨
      (op = GateOp.not ∧ ds.head? = some (Sum.inl true))) :
    op.eval (ds.map (dval w)) = dval w (remD op ds) := by
  rcases ds with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rcases h with ⟨_, h⟩ | ⟨_, h⟩ <;> simp at h
  · rcases h with ⟨hop | hop, h⟩ | ⟨hop, h⟩ <;> subst hop <;>
      rcases a with (_ | _) | k <;> simp_all [remD, GateOp.eval, dval]
  · rcases h with ⟨hop | hop, h⟩ | ⟨hop, h⟩ <;> subst hop <;>
      rcases a with (_ | _) | k <;> rcases b with (_ | _) | k' <;>
      simp_all [remD, GateOp.eval, dval]
  · simp at hlen

lemma remD_mem (op : GateOp) (ds : List (Bool ⊕ ℕ)) (hlen : ds.length ≤ 2) :
    (∃ c, remD op ds = Sum.inl c) ∨ remD op ds ∈ ds := by
  rcases ds with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · rcases op <;> simp [remD]
  · rcases a with (_ | _) | k <;> rcases op <;> simp [remD]
  · rcases a with (_ | _) | k <;> rcases b with (_ | _) | k' <;> rcases op <;> simp [remD]
  · simp at hlen

lemma getD_mem {α : Type} (l : List α) (i : ℕ) (d : α) : l.getD i d ∈ l ∨ l.getD i d = d := by
  by_cases h : i < l.length
  · left
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · right
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    rfl

def stepK (s : List (Bool ⊕ ℕ) × List Gate) (g : Gate) : List (Bool ⊕ ℕ) × List Gate :=
  (s.1 ++ [Sum.inr (8 + s.2.length)],
    s.2 ++ [mkG g.op (g.inputs.map fun i => s.1.getD i (Sum.inl false))])

def stepR (s : List (Bool ⊕ ℕ) × List Gate) (g : Gate) : List (Bool ⊕ ℕ) × List Gate :=
  (s.1 ++ [remD g.op (g.inputs.map fun i => s.1.getD i (Sum.inl false))], s.2)

def stepP (P : Gate → Bool) (s : List (Bool ⊕ ℕ) × List Gate) (g : Gate) :
    List (Bool ⊕ ℕ) × List Gate :=
  if P g then stepR s g else stepK s g

def Inv (y : Fin 8 → Bool) (s : List (Bool ⊕ ℕ) × List Gate) (ow : List Bool) : Prop :=
  s.1.length = ow.length ∧ (∀ k, Sum.inr k ∈ s.1 → k < 8 + s.2.length) ∧
    (∀ g ∈ s.2, OkG g) ∧ ∀ i, ow.getD i false = dval (nw s.2 y) (s.1.getD i (Sum.inl false))

lemma ins_mem (s : List (Bool ⊕ ℕ)) (g : Gate) (d : Bool ⊕ ℕ)
    (hd : d ∈ g.inputs.map fun i => s.getD i (Sum.inl false)) : d ∈ s ∨ d = Sum.inl false := by
  rw [List.mem_map] at hd
  obtain ⟨i, _, rfl⟩ := hd
  exact getD_mem s i _

lemma new_val (y : Fin 8 → Bool) (s : List (Bool ⊕ ℕ) × List Gate) (ow : List Bool) (g : Gate)
    (hI : Inv y s ow) :
    boolStep ow g = g.op.eval ((g.inputs.map fun i => s.1.getD i (Sum.inl false)).map
      (dval (nw s.2 y))) := by
  unfold boolStep
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  exact hI.2.2.2 i

lemma inv_stepK (y : Fin 8 → Bool) (s : List (Bool ⊕ ℕ) × List Gate) (ow : List Bool) (g : Gate)
    (hI : Inv y s ow) (hg : OkG g) : Inv y (stepK s g) (ow ++ [boolStep ow g]) := by
  have hval := new_val y s ow g hI
  obtain ⟨hlen, hb, hok, hc⟩ := hI
  have hdl : (g.inputs.map fun i => s.1.getD i (Sum.inl false)).length ≤ 2 := by
    rw [List.length_map]; exact hg.2
  have hstab : ∀ d, (d ∈ s.1 ∨ d = Sum.inl false) →
      dval (nw (s.2 ++ [mkG g.op (g.inputs.map fun i => s.1.getD i (Sum.inl false))]) y) d =
        dval (nw s.2 y) d := by
    intro d hd
    rcases d with c | k
    · rfl
    · have hk : k < 8 + s.2.length := by
        rcases hd with hd | hd
        · exact hb k hd
        · cases hd
      exact nw_prefix _ _ y k hk
  refine ⟨by simp [stepK, hlen], ?_, ?_, ?_⟩
  · intro k hk
    simp only [stepK, List.mem_append, List.mem_singleton, List.length_append,
      List.length_singleton] at hk ⊢
    rcases hk with hk | hk
    · have := hb k hk
      omega
    · cases hk
      omega
  · intro g' hg'
    simp only [stepK, List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | hg'
    · exact hok g' hg'
    · subst hg'
      exact mk_ok _ _ hg.1 hdl
  · intro i
    simp only [stepK]
    by_cases hi : i < ow.length
    · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega), hc i]
      exact (hstab _ (getD_mem s.1 i _)).symm
    · by_cases he : i = ow.length
      · subst he
        rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
          List.getD_append_right _ _ _ _ (by omega), show ow.length - s.1.length = 0 by omega,
          List.getD_cons_zero]
        show boolStep ow g = (nw (s.2 ++ [_]) y).getD (8 + s.2.length) false
        rw [nw_last, hval]
        unfold boolStep
        rw [mk_sem _ _ _ hg.1 hdl]
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
          List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
        rfl

lemma inv_stepR (y : Fin 8 → Bool) (s : List (Bool ⊕ ℕ) × List Gate) (ow : List Bool) (g : Gate)
    (hI : Inv y s ow) (hg : OkG g)
    (hR : ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        Sum.inl true ∈ (g.inputs.map fun i => s.1.getD i (Sum.inl false))) ∨
      (g.op = GateOp.not ∧ (g.inputs.map fun i => s.1.getD i (Sum.inl false)).head? =
        some (Sum.inl true))) :
    Inv y (stepR s g) (ow ++ [boolStep ow g]) := by
  have hval := new_val y s ow g hI
  obtain ⟨hlen, hb, hok, hc⟩ := hI
  have hdl : (g.inputs.map fun i => s.1.getD i (Sum.inl false)).length ≤ 2 := by
    rw [List.length_map]; exact hg.2
  refine ⟨by simp [stepR, hlen], ?_, hok, ?_⟩
  · intro k hk
    simp only [stepR, List.mem_append, List.mem_singleton] at hk ⊢
    rcases hk with hk | hk
    · exact hb k hk
    · rcases remD_mem g.op _ hdl with ⟨c, hc'⟩ | hm
      · rw [hc'] at hk
        cases hk
      · rw [← hk] at hm
        rcases ins_mem s.1 g _ hm with hm | hm
        · exact hb k hm
        · cases hm
  · intro i
    simp only [stepR]
    by_cases hi : i < ow.length
    · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (by omega), hc i]
    · by_cases he : i = ow.length
      · subst he
        rw [List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self, List.getD_cons_zero,
          List.getD_append_right _ _ _ _ (by omega), show ow.length - s.1.length = 0 by omega,
          List.getD_cons_zero, hval]
        exact rem_sem _ _ _ hdl hR
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega),
          List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
        rfl

def x2f (g : Gate) : List ℕ := if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs

lemma rv_of (s : List (Bool ⊕ ℕ)) (g : Gate) (hg : OkG g) (t : ℕ) (ht : t ∈ x2f g)
    (hd : s.getD t (Sum.inl false) = Sum.inl true) :
    ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧
        Sum.inl true ∈ (g.inputs.map fun i => s.getD i (Sum.inl false))) ∨
      (g.op = GateOp.not ∧ (g.inputs.map fun i => s.getD i (Sum.inl false)).head? =
        some (Sum.inl true)) := by
  rcases hg.1 with hop | hop | hop
  · left
    refine ⟨Or.inl hop, ?_⟩
    have ht' : t ∈ g.inputs := by
      simpa [x2f, hop, GateOp.eval] using ht
    exact List.mem_map.mpr ⟨t, ht', hd⟩
  · left
    refine ⟨Or.inr hop, ?_⟩
    have ht' : t ∈ g.inputs := by
      simpa [x2f, hop, GateOp.eval] using ht
    exact List.mem_map.mpr ⟨t, ht', hd⟩
  · right
    refine ⟨hop, ?_⟩
    have ht' : t ∈ g.inputs.take 1 := by
      simpa [x2f, hop, GateOp.eval] using ht
    rcases hin : g.inputs with _ | ⟨a, rest⟩
    · rw [hin] at ht'
      simp at ht'
    · rw [hin] at ht'
      simp at ht'
      subst ht'
      rw [List.map_cons, List.head?_cons, hd]

lemma fold_inv (y : Fin 8 → Bool) (P : Gate → Bool) (T : List ℕ) :
    ∀ (gs : List Gate) (s : List (Bool ⊕ ℕ) × List Gate) (ow : List Bool),
    Inv y s ow → (∀ t ∈ T, s.1.getD t (Sum.inl false) = Sum.inl true ∧ t < s.1.length) →
    (∀ g ∈ gs, OkG g) → (∀ g ∈ gs, P g = true → ∃ t ∈ T, t ∈ x2f g) →
    Inv y (gs.foldl (stepP P) s) (scan boolStep gs ow) ∧
      (∀ t ∈ T, (gs.foldl (stepP P) s).1.getD t (Sum.inl false) = Sum.inl true ∧
        t < (gs.foldl (stepP P) s).1.length) := by
  intro gs
  induction gs with
  | nil => intro s ow hI hT _ _; exact ⟨hI, hT⟩
  | cons g gs ih =>
    intro s ow hI hT hok hP
    have hg := hok g (by simp)
    have hI' : Inv y (stepP P s g) (ow ++ [boolStep ow g]) := by
      unfold stepP
      split_ifs with hpg
      · obtain ⟨t, htT, htx⟩ := hP g (by simp) hpg
        exact inv_stepR y s ow g hI hg (rv_of s.1 g hg t htx (hT t htT).1)
      · exact inv_stepK y s ow g hI hg
    have hT' : ∀ t ∈ T, (stepP P s g).1.getD t (Sum.inl false) = Sum.inl true ∧
        t < (stepP P s g).1.length := by
      intro t ht
      obtain ⟨h1, h2⟩ := hT t ht
      unfold stepP
      split_ifs
      · simp only [stepR]
        exact ⟨by rw [List.getD_append _ _ _ _ h2]; exact h1, by simp; omega⟩
      · simp only [stepK]
        exact ⟨by rw [List.getD_append _ _ _ _ h2]; exact h1, by simp; omega⟩
    exact ih (stepP P s g) (ow ++ [boolStep ow g]) hI' hT'
      (fun g' hg' => hok g' (by simp [hg'])) (fun g' hg' => hP g' (by simp [hg']))

lemma fold_len (P : Gate → Bool) :
    ∀ (gs : List Gate) (s : List (Bool ⊕ ℕ) × List Gate),
    (gs.foldl (stepP P) s).2.length = s.2.length + (gs.filter (fun g => !P g)).length := by
  intro gs
  induction gs with
  | nil => intro s; simp
  | cons g gs ih =>
    intro s
    rw [List.foldl_cons, ih]
    by_cases hpg : P g = true
    · simp [stepP, stepR, hpg, List.filter_cons]
    · have hpf : P g = false := by simpa using hpg
      simp [stepP, stepK, hpf, List.filter_cons]
      all_goals omega

def inputMap : List (Bool ⊕ ℕ) :=
  [Sum.inr 1, Sum.inr 0, Sum.inr 4, Sum.inr 7, Sum.inr 5, Sum.inr 2, Sum.inl true, Sum.inr 6,
    Sum.inr 3, Sum.inl true]

def oldIn (b : Bool) (y : Fin 8 → Bool) : List Bool :=
  [y 1, y 0, y 4, y 7, y 5, y 2, b, y 6, y 3, y 1 || b]

lemma ofFn_getD (y : Fin 8 → Bool) (k : ℕ) (hk : k < 8) :
    (List.ofFn y).getD k false = y ⟨k, hk⟩ := by
  rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_ofFn]

lemma inv_init (y : Fin 8 → Bool) : Inv y (inputMap, []) (oldIn true y) := by
  refine ⟨rfl, ?_, by simp, ?_⟩
  · intro k hk
    simp [inputMap] at hk
    simp
    omega
  · intro i
    have hn : nw [] y = List.ofFn y := rfl
    simp only [hn]
    match i with
    | 0 => simp [oldIn, inputMap, dval]
    | 1 => simp [oldIn, inputMap, dval]
    | 2 => simp [oldIn, inputMap, dval]
    | 3 => simp [oldIn, inputMap, dval]
    | 4 => simp [oldIn, inputMap, dval]
    | 5 => simp [oldIn, inputMap, dval]
    | 6 => simp [oldIn, inputMap, dval]
    | 7 => simp [oldIn, inputMap, dval]
    | 8 => simp [oldIn, inputMap, dval]
    | 9 => simp [oldIn, inputMap, dval]
    | n + 10 =>
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [oldIn]),
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [inputMap])]
      rfl

lemma okG_of_fan (C : Circuit) (hF : FanInTwo C) : ∀ g ∈ C.gates, OkG g := by
  intro g hg
  obtain ⟨hop, hlen⟩ := hF g hg
  refine ⟨?_, hlen⟩
  simpa using hop

def P1g (g : Gate) : Bool := (x2f g).contains 9

def P3g (n : ℕ) (g : Gate) : Bool := (x2f g).contains 9 || (x2f g).contains (10 + n)

theorem main (x3 x4 : List Gate) (x5 : Gate) (x6 : ℕ)
    (hF : FanInTwo ⟨x3 ++ x5 :: x4, x6⟩) (hop : x5.op = GateOp.or)
    (h6 : ((x2f x5).any fun i => decide (i = 6)) = true) :
    HasCircuitSize 8 (fun y => Circuit.eval ⟨x3 ++ x5 :: x4, x6⟩ (oldIn true y))
      (max 1 (x3.length + x4.length - ((x3.filter fun g => (x2f g).contains 9).length +
        (x4.filter fun g => (x2f g).contains 9 || (x2f g).contains (10 + x3.length)).length))) := by
  have hok := okG_of_fan _ hF
  have hok3 : ∀ g ∈ x3, OkG g := fun g hg => hok g (by simp [hg])
  have hok4 : ∀ g ∈ x4, OkG g := fun g hg => hok g (by simp [hg])
  have hok5 : OkG x5 := hok x5 (by simp)
  set s1 := x3.foldl (stepP P1g) (inputMap, []) with hs1
  set s2 := stepR s1 x5 with hs2
  set s3 := x4.foldl (stepP (P3g x3.length)) s2 with hs3
  have h6' : 6 ∈ x2f x5 := by
    rw [List.any_eq_true] at h6
    obtain ⟨i, hi, he⟩ := h6
    simp only [decide_eq_true_eq] at he
    rw [← he]
    exact hi
  have keyInv : ∀ y : Fin 8 → Bool, Inv y s3 (scan boolStep x4
      (scan boolStep x3 (oldIn true y) ++ [boolStep (scan boolStep x3 (oldIn true y)) x5])) := by
    intro y
    have hT0 : ∀ t ∈ [6, 9], (inputMap, ([] : List Gate)).1.getD t (Sum.inl false) =
        Sum.inl true ∧ t < (inputMap, ([] : List Gate)).1.length := by
      intro t ht
      simp at ht
      rcases ht with rfl | rfl <;> simp [inputMap]
    obtain ⟨hI1, hT1⟩ := fold_inv y P1g [6, 9] x3 (inputMap, []) (oldIn true y) (inv_init y) hT0
      hok3 (fun g _ hg => ⟨9, by simp, by simpa [P1g] using hg⟩)
    rw [← hs1] at hI1 hT1
    have hR5 := rv_of s1.1 x5 hok5 6 h6' (hT1 6 (by simp)).1
    have hI2 := inv_stepR y s1 _ x5 hI1 hok5 hR5
    rw [← hs2] at hI2
    have hlen1 : s1.1.length = 10 + x3.length := by
      rw [hI1.1, scan_length]
      simp only [oldIn, List.length_cons, List.length_nil]
      all_goals omega
    have hT2 : ∀ t ∈ [9, 10 + x3.length], s2.1.getD t (Sum.inl false) = Sum.inl true ∧
        t < s2.1.length := by
      intro t ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rw [hs2]
      simp only [stepR]
      rcases ht with rfl | rfl
      · obtain ⟨h1, h2⟩ := hT1 9 (by simp)
        refine ⟨?_, by simp; omega⟩
        rw [List.getD_append _ _ _ _ h2]
        exact h1
      · refine ⟨?_, by simp; omega⟩
        rw [List.getD_append_right _ _ _ _ (by omega),
          show 10 + x3.length - s1.1.length = 0 by omega, List.getD_cons_zero, hop]
        rfl
    obtain ⟨hI3, _⟩ := fold_inv y (P3g x3.length) [9, 10 + x3.length] x4 s2 _ hI2 hT2 hok4
      (fun g _ hg => by
        simp only [P3g, Bool.or_eq_true] at hg
        rcases hg with hg | hg
        · exact ⟨9, by simp, by simpa using hg⟩
        · exact ⟨10 + x3.length, by simp, by simpa using hg⟩)
    rw [← hs3] at hI3
    exact hI3
  have key : ∀ y : Fin 8 → Bool, Circuit.eval ⟨x3 ++ x5 :: x4, x6⟩ (oldIn true y) =
      dval (nw s3.2 y) (s3.1.getD x6 (Sum.inl false)) := by
    intro y
    have hw : (Circuit.wires ⟨x3 ++ x5 :: x4, x6⟩ (oldIn true y)) =
        scan boolStep x4 (scan boolStep x3 (oldIn true y) ++
          [boolStep (scan boolStep x3 (oldIn true y)) x5]) := by
      show scan boolStep (x3 ++ x5 :: x4) (oldIn true y) = _
      rw [scan_append, scan_cons]
    show (Circuit.wires ⟨x3 ++ x5 :: x4, x6⟩ (oldIn true y)).getD x6 false = _
    rw [hw]
    exact (keyInv y).2.2.2 x6
  have hsize : s3.2.length ≤ max 1 (x3.length + x4.length -
      ((x3.filter fun g => (x2f g).contains 9).length +
        (x4.filter fun g => (x2f g).contains 9 || (x2f g).contains (10 + x3.length)).length)) := by
    rw [hs3, fold_len, hs2]
    simp only [stepR]
    rw [hs1, fold_len]
    simp only [List.length_nil, Nat.zero_add]
    apply le_max_of_le_right
    have l3 := List.length_eq_length_filter_add (l := x3) P1g
    have l4 := List.length_eq_length_filter_add (l := x4) (P3g x3.length)
    change _ ≤ x3.length + x4.length - ((x3.filter P1g).length + (x4.filter (P3g x3.length)).length)
    omega
  rcases hd : s3.1.getD x6 (Sum.inl false) with c | k
  · cases c
    · refine ⟨⟨[], 8⟩, ?_, ?_, ?_⟩
      · intro g hg
        simp at hg
      · simp [Circuit.size]
      · intro y
        beta_reduce
        rw [key y, hd]
        show (List.ofFn y).getD 8 false = false
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp)]
        rfl
    · refine ⟨⟨[⟨GateOp.and, []⟩], 8⟩, ?_, ?_, ?_⟩
      · intro g hg
        simp at hg
        subst hg
        simp
      · simp [Circuit.size]
      · intro y
        beta_reduce
        rw [key y, hd]
        show (List.ofFn y ++ [GateOp.eval GateOp.and
          (List.map (fun i => (List.ofFn y).getD i false) [])]).getD 8 false = true
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp [GateOp.eval]
  · refine ⟨⟨s3.2, k⟩, ?_, ?_, ?_⟩
    · intro g hg
      have h := (keyInv (fun _ => false)).2.2.1 g hg
      refine ⟨?_, h.2⟩
      rcases h.1 with h1 | h1 | h1 <;> simp [h1]
    · simpa [Circuit.size] using hsize
    · intro y
      beta_reduce
      rw [key y, hd]
      rfl

end PEqualNP.Outside.L_meta_4161

theorem PEqualNP.Outside.L_meta_4161 : have x1 : Bool → (Fin (8 : ℕ) → Bool) → List Bool := fun (x1 : Bool) (x2 : Fin (8 : ℕ) → Bool) => [x2 (1 : Fin (8 : ℕ)), x2 (0 : Fin (8 : ℕ)), x2 (4 : Fin (8 : ℕ)), x2 (7 : Fin (8 : ℕ)), x2 (5 : Fin (8 : ℕ)), x2 (2 : Fin (8 : ℕ)), x1, x2 (6 : Fin (8 : ℕ)), x2 (3 : Fin (8 : ℕ)), x2 (1 : Fin (8 : ℕ)) || x1]; have x2 : PEqualNP.CircuitLowerBounds.Gate → List ℕ := fun (x2 : PEqualNP.CircuitLowerBounds.Gate) => if x2.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x2.inputs else x2.inputs; ∀ (x3 x4 : List PEqualNP.CircuitLowerBounds.Gate) (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : ℕ),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := x3 ++ x5 :: x4, output := x6 : PEqualNP.CircuitLowerBounds.Circuit };   PEqualNP.MetaComplexity.FanInTwo x7 → x5.op = PEqualNP.CircuitLowerBounds.GateOp.or → ((x2 x5).any fun (x10 : ℕ) => Decidable.decide (x10 = (6 : ℕ))) = Bool.true → PEqualNP.MetaComplexity.HasCircuitSize (8 : ℕ) (fun (x11 : Fin (8 : ℕ) → Bool) => x7.eval (x1 Bool.true x11)) (Max.max (1 : ℕ) (x3.length + x4.length - ((List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => (x2 x11).contains (9 : ℕ)) x3).length + (List.filter (fun (x11 : PEqualNP.CircuitLowerBounds.Gate) => (x2 x11).contains (9 : ℕ) || (x2 x11).contains ((10 : ℕ) + x3.length)) x4).length))) := by
  dsimp only
  intro x3 x4 x5 x6 hF hop h6
  exact PEqualNP.Outside.L_meta_4161.main x3 x4 x5 x6 hF hop h6
