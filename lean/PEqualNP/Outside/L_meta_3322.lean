import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3322_aux

open PEqualNP.CircuitLowerBounds

def rw (τ : Equiv.Perm (Fin 14)) (i : ℕ) : ℕ := if h : i < 14 then ((τ ⟨i, h⟩ : Fin 14) : ℕ) else i

def rg (τ : Equiv.Perm (Fin 14)) (g : Gate) : Gate := ⟨g.op, g.inputs.map (rw τ)⟩

def stp (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stp x := rfl

lemma rw_lt (τ : Equiv.Perm (Fin 14)) (i m : ℕ) (hm : 14 ≤ m) (hi : i < m) : rw τ i < m := by
  unfold rw; split
  · exact lt_of_lt_of_le (τ _).isLt hm
  · exact hi

lemma rw_ge (τ : Equiv.Perm (Fin 14)) (i : ℕ) (hi : 14 ≤ i) : rw τ i = i := by
  unfold rw; exact dite_eq_right_iff.mpr (fun h => absurd h (by omega))

def Inv (τ : Equiv.Perm (Fin 14)) (A B : List Bool) : Prop :=
  A.length = B.length ∧ 14 ≤ A.length ∧ ∀ i, A.getD (rw τ i) false = B.getD i false

lemma inv_step (τ : Equiv.Perm (Fin 14)) (A B : List Bool) (g : Gate) (h : Inv τ A B) :
    Inv τ (stp A (rg τ g)) (stp B g) := by
  obtain ⟨hl, h14, hv⟩ := h
  have hval : (rg τ g).op.eval ((rg τ g).inputs.map fun i => A.getD i false)
      = g.op.eval (g.inputs.map fun i => B.getD i false) := by
    simp only [rg, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hv i
  refine ⟨by simp [stp, hl], by simp [stp]; omega, fun i => ?_⟩
  simp only [stp]
  rw [hval]
  rcases lt_trichotomy i B.length with hi | hi | hi
  · have h1 : rw τ i < A.length := rw_lt τ i A.length h14 (hl ▸ hi)
    rw [List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ hi]
    exact hv i
  · subst hi
    rw [rw_ge τ _ (hl ▸ h14), ← hl]
    simp [List.getD_eq_getElem?_getD, hl]
  · rw [rw_ge τ _ (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

lemma inv_fold (τ : Equiv.Perm (Fin 14)) (gs : List Gate) :
    ∀ A B, Inv τ A B → Inv τ ((gs.map (rg τ)).foldl stp A) (gs.foldl stp B) := by
  induction gs with
  | nil => intro A B h; exact h
  | cons g gs ih => intro A B h; exact ih _ _ (inv_step τ A B g h)

lemma getD_ofFn14 (x : Fin 14 → Bool) (k : ℕ) (hk : k < 14) :
    (List.ofFn x).getD k false = x ⟨k, hk⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hk]

lemma inv_init (τ : Equiv.Perm (Fin 14)) (x : Fin 14 → Bool) :
    Inv τ (List.ofFn x) (List.ofFn (x ∘ τ)) := by
  refine ⟨by simp, by simp, fun i => ?_⟩
  by_cases hi : i < 14
  · have h1 : rw τ i = ((τ ⟨i, hi⟩ : Fin 14) : ℕ) := by simp [rw, hi]
    rw [h1, getD_ofFn14 _ _ (τ ⟨i, hi⟩).isLt, getD_ofFn14 _ _ hi]
    rfl
  · rw [rw_ge τ i (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

lemma permute_eval (τ : Equiv.Perm (Fin 14)) (C : Circuit) (x : Fin 14 → Bool) :
    (⟨C.gates.map (rg τ), rw τ C.output⟩ : Circuit).eval (List.ofFn x)
      = C.eval (List.ofFn (x ∘ τ)) := by
  simp only [Circuit.eval, wires_eq]
  exact (inv_fold τ C.gates _ _ (inv_init τ x)).2.2 C.output

def wf (σ : Equiv.Perm (Fin 14)) (c : Fin 15) : Fin 15 :=
  if h : c < 14 then ⟨((σ (Fin.ofNat 14 (c : ℕ)) : Fin 14) : ℕ), by omega⟩ else c

lemma wf_val (σ : Equiv.Perm (Fin 14)) (c : Fin 15) :
    ((wf σ c : Fin 15) : ℕ) = if c < 14 then ((σ (Fin.ofNat 14 (c : ℕ)) : Fin 14) : ℕ) else 14 := by
  unfold wf
  split
  · rfl
  · rename_i h
    have : (c : ℕ) = 14 := by
      have := c.isLt
      rw [Fin.lt_def] at h
      simp at h
      omega
    exact this

lemma ofNat_lt (c : ℕ) (hc : c < 14) : (Fin.ofNat 14 c : Fin 14) = ⟨c, hc⟩ := by
  ext; simp [Nat.mod_eq_of_lt hc]

lemma rw_wf (σ : Equiv.Perm (Fin 14)) (c : ℕ) (hc : c < 15) :
    rw σ c = ((wf σ ⟨c, hc⟩ : Fin 15) : ℕ) := by
  rw [wf_val]
  by_cases h : c < 14
  · have h' : (⟨c, hc⟩ : Fin 15) < 14 := by rw [Fin.lt_def]; simpa using h
    rw [if_pos h']
    simp only [rw, h, dite_true]
    rw [ofNat_lt c h]
  · have h' : ¬ (⟨c, hc⟩ : Fin 15) < 14 := by rw [Fin.lt_def]; simpa using h
    rw [if_neg h', rw_ge σ c (by omega)]
    omega

lemma wf_comp (ρ σ : Equiv.Perm (Fin 14)) (c : Fin 15) : wf ρ (wf σ c) = wf (ρ * σ) c := by
  apply Fin.ext
  rw [wf_val, wf_val, wf_val]
  by_cases h : c < 14
  · have hv : (c : ℕ) < 14 := by rw [Fin.lt_def] at h; simpa using h
    have h2 : wf σ c < 14 := by
      rw [Fin.lt_def, wf_val, if_pos h]; simp
    rw [if_pos h2, if_pos h, ofNat_lt _ (σ (Fin.ofNat 14 (c : ℕ))).isLt]
    simp only [Fin.eta, Equiv.Perm.mul_apply]
    rw [if_pos h]
  · have h2 : ¬ wf σ c < 14 := by
      rw [Fin.lt_def, wf_val, if_neg h]; simp
    rw [if_neg h2, if_neg h]

lemma wf_inj (σ : Equiv.Perm (Fin 14)) : Function.Injective (wf σ) := by
  intro c d h
  have h' := congrArg (fun t : Fin 15 => (t : ℕ)) h
  simp only [wf_val] at h'
  by_cases hc : c < 14 <;> by_cases hd : d < 14 <;> simp only [hc, hd, if_true, if_false] at h'
  · have hc' : (c : ℕ) < 14 := by rw [Fin.lt_def] at hc; simpa using hc
    have hd' : (d : ℕ) < 14 := by rw [Fin.lt_def] at hd; simpa using hd
    have := σ.injective (Fin.ext h')
    rw [ofNat_lt _ hc', ofNat_lt _ hd'] at this
    apply Fin.ext
    simpa using congrArg Fin.val this
  · exact absurd h' (by have := (σ (Fin.ofNat 14 (c : ℕ))).isLt; omega)
  · exact absurd h' (by have := (σ (Fin.ofNat 14 (d : ℕ))).isLt; omega)
  · have hc' : ¬ (c : ℕ) < 14 := by rw [Fin.lt_def] at hc; simpa using hc
    have hd' : ¬ (d : ℕ) < 14 := by rw [Fin.lt_def] at hd; simpa using hd
    apply Fin.ext; have := c.isLt; have := d.isLt; omega

lemma op_comm (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (u v : Bool) :
    op.eval [u, v] = op.eval [v, u] := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]

lemma op_mm {α : Type} [LinearOrder α] (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (f : α → Bool) (p q : α) : op.eval [f (min p q), f (max p q)] = op.eval [f p, f q] := by
  rcases le_total p q with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h]; exact op_comm op hop _ _

lemma nat_mm {α : Type} [LinearOrder α] (f : α → ℕ) (p q : α) :
    min (f (min p q)) (f (max p q)) = min (f p) (f q) ∧
      max (f (min p q)) (f (max p q)) = max (f p) (f q) := by
  rcases le_total p q with h | h
  · rw [min_eq_left h, max_eq_right h]; exact ⟨rfl, rfl⟩
  · rw [min_eq_right h, max_eq_left h]; exact ⟨min_comm _ _, max_comm _ _⟩

lemma min_lt_max' {α : Type} [LinearOrder α] (p q : α) (h : p ≠ q) : min p q < max p q := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]; exact h
  · rw [min_eq_right h.le, max_eq_left h.le]; exact h

def codeK (a b c d : ℕ) : ℕ := (15 * min a b + max a b) * 225 + (15 * min c d + max c d)

end PEqualNP.Outside.L_meta_3322_aux

open PEqualNP.Outside.L_meta_3322_aux PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_3322 : ∀ (x1 : (Fin (14 : ℕ) → Bool) → Bool) (x2 : PEqualNP.CircuitLowerBounds.Circuit),   PEqualNP.TopForm.IsAO2 (14 : ℕ) x2 →     (∀ x4 ∈ x2.gates, x4.inputs.Nodup) →       (2 : ℕ) ≤ x2.size →         x2.size ≤ (26 : ℕ) →           (∀ (x7 : Fin (14 : ℕ) → Bool), x2.eval (List.ofFn x7) = x1 x7) →             have x8 : ℕ → ℕ → ℕ → ℕ → ℕ := fun (x8 x9 x10 x11 : ℕ) => ((15 : ℕ) * Min.min x8 x9 + Max.max x8 x9) * (225 : ℕ) + ((15 : ℕ) * Min.min x10 x11 + Max.max x10 x11);             have x9 : Equiv.Perm (Fin (14 : ℕ)) → Fin (15 : ℕ) → ℕ := fun (x9 : Equiv.Perm (Fin (14 : ℕ))) (x10 : Fin (15 : ℕ)) => if x10 < (14 : Fin (15 : ℕ)) then ↑(x9 (Fin.ofNat (14 : ℕ) ↑x10)) else (14 : ℕ);             ∃ (x10 : Fin (14 : ℕ)) (x11 : Fin (14 : ℕ)) (x12 : Fin (15 : ℕ)) (x13 : Fin (15 : ℕ)) (x14 : PEqualNP.CircuitLowerBounds.GateOp) (x15 : PEqualNP.CircuitLowerBounds.GateOp) (x16 : PEqualNP.CircuitLowerBounds.Circuit),               x10 < x11 ∧                 x12 < x13 ∧                   (x14 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x14 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                     (x15 = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x15 = PEqualNP.CircuitLowerBounds.GateOp.or) ∧                       (∀ (x17 : Equiv.Perm (Fin (14 : ℕ))), (∀ (x18 : Fin (14 : ℕ) → Bool), x1 (x18 ∘ ⇑x17) = x1 x18) → x8 ↑x10 ↑x11 ↑x12 ↑x13 ≤ x8 (↑(x17 x10)) (↑(x17 x11)) (x9 x17 x12) (x9 x17 x13)) ∧                         PEqualNP.MetaComplexity.Monotone2 x16 ∧                           x16.size ≤ (24 : ℕ) ∧                             ∀ (x17 : Fin (14 : ℕ) → Bool),                               have x18 : List Bool := List.ofFn x17 ++ [x14.eval [x17 x10, x17 x11]];                               x16.eval (x18 ++ [x15.eval [x18.getD (↑x12) Bool.false, x18.getD (↑x13) Bool.false]]) = x1 x17 := by
  classical
  intro x1 x2 hAO hnd h2 h26 heval
  dsimp only
  obtain ⟨hand, hback, hlen⟩ := hAO
  obtain ⟨gates, out⟩ := x2
  rcases gates with _ | ⟨g0, _ | ⟨g1, rest⟩⟩
  · simp [Circuit.size] at h2
  · simp [Circuit.size] at h2
  have hsz : rest.length ≤ 24 := by simp [Circuit.size] at h26; omega
  have hop0 := hand g0 (by simp)
  have hop1 := hand g1 (by simp)
  obtain ⟨op0, ins0⟩ := g0
  obtain ⟨op1, ins1⟩ := g1
  simp only at hop0 hop1
  have hl0 : ins0.length = 2 := hlen ⟨op0, ins0⟩ (by simp)
  have hl1 : ins1.length = 2 := hlen ⟨op1, ins1⟩ (by simp)
  rcases ins0 with _ | ⟨a, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> simp at hl0
  rcases ins1 with _ | ⟨c, _ | ⟨d, _ | ⟨_, _⟩⟩⟩ <;> simp at hl1
  have hab : a ≠ b := by have := hnd ⟨op0, [a, b]⟩ (by simp); simpa using this
  have hcd : c ≠ d := by have := hnd ⟨op1, [c, d]⟩ (by simp); simpa using this
  have ha : a < 14 := by
    have := hback 0 (by simp) a (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt]); simpa using this
  have hb : b < 14 := by
    have := hback 0 (by simp) b (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt]); simpa using this
  have hc : c < 15 := by
    have := hback 1 (by simp) c (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt]); simpa using this
  have hd : d < 15 := by
    have := hback 1 (by simp) d (by simp [PEqualNP.MetaComplexity.NestedCover.gateAt]); simpa using this
  set A : Fin 14 := ⟨a, ha⟩
  set B : Fin 14 := ⟨b, hb⟩
  set Cc : Fin 15 := ⟨c, hc⟩
  set Dd : Fin 15 := ⟨d, hd⟩
  have hAB : A ≠ B := fun h => hab (congrArg Fin.val h)
  have hCD : Cc ≠ Dd := fun h => hcd (congrArg Fin.val h)
  let Aut : Finset (Equiv.Perm (Fin 14)) :=
    Finset.univ.filter (fun σ => ∀ y : Fin 14 → Bool, x1 (y ∘ σ) = x1 y)
  let F : Equiv.Perm (Fin 14) → ℕ := fun σ =>
    codeK ((σ A : Fin 14) : ℕ) ((σ B : Fin 14) : ℕ) ((wf σ Cc : Fin 15) : ℕ) ((wf σ Dd : Fin 15) : ℕ)
  have hne : Aut.Nonempty := ⟨1, by simp [Aut]⟩
  obtain ⟨σ, hσmem, hmin⟩ := Aut.exists_min_image F hne
  have hσ : ∀ y : Fin 14 → Bool, x1 (y ∘ σ) = x1 y := (Finset.mem_filter.mp hσmem).2
  refine ⟨min (σ A) (σ B), max (σ A) (σ B), min (wf σ Cc) (wf σ Dd), max (wf σ Cc) (wf σ Dd),
    op0, op1, ⟨rest.map (rg σ), rw σ out⟩, ?_, ?_, hop0, hop1, ?_, ?_, ?_, ?_⟩
  · exact min_lt_max' _ _ (fun h => hAB (σ.injective h))
  · exact min_lt_max' _ _ (fun h => hCD (wf_inj σ h))
  · intro ρ hρ
    have hρσ : ρ * σ ∈ Aut := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun y => ?_⟩
      have e : y ∘ ⇑(ρ * σ) = (y ∘ ρ) ∘ σ := by
        funext t; simp [Equiv.Perm.mul_apply]
      rw [e, hσ, hρ]
    have key := hmin _ hρσ
    simp only [F, codeK] at key
    rw [← wf_val ρ (min (wf σ Cc) (wf σ Dd)), ← wf_val ρ (max (wf σ Cc) (wf σ Dd))]
    obtain ⟨e1, e2⟩ := nat_mm (fun t : Fin 14 => (t : ℕ)) (σ A) (σ B)
    obtain ⟨e3, e4⟩ := nat_mm (fun t : Fin 15 => (t : ℕ)) (wf σ Cc) (wf σ Dd)
    obtain ⟨e5, e6⟩ := nat_mm (fun t : Fin 14 => ((ρ t : Fin 14) : ℕ)) (σ A) (σ B)
    obtain ⟨e7, e8⟩ := nat_mm (fun t : Fin 15 => ((wf ρ t : Fin 15) : ℕ)) (wf σ Cc) (wf σ Dd)
    rw [e1, e2, e3, e4, e5, e6, e7, e8, wf_comp, wf_comp]
    simpa using key
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    refine ⟨?_, ?_⟩
    · have := hand g' (by simp [hg'])
      rcases this with h | h <;> simp [rg, h]
    · simp [rg, hlen g' (by simp [hg'])]
  · simpa [Circuit.size] using hsz
  · intro x17
    have hrel := permute_eval σ ⟨⟨op0, [a, b]⟩ :: ⟨op1, [c, d]⟩ :: rest, out⟩ x17
    rw [heval, hσ] at hrel
    rw [← hrel]
    simp only [Circuit.eval, wires_eq, List.map_cons, List.foldl_cons]
    congr 2
    have hra : rw σ a = ((σ A : Fin 14) : ℕ) := by simp [rw, ha, A]
    have hrb : rw σ b = ((σ B : Fin 14) : ℕ) := by simp [rw, hb, B]
    have hrc : rw σ c = ((wf σ Cc : Fin 15) : ℕ) := rw_wf σ c hc
    have hrd : rw σ d = ((wf σ Dd : Fin 15) : ℕ) := rw_wf σ d hd
    have v0 : op0.eval [x17 (min (σ A) (σ B)), x17 (max (σ A) (σ B))]
        = op0.eval [(List.ofFn x17).getD (rw σ a) false, (List.ofFn x17).getD (rw σ b) false] := by
      rw [op_mm op0 hop0 x17, hra, hrb, getD_ofFn14 _ _ (σ A).isLt, getD_ofFn14 _ _ (σ B).isLt]
    simp only [stp, rg, List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
    rw [← v0]
    congr 3
    rw [hrc, hrd]
    exact op_mm op1 hop1 (fun t : Fin 15 => (List.ofFn x17 ++ [op0.eval [x17 (min (σ A) (σ B)), x17 (max (σ A) (σ B))]]).getD (t : ℕ) false) _ _
