import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.L_meta_2702 : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj],   have x3 : Finset (Fin (11 : ℕ)) := {(3 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))};   have x4 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ)))};   (∀ (x5 x6 : Fin (11 : ℕ)), x1.Adj x5 x6 → x5 ∈ x3 ∨ x6 ∈ x3 ∨ (x5, x6) ∈ x4 ∨ (x6, x5) ∈ x4) →     ∀ (x6 : Finset (Fin (11 : ℕ))),       PEqualNP.MetaComplexity.NestedCover.IsMinCover x1 x6 →         ∃ x8 ⊆ x3,           (∀ x9 ∈ x3 \ x8, ∀ x11 ∈ x3 \ x8, ¬x1.Adj x9 x11) ∧             have x9 : Finset (Fin (11 : ℕ)) := {x9 ∈ Finset.univ \ x3 | ∃ x10 ∈ x3 \ x8, x1.Adj x10 x9};             have x10 : Finset (Fin (11 : ℕ) × Fin (11 : ℕ)) := {x10 ∈ x4 | x1.Adj x10.1 x10.2 ∧ x10.1 ∉ x9 ∧ x10.2 ∉ x9};             x6.card = x8.card + x9.card + x10.card := by
  intro G _ X3 P hE T hT
  have hcov : ∀ a b : Fin 11, G.Adj a b → a ∈ T ∨ b ∈ T := fun a b h => hT.1 h
  have hPmem : ∀ p, p ∈ P ↔ p = (1, 4) ∨ p = (2, 5) ∨ p = (6, 7) := by
    intro p
    simp only [P, Finset.mem_insert, Finset.mem_singleton]
  have hX3mem : ∀ v, v ∈ X3 ↔ v = 3 ∨ v = 8 ∨ v = 9 ∨ v = 10 := by
    intro v
    simp only [X3, Finset.mem_insert, Finset.mem_singleton]
  have hPout : ∀ p ∈ P, p.1 ∉ X3 ∧ p.2 ∉ X3 := by
    intro p hp
    rw [hPmem] at hp
    rw [hX3mem, hX3mem]
    rcases hp with rfl | rfl | rfl <;> decide
  have hPinj : ∀ p ∈ P, ∀ q ∈ P, (p.1 = q.1 ∨ p.1 = q.2 ∨ p.2 = q.1 ∨ p.2 = q.2) → p = q := by
    intro p hp q hq h
    rw [hPmem] at hp hq
    rcases hp with rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl <;> first | rfl | (exfalso; revert h; decide)
  refine ⟨T ∩ X3, Finset.inter_subset_right, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Finset.mem_sdiff, Finset.mem_inter, not_and] at ha hb
    rcases hcov a b hab with h | h
    · exact ha.2 h ha.1
    · exact hb.2 h hb.1
  · intro Z M
    have hZ : ∀ v, v ∈ Z ↔ v ∉ X3 ∧ ∃ u ∈ X3, u ∉ T ∧ G.Adj u v := by
      intro v
      simp only [Z, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
        Finset.mem_inter, not_and]
      constructor
      · rintro ⟨hv, u, ⟨hu1, hu2⟩, hadj⟩
        exact ⟨hv, u, hu1, fun h => hu2 h hu1, hadj⟩
      · rintro ⟨hv, u, hu1, hu2, hadj⟩
        exact ⟨hv, u, ⟨hu1, fun h _ => hu2 h⟩, hadj⟩
    have hM : ∀ p, p ∈ M ↔ p ∈ P ∧ G.Adj p.1 p.2 ∧ p.1 ∉ Z ∧ p.2 ∉ Z := by
      intro p
      simp only [M, Finset.mem_filter]
    -- upper bound: an explicit cover
    have hC : G.IsVertexCover ((T ∩ X3 ∪ Z ∪ M.image Prod.fst : Finset (Fin 11)) : Set (Fin 11)) := by
      intro u v huv
      simp only [Finset.coe_union, Finset.coe_inter, Set.mem_union, Set.mem_inter_iff,
        Finset.mem_coe, Finset.coe_image, Set.mem_image]
      rcases hE u v huv with hu | hv | hp | hp
      · by_cases huT : u ∈ T
        · left; left; left; exact ⟨huT, hu⟩
        · by_cases hvX : v ∈ X3
          · right; left; left
            exact ⟨(hcov u v huv).resolve_left huT, hvX⟩
          · right; left; right
            exact (hZ v).2 ⟨hvX, u, hu, huT, huv⟩
      · by_cases hvT : v ∈ T
        · right; left; left; exact ⟨hvT, hv⟩
        · by_cases huX : u ∈ X3
          · left; left; left
            exact ⟨(hcov u v huv).resolve_right hvT, huX⟩
          · left; left; right
            exact (hZ u).2 ⟨huX, v, hv, hvT, huv.symm⟩
      · by_cases huZ : u ∈ Z
        · left; left; right; exact huZ
        · by_cases hvZ : v ∈ Z
          · right; left; right; exact hvZ
          · left; right; exact ⟨(u, v), (hM (u, v)).2 ⟨hp, huv, huZ, hvZ⟩, rfl⟩
      · by_cases huZ : u ∈ Z
        · left; left; right; exact huZ
        · by_cases hvZ : v ∈ Z
          · right; left; right; exact hvZ
          · right; right; exact ⟨(v, u), (hM (v, u)).2 ⟨hp, huv.symm, hvZ, huZ⟩, rfl⟩
    have hup : T.card ≤ (T ∩ X3).card + Z.card + M.card := by
      refine (hT.2 _ hC).trans ?_
      refine (Finset.card_union_le _ _).trans ?_
      refine Nat.add_le_add ((Finset.card_union_le _ _)) Finset.card_image_le
    -- lower bound: three disjoint pieces of T
    let W : Finset (Fin 11) := M.image (fun p => if p.1 ∈ T then p.1 else p.2)
    have hWT : W ⊆ T := by
      intro w hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
      have hadj := ((hM p).1 hp).2.1
      split_ifs with h
      · exact h
      · exact (hcov _ _ hadj).resolve_left h
    have hW : W.card = M.card := by
      apply Finset.card_image_of_injOn
      intro p hp q hq hpq
      have hp' := ((hM p).1 hp).1
      have hq' := ((hM q).1 hq).1
      apply hPinj p hp' q hq'
      simp only at hpq
      split_ifs at hpq <;> tauto
    have hZT : Z ⊆ T := by
      intro v hv
      obtain ⟨-, u, -, huT, hadj⟩ := (hZ v).1 hv
      exact (hcov u v hadj).resolve_left huT
    have hd1 : Disjoint (T ∩ X3) Z := by
      rw [Finset.disjoint_left]
      intro a ha hz
      exact ((hZ a).1 hz).1 (Finset.mem_inter.mp ha).2
    have hd2 : Disjoint (T ∩ X3 ∪ Z) W := by
      rw [Finset.disjoint_left]
      intro a ha hw
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hw
      obtain ⟨hpP, -, hz1, hz2⟩ := (hM p).1 hp
      obtain ⟨ho1, ho2⟩ := hPout p hpP
      rcases Finset.mem_union.mp ha with ha | ha
      · have := (Finset.mem_inter.mp ha).2
        split_ifs at this
        · exact ho1 this
        · exact ho2 this
      · split_ifs at ha
        · exact hz1 ha
        · exact hz2 ha
    have hlow : (T ∩ X3).card + Z.card + M.card ≤ T.card := by
      rw [← hW, ← Finset.card_union_of_disjoint hd1, ← Finset.card_union_of_disjoint hd2]
      apply Finset.card_le_card
      intro a ha
      rcases Finset.mem_union.mp ha with ha | ha
      · rcases Finset.mem_union.mp ha with ha | ha
        · exact (Finset.mem_inter.mp ha).1
        · exact hZT ha
      · exact hWT ha
    omega
