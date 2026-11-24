import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3487

lemma key (s d : ℕ) (hs : s ≤ 7656) : s * d ≤ 44 * (d * (d - 1)) + 44 * s := by
  rcases Nat.lt_or_ge d 45 with h | h
  · nlinarith
  · obtain ⟨t, rfl⟩ : ∃ t, d = t + 45 := ⟨d - 45, by omega⟩
    have e : t + 45 - 1 = t + 44 := by omega
    rw [e]
    have h1 : s * (t + 1) ≤ 7656 * (t + 1) := Nat.mul_le_mul_right _ hs
    have h2 : (0 : ℤ) ≤ ((t : ℤ) - 42) * ((t : ℤ) - 43) := by
      rcases le_or_gt (t : ℤ) 42 with h3 | h3
      · nlinarith
      · nlinarith
    have h4 : 7656 * (t + 1) ≤ 44 * ((t + 45) * (t + 44)) := by
      zify
      nlinarith
    nlinarith

lemma bound {α β : Type*} [DecidableEq α] [DecidableEq β] (E : Finset (α × β))
    (h : ∀ (p r : α) (l m : β), p ≠ r → l ≠ m →
      ¬((p, l) ∈ E ∧ (r, l) ∈ E ∧ (p, m) ∈ E ∧ (r, m) ∈ E))
    (hs : (E.image Prod.fst).card ≤ 7656) :
    E.card ≤ 44 * ((E.image Prod.fst).card + (E.image Prod.snd).card - 1) := by
  set P := E.image Prod.fst with hP
  set L := E.image Prod.snd with hL
  set F : β → Finset (α × β) := fun l => E.filter (fun e => e.2 = l) with hF
  have hsum : E.card = ∑ l ∈ L, (F l).card := Finset.card_eq_sum_card_image Prod.snd E
  have hpairs : ∑ l ∈ L, (F l).card * ((F l).card - 1) ≤ P.card * (P.card - 1) := by
    have e1 : ∀ l ∈ L, (F l).card * ((F l).card - 1) = ((F l).offDiag).card := by
      intro l _
      rw [Finset.offDiag_card, Nat.mul_sub_one]
    rw [Finset.sum_congr rfl e1, ← Finset.card_sigma]
    have e2 : P.card * (P.card - 1) = P.offDiag.card := by
      rw [Finset.offDiag_card, Nat.mul_sub_one]
    rw [e2]
    apply Finset.card_le_card_of_injOn (fun x => (x.2.1.1, x.2.2.1))
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_offDiag, hF,
        Finset.mem_filter] at hx
      obtain ⟨_, ⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩ := hx
      simp only [Finset.mem_coe, Finset.mem_offDiag, hP, Finset.mem_image]
      refine ⟨⟨_, h1, rfl⟩, ⟨_, h3, rfl⟩, ?_⟩
      intro h6
      apply h5
      exact Prod.ext h6 (h2.trans h4.symm)
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_sigma, Finset.mem_offDiag, hF,
        Finset.mem_filter] at hx hy
      obtain ⟨_, ⟨hx1, hx2⟩, ⟨hx3, hx4⟩, hx5⟩ := hx
      obtain ⟨_, ⟨hy1, hy2⟩, ⟨hy3, hy4⟩, hy5⟩ := hy
      simp only [Prod.mk.injEq] at hxy
      obtain ⟨hp, hr⟩ := hxy
      have hne : x.2.1.1 ≠ x.2.2.1 := by
        intro h6
        exact hx5 (Prod.ext h6 (hx2.trans hx4.symm))
      have hl : x.1 = y.1 := by
        by_contra hl
        apply h x.2.1.1 x.2.2.1 x.1 y.1 hne hl
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [← hx2]; exact hx1
        · rw [← hx4]; exact hx3
        · rw [hp, ← hy2]; exact hy1
        · rw [hr, ← hy4]; exact hy3
      obtain ⟨l, a, c⟩ := x
      obtain ⟨l', a', c'⟩ := y
      simp only at hl hp hr hx2 hx4 hy2 hy4
      subst hl
      have ha : a = a' := Prod.ext hp (hx2.trans hy2.symm)
      have hc : c = c' := Prod.ext hr (hx4.trans hy4.symm)
      subst ha hc
      rfl
  have hmain : P.card * E.card ≤ P.card * (44 * (P.card + L.card - 1)) := by
    rw [hsum, Finset.mul_sum]
    calc ∑ l ∈ L, P.card * (F l).card
        ≤ ∑ l ∈ L, (44 * ((F l).card * ((F l).card - 1)) + 44 * P.card) :=
          Finset.sum_le_sum (fun l _ => key P.card (F l).card hs)
      _ = 44 * ∑ l ∈ L, (F l).card * ((F l).card - 1) + L.card * (44 * P.card) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, smul_eq_mul]
      _ ≤ 44 * (P.card * (P.card - 1)) + L.card * (44 * P.card) := by
          have := Nat.mul_le_mul_left 44 hpairs
          omega
      _ = P.card * (44 * (P.card + L.card - 1)) := by
          rcases Nat.eq_zero_or_pos P.card with h0 | h0
          · rw [h0]; simp
          · obtain ⟨k, hk⟩ : ∃ k, P.card = k + 1 := ⟨P.card - 1, by omega⟩
            rw [hk]
            have e3 : k + 1 + L.card - 1 = k + L.card := by omega
            rw [e3, Nat.add_sub_cancel]
            ring
  rcases Nat.eq_zero_or_pos P.card with h0 | h0
  · have : E = ∅ := by
      rw [hP, Finset.card_eq_zero, Finset.image_eq_empty] at h0
      exact h0
    rw [this]
    simp
  · exact Nat.le_of_mul_le_mul_left hmain h0

end PEqualNP.Outside.L_meta_3487

theorem PEqualNP.Outside.L_meta_3487 : ∀ (x1 : ℕ) (x2 : Finset (Fin x1 × Fin x1)), (∀ (x3 x4 x5 x6 : Fin x1), x3 ≠ x4 → x5 ≠ x6 → ¬((x3, x5) ∈ x2 ∧ (x4, x5) ∈ x2 ∧ (x3, x6) ∈ x2 ∧ (x4, x6) ∈ x2)) → Min.min (Finset.image Prod.fst x2).card (Finset.image Prod.snd x2).card ≤ (7656 : ℕ) → x2.card ≤ (44 : ℕ) * ((Finset.image Prod.fst x2).card + (Finset.image Prod.snd x2).card - (1 : ℕ)) := by
  intro N E h hmin
  rcases min_le_iff.mp hmin with h1 | h1
  · exact PEqualNP.Outside.L_meta_3487.bound E h h1
  · have hmem : ∀ x : Fin N × Fin N, x ∈ E.image Prod.swap ↔ x.swap ∈ E := by
      intro x
      constructor
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        simpa using hy
      · intro hx
        exact Finset.mem_image.mpr ⟨x.swap, hx, Prod.swap_swap x⟩
    have hc : (E.image Prod.swap).card = E.card :=
      Finset.card_image_of_injective _ Prod.swap_injective
    have hf : (E.image Prod.swap).image Prod.fst = E.image Prod.snd := by
      rw [Finset.image_image]; rfl
    have hs : (E.image Prod.swap).image Prod.snd = E.image Prod.fst := by
      rw [Finset.image_image]; rfl
    have h' : ∀ (p r l m : Fin N), p ≠ r → l ≠ m →
        ¬((p, l) ∈ E.image Prod.swap ∧ (r, l) ∈ E.image Prod.swap ∧
          (p, m) ∈ E.image Prod.swap ∧ (r, m) ∈ E.image Prod.swap) := by
      intro p r l m hpr hlm hx
      simp only [hmem, Prod.swap_prod_mk] at hx
      exact h l m p r hlm hpr ⟨hx.1, hx.2.2.1, hx.2.1, hx.2.2.2⟩
    have := PEqualNP.Outside.L_meta_3487.bound (E.image Prod.swap) h' (by rw [hf]; exact h1)
    rw [hc, hf, hs] at this
    rw [Nat.add_comm (Finset.image Prod.fst E).card]
    exact this
