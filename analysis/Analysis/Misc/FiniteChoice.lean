import Mathlib.Tactic

theorem finite_choice {X:Type*} {f:X → ℕ} {N:ℕ} (h: ∀ n < N, ∃ x, f x = n) :
  ∃ g: Fin N → X, ∀ n, f (g n) = n := by
  induction' N with N ih
  . simp
  specialize ih ?_
  . intro n hn; exact h n (by linarith)
  obtain ⟨ g, hg ⟩ := ih
  specialize h N (by linarith); obtain ⟨ x, hx ⟩ := h
  set g' : Fin (N+1) → X := fun n ↦ if h:n.val < N then g ⟨ n.val, h ⟩ else x
  use g'
  intro n; by_cases h:n.val < N
  . simp [g', dif_pos h, hg]
  convert hx
  . simp [g', dif_neg h]
  have := n.isLt; omega

lemma sec_ex {α β:Type*} [Fintype β] (f : α → β) (h : ∀ b: β, ∃ a : α, f a = b) : ∃ s :β → α, f ∘ s = id := by
  set N := Fintype.card β
  let e : β ≃ Fin N := Fintype.equivFinOfCardEq (show Fintype.card β = N by rfl)
  set F: α → ℕ := fun a ↦ (e (f a)).val
  replace h : ∀ n < N, ∃ x, F x = n := by
    intro n hn
    obtain ⟨ a, ha ⟩ := h (e.symm ⟨ n, hn ⟩)
    use a; simp [F, ha]
  obtain ⟨ g, hg ⟩ := finite_choice h; use g ∘ e
  ext b; specialize hg (e b)
  simpa [F, Fin.val_inj] using hg
