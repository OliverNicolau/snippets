import «Snippets»

-- def main : IO Unit :=
--   IO.println s!"Hello, {hello}!"

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
  fun h : (∀ x, p x) ∨ (∀ x, q x) =>
  fun z =>
  Or.elim h
  (
    fun hl =>
    show p z ∨ q z from Or.intro_left (q z) (hl z)
  )
  (
    fun hr =>
    show p z ∨ q z from Or.intro_right (p z) (hr z)
  )

section
theorem iff_not_self_false {p : Prop} (h : p ↔ ¬ p) : False :=
  let h_and := iff_def.mp h
  let hnp := imp_not_self.mp h_and.left
  let hp := h_and.right hnp
  absurd hp hnp

variable (men : Type) (barber : men)
variable (shaves : men → men → Prop)

example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
  let h_ := h barber
  iff_not_self_false (h_)
end

open Classical

-- variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun h =>
  h.choose_spec

example (a : α) : r → (∃ x : α, r) :=
  fun h =>
  Exists.intro a h

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
  (fun h =>
  let wh := h.choose_spec
  let hr := wh.right
  let wp := Exists.intro h.choose wh.left
  And.intro wp hr)
  (fun h =>
  let hr := h.right
  let wh := h.left.choose
  let wth := h.left.choose_spec
  let w_and_h := And.intro wth hr
  Exists.intro wh w_and_h)

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
  (fun h =>
  let wh := h.choose
  let wth := h.choose_spec
  Or.elim wth
  (fun whl =>
  let hp := Exists.intro wh whl
  Or.intro_left (∃ x, q x) hp)
  (fun whl =>
  let hq := Exists.intro wh whl
  Or.intro_right (∃ x, p x) hq))
  (fun h =>
  Or.elim h
  (fun hp =>
  let w_or_h := Or.intro_left (q hp.choose) hp.choose_spec
  Exists.intro hp.choose w_or_h)
  (fun hq =>
  let w_or_h := Or.intro_right (p hq.choose) hq.choose_spec
  Exists.intro hq.choose w_or_h))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (fun ⟨a, (h1 : p a ∨ q a)⟩ =>
      Or.elim h1
        (fun hpa : p a => Or.inl ⟨a, hpa⟩)
        (fun hqa : q a => Or.inr ⟨a, hqa⟩))
    (fun h : (∃ x, p x) ∨ (∃ x, q x) =>
      Or.elim h
        (fun ⟨a, hpa⟩ => ⟨a, (Or.inl hpa)⟩)
        (fun ⟨a, hqa⟩ => ⟨a, (Or.inr hqa)⟩))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  apply Iff.intro
  intro
  | ⟨w, Or.inl h⟩ => exact Or.inl ⟨w, h⟩
  | ⟨w, Or.inr h⟩ => exact Or.inr ⟨w, h⟩
  intro
  | Or.inl ⟨w,  h⟩ => exact ⟨w, Or.inl h⟩
  | Or.inr ⟨w,  h⟩ => exact ⟨w, Or.inr h⟩
