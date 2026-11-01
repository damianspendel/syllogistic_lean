import Solutions.Ex2Soundness

/-!
# Exercise 3 — Completing the first figure

Aristotle takes only Barbara and Celarent as primitive. In *Prior Analytics*
A7 he notes that Darii and Ferio can themselves be reduced to them by
reductio. Do that here, as *derived rules* usable in any context `Γ`.

Toolkit (see `Syllogistic/Deduction.lean`):
* `Derives.reductio (d := ...)` — choose the pair `d`, `d.contra` to clash
* `h.lift _` — reuse an outside derivation inside a reductio
* `Derives.assumption _` — the reductio assumption itself
* `Derives.major`, `Derives.minor` — the premises of a syllogism

The contradictory of `⟨.I, s, p⟩` is `⟨.E, s, p⟩`, of `⟨.O, s, p⟩` is
`⟨.A, s, p⟩`. Lean sees through `Cat.contra` by computation, so `show`
can make goals readable.
-/

namespace Syllogistic

variable {Γ : List Cat} {s m p : Term}

/-- 3a. Darii as a derived rule. Hint: assume `E s p`, and use Celarent to
reach `E s m`, contradicting `I s m`. -/
theorem Derives.darii (h1 : Γ ⊢ ⟨.A, m, p⟩) (h2 : Γ ⊢ ⟨.I, s, m⟩) : Γ ⊢ ⟨.I, s, p⟩ := by
  -- SOLUTION
  apply Derives.reductio (d := ⟨.I, s, m⟩)
  · exact h2.lift _
  · show (⟨.E, s, p⟩ :: Γ) ⊢ ⟨.E, s, m⟩
    exact .convE (.celarent (.convE (.assumption _)) (h1.lift _))
  -- END

/-- 3b. Ferio as a derived rule. -/
theorem Derives.ferio (h1 : Γ ⊢ ⟨.E, m, p⟩) (h2 : Γ ⊢ ⟨.I, s, m⟩) : Γ ⊢ ⟨.O, s, p⟩ := by
  -- SOLUTION
  apply Derives.reductio (d := ⟨.I, s, m⟩)
  · exact h2.lift _
  · show (⟨.A, s, p⟩ :: Γ) ⊢ ⟨.E, s, m⟩
    exact .celarent (.convE (h1.lift _)) (.assumption _)
  -- END

/-- 3c. Subalternation A ⊢ I (only two conversions needed). -/
theorem Derives.subA (h : Γ ⊢ ⟨.A, s, p⟩) : Γ ⊢ ⟨.I, s, p⟩ := by
  -- SOLUTION
  exact .convI (.convA h)
  -- END

/-- 3d. Subalternation E ⊢ O. Hint: reductio. -/
theorem Derives.subE (h : Γ ⊢ ⟨.E, s, p⟩) : Γ ⊢ ⟨.O, s, p⟩ := by
  -- SOLUTION
  apply Derives.reductio (d := ⟨.I, s, p⟩)
  · exact (Derives.assumption _).subA
  · exact h.lift _
  -- END

/-! Now the six first-figure moods. `show` the concrete goal first. -/

/-- 3e. -/
theorem barbara_prov : Provable (syl "AAA" 1) := by
  show [⟨.A, .M, .P⟩, ⟨.A, .S, .M⟩] ⊢ ⟨.A, .S, .P⟩
  -- SOLUTION
  exact .barbara .major .minor
  -- END

/-- 3f. -/
theorem celarent_prov : Provable (syl "EAE" 1) := by
  show [⟨.E, .M, .P⟩, ⟨.A, .S, .M⟩] ⊢ ⟨.E, .S, .P⟩
  -- SOLUTION
  exact .celarent .major .minor
  -- END

/-- 3g. -/
theorem darii_prov : Provable (syl "AII" 1) := by
  show [⟨.A, .M, .P⟩, ⟨.I, .S, .M⟩] ⊢ ⟨.I, .S, .P⟩
  -- SOLUTION
  exact .darii .major .minor
  -- END

/-- 3h. -/
theorem ferio_prov : Provable (syl "EIO" 1) := by
  show [⟨.E, .M, .P⟩, ⟨.I, .S, .M⟩] ⊢ ⟨.O, .S, .P⟩
  -- SOLUTION
  exact .ferio .major .minor
  -- END

/-- 3i. Barbari — needs import (why? which rule carries it?). -/
theorem barbari_prov : Provable (syl "AAI" 1) := by
  show [⟨.A, .M, .P⟩, ⟨.A, .S, .M⟩] ⊢ ⟨.I, .S, .P⟩
  -- SOLUTION
  exact (Derives.barbara .major .minor).subA
  -- END

/-- 3j. Celaront. -/
theorem celaront_prov : Provable (syl "EAO" 1) := by
  show [⟨.E, .M, .P⟩, ⟨.A, .S, .M⟩] ⊢ ⟨.O, .S, .P⟩
  -- SOLUTION
  exact (Derives.celarent .major .minor).subE
  -- END

end Syllogistic
