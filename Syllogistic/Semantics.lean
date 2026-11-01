import Syllogistic.Syntax

/-!
# Set-theoretic semantics

A model interprets each term as a subset (predicate) of some domain `U`.

Aristotle's logic assumes *existential import*: every term is non-empty.
Under that assumption "every S is P" entails "some S is P", which is what
makes the 9 "weakened"/"strengthened" moods (Darapti, Felapton, Barbari, ...)
valid. Modern (Boolean) semantics drops the assumption and keeps only 15.
We define both and let the flag `ei : Bool` choose.
-/

namespace Syllogistic

structure Model (U : Type) where
  ext : Term → U → Prop

namespace Model
variable {U : Type} (m : Model U)

/-- Truth of a categorical proposition in a model. -/
def holds : Cat → Prop
  | ⟨.A, s, p⟩ => ∀ x, m.ext s x → m.ext p x
  | ⟨.E, s, p⟩ => ∀ x, m.ext s x → ¬ m.ext p x
  | ⟨.I, s, p⟩ => ∃ x, m.ext s x ∧ m.ext p x
  | ⟨.O, s, p⟩ => ∃ x, m.ext s x ∧ ¬ m.ext p x

/-- Existential import: all three terms are non-empty. -/
def Inhabited : Prop := ∀ t, ∃ x, m.ext t x

/-- A proposition and its contradictory always have opposite truth values. -/
theorem holds_contra (c : Cat) : m.holds c.contra ↔ ¬ m.holds c := by
  obtain ⟨f, s, p⟩ := c
  cases f <;> simp only [Cat.contra, Form.contra, holds] <;>
    first
    | (constructor
       · rintro ⟨x, hs, hp⟩ h; exact hp (h x hs)
       · intro h; exact Classical.byContradiction fun hn =>
           h fun x hs => Classical.byContradiction fun hp => hn ⟨x, hs, hp⟩)
    | (constructor
       · rintro ⟨x, hs, hp⟩ h; exact h x hs hp
       · intro h; exact Classical.byContradiction fun hn =>
           h fun x hs hp => hn ⟨x, hs, hp⟩)
    | (constructor
       · intro h ⟨x, hs, hp⟩; exact h x hs hp
       · intro h x hs hp; exact h ⟨x, hs, hp⟩)
    | (constructor
       · intro h ⟨x, hs, hp⟩; exact hp (h x hs)
       · intro h x hs; exact Classical.byContradiction fun hp => h ⟨x, hs, hp⟩)

end Model

/-- `Valid ei σ`: in every model (inhabited, if `ei`), true premises force a
true conclusion. `ei = true` is Aristotle's semantics, `false` the modern one. -/
def Valid (ei : Bool) (σ : Syllogism) : Prop :=
  ∀ (U : Type) (m : Model U), (ei = true → m.Inhabited) →
    m.holds σ.major → m.holds σ.minor → m.holds σ.concl

/-- Traditional (Aristotelian) validity. -/
abbrev TradValid := Valid true
/-- Modern (Boolean) validity. -/
abbrev ModernValid := Valid false

theorem Valid.of_modern {σ : Syllogism} (h : ModernValid σ) : TradValid σ :=
  fun U m _ => h U m (by intro h; cases h)

end Syllogistic
