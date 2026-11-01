import Exercises.Ex1Semantics

/-!
# Exercise 2 — Soundness of Aristotle's system

Show that anything derivable is semantically valid in every inhabited model.
Proceed by induction on the derivation. For the reductio case you will need
`Model.holds_contra : m.holds c.contra ↔ ¬ m.holds c` and classical logic
(`Classical.byContradiction`).

Your lemmas from Exercise 1 do most of the work.
-/

namespace Syllogistic

/-- 2a. Soundness. -/
theorem Derives.sound {Γ : List Cat} {c : Cat} (h : Γ ⊢ c)
    {U : Type} (m : Model U) (hinh : m.Inhabited) (hΓ : ∀ g ∈ Γ, m.holds g) :
    m.holds c := by
  sorry

/-- 2b. Hence every provable syllogism is valid. -/
theorem Provable.valid {σ : Syllogism} (h : Provable σ) : TradValid σ := by
  sorry

end Syllogistic
