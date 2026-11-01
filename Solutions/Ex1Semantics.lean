import Syllogistic.Deduction

/-!
# Exercise 1 — Semantics by hand

`decide` can settle any syllogism via the Venn metatheorem. Here you prove
things directly from the definition of `Model.holds`, to see what the
semantics actually says.

Useful tactics: `intro`, `exact`, `obtain ⟨x, hx⟩ := h`, `⟨x, h1, h2⟩`
(anonymous constructor), `simp only [Model.holds]` to unfold.
-/

namespace Syllogistic
open Term

variable {U : Type} (m : Model U)

/-- 1a. Barbara, directly: every M is P, every S is M ⊢ every S is P. -/
theorem barbara_sem (s mid p : Term)
    (h1 : m.holds ⟨.A, mid, p⟩) (h2 : m.holds ⟨.A, s, mid⟩) : m.holds ⟨.A, s, p⟩ := by
  -- SOLUTION
  intro x hx
  exact h1 x (h2 x hx)
  -- END

/-- 1b. Celarent: no M is P, every S is M ⊢ no S is P. -/
theorem celarent_sem (s mid p : Term)
    (h1 : m.holds ⟨.E, mid, p⟩) (h2 : m.holds ⟨.A, s, mid⟩) : m.holds ⟨.E, s, p⟩ := by
  -- SOLUTION
  intro x hx
  exact h1 x (h2 x hx)
  -- END

/-- 1c. E-conversion. -/
theorem convE_sem (s p : Term) (h : m.holds ⟨.E, s, p⟩) : m.holds ⟨.E, p, s⟩ := by
  -- SOLUTION
  intro x hp hs
  exact h x hs hp
  -- END

/-- 1d. I-conversion. -/
theorem convI_sem (s p : Term) (h : m.holds ⟨.I, s, p⟩) : m.holds ⟨.I, p, s⟩ := by
  -- SOLUTION
  obtain ⟨x, hs, hp⟩ := h
  exact ⟨x, hp, hs⟩
  -- END

/-- 1e. A-conversion *per accidens* — needs existential import. -/
theorem convA_sem (hinh : m.Inhabited) (s p : Term) (h : m.holds ⟨.A, s, p⟩) :
    m.holds ⟨.I, p, s⟩ := by
  -- SOLUTION
  obtain ⟨x, hx⟩ := hinh s
  exact ⟨x, h x hx, hx⟩
  -- END

/-- 1f. ...and it really does need it. Build a model where "every S is P" is
true but "some P is S" is false. Hint: make every term empty. -/
theorem convA_fails_without_import :
    ∃ (U : Type) (m : Model U), m.holds ⟨.A, S, P⟩ ∧ ¬ m.holds ⟨.I, P, S⟩ := by
  -- SOLUTION
  refine ⟨Unit, ⟨fun _ _ => False⟩, ?_, ?_⟩
  · intro _ h; exact h
  · rintro ⟨_, h, _⟩; exact h
  -- END

/-- 1g. Undistributed middle. Every P is M and every S is M, yet not every
S is P. Give an explicit countermodel (try `U := Bool`). -/
theorem undistributed_middle :
    ∃ (U : Type) (m : Model U), m.Inhabited ∧
      m.holds ⟨.A, P, M⟩ ∧ m.holds ⟨.A, S, M⟩ ∧ ¬ m.holds ⟨.A, S, P⟩ := by
  -- SOLUTION
  -- S = {false}, P = {true}, M = everything
  let m : Model Bool := ⟨fun t x => match t with
    | .S => x = false | .P => x = true | .M => True⟩
  refine ⟨Bool, m, ?_, ?_, ?_, ?_⟩
  · intro t; cases t
    · exact ⟨false, rfl⟩
    · exact ⟨true, trivial⟩
    · exact ⟨true, rfl⟩
  · intro _ _; trivial
  · intro _ _; trivial
  · intro h
    have : (false = true) := h false rfl
    cases this
  -- END

end Syllogistic
