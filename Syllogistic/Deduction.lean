import Syllogistic.Classification

/-!
# Aristotle's deductive system

*Prior Analytics* A1–7 gives a proof system, reconstructed by Corcoran (1972)
and Smiley (1973):

* two **perfect** syllogisms, taken as evident: Barbara and Celarent;
* three **conversion** rules:
  - E-conversion  (no S is P ⊢ no P is S)
  - I-conversion  (some S is P ⊢ some P is S)
  - A-conversion *per accidens* (every S is P ⊢ some P is S);
* **reductio**: if assuming the contradictory of `c` lets you derive both
  `d` and the contradictory of `d`, then `c`.

Every other valid mood is "perfected" (reduced) to the first figure using
these rules. The medieval names record how: the first letter names the
Figure-1 mood it reduces to, `s` = simple conversion, `p` = conversion
*per accidens*, `m` = swap the premises, `c` = reductio.

The exercises ask you to prove the system sound and to carry out each
reduction.
-/

namespace Syllogistic

/-- `Γ ⊢ c`: `c` is derivable from hypotheses `Γ` in Aristotle's system. -/
inductive Derives : List Cat → Cat → Prop where
  | hyp {Γ c} : c ∈ Γ → Derives Γ c
  | barbara {Γ s m p} :
      Derives Γ ⟨.A, m, p⟩ → Derives Γ ⟨.A, s, m⟩ → Derives Γ ⟨.A, s, p⟩
  | celarent {Γ s m p} :
      Derives Γ ⟨.E, m, p⟩ → Derives Γ ⟨.A, s, m⟩ → Derives Γ ⟨.E, s, p⟩
  | convE {Γ s p} : Derives Γ ⟨.E, s, p⟩ → Derives Γ ⟨.E, p, s⟩
  | convI {Γ s p} : Derives Γ ⟨.I, s, p⟩ → Derives Γ ⟨.I, p, s⟩
  | convA {Γ s p} : Derives Γ ⟨.A, s, p⟩ → Derives Γ ⟨.I, p, s⟩
  | reductio {Γ c d} :
      Derives (c.contra :: Γ) d → Derives (c.contra :: Γ) d.contra → Derives Γ c

@[inherit_doc] infix:40 " ⊢ " => Derives

/-- A syllogism is provable if its conclusion derives from its premises. -/
def Provable (σ : Syllogism) : Prop := [σ.major, σ.minor] ⊢ σ.concl

/-- Weakening: more hypotheses never hurt. -/
theorem Derives.weaken {Γ Δ : List Cat} {c : Cat} (h : Γ ⊢ c) (hsub : ∀ x ∈ Γ, x ∈ Δ) :
    Δ ⊢ c := by
  induction h generalizing Δ with
  | hyp hc => exact .hyp (hsub _ hc)
  | barbara _ _ ih1 ih2 => exact .barbara (ih1 hsub) (ih2 hsub)
  | celarent _ _ ih1 ih2 => exact .celarent (ih1 hsub) (ih2 hsub)
  | convE _ ih => exact .convE (ih hsub)
  | convI _ ih => exact .convI (ih hsub)
  | convA _ ih => exact .convA (ih hsub)
  | @reductio Γ' c' d' _ _ ih1 ih2 =>
    have hsub' : ∀ x ∈ c'.contra :: Γ', x ∈ c'.contra :: Δ := by
      intro x hx
      cases hx with
      | head => exact .head _
      | tail _ h => exact .tail _ (hsub x h)
    exact .reductio (ih1 hsub') (ih2 hsub')

/-- Use inside a reductio: lift a derivation to a context with one extra
assumption. -/
theorem Derives.lift {Γ : List Cat} {c : Cat} (a : Cat) (h : Γ ⊢ c) : (a :: Γ) ⊢ c :=
  h.weaken fun _ hx => .tail _ hx

/-- The assumption just introduced by a reductio. -/
theorem Derives.assumption {Γ : List Cat} (a : Cat) : (a :: Γ) ⊢ a := .hyp (.head _)

/-- The major premise. -/
theorem Derives.major {a b : Cat} : [a, b] ⊢ a := .hyp (.head _)
/-- The minor premise. -/
theorem Derives.minor {a b : Cat} : [a, b] ⊢ b := .hyp (.tail _ (.head _))

end Syllogistic
