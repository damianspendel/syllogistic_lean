import Solutions.Ex1Semantics

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
  -- SOLUTION
  induction h with
  | hyp hc => exact hΓ _ hc
  | barbara _ _ ih1 ih2 => exact barbara_sem m _ _ _ (ih1 hΓ) (ih2 hΓ)
  | celarent _ _ ih1 ih2 => exact celarent_sem m _ _ _ (ih1 hΓ) (ih2 hΓ)
  | convE _ ih => exact convE_sem m _ _ (ih hΓ)
  | convI _ ih => exact convI_sem m _ _ (ih hΓ)
  | convA _ ih => exact convA_sem m hinh _ _ (ih hΓ)
  | @reductio Γ c d _ _ ih1 ih2 =>
    apply Classical.byContradiction
    intro hnc
    have hΓ' : ∀ g ∈ c.contra :: Γ, m.holds g := by
      intro g hg
      cases hg with
      | head => exact (m.holds_contra c).2 hnc
      | tail _ hg => exact hΓ g hg
    exact (m.holds_contra d).1 (ih2 hΓ') (ih1 hΓ')
  -- END

/-- 2b. Hence every provable syllogism is valid. -/
theorem Provable.valid {σ : Syllogism} (h : Provable σ) : TradValid σ := by
  -- SOLUTION
  intro U m hinh hmaj hmin
  apply h.sound m (hinh rfl)
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact hmaj
  · exact hmin
  -- END

end Syllogistic
