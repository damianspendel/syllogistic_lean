import Exercises.Ex4Reductions

/-!
# Exercise 5 — Completeness

Put everything together: for syllogisms, Aristotle's proof system proves
exactly the semantically valid ones (Corcoran 1972; Smiley 1973).

Soundness is Exercise 2. For completeness, `trad_classification` (proved in
`Syllogistic/Classification.lean`) tells you the valid syllogisms are exactly
the 24 in `traditionalMoods`. Case-split on membership and use Exercises 3–4.

Tactics: `simp only [traditionalMoods, traditional, List.map, List.mem_cons,
List.not_mem_nil, or_false] at h` turns membership into a 24-way disjunction;
`rcases h with rfl | rfl | ...` splits it; then one `· exact _` per case.
-/

namespace Syllogistic

/-- 5a. Completeness for syllogisms. -/
theorem completeness : ∀ σ ∈ allSyllogisms, TradValid σ → Provable σ := by
  sorry

/-- 5b. **Soundness and completeness.** -/
theorem provable_iff_valid : ∀ σ ∈ allSyllogisms, Provable σ ↔ TradValid σ := by
  sorry

end Syllogistic
