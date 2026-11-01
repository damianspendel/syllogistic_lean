import Solutions.Ex4Reductions

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
  -- SOLUTION
  intro σ hσ hv
  have h := (trad_classification σ hσ).1 hv
  simp only [traditionalMoods, traditional, List.map, List.mem_cons, List.not_mem_nil,
    or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact barbara_prov
  · exact celarent_prov
  · exact darii_prov
  · exact ferio_prov
  · exact barbari_prov
  · exact celaront_prov
  · exact cesare_prov
  · exact camestres_prov
  · exact festino_prov
  · exact baroco_prov
  · exact cesaro_prov
  · exact camestros_prov
  · exact darapti_prov
  · exact disamis_prov
  · exact datisi_prov
  · exact felapton_prov
  · exact bocardo_prov
  · exact ferison_prov
  · exact bramantip_prov
  · exact camenes_prov
  · exact dimaris_prov
  · exact fesapo_prov
  · exact fresison_prov
  · exact camenos_prov
  -- END

/-- 5b. **Soundness and completeness.** -/
theorem provable_iff_valid : ∀ σ ∈ allSyllogisms, Provable σ ↔ TradValid σ := by
  -- SOLUTION
  intro σ hσ
  exact ⟨Provable.valid, completeness σ hσ⟩
  -- END

end Syllogistic
