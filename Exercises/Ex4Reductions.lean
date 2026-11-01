import Exercises.Ex3FirstFigure

/-!
# Exercise 4 — Reducing figures 2, 3 and 4 to the first

Read each name as instructions. The first letter is the Figure-1 mood you
reduce to (B → Barbara, C → Celarent, D → Darii, F → Ferio).
After a vowel:
* `s` — convert that proposition simply (`convE`, `convI`)
* `p` — convert it *per accidens* (`convA`, or `subA`/`subE` on a conclusion)
* `m` — swap the premises (*mutatio*)
* `c` — prove by reductio (*per contradictionem*)

Example: **Cesare** (E-A-E, figure 2). `C`: reduce to Celarent; the `s`
after the first `e`: convert the major premise `E P M` to `E M P`. Then
Celarent applies.

Figure 2: major `P–M`, minor `S–M`. Figure 3: major `M–P`, minor `M–S`.
Figure 4: major `P–M`, minor `M–S`.
-/

namespace Syllogistic

/-! ## Figure 2 -/

theorem cesare_prov : Provable (syl "EAE" 2) := by
  show [⟨.E, .P, .M⟩, ⟨.A, .S, .M⟩] ⊢ ⟨.E, .S, .P⟩
  sorry

theorem camestres_prov : Provable (syl "AEE" 2) := by
  show [⟨.A, .P, .M⟩, ⟨.E, .S, .M⟩] ⊢ ⟨.E, .S, .P⟩
  sorry

theorem festino_prov : Provable (syl "EIO" 2) := by
  show [⟨.E, .P, .M⟩, ⟨.I, .S, .M⟩] ⊢ ⟨.O, .S, .P⟩
  sorry

/-- Baroco: the `c` means reductio. Assume `A S P`; Barbara then gives
`A S M`, against the minor premise. -/
theorem baroco_prov : Provable (syl "AOO" 2) := by
  show [⟨.A, .P, .M⟩, ⟨.O, .S, .M⟩] ⊢ ⟨.O, .S, .P⟩
  sorry

theorem cesaro_prov : Provable (syl "EAO" 2) := by
  show [⟨.E, .P, .M⟩, ⟨.A, .S, .M⟩] ⊢ ⟨.O, .S, .P⟩
  sorry

theorem camestros_prov : Provable (syl "AEO" 2) := by
  show [⟨.A, .P, .M⟩, ⟨.E, .S, .M⟩] ⊢ ⟨.O, .S, .P⟩
  sorry

/-! ## Figure 3 -/

theorem darapti_prov : Provable (syl "AAI" 3) := by
  show [⟨.A, .M, .P⟩, ⟨.A, .M, .S⟩] ⊢ ⟨.I, .S, .P⟩
  sorry

theorem disamis_prov : Provable (syl "IAI" 3) := by
  show [⟨.I, .M, .P⟩, ⟨.A, .M, .S⟩] ⊢ ⟨.I, .S, .P⟩
  sorry

theorem datisi_prov : Provable (syl "AII" 3) := by
  show [⟨.A, .M, .P⟩, ⟨.I, .M, .S⟩] ⊢ ⟨.I, .S, .P⟩
  sorry

theorem felapton_prov : Provable (syl "EAO" 3) := by
  show [⟨.E, .M, .P⟩, ⟨.A, .M, .S⟩] ⊢ ⟨.O, .S, .P⟩
  sorry

theorem bocardo_prov : Provable (syl "OAO" 3) := by
  show [⟨.O, .M, .P⟩, ⟨.A, .M, .S⟩] ⊢ ⟨.O, .S, .P⟩
  sorry

theorem ferison_prov : Provable (syl "EIO" 3) := by
  show [⟨.E, .M, .P⟩, ⟨.I, .M, .S⟩] ⊢ ⟨.O, .S, .P⟩
  sorry

/-! ## Figure 4 (not in Aristotle; added by later logicians) -/

theorem bramantip_prov : Provable (syl "AAI" 4) := by
  show [⟨.A, .P, .M⟩, ⟨.A, .M, .S⟩] ⊢ ⟨.I, .S, .P⟩
  sorry

theorem camenes_prov : Provable (syl "AEE" 4) := by
  show [⟨.A, .P, .M⟩, ⟨.E, .M, .S⟩] ⊢ ⟨.E, .S, .P⟩
  sorry

theorem dimaris_prov : Provable (syl "IAI" 4) := by
  show [⟨.I, .P, .M⟩, ⟨.A, .M, .S⟩] ⊢ ⟨.I, .S, .P⟩
  sorry

theorem fesapo_prov : Provable (syl "EAO" 4) := by
  show [⟨.E, .P, .M⟩, ⟨.A, .M, .S⟩] ⊢ ⟨.O, .S, .P⟩
  sorry

theorem fresison_prov : Provable (syl "EIO" 4) := by
  show [⟨.E, .P, .M⟩, ⟨.I, .M, .S⟩] ⊢ ⟨.O, .S, .P⟩
  sorry

theorem camenos_prov : Provable (syl "AEO" 4) := by
  show [⟨.A, .P, .M⟩, ⟨.E, .M, .S⟩] ⊢ ⟨.O, .S, .P⟩
  sorry

end Syllogistic
