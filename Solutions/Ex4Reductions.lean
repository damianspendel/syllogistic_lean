import Solutions.Ex3FirstFigure

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
  -- SOLUTION
  exact .celarent (.convE .major) .minor
  -- END

theorem camestres_prov : Provable (syl "AEE" 2) := by
  show [⟨.A, .P, .M⟩, ⟨.E, .S, .M⟩] ⊢ ⟨.E, .S, .P⟩
  -- SOLUTION
  exact .convE (.celarent (.convE .minor) .major)
  -- END

theorem festino_prov : Provable (syl "EIO" 2) := by
  show [⟨.E, .P, .M⟩, ⟨.I, .S, .M⟩] ⊢ ⟨.O, .S, .P⟩
  -- SOLUTION
  exact .ferio (.convE .major) .minor
  -- END

/-- Baroco: the `c` means reductio. Assume `A S P`; Barbara then gives
`A S M`, against the minor premise. -/
theorem baroco_prov : Provable (syl "AOO" 2) := by
  show [⟨.A, .P, .M⟩, ⟨.O, .S, .M⟩] ⊢ ⟨.O, .S, .P⟩
  -- SOLUTION
  apply Derives.reductio (d := ⟨.O, .S, .M⟩)
  · exact Derives.minor.lift _
  · exact .barbara (Derives.major.lift _) (.assumption _)
  -- END

theorem cesaro_prov : Provable (syl "EAO" 2) := by
  show [⟨.E, .P, .M⟩, ⟨.A, .S, .M⟩] ⊢ ⟨.O, .S, .P⟩
  -- SOLUTION
  exact (Derives.celarent (.convE .major) .minor).subE
  -- END

theorem camestros_prov : Provable (syl "AEO" 2) := by
  show [⟨.A, .P, .M⟩, ⟨.E, .S, .M⟩] ⊢ ⟨.O, .S, .P⟩
  -- SOLUTION
  exact (Derives.convE (.celarent (.convE .minor) .major)).subE
  -- END

/-! ## Figure 3 -/

theorem darapti_prov : Provable (syl "AAI" 3) := by
  show [⟨.A, .M, .P⟩, ⟨.A, .M, .S⟩] ⊢ ⟨.I, .S, .P⟩
  -- SOLUTION
  exact .darii .major (.convA .minor)
  -- END

theorem disamis_prov : Provable (syl "IAI" 3) := by
  show [⟨.I, .M, .P⟩, ⟨.A, .M, .S⟩] ⊢ ⟨.I, .S, .P⟩
  -- SOLUTION
  exact .convI (.darii .minor (.convI .major))
  -- END

theorem datisi_prov : Provable (syl "AII" 3) := by
  show [⟨.A, .M, .P⟩, ⟨.I, .M, .S⟩] ⊢ ⟨.I, .S, .P⟩
  -- SOLUTION
  exact .darii .major (.convI .minor)
  -- END

theorem felapton_prov : Provable (syl "EAO" 3) := by
  show [⟨.E, .M, .P⟩, ⟨.A, .M, .S⟩] ⊢ ⟨.O, .S, .P⟩
  -- SOLUTION
  exact .ferio .major (.convA .minor)
  -- END

theorem bocardo_prov : Provable (syl "OAO" 3) := by
  show [⟨.O, .M, .P⟩, ⟨.A, .M, .S⟩] ⊢ ⟨.O, .S, .P⟩
  -- SOLUTION
  apply Derives.reductio (d := ⟨.O, .M, .P⟩)
  · exact Derives.major.lift _
  · exact .barbara (.assumption _) (Derives.minor.lift _)
  -- END

theorem ferison_prov : Provable (syl "EIO" 3) := by
  show [⟨.E, .M, .P⟩, ⟨.I, .M, .S⟩] ⊢ ⟨.O, .S, .P⟩
  -- SOLUTION
  exact .ferio .major (.convI .minor)
  -- END

/-! ## Figure 4 (not in Aristotle; added by later logicians) -/

theorem bramantip_prov : Provable (syl "AAI" 4) := by
  show [⟨.A, .P, .M⟩, ⟨.A, .M, .S⟩] ⊢ ⟨.I, .S, .P⟩
  -- SOLUTION
  exact .convA (.barbara .minor .major)
  -- END

theorem camenes_prov : Provable (syl "AEE" 4) := by
  show [⟨.A, .P, .M⟩, ⟨.E, .M, .S⟩] ⊢ ⟨.E, .S, .P⟩
  -- SOLUTION
  exact .convE (.celarent .minor .major)
  -- END

theorem dimaris_prov : Provable (syl "IAI" 4) := by
  show [⟨.I, .P, .M⟩, ⟨.A, .M, .S⟩] ⊢ ⟨.I, .S, .P⟩
  -- SOLUTION
  exact .convI (.darii .minor .major)
  -- END

theorem fesapo_prov : Provable (syl "EAO" 4) := by
  show [⟨.E, .P, .M⟩, ⟨.A, .M, .S⟩] ⊢ ⟨.O, .S, .P⟩
  -- SOLUTION
  exact .ferio (.convE .major) (.convA .minor)
  -- END

theorem fresison_prov : Provable (syl "EIO" 4) := by
  show [⟨.E, .P, .M⟩, ⟨.I, .M, .S⟩] ⊢ ⟨.O, .S, .P⟩
  -- SOLUTION
  exact .ferio (.convE .major) (.convI .minor)
  -- END

theorem camenos_prov : Provable (syl "AEO" 4) := by
  show [⟨.A, .P, .M⟩, ⟨.E, .M, .S⟩] ⊢ ⟨.O, .S, .P⟩
  -- SOLUTION
  exact (Derives.convE (.celarent .minor .major)).subE
  -- END

end Syllogistic
