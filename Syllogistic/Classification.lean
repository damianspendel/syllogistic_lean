import Syllogistic.Venn

/-!
# The classification of all 256 syllogisms

With the Venn metatheorem, validity is decided by kernel computation.
Every result below is checked by Lean's kernel (`decide`), not by a compiled
evaluator, so it rests only on the definitions and the metatheorem.

Results:
* Aristotelian semantics (existential import): exactly the 24 classical moods.
* Modern semantics: exactly 15 of those 24.
-/

namespace Syllogistic

/-- The 24 valid moods with their medieval mnemonic names. -/
def traditional : List (String × Syllogism) :=
  [ ("Barbara", syl "AAA" 1), ("Celarent", syl "EAE" 1), ("Darii", syl "AII" 1),
    ("Ferio", syl "EIO" 1), ("Barbari", syl "AAI" 1), ("Celaront", syl "EAO" 1),
    ("Cesare", syl "EAE" 2), ("Camestres", syl "AEE" 2), ("Festino", syl "EIO" 2),
    ("Baroco", syl "AOO" 2), ("Cesaro", syl "EAO" 2), ("Camestros", syl "AEO" 2),
    ("Darapti", syl "AAI" 3), ("Disamis", syl "IAI" 3), ("Datisi", syl "AII" 3),
    ("Felapton", syl "EAO" 3), ("Bocardo", syl "OAO" 3), ("Ferison", syl "EIO" 3),
    ("Bramantip", syl "AAI" 4), ("Camenes", syl "AEE" 4), ("Dimaris", syl "IAI" 4),
    ("Fesapo", syl "EAO" 4), ("Fresison", syl "EIO" 4), ("Camenos", syl "AEO" 4) ]

/-- The 9 that need existential import. -/
def needsImport : List String :=
  ["Barbari", "Celaront", "Cesaro", "Camestros", "Darapti", "Felapton",
   "Bramantip", "Fesapo", "Camenos"]

def traditionalMoods : List Syllogism := traditional.map (·.2)
def modernMoods : List Syllogism :=
  (traditional.filter fun p => !needsImport.contains p.1).map (·.2)

set_option maxRecDepth 100000 in
/-- **Main theorem (Aristotelian semantics).** A syllogism is valid iff it is
one of the 24 classical moods. -/
theorem trad_classification :
    ∀ σ ∈ allSyllogisms, TradValid σ ↔ σ ∈ traditionalMoods := by
  decide

set_option maxRecDepth 100000 in
/-- **Main theorem (modern semantics).** Exactly the 15 moods without
existential import survive. -/
theorem modern_classification :
    ∀ σ ∈ allSyllogisms, ModernValid σ ↔ σ ∈ modernMoods := by
  decide

theorem traditional_count : traditionalMoods.length = 24 := rfl
theorem modern_count : modernMoods.length = 15 := rfl

/-! Individual results, for reference. -/

theorem barbara : TradValid (syl "AAA" 1) := by decide
theorem barbara_modern : ModernValid (syl "AAA" 1) := by decide
/-- Darapti — "every M is P, every M is S, so some S is P" — fails when M is empty. -/
theorem darapti : TradValid (syl "AAI" 3) := by decide
theorem darapti_not_modern : ¬ ModernValid (syl "AAI" 3) := by decide
/-- Undistributed middle: "every P is M, every S is M, so every S is P". -/
theorem AAA2_invalid : ¬ TradValid (syl "AAA" 2) := by decide

end Syllogistic
