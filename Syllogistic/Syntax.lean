/-!
# Syntax of Aristotelian syllogistic

A categorical proposition links a subject term to a predicate term in one of
four forms (the medieval vowels):

* `A` — universal affirmative: every S is P
* `E` — universal negative:    no S is P
* `I` — particular affirmative: some S is P
* `O` — particular negative:   some S is not P

A syllogism has three terms: the minor term `S` (subject of the conclusion),
the major term `P` (predicate of the conclusion) and the middle term `M`.
The *figure* fixes where the middle term sits in the two premises; the *mood*
is the triple of forms (major premise, minor premise, conclusion).
4 figures × 4³ moods = 256 syllogisms.
-/

namespace Syllogistic

/-- The four forms of categorical proposition. -/
inductive Form where
  | A | E | I | O
  deriving DecidableEq, Repr, Inhabited

/-- The three terms of a syllogism. -/
inductive Term where
  | S | M | P
  deriving DecidableEq, Repr, Inhabited

/-- A categorical proposition: `form subj pred`. -/
structure Cat where
  form : Form
  subj : Term
  pred : Term
  deriving DecidableEq, Repr, Inhabited

/-- The contradictory: A ↔ O, E ↔ I (the diagonals of the square of opposition). -/
def Form.contra : Form → Form
  | .A => .O | .O => .A | .E => .I | .I => .E

def Cat.contra (c : Cat) : Cat := { c with form := c.form.contra }

@[simp] theorem Form.contra_contra (f : Form) : f.contra.contra = f := by
  cases f <;> rfl

@[simp] theorem Cat.contra_contra (c : Cat) : c.contra.contra = c := by
  cases c; simp [Cat.contra]

/-- The four figures. -/
inductive Figure where
  | one | two | three | four
  deriving DecidableEq, Repr, Inhabited

/-- A mood: forms of the major premise, minor premise, conclusion. -/
structure Mood where
  major : Form
  minor : Form
  concl : Form
  deriving DecidableEq, Repr, Inhabited

structure Syllogism where
  mood : Mood
  fig : Figure
  deriving DecidableEq, Repr, Inhabited

namespace Syllogism

open Term in
/-- Major premise. Figure 1 and 3: M–P. Figure 2 and 4: P–M. -/
def major (σ : Syllogism) : Cat :=
  match σ.fig with
  | .one | .three => ⟨σ.mood.major, M, P⟩
  | .two | .four  => ⟨σ.mood.major, P, M⟩

open Term in
/-- Minor premise. Figure 1 and 2: S–M. Figure 3 and 4: M–S. -/
def minor (σ : Syllogism) : Cat :=
  match σ.fig with
  | .one | .two   => ⟨σ.mood.minor, S, M⟩
  | .three | .four => ⟨σ.mood.minor, M, S⟩

/-- Conclusion: always S–P. -/
def concl (σ : Syllogism) : Cat := ⟨σ.mood.concl, .S, .P⟩

end Syllogism

def allForms : List Form := [.A, .E, .I, .O]
def allFigures : List Figure := [.one, .two, .three, .four]

/-- All 256 syllogisms, figure by figure. -/
def allSyllogisms : List Syllogism :=
  allFigures.flatMap fun fig =>
  allForms.flatMap fun a =>
  allForms.flatMap fun b =>
  allForms.map fun c => ⟨⟨a, b, c⟩, fig⟩

theorem allSyllogisms_length : allSyllogisms.length = 256 := by
  set_option maxRecDepth 4000 in decide

/-- Convenient notation: `syl "AAA" 1`. -/
def Form.ofChar : Char → Form
  | 'E' => .E | 'I' => .I | 'O' => .O | _ => .A

def Figure.ofIdx : Nat → Figure
  | 2 => .two | 3 => .three | 4 => .four | _ => .one

def syl (s : String) (n : Nat) : Syllogism :=
  match s.toList with
  | [a, b, c] => ⟨⟨.ofChar a, .ofChar b, .ofChar c⟩, .ofIdx n⟩
  | _ => default

def Form.toChar : Form → Char
  | .A => 'A' | .E => 'E' | .I => 'I' | .O => 'O'

def Figure.toNat : Figure → Nat
  | .one => 1 | .two => 2 | .three => 3 | .four => 4

def Syllogism.code (σ : Syllogism) : String :=
  String.ofList [σ.mood.major.toChar, σ.mood.minor.toChar, σ.mood.concl.toChar]
    ++ "-" ++ toString σ.fig.toNat

end Syllogistic
