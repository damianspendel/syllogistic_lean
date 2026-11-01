import Syllogistic

/-!
Dump all 256 syllogisms as JSON for the website, using the *same*
`Venn.counter` the metatheorem is about. For each invalid syllogism we emit
a smallest counter-model (fewest inhabited regions).
Region bit index = 4·[in S] + 2·[in M] + [in P].
-/

open Syllogistic

def regionIdx (r : Region) : Nat :=
  (if r.1 then 4 else 0) + (if r.2.1 then 2 else 0) + (if r.2.2 then 1 else 0)

def vennOfMask (n : Nat) : Venn := fun r => n.testBit (regionIdx r)

def popcount (n : Nat) : Nat := (List.range 8).countP (n.testBit ·)

def masksBySize : List Nat :=
  (List.range 9).flatMap fun k => (List.range 256).filter (popcount · == k)

def counterMask (ei : Bool) (σ : Syllogism) : Option Nat :=
  masksBySize.find? fun n => (vennOfMask n).counter ei σ

def nameOf (σ : Syllogism) : Option String :=
  (traditional.find? (·.2 == σ)).map (·.1)

def jsonOpt : Option Nat → String
  | some n => toString n
  | none => "null"

def catJson (c : Cat) : String :=
  s!"\{\"f\":\"{c.form.toChar}\",\"s\":\"{repr c.subj}\",\"p\":\"{repr c.pred}\"}"
    |>.replace "Syllogistic.Term." ""

def entry (σ : Syllogism) : String :=
  let name := match nameOf σ with | some n => s!"\"{n}\"" | none => "null"
  s!"\{\"code\":\"{σ.code}\",\"fig\":{σ.fig.toNat},\"name\":{name}," ++
  s!"\"trad\":{vennValid true σ},\"modern\":{vennValid false σ}," ++
  s!"\"cmTrad\":{jsonOpt (counterMask true σ)},\"cmModern\":{jsonOpt (counterMask false σ)}," ++
  s!"\"major\":{catJson σ.major},\"minor\":{catJson σ.minor},\"concl\":{catJson σ.concl}}"

def main : IO Unit := do
  IO.println ("[" ++ ",\n".intercalate (allSyllogisms.map entry) ++ "]")
