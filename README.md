# Syllogistic

Aristotle's syllogistic formalised in Lean 4, with no Mathlib dependency.

- **Semantics.** Terms are interpreted as subsets of any domain, under either Aristotle's semantics (every term non-empty) or modern Boolean semantics.
- **Decision procedure.** A metatheorem shows that validity over all models equals validity over the 256 Venn-diagram models. Validity is therefore decidable, and the kernel checks it.
- **Classification.** Of the 256 syllogisms, exactly 24 are valid under Aristotle's semantics and 15 under modern semantics. Both results are kernel-checked (`trad_classification`, `modern_classification`).
- **Proof theory.** Aristotle's deductive system: Barbara and Celarent, three conversions, and reductio.
- **Exercises.** 39 exercises take you from semantics by hand to soundness and completeness of Aristotle's system.
- **Explorer.** An interactive page shows every mood, its Venn diagram and a counter-model (`site/index.html`).

## Layout

```
Syllogistic/            the library (complete, no sorry)
  Syntax.lean           forms A E I O, terms, figures, 256 syllogisms
  Semantics.lean        models, existential import, Valid
  Venn.lean             256 Venn models; valid_iff_vennValid; Decidable instance
  Classification.lean   the 24 / 15 theorems, kernel-checked
  Deduction.lean        Aristotle's system: Derives, weakening, helpers
Exercises/              your work: each `sorry` is one exercise
  Ex1Semantics.lean     prove Barbara, the conversions, and countermodels by hand
  Ex2Soundness.lean     the system is sound (induction on derivations)
  Ex3FirstFigure.lean   derive Darii and Ferio by reductio; subalternation
  Ex4Reductions.lean    reduce figures 2–4 to figure 1, guided by the medieval names
  Ex5Completeness.lean  provable ⇔ valid
Solutions/              reference solutions (do not open until you have tried)
Export.lean             dumps all 256 verdicts and counter-models as JSON for the site
site/                   template.html + data.json → index.html
scripts/
  make_exercises.py     regenerates Exercises/ from Solutions/
  build_site.py         rebuilds site/index.html
  progress.sh           counts your remaining sorries
```

## Setup

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
cd syllogistic
lake build            # library, including kernel-checked classification (~15 s)
```

Editor: VS Code with the `lean4` extension. Open the folder; `lean-toolchain` pins Lean 4.35.0.

## Working the exercises

1. Open `Exercises/Ex1Semantics.lean`. Replace a `sorry` with a proof; the infoview shows the goal.
2. `./scripts/progress.sh` lists the sorries left in each file.
3. Do the exercises in order. Later files use earlier results as lemmas, so if you skip one, the rest still compile.
4. When you are stuck, the docstrings give hints. The full answers are in `Solutions/`.

Learning path:

| Ex | Teaches (Lean) | Teaches (logic) |
|----|----------------|-----------------|
| 1 | `intro`, `exact`, `obtain`, anonymous constructors, building a model | what A/E/I/O mean in sets; why per-accidens conversion needs import |
| 2 | `induction` on an inductive predicate, classical reasoning | soundness |
| 3 | `apply ... (d := ...)`, working inside a reductio context | Aristotle's own reduction of Darii and Ferio (*Pr. An.* A7) |
| 4 | term-mode proofs, dot notation | the medieval mnemonics as proof recipes |
| 5 | `simp only ... at`, `rcases` with many cases | completeness (Corcoran 1972, Smiley 1973) |

Stretch goals (no solutions supplied):

- Prove `¬ Provable (syl "AAA" 2)` without `decide`, using soundness and your countermodel from 1g.
- Square of opposition: state and prove contraries, subcontraries and subalterns semantically.
- Prove the medieval rules (distributed middle, quality, quantity) and show that they characterise validity.

## Rebuilding the site

```bash
lake exe export > site/data.json
python3 scripts/build_site.py https://github.com/damianspendel/syllogistic_lean
```

## References

- J. Łukasiewicz, *Aristotle's Syllogistic from the Standpoint of Modern Formal Logic*, 1951.
- J. Corcoran, "Completeness of an ancient logic", *Journal of Symbolic Logic* 37, 1972.
- T. Smiley, "What is a syllogism?", *Journal of Philosophical Logic* 2, 1973.
