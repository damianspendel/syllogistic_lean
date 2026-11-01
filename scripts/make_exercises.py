"""Generate Exercises/ from Solutions/ by replacing each
`-- SOLUTION ... -- END` block with `sorry`."""
import pathlib, re
root = pathlib.Path(__file__).resolve().parent.parent
out = root / "Exercises"; out.mkdir(exist_ok=True)
pat = re.compile(r"^(\s*)-- SOLUTION\n.*?^\s*-- END\n", re.S | re.M)
for f in sorted((root / "Solutions").glob("*.lean")):
    s = pat.sub(lambda m: f"{m.group(1)}sorry\n", f.read_text())
    s = s.replace("import Solutions.", "import Exercises.")
    (out / f.name).write_text(s)
    print("wrote", f.name)
