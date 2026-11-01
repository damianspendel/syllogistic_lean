"""Inline site/data.json into site/template.html -> site/index.html.
Usage: python3 scripts/build_site.py [repo-url]"""
import json, pathlib, sys
root = pathlib.Path(__file__).resolve().parent.parent / "site"
data = json.dumps(json.loads((root / "data.json").read_text()), separators=(",", ":"))
html = (root / "template.html").read_text().replace("/*DATA*/[]", data)
if len(sys.argv) > 1:
    html = html.replace('"/*REPO*/"', json.dumps(sys.argv[1]))
(root / "index.html").write_text(html)
print("wrote site/index.html", len(html), "bytes")
