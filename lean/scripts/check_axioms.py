#!/usr/bin/env python3
"""Check the output of the two axiom audits of the Lean project.

Usage:
  python3 -u check_axioms.py named <axioms.log> <Axioms.lean>
      every `#print axioms` line of Axioms.lean has an answer in the log, and no answer names an
      axiom other than propext, Classical.choice, Quot.sound.
  python3 -u check_axioms.py all <axioms_all.log>
      the summary line of AxiomsAll.lean reports no declaration with another axiom, and the axioms
      used anywhere are among the three above.
Exit status 0 on success, 1 on failure.  -h/--help prints this text.
"""
import re
import sys

OK = {"propext", "Classical.choice", "Quot.sound"}


def fail(msg):
    print("FAIL:", msg)
    sys.exit(1)


def named(log, src):
    text = open(log, encoding="utf-8", errors="replace").read()
    asked = len(re.findall(r"^#print axioms ", open(src, encoding="utf-8").read(), re.M))
    answered = len(re.findall(r"depends on axioms:|does not depend on any axioms", text))
    used = set()
    for m in re.finditer(r"depends on axioms: \[([^\]]*)\]", text, re.S):
        used.update(a.strip() for a in m.group(1).split(",") if a.strip())
    print(f"named declarations: asked {asked}, answered {answered}; axioms used: {sorted(used)}")
    if re.search(r":\d+:\d+: error", text):
        fail("the log contains a Lean error")
    if asked == 0 or asked != answered:
        fail("not every #print axioms line was answered")
    if used - OK:
        fail(f"unexpected axioms: {sorted(used - OK)}")


def all_decls(log):
    text = open(log, encoding="utf-8", errors="replace").read()
    m = re.search(r"AXIOMS-ALL: (\d+) declarations.*?\((\d+) theorems.*?axioms used anywhere: \[([^\]]*)\]; "
                  r"declarations with another axiom: (\d+)", text, re.S)
    if not m:
        fail("no AXIOMS-ALL summary line")
    used = {a.strip() for a in m.group(3).split(",") if a.strip()}
    print(f"all declarations: {m.group(1)} ({m.group(2)} theorems); axioms used: {sorted(used)}; "
          f"declarations with another axiom: {m.group(4)}")
    if m.group(4) != "0" or used - OK:
        fail("a declaration uses an axiom outside the standard three")


def main():
    a = sys.argv[1:]
    if not a or a[0] in ("-h", "--help"):
        print(__doc__)
        return
    if a[0] == "named" and len(a) == 3:
        named(a[1], a[2])
    elif a[0] == "all" and len(a) == 2:
        all_decls(a[1])
    else:
        print(__doc__)
        sys.exit(1)
    print("PASS")


if __name__ == "__main__":
    main()
