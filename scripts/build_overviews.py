#!/usr/bin/env python3
"""Compile the proof overview documents  GsimOT/<Folder>/*_overview.tex  and  ThinMatching/*_overview.tex.

The overviews are written by hand (unlike the correspondence tables, which
scripts/gen_correspondence.py generates). They share scripts/overview_preamble.tex.
Run from the repository root:

    python3 scripts/build_overviews.py                 # all overviews
    python3 scripts/build_overviews.py Theorem6_EditUpperBound   # only these folders
"""

import glob
import os
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def main():
    only = set(a.rstrip("/").split("/")[-1] for a in sys.argv[1:])
    if shutil.which("pdflatex") is None:
        sys.exit("error: pdflatex not found")
    paths = sorted(glob.glob(os.path.join(ROOT, "GsimOT", "*", "*_overview.tex")) +
                   glob.glob(os.path.join(ROOT, "ThinMatching", "*_overview.tex")))
    failed = []
    for path in paths:
        folder, name = os.path.split(path)
        if only and os.path.basename(folder) not in only:
            continue
        stem = name[:-4]
        ok = True
        for _ in range(2):  # twice, for references
            res = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", name],
                                 cwd=folder, capture_output=True, text=True, errors="replace")
            if res.returncode != 0:
                print(res.stdout[-3000:])
                ok = False
                break
        for ext in (".aux", ".log", ".out", ".toc"):
            p = os.path.join(folder, stem + ext)
            if os.path.exists(p):
                os.remove(p)
        rel = os.path.relpath(os.path.join(folder, stem + ".pdf"), ROOT)
        print(("wrote " if ok else "FAILED ") + rel)
        if not ok:
            failed.append(rel)
    if failed:
        sys.exit("error: pdflatex failed on " + ", ".join(failed))


if __name__ == "__main__":
    main()
