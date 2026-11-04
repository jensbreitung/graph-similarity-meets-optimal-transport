#!/usr/bin/env python3
"""Generate the paper <-> Lean correspondence documents (LaTeX + PDF).

For every formalised result folder this script writes `<Folder>/<Name>_correspondence.tex`
and, if `pdflatex` is available, compiles it to `<Folder>/<Name>_correspondence.pdf`.

The tables are generated from the data below; file names and line numbers of the Lean
declarations are looked up in the sources at generation time, so the documents always match the
code.  Run from the repository root:

    python3 scripts/gen_correspondence.py            # all documents
    python3 scripts/gen_correspondence.py Theorem6_EditUpperBound Common   # only these folders
"""

import os
import re
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "GsimOT")

PAPER = (r"J.~Breitung, T.~Gervens, M.~Grohe. \emph{Graph Similarity Meets Optimal Transport} (file "
         r"\texttt{Graph\_Similarity\_Meets\_Optimal\_Transport.pdf} in the repository). Statement, equation, page and "
         r"line numbers refer to this PDF; \texttt{docs/NUMBERING.md} lists the Lean files and declarations of all "
         r"numbered statements.")

# Folders given on the command line; if empty, all documents are generated.
ONLY = set(a.rstrip("/").split("/")[-1] for a in sys.argv[1:])

# ---------------------------------------------------------------------------------------------
# Locating Lean declarations
# ---------------------------------------------------------------------------------------------

DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:private\s+)?(?:noncomputable\s+)?(?:protected\s+)?"
    r"(theorem|lemma|def|abbrev|structure|inductive|instance|class)\s+([^\s(:{\[]+)")


def index_decls():
    """Map short and namespaced declaration names to (relative file, line)."""
    table = {}
    for dirpath, _, files in [w for root in (SRC, os.path.join(ROOT, "ThinMatching")) for w in os.walk(root)]:
        for fn in sorted(files):
            if not fn.endswith(".lean"):
                continue
            path = os.path.join(dirpath, fn)
            rel = os.path.relpath(path, ROOT)
            ns = []
            with open(path, encoding="utf-8") as fh:
                for lineno, line in enumerate(fh, 1):
                    s = line.strip()
                    if s.startswith("namespace "):
                        ns.append(s.split()[1])
                        continue
                    if s.startswith("end ") and ns and s.split()[1] == ns[-1]:
                        ns.pop()
                        continue
                    m = DECL_RE.match(s)
                    if m:
                        name = m.group(2)
                        full = ".".join(ns + [name])
                        table.setdefault(full, (rel, lineno))
                        table.setdefault(name, (rel, lineno))
    return table


DECLS = index_decls()


def lean_ref(name):
    """LaTeX for a Lean declaration name with its location."""
    if name not in DECLS:
        if ONLY:  # the table may belong to a document that is not generated now
            print(f"warning: Lean declaration `{name}` not found", file=sys.stderr)
            return r"\lean{" + name + r"} (not found)"
        sys.exit(f"error: Lean declaration `{name}` not found")
    rel, line = DECLS[name]
    short = rel.replace("GsimOT/", "", 1)
    return (r"\lean{" + name + r"}" + r"\newline{\scriptsize\texttt{" +
            tex_escape(short) + ":" + str(line) + r"}}")


def tex_escape(s):
    return (s.replace("\\", r"\textbackslash{}").replace("_", r"\_").replace("&", r"\&")
             .replace("#", r"\#").replace("%", r"\%"))


# ---------------------------------------------------------------------------------------------
# Data
# ---------------------------------------------------------------------------------------------

# Each row: (paper item, page, statement in LaTeX, [Lean declarations])

COMMON_ROWS = [
    ("Section~2", "5", r"Adjacency matrix $A_G\in\{0,1\}^{V\times V}$ (real entries)", ["GsimOT.adj"]),
    ("Appendix~A", "14", r"Degree $\deg_G(v)=|N_G(v)|$; $\sum_{v'}A_G(v,v')=\deg_G(v)$",
     ["GsimOT.deg", "GsimOT.sum_adj_eq_deg"]),
    ("Appendix~A, Eq.~(6)", "14", r"Discrepancy $D_{G,H}(v,w,v',w')=A_G(v,v')-A_H(w,w')$", ["GsimOT.disc"]),
    ("Section~2", "5", r"$\mathrm{DS}(V,W)$: doubly stochastic matrices", ["GsimOT.IsDS"]),
    ("Section~2", "5", r"Permutation matrix $P_\pi\in\mathrm{Perm}(V,W)$; $P_\pi\in\mathrm{DS}(V,W)$",
     ["GsimOT.permMat", "GsimOT.permMat_isDS"]),
    ("Section~2", "5", r"Local cost $L_Q(v,w)=\sum_{(v',w')}|D(v,w,v',w')|\,Q(v',w')$", ["GsimOT.localCost"]),
    ("Section~2, Eq.~(7)", "5, 14", r"$C_1(Q)=\max_{(v,w)\in\mathrm{supp}(Q)}L_Q(v,w)$",
     ["GsimOT.costOne", "GsimOT.localCost_le_costOne", "GsimOT.costOne_le"]),
    ("Section~2", "5", r"$C_1(\pi)=C_1(P_\pi)$ and $L_{P_\pi}(v,\pi(v))=|\pi(N_G(v))\triangle N_H(\pi(v))|$",
     ["GsimOT.costOneBij", "GsimOT.localCost_permMat_apply", "GsimOT.costOneBij_le_iff"]),
    ("Section~1, Section~2", "1, 5", r"$d_1(G,H)=\min_{\pi\in\mathrm{Bij}(V,W)}C_1(\pi)$", ["GsimOT.dOne"]),
    ("Section~2", "5", r"$d_1^{\mathrm{OT}}(G,H)=\min_{Q\in\mathrm{DS}(V,W)}C_1(Q)$ (as an infimum over $\mathrm{DS}(V,W)$)",
     ["GsimOT.dOTOne"]),
    ("Section~1, Section~2", "1, 5", r"Normalisations $\delta_1=n^{-1}d_1$, $\delta_1^{\mathrm{OT}}=n^{-1}d_1^{\mathrm{OT}}$ (scaling by $1/n$)",
     ["GsimOT.deltaOne", "GsimOT.deltaOTOne"]),
    ("Section~1, Section~3", "3, 6", r"$d_1^{\mathrm{OT}}\le d_1$ (every bijection is a fractional alignment)", ["GsimOT.dOTOne_le_dOne"]),
    ("Section~2, Eq.~(3)", "5", r"Birkhoff--von Neumann: $\mathrm{supp}(Q)$ contains the graph of a bijection",
     ["GsimOT.exists_bij_subset_supp"]),
    ("Observation~21", "20", r"$L_Q(v,w)\ge|\deg_G(v)-\deg_H(w)|$", ["GsimOT.observation21", "GsimOT.observation21_bij"]),
    ("Lemma~22 (construction)", "21", r"Adding the clique $K$ ($m=2\Delta+2\tau+k(\tau+\delta)+1$) and the staircase",
     ["GsimOT.lockSize", "GsimOT.stair", "GsimOT.lockGraph"]),
    ("Lemma~22 (1)", "21", r"$C_1(\pi)<\tau$ $\Rightarrow$ $\pi$ fixes all markers and $\pi(V)=V$", ["GsimOT.lemma22_bij"]),
    ("Lemma~22 (2)", "21", r"$Q(z_j,z_j)=1$ $\Rightarrow$ $C_1(Q')$ w.r.t.\ $(G',H')$ equals $C_1(Q)$ w.r.t.\ $(G,H)$",
     ["GsimOT.extendId", "GsimOT.lemma22_cost"]),
    ("Appendix~D.2", "28", r"Pseudometric $\rho_H(w,w')=|N_H(w)\triangle N_H(w')|$ and the triangle inequality",
     ["GsimOT.rho", "GsimOT.rho_triangle"]),
    ("Lemma~29 (first part)", "28", r"$Q(v,w)>0\Rightarrow\rho_H(\sigma(v),w)\le 2L$",
     ["GsimOT.rho_le_localCost_add", "GsimOT.lemma29_rho_le"]),
    ("Lemma~29 (second part)", "28", r"$L<1\Rightarrow\sigma$ is an isomorphism",
     ["GsimOT.rho_eq_zero_of_deg_eq_of_lt_two", "GsimOT.lemma29_iso", "GsimOT.lemma29_dOne_eq_zero"]),
    ("Lemma~29 (``in particular'')", "28", r"$G\not\cong H\Rightarrow d_1^{\mathrm{OT}}(G,H)\ge 1$",
     ["GsimOT.lemma29_one_le_dOTOne"]),
]

NORM_ROWS = [
    ("Appendix~A", "14", r"$\ell^p$ norm $\|x\|_p$ ($1\le p\le\infty$)",
     ["GsimOT.lpNorm", "GsimOT.lpNorm_eq_sum", "GsimOT.lpNorm_top"]),
    ("Appendix~A", "14", r"Operator norm $\|A\|_{p\to q}=\max_{\|x\|_p=1}\|Ax\|_q$ (in Lean the supremum over the unit ball $\|x\|_p\le1$, the same value for nonempty index sets)",
     ["GsimOT.opNorm", "GsimOT.lpNorm_mulVec_le", "GsimOT.opNorm_le_of_bound",
      "GsimOT.exists_lpNorm_mulVec_eq_opNorm"]),
    ("Appendix~A", "14", r"Hölder conjugate $q^*$ with $1/q^*=1-1/q$",
     ["GsimOT.one_le_conjExponent", "GsimOT.inv_conjExponent_toReal"]),
    ("Appendix~A", "14", r"Hölder's inequality $|y^\top z|\le\|y\|_{q^*}\|z\|_q$ and its equality case",
     ["GsimOT.abs_dotProduct_le_lpNorm_mul", "GsimOT.exists_dotProduct_eq_lpNorm"]),
    ("Lemma~19", "14", r"$\|A\|_{p\to q}=\max_{\|y\|_{q^*}=1,\|x\|_p=1}|y^\top Ax|$ (in Lean over the unit balls)",
     ["GsimOT.lemma19", "GsimOT.abs_dotProduct_mulVec_le_opNorm",
      "GsimOT.exists_abs_dotProduct_mulVec_eq_opNorm"]),
    ("--", "--", r"Triangle inequality, $\|A\|_{p\to q}\le\sum_{i,j}|A_{ij}|$ and continuity of $\|\cdot\|_{p\to q}$",
     ["GsimOT.opNorm_add_le", "GsimOT.opNorm_le_sum_abs", "GsimOT.abs_opNorm_sub_le", "GsimOT.continuous_opNorm"]),
    ("Appendix~A", "15", r"Restricting to rows and columns ``cannot increase the operator norm''",
     ["GsimOT.lpNorm_le_of_abs_le", "GsimOT.opNorm_restrict_le"]),
]

THM1_ROWS = [
    ("Theorem~1", "3", r"$\delta^{\bullet}_{p\to q}=\delta^{\mathrm{OT}}_{p\to q}$ for all $1\le p,q\le\infty$",
     ["GsimOT.theorem1"]),
    ("Theorem~1 (strengthened)", "3", r"$\delta_{p\to q}(G^{\bullet n\ell},H^{\bullet m\ell})\to\delta^{\mathrm{OT}}_{p\to q}(G,H)$ (the limit exists)",
     ["GsimOT.theorem1_tendsto"]),
    ("Theorem~1 (paper's proof)", "3, 15--20", r"If the limit defining $\delta^\bullet_{p\to q}$ exists (cited from [Gro25], p.~2), it equals $\delta^{\mathrm{OT}}_{p\to q}$; upper bound along $\ell=ks$ only",
     ["GsimOT.theorem1_of_tendsto"]),
    ("Section~1", "1--2", r"Blowup $G^{\bullet k}$ and blowup distance $\delta^\bullet=\lim_\ell\delta(G^{\bullet n\ell},H^{\bullet m\ell})$",
     ["GsimOT.blowup", "GsimOT.blowupSeq", "GsimOT.deltaBlowup"]),
    ("Section~1", "2", r"Fractional alignments $\mathrm{DS}^*(V,W)$", ["GsimOT.IsCoupling", "GsimOT.isCoupling_uniform"]),
    ("Section~1, Appendix~A, B", "3, 14, 15", r"$B_{p\to q}(G,H,Q^*)$ with $0^0:=0$; $\kappa_{p\to q}=1/q+1-1/p$",
     ["GsimOT.powZ", "GsimOT.Bmat", "GsimOT.kappa"]),
    ("Eq.~(2)", "3", r"$\delta^{\mathrm{OT}}_{p\to q}(G,H)=\min_{Q^*}\|B_{p\to q}(G,H,Q^*)\|_{p\to q}$ (infimum)",
     ["GsimOT.deltaOTPQ"]),
    ("Appendix~A", "14--15", r"The minimum in Eq.~(2) is attained (lower semicontinuity, compactness of $\mathrm{DS}^*(V,W)$)",
     ["GsimOT.lowerSemicontinuous_opNorm_Bmat", "GsimOT.isCompact_setOf_isCoupling", "GsimOT.exists_deltaOTPQ_eq"]),
    ("Section~1, 2, Appendix~B", "1, 3, 5, 20", r"$A^\pi_G$, $d_{p\to q}=\min_\pi\|A^\pi_G-A_H\|_{p\to q}$, $\delta_{p\to q}=N^{-\kappa}d_{p\to q}$",
     ["GsimOT.alignedDiff", "GsimOT.distPQ", "GsimOT.deltaPQ"]),
    ("Proof of Eq.~(9)", "15--16", r"$J(v,w)$ as blocks of the map $(w,j)\mapsto(v(w,j),w)$; $Q^*(v,w)=|J(v,w)|/N$",
     ["GsimOT.blockCard", "GsimOT.blockMap", "GsimOT.couplingOf"]),
    ("Proof of Eq.~(9)", "15", r"$Q^*\in\mathrm{DS}^*(V,W)$ (row sums $\ell n/N$, column sums $\ell m/N$)",
     ["GsimOT.sum_blockCard_row", "GsimOT.sum_blockCard_col", "GsimOT.isCoupling_couplingOf"]),
    ("Eq.~(10)", "15", r"$M_\pi((w,j),(w',j'))=D(v,w,v',w')$ for $j\in J(v,w)$, $j'\in J(v',w')$",
     ["GsimOT.alignedDiff_blowup_eq_disc"]),
    ("Proof of Eq.~(11)", "16", r"Spread test vectors: $\|\tilde x\|_p,\|\tilde y\|_{q^*}\le1$",
     ["GsimOT.lpNorm_spread_le"]),
    ("Proof of Eq.~(11)", "17", r"Chain of equalities $\tilde y^\top M_\pi\tilde x=N^\kappa\,y^\top Bx$",
     ["GsimOT.sum_comp_eq_sum_blockCard", "GsimOT.div_rpow_self_eq_powZ", "GsimOT.powZ_eq_rpow_mul_powZ_div"]),
    ("Eq.~(11)", "15", r"$\|M_\pi\|_{p\to q}\ge N^\kappa\|B_{p\to q}(G,H,Q^*)\|_{p\to q}$", ["GsimOT.eq11"]),
    ("Eqs.~(8), (9)", "15", r"$\delta^{\mathrm{OT}}_{p\to q}(G,H)\le\delta_{p\to q}(G^{\bullet n\ell},H^{\bullet m\ell})$ for all $\ell\ge1$",
     ["GsimOT.deltaOTPQ_le_blowupSeq"]),
    ("Claim~20 (proof)", "17", r"Rational couplings $Q^*_k$ with $\mathrm{supp}(Q^*_k)=\mathrm{supp}(Q^*_0)$ and $Q^*_k\to Q^*_0$ (here: denominators $\ell mn$, by Birkhoff rounding)",
     ["GsimOT.exists_integral_approx_close", "GsimOT.exists_rational_seq_supp_eq"]),
    ("(not in paper)", "--", r"Lift $Q$ to an $mn\times mn$ doubly stochastic matrix, Birkhoff, average back",
     ["GsimOT.liftM", "GsimOT.liftM_mem_doublyStochastic", "GsimOT.avgM", "GsimOT.isCoupling_avgM",
      "GsimOT.avgM_liftM", "GsimOT.permMatrix_apply_mem_rangeS"]),
    ("(not in paper)", "--", r"Rounding convex weights to multiples of $1/\ell$ with the same support",
     ["GsimOT.exists_round_weights"]),
    ("Claim~20 (proof)", "17", r"On a fixed support, $\|B_{p\to q}(G,H,Q^*_k)\|\to\|B_{p\to q}(G,H,Q^*_0)\|$",
     ["GsimOT.tendsto_powZ_apply", "GsimOT.exists_delta_opNorm_Bmat", "GsimOT.tendsto_opNorm_Bmat_of_supp_eq"]),
    ("Claim~20, Eq.~(13)", "17", r"A rational $Q^*\in\mathrm{DS}^*(V,W)$ with $\|B_{p\to q}(G,H,Q^*)\|\le\min_{Q^*_0}\|B_{p\to q}(G,H,Q^*_0)\|+\varepsilon$",
     ["GsimOT.claim20"]),
    ("Claim~20 (strengthened)", "17", r"Near-optimal couplings with denominator $N=\ell mn$ for \emph{every} large $\ell$",
     ["GsimOT.exists_integral_approx"]),
    ("Proof of Eq.~(15)", "18", r"Partitions $I(v,w)$, $J(v,w)$ of sizes $q(v,w)=NQ^*(v,w)$ and the bijection $\pi$",
     ["GsimOT.exists_fin_fun_card_fiber", "GsimOT.card_fiber_prod", "GsimOT.exists_blowup_bij"]),
    ("Proof of Eq.~(15)", "18--19", r"Averaged vectors: $\|x\|_p,\|y\|_{q^*}\le1$ (Hölder, Eq.~(5))",
     ["GsimOT.lpNorm_average_le"]),
    ("Proof of Eq.~(15)", "19--20", r"Chain of equalities $\tilde y^\top M_\pi\tilde x=N^\kappa\,y^\top Bx$",
     ["GsimOT.block_sum_eq"]),
    ("Eq.~(15)", "18", r"$N\cdot Q^*$ integral $\Rightarrow\delta_{p\to q}(G^{\bullet n\ell},H^{\bullet m\ell})\le\|B_{p\to q}(G,H,Q^*)\|_{p\to q}$",
     ["GsimOT.eq15_of_integral"]),
    (r"Eq.~(15), $\ell=ks$", "18", r"$k$ clears the denominators of $Q^*$ $\Rightarrow\delta_{p\to q}(G^{\bullet nks},H^{\bullet mks})\le\|B_{p\to q}(G,H,Q^*)\|$ for all $s\ge1$",
     ["GsimOT.exists_denom", "GsimOT.eq15"]),
    ("Eqs.~(12), (14)", "17--18", r"Conclusion: $\delta^\bullet\le\delta^{\mathrm{OT}}$, hence equality",
     ["GsimOT.theorem1_tendsto", "GsimOT.theorem1_of_tendsto"]),
]

THM1_NOTES = [
    r"\textbf{Two versions of the final step.} The paper takes the existence of the limit "
    r"$\delta^\bullet=\lim_\ell\delta_{p\to q}(G^{\bullet n\ell},H^{\bullet m\ell})$ from [Gro25] (p.~2) and "
    r"proves the upper bound only along the subsequence $\ell=ks$ (Eq.~(15)). \lean{theorem1_of_tendsto} is this "
    r"argument verbatim, with the existence of the limit as a hypothesis. The main theorem \lean{theorem1} needs no "
    r"such hypothesis: its approximation step (\lean{exists_integral_approx}) works for \emph{every} sufficiently large "
    r"$\ell$, so the whole sequence converges to $\delta^{\mathrm{OT}}_{p\to q}$ (\lean{theorem1_tendsto}). In Lean, "
    r"$\delta^\bullet$ is \texttt{limUnder} of the sequence (\lean{deltaBlowup}).",
    r"\textbf{Claim 20} (p.~17) is formalised as \lean{claim20} and follows the paper: a "
    r"minimiser $Q^*_0$ (\lean{exists_deltaOTPQ_eq}, from the attainment argument of Appendix~A), rational couplings "
    r"$Q^*_k\to Q^*_0$ with the same support, and convergence of the norms on a fixed support. The rational sequence is "
    r"obtained differently: the paper uses that the couplings vanishing outside $S$ form a rational "
    r"polytope; we construct the sequence explicitly. $Q^*_0$ is lifted to the doubly stochastic $mn\times mn$ matrix "
    r"$R((v,i),(w,j))=Q^*_0(v,w)$, decomposed by Birkhoff--von Neumann (Mathlib), the positive coefficients are rounded "
    r"to positive multiples of $1/\ell$, and the result is averaged back. This preserves the support, which is "
    r"essential: with $0^0=0$, $Q\mapsto B_{p\to q}(Q)$ is discontinuous at the boundary of the support for $p=1$ or "
    r"$q=\infty$.",
    r"Eqs.~(11) and (15) follow the paper's argument verbatim: the coupling $Q^*=|J|/N$, Eq.~(10), "
    r"maximising test vectors from Lemma~19, the spread (resp.\ averaged) vectors and the chain of equalities. "
    r"The norm computations for these vectors are factored out into the general block lemmas "
    r"\lean{lpNorm_spread_le} and \lean{lpNorm_average_le}, for a block map $b:\beta\to\alpha$ with blocks "
    r"$\{w\}\times J(v,w)$. \lean{eq11} is Eq.~(11) and \lean{eq15_of_integral} is Eq.~(15).",
    r"\textbf{Normalisation.} $\delta_{p\to q}=N^{-\kappa_{p\to q}}d_{p\to q}$ for graphs of order $N$, i.e.\ the "
    r"metric is scaled by $1/s(N)$ with $s(N)=N^{1/q+1-1/p}$ (p.~3, l.~88--90; Appendix~B, p.~15, l.~513--514, and "
    r"p.~20, l.~637--638).",
    r"Operator norms are defined as the supremum of $\|Ax\|_q$ over the unit \emph{ball} $\|x\|_p\le1$, and "
    r"Lemma~19 is stated with $\|x\|_p\le1$, $\|y\|_{q^*}\le1$. For nonempty index sets this equals the "
    r"paper's maximum over unit spheres by homogeneity; the paper's proof notes this itself (p.~20, l.~636--637).",
    r"Theorem~1 is formalised for general $p,q\in[1,\infty]$ (\texttt{ENNReal}). It is independent of the "
    r"local edit distance development: for $p=q=1$ it concerns $\|B_{1\to1}\|_1$, which the paper relates "
    r"to $C_1$ in Eq.~(7); this link is proved in Common (\lean{dOT_one_one_eq_dOTOne}) but not needed here.",
]

CUT_ROWS = [
    ("Appendix~A", "14", r"Cut norm $\|A\|_\square=\max_{S,T}|A(S,T)|$",
     ["GsimOT.cutNorm", "GsimOT.le_cutNorm", "GsimOT.cutNorm_le", "GsimOT.exists_eq_cutNorm", "GsimOT.cutNorm_smul"]),
    ("Section~1, Section~2", "2, 5", r"$B(G,H,Q)$ and $C_\square(Q)=\|B(G,H,Q)\|_\square$",
     ["GsimOT.B", "GsimOT.costCut"]),
    ("Section~1, Section~2", "1--2, 5", r"$d_\square$, $d_\square^{\mathrm{OT}}$ (infimum) and $\delta_\square=n^{-2}d_\square$, $\delta^{\mathrm{OT}}_\square=n^{-2}d^{\mathrm{OT}}_\square$",
     ["GsimOT.dCut", "GsimOT.dOTCut", "GsimOT.deltaCut", "GsimOT.deltaOTCut"]),
    ("Appendix~E.2, Eq.~(21), E.2.2", "32, 36", r"$\zeta_R(A,B)=\|D_{A,B}\|_{\square,\mu_R}$ with $\mu_R=R/n$; $\zeta_R(A_G,A_H)=\zeta_R=n^{-2}C_\square(R)$ for graphs",
     ["GsimOT.epsR", "GsimOT.adjMat", "GsimOT.epsR_adjMat"]),
    ("Section~1, Appendix~B", "1, 3, 15", r"$\kappa_{p\to q}=1/q+1-1/p$, $A^\pi_G-A_H$, $d_{p\to q}$ and $\delta_{p\to q}=n^{-\kappa_{p\to q}}d_{p\to q}$ ($s(n)=n^{\kappa_{p\to q}}$)",
     ["GsimOT.kappa", "GsimOT.alignedDiff", "GsimOT.distPQ", "GsimOT.deltaPQ"]),
]

PROP12_ROWS = [
    ("Proposition~12", "11", r"$\delta_\square(G,H)\le\delta_2(G,H)\le2\sqrt{\delta_\square(G,H)}$", ["GsimOT.proposition12"]),
    ("Proof of Prop.~12 (Appendix~F)", "44--45", r"$\frac1{\sqrt{mn}}\|A\|_\square\le\|A\|_2$ (l.~1384; Cauchy--Schwarz, l.~1391--1396)", ["GsimOT.cutNorm_le_sqrt_mul_opNorm_two"]),
    ("Proof of Prop.~12 ([Nik09, Thm.~3])", "44--45", r"$\|A\|_2\le2\sqrt{\|A\|_{(\infty)}\|A\|_\square}$ with $\|A\|_{(\infty)}=\max_{v,w}|A_{vw}|$ (l.~1384--1385; cited in the paper, l.~1397; proved here)",
     ["GsimOT.opNorm_two_le_two_sqrt_cutNorm", "GsimOT.opNorm_two_le_two_sqrt_of_abs_le", "GsimOT.maxEntryNorm"]),
    ("(proof of [Nik09])", "--", r"$\|A\|_{\infty\to1}\le4\|A\|_\square$ (sign vectors)", ["GsimOT.infOneNorm_le_four_cutNorm"]),
    ("Proof of Prop.~12", "44", r"Apply to $A^\pi_G-A_H$ (entries in $[-1,1]$) and normalise (l.~1385--1387)", ["GsimOT.proposition12"]),
]

PROP12_NOTES = [
    r"\textbf{Nikiforov's inequality is proved, not cited.} The paper cites [Nik09, Thm.~3] (p.~45, l.~1397) for "
    r"$\|A\|_2\le2\sqrt{\|A\|_{(\infty)}\|A\|_\square}$. The formalisation proves it directly. "
    r"By the Schur test, $\|Ax\|_2^2=x^\top A^\top Ax\le\max_j\sum_k|(A^\top A)_{jk}|\,\|x\|_2^2$. Moreover "
    r"$\sum_k|(A^\top A)_{jk}|=\sum_iA_{ij}(As)_i\le\|A\|_{(\infty)}\|A\|_{\infty\to1}\le4\|A\|_{(\infty)}\|A\|_\square$ "
    r"for a suitable sign vector $s$.",
    r"$\delta_2=\delta_{2\to2}=n^{-\kappa_{2\to2}}d_2$ with $\kappa_{2\to2}=1$, using the shared definitions "
    r"in \texttt{Common/AlignedDistances.lean} and the operator norms of \texttt{Common/OperatorNorm.lean}.",
    r"The first inequality is formalised as $\|A\|_\square\le\sqrt{mn}\,\|A\|_2$ (\lean{cutNorm_le_sqrt_mul_opNorm_two}), "
    r"the paper's $\frac1{\sqrt{mn}}\|A\|_\square\le\|A\|_2$ (p.~44, l.~1384) multiplied by $\sqrt{mn}$.",
]

PROP10_ROWS = [
    ("Proposition~10", "9", r"Graphs on $145$ vertices with $d_\square(G,H)=8$ and $d^{\mathrm{OT}}_\square(G,H)\le4$ (exactly as stated)",
     ["GsimOT.Prop10.proposition10", "GsimOT.Prop10.card_Vtx"]),
    ("Remark after Prop.~10", "10", r"$d^{\mathrm{OT}}_\square(G,H)=4$ (l.~330; the Lean certificate \texttt{OptimalAlignment.lean}, linked in footnote~2); $C_\square(Q)\ge4$ for every $Q\in\mathrm{DS}(V,W)$",
     ["GsimOT.Prop10.dOTCut_eq_four", "GsimOT.Prop10.four_le_dOTCut", "GsimOT.Prop10.four_le_costCut"]),
    ("Theorem~3~(3)", "4", r"$\delta_\square(G,H)=2\,\delta^{\mathrm{OT}}_\square(G,H)$ for these graphs (l.~126)",
     ["GsimOT.Prop10.theorem3_item3"]),
    ("Appendix~E.1", "30--31", r"Core pairs $v_i^\sigma$, markers $L_i$ ($|L_i|=9(i+1)$), matrix $Z$",
     ["GsimOT.Prop10.Vtx", "GsimOT.Prop10.Core", "GsimOT.Prop10.Marker", "GsimOT.Prop10.Z"]),
    ("Appendix~E.1, Fig.~3", "10, 31", r"$G$: $v_i^\sigma v_j^\tau\in E$ iff $\sigma\tau=Z_{ij}$; $H$: iff $\sigma\tau=-Z_{ij}$; markers adjacent to their pair",
     ["GsimOT.Prop10.gAdj", "GsimOT.Prop10.hAdj", "GsimOT.Prop10.G12", "GsimOT.Prop10.H12"]),
    ("Appendix~E.1", "31", r"Degrees $13,22,31,40,49$ on pairs, $2$ on markers; different degrees differ by $\ge9$",
     ["GsimOT.Prop10.dg", "GsimOT.Prop10.sum_adj_G12", "GsimOT.Prop10.sum_adj_H12", "GsimOT.Prop10.nine_le_of_dg_ne"]),
    ("Lemma~33", "31", r"$d_\square(G,H)=8$", ["GsimOT.Prop10.lemma33"]),
    ("Proof of Lemma~33", "31", r"$C_\square(\pi)\ge|\deg_G(v)-\deg_H(\pi(v))|$ (cut $S=\{\pi v\}$, $T=W$)",
     ["GsimOT.Prop10.abs_dg_sub_le"]),
    ("Proof of Lemma~33", "31", r"Pair-preserving $\pi$: core cut values $x^\top My$ with $M_{ij}=\frac12Z_{ij}(1+r_ir_j)$; $\ge8$ for all $32$ patterns $r$",
     ["GsimOT.Prop10.Mr", "GsimOT.Prop10.wit", "GsimOT.Prop10.eight_le_wit", "GsimOT.Prop10.eight_le_of_dg"]),
    ("Proof of Lemma~33", "31", r"Every bijection costs $\ge8$", ["GsimOT.Prop10.eight_le_cutNorm"]),
    ("Proof of Lemma~33", "31", r"For $\pi=\mathrm{id}$ every cut value is $x^\top Zy$, $x,y\in\{-1,0,1\}^5$, and $|x^\top Zy|\le8$",
     ["GsimOT.Prop10.cut_sum_eq_core", "GsimOT.Prop10.abs_bilin_Z_le", "GsimOT.Prop10.cutNorm_refl_le"]),
    ("Lemma~34", "31", r"$d^{\mathrm{OT}}_\square(G,H)\le4$", ["GsimOT.Prop10.lemma34"]),
    ("Proof of Lemma~34", "31", r"$Q$: identity on markers, $\frac12$ on each pair block", ["GsimOT.Prop10.Q40", "GsimOT.Prop10.Q40_isDS"]),
    ("Proof of Lemma~34", "32", r"Discrepancies involving markers vanish; core discrepancy $\frac12Z_{ij}(\sigma\sigma'+\tau\tau')$",
     ["GsimOT.Prop10.B40_eq_zero_left", "GsimOT.Prop10.B40_eq_zero_right", "GsimOT.Prop10.B40_atom"]),
    ("Proof of Lemma~34", "32", r"Straight/crossed decomposition: two pentagon copies of weight $\frac12$, each cut $\le2$",
     ["GsimOT.Prop10.atom_sum_eq", "GsimOT.Prop10.costCut_Q40_le"]),
    (r"$d^{\mathrm{OT}}_\square\ge4$, step 1", "", r"$|B(f,g)|\le C_\square(Q)$ for $f,g\colon\Omega\to[0,1]$",
     ["GsimOT.Prop10.exists_abs_sum_mul_le", "GsimOT.Prop10.abs_bilin_le_cutNorm"]),
    (r"$d^{\mathrm{OT}}_\square\ge4$, step 2", "", r"$\sum_y D(x,y)q_y=d(x)$ and $\sum_x q_xd(x)=0$",
     ["GsimOT.Prop10.sum_disc_mul", "GsimOT.Prop10.sum_B_right", "GsimOT.Prop10.sum_mul_dd"]),
    (r"$d^{\mathrm{OT}}_\square\ge4$, step 3", "", r"$L+B(s,t)\le4C_\square(Q)$ for $|s|,|t|\le1$, $s=0$ where $d\ne0$",
     ["GsimOT.Prop10.degree_add_bil_le"]),
    (r"$d^{\mathrm{OT}}_\square\ge4$, step 4", "", r"$L\ge9(10-T)$, $T$ the mass on the core atoms",
     ["GsimOT.Prop10.nine_mul_le_row", "GsimOT.Prop10.nine_mul_le_L"]),
    (r"$d^{\mathrm{OT}}_\square\ge4$, step 5", "", r"$\max_{a,b\in\{\pm1\}^5}a^\top\mathrm{diag}(x)Z\mathrm{diag}(x)b\ge\frac{16}5\sum_ix_i-8$ for $x\in[0,2]^5$",
     ["GsimOT.Prop10.zForm", "GsimOT.Prop10.zForm_flip", "GsimOT.Prop10.exists_zForm_ge"]),
    (r"$d^{\mathrm{OT}}_\square\ge4$, step 5", "", r"Test functions on straight and crossed atoms: $B(s,t)=a^\top CZCb+a'^\top HZHb'$",
     ["GsimOT.Prop10.testFn", "GsimOT.Prop10.disc_atom", "GsimOT.Prop10.bil_testFn"]),
]

PROP10_NOTES = [
    r"\textbf{$d^{\mathrm{OT}}_\square(G,H)=4$.} Proposition~10 states $d^{\mathrm{OT}}_\square(G,H)\le4$. The remark after "
    r"it (p.~10, l.~330) states equality, verified by ``one of our Lean certificates''; its footnote~2 links the file "
    r"\texttt{OptimalAlignment.lean}, whose main result is \lean{dOTCut_eq_four}. Theorem~3~(3) (p.~4, l.~126) uses this "
    r"equality. The paper refers to this file for the proof, so the rows ``step 1--5'' above follow the outline in its "
    r"module docstring. For every "
    r"$Q\in\mathrm{DS}(V,W)$ with $T$ the mass of $Q$ on the $20$ core atoms, $d(x)=\deg_G(v)-\deg_H(w)$ and "
    r"$L=\sum_xq_x|d(x)|$: $4C_\square(Q)\ge L+B(s,t)\ge9(10-T)+\frac{16}5T-16\ge16$ for suitable test functions $s,t$.",
    r"The finite checks are done by \texttt{decide} (no \texttt{native\_decide}, so no extra axioms). "
    r"$|x^\top Zy|\le8$ is reduced to $\sum_j|(Zx)_j|\le8$ over the $3^5$ vectors $x$. The lower bound $\ge8$ "
    r"is checked for each of the $32$ sign patterns $r$ with an explicit table of maximisers \lean{wit}. This "
    r"replaces the paper's case analysis on $|K|$ up to symmetry.",
    r"Both graphs live on the same vertex type \lean{Vtx} $=(\mathrm{Fin}\,5\times\mathrm{Bool})\oplus"
    r"\Sigma_i\,\mathrm{Fin}(9(i+1))$; the natural bijection $\mathrm{id}$ of the paper is \texttt{Equiv.refl}.",
]

THM11_ROWS = [
    ("Theorem~11", "10", r"$\delta^{\mathrm{OT}}_\square\le\delta_\square\le C\,\delta^{\mathrm{OT}}_\square\ln\frac{e}{\delta^{\mathrm{OT}}_\square}\ln\bigl(e\ln\frac{e}{\delta^{\mathrm{OT}}_\square}\bigr)$ (assuming Thm.~35)",
     ["GsimOT.theorem11_of_thin", "GsimOT.theorem11", "GsimOT.theorem11_of_rackeShah"]),
    ("Theorem~11 (power bound), E.2.3", "10, 44", r"$\delta_\square\le C_\alpha(\delta^{\mathrm{OT}}_\square)^\alpha$ for every $\alpha<1$ (also the $0<\alpha<1$ versions)",
     ["GsimOT.theorem11_power_lt_one_of_thin", "GsimOT.theorem11_power_lt_one", "GsimOT.theorem11_power_lt_one_of_rackeShah", "GsimOT.theorem11_power_of_thin", "GsimOT.theorem11_power"]),
    ("Theorem~2 (cut part)", "3", r"$\delta_\square\le C_\varepsilon(\delta^{\mathrm{OT}}_\square)^{1-\varepsilon}$ for every $\varepsilon>0$",
     ["GsimOT.theorem2_cut_of_thin", "GsimOT.theorem2_cut_of_rackeShah"]),
    ("Theorem~35 [HOG26]", "32", r"Thin permutations exist with $\alpha\le C_{\mathrm{thin}}\ln(2n)\ln\ln(4n)$ --- \textbf{explicit hypothesis}",
     ["GsimOT.ThinPermutationTheorem", "GsimOT.IsThin"]),
    ("Theorem~35 from [HOG26, Thm.~1.4]", "32", r"Derived from the \texttt{ThinMatching} library, assuming only [RS14]",
     ["GsimOT.thinPermutationTheorem_of_rackeShah"]),
    ("Theorem~39", "36", r"$\zeta_P\le\zeta_Q+36\sqrt{d_n}\,n^{-1/6}$, $d_n=\lceil2\log n\rceil$ ($n\ge2$; $A,B$ symmetric with entries in $[0,1]$)",
     ["GsimOT.theorem39", "GsimOT.dn"]),
    ("Lemma~40", "36", r"Lifted kernels: $\|K\|_{\mathcal L^2(n)}\le t\Rightarrow\|K^{(1)}\|_{\square,\mu_Q},\|K^{(2)}\|_{\square,\mu_Q}\le t$",
     ["GsimOT.lemma40_fst", "GsimOT.lemma40_snd", "GsimOT.OpBound", "GsimOT.weight_sq_le"]),
    ("Eqs.~(21), (22)", "32", r"$\zeta_Q$ (\lean{epsR}); bilinear forms with $[0,1]$-valued functions are bounded by the cut norm; testing on sets",
     ["GsimOT.epsR", "GsimOT.abs_bilin_le_cutNorm", "GsimOT.abs_cut_le_epsR"]),
    ("Lemma~41", "37", r"Close support functions $\Rightarrow$ close bilinear maxima (paper's proof: $m_T(Y,Y')$ via $h_Y(Tu')$ and $h_{Y'}(T^*u)$)",
     ["GsimOT.lemma41", "GsimOT.lemma41_step", "GsimOT.abs_inner_le_bilMax_add", "GsimOT.abs_supportFn_sub_le", "GsimOT.supportFn", "GsimOT.bilMax"]),
    ("Lemma~42", "37", r"Symmetrisation (independent $X_a\in\{0,1\}$ with $\mathbb E X_a=\theta_a$)", ["GsimOT.Lemma47.lemma42", "GsimOT.Lemma47.bern"]),
    ("Lemma~43 [LT91, Thm.~4.12]", "38", r"Talagrand contraction lemma (cited in the paper; \textbf{proved here})",
     ["GsimOT.ContractionPrinciple", "GsimOT.contractionPrinciple", "GsimOT.ContractionAux.two_point", "GsimOT.ContractionAux.comparison"]),
    ("Lemma~44, Eq.~(29)", "38--39", r"Block Rademacher estimate $\le2M(\sum_j\ell_j^2)^{1/2}$ (random representatives $I_j\in B_j$, Jensen, Lemma~43)",
     ["GsimOT.Lemma47.lemma44", "GsimOT.Lemma47.sum_piFinset_comp", "GsimOT.Lemma47.radAvg_norm_le"]),
    ("Proof of Lemma~45", "39--40", r"Spectral theorem, Parseval, truncations $A_t,B_t$ with $\|A-A_t\|_{\mathcal L^2(n)},\|B-B_t\|_{\mathcal L^2(n)}\le t$",
     ["GsimOT.spectral_entry", "GsimOT.parseval_row", "GsimOT.specTrunc", "GsimOT.opBound_sub_specTrunc"]),
    ("Eq.~(31)", "39", r"$|\zeta_Q(A,B)-\zeta_Q(A_t,B_t)|\le2t$", ["GsimOT.eq31", "GsimOT.cutNorm_le_of_eq_add3"]),
    ("Proof of Lemma~45", "39--40", r"Vectors $z_{ij}$ ($\|z_{ij}\|\le\sqrt2$), operator $T_t$ ($\|T_t\|_{2\to2}\le1/t$), $\langle z_{ij},T_tz_{k\ell}\rangle=(A_t)_{ik}-(B_t)_{j\ell}$",
     ["GsimOT.specVec", "GsimOT.specDiag", "GsimOT.diagOp", "GsimOT.norm_specVec_le", "GsimOT.abs_specDiag_le", "GsimOT.norm_diagOp_le", "GsimOT.diagForm_specVec", "GsimOT.inner_diagOp"]),
    ("Lemma~45, Eq.~(30)", "39", r"Spectral approximation: $|\zeta_Q-\max_{S,T}|\ldots\langle z_{ij},T_tz_{k\ell}\rangle\ldots||\le2t$",
     ["GsimOT.lemma45", "GsimOT.zonKernel"]),
    ("Eqs.~(32)--(34)", "40", r"Zonotope $Z_Q$, its support function $h_Q$ (Eq.~(33)), pseudometric $\rho$",
     ["GsimOT.zonLin", "GsimOT.cube", "GsimOT.hSupp", "GsimOT.supportFn_zonotope", "GsimOT.rhoSupp", "GsimOT.norm_zonLin_le", "GsimOT.isCompact_zonotope"]),
    ("Eq.~(35)", "40", r"$\rho$ is a pseudometric, convex in both arguments",
     ["GsimOT.rhoSupp_triangle", "GsimOT.rhoSupp_convex", "GsimOT.hSupp_lin"]),
    ("Eqs.~(36), (37)", "40--41", r"$\max_{u,u'\in Z_Q}|\langle u,T_tu'\rangle|$ is the maximum of Eq.~(30) (attained at indicators); $|\zeta_Q-\max_{Z_Q}|\le2t$",
     ["GsimOT.eq36", "GsimOT.eq36_expand", "GsimOT.eq37"]),
    ("Corollary~46", "41", r"$\zeta_P\le\zeta_Q+4t+\frac{2\sqrt2}{t}\rho(P,Q)$ for all $P,Q\in\mathrm{DS}(n)$", ["GsimOT.corollary46"]),
    ("Lemma~47", "41", r"Merging two permutations: $\rho(P,(1-\theta)P_0+\theta P_1)\le20Mn^{-1/3}$ (the proof gives $18M$)",
     ["GsimOT.lemma47", "GsimOT.lemma47_sharp"]),
    ("Proof of Lemma~47", "42", r"Blocks along the cycles of $\tau$ with properties (i), (ii)",
     ["GsimOT.Lemma47.exists_sep_cover", "GsimOT.Lemma47.exists_blocks"]),
    ("Proof of Lemma~47, Eq.~(38)", "42--43", r"A good choice $X$ ($\Delta(T_X)\le16Mn^{-1/3}$); repairing $T_X$ into a bijection",
     ["GsimOT.Lemma47.exists_good_choice", "GsimOT.Lemma47.exists_equiv_eq_off"]),
    (r"Proof of Lemma~48, Eq.~(3)", "43", r"Birkhoff + Carath\'eodory: $Q=\sum_{s\le N}\lambda_sP_s$, $N\le n^2$", ["GsimOT.exists_perm_decomp"]),
    ("Lemma~48", "43", r"Binary-tree merging: $\rho(P,Q)\le20Md_nn^{-1/3}$", ["GsimOT.lemma48", "GsimOT.merge_aux", "GsimOT.combo"]),
    ("Proof of Theorem~39", "43", r"$t=\sqrt{20d_n}\,n^{-1/6}$: $4t+80d_nn^{-1/3}/t=8t<36\sqrt{d_n}\,n^{-1/6}$", ["GsimOT.theorem39"]),
    ("Eq.~(23)", "32", r"$\alpha$-thin permutations: thinness for all cuts $(X\cup Y,\overline X\cup\overline Y)$", ["GsimOT.IsThin"]),
    ("Lemma~36", "33", r"Thinness $\Rightarrow\sum_i|x_i-y_{\pi(i)}|\le\alpha\sum_{ij}Q_{ij}|x_i-y_j|$ (level sets, integral)",
     ["GsimOT.lemma36", "GsimOT.levelInd", "GsimOT.levelInd_apply", "GsimOT.integral_levelInd"]),
    ("Lemma~37, Eq.~(24)", "33--34", r"Local agreement (for $y=\mathbf1_T$, the case used)", ["GsimOT.lemma37"]),
    ("Eq.~(25)", "34", r"$\|RK\|_\square\le\|K\|_\square$ for $R\in\mathrm{DS}(n)$ (one-dimensional form)", ["GsimOT.abs_sum_mul_le_of_cut"]),
    ("Theorem~38", "34", r"There is $P$ with $\zeta_P\le(1+4\alpha)\zeta_Q$, $\alpha=C_{\mathrm{thin}}\ln(2n)\ln\ln(4n)$", ["GsimOT.theorem38"]),
    ("Proof of Thm.~38, Eq.~(26)", "34", r"$\zeta_P\le(1+4\alpha)\zeta_Q$ for every $\alpha$-thin $P$; $\zeta_P=n^{-2}\|A-PBP^\top\|_\square$",
     ["GsimOT.eq26", "GsimOT.epsR_permMat_le", "GsimOT.sum_permMat_mul_atoms"]),
    ("Proof of Thm.~38, Eq.~(27)", "35", r"$n^{-2}\|Q^\top AQ-B\|_\square\le\zeta_Q$", ["GsimOT.eq27_left"]),
    ("Proof of Thm.~38", "35", r"$n^{-2}\|EA\|_\square\le2\alpha\zeta_Q$ (Lemmas~36, 37, mean zero)",
     ["GsimOT.normEA_le", "GsimOT.abs_sum_le_half_of_sum_eq_zero"]),
    ("Proof of Thm.~38, Eqs.~(28), (25)", "35", r"$A-RAR^\top=EA+R(EA)^\top$; $\|R(EA)^\top\|_\square\le\|EA\|_\square$",
     ["GsimOT.eq28_cut", "GsimOT.cut_R_EAt_le"]),
    ("Proof of Thm.~38, Eq.~(27)", "35", r"$n^{-2}\|A-RAR^\top\|_\square\le4\alpha\zeta_Q$", ["GsimOT.eq27_right"]),
    ("Section~2; proof of Thm.~11", "5, 44", r"$C_\square(P_\pi)=\|A^\pi_G-A_H\|_\square$; lower bound $\delta^{\mathrm{OT}}_\square\le\delta_\square$",
     ["GsimOT.costCut_permMat", "GsimOT.deltaOTCut_le_deltaCut"]),
    ("Proof of Thm.~11", "44", r"An optimal $Q$ exists (compactness of $\mathrm{DS}$, continuity of $C_\square$)",
     ["GsimOT.isCompact_DS", "GsimOT.continuous_costCut", "GsimOT.exists_costCut_eq_dOTCut"]),
    ("Eq.~(39)", "44", r"$\delta_\square\le C_1\ln(2n)\ln\ln(4n)\,\varepsilon$, $C_1=1+4C_{\mathrm{thin}}$, using $\ln4\cdot\ln\ln8>1$",
     ["GsimOT.eq39", "GsimOT.one_le_log_mul_log_log", "GsimOT.one_lt_log_four_mul_log_log_eight"]),
    ("Proof of Thm.~11", "44", r"Case analysis ($\varepsilon=0$, $\varepsilon\ge\frac12$, $n\le\varepsilon^{-12}$, $n>\varepsilon^{-12}$), $C=\max\{2,39C_1,113\}$",
     ["GsimOT.main_numeric", "GsimOT.error_term_le", "GsimOT.dn_mul_log_two_le", "GsimOT.log_fourteen_lt_three"]),
    ("(not in the paper)", "", r"$n=1$: $\delta_\square=0$ (the paper assumes $n\ge2$ in Appendix~E.2)",
     ["GsimOT.deltaCut_le_zero_of_card_eq_one", "GsimOT.rhs_nonneg"]),
    ("Proof of Thm.~11", "44", r"$\varepsilon^{1-\alpha}\ln\frac e\varepsilon\ln(e\ln\frac e\varepsilon)$ is bounded on $(0,1]$, for every $\alpha<1$",
     ["GsimOT.power_numeric", "GsimOT.power_numeric_lt_one"]),
]

THM11_NOTES = [
    r"\textbf{Cited results.} Theorem~35 ([HOG26, Thm.~1.4], Haqi--Oveis Gharan; p.~32) is the only remaining "
    r"assumption. It is the explicit hypothesis \lean{ThinPermutationTheorem} of \lean{theorem11_of_thin}; "
    r"no \texttt{axiom} is added. Its statement matches [HOG26, Thm.~1.4] (bipartite case: an "
    r"$O(\log n\log\log n)$-thin perfect matching, not necessarily in $\mathrm{supp}(x)$), written with an "
    r"absolute constant as $C\ln(2n)\ln\ln(4n)$ as in the paper, with thinness in the cut form of Eq.~(23). "
    r"The Lean hypothesis gives thinness with exactly $\alpha=C_{\mathrm{thin}}\ln(2n)\ln\ln(4n)$, so the step "
    r"``$\alpha'$-thin with $\alpha'\le\alpha$, hence $\alpha$-thin'' of the proof of Theorem~38 is built in. "
    r"The contraction principle [LT91, Thm.~4.12] (Lemma~43), also "
    r"cited in the paper, is \emph{proved} (\lean{contractionPrinciple}) via Talagrand's comparison argument. "
    r"The paper's other citations used here are also proved: [vdVW96, L.~2.3.1] (Lemma~42) and "
    r"Carath\'eodory's theorem [Sch86] with $N\le n^2$ (proof of Lemma~48).",
    r"\textbf{Theorem~35 from [HOG26].} [HOG26] is formalised in the separate library \texttt{ThinMatching} "
    r"(see \texttt{ThinMatching/HOG26\_correspondence.pdf}), assuming the tree-cut sparsifier theorem of "
    r"R\"acke--Shah [RS14] that [HOG26] cites. \lean{thinPermutationTheorem_of_rackeShah} derives "
    r"\lean{ThinPermutationTheorem} from it, so \lean{theorem11_of_rackeShah} proves Theorem~11 assuming only [RS14].",
    r"\textbf{Additive bound (Appendix~E.2.2): what follows the paper.} Lemma~41 is proved with the paper's "
    r"support-function argument (\lean{lemma41_step}: $m_T(Z,Z)\le m_T(Z',Z)+M\eta\tau$ via $h_Z(Tu')$, then "
    r"$m_T(Z',Z)\le m_T(Z',Z')+M\eta\tau$ via $h_{Z'}(T^*u)$ with the adjoint; then $T$ and $-T$); the statement does "
    r"not assume $Z,Z'$ convex. Lemma~44 averages over independent uniform representatives $I_j\in B_j$ "
    r"(\lean{sum_piFinset_comp}), uses Jensen, Lemma~43 for fixed $I$ and Eq.~(29); the statement does not assume "
    r"the blocks disjoint. Lemma~42 is proved for arbitrary $\theta_j$. Eq.~(36) is proved as an identity "
    r"(\lean{eq36}) and Corollary~46 for all $P,Q\in\mathrm{DS}(n)$. Expectations are finite weighted sums "
    r"(\lean{radAvg}, \lean{bern}, uniform averages over \lean{Fintype.piFinset}).",
    r"\textbf{Additive bound: choices of the formalisation.} (1) The standard inner product on $\mathbb R^n$ is used instead of "
    r"$\mathcal L^2(n)$, with the scalings adjusted (eigenvalues $\lambda_r/n$, eigenfunctions $\sqrt n\,e_r$); "
    r"$\|K\|_{\mathcal L^2(n)}\le t$ is \lean{OpBound} $K$ $(tn)$ in the equivalent AM--GM form. (2) $H=\mathbb R^{V\sqcup W}$ "
    r"(dimension $2n$) instead of $\mathbb R^{I_A\sqcup I_B}$; the extra coordinates of $z_{ij}$ are zero, so the "
    r"case $I_A=I_B=\emptyset$ needs no separate treatment. (3) The blocks of Lemma~47 come from a maximal set of "
    r"``cut points'', no two of them $1$ to $L-1$ steps apart along $\tau$, instead of the explicit cycle "
    r"decomposition; they satisfy the paper's properties (i) and (ii), which is all the proof uses. "
    r"Lemma~44 is applied to all blocks with the vectors $X_au_i$ (zero on blocks with $X_a=0$) instead of to the "
    r"blocks with $X_a=1$; the bound is the same. The w.l.o.g.\ step $P_0=I$ is done by working with "
    r"$\tau=\pi_0^{-1}\pi_1$ and $u_i=z_{i,\pi_0(i)}$ directly. The proof gives $18Mn^{-1/3}$ "
    r"(\lean{lemma47_sharp}), the statement $20Mn^{-1/3}$ (\lean{lemma47}). (4) In Lemma~48 the binary tree splits "
    r"the index set in halves at every node (all weights positive) instead of padding with leaves of weight zero; "
    r"the induction is the paper's.",
    r"\textbf{Theorem~38 (Appendix~E.2.1).} The proof follows the paper step by step: $\zeta_P$ as a cut norm "
    r"(\lean{epsR_permMat_le}), the split $A-PBP^\top=(A-RAR^\top)+P(Q^\top AQ-B)P^\top$ with $R=PQ^\top$, the two bounds "
    r"of Eq.~(27) (\lean{eq27_left}, \lean{eq27_right}), the bound on $EA$ via Lemmas~36 and~37 (\lean{normEA_le}), and "
    r"Eq.~(28) with Eq.~(25) (\lean{eq28_cut}, \lean{cut_R_EAt_le}). Matrices are written entrywise "
    r"($R(v,k)=Q(k,\pi v)$). Lemma~37 is proved for $y=\mathbf1_T$, the only case used. Eq.~(25) is used in the "
    r"one-dimensional form \lean{abs_sum_mul_le_of_cut}. The bound for every $\alpha$-thin $P$ (Eq.~(26)) is "
    r"\lean{eq26}, the existence statement is \lean{theorem38}.",
    r"\textbf{Proof of Theorem~11 (Appendix~E.2.3).} The optimal $Q$ is obtained by compactness, as in the paper's "
    r"``let $Q$ be optimal''. Eq.~(39) uses $C_1=1+4C_{\mathrm{thin}}$ and $\ln(2n)\ln\ln(4n)\ge\ln4\cdot\ln\ln8>1$ "
    r"for $n\ge2$ as in the paper. The case $n=1$, excluded in Appendix~E.2, is handled separately ($\delta_\square=0$). "
    r"For $n>\varepsilon^{-12}$, the paper's monotonicity argument for "
    r"$x\mapsto x^{-1/6}\sqrt{\ln x}$ is replaced by $\ln m\le m/e$ with $m=n^{1/6}$; the constant $112$ is the same. "
    r"The constants are $C=\max\{2,39C_1,113\}$ as in the paper.",
    r"\textbf{Power bound.} Proved for every $\alpha<1$ (\lean{theorem11_power_lt_one_of_thin}), as stated in E.2.3; "
    r"for $\alpha\le\frac12$ the bound for $\alpha=\frac12$ is used together with $f^{1/2}\le f^\alpha$ on $[0,1]$. "
    r"The cut part of Theorem~2, $\delta_\square\le C_\varepsilon(\delta^{\mathrm{OT}}_\square)^{1-\varepsilon}$ for every "
    r"$\varepsilon>0$, is \lean{theorem2_cut_of_thin}. (In Lean $0^\alpha=0$ for $\alpha<0$; the statement still holds "
    r"since $\delta^{\mathrm{OT}}_\square=0$ forces $\delta_\square=0$.)",
    r"In Lean $\ln0=0$ and $e/0=0$, so the right-hand side of Theorem~11 is $0$ when $\delta^{\mathrm{OT}}_\square=0$, "
    r"matching the paper's convention.",
]

HOG_PAPER = (r"A.~Haqi, S.~Oveis Gharan. \emph{On Thin Perfect Matchings up to Polylogarithmic Factors}. "
             r"arXiv:2606.01330v2 (2026) [HOG26].")

HOG_ROWS = [
    ("Section~1, Section~2", "1, 4", r"Weighted graph $G=(V,E,x)$, $x(\delta(S))$, perfect matchings, $|M\cap\delta(S)|$, $\alpha$-thin, $M\subseteq\mathrm{supp}(x)$",
     ["ThinMatching.WGraph", "ThinMatching.cutWeight", "ThinMatching.PerfectMatching", "ThinMatching.crossCount", "ThinMatching.IsThin", "ThinMatching.InSupport"]),
    ("Section~1, Thm.~2.5", "1, 5", r"$x\in\mathrm{PM}(G)$: convex combination of perfect matchings; bipartite version (degree constraints)",
     ["ThinMatching.IsFracPM", "ThinMatching.IsFracPMBip", "ThinMatching.bipGraph"]),
    ("Thm.~1.4 (bipartite)", "1, 2", r"Bipartite cut weight, crossing count and thinness for $M=\{(l,\pi l)\}$",
     ["ThinMatching.bipCutWeight", "ThinMatching.bipCrossCount", "ThinMatching.IsThinBip"]),
    ("Lemma~1.2", "1", r"Every perfect matching in $\mathrm{supp}(x)$ of the graph of Fig.~1 ($2n+2$ vertices) is at best $\frac n2$-thin",
     ["ThinMatching.lemma12", "ThinMatching.lemma12_not_thin"]),
    ("Fig.~1", "1", r"The graph: solid edges $1-\frac1n$, dotted edges $\frac1n$; $x$ as the average of $n$ perfect matchings",
     ["ThinMatching.LowerBound.fig1", "ThinMatching.LowerBound.Mk", "ThinMatching.LowerBound.fig1_isFracPM", "ThinMatching.LowerBound.fig1_bad_cut"]),
    ("Theorem~1.3", "2", r"Support-constrained $O(n\log n)$-thin perfect matching (assuming Lemma~3.6)", ["ThinMatching.theorem13_support"]),
    ("Def.~3.1, Lemma~3.2", "5", r"Trimming $\tilde x$; removed weight $\le(|V|-1)\varepsilon$; components $\varepsilon$-edge-connected",
     ["ThinMatching.trimGraph", "ThinMatching.IsTrimmed", "ThinMatching.exists_split", "ThinMatching.trimming_exists", "ThinMatching.lemma32"]),
    ("Algorithm~1", "6", r"Independent sampling of $\alpha$ copies of each edge with probability $\tilde x_e$ (finite product space)",
     ["ThinMatching.bernW", "ThinMatching.prob", "ThinMatching.sampleProb", "ThinMatching.sampleCut", "ThinMatching.sampleGraph"]),
    ("Thm.~2.4, Def.~3.3", "5", r"Tutte's theorem (Mathlib) and Tutte witnesses",
     ["ThinMatching.IsTutteWitness", "ThinMatching.witnessF", "ThinMatching.exists_witness_of_no_pm"]),
    ("Lemma~3.4", "6", r"At most $(|V|+1)^{|V|}$ Tutte witnesses", ["ThinMatching.card_witnesses_le"]),
    ("Lemma~3.5, Eq.~(1)", "6", r"The sample contains a perfect matching w.h.p.; $x(F)\ge1$ (odd-set argument)",
     ["ThinMatching.lemma35", "ThinMatching.one_le_witnessF_weight", "ThinMatching.witness_bound_le"]),
    ("Lemma~3.6", "7", r"Sampling preserves cuts up to $O(\alpha)$ w.h.p.\ (proof omitted in [HOG26]) --- \textbf{explicit hypothesis}",
     ["ThinMatching.Lemma36"]),
    ("Proof of Thm.~1.3", "7", r"Union over components; thinness for all cuts; $M\subseteq Y\subseteq\mathrm{supp}(\tilde x)\subseteq\mathrm{supp}(x)$",
     ["ThinMatching.sum_cut_eq_sum_blocks", "ThinMatching.crossCount_le_of_good", "ThinMatching.prob_bad_blocks_le"]),
    ("Def.~2.1", "4", r"Weighted tree with Steiner nodes (rooted, parent function); $y(\delta_{\mathcal T}(\mathcal S))$; $\lambda_{\mathcal T}(S)$; $q$-tree-cut-sparsifier",
     ["ThinMatching.RootedTree", "ThinMatching.subtree", "ThinMatching.treeCutWeight", "ThinMatching.lambdaT", "ThinMatching.IsTreeCutSparsifier"]),
    ("Thm.~2.2 [RS14]", "4", r"Every graph has an $O(\log n\log\log n)$-tree-cut-sparsifier --- \textbf{explicit hypothesis}",
     ["ThinMatching.RackeShahTheorem"]),
    ("Defs.~4.1, 4.2, 4.4", "7--8", r"Tree cuts, load of a matching on a tree edge, discrepancy $\Delta$",
     ["ThinMatching.load", "ThinMatching.loadBip", "ThinMatching.discBip", "ThinMatching.discNonBip"]),
    ("Proposition~4.3", "7", r"$\mathrm{load}_M(f)\le\beta\,x(\delta(V_r(f)))$ for all tree edges $\Rightarrow$ $M$ is $\beta q$-thin",
     ["ThinMatching.prop43", "ThinMatching.LoadVsCut.exists_cut_edge", "ThinMatching.LoadVsCut.treeCutWeight_subtree"]),
    ("Lemma~4.5", "8", r"$x(\delta(S))\ge\Delta_{\mathrm{bip}}(S)$; $x(\delta(S))\ge1$ for $|S|$ odd",
     ["ThinMatching.lemma45_bip", "ThinMatching.lemma45", "ThinMatching.one_le_crossCount_of_odd", "ThinMatching.cutWeight_eq_sum_crossCount"]),
    ("Lemma~4.6, Algorithm~2", "9--10", r"Tree pairing: a perfect matching with $\mathrm{load}_M(f)=\Delta(V_r(f))$ for every tree edge",
     ["ThinMatching.lemma46_bip", "ThinMatching.lemma46", "ThinMatching.subtree_laminar", "ThinMatching.subtree_ssubset_of_separates"]),
    ("Theorem~1.4 (bipartite)", "2", r"An $O(\log n\log\log n)$-thin perfect matching $M\subseteq L\times R$ (assuming [RS14])",
     ["ThinMatching.theorem14_bip", "ThinMatching.Theorem14.bipPM", "ThinMatching.Theorem14.cutWeight_bipGraph", "ThinMatching.Theorem14.log_mul_loglog_le"]),
    ("Theorem~1.4 (general)", "2", r"An $O(\log n\log\log n)$-thin perfect matching $M\subseteq\binom V2$ for $x\in\mathrm{PM}(G)$ (assuming [RS14])",
     ["ThinMatching.theorem14"]),
    ("Main paper, Thm.~35, Eq.~(23)", "--", r"Bridge to \texttt{GsimOT}: Theorem~35 (p.~32, thinness Eq.~(23)) and Theorem~11 of the main paper assuming only [RS14]",
     ["GsimOT.thinPermutationTheorem_of_rackeShah", "GsimOT.theorem11_of_rackeShah", "GsimOT.theorem11_power_of_rackeShah"]),
]

HOG_NOTES = [
    r"\textbf{Independence.} The library \texttt{ThinMatching} imports only Mathlib and does not depend on the "
    r"\texttt{GsimOT} formalisation. It has its own definitions of weighted graphs, cuts, perfect matchings, "
    r"thinness and trees. The only connection is the bridge file \texttt{GsimOT/Theorem11\_CutUpperBound/"
    r"FromThinMatching.lean}, which derives the main paper's Theorem~35 from the "
    r"bipartite case of Theorem~1.4. The main paper's $\alpha$-thinness, Eq.~(23) (cuts $(X\cup Y,\overline X\cup"
    r"\overline Y)$ of $K_{n,n}$, all $X,Y\subseteq[n]$), is exactly \lean{IsThinBip} with $S_L=X$, $S_R=Y$, and "
    r"its constant $C_{\mathrm{thin}}\ln(2n)\ln\ln(4n)$ is the one of \lean{theorem14_bip} (same $C$).",
    r"\textbf{Cited results.} Theorem~2.2 (R\"acke--Shah [RS14], tree-cut sparsifiers) is used but not proved in "
    r"[HOG26]. It is the explicit hypothesis \lean{RackeShahTheorem}, with the bound $C\ln(2n)\ln\ln(4n)$, which "
    r"is positive for all $n\ge1$. Lemma~3.6 is stated in [HOG26] with its proof omitted (``a simple Chernoff "
    r"bound and a cut-counting argument''). It is the explicit hypothesis \lean{Lemma36}, formulated in the "
    r"finite sampling model of Algorithm~1, for any $\alpha\ge cN\ln(2N)$ with $N\ge|W|$, with failure probability "
    r"$\le1/(4N)$. This is what the omitted argument (Karger's cut counting + Chernoff) yields. No Lean "
    r"\texttt{axiom} is introduced; Theorems~1.3 and 1.4 take these hypotheses as arguments.",
    r"\textbf{Trees.} A weighted tree with Steiner nodes is represented as a rooted tree on a finite type via a "
    r"parent function, with $V\hookrightarrow\mathcal V$; the tree edges are $\{v,\mathrm{parent}(v)\}$. Every "
    r"tree can be rooted, so this is no loss of generality. The tree path between two vertices uses the edge "
    r"$\{v,\mathrm{parent}(v)\}$ iff exactly one of them lies in the subtree of $v$; this is how loads are defined. "
    r"Discrepancies are taken on the subtree side $V_s(f)$, which equals the root side $V_r(f)$ of the paper since "
    r"$|L|=|R|$ resp.\ $|V|$ is even.",
    r"\textbf{Lemma 4.6 (Algorithm 2).} Instead of executing the greedy vertex by vertex, the proof matches, one "
    r"pair at a time, a matchable pair inside a \emph{minimal} subtree that contains one. This is the first pair "
    r"the greedy forms. The paper's main observation (no proper subtree of it contains a matchable pair) shows "
    r"that load and discrepancy change in the same way, which gives $\mathrm{load}=\Delta$ by induction.",
    r"\textbf{Proposition 4.3.} The charging step uses a lemma (\lean{exists_cut_edge}) finding, for $a\in\mathcal S$, "
    r"$b\notin\mathcal S$, a tree edge cut by $\mathcal S$ that separates $a$ and $b$, by induction on the depths "
    r"instead of via the explicit path. Lemma~4.5 in the general case is derived from the convex combination of "
    r"perfect matchings (each crosses an odd set), the easy direction of Theorem~2.5.",
    r"\textbf{Theorem 1.3.} The paper argues per component. The formalisation also checks cuts through "
    r"several components: sampled edges lie inside blocks, so the per-component bounds add up. Further choices: a "
    r"union bound over at most $|V|$ components, $\varepsilon=1/(4|V|)$ (the paper's $1/(8n)$ for $|V|=2n$), and "
    r"$x(F)\ge1$ (slightly stronger than the paper's route). Trimming is modelled by block labellings, and each "
    r"step adds one block.",
    r"\textbf{Not formalised.} Corollary~1.6 (metric distortion) depends on [ACR23, Prop.~3] and on mechanism "
    r"definitions outside the mathematical core of the paper. Theorem~2.3 (algorithmic sparsifiers) is not used.",
    r"Lemma~1.2 is proved for every $n\ge1$; as in the paper, one crossing matching edge is counted (ratio $\ge n/2$).",
]

OT_ROWS = [
    ("Section~1, Appendix~A", "2--3, 14", r"Couplings $\mathrm{DS}^*(V,W)$; $x^a$ with $0^a:=0$ (convention $0^0=0$)", ["GsimOT.IsCoupling", "GsimOT.powZ"]),
    ("Section~1, Eqs.~(1), (2)", "2--3", r"$B(G,H,Q)$ and $B_{p\to q}(G,H,Q)$", ["GsimOT.B", "GsimOT.Bmat"]),
    ("Eq.~(2), Section~2", "3, 5", r"$\delta^{\mathrm{OT}}_{p\to q}$ (couplings) and $d^{\mathrm{OT}}_{p\to q}$ ($\mathrm{DS}(V,W)$), both infima",
     ["GsimOT.deltaOTPQ", "GsimOT.dOT"]),
    ("Sections~1--2, Appendices~A--B", "3, 5, 14--15", r"$\delta^{\mathrm{OT}}_{p\to q}=n^{-\kappa_{p\to q}}d^{\mathrm{OT}}_{p\to q}$ for graphs of the same order $n$ ($d^{\mathrm{OT}}_{p\to q}$ is the unnormalised version, $s(n)=n^{\kappa_{p\to q}}$), via $\mathrm{DS}(V,W)=n\,\mathrm{DS}^*(V,W)$ and the homogeneity of $B_{p\to q}$ and of $\|\cdot\|_{p\to q}$",
     ["GsimOT.deltaOTPQ_eq_dOT", "GsimOT.Bmat_smul", "GsimOT.opNorm_smul_of_nonneg"]),
    ("Appendix~A", "14--15", r"``All minima \dots\ are attained'' for $\delta^{\mathrm{OT}}_{p\to q}$ and $d^{\mathrm{OT}}_{p\to q}$: lower semicontinuity of $Q\mapsto\|B_{p\to q}(G,H,Q)\|$, compactness",
     ["GsimOT.lowerSemicontinuous_opNorm_Bmat", "GsimOT.isCompact_setOf_isCoupling", "GsimOT.exists_deltaOTPQ_eq",
      "GsimOT.exists_dOT_eq"]),
]

PROP13_ROWS = [
    ("Proposition~13", "11", r"$d_2(G_r,H_r)=\sqrt r$ and $\frac1{2\sqrt2}\le d^{\mathrm{OT}}_2(G_r,H_r)\le1$, $n=4r^2+3r+1=\Theta(r^2)$",
     ["GsimOT.Prop13.proposition13"]),
    ("Prop.~13 + Lemma~49", "11, 45", r"the same with $\frac1{2\sqrt2}\le\frac r{\sqrt n}\le d^{\mathrm{OT}}_2(G_r,H_r)$, the bound $\frac r{\sqrt n}\le d^{\mathrm{OT}}_2(G_r,H_r)$ being Lemma~49",
     ["GsimOT.Prop13.proposition13_explicit"]),
    ("Theorem~3 (4)", "4", r"$\delta_2(G_r,H_r)\ge\sqrt r\cdot\delta^{\mathrm{OT}}_2(G_r,H_r)$", ["GsimOT.Prop13.theorem3_item4"]),
    ("after Prop.~13", "11", r"No bound $\delta_2\le C_\alpha(\delta^{\mathrm{OT}}_2)^\alpha$ for $\alpha>\frac34$ (l.~391--393)",
     ["GsimOT.Prop13.no_power_bound", "GsimOT.Prop13.deltaPQ_eq", "GsimOT.Prop13.deltaOTPQ_bounds"]),
    ("Appendix~F.1, Fig.~7", "45", r"Core $X=\{u\}\cup\{v_{i,k}\}$, clocks $C$, tags $T_i$; $N(v_{i,k})=T_i\cup\{c_1,\dots,c_k\}$; $u$ isolated in $G_r$, adjacent to $C$ in $H_r$",
     ["GsimOT.Prop13.Core", "GsimOT.Prop13.Marker", "GsimOT.Prop13.Vtx", "GsimOT.Prop13.graph", "GsimOT.Prop13.Gr", "GsimOT.Prop13.Hr"]),
    ("Appendix~F.1", "45", r"$|V|=n=4r^2+3r+1$; $H_r$ has minimum degree $\ge r$", ["GsimOT.Prop13.card_Vtx", "GsimOT.Prop13.le_deg_Hr"]),
    ("Appendix~F.1", "45", r"$d_2(G_r,H_r)=\sqrt r$: row of $\pi(u)$ (spectral norm $\ge$ row norm) and the star for $\mathrm{id}$ (l.~1412--1416)",
     ["GsimOT.Prop13.distPQ_eq", "GsimOT.Prop13.sqrt_row_le_opNorm22", "GsimOT.Prop13.sqrt_le_opNorm_alignedDiff", "GsimOT.Prop13.opNorm_diff_refl_le"]),
    ("Lemma~49", "45", r"$\frac r{\sqrt n}\le d^{\mathrm{OT}}_2(G_r,H_r)\le1$", ["GsimOT.Prop13.lemma49"]),
    ("Proof of Lemma~49", "45--46", r"Shifts $\sigma_i$ and $Q=\frac1{2r}\sum_iP_{\sigma_i}$", ["GsimOT.Prop13.shift", "GsimOT.Prop13.tau", "GsimOT.Prop13.Qs", "GsimOT.Prop13.Qs_isDS"]),
    ("Proof of Lemma~49", "46", r"Vectors $d_{xy}$; $C_2(Q)\le1$ (tags: Cauchy--Schwarz, clocks orthogonal; l.~1424--1436)",
     ["GsimOT.Prop13.dv", "GsimOT.Prop13.sum_qc_dvDot_le", "GsimOT.Prop13.opNorm_Bq_le", "GsimOT.Prop13.dOT_le_one"]),
    ("Proof of Lemma~49", "46", r"Test vector $\mathbf1_R$: $(B\mathbf1_R)(x,y)=\mathbf1_R(x,y)(\deg_G x-\deg_H y)$, hence $C_2(R)\ge r/\sqrt n$ (l.~1437--1446)",
     ["GsimOT.Prop13.le_opNorm_Bmat", "GsimOT.Prop13.le_dOT_of_deg", "GsimOT.Prop13.le_dOT"]),
    ("Proof of Prop.~13", "46", r"$\frac r{\sqrt n}\ge\frac1{2\sqrt2}$ since $8r^2\ge n$ (l.~1447--1448)", ["GsimOT.Prop13.proposition13_explicit"]),
]

PROP13_NOTES = [
    r"\textbf{Upper bound of Lemma~49.} The paper computes $C_2(Q)^2=\|K^\top K\|_2=1$ for the block form "
    r"$\begin{pmatrix}0&K\\K^\top&0\end{pmatrix}$. The formalisation instead shows "
    r"$\sum_{(x,y)}Q(x,y)(d_{xy}\cdot\zeta)^2\le\|\zeta\|^2$. It uses Cauchy--Schwarz on each tag block and the "
    r"orthogonality of the clock markers, and concludes $|y^\top Bx|\le1$ through Lemma~19. This is the same "
    r"estimate, organised as a bilinear bound.",
    r"The lower bound of Lemma~49 is proved for arbitrary graphs (\lean{le_dOT_of_deg}: a vertex whose "
    r"degree differs from every degree in $H$ by $\ge c$ forces $d^{\mathrm{OT}}_2\ge c/\sqrt n$) and then "
    r"specialised to $c=r$.",
    r"The remark after Proposition~13 is formalised as \lean{no_power_bound}. It uses "
    r"$\delta_2(G_r,H_r)=\sqrt r/n$, $\delta^{\mathrm{OT}}_2(G_r,H_r)\le1/n$ and $n\le8r^2$; the lower estimate "
    r"$\delta^{\mathrm{OT}}_2=\Omega(n^{-1})$ is not needed for this conclusion.",
    r"Indices: $v_{i,k}$ is \texttt{some (i, k)} and $u$ is \texttt{none} in \lean{Core}; clocks and tags are the "
    r"two summands of \lean{Marker}. $G_r$ and $H_r$ are one construction \lean{graph} with a Boolean flag for the "
    r"edges at $u$.",
    r"\lean{proposition13} is Proposition~13. \lean{proposition13_explicit} states Proposition~13 together with the bound "
    r"$\frac r{\sqrt n}\le d^{\mathrm{OT}}_2(G_r,H_r)$ of Lemma~49, which the proof of Proposition~13 combines with "
    r"$\frac r{\sqrt n}\ge\frac1{2\sqrt2}$; \lean{proposition13} is derived from it.",
]

THM14_ROWS = [
    ("Theorem~14", "12", r"$\delta_2\le\delta^{\mathrm{OT}}_2+2\sqrt{2\delta^{\mathrm{OT}}_2}$", ["GsimOT.theorem14"]),
    ("end of proof of Thm.~14", "50", r"$\delta_2\le\gamma_Q+4\sqrt{\gamma_Qh}$ with $\gamma_Q=\delta^{\mathrm{OT}}_2$ (l.~1573--1574)", ["GsimOT.theorem14_h"]),
    ("Thm.~14 and end of its proof", "12, 50", r"$\delta_2\le\min\{1,\delta^{\mathrm{OT}}_2+4\sqrt{h\,\delta^{\mathrm{OT}}_2}\}\le\min\{1,\delta^{\mathrm{OT}}_2+2\sqrt{2\delta^{\mathrm{OT}}_2}\}$: the bound of the proof combined with $\delta_2\le1$ ($\|\cdot\|_2\le\|\cdot\|_F\le n$)",
     ["GsimOT.theorem14_min", "GsimOT.deltaPQ_two_two_le_one", "GsimOT.Theorem14.distPQ_le_card"]),
    ("after Thm.~14; Thm.~2 ($\\delta_2$)", "3, 12", r"$\delta^{\mathrm{OT}}_2\le1$, hence $\delta_2\le(1+2\sqrt2)\sqrt{\delta^{\mathrm{OT}}_2}$ (l.~399)",
     ["GsimOT.theorem14_sqrt", "GsimOT.deltaOTPQ_two_two_le_one", "GsimOT.opNorm_Bmat_le_sum"]),
    ("Appendix~F.2", "47", r"Spectral norm: $\|\cdot\|_{2\to2}$ equals Mathlib's $\ell^2$ operator norm; $\|K\|_2\le\|K\|_F$; transposition, reindexing (l.~1452--1453)",
     ["GsimOT.opNorm_two_two_eq", "GsimOT.l2_norm_le_frobenius", "GsimOT.l2_norm_transpose", "GsimOT.l2_norm_submatrix"]),
    ("Appendix~F.2", "47, 50", r"$\|K\|_F^2=\sum_r\|K\phi_r\|_2^2$ for an orthonormal basis (l.~1453; in the proof of Eq.~(43), l.~1554--1556)", ["GsimOT.Theorem14.frobenius_eq_sum_eigvec"]),
    ("Eq.~(40)", "47", r"$\gamma_Q(A',B')$: $n\gamma_Q=\|B_{2\to2}\|_2$ (kernel $\sqrt Q\,D\,\sqrt Q$); the bilinear bound",
     ["GsimOT.Theorem14.discKernel", "GsimOT.Theorem14.eq40_le", "GsimOT.Theorem14.discKernel_shift"]),
    ("Eq.~(41)", "47", r"$A-PBP^\top=(A-RAR^\top)+P(Q^\top AQ-B)P^\top$, $R=PQ^\top$", ["GsimOT.Theorem14.eq41"]),
    ("Lemma~50", "47", r"$n^{-1}\|Q^\top A'Q-B'\|_2\le\gamma_Q(A',B')$ (via Lemma~19)", ["GsimOT.Theorem14.lemma50"]),
    ("Appendix~F.2", "47", r"$\|R\|_2\le1$ for $R\in\mathrm{DS}(n)$; $\|P\|_2\le1$ (l.~1485--1486)",
     ["GsimOT.l2_norm_le_one_of_stochastic", "GsimOT.Theorem14.norm_pmat_mul_transpose_le", "GsimOT.Theorem14.norm_pmat_le"]),
    ("Eq.~(28)", "47, 50", r"$X-RXR^\top=EX+R(EX)^\top$, $E=I-R$, for symmetric $X$", ["GsimOT.Theorem14.eq28"]),
    ("Eq.~(42)", "48", r"$\frac1{n^2}\sum_{ij}Q_{ij}F_{ij}^2\le\gamma_Q^2\|y\|^2$, $F_{ij}=x_i-r_j$",
     ["GsimOT.Theorem14.Fmat", "GsimOT.Theorem14.Fmat_eq", "GsimOT.Theorem14.eq42"]),
    ("Lemma~51", "48", r"Local agreement: $\frac1{n^2}\sum_{ij}Q_{ij}(x_i-(Q^\top x)_j)^2\le\gamma_Q^2\|y\|^2$ for $x=A'y$",
     ["GsimOT.Theorem14.lemma51", "GsimOT.sum_weighted_sq_sub"]),
    ("Lemma~52", "48--49", r"$\mathbb E\|(I-R)x\|_2^2=\sum_{ij}Q_{ij}(x_i-(Q^\top x)_j)^2$ for the random permutation of a Birkhoff decomposition",
     ["GsimOT.Theorem14.lemma52", "GsimOT.Theorem14.sum_birkhoff_eq", "GsimOT.exists_birkhoff_decomposition"]),
    ("Proof of Thm.~14", "49", r"$Q$ optimal: $\gamma_Q=\delta^{\mathrm{OT}}_2$ (l.~1526)", ["GsimOT.exists_dOT_eq", "GsimOT.deltaOTPQ_eq_dOT"]),
    ("Proof of Thm.~14", "49", r"Centring: $p_G=2|E(G)|/n^2$, $A'=A-p_GJ$, $B'=B-p_GJ$; $D_{A',B'}=D_{A,B}$, $A'-PB'P^\top=A-PBP^\top$, $\|A'\|_F^2=n^2h^2$ (l.~1528--1532)",
     ["GsimOT.edgeDensity", "GsimOT.edgeDensity_eq", "GsimOT.Theorem14.shiftAdj", "GsimOT.Theorem14.discKernel_shift", "GsimOT.Theorem14.aligned_shift", "GsimOT.Theorem14.sum_sq_shiftAdj"]),
    ("Proof of Thm.~14", "49", r"Spectral truncation $A'_t$, $I_t$; $\|A'-A'_t\|_2\le nt$, $|I_t|\le h^2/t^2$ (l.~1533--1544)",
     ["GsimOT.Theorem14.truncHigh", "GsimOT.Theorem14.truncLow", "GsimOT.Theorem14.ind", "GsimOT.Theorem14.norm_truncLow_le", "GsimOT.Theorem14.sq_mul_card_le"]),
    ("Eq.~(43)", "49", r"$\mathbb E\|EA'_t\|_2^2\le\mathbb E\|EA'_t\|_F^2=\sum_{r\in I_t}\mathbb E\|EA'\phi_r\|_2^2\le n^2\gamma_Q^2|I_t|$",
     ["GsimOT.Theorem14.eq43", "GsimOT.Theorem14.frobenius_one_sub_R_truncHigh", "GsimOT.Theorem14.truncHigh_mulVec_eigvec", "GsimOT.Theorem14.errBij"]),
    ("Proof of Thm.~14", "50", r"Some $P$ with $\|EA'_t\|_2\le n\gamma_Qh/t$ (l.~1561--1562)",
     ["GsimOT.Theorem14.exists_one_sub_R_truncHigh_le", "GsimOT.Theorem14.exists_le_of_sum_mul_le"]),
    ("chain (a), p.~50", "50", r"$\|A'-RA'R^\top\|_2\le2nt+2n\gamma_Qh/t$; with Eq.~(41), Lemma~50: $\gamma_P\le\gamma_Q+2t+2\gamma_Qh/t$",
     ["GsimOT.Theorem14.exists_bij_norm_le'", "GsimOT.Theorem14.exists_bij_norm_le", "GsimOT.Theorem14.exists_aligned_le", "GsimOT.Theorem14.exists_aligned_le'",
      "GsimOT.Theorem14.deltaPQ_le_threshold_G", "GsimOT.Theorem14.deltaPQ_le_threshold_H"]),
    ("Proof of Thm.~14", "50", r"Choice $t=\sqrt{\gamma_Qh}$ (or $t\to0$); $h\le\frac12$ (l.~1573--1575)",
     ["GsimOT.Theorem14.le_of_forall_threshold", "GsimOT.Theorem14.deltaPQ_le_of_isDS", "GsimOT.min_sqrt_density_le_half", "GsimOT.four_sqrt_le"]),
]

THM14_NOTES = [
    r"\textbf{Statement.} \lean{theorem14} is Theorem~14, $\delta_2\le\delta^{\mathrm{OT}}_2+2\sqrt{2\delta^{\mathrm{OT}}_2}$. "
    r"As in the paper, it follows from the bound $\delta_2\le\gamma_Q+4\sqrt{\gamma_Qh}$ at the end of the proof "
    r"(\lean{theorem14_h}) and $h\le\frac12$. \lean{theorem14_min} combines \lean{theorem14_h} with $\delta_2\le1$ "
    r"(\lean{deltaPQ_two_two_le_one}, via $\|\cdot\|_2\le\|\cdot\|_F\le n$) into "
    r"$\delta_2\le\min\{1,\delta^{\mathrm{OT}}_2+4\sqrt{h\,\delta^{\mathrm{OT}}_2}\}\le\min\{1,\delta^{\mathrm{OT}}_2+2\sqrt{2\delta^{\mathrm{OT}}_2}\}$, "
    r"which implies Theorem~14.",
    r"\textbf{Proof structure.} The formalisation follows Appendix~F.2 step by step: \lean{lemma50} uses Lemma~19 and the "
    r"bilinear bound \lean{eq40_le} behind Eq.~(40) (two test vectors); \lean{eq42} and \lean{lemma51} follow the proof "
    r"of Lemma~51 (via $F_{ij}$ and the expansion $\sum Q(F-m)^2=\sum QF^2-\sum m^2$); Eq.~(43) is \lean{eq43} "
    r"(expectation of the squared spectral norm, bounded by the Frobenius norm computed in the eigenbasis, "
    r"\lean{frobenius_eq_sum_eigvec}); the chain (a) uses Eq.~(28) for $A'_t$ (\lean{eq28}) and Eq.~(41) "
    r"(\lean{eq41}); and the proof starts from an optimal $Q$ (\lean{exists_dOT_eq}).",
    r"\textbf{No symmetry reduction.} Instead of assuming $h=\sqrt{p_G(1-p_G)}$ by symmetry (l.~1529), both cases are "
    r"proved: centre by $p_G$ and use $\|A'\|_F$ (\lean{deltaPQ_le_threshold_G}), or centre by $p_H$ and use "
    r"$\|B'\|_F$, applying the argument to $(B',A',Q^\top)$ (\lean{deltaPQ_le_threshold_H}). The minimum is then taken.",
    r"\textbf{Normalisations.} The Lean works with $\|B_{2\to2}(G,H,Q)\|_2=n\gamma_Q$ (\lean{discKernel}) and with the "
    r"threshold $s=nt$; all statements are the paper's after division by $n$. Expectations over the random "
    r"permutation are weighted sums over a Birkhoff decomposition (\lean{exists_birkhoff_decomposition}).",
    r"\textbf{$\delta^{\mathrm{OT}}_2\le1$} (used after Theorem~14, l.~399) is proved as "
    r"\lean{deltaOTPQ_two_two_le_one}: $\|B_{2\to2}(G,H,Q^*)\|_2\le\|B_{2\to2}(G,H,Q^*)\|_F\le\sum Q^*\le1$.",
]

PROP8_ROWS = [
    ("Proposition~8", "7", r"For even $r\ge2$: $d_1(G_r,H_r)=r$, $d_1^{\mathrm{OT}}(G_r,H_r)=1$, $|V(G_r)|=\Theta(r^3)$",
     ["GsimOT.Prop8.proposition8"]),
    ("Theorem~3 (2)", "4", r"For even $r\ge2$: $\delta_1(G_r,H_r)=r\cdot\delta_1^{\mathrm{OT}}(G_r,H_r)$",
     ["GsimOT.Prop8.theorem3_item2"]),
    ("after Prop.~8", "9", r"No bound of the form $\delta_1\le c\cdot\delta_1^{\mathrm{OT}}$", ["GsimOT.Prop8.no_linear_bound"]),
    ("after Thm.~9", "9", r"No bound of the form $\delta_1\le C\cdot(\delta_1^{\mathrm{OT}})^\alpha$ with $\alpha>2/3$",
     ["GsimOT.Prop8.no_power_bound"]),
    ("Appendix~D.1", "25", r"$\ell=r^2+2r$; core $X$ ($n_X=1+r(\ell-1)$), markers $M=C\cup T\cup B$ ($n_M=2r^2$)",
     ["GsimOT.Prop8.ell", "GsimOT.Prop8.Core", "GsimOT.Prop8.Marker", "GsimOT.Prop8.card_core",
      "GsimOT.Prop8.card_marker"]),
    ("Appendix~D.1 (table)", "26", r"Adjacency of core vertices to clocks, tags and bits; patterns $\chi$",
     ["GsimOT.Prop8.pat", "GsimOT.Prop8.chiG", "GsimOT.Prop8.chiH"]),
    ("Appendix~D.1", "25--26", r"$G^0_r$, $H^0_r$; $\deg_{H^0_r}(z)=\deg_{G^0_r}(z)+\mathbf 1[z\in C]$",
     ["GsimOT.Prop8.bipGraph", "GsimOT.Prop8.G0", "GsimOT.Prop8.H0", "GsimOT.Prop8.deg_H0_marker"]),
    ("Appendix~D.1", "26", r"Lemma~22 applied with markers sorted by degree, $\Delta=n_X$, $\tau=r$, $\delta=1$",
     ["GsimOT.Prop8.markerEnum", "GsimOT.Prop8.markerEnum_mono", "GsimOT.Prop8.Gr", "GsimOT.Prop8.Hr",
      "GsimOT.Prop8.lock_hyp_deg_G", "GsimOT.Prop8.lock_hyp_delta"]),
    ("Appendix~D.1", "26", r"All vertices of $G^0_r$, $H^0_r$ have degree $\le n_X$",
     ["GsimOT.Prop8.deg_bip_le", "GsimOT.Prop8.card_marker_le_card_core"]),
    ("Appendix~D.1", "26", r"$\chi_{G_r}(u)=0$, $\chi_{H_r}(u)=\mathbf 1_C$ (uses $r$ even)",
     ["GsimOT.Prop8.pat_zero", "GsimOT.Prop8.pat_ell"]),
    ("Appendix~D.1 (Fig.~6)", "26", r"Consecutive patterns differ in (at most) one coordinate",
     ["GsimOT.Prop8.change_clock_iff", "GsimOT.Prop8.change_tag_iff", "GsimOT.Prop8.change_bit_iff",
      "GsimOT.Prop8.ham_pat_succ_le_one"]),
    ("Proof of Lemma~27", "27", r"Shifts $\sigma_i$ along branch $i$",
     ["GsimOT.Prop8.node", "GsimOT.Prop8.shift", "GsimOT.Prop8.shiftPerm", "GsimOT.Prop8.sigma",
      "GsimOT.Prop8.sigmaExt"]),
    ("Proof of Lemma~27", "27", r"$Q_r=\frac1r\sum_i P_{\sigma_i}$ (extended by the identity on $K$)",
     ["GsimOT.Prop8.Qr", "GsimOT.Prop8.Qr_isDS", "GsimOT.Prop8.QrExt"]),
    ("Proof of Lemma~27", "27", r"Cost of supported core pairs = Hamming distance of patterns",
     ["GsimOT.Prop8.localCost_sigma_core", "GsimOT.Prop8.ham_shift_le_one"]),
    ("Proof of Lemma~27", "27", r"Cost at a marker = mass of changes: clocks $1$, tags $2/r$, bits $1$",
     ["GsimOT.Prop8.localCost_sigma_marker", "GsimOT.Prop8.nchg_clock_le", "GsimOT.Prop8.nchg_tag_le",
      "GsimOT.Prop8.nchg_bit_le", "GsimOT.Prop8.sum_nchg_le"]),
    ("Lemma~27 ($\\le$)", "27", r"$C_1(Q_r)\le 1$ (computed in $(G^0_r,H^0_r)$ via Lemma~22 (2))",
     ["GsimOT.Prop8.costOne_Qr_base_le_one", "GsimOT.Prop8.costOne_Qr_le_one"]),
    ("Lemma~27", "27", r"$d_1^{\mathrm{OT}}(G_r,H_r)=1$ ($\ge$ by Lemma~29, since $G_r\not\cong H_r$)",
     ["GsimOT.Prop8.lemma27"]),
    ("Lemma~28", "27", r"$d_1(G_r,H_r)\ge r$", ["GsimOT.Prop8.lemma28", "GsimOT.Prop8.lemma28_dOne"]),
    ("Proof of Lemma~28", "27", r"$C_1(\pi)<r\Rightarrow\pi$ fixes the markers and permutes $X$ (Lemma~22 (1) with $\tau=r$); $L_\pi(x,\pi(x))$ is the Hamming distance of the patterns (used as $\ge$)",
     ["GsimOT.Prop8.lemma28"]),
    ("Proof of Lemma~28", "27", r"Walk $u,\pi(u),\pi^2(u),\dots$ and its pattern sequence $x_0,\dots,x_s$",
     ["GsimOT.Prop8.lemma28"]),
    ("Proof of Lemma~28", "27", r"Clock level $c(x)$; consecutive clock levels differ by $<r$",
     ["GsimOT.Prop8.clockLevel", "GsimOT.Prop8.clockLevel_le_add_ham"]),
    ("Proof of Lemma~28", "27", r"Middle clock level $\Rightarrow$ all tags of the branch on; patterns on different branches differ in $\ge 2r$ markers (the formalisation uses $\ge r$)",
     ["GsimOT.Prop8.pat_tag_of_middle", "GsimOT.Prop8.ham_ge_of_middle_ne"]),
    ("Proof of Lemma~28", "27", r"$c(x_{\iota_j-1})\in((j-1)r,jr)\Rightarrow$ time in block $j$, bit value $j\bmod 2$",
     ["GsimOT.Prop8.div_eq_of_clockLevel", "GsimOT.Prop8.pat_bit_self"]),
    ("Proof of Lemma~28", "27", r"$\alpha,\beta,\iota_j$; the bit sequence alternates $r$ times; $L_\pi(b_i,b_i)\ge r$",
     ["GsimOT.Prop8.walk_bits", "GsimOT.Prop8.card_changes_step", "GsimOT.Prop8.lemma28"]),
    ("Proof of Prop.~8", "27--28", r"$C_1(\sigma_1)\le r$ (computed in $(G^0_r,H^0_r)$ via Lemma~22 (2))",
     ["GsimOT.Prop8.costOne_sigma_base_le", "GsimOT.Prop8.costOneBij_sigmaExt_le", "GsimOT.Prop8.nchg_le"]),
    ("Proof of Prop.~8", "28", r"$d_1(G_r,H_r)=r$", ["GsimOT.Prop8.dOne_Gr_Hr"]),
    ("Proof of Prop.~8", "28", r"$|V(G_r)|=5r^3+10r^2-r+4=\Theta(r^3)$",
     ["GsimOT.Prop8.card_Vr", "GsimOT.Prop8.card_Vr_bounds"]),
]

THM9_ROWS = [
    ("Theorem~9", "9", r"$\delta_1(G,H)\le 15\sqrt{\delta_1^{\mathrm{OT}}(G,H)\ln(4/\delta_1^{\mathrm{OT}}(G,H))}$",
     ["GsimOT.theorem9"]),
    (r"Theorem~2 ($\delta_1$ part)", "3", r"$\delta_1\le15\sqrt{\delta_1^{\mathrm{OT}}\ln(4/\delta_1^{\mathrm{OT}})}$ (Thm.~2 follows from Thms.~6, 9, 11, 14)",
     ["GsimOT.theorem9"]),
    ("after Thm.~9", "9", r"Theorem~9 yields $\delta_1\le C_\alpha(\delta_1^{\mathrm{OT}})^\alpha$ for every $\alpha<1/2$",
     ["GsimOT.theorem9_power", "GsimOT.sqrt_mul_log_le_rpow"]),
    ("Proof of Thm.~9", "30", r"Same bound with $f=C_1(Q)/n$ for every $Q\in\mathrm{DS}(V,W)$",
     ["GsimOT.theorem9_of_isDS"]),
    ("Appendix~D.2, Eq.~(18)", "28", r"Reference bijection $\sigma$ with graph in $\mathrm{supp}(Q)$",
     ["GsimOT.exists_bij_subset_supp"]),
    ("Appendix~D.2, Lemma~29", "28", r"$\rho_H$ and Lemma~29 (shared, see Common)",
     ["GsimOT.rho", "GsimOT.lemma29_rho_le", "GsimOT.lemma29_iso", "GsimOT.lemma29_dOne_eq_zero"]),
    ("Appendix~D.2", "28", r"Error $\Phi_v(M)=\sum_{(v',w')\in M}|A_G(v,v')-A_H(\sigma(v),w')|$", ["GsimOT.errAt"]),
    ("Lemma~30 [CVZ11]", "29", r"Dependent rounding with tail bound~(19) --- \textbf{explicit hypothesis}",
     ["GsimOT.CVZRounding", "GsimOT.IsMatching"]),
    ("Lemma~31", "29", r"Matching $M\subseteq\mathrm{supp}(Q)$ with $n-|M|\le2\gamma n$, $\Phi_v(M)\le 2L+10\ln(4n)/\gamma$",
     ["GsimOT.lemma31", "GsimOT.IsMatching.card_le"]),
    ("Proposition~32", "29", r"$d_1\le 2L+10\ln(4n)/\gamma+2\gamma n+n/\ell+2\ell L$",
     ["GsimOT.proposition32"]),
    ("Proof of Prop.~32", "29--30", r"Rounding step for a given matching (deterministic part)",
     ["GsimOT.prop38_of_matching"]),
    ("Proof of Prop.~32", "29", r"Partial injective map $\mu$; walks $v\to\mu(v)$",
     ["GsimOT.PathCutting.iter", "GsimOT.PathCutting.PInj", "GsimOT.PathCutting.NonCycle"]),
    ("Proof of Prop.~32", "29", r"Paths are finite and positions along paths are well defined",
     ["GsimOT.PathCutting.lt_card_of_iter", "GsimOT.PathCutting.depth", "GsimOT.PathCutting.depth_step"]),
    ("Proof of Prop.~32", "29", r"Cut every path into blocks of $\ell$ vertices; at most $n/\ell$ cuts",
     ["GsimOT.PathCutting.cutSet", "GsimOT.PathCutting.cutMap", "GsimOT.PathCutting.card_cutSet_mul_le",
      "GsimOT.PathCutting.iter_cutMap_eq_none"]),
    ("Proof of Prop.~32", "29", r"Close every block to a cycle; permutation $\tau$",
     ["GsimOT.PathCutting.exists_perm_close"]),
    ("Proof of Prop.~32", "29", r"$\tau$ retains $\mu$ outside $\le m+n/\ell$ closing edges; closing edges span $<\ell$ steps",
     ["GsimOT.PathCutting.exists_perm_of_partialInj"]),
    ("Proof of Prop.~32", "29--30", r"$\rho_H(\sigma(v),\pi(v))\le 2\ell L$ and $L_{P_\pi}(v,\pi(v))\le\Phi_v(M)+m+n/\ell+2\ell L$",
     ["GsimOT.prop38_of_matching"]),
    ("Proof of Thm.~9", "30", r"$L<1\Rightarrow G\cong H$ by Lemma~29, i.e.\ $\delta_1=0$", ["GsimOT.lemma29_dOne_eq_zero"]),
    ("Proof of Thm.~9", "30", r"Trivial bound $d_1\le n$ (case $\gamma^*>1/2$)", ["GsimOT.dOne_le_card"]),
    ("Proof of Thm.~9", "30", r"$x\mapsto\ln(4x)/x$ is decreasing for $x\ge1$", ["GsimOT.log_four_mul_div_antitone"]),
    ("Proof of Thm.~9", "30", r"Eq.~(20) and normalisation: $b\le 4f+2\sqrt{2f}+4\sqrt5\sqrt{f\ln(4/f)}$",
     ["GsimOT.theorem9_of_isDS"]),
    ("Proof of Thm.~9", "30", r"Final numerical estimate $\frac{b}{\sqrt{fh}}\le\frac{4+2\sqrt2}{\sqrt{\ln4}}+4\sqrt5<15$", ["GsimOT.final_estimate"]),
]

COMMON_NOTES = [
    r"The paper defines $C_1(Q)$ as the operator $1\to1$-norm of $B_{1\to1}(G,H,Q)$ and gives the "
    r"formula $C_1(Q)=\max_{(v,w)\in\mathrm{supp}(Q)}L_Q(v,w)$ (Section~2, p.~5, l.~184--189; Eq.~(7), p.~14). The formalisation takes "
    r"this formula as the definition of \lean{costOne} and proves the identity (\lean{opNorm_Bpq_one_one_eq_costOne}).",
    r"$d_1^{\mathrm{OT}}$, $d^{\mathrm{OT}}_{\mathrm{ed}}$, $d^{\mathrm{OT}}_\square$, $d^{\mathrm{OT}}_{p\to q}$ and "
    r"$\delta^{\mathrm{OT}}_{p\to q}$ are defined as \emph{infima}. The paper takes minima and argues that they are attained "
    r"(Appendix~A, pp.~14--15, l.~503--510). This is formalised for the operator norms (\lean{exists_deltaOTPQ_eq}, "
    r"\lean{exists_dOT_eq}, following the paper's lower-semicontinuity argument; used by Claim~20) and for the edit "
    r"distance (\lean{exists_dOTEdit_eq}, used by Theorem~15). For bijections the minimum over the finite set "
    r"$\mathrm{Bij}(V,W)$ is the infimum.",
    r"Normalisation: for graphs of the same order $n$, $\delta_\diamondsuit=d_\diamondsuit/s(n)$ and "
    r"$\delta^{\mathrm{OT}}_\diamondsuit=d^{\mathrm{OT}}_\diamondsuit/s(n)$ with $s(n)=n^2$ for the edit and the cut distance "
    r"(p.~1, l.~24--27) and $s(n)=n^{\kappa_{p\to q}}$, $\kappa_{p\to q}=1/q+1-1/p$, for $\|\cdot\|_{p\to q}$ (p.~3, l.~88--90; "
    r"Appendix~B, p.~15, l.~513--514), so $s(n)=n$ for $\|\cdot\|_1$. In Lean, \lean{deltaPQ} multiplies $d_{p\to q}$ by "
    r"$n^{-\kappa}$, the other normalised distances divide by $n$ or $n^2$, and \lean{deltaOTPQ_eq_dOT} proves "
    r"$\delta^{\mathrm{OT}}_{p\to q}=n^{-\kappa}d^{\mathrm{OT}}_{p\to q}$.",
    r"Lemma~22 is stated in the paper for $\diamondsuit\in\{\mathrm{ed},1\}$; both cases are formalised, "
    r"$\diamondsuit=1$ in \texttt{Lemma22\_LockingMarkers.lean} and $\diamondsuit=\mathrm{ed}$ in "
    r"\texttt{Lemma22\_LockingMarkersEdit.lean}. In Lean, the clique vertex $y_{i+1}$ is \texttt{Sum.inr i} and the "
    r"marker index $j$ of the paper is \texttt{j.val + 1}.",
    r"Lemma~29 is proved in the paper for an optimal $Q$ and $L=d_1^{\mathrm{OT}}(G,H)$. Its proof only uses "
    r"that all supported local costs of $Q$ are at most $L$, which is how it is stated in Lean. "
    r"It is shared by Proposition~8 (via Lemma~27) and Theorem~9.",
    r"Eq.~(3): \lean{exists_birkhoff_decomposition} sums over all permutations with weights $\ge0$; "
    r"\lean{exists_birkhoff_decomposition_pos} is the exact statement with $\lambda_i>0$.",
]

PROP8_NOTES = [
    r"Proposition~8 states $\Theta(r^3)$ vertices. The formalisation proves $r^3\le|V(G_r)|\le19r^3$ and, more precisely, "
    r"$|V(G_r)|=5r^3+10r^2-r+4$ (\lean{card_Vr}).",
    r"Indices are 0-based in Lean: \texttt{Marker.clock j h} is $c_{j+1,h+1}$, \texttt{Marker.tag i h} is "
    r"$t_{i+1,h+1}$, \texttt{Marker.bit i} is $b_{i+1}$ and \texttt{Core.v i k} is $v_{i+1,k+1}$.",
    r"Adjacency is defined through the pattern \lean{pat} $r\,i\,t$ of branch $i$ at time $t\in[0,\ell]$, which "
    r"is exactly the table of Appendix~D.1 (p.~26, l.~800) with $k$ replaced by $t$. Thus $\chi(v_{i,k})=\mathtt{pat}\,i\,k$, "
    r"$\chi_{G_r}(u)=\mathtt{pat}\,i\,0=0$ and $\chi_{H_r}(u)=\mathtt{pat}\,i\,\ell=\mathbf 1_C$.",
    r"The proof of Lemma~27 obtains $d_1^{\mathrm{OT}}(G_r,H_r)\ge1$ from Lemma~29 since $G_r\not\cong H_r$ "
    r"(p.~27, l.~837). The formalisation derives $G_r\not\cong H_r$ from Lemma~28: every bijection has cost "
    r"$\ge r>0$, while an isomorphism would have cost $0$. (The proof idea, p.~8, l.~282--283, obtains the "
    r"equality from Observation~21 instead: $u$ is isolated in $G_r$ but $H_r$ has no isolated vertex.)",
    r"In the proof of Lemma~27 (p.~27, l.~836--837) the paper computes the local costs at clock markers, tags and bits as exactly "
    r"$1$, $2/r$ and $1$. The formalisation proves the upper bounds $1$, $2/r$ and $1$, which are all that is "
    r"needed for $C_1(Q_r)\le1$.",
    r"Proof of Proposition~8: for $d_1(G_r,H_r)\le r$ the formalisation shows that \emph{every} local cost of "
    r"$\sigma_1$ is at most $r$ (core pairs $\le1$, clocks $\le1$, tags $\le2$, bits $\le r$), which is the content "
    r"of ``its local costs can be computed \dots\ as in the proof of Lemma~27''.",
    r"Proof of Lemma~28: the walk is formalised via the permutation $P$ of the core induced by $\pi$ and its "
    r"orbit $u,P(u),\dots,P^{s}(u)=u$, with $s$ the least positive period. The pattern sequence is "
    r"$x_\iota=\chi_{G_r}(P^\iota(u))$ for $\iota<s$ and $x_s=\chi_{H_r}(u)$, as in the paper. The indices "
    r"$\alpha,\beta,\iota_j$ are defined exactly as in the paper (via \texttt{Nat.find} / "
    r"\texttt{Nat.findGreatest}). For patterns on different branches the formalisation only uses Hamming "
    r"distance $\ge r$ (the paper notes $\ge2r$), which suffices. At a core vertex $x$ it only uses that "
    r"$L_\pi(x,\pi(x))$ is at least the Hamming distance of the patterns (the paper: equal to it, p.~27, "
    r"l.~840--841).",
    r"The remark after Theorem~9 (p.~9, l.~318--320): since $\delta_1(G_r,H_r)=r/n$, $\delta_1^{\mathrm{OT}}(G_r,H_r)=1/n$ and "
    r"$n=|V(G_r)|\le19r^3$, no bound $\delta_1\le C(\delta_1^{\mathrm{OT}})^\alpha$ with $\alpha>2/3$ holds "
    r"(\lean{no_power_bound}). The exact asymptotics $\Theta(r^{-3})$, $\Theta(r^{-2})$ are not stated separately.",
]

THM9_NOTES = [
    r"\textbf{Lemma~30 is a hypothesis.} Lemma~30 is the dependent rounding theorem of Chekuri, Vondr\'ak "
    r"and Zenklusen [CVZ11, Thm.~1.1], which the paper cites without proof. It is stated as the proposition "
    r"\lean{CVZRounding} and appears as the explicit hypothesis \texttt{hCVZ} of \lean{theorem9} (no Lean "
    r"\texttt{axiom} is introduced). It is specialised to doubly stochastic $Q$ (a point of the perfect "
    r"matching polytope), which is the only case used, and a ``random matching'' is a finitely supported "
    r"probability distribution on subsets of $V\times W$. Apart from this specialisation, the statement is the "
    r"paper's (p.~29, l.~895--898).",
    r"Final estimate of the proof of Theorem~9 (p.~30, l.~945--947): the paper's bound "
    r"$\frac{b}{\sqrt{fh}}\le4\sqrt{f/h}+\frac{2\sqrt2}{\sqrt h}+4\sqrt5\le\frac{4+2\sqrt2}{\sqrt{\ln4}}+4\sqrt5<15$ "
    r"(using $f\le1$ and $h\ge\ln4$; the constant is $\approx14.74$) is formalised as \lean{final_estimate}.",
    r"In the proof of Theorem~9, the quantity $\sqrt{n/(2L)}$ is called $s$ in Lean, so $2\sqrt{2nL}=4Ls$.",
    r"Optimal vs.\ arbitrary $Q$: Lemmas~29, 31 and Proposition~32 are stated for any $Q\in\mathrm{DS}(V,W)$ "
    r"whose supported local costs are at most $L$. The paper takes $Q$ optimal and $L=d_1^{\mathrm{OT}}$. "
    r"Theorem~9 is first proved with $f=C_1(Q)/n$ for every $Q$ (\lean{theorem9_of_isDS}), and the "
    r"statement for $\delta_1^{\mathrm{OT}}$ (an infimum in Lean) follows by continuity of "
    r"$f\mapsto15\sqrt{f\ln(4/f)}$ at $f>0$. The case $d_1^{\mathrm{OT}}<1$ is the isomorphic case "
    r"(Lemma~29). The paper distinguishes $L=0$ and $L>0$ and then uses $L\ge1$; the Lean proof splits "
    r"directly into $L<1$ and $L\ge1$.",
    r"Convention $f=0$: in Lean $\ln0=0$ and $4/0=0$, so $15\sqrt{f\ln(4/f)}=0$ for $f=0$, matching the "
    r"paper's convention.",
    r"Proof of Proposition~32: the path decomposition is formalised in two steps, exactly as described: "
    r"(i)~the outgoing edge of every vertex at position $p\equiv\ell-1\pmod\ell$ on a path is removed (this cuts "
    r"every path into consecutive blocks of $\ell$ vertices plus a final shorter block), and (ii)~every block is "
    r"closed to a cycle. The bound ``number of closing edges $\le m+n/\ell$'' is proved by counting the "
    r"$\le n/\ell$ cut positions (each owns the $\ell$ vertices of its block) plus the $m$ path ends. The paper "
    r"counts $\sum_j\lceil p_j/\ell\rceil\le m+n/\ell$ instead; both give the same bound.",
    r"In Proposition~32 the bound $\rho_H(\sigma(v_k),\sigma(v_1))\le2(k-1)L$ is used in the weaker form "
    r"$\le2\ell L$, as in the paper's statement of the claim.",
    r"Lemma~31 handles the degenerate case $n=0$ separately (the paper implicitly has $n\ge1$ since $L>0$).",
    r"The remark after Theorem~9 (p.~9, l.~320) that Theorem~9 yields $\delta_1\le C_\alpha(\delta_1^{\mathrm{OT}})^\alpha$ "
    r"for every $\alpha<1/2$ is \lean{theorem9_power} (with $C_\alpha=15\sqrt{4^{\varepsilon}/\varepsilon}$, "
    r"$\varepsilon=1-2\alpha$), derived from Theorem~9 via $\ln x\le x^{\varepsilon}/\varepsilon$ "
    r"(\lean{sqrt_mul_log_le_rpow}).",
]



# Edit distance (Theorem 7, Theorem 16), Eq. (8) and the shared notions of Section 4

EDIT_ROWS = [
    ("Section~1, Section~2", "2, 5",
     r"$C_{\mathrm{ed}}(Q)=\sum_{v,w,v',w'}|D(v,w,v',w')|\,Q(v,w)\,Q(v',w')$ and "
     r"$C_{\mathrm{ed}}(\pi)=C_{\mathrm{ed}}(P_\pi)=\|A_G^\pi-A_H\|_{\mathrm{ed}}$",
     ["GsimOT.costEdit", "GsimOT.costEditBij", "GsimOT.costEditBij_eq"]),
    ("Section~1, Eq.~(1), Section~2, Appendix~A", "2, 5, 14--15",
     r"$d_{\mathrm{ed}}=\min_\pi C_{\mathrm{ed}}(\pi)$ and $d^{\mathrm{OT}}_{\mathrm{ed}}=\min_{Q\in\mathrm{DS}(V,W)}"
     r"C_{\mathrm{ed}}(Q)$ (infimum, attained); $d^{\mathrm{OT}}_{\mathrm{ed}}\le d_{\mathrm{ed}}$",
     ["GsimOT.dEdit", "GsimOT.dOTEdit", "GsimOT.exists_dOTEdit_eq", "GsimOT.dOTEdit_le_dEdit"]),
    ("Section~1, Section~2", "1--2, 5",
     r"$\delta_{\mathrm{ed}}=n^{-2}d_{\mathrm{ed}}$, $\delta^{\mathrm{OT}}_{\mathrm{ed}}=n^{-2}d^{\mathrm{OT}}_{\mathrm{ed}}$ "
     r"(scaling by $1/n^2$)",
     ["GsimOT.deltaEdit", "GsimOT.deltaOTEdit"]),
    ("Section~1, Section~2, Appendix~A", "2, 5, 14", r"$C_{\mathrm{ed}}(Q)=\|B(G,H,Q)\|_{\mathrm{ed}}$ for $Q\ge0$ (entrywise $1$-norm $\|\cdot\|_{\mathrm{ed}}=\|\cdot\|_{(1)}$)",
     ["GsimOT.entrywiseNorm", "GsimOT.costEdit_eq_entrywiseNorm_B"]),
    ("Section~2, Eq.~(3)", "5",
     r"Birkhoff--von Neumann: $Q=\sum_i\lambda_iP_{\pi_i}$ with $\lambda_i>0$, $\sum_i\lambda_i=1$ (also: over all "
     r"$\sigma\in\mathrm{Perm}(V)$ with $\lambda\ge0$); conversely every such combination is in $\mathrm{DS}(V,W)$",
     ["GsimOT.exists_birkhoff_decomposition_pos", "GsimOT.exists_birkhoff_decomposition", "GsimOT.isDS_of_decomposition"]),
]

EQ7_ROWS = [
    ("Section~2, Eq.~(7)", "5, 14",
     r"$\|B_{1\to1}(G,H,Q)\|_{1\to1}=C_1(Q)=\max_{(v,w)\in\mathrm{supp}(Q)}L_Q(v,w)$ for $Q\in\mathrm{DS}(V,W)$; "
     r"hence $d^{\mathrm{OT}}_{1\to1}=d^{\mathrm{OT}}_1$",
     ["GsimOT.opNorm_Bpq_one_one_eq_costOne", "GsimOT.dOT_one_one_eq_dOTOne"]),
]

DS_ROWS = [
    ("--", "--",
     r"Sums over $V\times W$ against $Q\in\mathrm{DS}(V,W)$; partial sums $Q(S,T)$ and their bounds; "
     r"$\mathrm{DS}(V,W)$ is compact; bounds for infima over $\mathrm{DS}(V,W)$",
     ["GsimOT.IsDS.sum_mul_fst", "GsimOT.mass", "GsimOT.card_mul_le_of_lt_mass", "GsimOT.isCompact_setOf_isDS",
      "GsimOT.iInf_isDS_le", "GsimOT.le_iInf_isDS"]),
]

GADGET_ROWS = [
    ("Proofs of Thms.~15--17", "50--57",
     r"Disjoint unions of paths ($F_1$) and of cycles; their degrees and edge counts",
     ["GsimOT.Hardness.pathUnion", "GsimOT.Hardness.cycleUnion", "GsimOT.Hardness.sum_adj_pathUnion",
      "GsimOT.Hardness.deg_cycleUnion"]),
    ("Proof of Thm.~15", "50",
     r"Three-Partition instances $(A,a_1,\dots,a_{3m})$; the step of adding $3$ to each $a_i$ and $9$ to $A$",
     ["GsimOT.Hardness.ThreePartition", "GsimOT.Hardness.ThreePartition.IsYes",
      "GsimOT.Hardness.ThreePartition.shift", "GsimOT.Hardness.ThreePartition.shift_isYes_iff"]),
    ("Proofs of Thms.~15--17", "50--56",
     r"A solution gives a bijection mapping each path into one component; conversely a $Q\in\mathrm{DS}$ "
     r"mapping every path into a single component gives a solution (counting mass)",
     ["GsimOT.Hardness.ThreePartition.layoutEquiv", "GsimOT.Hardness.ThreePartition.isYes_of_isDS"]),
    ("Proofs of Thms.~17, 18", "54, 57", r"Attaching $\ell(b)$ leaves to every vertex $b$ of a base graph",
     ["GsimOT.Hardness.addLeaves"]),
]

LOCK_EDIT_ROWS = [
    (r"Lemma~22 (1), $\diamondsuit=\mathrm{ed}$", "21",
     r"$C_{\mathrm{ed}}(\pi)<\tau$ $\Rightarrow$ $\pi$ fixes all markers and $\pi(V)=V$; via "
     r"$C_1(\pi)\le C_{\mathrm{ed}}(\pi)$ and the case $\diamondsuit=1$",
     ["GsimOT.costOneBij_le_costEditBij", "GsimOT.lemma22_bij_edit"]),
    (r"Lemma~22 (2), $\diamondsuit=\mathrm{ed}$", "21",
     r"$Q(z_j,z_j)=1$ $\Rightarrow$ $C_{\mathrm{ed}}(Q')$ w.r.t.\ $(G',H')$ equals $C_{\mathrm{ed}}(Q)$ "
     r"w.r.t.\ $(G,H)$",
     ["GsimOT.lemma22_cost_edit"]),
]


# Observation 21 and Lemma 22, as used by Proposition 5.
LOCK_ROWS = ([row for row in COMMON_ROWS
              if row[0].startswith(("Observation~21", "Lemma~22 (construction)", "Lemma~22 (2)"))]
             + LOCK_EDIT_ROWS)

PROP5_ROWS = [
    ("Appendix~C.1 (construction, l.~677--687)", "21",
     r"Markers $z_0,\dots,z_{N-1}$; cores $S_G=\{v_0,v_2,\dots,v_{2N-2}\}$, $S_H=\{w_1,\dots,w_{2N-1}\}$ at "
     r"their positions in $\mathbb Z_{2N}$; distinct core vertices adjacent iff their positions sum to $0$ mod "
     r"$2N$; $z_r$ adjacent to the core vertices on $I_r=\{(r+s)\bmod 2N\mid s<N\}$",
     ["GsimOT.Prop5.Base", "GsimOT.Prop5.semicircle", "GsimOT.Prop5.mem_semicircle", "GsimOT.Prop5.posG",
      "GsimOT.Prop5.posH", "GsimOT.Prop5.coreGraph", "GsimOT.Prop5.Gp", "GsimOT.Prop5.Hp"]),
    ("Appendix~C.1 (construction, l.~692--694)", "22",
     r"For odd $N$: core edges $\{c,c'\}$ with $c+c'=N$ in $G'$ and with $c+c'+1=N$, $c\ne c'$ in $H'$; "
     r"$v_0$ and $w_N$ are isolated",
     ["GsimOT.Prop5.Gp_adj_inl_inl", "GsimOT.Prop5.Hp_adj_inl_inl"]),
    ("Appendix~C.1 (construction, l.~688--691)", "21--22",
     r"$G,H$ by Lemma~22, markers ordered by their degree in $G'$, $\Delta=N+1$, $\tau=4N-1$, $\delta=1$; "
     r"all degrees are at most $N+1$, and the degrees of $z_r$ in $G'$ and $H'$ differ by one",
     ["GsimOT.Prop5.markerEnum", "GsimOT.Prop5.markerEnum_mono", "GsimOT.Prop5.deg_Gp_le",
      "GsimOT.Prop5.deg_Hp_le", "GsimOT.Prop5.deg_Gp_inr", "GsimOT.Prop5.deg_Hp_inr",
      "GsimOT.Prop5.markerEnum_deg", "GsimOT.Prop5.mK", "GsimOT.Prop5.GN", "GsimOT.Prop5.HN"]),
    ("Lemma~23, Fig.~4 (l.~696--699, 703--706)", "22",
     r"$\ell(v_i,w_j)=\min_k|i-j+2kN|$; mapping $v_i$ to $w_j$ changes the adjacency to exactly "
     r"$\ell(v_i,w_j)$ markers",
     ["GsimOT.Prop5.cycDist", "GsimOT.Prop5.ell", "GsimOT.Prop5.card_semicircle_ne",
      "GsimOT.Prop5.sum_marker_inl", "GsimOT.Prop5.sum_marker_inr"]),
    ("Lemma~23 (l.~700--702)", "22",
     r"For compliant $Q$, the core-marker pairs contribute exactly $2\sum Q(v_i,w_j)\,\ell(v_i,w_j)$ to "
     r"$C_{\mathrm{ed}}(Q)$",
     ["GsimOT.Prop5.extMarkers", "GsimOT.Prop5.coreCost", "GsimOT.Prop5.costEdit_extMarkers",
      "GsimOT.Prop5.lemma23"]),
    ("Proof of Lemma~24 (l.~708--714)", "22",
     r"$\pi_\pm(v_i)=w_{i\pm1}$, $Q=\frac12(P_{\pi_-}+P_{\pi_+})$; $\ell(v_i,\pi_\pm(v_i))=1$",
     ["GsimOT.Prop5.predCore", "GsimOT.Prop5.avgPerm", "GsimOT.Prop5.Rwit", "GsimOT.Prop5.Qwit",
      "GsimOT.Prop5.ell_self", "GsimOT.Prop5.ell_predCore"]),
    ("Proof of Lemma~24, Fig.~5 (l.~715--724)", "22--23",
     r"Core-core pairs: the core edges are preserved iff one endpoint moves forward and the other backward, "
     r"except near $v_0$ and $w_N$; the Lean computes their cost as $\frac14(2(N-1)+2+2+2(N-1))=N$",
     ["GsimOT.Prop5.pres_eq", "GsimOT.Prop5.pres_id_id", "GsimOT.Prop5.pres_pred_pred",
      "GsimOT.Prop5.pres_id_pred", "GsimOT.Prop5.pres_pred_id", "GsimOT.Prop5.coreCost_avgPerm",
      "GsimOT.Prop5.coreCost_witness"]),
    ("Lemma~24 (l.~707, 725)", "22--23",
     r"$d^{\mathrm{OT}}_{\mathrm{ed}}(G,H)\le3N+1$, from $C_{\mathrm{ed}}(Q)=3N$ for the witness $Q$",
     ["GsimOT.Prop5.costEdit_witness", "GsimOT.Prop5.lemma24"]),
    ("Proof of Lemma~25 (l.~727--729)", "23",
     r"If $C_{\mathrm{ed}}(\pi)<\tau$, then $\pi$ fixes the markers and maps $S_G$ onto $S_H$ (Lemma~22); "
     r"the pairs involving the clique only add to the cost",
     ["GsimOT.lemma22_bij_edit", "GsimOT.Prop5.restrictInl", "GsimOT.Prop5.costEditBij_restrict",
      "GsimOT.Prop5.costEditBij_sumCongr"]),
    ("Proof of Lemma~25, Claim~26 (l.~729--742)", "23--24",
     r"Displacements $d_i\in\{-N+2,\dots,N\}$ with $\ell(v_i,\pi(v_i))=|d_i|$; "
     r"$\sum d_i\equiv N\pmod{2N}$, so $|\sum d_i|\ge N$",
     ["GsimOT.Prop5.disp", "GsimOT.Prop5.ell_eq_abs_disp", "GsimOT.Prop5.one_le_ell",
      "GsimOT.Prop5.sum_disp", "GsimOT.Prop5.sum_disp_ge"]),
    ("Claim~26 (l.~737--749)", "24",
     r"$U\ge N+2k$; preserved edges have $d_i+d_{i'}=0$",
     ["GsimOT.Prop5.Preserved", "GsimOT.Prop5.disp_add_disp_partner", "GsimOT.Prop5.claim26"]),
    ("Proof of Lemma~25 (l.~750--751)", "24",
     r"Both cores have $(N-1)/2$ edges; their ordered pairs contribute $2(N-1-2k)$",
     ["GsimOT.Prop5.sum_adj_Gp_core", "GsimOT.Prop5.sum_adj_Hp_core", "GsimOT.Prop5.mixCore",
      "GsimOT.Prop5.pres", "GsimOT.Prop5.mixCore_eq"]),
    ("Lemma~25 (l.~726, 753)", "23--24", r"$C_{\mathrm{ed}}(\pi)\ge4N-2$ for every $\pi$, i.e.\ "
     r"$d_{\mathrm{ed}}(G,H)\ge4N-2$",
     ["GsimOT.Prop5.lemma25_bij", "GsimOT.Prop5.lemma25"]),
    ("Proposition~5 (l.~221--222)", "6",
     r"$d_{\mathrm{ed}}(G,H)\ge4N-2$ and $d^{\mathrm{OT}}_{\mathrm{ed}}(G,H)\le3N+1$; in terms of costs: "
     r"$C_{\mathrm{ed}}(\pi)\ge4N-2$ for all $\pi$, $C_{\mathrm{ed}}(Q)\le3N+1$ for some $Q$",
     ["GsimOT.Prop5.proposition5_dEdit", "GsimOT.Prop5.proposition5"]),
    ("Proof of Proposition~5 (l.~754--758)", "24",
     r"$d_{\mathrm{ed}}\ge4N-2=(\frac43-\frac{10}{3(3N+1)})(3N+1)\ge(\frac43-\frac{10}{3(3N+1)})\,"
     r"d^{\mathrm{OT}}_{\mathrm{ed}}$; same normalisation; choose $N$ with $\frac{10}{3(3N+1)}\le\varepsilon$",
     ["GsimOT.Prop5.proposition5_delta_of_le"]),
    ("Proposition~5 (l.~222--223)", "6",
     r"For every $\varepsilon>0$ there is an $N$ with "
     r"$\delta_{\mathrm{ed}}(G,H)\ge(\frac43-\varepsilon)\,\delta^{\mathrm{OT}}_{\mathrm{ed}}(G,H)$",
     ["GsimOT.Prop5.proposition5_delta"]),
    ("Theorem~3 (1) (l.~124)", "4",
     r"For every $\varepsilon>0$ some $G,H$ have $\delta_{\mathrm{ed}}\ge(\frac43-\varepsilon)\,"
     r"\delta^{\mathrm{OT}}_{\mathrm{ed}}$",
     ["GsimOT.Prop5.theorem3_item1"]),
]

PROP5_NOTES = [
    r"Proposition~5 states $d_{\mathrm{ed}}(G,H)\ge4N-2$ and $d^{\mathrm{OT}}_{\mathrm{ed}}(G,H)\le3N+1$ "
    r"(\lean{proposition5_dEdit}); \lean{proposition5} is the form with "
    r"the explicit witness $Q$. \lean{proposition5_delta_of_le} is the computation of the proof for every odd "
    r"$N\ge3$ with $\frac{10}{3(3N+1)}\le\varepsilon$.",
    r"The common vertex set of $G'$ and $H'$ is \lean{Base N} $=$ \lean{Fin N} $\oplus$ \lean{Fin N}: "
    r"\lean{Sum.inl c} is the core vertex $v_{2c}$ of $G'$ and $w_{2c+1}$ of $H'$ (the identification "
    r"$v_i\leftrightarrow w_{i+1}$ of the paper), \lean{Sum.inr r} is the marker $z_r$, and $\mathbb Z_{2N}$ is "
    r"$\{0,\dots,2N-1\}$. With this identification, $\pi_+$ is the identity on the core and $\pi_-$ maps the core "
    r"vertex $c$ to $c-1\bmod N$ (\lean{predCore}).",
    r"A compliant $Q$ is \lean{extendId (extMarkers R)}, with $R$ the restriction of $Q$ to the core vertices. "
    r"Lemma~23 is computed on $(G',H')$ (\lean{costEdit_extMarkers}) and transferred to $(G,H)$ by "
    r"Lemma~22~(2) (\lean{lemma23}).",
    r"Lemma~24: \lean{costEdit_witness} computes the cost of the witness, $C_{\mathrm{ed}}(Q)=3N$, and "
    r"\lean{lemma24} derives $d^{\mathrm{OT}}_{\mathrm{ed}}(G,H)\le3N+1$ from it.",
    r"Lemma~25: instead of replacing $\pi$ on the clique by the identity, the pairs involving the clique are "
    r"dropped from $C_{\mathrm{ed}}(\pi)$ (\lean{costEditBij_restrict}). Claim~26 is stated with $2k$, "
    r"the number of preserved ordered core edges (\lean{pres}), and $\sum_{v_i\in S}d_i=0$ is proved with the "
    r"involution $c\mapsto N-c$ on $S$.",
    r"Lemma~22 for $\diamondsuit=\mathrm{ed}$ is in \texttt{Common/Lemma22\_LockingMarkersEdit.lean}; its first "
    r"item follows from the case $\diamondsuit=1$, as $C_1(\pi)\le C_{\mathrm{ed}}(\pi)$. The parameters "
    r"$k=N$, $\Delta=N+1$, $\tau=4N-1$, $\delta=1$ are those of the paper (\lean{mK}, \lean{GN}).",
]

THM6_ROWS = [
    ("Eq.~(17) (l.~762--765)", "24",
     r"$C_{\mathrm{ed}}(R)=\|A_G\|_F^2+\|A_H\|_F^2-2\langle A_GR,RA_H\rangle_F$ for $R\in\mathrm{DS}(V,W)$, "
     r"from $|a-b|=a^2+b^2-2ab$ for $a,b\in\{0,1\}$",
     ["GsimOT.costEdit_eq_frob", "GsimOT.abs_disc_eq", "GsimOT.frob", "GsimOT.adjMul", "GsimOT.mulAdj"]),
    ("Proof of Thm.~6, first step (l.~767)", "24",
     r"$C_{\mathrm{ed}}(\pi)=\|A_G-P_\pi A_HP_\pi^\top\|_F^2$",
     ["GsimOT.costEditBij_eq_frob_conjMul", "GsimOT.conjMul", "GsimOT.conjMul_permMat"]),
    ("Proof of Thm.~6, step~(a) (l.~768)", "25",
     r"$\|A_G-PA_HP^\top\|_F=\|A_GP-PA_H\|_F$ (permutation invariance)",
     ["GsimOT.frob_conjMul_eq", "GsimOT.adjMul_permMat", "GsimOT.mulAdj_permMat"]),
    ("Proof of Thm.~6, step~(b) (l.~770)", "25", r"$\|X+Y\|_F^2\le2\|X\|_F^2+2\|Y\|_F^2$",
     ["GsimOT.frob_add_self_le"]),
    ("Proof of Thm.~6, steps~(c), (f) (l.~771, 774)", "25",
     r"$\|X-Y\|_F^2=\|X\|_F^2+\|Y\|_F^2-2\langle X,Y\rangle_F$",
     ["GsimOT.frob_sub_self", "GsimOT.frob_comm"]),
    ("Proof of Thm.~6, steps~(d), (g) (l.~772, 776)", "25",
     r"$\mathbb E[P]=Q$: $A_GQ=\sum_i\lambda_iA_GP_{\pi_i}$, $QA_H=\sum_i\lambda_iP_{\pi_i}A_H$, and "
     r"$\langle\cdot,\cdot\rangle_F$ is linear; $\|A_GP_\pi\|_F=\|A_G\|_F$, $\|P_\pi A_H\|_F=\|A_H\|_F$",
     ["GsimOT.adjMul_eq_sum", "GsimOT.mulAdj_eq_sum", "GsimOT.frob_eq_sum_left", "GsimOT.frob_eq_sum_right",
      "GsimOT.frob_adjMul_permMat", "GsimOT.frob_mulAdj_permMat"]),
    ("Theorem~6 (l.~245--246)", "7, 24--25",
     r"$\sum_i\lambda_iC_{\mathrm{ed}}(\pi_i)\le2\,C_{\mathrm{ed}}(Q)$ for $Q=\sum_i\lambda_iP_{\pi_i}$; the "
     r"proof is the chain (a)--(g) and Eq.~(17) of Appendix~C.2 (l.~767--777)",
     ["GsimOT.theorem6"]),
    ("Theorem~6 (``in particular'', l.~247, 783--785)", "7, 25",
     r"$d_{\mathrm{ed}}(G,H)\le2\,d^{\mathrm{OT}}_{\mathrm{ed}}(G,H)$ (in Lean for all $G,H$)",
     ["GsimOT.theorem6_dEdit"]),
    ("Theorem~2 (first bound, l.~119)", "3",
     r"$\delta_{\mathrm{ed}}(G,H)\le2\,\delta^{\mathrm{OT}}_{\mathrm{ed}}(G,H)$",
     ["GsimOT.theorem2_edit"]),
]

THM6_NOTES = [
    r"The formalisation follows the proof of Theorem~6 in Appendix~C.2. The expectation "
    r"$\mathbb E[f(\pi)]$ over the random bijection with $\Pr(\pi=\pi_i)=\lambda_i$ is the sum "
    r"$\sum_i\lambda_if(\pi_i)$, and the chain of l.~767--777 is a \texttt{calc} block with one step per line, "
    r"commented with the paper's line numbers and labels (a)--(g).",
    r"Matrices are functions $V\to W\to\mathbb R$, as in \texttt{Common/Basic.lean}: \lean{adjMul G R} is "
    r"$A_GR$, \lean{mulAdj H R} is $RA_H$, \lean{conjMul H R} is $RA_HR^\top$ and \lean{frob X Y} is "
    r"$\langle X,Y\rangle_F$, so $\|X\|_F^2$ is \lean{frob X X}.",
    r"A decomposition is given by weights $\lambda_i\ge0$ with $\sum_i\lambda_i=1$ over any finite index type; "
    r"only these are assumed, so \lean{theorem6} applies to every decomposition as in Eq.~(3).",
    r"The first step of the chain (l.~767) holds since the entries of "
    r"$A_G$ and $A_H$ are in $\{0,1\}$ (\lean{costEditBij_eq_frob_conjMul}).",
    r"Example~7 (p.~7) and the remark at the end of Appendix~C.2 (p.~25, arbitrary matrices via thresholds) are "
    r"not formalised.",
]

HARDNESS_NOTE = (
    r"Only the correctness of the reduction is formalised: for the constructed graphs, YES-instances have a "
    r"small and NO-instances a large distance. The complexity side (polynomial running time, NP-hardness of "
    r"Three-Partition, H\aa{}stad's bound for MaxCut) is not formalised. The results of Section~4 and their "
    r"shared gadgets are in the namespace \lean{GsimOT.Hardness}.")

THM15_ROWS = [
    ("Proof of Thm.~15, l.~1600--1602", "51",
     r"$\|B(F_1,F_2,Q)\|_{(1)}=2|E(F_2)|-2|E(F_1)|+2\,\mathrm{lost}(Q)=4m+2\,\mathrm{lost}(Q)$ for "
     r"$Q\in\mathrm{DS}$, where $\mathrm{lost}(Q)\ge0$ is the edge mass of $F_1$ mapped to non-edges of $F_2$ "
     r"(the paper's $\|A^\pi_{F_1'}-A_{F_2'}\|_{(1)}=4mk^2+4b$ for blowups)",
     ["GsimOT.Hardness.lost", "GsimOT.Hardness.entrywiseNorm_B_eq",
      "GsimOT.Hardness.ThreePartition.sum_adj_sub_sum_adj"]),
    ("Proof of Thm.~15, l.~1611--1616", "51",
     r"If $\mathrm{lost}(Q)=0$, no edge of $F_1$ is mapped to a non-edge of $F_2$, so every path of $F_1$ "
     r"goes into one path of $F_2$ (the paper's $j(\cdot)$ is constant on paths)",
     ["GsimOT.Hardness.mul_eq_zero_of_lost_eq_zero"]),
    ("Proof of Thm.~15, l.~1588--1597", "50--51",
     r"YES-instances: the layout bijection maps edges to edges, so $\mathrm{lost}=0$ and the cost is $4m$",
     ["GsimOT.Hardness.lost_permMat"]),
    (r"Theorem~15, Theorem~4\,(1)", "4, 12, 50--51",
     r"$d^{\mathrm{OT}}_{\mathrm{ed}}(F_1,F_2)\le4m$ if and only if the Three-Partition instance is a YES-instance",
     ["GsimOT.Hardness.ThreePartition.dOTEdit_le_iff"]),
    ("Theorem~15 (arbitrary instances), l.~1586--1587", "50",
     r"The same after adding $3$ to each $a_i$ and $9$ to $A$",
     ["GsimOT.Hardness.ThreePartition.dOTEdit_shift_le_iff"]),
]

THM15_NOTES = [
    HARDNESS_NOTE,
    r"$d^{\mathrm{OT}}_{\mathrm{ed}}$ is \lean{GsimOT.dOTEdit}, the definition Theorem~6 uses. The paper argues with "
    r"blowups via $d^{\mathrm{OT}}_{\mathrm{ed}}=d^{\bullet}_{\mathrm{ed}}$, cited from [Gro25, Theorem~3.10] "
    r"(p.~50, l.~1585--1586). The formalisation works directly "
    r"with doubly stochastic matrices: the same edge count with $b/k^2$ replaced by $\mathrm{lost}(Q)/2$, where "
    r"the paper's approximation by $\gamma=1/(2mA)$ becomes exact because the minimum is attained "
    r"(\lean{GsimOT.exists_dOTEdit_eq}). So nothing is cited.",
    r"The formalisation assumes $a_i\ge2$ (\lean{GsimOT.Hardness.ThreePartition.dOTEdit_le_iff}); the shifted "
    r"version \lean{GsimOT.Hardness.ThreePartition.dOTEdit_shift_le_iff} holds for every instance.",
    r"Proposition~57 (p.~57; membership in NP, exact blowup sizes) is not formalised.",
]

THM16_ROWS = [
    ("Proof of Thm.~16, l.~1661", "52",
     r"$L_Q(v,w)=\deg(v)+\deg(w)-2\,Q(N(v),N(w))$ for $Q\in\mathrm{DS}$ (the fractional form of the "
     r"mismatch count $(2k-\ell)+(dk-\ell)$)",
     ["GsimOT.Hardness.nbrMass", "GsimOT.Hardness.localCost_eq"]),
    ("Theorem~16 (YES), l.~1626--1632", "12, 51", r"YES-instances: $d^{\mathrm{OT}}_1(F_1,F_2)\le1$",
     ["GsimOT.Hardness.ThreePartition.dOTOne_le_of_isYes"]),
    ("Theorem~16 (NO), Eq.~(44), Cases~1 and~2, l.~1633--1666", "12, 52",
     r"NO-instances: $d^{\mathrm{OT}}_1(F_1,F_2)\ge2$",
     ["GsimOT.Hardness.ThreePartition.two_le_dOTOne_of_not_isYes"]),
    ("Theorem~16 (arbitrary instances), l.~1622--1624", "51",
     r"Both bounds after adding $3$ to each $a_i$ and $9$ to $A$; this is the case $p=1$ of Theorem~4\,(2)",
     ["GsimOT.Hardness.ThreePartition.dOTOne_shift_gap"]),
]

THM16_NOTES = [
    HARDNESS_NOTE,
    r"$d^{\mathrm{OT}}_1$ is \lean{GsimOT.dOTOne}, the definition of Proposition~8 and Theorem~9. By Eq.~(7) "
    r"(\lean{GsimOT.dOT_one_one_eq_dOTOne}) it equals the operator-norm distance $d^{\mathrm{OT}}_{1\to1}$. The paper "
    r"bounds $d^{\bullet}_1$ via permutations of blowups and then applies Theorem~1 (p.~52, l.~1667). The proof works "
    r"directly with doubly stochastic matrices, with the same case distinction: a row of $Q$ split over two "
    r"cycles (Case~2) or adjacent vertices sent to different cycles (Case~1) gives a local cost $\ge2$, and "
    r"otherwise the counting after Eq.~(44) gives a solution.",
    r"The formalisation assumes $a_i\ge2$ for the YES-direction "
    r"(\lean{GsimOT.Hardness.ThreePartition.dOTOne_le_of_isYes}); the NO-direction has no hypothesis on the $a_i$.",
]

THM17_ROWS = [
    ("Eq.~(45)", "53",
     r"The aggregated matrix $A^Q_{G,H}=A_G-QA_HQ^\top$, $A^Q_{G,H}(v,v')=\sum_{w,w'}Q(v,w)D(v,w,v',w')Q(v',w')$",
     ["GsimOT.Hardness.aggMatrix", "GsimOT.Hardness.aggMatrix_isSymm"]),
    ("Lemma~53", "53--54",
     r"$\|A^Q_{G,H}\|_p\le\|B_p(G,H,Q)\|_p$ for all $Q\in\mathrm{DS}(V,W)$ and $1\le p\le\infty$",
     ["GsimOT.Hardness.opNorm_aggMatrix_le"]),
    ("Corollary~54", "54",
     r"If a column of $A^Q_{G,H}$ has $k$ entries of absolute value $\ge\varepsilon$, then "
     r"$\|A^Q_{G,H}\|_p\ge k^{b(p)}\varepsilon$, so $\|B_p(G,H,Q)\|_p\ge k^{b(p)}\varepsilon$ by Lemma~53; "
     r"hence $\|B_p(G,H,Q)\|_p>c$ if $k>(c/\varepsilon)^{1/b(p)}$",
     ["GsimOT.Hardness.rpow_bExp_mul_le_opNorm", "GsimOT.Hardness.rpow_bExp_mul_le_opNorm_Bpq",
      "GsimOT.Hardness.lt_opNorm_Bpq"]),
    ("Proof of Thm.~17: $G$, $H$", "54",
     r"Paths on $a_i$ vertices and $m$ cycles on $A$ vertices, with $M$ leaves attached to every vertex",
     ["GsimOT.Hardness.ThreePartition.graphG", "GsimOT.Hardness.ThreePartition.graphH"]),
    ("Proof of Thm.~17: observation", "54",
     r"If $xx'\in E(G)$, then $A^Q_{G,H}(x,x')=\sum_{yy'\notin E(H)}Q(x,y)Q(x',y')$ (and the analogue for non-edges)",
     ["GsimOT.Hardness.aggMatrix_of_adj", "GsimOT.Hardness.aggMatrix_of_not_adj"]),
    ("Claim~55", "55",
     r"If $Q(v,L_H)\ge\eta>0$ for a base vertex $v$ and $M>2(4/\eta)^2+1$, then $\|B_p(G,H,Q)\|_p>2^{b(p)}$",
     ["GsimOT.Hardness.claim55"]),
    ("Claim~56", "55--56",
     r"If $Q(v,w),Q(v,w')\ge\varepsilon>0$ for distinct base vertices $w,w'$ (with at most one common "
     r"neighbour, which follows from $A\ge5$) and $M>2(2/\varepsilon)^2+1$, then $\|B_p(G,H,Q)\|_p>2^{b(p)}$",
     ["GsimOT.Hardness.claim56"]),
    ("Theorem~17 (YES)", "12, 55", r"YES-instances: $d^{\mathrm{OT}}_p(G,H)\le1$ for all $1\le p\le\infty$",
     ["GsimOT.Hardness.ThreePartition.dOT_le_one_of_isYes", "GsimOT.Hardness.opNorm_Bpq_permMat_le_one"]),
    ("Theorem~17 (NO), Eq.~(46)", "12, 56--57",
     r"NO-instances with all $a_i\ge3$: $d^{\mathrm{OT}}_p(G,H)>2^{b(p)}-\varepsilon$ for $0<\varepsilon\le1$ and $M$ as in Eq.~(46)",
     ["GsimOT.Hardness.ThreePartition.lt_dOT_of_not_isYes"]),
    (r"Theorem~17 (w.l.o.g.\ $a_i\ge3$)", "54", r"Both bounds after adding $3$ to each $a_i$ and $9$ to $A$",
     ["GsimOT.Hardness.ThreePartition.dOT_shift_gap"]),
    (r"Theorem~4\,(2)", "4",
     r"Hardness of approximating $d^{\mathrm{OT}}_p$ within $2^{b(p)}-\varepsilon$ (complexity side not formalised)",
     ["GsimOT.Hardness.ThreePartition.dOT_shift_gap"]),
]

THM17_NOTES = [
    HARDNESS_NOTE,
    r"Theorem~17 is proved with the bound $2^{b(p)}-\varepsilon$ of its statement. The paper fixes "
    r"$0<\varepsilon^*<\sqrt2-1$ (p.~54, l.~1728), so that $2^{b(p)}-\varepsilon^*>1$ (l.~1729--1730); the Lean "
    r"statement holds for all $0<\varepsilon\le1$, which includes this range.",
    r"Lemma~53 is proved without the duality of Lemma~19 (Appendix~A): $A^Qx$ is the $Q$-average of $B_p\tilde x$ with "
    r"$\tilde x(v,w)=Q(v,w)^{1/p}x(v)$ (the paper's $\tilde x$), and the averaging is an $\ell^p$ contraction by Jensen. "
    r"Corollary~54 uses the test vectors $e_v$ and a normalised sign vector on the column support instead of "
    r"$\|A\|_p=\|A^\top\|_{p^*}$.",
    r"YES-instances: the paper observes that $A_H-A^\pi_G$ is the adjacency matrix of $3m$ disjoint edges, so "
    r"$\|A^\pi_G-A_H\|_p=1$ (p.~55, l.~1736--1737); the formalisation bounds it by $1$ "
    r"by the Schur test (all absolute row and column sums are at most $1$).",
    r"Claim~56 takes $|N_H(w)\cap N_H(w')|\le1$ as a hypothesis; it is discharged with $A\ge7$ in the proof of the theorem.",
    r"Remark~62 (other operator $p\to q$-norms, p.~62) is not formalised.",
]

THM18_ROWS = [
    ("Proof of Thm.~18 ([GG22], [AN06])", "57, 59",
     r"Base graphs $G',H'$ from the [AN06] matrix ($G'$: edges of the positive entries, $H'$: edges of the "
     r"negative entries, l.~1885--1891) with $C_\square(\pi)=\|A_{G'}-A_{H'}\|_\square=2\,\mathrm{maxcut}(F)$ "
     r"(l.~1826--1830)",
     ["GsimOT.Hardness.anG", "GsimOT.Hardness.anH", "GsimOT.Hardness.cutNorm_anG_sub_anH"]),
    ("Proof of Thm.~18: leaves", "57, 62",
     r"$\ell_i=i(n^2+n)k$ leaves at the $i$-th base vertex of both graphs (l.~1831--1834), $k=\lceil1600n^6/\delta\rceil$ "
     r"(l.~1977)",
     ["GsimOT.Hardness.leafCount", "GsimOT.Hardness.leavesPaper"]),
    ("Claim~58", "58--59",
     r"If $Q(v,L_H)\ge\eta$ for a base vertex $v$, then $\|B(G,H,Q)\|_\square\ge\eta(M-2)/4$, where every base "
     r"vertex has at least $M$ leaves",
     ["GsimOT.Hardness.claim58"]),
    ("Claim~59", "59--60",
     r"If $Q(v,w),Q(v,w')\ge\tau$ for distinct base vertices $w,w'$, then $\|B(G,H,Q)\|_\square\ge\tau(M-2d)/2$, "
     r"where $d$ bounds the degrees in $H'$",
     ["GsimOT.Hardness.claim59"]),
    ("Claim~60", "60",
     r"If $v_i$ sends mass to $w_j$, $i\ne j$: $\|B(G,H,Q)\|_\square\ge Q(v_i,w_j)(|\ell_j-\ell_i|-d)$, split by the "
     r"order of $\ell_i,\ell_j$",
     ["GsimOT.Hardness.claim60", "GsimOT.Hardness.claim60'"]),
    ("Claim~61 (proof)", "61",
     r"If $Q(v_i,w_i)\ge1-\alpha$ for all $i$, then $\|B(G,H,Q)\|_\square\ge\|A_{G'}-A_{H'}\|_\square-2\alpha|V(G')|^2$",
     ["GsimOT.Hardness.claim61"]),
    ("Claim~61", "61",
     r"For $\delta\ge0$, $0\le\alpha\le\delta/(2n')^2$ and $Q(v_i,w_i)\ge1-\alpha$ for all $i$: "
     r"$\|B(G,H,Q)\|_\square\ge2(1-\delta)\,c$ if $\|A_{G'}-A_{H'}\|_\square=2c$, $c\in\mathbb N$",
     ["GsimOT.Hardness.claim61_delta"]),
    ("Facts used in Claims~58--60", "59, 60, 62",
     r"$\Delta(G'),\Delta(H')\le n-1$ (l.~1885--1892); $n'=2m+n\le n^2$ (l.~1969); $\mathrm{maxcut}(F)\le n^2/4$ "
     r"(l.~1880)",
     ["GsimOT.Hardness.card_adj_anG_le", "GsimOT.Hardness.card_adj_anH_le",
      "GsimOT.Hardness.two_mul_card_edge_add_le", "GsimOT.Hardness.four_mul_maxcut_le"]),
    ("Upper bound", "58",
     r"$d^{\mathrm{OT}}_\square(G,H)\le\|A_{G'}-A_{H'}\|_\square$ ($d^{\mathrm{OT}}_\square\le d_\square$ and the "
     r"canonical bijection, l.~1839--1840)",
     ["GsimOT.Hardness.dOTCut_addLeaves_le"]),
    ("Choice of the constants", "61--62",
     r"For $0<\delta<1$: $2(1-\delta)c\le d^{\mathrm{OT}}_\square(G,H)$ with $\alpha=\delta/(200n^4)$, $\eta=\alpha/2$, "
     r"$\tau=\alpha/(4n^2)$, $k=\lceil1600n^6/\delta\rceil$, for base graphs with $n'\le n^2$, degrees $\le n-1$ and "
     r"$\|A_{G'}-A_{H'}\|_\square=2c$, $1\le c\le n^2/4$",
     ["GsimOT.Hardness.le_dOTCut_addLeaves"]),
    ("Theorem~18 (reduction)", "13, 62",
     r"For $0<\delta<1$: $2(1-\delta)\,\mathrm{maxcut}(F)\le d^{\mathrm{OT}}_\square(G,H)\le2\,\mathrm{maxcut}(F)$ "
     r"for every graph $F$ with an edge, with the construction of the paper (l.~1982--1983)",
     ["GsimOT.Hardness.maxcut_dOTCut_bounds_paper"]),
    ("Eq.~(47)", "58",
     r"$\tfrac{33}{17}\,\mathrm{maxcut}(F)\le d^{\mathrm{OT}}_\square(G,H)\le2\,\mathrm{maxcut}(F)$: the case "
     r"$\delta=1/34$",
     ["GsimOT.Hardness.maxcut_dOTCut_bounds_eq47"]),
    ("Theorem~18 (variant)", "13",
     r"The reduction with $n'$ in place of $n$ in the leaf counts",
     ["GsimOT.Hardness.maxcut_dOTCut_bounds"]),
]

THM18_NOTES = [
    HARDNESS_NOTE,
    r"The base graphs $G',H'$ are built in \texttt{BaseGraphs.lean} from the [AN06] matrix as described in the "
    r"proof of Claim~59 (p.~59, l.~1885--1891): the vertices are the signed edges $e^\pm$ and the vertices of $F$; "
    r"for $e=uv$, $u<v$, $G'$ has the edges $e^+u$, $e^-v$ and $H'$ the edges $e^+v$, $e^-u$. "
    r"\lean{cutNorm_anG_sub_anH} proves $\|A_{G'}-A_{H'}\|_\square=2\,\mathrm{maxcut}(F)$, and the facts on "
    r"$G',H',F$ that the proof uses are proved: maximum degree at most $n-1$ (p.~59, l.~1885--1892), "
    r"$n'=2m+n\le n^2$ (p.~62, l.~1969) and $\mathrm{maxcut}(F)\le n^2/4$ (p.~59, l.~1880).",
    r"\lean{maxcut_dOTCut_bounds_paper} is the reduction with the paper's leaf counts "
    r"$i(n^2+n)\lceil1600n^6/\delta\rceil$; \lean{maxcut_dOTCut_bounds_eq47} is its case $\delta=1/34$, "
    r"Eq.~(47). \lean{maxcut_dOTCut_bounds} uses $n'$ in place of $n$ and needs neither the degree bound nor "
    r"$n'\le n^2$.",
    r"Claims~58--61 are proved for general parameters ($M$, $d$, $\eta$, $\tau$, $\rho$, $\alpha$); the thresholds "
    r"on $k$ are checked once, in \lean{le_dOTCut_addLeaves}, with the paper's $\alpha=\delta/(200n^4)$, "
    r"$\eta=\alpha/2$, $\tau=\alpha/(4n^2)$ and $k=\lceil1600n^6/\delta\rceil$. Claim~60 is split by the order of "
    r"$\ell_i$ and $\ell_j$. \lean{claim61} bounds $\|B(G,H,Q)\|_\square$ from below by "
    r"$\|A_{G'}-A_{H'}\|_\square-2\alpha|V(G')|^2$; \lean{claim61_delta} derives Claim~61 from it.",
]


# ---------------------------------------------------------------------------------------------
# LaTeX output
# ---------------------------------------------------------------------------------------------

PREAMBLE = r"""\documentclass[10pt,a4paper]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage[margin=2cm,landscape]{geometry}
\usepackage{amsmath,amssymb}
\usepackage{array,booktabs,longtable}
\usepackage{xcolor}
\usepackage{enumitem}
\usepackage[hidelinks]{hyperref}
\newcommand{\lean}[1]{\textcolor{blue!50!black}{\texttt{\detokenize{#1}}}}
\setlength{\LTpre}{6pt}\setlength{\LTpost}{6pt}
\renewcommand{\arraystretch}{1.25}
\begin{document}
"""


def table(rows):
    out = [r"\begin{longtable}{>{\raggedright\arraybackslash}p{3.2cm} >{\centering\arraybackslash}p{1.1cm} "
           r">{\raggedright\arraybackslash}p{8.4cm} >{\raggedright\arraybackslash}p{10.2cm}}",
           r"\toprule",
           r"\textbf{Paper} & \textbf{Page} & \textbf{Statement} & \textbf{Lean declaration(s) and location} \\",
           r"\midrule\endhead",
           r"\bottomrule\endfoot"]
    for item, page, stmt, names in rows:
        refs = r" \newline ".join(lean_ref(n) for n in names)
        out.append(f"{{}}{item} & {page} & {stmt} & {refs} \\\\ \\midrule")
    out[-1] = out[-1][: -len(r" \midrule")]
    out.append(r"\end{longtable}")
    return "\n".join(out)


def notes(items):
    return "\\begin{enumerate}[leftmargin=*]\n" + "\n".join(r"\item " + n for n in items) + "\n\\end{enumerate}"


def document(title, intro, main_stmt, sections=None, paper=None):
    parts = [PREAMBLE,
             r"\begin{center}{\Large\bfseries " + title + r"}\\[4pt]",
             r"{\small Correspondence between the paper and the Lean~4/Mathlib formalisation}\end{center}",
             r"\noindent\textbf{Paper.} " + (paper or PAPER) + r"\par\smallskip",
             intro]
    if main_stmt:
        parts.append(r"\paragraph{Main statement in Lean.}" + main_stmt)
    for heading, body in sections:
        parts.append(r"\section*{" + heading + "}")
        parts.append(body)
    parts.append(r"\end{document}")
    return "\n\n".join(parts)


AXIOMS = (r"\paragraph{Checking.} Run \texttt{bash build.sh} in the repository root (see \texttt{README.md}). "
          r"The script builds the library and runs \texttt{scripts/CheckAxioms.lean}, which must report only the standard "
          r"axioms \texttt{propext}, \texttt{Classical.choice}, \texttt{Quot.sound}: no \texttt{sorry} and no "
          r"additional axioms.")


def write_doc(folder, stem, tex, base=SRC):
    if ONLY and os.path.basename(os.path.normpath(os.path.join(base, folder))) not in ONLY:
        return
    out_dir = os.path.join(base, folder)
    tex_path = os.path.join(out_dir, stem + ".tex")
    with open(tex_path, "w", encoding="utf-8") as fh:
        fh.write(tex)
    print("wrote", os.path.relpath(tex_path, ROOT))
    if shutil.which("pdflatex") is None:
        print("  pdflatex not found; skipping PDF")
        return
    for _ in range(2):
        res = subprocess.run(["pdflatex", "-interaction=nonstopmode", "-halt-on-error", stem + ".tex"],
                             cwd=out_dir, capture_output=True, text=True)
        if res.returncode != 0:
            print(res.stdout[-3000:])
            sys.exit(f"error: pdflatex failed on {tex_path}")
    for ext in (".aux", ".log", ".out", ".toc"):
        p = os.path.join(out_dir, stem + ext)
        if os.path.exists(p):
            os.remove(p)
    print("wrote", os.path.relpath(os.path.join(out_dir, stem + ".pdf"), ROOT))


def main():
    # Common
    write_doc("Common", "Common_correspondence", document(
        r"Common notions and shared lemmas",
        r"The folder \texttt{GsimOT/Common} contains the notions shared by all formalised results "
        r"(Sections~1--2 and Appendix~A of the paper) together with the auxiliary results that are used by more than one "
        r"proof: Observation~21, Lemma~22, Lemma~29 and Eq.~(3), the $\ell^p$/operator norms with Lemma~19, the cut norm, "
        r"the optimal transport distances and the attainment of their minima (Appendix~A), the edit distance with Eq.~(7), "
        r"and the graphs of the reductions of Section~4. A reviewer-oriented overview of all definitions is "
        r"\texttt{Common\_overview.pdf}.\par" + AXIOMS,
        None,
        [("Correspondence", table(COMMON_ROWS)),
         ("Operator norms (\\texttt{OperatorNorm.lean}, \\texttt{Attainment.lean})", table(NORM_ROWS)),
         ("Cut norm and cut distance (\\texttt{CutNorm.lean}, \\texttt{AlignedDistances.lean})", table(CUT_ROWS)),
         ("Optimal transport distances (\\texttt{OTDistances.lean}, \\texttt{Attainment.lean})", table(OT_ROWS)),
         ("Lemma~22 for the edit distance (\\texttt{Lemma22\\_LockingMarkersEdit.lean})", table(LOCK_EDIT_ROWS)),
         ("Edit distance and Eq.~(3) (\\texttt{EditDistance.lean}, \\texttt{BirkhoffDecomposition.lean}, "
          "\\texttt{MatrixNorms.lean})", table(EDIT_ROWS)),
         ("Eq.~(7) (\\texttt{MatrixNorms.lean})", table(EQ7_ROWS)),
         ("Doubly stochastic matrices (\\texttt{DoublyStochastic.lean})", table(DS_ROWS)),
         ("Graphs of the reductions of Section~4 (\\texttt{PathsAndCycles.lean}, \\texttt{ThreePartition.lean}, "
          "\\texttt{Leaves.lean})", table(GADGET_ROWS)),
         ("Notes on the formalisation", notes(COMMON_NOTES))]))
    # HOG26 (separate library)
    write_doc(".", "HOG26_correspondence", document(
        r"Thin perfect matchings [HOG26]: Lean formalisation",
        r"The library \texttt{ThinMatching/} (independent of \texttt{GsimOT}) formalises [HOG26]: Lemma~1.2, "
        r"Theorem~1.3 (support-constrained) and Theorem~1.4 (relaxed, bipartite and general) with all lemmas of "
        r"Sections~3 and~4. Theorem~1.4 is the cited Theorem~35 of the main paper (p.~32). "
        r"A proof overview is in \texttt{ThinMatching/HOG26\_overview.pdf}.\par" + AXIOMS,
        r""" \lean{ThinMatching.theorem14_bip}: assuming [RS14] (\lean{RackeShahTheorem}), there is an absolute $C>0$ such that
for every bipartite fractional perfect matching $x$ on $L\cup R$, $|L|=|R|=n$, some perfect matching $M\subseteq L\times R$
satisfies $|M\cap\delta(S)|\le C\ln(2n)\ln\ln(4n)\,x(\delta(S))$ for all $S\subseteq L\cup R$.
\lean{ThinMatching.theorem13_support}: assuming Lemma~3.6 (\lean{Lemma36}), every $x\in\mathrm{PM}(G)$ has a
$C|V|\ln(2|V|)$-thin perfect matching inside $\mathrm{supp}(x)$.""",
        [("Correspondence", table(HOG_ROWS)), ("Notes on the formalisation", notes(HOG_NOTES))],
        paper=HOG_PAPER),
        base=os.path.join(ROOT, "ThinMatching"))
    # Proposition 12 (folder Proposition12_CutVsSpectral)
    write_doc("Proposition12_CutVsSpectral", "Proposition12_correspondence", document(
        r"Proposition 12: cut distance and spectral distance",
        r"The folder \texttt{GsimOT/Proposition12\_CutVsSpectral} formalises Proposition~12 (p.~11) and its proof "
        r"(beginning of Appendix~F, pp.~44--45).\par" + AXIOMS,
        r""" \lean{GsimOT.proposition12}: for all graphs $G,H$ of the same order,
\[ \delta_\square(G,H)\le\delta_2(G,H)\le2\sqrt{\delta_\square(G,H)}. \]""",
        [("Correspondence", table(PROP12_ROWS)),
         ("Shared notions used (from \\texttt{GsimOT/Common})", table(CUT_ROWS)),
         ("Notes on the formalisation", notes(PROP12_NOTES))]))
    # Proposition 10 (folder Proposition10_CutLowerBound)
    write_doc("Proposition10_CutLowerBound", "Proposition10_correspondence", document(
        r"Proposition 10: a factor 2 gap for the cut distance",
        r"The folder \texttt{GsimOT/Proposition10\_CutLowerBound} formalises Proposition~10 (p.~9) with the construction "
        r"of Appendix~E.1, Lemmas~33 and~34, the remark after Proposition~10 ($d^{\mathrm{OT}}_\square(G,H)=4$; its Lean "
        r"certificate, linked in footnote~2 of the paper, is \texttt{OptimalAlignment.lean}) and Theorem~3~(3).\par" + AXIOMS,
        r""" \lean{GsimOT.Prop10.proposition10}: the graphs $G,H$ of Appendix~E.1 have $145$ vertices,
\[ d_\square(G,H)=8\qquad\text{and}\qquad d^{\mathrm{OT}}_\square(G,H)\le4, \]
exactly as Proposition~10 states. \lean{GsimOT.Prop10.dOTCut_eq_four}: $d^{\mathrm{OT}}_\square(G,H)=4$, the
Lean certificate of the remark after Proposition~10. \lean{GsimOT.Prop10.theorem3_item3}:
$\delta_\square(G,H)=2\,\delta^{\mathrm{OT}}_\square(G,H)$ (Theorem~3~(3)).""",
        [("Correspondence", table(PROP10_ROWS)),
         ("Shared notions used (from \\texttt{GsimOT/Common})", table(CUT_ROWS)),
         ("Notes on the formalisation", notes(PROP10_NOTES))]))
    # Theorem 11 (folder Theorem11_CutUpperBound)
    write_doc("Theorem11_CutUpperBound", "Theorem11_correspondence", document(
        r"Theorem 11: upper bound for the cut distance",
        r"The folder \texttt{GsimOT/Theorem11\_CutUpperBound} formalises Theorem~11 (p.~10), the cut part of "
        r"Theorem~2, and Appendix~E.2: the multiplicative rounding via thin matchings (E.2.1: Lemmas~36, 37, Theorem~38), "
        r"the additive rounding (E.2.2: Lemmas~40--45, 47, 48, Corollary~46, Theorem~39), the Talagrand contraction "
        r"lemma (Lemma~43), and the final proof (E.2.3).\par" + AXIOMS,
        r""" \lean{GsimOT.theorem11_of_thin}: assuming Theorem 35 [HOG26] (\lean{ThinPermutationTheorem}),
there is a universal $C>0$ such that for all graphs $G,H$ of the same order, with $f=\delta^{\mathrm{OT}}_\square(G,H)$,
\[ f\le\delta_\square(G,H)\le C\,f\ln(e/f)\ln\bigl(e\ln(e/f)\bigr). \]
\lean{GsimOT.theorem11_power_lt_one_of_thin}: for every $\alpha<1$ there is $C_\alpha>0$ with
$\delta_\square(G,H)\le C_\alpha\,\delta^{\mathrm{OT}}_\square(G,H)^\alpha$; \lean{GsimOT.theorem2_cut_of_thin}: the same with
$\alpha=1-\varepsilon$ (Theorem~2). The \texttt{\_of\_rackeShah} versions assume only [RS14].""",
        [("Correspondence", table(THM11_ROWS)),
         ("Shared notions used (from \\texttt{GsimOT/Common})", table(CUT_ROWS)),
         ("Notes on the formalisation", notes(THM11_NOTES))]))
    # Proposition 13 (folder Proposition13_SpectralLowerBound)
    write_doc("Proposition13_SpectralLowerBound", "Proposition13_correspondence", document(
        r"Proposition 13: no linear bound for the spectral distance",
        r"The folder \texttt{GsimOT/Proposition13\_SpectralLowerBound} formalises Proposition~13 with the "
        r"construction of Appendix~F.1, Lemma~49, Theorem~3~(4) and the remark after Proposition~13.\par" + AXIOMS,
        r""" \lean{GsimOT.Prop13.proposition13}: for every $r\ge1$, with $n=|V(G_r)|=4r^2+3r+1$,
\[ d_2(G_r,H_r)=\sqrt r\qquad\text{and}\qquad \tfrac{1}{2\sqrt2}\le d^{\mathrm{OT}}_2(G_r,H_r)\le1; \]
\lean{GsimOT.Prop13.proposition13_explicit} adds $\frac1{2\sqrt2}\le\frac r{\sqrt n}\le d^{\mathrm{OT}}_2(G_r,H_r)$ (Lemma~49).
\lean{GsimOT.Prop13.no_power_bound}: for every $\alpha>\frac34$ and $C$, some $G_r,H_r$ violate $\delta_2\le C(\delta^{\mathrm{OT}}_2)^\alpha$.""",
        [("Correspondence", table(PROP13_ROWS)),
         ("Shared notions used (from \\texttt{GsimOT/Common})", table(OT_ROWS)),
         ("Notes on the formalisation", notes(PROP13_NOTES))]))
    # Theorem 14 (folder Theorem14_SpectralUpperBound)
    write_doc("Theorem14_SpectralUpperBound", "Theorem14_correspondence", document(
        r"Theorem 14: upper bound for the spectral distance",
        r"The folder \texttt{GsimOT/Theorem14\_SpectralUpperBound} formalises Theorem~14, its proof in Appendix~F.2 with "
        r"Lemmas~50--52, and the $\delta_2$ part of Theorem~2. No cited results are assumed.\par" + AXIOMS,
        r""" \lean{GsimOT.theorem14}: for all graphs $G,H$ of the same order, with $\delta=\delta^{\mathrm{OT}}_2(G,H)$,
\[ \delta_2(G,H)\le\delta+2\sqrt{2\delta}. \]
\lean{GsimOT.theorem14_h}: $\delta_2(G,H)\le\delta+4\sqrt{h\delta}$ with $h=\min\{\sqrt{p_G(1-p_G)},\sqrt{p_H(1-p_H)}\}$ (end of the proof);
\lean{GsimOT.theorem14_min}: $\delta_2(G,H)\le\min\{1,\delta+4\sqrt{h\delta}\}\le\min\{1,\delta+2\sqrt{2\delta}\}$ (with $\delta_2\le1$);
\lean{GsimOT.theorem14_sqrt}: $\delta_2(G,H)\le(1+2\sqrt2)\sqrt{\delta}$.""",
        [("Correspondence", table(THM14_ROWS)),
         ("Shared notions used (from \\texttt{GsimOT/Common})", table(OT_ROWS)),
         ("Notes on the formalisation", notes(THM14_NOTES))]))
    # Theorem 1
    write_doc("Theorem1_BlowupEqualsOT", "Theorem1_correspondence", document(
        r"Theorem 1: blowup distances equal optimal transport distances",
        r"The folder \texttt{GsimOT/Theorem1\_BlowupEqualsOT} formalises Theorem~1 and its proof in "
        r"Appendix~B, including Claim~20. The operator norms, Lemma~19 and the attainment of the minimum in Eq.~(2) live in "
        r"\texttt{GsimOT/Common} (\texttt{OperatorNorm.lean}, \texttt{Attainment.lean}). A proof overview is "
        r"\texttt{Theorem1\_overview.pdf}.\par" + AXIOMS,
        r""" \lean{GsimOT.theorem1}: for all $p,q\in[1,\infty]$ and all finite graphs $G$ on $V\neq\emptyset$, $H$ on
$W\neq\emptyset$, \[ \delta^{\bullet}_{p\to q}(G,H)=\delta^{\mathrm{OT}}_{p\to q}(G,H). \]
\lean{GsimOT.theorem1_tendsto}: moreover $\delta_{p\to q}(G^{\bullet n\ell},H^{\bullet m\ell})\to
\delta^{\mathrm{OT}}_{p\to q}(G,H)$ as $\ell\to\infty$, where $m=|V|$, $n=|W|$ (so the limit exists).
\lean{GsimOT.theorem1_of_tendsto}: the paper's argument, assuming the existence of the limit.""",
        [("Correspondence: Theorem 1 and its proof", table(THM1_ROWS)),
         ("Operator norms and Lemma 19 used (from \\texttt{GsimOT/Common})", table(NORM_ROWS)),
         ("Notes on the formalisation", notes(THM1_NOTES))]))
    # Proposition 9
    write_doc("Proposition8_LocalEditLowerBound", "Proposition8_correspondence", document(
        r"Proposition 8: no linear bound for the local edit distance",
        r"The folder \texttt{GsimOT/Proposition8\_LocalEditLowerBound} formalises Proposition~8 together with the construction of Appendix~D.1 and "
        r"Lemmas~27 and~28, Theorem~3~(2), and the remarks after Proposition~8 and Theorem~9 that concern "
        r"$G_r,H_r$. Shared notions and lemmas (Observation~21, Lemma~22, Lemma~29) come from "
        r"\texttt{GsimOT/Common}; they are listed at the end.\par" + AXIOMS,
        r""" \lean{GsimOT.Prop8.proposition8}: for every $r\in\mathbb N$ with $2\le r$ and $r$ even,
\[ d_1(G_r,H_r)=r,\qquad d_1^{\mathrm{OT}}(G_r,H_r)=1,\qquad r^3\le|V(G_r)|\le 19\,r^3 . \]
\lean{GsimOT.Prop8.no_linear_bound}: for every $c\in\mathbb R$ there is an even $r\ge2$ with
$\delta_1(G_r,H_r)>c\cdot\delta_1^{\mathrm{OT}}(G_r,H_r)$.
\lean{GsimOT.Prop8.no_power_bound}: for all $C\in\mathbb R$ and $\alpha>2/3$ there is an even $r\ge2$ with
$\delta_1(G_r,H_r)>C\cdot(\delta_1^{\mathrm{OT}}(G_r,H_r))^\alpha$.""",
        [("Correspondence: Proposition 8 and its proof", table(PROP8_ROWS)),
         ("Shared notions and lemmas used (from \\texttt{GsimOT/Common})", table(COMMON_ROWS)),
         ("Notes on the formalisation", notes(PROP8_NOTES))]))
    # Theorem 10
    write_doc("Theorem9_LocalEditUpperBound", "Theorem9_correspondence", document(
        r"Theorem 9: upper bound for the local edit distance",
        r"The folder \texttt{GsimOT/Theorem9\_LocalEditUpperBound} formalises Theorem~9 together with Appendix~D.2 (Lemmas~30, 31, Proposition~32 and the "
        r"path-cutting construction); Theorem~9 is the $\delta_1$ part of Theorem~2. Shared notions and "
        r"lemmas (Eq.~(3), Observation~21, Lemma~29) come from \texttt{GsimOT/Common}; they are listed at "
        r"the end.\par" + AXIOMS,
        r""" \lean{GsimOT.theorem9}: assuming Lemma~30 (\lean{CVZRounding}), for all finite graphs $G$ on $V$
and $H$ on $W$ with $|V|=|W|$,
\[ \delta_1(G,H)\;\le\;15\sqrt{\delta_1^{\mathrm{OT}}(G,H)\cdot\ln\bigl(4/\delta_1^{\mathrm{OT}}(G,H)\bigr)} . \]
\lean{GsimOT.theorem9_power}: under the same hypotheses, for every $\alpha<1/2$ there is $C_\alpha$ with
$\delta_1(G,H)\le C_\alpha\,(\delta_1^{\mathrm{OT}}(G,H))^\alpha$.""",
        [("Correspondence: Theorem 9 and its proof", table(THM9_ROWS)),
         ("Shared notions and lemmas used (from \\texttt{GsimOT/Common})", table(COMMON_ROWS)),
         ("Notes on the formalisation", notes(THM9_NOTES))]))
    # Proposition 6
    write_doc("Proposition5_EditLowerBound", "Proposition5_correspondence", document(
        r"Proposition 5: the lower bound $4/3$ for the edit distance",
        r"The folder \texttt{GsimOT/Proposition5\_EditLowerBound} formalises Proposition~5 (p.~6) "
        r"with the construction of Appendix~C.1, Lemmas~23--25 "
        r"and Claim~26, and Theorem~3~(1). Shared notions and lemmas (the edit distance, Observation~21, "
        r"Lemma~22) come from \texttt{GsimOT/Common}; they are listed at the end.\par" + AXIOMS,
        r""" \lean{GsimOT.Prop5.proposition5_dEdit}: for every odd $N\ge3$, the graphs $G=$ \lean{GN N} and
$H=$ \lean{HN N} on the common vertex set \lean{VN N} satisfy
\[ d_{\mathrm{ed}}(G,H)\ge4N-2,\qquad d^{\mathrm{OT}}_{\mathrm{ed}}(G,H)\le3N+1; \]
\lean{GsimOT.Prop5.proposition5} states it for the costs ($C_{\mathrm{ed}}(\pi)\ge4N-2$ for all
bijections $\pi$, $C_{\mathrm{ed}}(Q)\le3N+1$ for some $Q\in\mathrm{DS}(V,W)$).
\lean{GsimOT.Prop5.proposition5_delta} (and \lean{GsimOT.Prop5.theorem3_item1}, Theorem~3~(1)): for every
$\varepsilon>0$ there is an odd $N\ge3$ with
$\delta_{\mathrm{ed}}(G,H)\ge(\frac43-\varepsilon)\,\delta^{\mathrm{OT}}_{\mathrm{ed}}(G,H)$; by
\lean{GsimOT.Prop5.proposition5_delta_of_le} this holds for every odd $N\ge3$ with
$\frac{10}{3(3N+1)}\le\varepsilon$.""",
        [("Correspondence: Proposition 5 and its proof", table(PROP5_ROWS)),
         ("Shared notions and lemmas used (from \\texttt{GsimOT/Common})", table(EDIT_ROWS + LOCK_ROWS)),
         ("Notes on the formalisation", notes(PROP5_NOTES))]))
    # Theorem 7
    write_doc("Theorem6_EditUpperBound", "Theorem6_correspondence", document(
        r"Theorem 6: upper bound for the edit distance",
        r"The folder \texttt{GsimOT/Theorem6\_EditUpperBound} formalises Theorem~6 (p.~7) "
        r"with its proof in Appendix~C.2 (Eq.~(17) and the "
        r"steps (a)--(g)) and the $\delta_{\mathrm{ed}}$ part of Theorem~2. Shared notions "
        r"(the edit distance, Eq.~(3)) come from \texttt{GsimOT/Common}; they are listed at the end.\par" + AXIOMS,
        r""" \lean{GsimOT.theorem6}: for weights $\lambda_i\ge0$ with $\sum_i\lambda_i=1$ and bijections
$\pi_i\colon V\to W$ over a finite index set, if $Q=\sum_i\lambda_iP_{\pi_i}$, then
\[ \sum_i\lambda_i\,C_{\mathrm{ed}}(\pi_i)\le2\,C_{\mathrm{ed}}(Q). \]
\lean{GsimOT.theorem6_dEdit}: $d_{\mathrm{ed}}(G,H)\le2\,d^{\mathrm{OT}}_{\mathrm{ed}}(G,H)$, and
\lean{GsimOT.theorem2_edit} (Theorem~2, first bound): $\delta_{\mathrm{ed}}(G,H)\le2\,\delta^{\mathrm{OT}}_{\mathrm{ed}}(G,H)$,
for all finite graphs $G,H$.""",
        [("Correspondence: Theorem 6 and its proof", table(THM6_ROWS)),
         ("Shared notions used (from \\texttt{GsimOT/Common})", table(EDIT_ROWS)),
         ("Notes on the formalisation", notes(THM6_NOTES))]))
    # Theorem 16
    write_doc("Theorem15_EditHardness", "Theorem15_correspondence", document(
        r"Theorem 15: hardness of the optimal-transport edit distance",
        r"The folder \texttt{GsimOT/Theorem15\_EditHardness} formalises the reduction of Theorem~15 "
        r"(p.~12, proof in Appendix~G, pp.~50--51) from "
        r"Three-Partition. It gives Theorem~4\,(1). Shared notions come from \texttt{GsimOT/Common}; they are "
        r"listed at the end.\par" + AXIOMS,
        r""" \lean{GsimOT.Hardness.ThreePartition.dOTEdit_le_iff}: for an instance $(A,a_1,\dots,a_{3m})$ of
Three-Partition with all $a_i\ge2$, the union $F_1$ of paths on $a_i$ vertices and the union $F_2$ of $m$ paths
on $A$ vertices satisfy
\[ d^{\mathrm{OT}}_{\mathrm{ed}}(F_1,F_2)\le4m\iff\text{the instance is a YES-instance}. \]""",
        [("Correspondence", table(THM15_ROWS)),
         ("Shared notions used (from \\texttt{GsimOT/Common})", table(EDIT_ROWS + GADGET_ROWS)),
         ("Notes on the formalisation", notes(THM15_NOTES))]))
    # Theorem 17
    write_doc("Theorem16_LocalEditHardness", "Theorem16_correspondence", document(
        r"Theorem 16: inapproximability of the optimal-transport local edit distance",
        r"The folder \texttt{GsimOT/Theorem16\_LocalEditHardness} formalises the reduction of Theorem~16 "
        r"(p.~12, proof in Appendix~G, pp.~51--52) from "
        r"Three-Partition. It gives the case $p=1$ of Theorem~4\,(2). Shared notions come from "
        r"\texttt{GsimOT/Common}; they are listed at the end.\par" + AXIOMS,
        r""" For an instance $(A,a_1,\dots,a_{3m})$ of Three-Partition, let $F_1$ be the union of paths on $a_i$
vertices and $F_2$ the union of $m$ cycles on $A$ vertices.
\lean{GsimOT.Hardness.ThreePartition.dOTOne_le_of_isYes}: for a YES-instance with all $a_i\ge2$,
$d^{\mathrm{OT}}_1(F_1,F_2)\le1$.
\lean{GsimOT.Hardness.ThreePartition.two_le_dOTOne_of_not_isYes}: for a NO-instance,
$d^{\mathrm{OT}}_1(F_1,F_2)\ge2$.""",
        [("Correspondence", table(THM16_ROWS)),
         ("Shared notions used (from \\texttt{GsimOT/Common})", table(EQ7_ROWS + GADGET_ROWS)),
         ("Notes on the formalisation", notes(THM16_NOTES))]))
    # Theorem 18
    write_doc("Theorem17_OperatorNormHardness", "Theorem17_correspondence", document(
        r"Theorem 17: inapproximability for the operator $p$-norms",
        r"The folder \texttt{GsimOT/Theorem17\_OperatorNormHardness} formalises Eq.~(45), Lemma~53, Corollary~54 and the "
        r"reduction of Theorem~17 (p.~12, proof in Appendix~G, pp.~54--57) from Three-Partition with Claims~55 and~56 "
        r"and Eq.~(46). It gives Theorem~4\,(2). Shared "
        r"notions come from \texttt{GsimOT/Common}; they are listed at the end.\par" + AXIOMS,
        r""" For an instance $(A,a_1,\dots,a_{3m})$ of Three-Partition, the graphs $G$ and $H$ arise from the
union of paths on $a_i$ vertices and the union of $m$ cycles on $A$ vertices by attaching $M$ leaves to every
vertex. Let $1\le p\le\infty$.
\lean{GsimOT.Hardness.ThreePartition.dOT_le_one_of_isYes}: for a YES-instance with all $a_i\ge2$,
$d^{\mathrm{OT}}_p(G,H)\le1$.
\lean{GsimOT.Hardness.ThreePartition.lt_dOT_of_not_isYes}: for a NO-instance with all $a_i\ge3$, $0<\varepsilon\le1$
and $M$ as in Eq.~(46), $d^{\mathrm{OT}}_p(G,H)>2^{b(p)}-\varepsilon$.""",
        [("Correspondence", table(THM17_ROWS)),
         ("Shared notions used (from \\texttt{GsimOT/Common})", table(NORM_ROWS + OT_ROWS + GADGET_ROWS)),
         ("Notes on the formalisation", notes(THM17_NOTES))]))
    # Theorem 22
    write_doc("Theorem18_CutHardness", "Theorem18_correspondence", document(
        r"Theorem 18: hardness of approximating the optimal-transport cut distance",
        r"The folder \texttt{GsimOT/Theorem18\_CutHardness} formalises the reduction of Theorem~18 (p.~13, l.~443--444; "
        r"proof in Appendix~G, pp.~57--62) from MaxCut with Claims~58--61 and Eq.~(47). It gives Theorem~4\,(3) up to the "
        r"complexity side. Shared notions come from \texttt{GsimOT/Common}; they are listed at the end.\par" + AXIOMS,
        r""" \lean{GsimOT.Hardness.maxcut_dOTCut_bounds_paper}: for every $0<\delta<1$ and every graph $F$ on $n$ vertices
with an edge, the graphs $G,H$ obtained from the base graphs $G',H'$ by attaching
$\ell_i=i(n^2+n)\lceil1600n^6/\delta\rceil$ leaves to the $i$-th vertex satisfy
\[ 2(1-\delta)\,\mathrm{maxcut}(F)\le d^{\mathrm{OT}}_\square(G,H)\le2\,\mathrm{maxcut}(F). \]
\lean{GsimOT.Hardness.maxcut_dOTCut_bounds_eq47}: the case $\delta=1/34$, Eq.~(47):
$\tfrac{33}{17}\,\mathrm{maxcut}(F)\le d^{\mathrm{OT}}_\square(G,H)\le2\,\mathrm{maxcut}(F)$.""",
        [("Correspondence", table(THM18_ROWS)),
         ("Shared notions used (from \\texttt{GsimOT/Common})", table(CUT_ROWS + DS_ROWS + GADGET_ROWS)),
         ("Notes on the formalisation", notes(THM18_NOTES))]))


if __name__ == "__main__":
    main()
