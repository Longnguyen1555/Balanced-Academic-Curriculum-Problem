from __future__ import annotations

from dataclasses import dataclass
from math import ceil, floor
from typing import Iterable

from pysat.card import CardEnc, EncType
from pysat.examples.rc2 import RC2
from pysat.formula import IDPool, WCNF
from pysat.pb import PBEnc

from Bacp_Instance import BacpInstance




def transitive_closure(n_courses: int, arcs: Iterable[tuple[int, int]]) -> list[tuple[int, int]]:
    """Return prerequisite (pre, post)."""
    succ = [set() for _ in range(n_courses)]
    for u, v in arcs:
        succ[u].add(v)

    changed = True
    while changed:
        changed = False
        for u in range(n_courses):
            extra = set()
            for v in list(succ[u]):
                extra |= succ[v]
            new_nodes = extra - succ[u]
            if new_nodes:
                succ[u] |= new_nodes
                changed = True

    out: list[tuple[int, int]] = []
    for u in range(n_courses):
        for v in sorted(succ[u]):
            out.append((u, v))
    return out


class BacpMaxSATSolver:
    def __init__(self, inst: BacpInstance) -> None:
        self.inst = inst
        self.n_courses = len(inst.course_names)
        self.n_terms = inst.n_terms
        self.vpool = IDPool()
        self.wcnf = WCNF()

        self.total_credits = sum(inst.credits)
        self.alpha_floor = floor(self.total_credits / self.n_terms)
        self.alpha_ceil = ceil(self.total_credits / self.n_terms)

        self.add_hard_constraints()

    # ---------- variable helpers ----------

    def x(self, c: int, t: int) -> int:
        """x(c,t) = course c is assigned to term t."""
        return self.vpool.id(("x", c, t))

    def fwd(self, c: int, t: int) -> int:
        """F(c,t) = course c is assigned to one of terms 0..t."""
        return self.vpool.id(("F", c, t))

    def ok(self, d: int) -> int:
        """ok(d) = every term load lies within deviation d from the average target band."""
        return self.vpool.id(("ok", d))

    def term_lits(self, t: int) -> list[int]:
        return [self.x(c, t) for c in range(self.n_courses)]

    def append_hard(self, clauses: list[list[int]]) -> None:
        for clause in clauses:
            self.wcnf.append(clause)

    # ---------- hard constraints ----------

    def add_hard_constraints(self) -> None:
        self.add_exactly_one()
        self.add_course_count_limits()
        self.add_credit_limits()
        self.add_forward_staircase_prereqs()

    def add_exactly_one(self) -> None:
        for c in range(self.n_courses):
            lits = [self.x(c, t) for t in range(self.n_terms)]
            enc = CardEnc.equals(lits=lits, bound=1, vpool=self.vpool, encoding=EncType.seqcounter)
            self.append_hard(enc.clauses)

    def add_course_count_limits(self) -> None:
        for t in range(self.n_terms):
            lits = self.term_lits(t)

            enc_ge = CardEnc.atleast(
                lits=lits,
                bound=self.inst.min_courses,
                vpool=self.vpool,
                encoding=EncType.seqcounter,
            )
            enc_le = CardEnc.atmost(
                lits=lits,
                bound=self.inst.max_courses,
                vpool=self.vpool,
                encoding=EncType.seqcounter,
            )
            self.append_hard(enc_ge.clauses)
            self.append_hard(enc_le.clauses)

    def add_credit_limits(self) -> None:
        weights = list(self.inst.credits)
        for t in range(self.n_terms):
            lits = self.term_lits(t)

            enc_ge = PBEnc.atleast(
                lits=lits,
                weights=weights,
                bound=self.inst.min_credits,
                vpool=self.vpool,
            )
            enc_le = PBEnc.atmost(
                lits=lits,
                weights=weights,
                bound=self.inst.max_credits,
                vpool=self.vpool,
            )
            self.append_hard(enc_ge.clauses)
            self.append_hard(enc_le.clauses)

    def add_forward_staircase_prereqs(self) -> None:
        # F(c,t) <-> x(c,0) V ... V x(c,t)
        for c in range(self.n_courses):
            f0 = self.fwd(c, 0)
            x0 = self.x(c, 0)
            self.wcnf.append([-f0, x0])
            self.wcnf.append([-x0, f0])

            for t in range(1, self.n_terms):
                ft = self.fwd(c, t)
                ftm1 = self.fwd(c, t - 1)
                xt = self.x(c, t)

                # ft <-> (ftm1 or xt)
                self.wcnf.append([-ftm1, ft])
                self.wcnf.append([-xt, ft])
                self.wcnf.append([-ft, ftm1, xt])

        # not F(post, t) or not x(pre, t)
        for pre, post in self.inst.prereq_pairs:
            self.wcnf.append([-self.x(pre, self.n_terms - 1)])
            self.wcnf.append([-self.x(post, 0)])

            for t in range(self.n_terms - 1):
                self.wcnf.append([-self.fwd(post, t), -self.x(pre, t)])

    # ---------- decoding and objective ----------

    def decode_solution(self, model: list[int]) -> list[int]:
        pos = {v for v in model if v > 0}
        assign = [-1] * self.n_courses
        for c in range(self.n_courses):
            for t in range(self.n_terms):
                if self.x(c, t) in pos:
                    assign[c] = t
                    break
        return assign

    def term_loads(self, assign: list[int]) -> list[int]:
        loads = [0] * self.n_terms
        for c, t in enumerate(assign):
            loads[t] += self.inst.credits[c]
        return loads

    def deviation_cost(self, assign: list[int]) -> int:
        worst = 0
        for load in self.term_loads(assign):
            if load > self.alpha_ceil:
                worst = max(worst, load - self.alpha_ceil)
            elif load < self.alpha_floor:
                worst = max(worst, self.alpha_floor - load)
        return worst

    # ---------- MaxSAT deviation objective ----------

    def band_clauses_for_deviation(self, d: int) -> list[list[int]]:
        clauses: list[list[int]] = []
        weights = list(self.inst.credits)
        lo = max(0, self.alpha_floor - d)
        hi = self.alpha_ceil + d

        for t in range(self.n_terms):
            lits = self.term_lits(t)
            enc_hi = PBEnc.atmost(lits=lits, weights=weights, bound=hi, vpool=self.vpool)
            enc_lo = PBEnc.atleast(lits=lits, weights=weights, bound=lo, vpool=self.vpool)
            clauses.extend(enc_hi.clauses)
            clauses.extend(enc_lo.clauses)

        return clauses

    def deviation_upper_bound(self) -> int:
        """Safe upper bound such that deviation ub is always compatible with hard credit limits."""
        return max(
            self.alpha_floor,
            max(0, self.alpha_floor - self.inst.min_credits),
            max(0, self.inst.max_credits - self.alpha_ceil),
        )

    def add_deviation_objective(self, soft_weight: int = 1) -> int:
        if soft_weight <= 0:
            raise ValueError("soft_weight must be positive")

        ub = self.deviation_upper_bound()

        # ok(d) -> all terms stay within the deviation-d band.
        for d in range(ub + 1):
            ok_d = self.ok(d)
            for clause in self.band_clauses_for_deviation(d):
                self.wcnf.append([-ok_d] + clause)

        #
        for d in range(1, ub + 1):
            self.wcnf.append([-self.ok(d - 1), self.ok(d)])

        # Maximize the number of satisfied ok(d). Because of monotonicity,
        # this is equivalent to minimizing the smallest feasible deviation.
        for d in range(ub + 1):
            self.wcnf.append([self.ok(d)], weight=soft_weight)

        return ub

    def solve_maxsat(self, soft_weight: int = 1) -> tuple[list[int] | None, int | None]:
        self.add_deviation_objective(soft_weight=soft_weight)

        with RC2(self.wcnf) as rc2:
            model = rc2.compute()
            if model is None:
                return None, None

        assign = self.decode_solution(model)
        return assign, self.deviation_cost(assign)


# ---------- public wrapper with a familiar signature ----------

def solve_bacp(inst: BacpInstance) -> tuple[list[int] | None, int | None, list[int] | None]:

    solver = BacpMaxSATSolver(inst)
    assign, best_d = solver.solve_maxsat(soft_weight=1)
    if assign is None:
        return None, None, None
    return assign, best_d, solver.term_loads(assign)


