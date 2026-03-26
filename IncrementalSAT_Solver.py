from __future__ import annotations

from Bacp_Instance import BacpInstance
from math import ceil, floor
from typing import Iterable

from pysat.card import CardEnc, EncType
from pysat.formula import CNF, IDPool
from pysat.pb import PBEnc
from pysat.solvers import Glucose3



def transitive_closure(n_courses: int, arcs: Iterable[tuple[int, int]]) -> list[tuple[int, int]]:
    """Return transitive closure of prerequisite arcs (pre, post)."""
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


class BacpIncrementalSolver:
    def __init__(self, inst: BacpInstance) -> None:
        self.inst = inst
        self.n_courses = len(inst.course_names)
        self.n_terms = inst.n_terms
        self.vpool = IDPool()
        self.cnf = CNF()

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

    def term_lits(self, t: int) -> list[int]:
        return [self.x(c, t) for c in range(self.n_courses)]

    # ---------- hard constraints ----------

    def add_hard_constraints(self) -> None:
        self.add_exactly_one()
        self.add_course_limits()
        self.add_credit_limits()
        self.add_forward_staircase_prereqs()

    def add_exactly_one(self) -> None:
        for c in range(self.n_courses):
            lits = [self.x(c, t) for t in range(self.n_terms)]
            enc = CardEnc.equals(lits=lits, bound=1, vpool=self.vpool, encoding=EncType.seqcounter)
            self.cnf.extend(enc.clauses)

    def add_course_limits(self) -> None:
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
            self.cnf.extend(enc_ge.clauses)
            self.cnf.extend(enc_le.clauses)

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
            self.cnf.extend(enc_ge.clauses)
            self.cnf.extend(enc_le.clauses)

    def add_forward_staircase_prereqs(self) -> None:
        # F(c,t) <-> x(c,0) V ... V x(c,t)
        for c in range(self.n_courses):
            f0 = self.fwd(c, 0)
            x0 = self.x(c, 0)
            self.cnf.append([-f0, x0])
            self.cnf.append([-x0, f0])

            for t in range(1, self.n_terms):
                ft = self.fwd(c, t)
                ftm1 = self.fwd(c, t - 1)
                xt = self.x(c, t)

                # ft <-> (ftm1 or xt)
                self.cnf.append([-ftm1, ft])
                self.cnf.append([-xt, ft])
                self.cnf.append([-ft, ftm1, xt])

        #     not F(post, t) or not x(pre, t)
        for pre, post in self.inst.prereq_pairs:

            self.cnf.append([-self.x(pre, self.n_terms - 1)])
            self.cnf.append([-self.x(post, 0)])

            for t in range(self.n_terms - 1):
                self.cnf.append([-self.fwd(post, t), -self.x(pre, t)])

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

    # ---------- incremental method ----------

    def bound_clauses_for_deviation(self, d: int) -> list[list[int]]:

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

    def solve_incremental(self) -> tuple[list[int] | None, int | None]:

        with Glucose3(bootstrap_with=self.cnf.clauses) as solver:
            if not solver.solve():
                return None, None

            best_model = solver.get_model()
            best_assign = self.decode_solution(best_model)
            best_d = self.deviation_cost(best_assign)

            # loop until UNSAT.
            for d in range(best_d - 1, -1, -1):
                solver.append_formula(self.bound_clauses_for_deviation(d))
                if not solver.solve():
                    break

                best_model = solver.get_model()
                best_assign = self.decode_solution(best_model)
                best_d = self.deviation_cost(best_assign)

            return best_assign, best_d




def solve_bacp(inst: BacpInstance) -> tuple[list[int] | None, int | None, list[int] | None]:

    solver = BacpIncrementalSolver(inst)
    assign, best_d = solver.solve_incremental()
    if assign is None:
        return None, None, None
    return assign, best_d, solver.term_loads(assign)


