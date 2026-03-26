from __future__ import annotations

from dataclasses import dataclass
from math import ceil, floor
from typing import Iterable

from pysat.card import CardEnc, EncType
from pysat.examples.rc2 import RC2
from pysat.formula import IDPool, WCNF
from pysat.pb import PBEnc


@dataclass
class BacpInstance:
    course_names: list[str]
    n_terms: int
    credits: list[int]
    prereq_pairs: list[tuple[int, int]]  # (pre, post)
    min_credits: int
    max_credits: int
    min_courses: int
    max_courses: int


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

        self._add_hard_constraints()

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

    def _term_lits(self, t: int) -> list[int]:
        return [self.x(c, t) for c in range(self.n_courses)]

    def _append_hard(self, clauses: list[list[int]]) -> None:
        for clause in clauses:
            self.wcnf.append(clause)

    # ---------- hard constraints ----------

    def _add_hard_constraints(self) -> None:
        self._add_exactly_one()
        self._add_course_count_limits()
        self._add_credit_limits()
        self._add_forward_staircase_prereqs()

    def _add_exactly_one(self) -> None:
        for c in range(self.n_courses):
            lits = [self.x(c, t) for t in range(self.n_terms)]
            enc = CardEnc.equals(lits=lits, bound=1, vpool=self.vpool, encoding=EncType.seqcounter)
            self._append_hard(enc.clauses)

    def _add_course_count_limits(self) -> None:
        for t in range(self.n_terms):
            lits = self._term_lits(t)

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
            self._append_hard(enc_ge.clauses)
            self._append_hard(enc_le.clauses)

    def _add_credit_limits(self) -> None:
        weights = list(self.inst.credits)
        for t in range(self.n_terms):
            lits = self._term_lits(t)

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
            self._append_hard(enc_ge.clauses)
            self._append_hard(enc_le.clauses)

    def _add_forward_staircase_prereqs(self) -> None:
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

    def _band_clauses_for_deviation(self, d: int) -> list[list[int]]:
        clauses: list[list[int]] = []
        weights = list(self.inst.credits)
        lo = max(0, self.alpha_floor - d)
        hi = self.alpha_ceil + d

        for t in range(self.n_terms):
            lits = self._term_lits(t)
            enc_hi = PBEnc.atmost(lits=lits, weights=weights, bound=hi, vpool=self.vpool)
            enc_lo = PBEnc.atleast(lits=lits, weights=weights, bound=lo, vpool=self.vpool)
            clauses.extend(enc_hi.clauses)
            clauses.extend(enc_lo.clauses)

        return clauses

    def _deviation_upper_bound(self) -> int:
        """Safe upper bound such that deviation ub is always compatible with hard credit limits."""
        return max(
            self.alpha_floor,
            max(0, self.alpha_floor - self.inst.min_credits),
            max(0, self.inst.max_credits - self.alpha_ceil),
        )

    def _add_deviation_objective(self, soft_weight: int = 1) -> int:
        if soft_weight <= 0:
            raise ValueError("soft_weight must be positive")

        ub = self._deviation_upper_bound()

        # ok(d) -> all terms stay within the deviation-d band.
        for d in range(ub + 1):
            ok_d = self.ok(d)
            for clause in self._band_clauses_for_deviation(d):
                self.wcnf.append([-ok_d] + clause)

        # Monotonicity: if deviation <= d-1 is feasible, then deviation <= d is feasible.
        for d in range(1, ub + 1):
            self.wcnf.append([-self.ok(d - 1), self.ok(d)])

        # Maximize the number of satisfied ok(d). Because of monotonicity,
        # this is equivalent to minimizing the smallest feasible deviation.
        for d in range(ub + 1):
            self.wcnf.append([self.ok(d)], weight=soft_weight)

        return ub

    def solve_maxsat(self, soft_weight: int = 1) -> tuple[list[int] | None, int | None]:
        self._add_deviation_objective(soft_weight=soft_weight)

        with RC2(self.wcnf) as rc2:
            model = rc2.compute()
            if model is None:
                return None, None

        assign = self.decode_solution(model)
        return assign, self.deviation_cost(assign)


# ---------- public wrapper with a familiar signature ----------

def solve_bac(
    course_names: list[str],
    n_terms: int,
    credits: list[int],
    prereq_pairs: list[tuple[int, int]],
    min_credits: int,
    max_credits: int,
    min_courses: int,
    max_courses: int,
    soft_weight: int = 1,
) -> tuple[list[int] | None, int | None, list[int] | None]:
    inst = BacpInstance(
        course_names=course_names,
        n_terms=n_terms,
        credits=credits,
        prereq_pairs=transitive_closure(len(course_names), prereq_pairs),
        min_credits=min_credits,
        max_credits=max_credits,
        min_courses=min_courses,
        max_courses=max_courses,
    )

    solver = BacpMaxSATSolver(inst)
    assign, best_d = solver.solve_maxsat(soft_weight=soft_weight)
    if assign is None:
        return None, None, None
    return assign, best_d, solver.term_loads(assign)


# ---------- output ----------

def pretty_print_schedule(
    course_names: list[str],
    credits: list[int],
    assign: list[int],
    n_terms: int,
    best_deviation: int | None = None,
) -> None:
    buckets = [[] for _ in range(n_terms)]
    for c, t in enumerate(assign):
        buckets[t].append(c)

    total_credits = sum(credits)
    alpha_floor = floor(total_credits / n_terms)
    alpha_ceil = ceil(total_credits / n_terms)

    print("\n===== SCHEDULE (MaxSAT) =====")
    print(f"Average-load target band: [{alpha_floor}, {alpha_ceil}]")
    if best_deviation is not None:
        print(f"Optimal L'_inf deviation: {best_deviation}")

    for t in range(n_terms):
        term_courses = buckets[t]
        term_credits = sum(credits[c] for c in term_courses)
        print(f"\nTerm {t + 1}: {len(term_courses)} courses, {term_credits} credits")
        for c in term_courses:
            print(f"  - {course_names[c]} ({credits[c]})")


# ---------- demo on the same dataset ----------

def main() -> None:
    p = 10
    a = 10
    b = 24
    cmin = 2
    dmax = 10

    courses = [
        "dew100", "fis100", "hrwxx1", "iwg101", "mat021", "qui010",
        "dew101", "fis110", "hrwxx2", "iwi131", "mat022",
        "dewxx0", "fis120", "hcw310", "hrwxx3", "ili134", "ili151", "mat023",
        "hcw311", "ili135", "ili153", "ili260", "iwn261", "mat024",
        "fis130", "ili239", "ili245", "ili253", "fis140", "ili236", "ili243",
        "ili270", "ili280", "ici344", "ili263", "ili332", "ili355", "iwn170",
        "icdxx1", "ili362", "iwn270", "icdxx2",
    ]

    credit = [
        1, 3, 2, 2, 5, 3,
        1, 5, 2, 3, 5,
        1, 4, 1, 2, 4, 3, 4,
        1, 4, 3, 3, 3, 4,
        4, 4, 4, 4, 4, 4, 4,
        3, 4, 4, 3, 4, 4, 3,
        3, 3, 3, 3,
    ]

    # Raw format: (course, prerequisite)
    prereq_raw = [
        ("dew101", "dew100"),
        ("fis110", "fis100"), ("fis110", "mat021"),
        ("mat022", "mat021"),
        ("dewxx0", "dew101"),
        ("fis120", "fis110"), ("fis120", "mat022"),
        ("ili134", "iwi131"),
        ("ili151", "iwi131"),
        ("mat023", "mat022"),
        ("hcw311", "hcw310"),
        ("ili135", "ili134"),
        ("ili153", "ili134"), ("ili153", "ili151"),
        ("mat024", "mat023"),
        ("fis130", "fis110"), ("fis130", "mat022"),
        ("ili239", "ili135"),
        ("ili245", "ili153"),
        ("ili253", "ili153"),
        ("fis140", "fis120"), ("fis140", "fis130"),
        ("ili236", "ili239"),
        ("ili243", "ili245"),
        ("ili270", "ili260"), ("ili270", "iwn261"),
        ("ili280", "mat024"),
        ("ici344", "ili243"),
        ("ili263", "ili260"), ("ili263", "iwn261"),
        ("ili332", "ili236"),
        ("ili355", "ili153"), ("ili355", "ili280"),
        ("ili362", "ili263"),
    ]

    idx = {name: i for i, name in enumerate(courses)}
    prereq_pairs = [(idx[pre], idx[course]) for course, pre in prereq_raw]

    assign, best_deviation, loads = solve_bac(courses, p, credit, prereq_pairs, a, b, cmin, dmax)

    if assign is None:
        print("UNSAT")
        return

    print(f"Term loads: {loads}")
    pretty_print_schedule(courses, credit, assign, p, best_deviation=best_deviation)


if __name__ == "__main__":
    main()
