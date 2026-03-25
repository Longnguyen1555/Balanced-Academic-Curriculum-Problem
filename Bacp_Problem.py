from pysat.solvers import Glucose3
from pysat.formula import CNF, IDPool
from pysat.card import CardEnc, EncType


"""
Constraints:
1) Each course is assigned to exactly one term.
2) Each term has between [min_courses, max_courses] courses.
3) Each term has between [min_credits, max_credits] total credits.
4) Prerequisites: if (ci is prerequisite of cj) then term(ci) < term(cj)
"""

def var_ct(c, t, n_terms):
    return c * n_terms + t + 1

def add_exactly_one(cnf, n_courses, n_terms, vpool):
    for c in range(n_courses):
        lits = [var_ct(c, t, n_terms) for t in range(n_terms)]
        enc = CardEnc.equals(lits, 1, vpool, EncType.seqcounter)
        cnf.extend(enc.clauses)

def add_course_limits(cnf, n_courses, n_terms, min_courses, max_courses, vpool):
    for t in range(n_terms):
        lits = [var_ct(c, t, n_terms) for c in range(n_courses)]

        enc_up = CardEnc.atleast(lits, min_courses, vpool, EncType.seqcounter)
        cnf.extend(enc_up.clauses)

        enc_low = CardEnc.atmost(lits, max_courses, vpool, EncType.seqcounter)
        cnf.extend(enc_low.clauses)


def add_credit_limits(cnf, n_courses, n_terms, credits, min_credits, max_credits, vpool):
    for t in range(n_terms):
        temp = []
        for c in range(n_courses):
            lit = var_ct(c, t, n_terms)
            w = int(credits[c])
            if w < 0:
                raise ValueError("credits must be non-negative")
            temp.extend([lit] * w)

        enc_low = CardEnc.atleast(temp, min_credits, vpool, EncType.seqcounter)
        cnf.extend(enc_low.clauses)

        enc_up = CardEnc.atmost(temp, max_credits, vpool, EncType.seqcounter)
        cnf.extend(enc_up.clauses)


def add_prerequisites(cnf, prereq_pairs, n_terms):
    for (ci, cj) in prereq_pairs:
        for t in range(n_terms):
            x_cj_t = var_ct(cj, t, n_terms)
            for k in range(t, n_terms):
                x_ci_k = var_ct(ci, k, n_terms)
                cnf.append([-x_cj_t, -x_ci_k])


def decode_solution(model: list[int], n_courses: int, n_terms: int) -> list[int]:

    pos = set(l for l in model if l > 0)
    assign = [-1] * n_courses
    for c in range(n_courses):
        for t in range(n_terms):
            if var_ct(c, t, n_terms) in pos:
                assign[c] = t
                break
    return assign


def solve_bac(course_names, n_terms, credits, prereq_pairs, min_credits, max_credits, min_courses, max_courses):

    n_courses = len(course_names)
    cnf = CNF()

    vpool = IDPool(n_courses * n_terms + 1)

    add_exactly_one(cnf, n_courses, n_terms, vpool)
    add_course_limits(cnf, n_courses, n_terms, min_courses, max_courses, vpool)
    add_credit_limits(cnf, n_courses, n_terms, credits, min_credits, max_credits, vpool)
    add_prerequisites(cnf, prereq_pairs, n_terms)

    with Glucose3(cnf.clauses) as solver:
        if not solver.solve():
            return None
        model = solver.get_model()

    return decode_solution(model, n_courses, n_terms)


def print_schedule(course_names: list[str], credits: list[int], assign: list[int], n_terms: int) -> None:

    buckets = [[] for _ in range(n_terms)]
    for c, t in enumerate(assign):
        buckets[t].append(c)

    print("\n===== SCHEDULE =====")
    for t in range(n_terms):
        term_courses = buckets[t]
        term_credits = sum(credits[c] for c in term_courses)
        print(f"\nTerm {t + 1}: {len(term_courses)} courses, {term_credits} credits")
        for c in term_courses:
            print(f"  - {course_names[c]} ({credits[c]})")


def main():
    p = 10   # number of terms
    a = 10   # min credits per term
    b = 24   # max credits per term
    cmin = 2 # min courses per term
    dmax = 10# max courses per term

    courses = [
        "dew100","fis100","hrwxx1","iwg101","mat021","qui010",
        "dew101","fis110","hrwxx2","iwi131","mat022",
        "dewxx0","fis120","hcw310","hrwxx3","ili134","ili151","mat023",
        "hcw311","ili135","ili153","ili260","iwn261","mat024",
        "fis130","ili239","ili245","ili253","fis140","ili236","ili243",
        "ili270","ili280","ici344","ili263","ili332","ili355","iwn170",
        "icdxx1","ili362","iwn270","icdxx2",
    ]

    credit = [
        1,3,2,2,5,3,
        1,5,2,3,5,
        1,4,1,2,4,3,4,
        1,4,3,3,3,4,
        4,4,4,4,4,4,4,
        3,4,4,3,4,4,3,
        3,3,3,3,
    ]

    # Prerequisite: <course, prerequisite>
    prereq_raw = [
        ("dew101","dew100"),
        ("fis110","fis100"), ("fis110","mat021"),
        ("mat022","mat021"),
        ("dewxx0","dew101"),
        ("fis120","fis110"), ("fis120","mat022"),

        ("ili134","iwi131"),
        ("ili151","iwi131"),
        ("mat023","mat022"),
        ("hcw311","hcw310"),
        ("ili135","ili134"),
        ("ili153","ili134"), ("ili153","ili151"),

        ("mat024","mat023"),
        ("fis130","fis110"), ("fis130","mat022"),
        ("ili239","ili135"),
        ("ili245","ili153"),
        ("ili253","ili153"),
        ("fis140","fis120"), ("fis140","fis130"),
        ("ili236","ili239"),
        ("ili243","ili245"),
        ("ili270","ili260"), ("ili270","iwn261"),
        ("ili280","mat024"),
        ("ici344","ili243"),
        ("ili263","ili260"), ("ili263","iwn261"),
        ("ili332","ili236"),
        ("ili355","ili153"), ("ili355","ili280"),
        ("ili362","ili263"),
    ]

    idx = {name: i for i, name in enumerate(courses)}

    prereq_pairs = [(idx[pre], idx[course]) for (course, pre) in prereq_raw]

    assign = solve_bac(courses,p,credit,prereq_pairs,a,b,cmin,dmax)

    if assign is None:
        print("UNSAT")
    else:
        print_schedule(courses, credit, assign, p)


if __name__ == "__main__":
    main()