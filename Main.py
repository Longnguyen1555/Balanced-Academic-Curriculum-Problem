import os
import csv

import MaxSAT_Solver
import IncrementalSAT_Solver
import Bacp_Instance


def build_rows(instance_name, method_name, course_names, credits, assign, final_deviation, n_terms):
    rows = []
    term_courses = [[] for _ in range(n_terms)]
    term_credits = [0] * n_terms

    for c, t in enumerate(assign):
        term_courses[t].append(course_names[c])
        term_credits[t] += credits[c]

    for t in range(n_terms):
        rows.append({
            "instance": instance_name,
            "method": method_name,
            "term": t + 1,
            "num_courses": len(term_courses[t]),
            "total_credits": term_credits[t],
            "final_deviation": final_deviation,
            "courses": ", ".join(term_courses[t])
        })

    return rows


def compute_deviation(loads, n_terms):
    total = sum(loads)
    avg_floor = total // n_terms
    avg_ceil = (total + n_terms - 1) // n_terms

    deviation = 0
    for load in loads:
        if load > avg_ceil:
            deviation = max(deviation, load - avg_ceil)
        elif load < avg_floor:
            deviation = max(deviation, avg_floor - load)

    return deviation


def solve_one_file(path):
    inst = Bacp_Instance.read_instance(path)
    rows = []
    instance_name = os.path.basename(path)

    # Incremental SAT
    inc_assign, inc_dev, inc_loads = IncrementalSAT_Solver.solve_bacp(inst)
    if inc_assign is not None:
        rows.extend(build_rows(
            instance_name,
            "IncrementalSAT",
            inst.course_names,
            inst.credits,
            inc_assign,
            inc_dev,
            inst.n_terms
        ))

    # MaxSAT
    max_result = MaxSAT_Solver.solve_bacp(inst)
    if max_result is not None:
        max_assign, _, _ = max_result

        max_loads = [0] * inst.n_terms
        for c, t in enumerate(max_assign):
            max_loads[t] += inst.credits[c]

        max_dev = compute_deviation(max_loads, inst.n_terms)

        rows.extend(build_rows(
            instance_name,
            "MaxSAT",
            inst.course_names,
            inst.credits,
            max_assign,
            max_dev,
            inst.n_terms
        ))

    return rows


def main():
    data_dir = "data"
    output_csv = "comparison.csv"

    if not os.path.isdir(data_dir):
        print(f"Directory '{data_dir}' does not exist.")
        return

    dat_files = []
    for filename in os.listdir(data_dir):
        if filename.endswith(".dat"):
            dat_files.append(os.path.join(data_dir, filename))

    dat_files.sort()

    if not dat_files:
        print(f"No .dat files found in '{data_dir}'.")
        return

    all_rows = []
    for path in dat_files:
        all_rows.extend(solve_one_file(path))

    with open(output_csv, "w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "instance",
                "method",
                "term",
                "num_courses",
                "total_credits",
                "final_deviation",
                "courses"
            ]
        )
        writer.writeheader()
        writer.writerows(all_rows)

    print(f"Saved CSV to {output_csv}")


if __name__ == "__main__":
    main()