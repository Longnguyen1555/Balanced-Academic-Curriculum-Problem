import re
from dataclasses import dataclass


@dataclass
class BacpInstance:
    course_names: list[str]
    n_terms: int
    credits: list[int]
    prereq_pairs: list[tuple[int, int]]   # (pre, post)
    min_credits: int
    max_credits: int
    min_courses: int
    max_courses: int


def read_instance(path: str) -> BacpInstance:
    with open(path, "r", encoding="utf-8") as f:
        text = f.read()

    lines = []
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("%"):
            continue
        lines.append(line)

    text = "\n".join(lines)

    def extract_int(name: str) -> int:
        pattern = rf"\b{name}\s*=\s*(\d+)\s*;"
        m = re.search(pattern, text)
        if not m:
            raise ValueError(f"Cannot find integer field: {name}")
        return int(m.group(1))

    def extract_block(name: str, open_char: str, close_char: str) -> str:
        start_pattern = rf"\b{name}\s*=\s*{re.escape(open_char)}"
        m = re.search(start_pattern, text)
        if not m:
            raise ValueError(f"Cannot find block start: {name}")

        start_idx = m.end()
        depth = 1
        i = start_idx

        while i < len(text):
            ch = text[i]
            if ch == open_char:
                depth += 1
            elif ch == close_char:
                depth -= 1
                if depth == 0:
                    return text[start_idx:i]
            i += 1

        raise ValueError(f"Cannot find block end: {name}")

    p = extract_int("p")
    a = extract_int("a")
    b = extract_int("b")
    c = extract_int("c")
    d = extract_int("d")

    courses_block = extract_block("courses", "{", "}")
    credit_block = extract_block("credit", "[", "]")
    prereq_block = extract_block("prereq", "{", "}")

    course_names = [x.strip() for x in courses_block.split(",") if x.strip()]
    credits = [int(x.strip()) for x in credit_block.replace("\n", " ").split(",") if x.strip()]

    if len(course_names) != len(credits):
        raise ValueError(
            f"Mismatch: {len(course_names)} courses but {len(credits)} credits in {path}"
        )

    name_to_id = {name: i for i, name in enumerate(course_names)}

    prereq_pairs = []
    pairs = re.findall(r"<\s*([^,<>]+)\s*,\s*([^,<>]+)\s*>", prereq_block)

    for course, prereq in pairs:
        course = course.strip()
        prereq = prereq.strip()

        if prereq not in name_to_id:
            raise ValueError(f"Unknown prerequisite course: {prereq}")
        if course not in name_to_id:
            raise ValueError(f"Unknown course in prerequisite: {course}")

        # file ghi theo dạng <course, prerequisite>

        prereq_pairs.append((name_to_id[prereq], name_to_id[course]))

    return BacpInstance(
        course_names=course_names,
        n_terms=p,
        credits=credits,
        prereq_pairs=prereq_pairs,
        min_credits=a,
        max_credits=b,
        min_courses=c,
        max_courses=d
    )


if __name__ == "__main__":
    inst = read_instance("data/bacp10.dat")
    print("n_terms =", inst.n_terms)
    print("n_courses =", len(inst.course_names))
    print("n_credits =", len(inst.credits))
    print("n_prereqs =", len(inst.prereq_pairs))
    print("first 5 courses =", inst.course_names[:5])