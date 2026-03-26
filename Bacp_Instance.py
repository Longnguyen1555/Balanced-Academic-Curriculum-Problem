from dataclasses import dataclass
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