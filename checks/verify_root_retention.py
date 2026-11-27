"""Exact cost certificate for an obstruction to retaining earlier square roots."""

import json

from checks.classical import shortest_chain
from checks.verify_square_instability import replay
from solved.chains import chains, level
from solved.menu_programs import shortest_from_menu

SOURCE = (1, 2, 4, 5, 20, 100, 2000, 4000000)
JOINT = (1, 2, 3, 5, 10, 20, 100, 2000)
ALTERNATIVE = (1, 2, 4, 5, 20, 400, 2000, 4000000)
CONTROL = (1, 2, 4, 8, 10, 80, 640)


def verify():
    replay(SOURCE)
    replay(JOINT)
    replay(ALTERNATIVE)
    replay(CONTROL)
    if SOURCE[-1] != 2000**2 or 100 != 10**2 or len(SOURCE) - 1 - level(SOURCE[-1]) != 2:
        raise ArithmeticError("the source is not the declared defect-two square history")
    minima = []
    for target, cost in ((2000, 6), (4000000, 7)):
        exact = shortest_chain(target, product=True)
        if len(exact) - 1 != cost:
            raise ArithmeticError("the independent shortest search changed the cost")
        census = {}
        for defect, chain in chains(target, cost - 1 - level(target)):
            census[defect] = census.get(defect, 0) + 1
            if chain.values[-1] == target:
                raise ArithmeticError("a shorter chain contradicts the claimed minimum")
        minima.append(
            {
                "target": target,
                "minimum": cost,
                "excluded_budget": cost - 1,
                "lower_bound_census": {str(k): census[k] for k in sorted(census)},
            }
        )
    inspected = 0
    endpoints = []
    for _, chain in chains(2000, 2):
        inspected += 1
        if chain.values[-1] == 2000:
            if 10 in chain.values:
                raise ArithmeticError("a six-write joint witness was found")
            endpoints.append(list(chain.values))
    menu = {1, 2, 3, 4, 5, 10, 16, 20, 100, 256, 1000, 2000}
    if shortest_from_menu(menu, 2000, 6, required=(10,)) is not None:
        raise ArithmeticError("the restricted menu contradicts the independent lower bound")
    joint = shortest_from_menu(menu, 2000, 7, required=(10,))
    if joint is None or len(joint.recipes) != 7 or not {10, 2000} <= set(joint.values):
        raise ArithmeticError("the joint upper bound was not reconstructed")
    return {
        "model": "increasing addition-multiplication chains from 1, unrestricted retention",
        "source": list(SOURCE),
        "source_level": level(SOURCE[-1]),
        "source_defect": 2,
        "root": 2000,
        "required_earlier_root": 10,
        "endpoint_minima": minima,
        "joint_minimum": 7,
        "joint_witness": list(JOINT),
        "joint_excluded_budget": 6,
        "independent_census_sequences": inspected,
        "all_six_write_root_histories": endpoints,
        "alternative_optimal_source": list(ALTERNATIVE),
        "alternative_root_witness": list(ALTERNATIVE[:-1]),
        "menu_gap_control_witness": list(CONTROL),
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
