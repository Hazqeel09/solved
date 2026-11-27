import unittest
from itertools import combinations_with_replacement
from math import isqrt

from checks.verify_root_sectors import replay, verify
from solved.chains import Chain, chains, level
from solved.limits import ResourceLimit
from solved.menu_programs import shortest_from_menu
from solved.root_sectors import four_event_menu, reduce_square


def explicit_chain(values):
    """Independent all-pairs recipe search for short hand-written fixtures."""
    recipes = []
    for i, target in enumerate(values[1:], 1):
        candidates = [
            (op, a, b)
            for a in range(i)
            for b in range(a, i)
            for op, value in (("+", values[a] + values[b]), ("*", values[a] * values[b]))
            if value == target
        ]
        if not candidates:
            raise AssertionError("fixture is not an AM chain")
        recipes.append(candidates[0])
    return Chain(tuple(values), tuple(recipes))


class RootSectorTests(unittest.TestCase):
    def test_all_final_recipe_aliases_in_a_complete_finite_range(self):
        record = verify(8, aliases=True)
        self.assertGreater(record["checked_square_chains_or_recipe_variants"], 5000)
        self.assertEqual(
            set(record["rules"]),
            {
                "trailing_square",
                "halve_available_factors",
                "exceptional_sum",
                "unused_first_event",
                "exceptional_product",
                "paired_twos",
                "halve_first_product",
                "halve_two_products",
                "doubled_tower_sum",
                "seven_ray",
                "seven_square_base",
                "retained_root",
                "four_event_menu",
                "late_small_menu",
                "power_exponents",
                "one_big_menu",
                "two_big_menu",
                "two_big_available",
                "two_big_prefix_root",
                "two_big_six_family",
                "two_big_three_family",
            },
        )

    def test_hand_written_boundary_cases_and_operand_orders(self):
        for values in (
            (1, 2, 4, 5, 9),
            (1, 2, 4, 16, 18, 36),
            (1, 2, 4, 16, 20, 36),
            (1, 2, 4, 16, 32, 64),
            (1, 2, 4, 5, 6, 36),
            (1, 2, 4, 16, 20, 400, 160000, 640000),
            (1, 2, 4, 16, 256, 1024, 4096),
        ):
            chain = explicit_chain(values)
            reversed_chain = Chain(chain.values, tuple((op, b, a) for op, a, b in chain.recipes))
            for source in (chain, reversed_chain):
                result = reduce_square(source)
                self.assertEqual(replay(result.chain) ** 2, values[-1])
                self.assertGreaterEqual(result.saved_instructions, 1)
                self.assertLessEqual(len(result.chain.recipes) - level(result.root), 2)

    def test_long_square_runs_and_missing_first_product_root(self):
        for gap in (2, 3, 12):
            values = [1, 2, 4, 16, 64]
            recipes = [("+", 0, 0), ("*", 1, 1), ("*", 2, 2), ("*", 2, 3)]
            for _ in range(gap):
                recipes.append(("*", len(values) - 1, len(values) - 1))
                values.append(values[-1] ** 2)
            recipes.append(("*", 4, len(values) - 1))
            values.append(64 * values[-1])
            source = Chain(tuple(values), tuple(recipes))
            result = reduce_square(source)
            self.assertEqual(result.rule, "halve_first_product")
            self.assertEqual(result.saved_instructions, 1)
            self.assertEqual(replay(result.chain) ** 2, values[-1])

    def test_unsupported_inputs_are_not_reported_as_root_obstructions(self):
        for source in (
            explicit_chain((1, 2, 4)),
            explicit_chain((1, 2, 4, 5, 6)),
            Chain((1, 2, 4, 5, 9), (("+", 0, 0), ("*", 1, 1), ("+", 0, 2), ("+", 4, 4))),
            Chain((1, 2), (("+", True, 0),)),
            None,
        ):
            with self.assertRaises(ValueError):
                reduce_square(source)
        with self.assertRaises(ValueError):
            verify(True)

    def test_source_lists_are_frozen(self):
        source = explicit_chain((1, 2, 4, 5, 9))
        values, recipes = list(source.values), [list(r) for r in source.recipes]
        result = reduce_square(Chain(values, recipes))
        values[-1] = 100
        recipes[-1][0] = "*"
        self.assertEqual(result.chain.values, (1, 2, 3))
        self.assertEqual(result.root, 3)

    def test_four_event_shared_helpers_outside_source_and_roots(self):
        source = explicit_chain((1, 2, 4, 16, 64, 80, 6400, 409600))
        menu = four_event_menu(source)
        self.assertIn(20, menu)
        self.assertIn(32, menu)
        result = reduce_square(source)
        self.assertEqual(result.chain.values, (1, 2, 4, 16, 20, 32, 640))
        self.assertEqual(result.saved_instructions, 1)
        for kwargs in ({"max_states": 0}, {"max_pairs": 0}):
            with self.assertRaises(ResourceLimit):
                reduce_square(source, **kwargs)
        with self.assertRaises(ValueError):
            four_event_menu(explicit_chain((1, 2, 4, 5, 9)))
        with self.assertRaises(ValueError):
            reduce_square(source, max_states=True)

    def test_parameterized_exchange_family_and_restricted_menu_gap(self):
        from math import isqrt

        for j in range(9):
            values = [1, 2]
            for _ in range(j + 2):
                values.append(values[-1] ** 2)
            A, u = values[-1], values[-2]
            B = A * u
            C = B + A
            values.extend((B, C, C * C, C * C * B))
            source = explicit_chain(values)
            root = isqrt(values[-1])
            bare = set(values) | {isqrt(v) for v in values if isqrt(v) ** 2 == v}
            bare = tuple(sorted(v for v in bare if v <= root))
            self.assertIsNone(shortest_from_menu(bare, root, j + 6))
            restricted = shortest_from_menu(bare, root, j + 7)
            self.assertEqual(len(restricted.recipes), j + 7)
            result = reduce_square(source)
            self.assertEqual(replay(result.chain), root)
            self.assertEqual(len(result.chain.recipes), j + 6)

    def test_late_small_power_prefixes_at_large_scales(self):
        for k, gap in ((1, 0), (1, 8), (2, 0), (4, 4), (8, 3)):
            prefix = [1, 2]
            for _ in range(k):
                prefix.append(prefix[-1] ** 2)
            A, sqrtA = prefix[-1], prefix[-2]
            B = A * sqrtA
            C = A * B
            prefix.extend((B, C, B * C))
            for _ in range(gap):
                prefix.append(prefix[-1] ** 2)
            H = prefix[-1]
            for values in ((*prefix, 4 * H), (*prefix, 4 * H, 4 * H * H)):
                source = explicit_chain(values)
                result = reduce_square(source)
                self.assertEqual(replay(result.chain) ** 2, values[-1])
                self.assertGreaterEqual(result.saved_instructions, 1)
                self.assertLessEqual(len(result.chain.recipes) - level(result.root), 2)

    def test_late_small_long_runs_and_exceptional_prefix(self):
        for prefix in ((1, 2, 3, 6, 18), (1, 2, 4, 8, 32, 256)):
            for gap, final_gap in ((2, 2), (4, 3), (8, 2)):
                values = list(prefix)
                for _ in range(gap):
                    values.append(values[-1] ** 2)
                values.append(values[-1] * values[-2])
                source = explicit_chain(values)
                result = reduce_square(source)
                self.assertEqual(replay(result.chain) ** 2, values[-1])
                for _ in range(final_gap):
                    values.append(values[-1] ** 2)
                values.append(values[-1] * values[-2])
                source = explicit_chain(values)
                result = reduce_square(source)
                self.assertEqual(replay(result.chain) ** 2, values[-1])
                self.assertGreaterEqual(result.saved_instructions, 1)

        for values, root in (
            ((1, 2, 4, 8, 32, 256, 1024, 262144), 512),
            ((1, 2, 4, 8, 32, 256, 8192, 67108864, 17179869184), 131072),
            ((1, 2, 3, 6, 18, 54, 324), 18),
        ):
            source = explicit_chain(values)
            result = reduce_square(source)
            self.assertEqual(replay(result.chain), root)
            self.assertGreaterEqual(result.saved_instructions, 2)

    def test_remaining_event_orders_stay_explicitly_unsupported(self):
        for values in (
            (1, 2, 3, 9, 10, 27, 270, 72900),
            (1, 2, 3, 9, 10, 81, 810, 65610, 4304672100),
        ):
            with self.assertRaisesRegex(ValueError, "supported sectors"):
                reduce_square(explicit_chain(values))
        source = explicit_chain((1, 2, 4, 8, 32, 256, 1024, 262144))
        for limits in ({"max_states": 0}, {"max_pairs": 0}):
            with self.assertRaises(ResourceLimit):
                reduce_square(source, **limits)

    def test_published_prefix_families_against_independent_enumeration(self):
        checked = 0
        for defect, source in chains((1 << 256) - 1, 1):
            events = [
                i
                for i in range(1, len(source.values))
                if source.values[i] != source.values[i - 1] ** 2
            ]
            if defect != 1 or len(events) != 4:
                continue
            prefix = source.values[: events[3] + 1]
            if prefix[2] == 3:
                self.assertEqual(prefix, (1, 2, 3, 6, 18))
            else:
                tower = prefix[: events[1]]
                A, sqrtA = tower[-1], tower[-2]
                self.assertGreaterEqual(A, 4)
                self.assertEqual(prefix, (*tower, A * sqrtA, A * A * sqrtA, A**4))
            checked += 1
        self.assertGreater(checked, 10)

    def test_fixed_prefix_zero_gap_palette(self):
        prefix = (1, 2, 3, 6, 18)
        small_values = {v for x in prefix for y in prefix for v in (x + y, x * y) if 18 < v < 256}
        self.assertEqual(small_values, {19, 20, 21, 24, 36, 54, 108})
        endpoints = set()
        from math import isqrt

        for D in small_values:
            for x in (*prefix, D):
                for y in (*prefix, D):
                    for N in (x + y, x * y):
                        if 256 <= N != D * D and isqrt(N) ** 2 == N:
                            endpoints.add(N)
        self.assertEqual(endpoints, {324})

    def test_one_big_prefix_growth_gaps(self):
        checked = set()
        for defect, chain in chains((1 << 512) - 1, 1):
            events = [
                i
                for i in range(1, len(chain.values))
                if chain.values[i] != chain.values[i - 1] ** 2
            ]
            if defect != 1 or len(events) != 3:
                continue
            prefix = chain.values[: events[-1] + 1]
            if prefix in checked:
                continue
            checked.add(prefix)
            Q, C = prefix[-2:]
            U = 1 << (1 << level(C))
            self.assertLess(C * C * (C + 1), U * U)
            self.assertLess(Q * Q + C, U)
            self.assertLess(2 * C + Q, U)
            if C not in (4, 5, 6):
                self.assertLess((C + Q) ** 3, U * U)
            if all(v & (v - 1) == 0 for v in prefix):
                for addend in prefix[:-1]:
                    D = C + addend
                    for cofactor in prefix:
                        N = D * cofactor
                        if D < U <= N:
                            self.assertNotEqual(isqrt(N) ** 2, N)
        self.assertGreater(len(checked), 100)
        for addend in (1, 2, 4, 16):
            N = 288 * (288 + addend)
            self.assertNotEqual(isqrt(N) ** 2, N)

    def test_gsg_fixed_palette_completeness(self):
        cases = (
            ((1, 2, 3, 4), 16, {16, 36}),
            ((1, 2, 3, 5), 16, {16, 25}),
            ((1, 2, 3, 6), 16, {16, 36}),
            ((1, 2, 3, 9, 18), 256, {324, 729, 2916}),
            ((1, 2, 3, 9, 27), 256, {324, 729, 6561}),
        )
        for prefix, boundary, expected in cases:
            small = {
                v
                for x, y in combinations_with_replacement(prefix, 2)
                for v in (x + y, x * y)
                if prefix[-1] < v < boundary
            }
            endpoints = set()
            for D in small:
                for x, y in combinations_with_replacement((*prefix, D), 2):
                    for N in (x + y, x * y):
                        if N >= boundary and N != D * D and isqrt(N) ** 2 == N:
                            endpoints.add(N)
                            result = reduce_square(explicit_chain((*prefix, D, N)))
                            self.assertEqual(replay(result.chain) ** 2, N)
                            self.assertGreaterEqual(result.saved_instructions, 1)
            self.assertEqual(endpoints, expected)

    def test_gsg_tall_towers_and_required_second_small_root(self):
        for k in (1, 2, 4, 7):
            tower = [1, 2]
            for _ in range(k):
                tower.append(tower[-1] ** 2)
            A = tower[-1]
            for offset in {1, 2, tower[-2]}:
                B = A + offset
                C = A * B
                D = C * B
                for suffix in ((4 * C, 4 * C * C), (D, D * D, D**3)):
                    source = explicit_chain((*tower, B, C, *suffix))
                    result = reduce_square(source)
                    self.assertEqual(replay(result.chain) ** 2, source.values[-1])
                    self.assertGreaterEqual(result.saved_instructions, 1)
        source = explicit_chain((1, 2, 3, 4, 7, 49, 2401, 117649))
        self.assertEqual(replay(reduce_square(source).chain), 343)

    def test_gsg_missing_first_big_root_and_operand_aliases(self):
        for e in (2, 3, 6, 10):
            prefix = [1, 2, 3]
            for _ in range(e):
                prefix.append(prefix[-1] ** 2)
            Q, X = prefix[-1], prefix[-2]
            C = Q * X
            prefix.append(C)
            for D in (C * Q, C * X):
                source = explicit_chain((*prefix, D, D * D, D * D * C))
                result = reduce_square(source)
                self.assertEqual(replay(result.chain) ** 2, source.values[-1])
                self.assertGreaterEqual(result.saved_instructions, 1)
                if D == Q * Q:
                    rows = list(source.recipes)
                    rows[len(prefix) - 1] = ("*", prefix.index(Q), prefix.index(Q))
                    aliased = Chain(source.values, tuple(rows))
                    result = reduce_square(aliased)
                    self.assertEqual(replay(result.chain) ** 2, source.values[-1])

    def test_gsg_half_root_helper_is_necessary_in_the_declared_menu(self):
        # At A=4,B=6,g=1 the distinct nonsquare pair B,C reaches the boundary.
        for D in (3456, 13824):
            source = explicit_chain((1, 2, 4, 6, 24, 576, D, 82944))
            root = 288
            without_half = {1, 2, 3, 4, 6, 16, 24, 256, root}
            self.assertIsNone(shortest_from_menu(without_half, root, 6))
            result = reduce_square(source)
            self.assertEqual(result.rule, "one_big_menu")
            self.assertEqual(result.chain.values, (1, 2, 4, 6, 24, 144, 288))
            self.assertEqual(result.saved_instructions, 1)
            with self.assertRaises(ResourceLimit):
                reduce_square(source, max_states=0)

    def test_two_big_final_gap_exceptional_programs_at_large_parameters(self):
        for gap in (2, 3, 6, 10):
            six = [1, 2, 3, 6]
            for _ in range(gap):
                six.append(six[-1] ** 2)
            H = six[-1]
            D, E = H * six[-2], H * H * six[-2]
            six.extend((D, E, E * E, E * E * D))
            result = reduce_square(explicit_chain(six), max_states=0, max_pairs=0)
            self.assertEqual(result.rule, "two_big_six_family")
            self.assertEqual(result.saved_instructions, 1)
            self.assertEqual(replay(result.chain) ** 2, six[-1])

            three = [1, 2, 3]
            for _ in range(gap):
                three.append(three[-1] ** 2)
            Q, X = three[-1], three[-2]
            C = Q * X
            D, E = C * Q, C * C * Q
            three.extend((C, D, E, E * E, E * E * D))
            result = reduce_square(explicit_chain(three), max_states=0, max_pairs=0)
            self.assertEqual(result.rule, "two_big_three_family")
            self.assertEqual(result.saved_instructions, 1)
            self.assertEqual(replay(result.chain) ** 2, three[-1])

    def test_two_big_final_gap_reuses_only_the_needed_root(self):
        for gap in (2, 5, 12):
            values = [1, 2, 3, 6, 8, 48]
            for _ in range(gap):
                values.append(values[-1] ** 2)
            values.append(values[-1] * values[-2])
            result = reduce_square(explicit_chain(values), max_states=0, max_pairs=0)
            self.assertEqual(result.rule, "two_big_available")
            self.assertEqual(result.saved_instructions, 1)
            self.assertEqual(replay(result.chain) ** 2, values[-1])
        source = explicit_chain(
            (1, 2, 3, 4, 12, 144, 20736, 2985984, 8916100448256, 26623333280885243904)
        )
        result = reduce_square(source)
        self.assertEqual(result.rule, "two_big_prefix_root")
        self.assertEqual(replay(result.chain), 5159780352)
        for limits in ({"max_states": 0}, {"max_pairs": 0}):
            with self.assertRaises(ResourceLimit):
                reduce_square(source, **limits)

    def test_two_big_adjacent_endings_and_targeted_cubic_enrichment(self):
        for k in (1, 2, 5, 9):
            tower = [1, 2]
            for _ in range(k):
                tower.append(tower[-1] ** 2)
            A = tower[-1]
            for B in (A + 1, A + tower[-2]):
                C = A * A
                for D in (C * A, C * B):
                    E = D * C
                    source = explicit_chain((*tower, B, C, D, E, E * D))
                    result = reduce_square(source)
                    self.assertEqual(result.rule, "two_big_menu")
                    self.assertEqual(replay(result.chain) ** 2, source.values[-1])
                    self.assertGreaterEqual(result.saved_instructions, 1)
        for e in (2, 4, 8):
            prefix = [1, 2, 3]
            for _ in range(e):
                prefix.append(prefix[-1] ** 2)
            C = prefix[-1] * prefix[-2]
            D = C * prefix[-1]
            for h in (1, 4):
                values = [*prefix, C, D]
                for _ in range(h):
                    values.append(values[-1] ** 2)
                K = values[-1]
                for v in (C, D):
                    E = K * v
                    source = explicit_chain((*values, E, E * K))
                    result = reduce_square(source)
                    self.assertEqual(replay(result.chain) ** 2, source.values[-1])
                    self.assertGreaterEqual(result.saved_instructions, 1)
        for base in ((1, 2, 3, 5), (1, 2, 4, 6, 24), (1, 2, 3, 9, 81, 729)):
            for gap in (2, 5):
                values = list(base)
                for _ in range(gap):
                    values.append(values[-1] ** 2)
                H = values[-1]
                D = H * values[-2]
                for E in (H * H, D * H):
                    source = explicit_chain((*values, D, E, H * H * D))
                    result = reduce_square(source)
                    self.assertEqual(replay(result.chain) ** 2, source.values[-1])
                    self.assertGreaterEqual(result.saved_instructions, 1)

    def test_two_big_fixed_zero_gap_palettes(self):
        cases = (
            ((1, 2, 3, 4), 16, {(8, 32, 256), (9, 36, 324), (12, 48, 576)}),
            ((1, 2, 3, 5), 16, set()),
            ((1, 2, 3, 6), 16, {(9, 36, 324), (9, 54, 324)}),
            ((1, 2, 3, 9, 18), 256, {(162, 1458, 236196)}),
            ((1, 2, 3, 9, 27), 256, {(243, 2187, 531441)}),
        )

        def choices(values):
            return {
                v
                for x, y in combinations_with_replacement(values, 2)
                for v in (x + y, x * y)
                if v > values[-1]
            }

        for prefix, U, expected in cases:
            found = set()
            for D in choices(prefix):
                if D >= U:
                    continue
                for E in choices((*prefix, D)):
                    if E < U or E == D * D:
                        continue
                    for N in choices((*prefix, D, E)):
                        if N < U * U or N == E * E or isqrt(N) ** 2 != N:
                            continue
                        found.add((D, E, N))
                        result = reduce_square(explicit_chain((*prefix, D, E, N)))
                        self.assertEqual(replay(result.chain) ** 2, N)
                        self.assertGreaterEqual(result.saved_instructions, 1)
            self.assertEqual(found, expected)

    def test_two_big_structural_claims_on_independently_enumerated_histories(self):
        checked = 0
        for defect, chain in chains((1 << 512) - 1, 2):
            ev = tuple(
                i
                for i in range(1, len(chain.values))
                if chain.values[i] != chain.values[i - 1] ** 2
            )
            word = "".join(
                "S" if level(chain.values[i]) == level(chain.values[i - 1]) else "G" for i in ev[2:]
            )
            if defect != 2 or word != "GSGG":
                continue
            B, C, D, E = (chain.values[i] for i in ev[1:5])
            A = chain.values[ev[1] - 1]
            g, h, j = (ev[i + 1] - ev[i] - 1 for i in (2, 3, 4))
            V = 1 << (1 << level(D))
            self.assertGreaterEqual(D**3, V**2)
            if B & (B - 1) == 0:
                self.assertTrue(all(v & (v - 1) == 0 for v in chain.values))
            N = chain.values[-1]
            if ev[-1] != len(chain.values) - 1 or isqrt(N) ** 2 != N or j:
                continue
            checked += 1
            if h:
                K = chain.values[ev[4] - 1]
                self.assertEqual(N, E * K)
                self.assertEqual(E % K, 0)
                self.assertEqual(isqrt(E // K) ** 2, E // K)
            elif g:
                H = chain.values[ev[3] - 1]
                self.assertTrue(
                    (E % D == 0 and N == D * E and isqrt(E // D) ** 2 == E // D)
                    or (N == H * H * D and isqrt(D) ** 2 == D)
                )
            elif B & (B - 1):
                if A >= 4 and C == A * B:
                    self.assertEqual((A, B, N), (4, 6, 82944))
                elif A >= 4 and C == A * A:
                    self.assertEqual(N, D * D * C)
                elif C not in (4, 5, 6, 18, 27):
                    self.assertEqual(isqrt(D) ** 2, D)
                    self.assertEqual(isqrt(E) ** 2, E)
        self.assertGreater(checked, 100)

    def test_arbitrary_prefix_fibonacci_envelope(self):
        fib = [0, 1]
        for _ in range(10):
            fib.append(fib[-1] + fib[-2])
        checked = 0
        for _, chain in chains(4096, 2):
            for start in range(1, len(chain.values)):
                suffix = chain.values[start:]
                b = sum(y != x * x for x, y in zip(suffix, suffix[1:]))
                d = len(suffix) - 1 - b
                D = suffix[0]
                self.assertLessEqual(suffix[-1], D ** ((1 << d) * fib[b + 2]))
                if b == 2:
                    U = 1 << (1 << level(D))
                    if D**3 < U**2:
                        self.assertLess(suffix[-1], U ** (1 << (d + 1)))
                checked += 1
        self.assertGreater(checked, 1000)
