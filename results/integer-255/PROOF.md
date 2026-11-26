# Exact computation costs for the integer 255

**Status: finite verification.** The checks establish only the stated finite range.

Starting from 1, successive writes 2,4,16,256,255 take five operations. The cap must allow 256. After three writes every absolute value is at most 16 by maximum growth, even admitting negative values. A fourth sum or difference has magnitude at most 32 and no two positive integers at most 16 have product 255, as its factor pairs follow from 255=3·5·17. This proves the lower bound of five. For unsigned programs, prune unused results and order distinct useful values increasingly. Positive additions and nontrivial multiplications strictly increase beyond their inputs, and no useful value exceeds 255. Iterative deepening enumerates every such chain by all preceding unordered pairs. The first success has length six, with values 1,2,3,5,15,17,255. [Exact witnesses](../../checks/expected/classical.json)
