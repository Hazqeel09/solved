# Star-chain lifting and finite Scholz–Brauer certificates

**Status: finite verification.** The checks establish only the stated finite range.

In a star chain for the exponent, a step v=a+b uses the previous largest exponent a and an earlier b. Given Mₐ=2ᵃ−1 and Mᵦ, use b doublings and one addition to obtain Mᵥ=2ᵇMₐ+Mᵦ. Extra doublings sum to n−1, so this lift costs n−1 plus the star-chain length. For n≤59, exhaustive iterative deepening over all chains and over star chains yields the same minimum exponent length. The certificate stores each star chain and the verifier checks that every lifted value is a sum of earlier entries. The exact Mersenne optimum may be below this upper bound. [Finite certificates](../../checks/expected/classical.json)
