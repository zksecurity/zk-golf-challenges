# Keccak-f[1600] — leaderboard comparison points

Provenance and reproduction steps for the `comparison_points` on the
`keccak-f1600` entry in `lean/instances.yml`. Every number here was **measured**
by compiling the referenced circuit, not estimated.

The challenge metric is `score = allocations + constraints` over **pure R1CS**
(Groth16): `constraints` = non-linear R1CS rows, `allocations` = witness signals
the circuit allocates (the 1600 input bits are *not* counted — the caller
allocates them). The challenge is the bare **permutation** (1600 input bits →
1600 output bits, no padding/absorb/squeeze), so every comparison targets each
library's bare permutation, not a full hash.

## vocdoni/keccak256-circom — score 307,200

- Repo: <https://github.com/vocdoni/keccak256-circom>, commit `af3e898`.
- Compiler: circom 2.x (iden3), `--O2` (linear-constraint elimination on).
- Component: `Keccakf()` — the 24-round permutation, `in[25*64] -> out[25*64]`.

```
component main = Keccakf();          # main_keccakf.circom
circom main_keccakf.circom --r1cs --O2
```

Raw output:

```
non-linear constraints: 153600
linear constraints:     0
private inputs:         1600
public outputs:         1600
wires:                  155201        # 1 constant + 1600 inputs + 153600 witnessed
```

Mapping to the challenge metric: `wires - 1 (constant) - 1600 (inputs) = 153600`
allocations; `153600` constraints → **307,200**, exactly the baseline.

Note: the repo README's headline "≈150848 constraints" is a full
`Keccak(256,256)` **hash** of a 32-byte input, which we also compiled
(`150848` constraints, `151105` wires). That is *smaller* than the permutation
because it absorbs a short message into an all-zero state, so `--O2` folds away
much of round 1 — the free-input permutation cannot, hence 153600 > 150848.

## Why gnark is not listed

gnark's `std/permutation/keccakf` (v0.15.0) is **not pure R1CS**, so it is not a
relevant comparison for this challenge. Its `uints.BinaryField` implements every
bytewise XOR/AND with 256×256 **lookup tables** (a log-derivative argument),
which is cheap in gnark's default PLONKish backend but not in Groth16. For the
record, compiling it with `r1cs.NewBuilder` reports 189,072 constraints /
348,468 witnesses — *more* than the bit-blasted Circom reference, because the
lookup tables must be realized as R1CS rows. This is exactly the "verify the
gnark backend before comparing" caveat from the source report, confirmed.

## What was validated against the source report

| Claim | Result |
|---|---|
| vocdoni full hash `Keccak(256,256)` ≈ 150,848 constraints | **Exact** — compiled: 150,848 / 151,105 wires. |
| 150,848 is *the* Keccak-in-R1CS figure | **Corrected** — that is a full hash of a small input; the permutation (the challenge) is 153,600. |
| ρ/π free, θ/ι linear, χ the only essential nonlinearity (1 AND/bit) | Confirmed against `permutations.circom` and our spec. |
| Gate costs (`XOR`=1 mult, `AND`=1 mult, `XorArraySingle`=`1−a`=0 mult) | Confirmed against circomlib `gates.circom`. |
| gnark is "mixed / not the standard R1CS path" | **Confirmed** — lookup-based; 189,072 constraints in R1CS, worse than vocdoni. |
| Electron-Labs/keccak256-circom (`5f65355`) | Fork of vocdoni; permutation circuit is byte-identical → same 153,600. |
| ~38k essential-χ floor | Correct as a floor; not reachable in pure R1CS (needs lookups/GKR), consistent with the report. |
